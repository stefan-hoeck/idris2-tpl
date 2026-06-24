module TPL.ArExp.TT

import Derive.HDecEq
import Derive.Prelude
import TPL.ArExp.Term
import Text.ByteBounds

%default total
%language ElabReflection

public export
data Tpe = TNat | TBool

%runElab derive "Tpe" [Show,Eq,Ord,HDecEq]

export
Interpolation Tpe where
  interpolate TNat  = "Nat"
  interpolate TBool = "Bool"

public export
data TpeErr : Type where
  ErrUnify : (exp, found : Tpe) -> TpeErr

%runElab derive "TpeErr" [Show,Eq]

export
Interpolation TpeErr where
  interpolate (ErrUnify e f) =
    "type mismatch; can't unify \{e} (expected) with \{f} (found)"

public export
0 ArErr : Type
ArErr = BBErr TpeErr

||| The Idris type corresponding to a `Tpe`
public export
0 IType : Tpe -> Type
IType TNat  = Nat
IType TBool = Bool

public export
data ArTT : Tpe -> Type where
  ATrue  : ByteBounds -> ArTT TBool
  AFalse : ByteBounds -> ArTT TBool

  AZero  : ByteBounds -> ArTT TNat
  ASucc  : ByteBounds -> ArTT TNat -> ArTT TNat
  APred  : ByteBounds -> ArTT TNat -> ArTT TNat
  AIsZ   : ByteBounds -> ArTT TNat -> ArTT TBool

  AIf    : ByteBounds -> ArTT TBool -> ArTT t -> ArTT t -> ArTT t

%runElab deriveIndexed "ArTT" [Show]

export
fromBool : ByteBounds -> Bool -> ArTT TBool
fromBool b True  = ATrue b
fromBool b False = AFalse b

export
Cast (ArTT t) ByteBounds where
  cast (ATrue x)     = x
  cast (AFalse x)    = x
  cast (AZero x)     = x
  cast (ASucc x _)   = x
  cast (APred x _)   = x
  cast (AIsZ x _)    = x
  cast (AIf x _ _ _) = x

--------------------------------------------------------------------------------
-- Type Checking
--------------------------------------------------------------------------------

typeErr : Cast t ByteBounds => t -> Tpe -> Tpe -> Either ArErr a
typeErr t e f = Left $ B (Custom $ ErrUnify e f) (cast t)

||| Very basic type checking.
export
typeCheck : Term -> Either ArErr (t ** ArTT t)
typeCheck (TTrue b)   = Right (_ ** ATrue b)
typeCheck (TFalse b)  = Right (_ ** AFalse b)
typeCheck (TZ b)      = Right (_ ** AZero b)
typeCheck (TSucc b x) =
  case typeCheck x of
    Right (TNat ** t) => Right (_ ** ASucc b t)
    Right (t ** _)    => typeErr x TNat t
    Left x            => Left x
typeCheck (TPred b x)   =
  case typeCheck x of
    Right (TNat ** t) => Right (_ ** APred b t)
    Right (t ** _)    => typeErr x TNat t
    Left x            => Left x
typeCheck (TIsZ b x)    =
  case typeCheck x of
    Right (TNat ** t) => Right (_ ** AIsZ b t)
    Right (t ** _)    => typeErr x TNat t
    Left x            => Left x
typeCheck (TIf b i t e) = Prelude.do
  (TBool ** i2) <- typeCheck i | (t ** _) => typeErr i TBool t
  (tt    ** t2) <- typeCheck t
  (te    ** e2) <- typeCheck e
  case hdecEq tt te of
    Just0 prf  => Right (tt ** AIf b i2 t2 (rewrite prf in e2))
    Nothing0   => typeErr e tt te

--------------------------------------------------------------------------------
-- Evaluation
--------------------------------------------------------------------------------

export
step : ArTT t -> Either (IType t) (ArTT t)
step (ATrue _)       = Left True
step (AFalse _)      = Left False
step (AZero _)       = Left 0
step (ASucc b x)     = bimap S (ASucc b) $ step x
step (APred b x)     = bimap pred (APred b) $ step x
step (AIsZ b x)      = bimap isZero (AIsZ b) $ step x
step (AIf _ (ATrue _)  t f) = Right t
step (AIf _ (AFalse _) t f) = Right f
step (AIf b v    t f) =
  case step v of
    Right v2 => Right (AIf b v2 t f)
    Left val => Right (AIf b (fromBool (cast v) val) t f)

export
eval : ArTT t -> IType t
eval x =
  case step x of
    Left v   => v
    Right x2 => eval (assert_smaller x x2)
