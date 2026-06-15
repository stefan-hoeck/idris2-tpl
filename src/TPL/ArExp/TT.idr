module TPL.ArExp.TT

import Derive.Prelude
import Derive.HDecEq
import TPL.ArExp.Term

%default total
%language ElabReflection

public export
data Tpe = TNat | TBool

%runElab derive "Tpe" [Show,Eq,Ord,HDecEq]

export
Interpolation Tpe where
  interpolate TNat  = "Nat"
  interpolate TBool = "Bool"

||| The Idris type corresponding to a `Tpe`
public export
0 IType : Tpe -> Type
IType TNat  = Nat
IType TBool = Bool

public export
data ArTT : Tpe -> Type where
  ATrue  : ArTT TBool
  AFalse : ArTT TBool

  AZero  : ArTT TNat
  ASucc  : ArTT TNat -> ArTT TNat
  APred  : ArTT TNat -> ArTT TNat
  AIsZ   : ArTT TNat -> ArTT TBool

  AIf    : ArTT TBool -> ArTT t -> ArTT t -> ArTT t

%runElab deriveIndexed "ArTT" [Show]

export
Cast Bool (ArTT TBool) where
  cast True  = ATrue
  cast False = AFalse

--------------------------------------------------------------------------------
-- Type Checking
--------------------------------------------------------------------------------

typeErr : Tpe -> Tpe -> Either String a
typeErr x y = Left "Type error: Can't unify \{x} with \{y}"

||| Very basic type checking.
|||
||| TODO: We should have proper error messages with source locations here.
export
typeCheck : Term -> Either String (t ** ArTT t)
typeCheck TTrue       = Right (_ ** ATrue)
typeCheck TFalse      = Right (_ ** AFalse)
typeCheck TZ          = Right (_ ** AZero)
typeCheck (TSucc x)   =
  case typeCheck x of
    Right (TNat ** t) => Right (_ ** ASucc t)
    Right (t ** _)    => typeErr t TNat
    Left x            => Left x
typeCheck (TPred x)   =
  case typeCheck x of
    Right (TNat ** t) => Right (_ ** APred t)
    Right (t ** _)    => typeErr t TNat
    Left x            => Left x
typeCheck (TIsZ x)    =
  case typeCheck x of
    Right (TNat ** t) => Right (_ ** AIsZ t)
    Right (t ** _)    => typeErr t TNat
    Left x            => Left x
typeCheck (TIf i t e) = Prelude.do
  (TBool ** i2) <- typeCheck i | (t ** _) => typeErr t TBool
  (tt    ** t2) <- typeCheck t
  (te    ** e2) <- typeCheck e
  case hdecEq tt te of
    Just0 prf  => Right (tt ** AIf i2 t2 (rewrite prf in e2))
    Nothing0   => typeErr tt te

--------------------------------------------------------------------------------
-- Evaluation
--------------------------------------------------------------------------------

export
step : ArTT t -> Either (IType t) (ArTT t)
step ATrue       = Left True
step AFalse      = Left False
step AZero       = Left 0
step (ASucc x)   = bimap S ASucc $ step x
step (APred x)   = bimap pred APred $ step x
step (AIsZ x)    = bimap isZero AIsZ $ step x
step (AIf ATrue  t f) = Right t
step (AIf AFalse t f) = Right f
step (AIf b      t f) =
  case step b of
    Right b2 => Right (AIf b2 t f)
    Left v   => Right (AIf (cast v) t f)

export
eval : ArTT t -> IType t
eval x =
  case step x of
    Left v   => v
    Right x2 => eval (assert_smaller x x2)
