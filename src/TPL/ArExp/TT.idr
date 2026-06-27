module TPL.ArExp.TT

import Derive.HDecEq
import Derive.Prelude
import TPL.ArExp.Term
import Text.ByteBounds
import public TPL.Error

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
0 TpeErr : Type
TpeErr = TplErr Tpe

public export
0 ArErr : Type
ArErr = BBErr (TplErr Tpe)

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

check :
     {found : _}
  -> (exp : Tpe)
  -> ByteBounds
  -> ArTT found
  -> Either ArErr (ArTT exp)
check exp bb t =
  case hdecEq exp found of
    Just0 prf => Right (rewrite prf in t)
    Nothing0  => typeErr bb exp found

typeCheckAs : (t : Tpe) -> Term -> Either ArErr (ArTT t)
typeCheckAs t (TTrue x)     = check t x (ATrue x)
typeCheckAs t (TFalse x)    = check t x (AFalse x)
typeCheckAs t (TZ x)        = check t x (AZero x)
typeCheckAs t (TSucc x y)   = typeCheckAs TNat y >>= check t x . ASucc x
typeCheckAs t (TPred x y)   = typeCheckAs TNat y >>= check t x . APred x
typeCheckAs t (TIsZ x y)    = typeCheckAs TNat y >>= check t x . AIsZ x
typeCheckAs t (TIf x i y e) = Prelude.do
  i2 <- typeCheckAs TBool i
  y2 <- typeCheckAs t y
  e2 <- typeCheckAs t e
  Right (AIf x i2 y2 e2)

wrap : {t : _} -> ArTT t -> (x ** ArTT x)
wrap x = (t ** x)

export
typeCheck : Term -> Either ArErr (t ** ArTT t)
typeCheck (TTrue b)   = Right (_ ** ATrue b)
typeCheck (TFalse b)  = Right (_ ** AFalse b)
typeCheck (TZ b)      = Right (_ ** AZero b)
typeCheck (TSucc b x) = (wrap . ASucc b) <$> typeCheckAs TNat x
typeCheck (TPred b x) = (wrap . APred b) <$> typeCheckAs TNat x
typeCheck (TIsZ b x)  = (wrap . AIsZ b)  <$> typeCheckAs TNat x
typeCheck (TIf b i t e) = Prelude.do
  i2 <- typeCheckAs TBool i
  (tt ** t2) <- typeCheck t
  e2 <- typeCheckAs tt e
  Right (tt ** AIf b i2 t2 e2)

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
