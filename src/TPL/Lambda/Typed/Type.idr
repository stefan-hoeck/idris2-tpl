module TPL.Lambda.Typed.Type

import public Decidable.HDecEq
import public TPL.Error
import public Text.ByteBounds
import Derive.Prelude

%default total
%language ElabReflection

public export
data Tpe : Type where
  TNat  : Tpe
  TBool : Tpe
  TUnit : Tpe
  TFun  : Tpe -> Tpe -> Tpe

%runElab derive "Tpe" [Show,Eq]

public export
0 TpeErr : Type
TpeErr = TplErr Tpe

public export
0 LamErr : Type
LamErr = BBErr (TplErr Tpe)

export
HDecEq Tpe where
  hdecEq TNat  TNat                = Just0 Refl
  hdecEq TBool TBool               = Just0 Refl
  hdecEq TUnit TUnit               = Just0 Refl
  hdecEq (TFun a1 r1) (TFun a2 r2) =
    maybeCong2 TFun (hdecEq a1 a2) (hdecEq r1 r2)
  hdecEq _ _                       = Nothing0

public export
0 IType : Tpe -> Type
IType TNat       = Nat
IType TBool      = Bool
IType TUnit      = Unit
IType (TFun x y) = IType x -> IType y

export
tpeAppAll : SnocList (ByteBounded Tpe) -> ByteBounded Tpe -> ByteBounded Tpe
tpeAppAll [<]       y = y
tpeAppAll (sx :< x) y = tpeAppAll sx [| TFun x y |]

public export
0 MTpe : Type
MTpe = Maybe Tpe

--------------------------------------------------------------------------------
-- Interpolation
--------------------------------------------------------------------------------

paren : Tpe -> String

prettyTpe : Tpe -> String
prettyTpe TNat       = "Nat"
prettyTpe TBool      = "Bool"
prettyTpe TUnit      = "Unit"
prettyTpe (TFun a r) = "\{paren a} -> \{prettyTpe r}"

paren t@(TFun {}) = "(\{prettyTpe t})"
paren t           = prettyTpe t

export %inline
Interpolation Tpe where
  interpolate = prettyTpe
