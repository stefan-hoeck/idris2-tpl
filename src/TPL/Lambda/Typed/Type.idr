module TPL.Lambda.Typed.Type

import public Decidable.HDecEq
import public TPL.Error
import public TPL.Name
import public Text.ByteBounds
import Derive.Prelude

%default total
%language ElabReflection

||| Freshly parsed type: type names and function types.
public export
data RawTpe : Type where
  PVar  : ByteBounds -> VarName -> RawTpe
  PFun  : ByteBounds -> RawTpe -> RawTpe -> RawTpe

%runElab derive "RawTpe" [Show,Eq]

export %inline
pvar : ByteBounded VarName -> RawTpe
pvar (B v b) = PVar b v

export
Cast RawTpe ByteBounds where
  cast (PVar b _)   = b
  cast (PFun b _ _) = b

export
tpeAppAll : SnocList RawTpe -> RawTpe -> RawTpe
tpeAppAll [<]       y = y
tpeAppAll (sx :< x) y = tpeAppAll sx (PFun (cast x <+> cast y) x y)

||| Fully resolved type
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

public export
0 MTpe : Type
MTpe = Maybe Tpe

export
Cast Tpe RawTpe where
  cast TNat       = PVar NoBB "Nat"
  cast TBool      = PVar NoBB "Bool"
  cast TUnit      = PVar NoBB "Unit"
  cast (TFun x y) = PFun NoBB (cast x) (cast y)

--------------------------------------------------------------------------------
-- Interpolation
--------------------------------------------------------------------------------

paren : RawTpe -> String

prettyTpe : RawTpe -> String
prettyTpe (PVar _ v)   = interpolate v
prettyTpe (PFun _ a r) = "\{paren a} -> \{prettyTpe r}"

paren t@(PFun {}) = "(\{prettyTpe t})"
paren t           = prettyTpe t

export %inline
Interpolation RawTpe where
  interpolate = prettyTpe

export %inline
Interpolation Tpe where
  interpolate = prettyTpe . cast
