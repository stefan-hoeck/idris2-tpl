module TPL.Lambda.Typed.Type

import public Data.List.Quantifiers as L
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
  PRec  : ByteBounds -> List (VarName,RawTpe) -> RawTpe

%runElab derive "RawTpe" [Show,Eq]

export %inline
pvar : ByteBounded VarName -> RawTpe
pvar (B v b) = PVar b v

export
Cast RawTpe ByteBounds where
  cast (PVar b _)   = b
  cast (PFun b _ _) = b
  cast (PRec b _)   = b

export
MapBounds RawTpe where
  mapBounds f (PVar b v)   = PVar (f b) v
  mapBounds f (PFun b x y) = PFun (f b) (mapBounds f x) (mapBounds f y)
  mapBounds f (PRec b fs)  =
    assert_total $ PRec (f b) (map (mapBounds f) <$> fs)

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
  TRec  : List (VarName,Tpe) -> Tpe

%runElab derive "Tpe" [Show,Eq]

public export
data IsField : VarName -> List (VarName,Tpe) -> Tpe -> Type where
  IFZ : IsField v ((v,t)::ps) t
  IFS : IsField v ps t -> IsField v (p::ps) t

export
isField : (v : VarName) -> (ps : List (VarName,Tpe)) -> Maybe (t ** IsField v ps t)
isField v []            = Nothing
isField v ((w,x) :: xs) =
  case hdecEq v w of
    Just0 p  => Just (x ** rewrite p in IFZ)
    Nothing0 => (\(t ** prf) => (t ** IFS prf)) <$> isField v xs

public export
0 TpeErr : Type
TpeErr = TplErr Tpe

public export
0 LamErr : Type
LamErr = BBErr (TplErr Tpe)

pairsEq : (xs,ys : List (VarName,Tpe)) -> Maybe0 (xs === ys)

pairEq : (x,y : (VarName,Tpe)) -> Maybe0 (x === y)

tpeEq : (x,y : Tpe) -> Maybe0 (x === y)
tpeEq TNat  TNat                = Just0 Refl
tpeEq TBool TBool               = Just0 Refl
tpeEq TUnit TUnit               = Just0 Refl
tpeEq (TFun a1 r1) (TFun a2 r2) = maybeCong2 TFun (tpeEq a1 a2) (tpeEq r1 r2)
tpeEq (TRec r1) (TRec r2)       = maybeCong TRec (pairsEq r1 r2)
tpeEq _ _                       = Nothing0

pairEq (v1,t1) (v2,t2) = maybeCong2 MkPair (hdecEq v1 v2) (tpeEq t1 t2)

pairsEq [] []               = Just0 Refl
pairsEq (p1::ps1) (p2::ps2) = maybeCong2 (::) (pairEq p1 p2) (pairsEq ps1 ps2)
pairsEq _ _                 = Nothing0

export %inline
HDecEq Tpe where hdecEq = tpeEq

public export
0 RecTypes : List (VarName,Tpe) -> List Type

public export
0 IType : Tpe -> Type
IType TNat       = Nat
IType TBool      = Bool
IType TUnit      = Unit
IType (TFun x y) = IType x -> IType y
IType (TRec ps)  = HList (RecTypes ps)

RecTypes []          = []
RecTypes ((_,t)::ps) = IType t :: RecTypes ps

public export
0 MTpe : Type
MTpe = Maybe Tpe

export
Cast Tpe RawTpe where
  cast TNat       = PVar NoBB "Nat"
  cast TBool      = PVar NoBB "Bool"
  cast TUnit      = PVar NoBB "Unit"
  cast (TFun x y) = PFun NoBB (cast x) (cast y)
  cast (TRec ps)  = assert_total $ PRec NoBB (map cast <$> ps)

--------------------------------------------------------------------------------
-- Interpolation
--------------------------------------------------------------------------------

paren : RawTpe -> String

prettyFields : SnocList String -> List (VarName,RawTpe) -> String

prettyTpe : RawTpe -> String
prettyTpe (PVar _ v)   = interpolate v
prettyTpe (PFun _ a r) = "\{paren a} -> \{prettyTpe r}"
prettyTpe (PRec _ fs)  = "<\{prettyFields [<] fs}>"

paren t@(PFun {}) = "(\{prettyTpe t})"
paren t           = prettyTpe t

prettyFields ss []          = fastConcat $ intersperse "," (ss <>> [])
prettyFields ss ((n,t)::ps) = prettyFields (ss:<"\{n}:\{prettyTpe t}") ps

export %inline
Interpolation RawTpe where
  interpolate = prettyTpe

export %inline
Interpolation Tpe where
  interpolate = prettyTpe . cast
