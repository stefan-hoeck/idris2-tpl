module TPL.Lambda.Typed.Syntax

import Derive.Prelude
import public TPL.Env
import public TPL.Name.Var
import public TPL.Lambda.Typed.Type

%default total
%language ElabReflection

--------------------------------------------------------------------------------
-- Patterns
--------------------------------------------------------------------------------

public export
data Pattern : Type where
  PV : BindName -> Pattern
  PT : List (ByteBounded VarName, Pattern) -> Pattern

%runElab derive "Pattern" [Show,Eq]

public export
0 PatField : Type
PatField = (ByteBounded VarName, Pattern)

mapPatFields : (ByteBounds -> ByteBounds) -> List PatField -> List PatField

mapPatBounds : (ByteBounds -> ByteBounds) -> Pattern -> Pattern
mapPatBounds f (PV x)  = PV x
mapPatBounds f (PT xs) = PT $ mapPatFields f xs

mapPatFields f [] = []
mapPatFields f ((v,p)::ps) =
  (mapBounds f v, mapPatBounds f p) :: mapPatFields f ps

prettyPatFields : SnocList String -> List PatField -> String

prettyPat : Pattern -> String
prettyPat (PV n)  = interpolate n
prettyPat (PT ps) = "{\{prettyPatFields [<] ps}}"

prettyPatFields ss [] = fastConcat $ intersperse "," (ss <>> [])
prettyPatFields ss ((v,p)::ps) =
  prettyPatFields (ss:<"\{v.val}=\{prettyPat p}") ps

export %inline
Interpolation Pattern where interpolate = prettyPat

export %inline
MapBounds Pattern where mapBounds = mapPatBounds

--------------------------------------------------------------------------------
-- Primitives
--------------------------------------------------------------------------------

public export
data Prim : Type where
  PNat  : Nat -> Prim
  PBool : Bool -> Prim
  PUnit : Prim

%runElab derive "Prim" [Show,Eq]

export
Interpolation Prim where
  interpolate (PNat v)  = show v
  interpolate (PBool v) = show v
  interpolate PUnit     = "unit"

--------------------------------------------------------------------------------
-- Parsed Terms
--------------------------------------------------------------------------------

||| High-level syntax
public export
data PTerm : Type where
  ||| Variables
  PVar     : ByteBounds -> (v : VarName) -> PTerm

  ||| Record field projection
  PField   : ByteBounds -> PTerm -> ByteBounded VarName -> PTerm

  ||| Abstraction: A bound variable, its type, and its scope
  PLam     : ByteBounds -> (v : BindName) -> (t : RawTpe) -> (sc : PTerm) -> PTerm

  ||| Let binding
  PLet     : ByteBounds -> Pattern -> (x : PTerm) -> (sc : PTerm) -> PTerm

  ||| Recursive let binding
  PLetrec  :
       ByteBounds
    -> (v : BindName)
    -> (t : RawTpe)
    -> (x : PTerm)
    -> (sc : PTerm)
    -> PTerm

  ||| Function application
  PApp     : ByteBounds -> (t,s : PTerm) -> PTerm

  ||| Primitive values
  PPrim    : ByteBounds -> Prim -> PTerm

  ||| record constructor
  PRec     : ByteBounds -> List (VarName, PTerm) -> PTerm

  ||| `if ... then ... else` function. Eventually, this could be
  ||| desugared into a pattern match on bools.
  PIf      : ByteBounds -> (i,t,e : PTerm) -> PTerm

%runElab derive "PTerm" [Show,Eq]

public export %inline
FromString PTerm where fromString = PVar NoBB . fromString

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

export
Cast PTerm ByteBounds where
  cast (PVar b _)          = b
  cast (PField b _ _)      = b
  cast (PLam b _ _ _)      = b
  cast (PLet b _ _ _)      = b
  cast (PLetrec b _ _ _ _) = b
  cast (PApp b _ _)        = b
  cast (PPrim b _)         = b
  cast (PRec b _)          = b
  cast (PIf b _ _ _)       = b

export
MapBounds PTerm where
  mapBounds f (PVar b v)            = PVar (f b) v
  mapBounds f (PField b t v)        = PField (f b) (mapBounds f t) (mapBounds f v)
  mapBounds f (PLam b v t sc)       = PLam (f b) v (mapBounds f t) (mapBounds f sc)
  mapBounds f (PLet b v x sc)       = PLet (f b) (mapBounds f v) (mapBounds f x) (mapBounds f sc)
  mapBounds f (PLetrec b v t x sc)  = PLetrec (f b) v (mapBounds f t) (mapBounds f x) (mapBounds f sc)
  mapBounds f (PApp b t s)          = PApp (f b) (mapBounds f t) (mapBounds f s)
  mapBounds f (PPrim b y)           = PPrim (f b) y
  mapBounds f (PRec b y)            = assert_total $ PRec (f b) (map (mapBounds f) <$> y)
  mapBounds f (PIf b i t e)         =
    PIf (f b) (mapBounds f i) (mapBounds f t) (mapBounds f e)

export
nat : ByteBounds -> Nat -> PTerm
nat bb n = PPrim bb (PNat n)

export %inline
int : ByteBounded Integer -> PTerm
int (B i bb) = nat bb $ cast i

export %inline
bool : ByteBounded Bool -> PTerm
bool (B b bb) = PPrim bb (PBool b)

export %inline
unit : ByteBounds -> PTerm
unit bb = PPrim bb PUnit

export
appAll : PTerm -> List PTerm -> PTerm
appAll s [] = s
appAll s (x::xs) = appAll (PApp (cast s <+> cast x) s x) xs

export %inline
appSnoc : PTerm -> SnocList PTerm -> PTerm
appSnoc s = appAll s . (<>> [])

export %inline
seq : PTerm -> PTerm -> PTerm
seq s t = PApp NoBB (PLam NoBB PH (PVar NoBB "Unit") t) s

export %inline
tif : ByteBounds -> PTerm -> PTerm -> PTerm -> PTerm
tif b i t e = PIf (b <+> cast e) i t e

--------------------------------------------------------------------------------
-- Pretty Printing
--------------------------------------------------------------------------------

isAtom : PTerm -> Bool
isAtom (PVar {})   = True
isAtom (PField {}) = True
isAtom (PPrim {})  = True
isAtom (PRec {})   = True
isAtom _           = False

appL : PTerm -> String

paren : PTerm -> String

prettyFields : SnocList String -> List (VarName,PTerm) -> String

pretty : PTerm -> String
pretty (PVar _ v)           = v.name
pretty (PField _ t v)       = "\{paren t}.\{v.val}"
pretty (PLam _ v t sc)      = "λ\{v}: \{t}. \{pretty sc}"
pretty (PLet _ v x sc)      = "let \{v} = \{pretty x} in \{pretty sc}"
pretty (PLetrec _ v t x sc) = "letrec \{v} : \{t} = \{pretty x} in \{pretty sc}"
pretty (PApp _ t s)         = "\{appL t} \{paren s}"
pretty (PPrim _ p)          = interpolate p
pretty (PRec _ p)           = "{\{prettyFields [<] p}}"
pretty (PIf _ i t e)        = "if \{pretty i} then \{pretty t} else \{pretty e}"

paren t = if isAtom t then pretty t else "(\{pretty t})"

prettyFields ss []          = fastConcat $ intersperse "," (ss <>> [])
prettyFields ss ((n,t)::ps) = prettyFields (ss:<"\{n}=\{pretty t}") ps

appL (PApp _ t s) = "\{appL t} \{paren s}"
appL t            = paren t

export %inline
Interpolation PTerm where interpolate = pretty
