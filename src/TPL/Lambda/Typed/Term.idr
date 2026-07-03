module TPL.Lambda.Typed.Term

import Derive.Prelude
import public TPL.Env
import public TPL.Name.Var
import public TPL.Lambda.Typed.Type

%default total
%language ElabReflection

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

public export
data Term : Type where
  ||| Variables
  TVar   : ByteBounds -> (v : VarName) -> Term

  ||| Abstraction: A bound variable, its type, and its scope
  TLam   : ByteBounds -> (v : BindName) -> (t : RawTpe) -> (sc : Term) -> Term

  ||| Function application
  TApp   : ByteBounds -> (t,s : Term) -> Term

  ||| Primitive values
  TPrim  : ByteBounds -> Prim -> Term

  ||| `if ... then ... else` function. Eventually, this could be
  ||| desugared into a pattern match on bools.
  TIf    : ByteBounds -> (i,t,e : Term) -> Term

%runElab derive "Term" [Show,Eq]

public export %inline
FromString Term where fromString = TVar NoBB . fromString

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

export
Cast Term ByteBounds where
  cast (TVar x _)     = x
  cast (TLam x _ _ _) = x
  cast (TApp x _ _)   = x
  cast (TPrim x _)    = x
  cast (TIf x _ _ _)  = x

export
MapBounds Term where
  mapBounds f (TVar x v)      = TVar (f x) v
  mapBounds f (TLam x v t sc) = TLam (f x) v (mapBounds f t) (mapBounds f sc)
  mapBounds f (TApp x t s)    = TApp (f x) (mapBounds f t) (mapBounds f s)
  mapBounds f (TPrim x y)     = TPrim (f x) y
  mapBounds f (TIf x i t e)   =
    TIf (f x) (mapBounds f i) (mapBounds f t) (mapBounds f e)

export
nat : ByteBounds -> Nat -> Term
nat bb n = TPrim bb (PNat n)

export %inline
int : ByteBounded Integer -> Term
int (B i bb) = nat bb $ cast i

export %inline
bool : ByteBounded Bool -> Term
bool (B b bb) = TPrim bb (PBool b)

export %inline
unit : ByteBounds -> Term
unit bb = TPrim bb PUnit

export
appAll : Term -> List Term -> Term
appAll s []      = s
appAll s (t::ts) = appAll (TApp (cast s <+> cast t) s t) ts

export %inline
appAllSnoc : Term -> SnocList Term -> Term
appAllSnoc s = appAll s . (<>>[])

export %inline
seq : SnocList Term -> Term -> Term
seq [<]     t = t
seq (ss:<s) t = seq ss $ TApp NoBB (TLam NoBB PH (PVar NoBB "Unit") t) s

--------------------------------------------------------------------------------
-- Pretty Printing
--------------------------------------------------------------------------------

isAtom : Term -> Bool
isAtom (TVar {})  = True
isAtom (TPrim {}) = True
isAtom _          = False

appL : Term -> String

paren : Term -> String

pretty : Term -> String
pretty (TVar _ v)      = v.name
pretty (TLam _ v t sc) = "λ\{v}: \{t}. \{pretty sc}"
pretty (TApp _ t s)    = "\{appL t} \{paren s}"
pretty (TPrim _ p)     = interpolate p
pretty (TIf _ i t e)   = "if \{pretty i} then \{pretty t} else \{pretty e}"

paren t = if isAtom t then pretty t else "(\{pretty t})"

appL (TApp _ t s) = "\{appL t} \{paren s}"
appL t            = paren t

export %inline
Interpolation Term where interpolate = pretty
