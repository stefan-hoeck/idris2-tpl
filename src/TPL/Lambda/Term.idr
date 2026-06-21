module TPL.Lambda.Term

import TPL.Name.Var
import Derive.Prelude

%default total
%language ElabReflection

public export
data Term : Type where
  TVar : (v : VarName) -> Term -- a plain variable
  TLam : (v : VarName) -> (sc : Term) -> Term -- variable and its scope
  TApp : (t,s : Term) -> Term -- function application

%runElab derive "Term" [Show,Eq]

public export %inline
FromString Term where fromString = TVar . fromString

export
appAll : Term -> List Term -> Term
appAll s []      = s
appAll s (t::ts) = appAll (TApp s t) ts

export %inline
appAllSnoc : Term -> SnocList Term -> Term
appAllSnoc s = appAll s . (<>>[])

--------------------------------------------------------------------------------
-- Pretty Printing
--------------------------------------------------------------------------------

appL, appR : Term -> String

pretty : Term -> String
pretty (TVar v)    = v.name
pretty (TLam v sc) = "λ\{v}. \{pretty sc}"
pretty (TApp t s)  = "\{appL t} \{appR s}"

appL l@(TLam {}) = "(\{pretty l})"
appL t           = pretty t

appR (TVar v) = v.name
appR t        = "(\{pretty t})"

export %inline
Interpolation Term where interpolate = pretty

--------------------------------------------------------------------------------
-- Scoped Term
--------------------------------------------------------------------------------

public export
data STerm : (sc : Scope) -> Type where
  SVar : Var sc -> STerm sc
  SLam : (x : VarName) -> STerm (sc:<x) -> STerm sc
  SApp : (t,s : STerm sc) -> STerm sc

export
scoped : {sc : _} -> Term -> Maybe (STerm sc)
scoped (TVar v)   = SVar <$> mkVar sc v
scoped (TLam v x) = SLam v <$> scoped x
scoped (TApp t s) = [| SApp (scoped t) (scoped s) |]

export %inline
closed : Term -> Maybe (STerm [<])
closed = scoped

--------------------------------------------------------------------------------
-- Pretty Printing
--------------------------------------------------------------------------------

sappL, sappR : {sc : _} -> STerm sc -> String

spretty : {sc : _} -> STerm sc -> String
spretty (SVar v)    = interpolate v
spretty (SLam v sc) = "λ\{v}. \{spretty sc}"
spretty (SApp t s)  = "\{sappL t} \{sappR s}"

sappL l@(SLam {}) = "(\{spretty l})"
sappL t           = spretty t

sappR (SVar v) = interpolate v
sappR t        = "(\{spretty t})"

export %inline
{sc : _} -> Interpolation (STerm sc) where interpolate = spretty
