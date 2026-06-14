module TPL.Lambda.Term

import Derive.Prelude

%default total
%language ElabReflection

public export
record Var where
  constructor V
  name : String

%runElab derive "Var" [Show,Eq,Ord,FromString,Semigroup,Monoid]

public export %inline
Interpolation Var where interpolate = name

public export
data Term : Type where
  TVar : (v : Var) -> Term -- a plain variable
  TLam : (v : Var) -> (sc : Term) -> Term -- variable and its scope
  TApp : (t,s : Term) -> Term -- function application

%runElab derive "Term" [Show,Eq]

public export %inline
FromString Term where fromString = TVar . fromString

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
