module TPL.Lambda.Term

import TPL.Env
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
  SApp : (t,s : STerm sc) -> STerm sc
  SLam : (x : VarName) -> STerm (sc:<x) -> STerm sc

public export
0 ClosedTerm : Type
ClosedTerm = STerm [<]

shiftImpl : GenShift STerm
shiftImpl sol son (SVar x)   = SVar (genShift sol son x)
shiftImpl sol son (SApp t s) = SApp (shiftImpl sol son t) (shiftImpl sol son s)
shiftImpl sol son (SLam x y) = SLam x (shiftImpl (suc sol) son y)

export %inline
Shiftable STerm where genShift = shiftImpl

strImpl : GenStrengthen STerm
strImpl s t (SVar x)   = SVar <$> genStrengthen s t x
strImpl s t (SApp x y) = [| SApp (strImpl s t x) (strImpl s t y) |]
strImpl s t (SLam x y) = SLam x <$> strImpl s (suc t) y

export %inline
Strengthenable STerm where genStrengthen = strImpl

embedImpl : Embed STerm
embedImpl (SVar x)   = SVar (embed x)
embedImpl (SApp t s) = SApp (embedImpl t) (embedImpl s)
embedImpl (SLam x y) = SLam x (embedImpl y)

export %inline
Embeddable STerm where embed = embedImpl

parameters (env : Env ClosedTerm)

  export
  scoped : {sc : _} -> Term -> Either String (STerm sc)
  scoped (TVar v)   =
    case mkVar sc v of
      Just vr => Right (SVar vr)
      Nothing => case lookup v env of
        Just ct => Right $ embed ct
        Nothing => Left "unknown variable: \{v}"
  scoped (TApp t s) = [| SApp (scoped t) (scoped s) |]
  scoped (TLam v x) = SLam v <$> scoped x

  export %inline
  closed : Term -> Either String (STerm [<])
  closed = scoped

export
restore : {sc : Scope} -> STerm sc -> Term
restore (SVar $ V n _ p) = TVar (getName sc n @{p})
restore (SApp t s)       = TApp (restore t) (restore s)
restore (SLam x y)       = TLam x (restore y)

export
subst : {sc : _} -> Var sc -> STerm sc -> STerm sc -> STerm sc
subst v s (SVar x)   = if v == x then s else SVar x
subst v s (SApp t x) = SApp (subst v s t) (subst v s x)
subst v s (SLam x y) = SLam x $ subst (shift v) (shift s) y

--------------------------------------------------------------------------------
-- Evaluation
--------------------------------------------------------------------------------

export
step : {sc : _} -> STerm sc -> Maybe (STerm sc)
step (SApp (SLam x t) s@(SLam {})) =
  strengthen (suc zero) $ subst zero (shift s) t
step (SApp t s) =
  case step t of
    Just t2 => Just (SApp t2 s)
    Nothing => SApp t <$> step s
step _ = Nothing

export covering
eval : {sc : _} -> STerm sc -> STerm sc
eval t =
  case step t of
    Nothing => t
    Just t2 => eval t2

--------------------------------------------------------------------------------
-- Pretty Printing
--------------------------------------------------------------------------------

sappL, sappR : {sc : _} -> STerm sc -> String

spretty : {sc : _} -> STerm sc -> String
spretty (SVar v)    = interpolate v
spretty (SApp t s)  = "\{sappL t} \{sappR s}"
spretty (SLam v sc) = "λ\{v}. \{spretty sc}"

sappL l@(SLam {}) = "(\{spretty l})"
sappL t           = spretty t

sappR (SVar v) = interpolate v
sappR t        = "(\{spretty t})"

export %inline
{sc : _} -> Interpolation (STerm sc) where interpolate = spretty
