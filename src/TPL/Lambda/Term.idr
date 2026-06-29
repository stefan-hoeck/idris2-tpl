module TPL.Lambda.Term

import Derive.Prelude
import TPL.Env
import TPL.Name.Var
import Text.ByteBounds
import public TPL.Error

%default total
%language ElabReflection

public export
data Prim : Type where
  PNat  : Nat -> Prim
  PBool : Bool -> Prim

%runElab derive "Prim" [Show,Eq]

public export
0 TpeErr : Type
TpeErr = TplErr Void

public export
0 LamErr : Type
LamErr = BBErr TpeErr

export
Interpolation Prim where
  interpolate (PNat v)  = show v
  interpolate (PBool v) = show v

public export
data Term : Type where
  TVar   : ByteBounds -> (v : VarName) -> Term -- a plain variable
  TLam   : ByteBounds -> (v : VarName) -> (sc : Term) -> Term -- variable and its scope
  TApp   : ByteBounds -> (t,s : Term) -> Term -- function application
  TPrim  : ByteBounds -> Prim -> Term -- primiive values
  TIf    : ByteBounds -> (i,t,e : Term) -> Term -- if then else

%runElab derive "Term" [Show,Eq]

public export %inline
FromString Term where fromString = TVar NoBB . fromString

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

export
Cast Term ByteBounds where
  cast (TVar x _)    = x
  cast (TLam x _ _)  = x
  cast (TApp x _ _)  = x
  cast (TPrim x _)   = x
  cast (TIf x _ _ _) = x

export
nat : ByteBounds -> Nat -> Term
nat bb n = TPrim bb (PNat n)

export %inline
int : ByteBounded Integer -> Term
int (B i bb) = nat bb $ cast i

export %inline
bool : ByteBounded Bool -> Term
bool (B b bb) = TPrim bb (PBool b)

export
appAll : Term -> List Term -> Term
appAll s []      = s
appAll s (t::ts) = appAll (TApp (cast s <+> cast t) s t) ts

export %inline
appAllSnoc : Term -> SnocList Term -> Term
appAllSnoc s = appAll s . (<>>[])

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
pretty (TVar _ v)    = v.name
pretty (TLam _ v sc) = "λ\{v}. \{pretty sc}"
pretty (TApp _ t s)  = "\{appL t} \{paren s}"
pretty (TPrim _ p)   = interpolate p
pretty (TIf _ i t e) = "if \{pretty i} then \{pretty t} else \{pretty e}"

paren t = if isAtom t then pretty t else "(\{pretty t})"

appL (TApp _ t s) = "\{appL t} \{paren s}"
appL t            = paren t

export %inline
Interpolation Term where interpolate = pretty

--------------------------------------------------------------------------------
-- Scoped Term
--------------------------------------------------------------------------------

public export
data STerm : (sc : Scope VarName) -> Type where
  SVar   : {nm : _} -> ByteBounds -> (v : NVar nm sc) -> STerm sc
  SLam   : ByteBounds -> (v : VarName) -> STerm (sc:<v) -> STerm sc
  SApp   : ByteBounds -> (t,s : STerm sc) -> STerm sc
  SPrim  : ByteBounds -> Prim -> STerm sc
  SIf    : ByteBounds -> (i,t,e : STerm sc) -> STerm sc
  SSucc  : ByteBounds -> STerm sc -> STerm sc
  SPred  : ByteBounds -> STerm sc -> STerm sc
  SIsZ   : ByteBounds -> STerm sc -> STerm sc

public export
0 ClosedTerm : Type
ClosedTerm = STerm [<]

shiftImpl : GenShift STerm
shiftImpl sol son (SVar b x)    = SVar b (genShift sol son x)
shiftImpl sol son (SApp b t s)  = SApp b (shiftImpl sol son t) (shiftImpl sol son s)
shiftImpl sol son (SLam b x y)  = SLam b x (shiftImpl (suc sol) son y)
shiftImpl sol son (SPrim b p)   = SPrim b p
shiftImpl sol son (SIf b i t e) = SIf b (shiftImpl sol son i) (shiftImpl sol son t) (shiftImpl sol son e)
shiftImpl sol son (SSucc b x)   = SSucc b (shiftImpl sol son x)
shiftImpl sol son (SPred b x)   = SPred b (shiftImpl sol son x)
shiftImpl sol son (SIsZ b x)    = SIsZ b (shiftImpl sol son x)

export %inline
Shiftable VarName STerm where genShift = shiftImpl

strImpl : GenStrengthen STerm
strImpl s t (SVar b x)    = SVar b <$> genStrengthen s t x
strImpl s t (SApp b x y)  = [| SApp (pure b) (strImpl s t x) (strImpl s t y) |]
strImpl s t (SLam b x y)  = SLam b x <$> strImpl s (suc t) y
strImpl s t (SPrim b p)   = Just $ SPrim b p
strImpl s t (SIf b i x y) = [| SIf (pure b) (strImpl s t i) (strImpl s t x) (strImpl s t y) |]
strImpl s t (SSucc b x)   = SSucc b <$> strImpl s t x
strImpl s t (SPred b x)   = SPred b <$> strImpl s t x
strImpl s t (SIsZ b x)    = SIsZ b <$> strImpl s t x

export %inline
Strengthenable VarName STerm where genStrengthen = strImpl

embedImpl : Embed STerm
embedImpl (SVar b x)      = SVar b (embed x)
embedImpl (SApp b t s)    = SApp b (embedImpl t) (embedImpl s)
embedImpl (SLam b x y)    = SLam b x (embedImpl y)
embedImpl (SPrim b p)     = SPrim b p
embedImpl (SIf b i x y)   = SIf b (embedImpl i) (embedImpl x) (embedImpl y)
embedImpl (SSucc b x)     = SSucc b $ embedImpl x
embedImpl (SPred b x)     = SPred b $ embedImpl x
embedImpl (SIsZ b x)      = SIsZ b $ embedImpl x

export %inline
Embeddable VarName STerm where embed = embedImpl

parameters (env : Env ClosedTerm)

  export
  scoped : {sc : _} -> Term -> Either LamErr (STerm sc)
  scoped (TVar b v)   =
    case findNVar (v==) sc of
      Just (nm ** vr) => Right (SVar b vr)
      Nothing => case lookup v env of
        Just ct => Right $ embed ct
        Nothing => bindErr b v
  scoped (TApp b t s)  = [| SApp (pure b) (scoped t) (scoped s) |]
  scoped (TLam b v x)  = SLam b v <$> scoped x
  scoped (TPrim b p)   = Right $ SPrim b p
  scoped (TIf b i x y) = [|SIf (pure b) (scoped i) (scoped x) (scoped y) |]

  export %inline
  closed : Term -> Either LamErr (STerm [<])
  closed = scoped

export
restore : {sc : Scope VarName} -> STerm sc -> Term
restore (SVar {nm} b _) = TVar b nm
restore (SApp b t s)    = TApp b (restore t) (restore s)
restore (SLam b x y)    = TLam b x (restore y)
restore (SPrim b p)     = TPrim b p
restore (SIf b i x y)   = TIf b (restore i) (restore x) (restore y)
restore (SSucc b x)     = TApp b "succ" (restore x)
restore (SPred b x)     = TApp b "pred" (restore x)
restore (SIsZ b x)      = TApp b "iszero" (restore x)

export
subst : {sc : _} -> {n : _} -> (0 v : NVar n sc) -> STerm sc -> STerm sc -> STerm sc
subst v s (SVar {nm} b x) = if nm == n then s else SVar b x
subst v s (SApp b t x)    = SApp b (subst v s t) (subst v s x)
subst v s (SLam b x y)    = SLam b x $ subst (shift v) (shift s) y
subst v s (SPrim b p)     = SPrim b p
subst v s (SIf b i x y)   = SIf b (subst v s i) (subst v s x) (subst v s y)
subst v s (SSucc b x)     = SSucc b $ subst v s x
subst v s (SPred b x)     = SPred b $ subst v s x
subst v s (SIsZ b x)      = SIsZ b $ subst v s x

--------------------------------------------------------------------------------
-- Evaluation
--------------------------------------------------------------------------------

isVal : STerm sc -> Bool
isVal (SPrim {}) = True
isVal (SLam {})  = True
isVal t          = False

export
step : {sc : _} -> STerm sc -> Maybe (STerm sc)
step trm =
  case trm of
    SApp b (SLam bl x s) t =>
      case isVal t of
        True  => strengthen (suc zero) $ subst nzero (shift t) s
        False => SApp b (SLam bl x s) <$> step t
    SApp b t s =>
      case step t of
        Just t2 => Just (SApp b t2 s)
        Nothing => SApp b t <$> step s
    SSucc b (SPrim _ $ PNat n) => Just (SPrim b (PNat $ S n))
    SPred b (SPrim _ $ PNat n) => Just (SPrim b (PNat $ pred n))
    SIsZ b  (SPrim _ $ PNat n) => Just (SPrim b $ PBool $ isZero n)
    SPred b t => SPred b <$> step t
    SSucc b t => SSucc b <$> step t
    SIsZ b t  => SIsZ b <$> step t
    SIf b (SPrim _ $ PBool v) y z => Just $ if v then y else z
    SIf b x y z => (\x2 => SIf b x2 y z) <$> step x
    _ => Nothing

export covering
eval : {sc : _} -> STerm sc -> STerm sc
eval t =
  case step t of
    Nothing => t
    Just t2 => eval t2

export %inline
{sc : _} -> Interpolation (STerm sc) where interpolate t = "\{restore t}"
