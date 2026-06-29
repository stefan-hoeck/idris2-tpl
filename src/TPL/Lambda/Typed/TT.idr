module TPL.Lambda.Typed.TT

import Data.Maybe
import Data.Nat
import public TPL.Env
import public TPL.Lambda.Typed.Term

%default total
%language ElabReflection

public export
PrimTpe : Prim -> Tpe
PrimTpe (PNat _)  = TNat
PrimTpe (PBool _) = TBool

public export
data STerm : (t : Tpe) -> (sc : Scope) -> Type where
  SVar   : ByteBounds -> (t : Tpe) -> (v : Var sc) -> STerm t sc
  SLam   :
       ByteBounds
    -> (v : VarName)
    -> (s : Tpe)
    -> STerm t (sc:<v)
    -> STerm (TFun s t) sc
  SApp   : ByteBounds -> STerm (TFun s t) sc -> STerm s sc -> STerm t sc
  SPrim  : ByteBounds -> (p : Prim) -> STerm (PrimTpe p) sc
  SIf    :
       ByteBounds
    -> (pred : STerm TBool sc)
    -> (fst  : STerm t sc)
    -> (snd  : STerm t sc)
    -> STerm t sc
  SFix   : ByteBounds -> STerm (TFun t t) sc -> STerm t sc
  SSucc  : ByteBounds -> STerm TNat sc -> STerm TNat sc
  SPred  : ByteBounds -> STerm TNat sc -> STerm TNat sc
  SIsZ   : ByteBounds -> STerm TNat sc -> STerm TBool sc

||| Top-level definitions
public export
record Def where
  constructor D
  type : Tpe
  term : STerm type [<]

export
restore : {sc : _} -> STerm t sc -> Term
restore (SVar b t $ V n _ p) = TVar b (getName sc n @{p})
restore (SApp b t s)         = TApp b (restore t) (restore s)
restore (SLam b x t y)       = TLam b x t (restore y)
restore (SPrim b p)          = TPrim b p
restore (SIf b i x y)        = TIf b (restore i) (restore x) (restore y)
restore (SFix b x)           = TApp b "fix" (restore x)
restore (SSucc b x)          = TApp b "succ" (restore x)
restore (SPred b x)          = TApp b "pred" (restore x)
restore (SIsZ b x)           = TApp b "iszero" (restore x)

--------------------------------------------------------------------------------
-- Handling Scope
--------------------------------------------------------------------------------

shiftImpl : GenShift (STerm t)
shiftImpl sol son (SVar b t x)   = SVar b t (genShift sol son x)
shiftImpl sol son (SApp b t s)   = SApp b (shiftImpl sol son t) (shiftImpl sol son s)
shiftImpl sol son (SLam b x t y) = SLam b x t (shiftImpl (suc sol) son y)
shiftImpl sol son (SPrim b p)    = SPrim b p
shiftImpl sol son (SIf b i t e)  = SIf b (shiftImpl sol son i) (shiftImpl sol son t) (shiftImpl sol son e)
shiftImpl sol son (SFix b x)     = SFix b (shiftImpl sol son x)
shiftImpl sol son (SSucc b x)    = SSucc b (shiftImpl sol son x)
shiftImpl sol son (SPred b x)    = SPred b (shiftImpl sol son x)
shiftImpl sol son (SIsZ b x)     = SIsZ b (shiftImpl sol son x)

export %inline
Shiftable (STerm t) where genShift = shiftImpl

strImpl : GenStrengthen (STerm t)
strImpl s t (SVar b p x)   = SVar b p <$> genStrengthen s t x
strImpl s t (SApp b x y)   = [| SApp (pure b) (strImpl s t x) (strImpl s t y) |]
strImpl s t (SLam b x p y) = SLam b x p <$> strImpl s (suc t) y
strImpl s t (SPrim b p)    = Just $ SPrim b p
strImpl s t (SIf b i x y)  = [| SIf (pure b) (strImpl s t i) (strImpl s t x) (strImpl s t y) |]
strImpl s t (SFix b x)     = SFix b <$> strImpl s t x
strImpl s t (SSucc b x)    = SSucc b <$> strImpl s t x
strImpl s t (SPred b x)    = SPred b <$> strImpl s t x
strImpl s t (SIsZ b x)     = SIsZ b <$> strImpl s t x

export %inline
Strengthenable (STerm t) where genStrengthen = strImpl

embedImpl : Embed (STerm t)
embedImpl (SVar b p x)    = SVar b p (embed x)
embedImpl (SApp b t s)    = SApp b (embedImpl t) (embedImpl s)
embedImpl (SLam b x p y)  = SLam b x p (embedImpl y)
embedImpl (SPrim b p)     = SPrim b p
embedImpl (SIf b i x y)   = SIf b (embedImpl i) (embedImpl x) (embedImpl y)
embedImpl (SFix b x)      = SFix b $ embedImpl x
embedImpl (SSucc b x)     = SSucc b $ embedImpl x
embedImpl (SPred b x)     = SPred b $ embedImpl x
embedImpl (SIsZ b x)      = SIsZ b $ embedImpl x

export %inline
Embeddable (STerm t) where embed = embedImpl

--------------------------------------------------------------------------------
-- Type Checking
--------------------------------------------------------------------------------

check :
     {found : _}
  -> (exp : Tpe)
  -> ByteBounds
  -> STerm found sc
  -> Either LamErr (STerm exp sc)
check exp bb t =
  case hdecEq exp found of
    Just0 prf => Right (rewrite prf in t)
    Nothing0  => typeErr bb exp found

parameters (env : Env Def)

  export
  typecheckAs :
       {sc : _}
    -> (t : Tpe)
    -> Local Tpe sc
    -> Term
    -> Either LamErr (STerm t sc)

  export
  typecheck :
       {sc : _}
    -> Local Tpe sc
    -> Term
    -> Either LamErr (t ** STerm t sc)
  typecheck loc (TVar b v) =
    case mkVar sc v of
      Just vr => let t := getVar vr loc in Right (t ** SVar b t vr)
      Nothing => case lookup v env of
        Just (D t ct) => Right $ (t ** embed ct)
        Nothing => bindErr b v
  typecheck loc (TApp b (TVar b2 "fix") arg)  = Prelude.do
    (TFun s t ** sarg) <- typecheck loc arg | (t ** _) => funErr arg t
    case hdecEq s t of
      Just0 p  => Right (t ** SFix b2 (replace {p = \x => STerm (TFun x t) sc} p sarg))
      Nothing0 => typeErr arg s t
  typecheck loc (TApp b fun arg)  = Prelude.do
    (TFun s t ** sfun) <- typecheck loc fun | (t ** _) => funErr fun t
    sarg <- typecheckAs s loc arg
    Right (t ** SApp b sfun sarg)
  typecheck loc (TLam b v t x)= Prelude.do
    (res ** sx) <- typecheck (loc:<t) x
    Right (TFun t res ** SLam b v t sx)
  typecheck loc (TPrim b p)   = Right $ (PrimTpe p ** SPrim b p)
  typecheck loc (TIf b i x y) = Prelude.do
    si <- typecheckAs TBool loc i
    (t ** sx) <- typecheck loc x
    sy <- typecheckAs t loc y
    Right (t ** SIf b si sx sy)

  typecheckAs t loc (TLam b v at z)  =
    case t of
      TFun eat ert => case hdecEq eat at of
        Nothing0 => typeErr b eat at
        Just0 _  => Prelude.do
          sz <- typecheckAs ert (loc:<eat) z
          Right (SLam b v eat sz)
      _ => unexpFunErr b t

  typecheckAs t loc (TApp b fun arg) = Prelude.do
    (TFun at rt ** sfun) <- typecheck loc fun | (t ** _) => funErr fun t
    sarg <- typecheckAs at loc arg
    check t b (SApp b sfun sarg)
  typecheckAs t loc (TIf b i x y)   = Prelude.do
    si <- typecheckAs TBool loc i
    sx <- typecheckAs t loc x
    sy <- typecheckAs t loc y
    Right (SIf b si sx sy)
  typecheckAs t loc trm = Prelude.do
    (ft ** strm) <- typecheck loc trm
    check t (cast trm) strm

  export
  definition : Term -> Either LamErr Def
  definition t = map (\(tpe ** trm) => D tpe trm) (typecheck [<] t)

--------------------------------------------------------------------------------
-- Evaluation
--------------------------------------------------------------------------------

export
subst :
     {sc : _}
  -> {t1 : _}
  -> Var sc
  -> STerm t1 sc
  -> STerm t sc
  -> STerm t sc
subst v s (SVar b t x)    =
  case v == x of
    -- strictly speaking, the hdecEq check should not be necessary
    -- but its a very small test, so to keep things simple, it
    -- stays for the time being
    True  => case hdecEq t t1 of
      Just0 prf => rewrite prf in s
      Nothing0  => SVar b t x
    False => SVar b t x
subst v s (SApp b t x)   = SApp b (subst v s t) (subst v s x)
subst v s (SLam b x p y) = SLam b x p $ subst (shift v) (shift s) y
subst v s (SPrim b p)    = SPrim b p
subst v s (SIf b i x y)  = SIf b (subst v s i) (subst v s x) (subst v s y)
subst v s (SFix b x)     = SFix b $ subst v s x
subst v s (SSucc b x)    = SSucc b $ subst v s x
subst v s (SPred b x)    = SPred b $ subst v s x
subst v s (SIsZ b x)     = SIsZ b $ subst v s x

isVal : STerm t sc -> Bool
isVal (SLam {})  = True
isVal (SPrim {}) = True
isVal _          = False

export
step : {sc : _} -> STerm t sc -> STerm t sc
step t@(SApp b fun@(SLam _ v tp sc) arg) =
  case isVal arg of
    True  => fromMaybe t $ strengthen (suc zero) $ subst zero (shift arg) sc
    False => SApp b fun (step arg)
step (SApp b fun arg) = SApp b (step fun) arg
step (SIf b pred fst snd) =
  case pred of
    SPrim _ (PBool True)  => fst
    SPrim _ (PBool False) => snd
    _                     => SIf b (step pred) fst snd
step t@(SFix b y)          =
  case y of
    SLam _ v tp sc   => fromMaybe t $ strengthen (suc zero) $ subst zero (shift t) sc
    _                => SFix b $ step y
step (SSucc b y)          =
  case y of
    SPrim b (PNat n) => SPrim b $ PNat (S n)
    _                => SSucc b $ step y
step (SPred b y)          =
  case y of
    SPrim b (PNat n) => SPrim b $ PNat (pred n)
    _                => SPred b $ step y
step (SIsZ b y)           =
  case y of
    SPrim b (PNat n) => SPrim b $ PBool (isZero n)
    _                => SIsZ b $ step y
step t = t

public export
data Value : (t : Tpe) -> (sc : Scope) -> Type where
  VPrim : (p : Prim) -> Value (PrimTpe p) sc
  VLam  :
       (v : VarName)
    -> (t1 : Tpe)
    -> STerm t2 (sc:<v)
    -> Value (TFun t1 t2) sc

export
toTerm : Value t sc -> STerm t sc
toTerm (VPrim p)     = SPrim NoBB p
toTerm (VLam v t sc) = SLam NoBB v t sc

export
{sc : _} -> Interpolation (Value t sc) where
  interpolate = interpolate . restore . toTerm

export
toValue : STerm t sc -> Maybe (Value t sc)
toValue (SLam x v s y) = Just (VLam v s y)
toValue (SPrim x p)    = Just (VPrim p)
toValue _              = Nothing

export covering
eval : {sc : _} -> STerm t sc -> Value t sc
eval trm =
  case toValue trm of
    Just v  => v
    Nothing => eval (step trm)
