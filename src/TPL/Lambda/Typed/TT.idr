module TPL.Lambda.Typed.TT

import Data.Maybe
import Data.Nat
import public TPL.Env
import public TPL.Lambda.Typed.Term

%default total
%language ElabReflection

public export
record TTVar where
  constructor V
  name : VarName
  type : Tpe

public export
PrimTpe : Prim -> Tpe
PrimTpe (PNat _)  = TNat
PrimTpe (PBool _) = TBool

public export
data STerm : (t : Tpe) -> (sc : Scope TTVar) -> Type where
  SVar   : {v : _} -> ByteBounds -> NVar v sc -> STerm (type v) sc
  SLam   :
       ByteBounds
    -> (v : VarName)
    -> (s : Tpe)
    -> STerm t (sc:<V v s)
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
restore (SVar {v} b _) = TVar b v.name
restore (SApp b t s)   = TApp b (restore t) (restore s)
restore (SLam b x t y) = TLam b x t (restore y)
restore (SPrim b p)    = TPrim b p
restore (SIf b i x y)  = TIf b (restore i) (restore x) (restore y)
restore (SFix b x)     = TApp b "fix" (restore x)
restore (SSucc b x)    = TApp b "succ" (restore x)
restore (SPred b x)    = TApp b "pred" (restore x)
restore (SIsZ b x)     = TApp b "iszero" (restore x)

--------------------------------------------------------------------------------
-- Handling Scope
--------------------------------------------------------------------------------

shiftImpl : GenShift (STerm t)
shiftImpl sol son (SVar b x)     = SVar b (genShift sol son x)
shiftImpl sol son (SApp b t s)   = SApp b (shiftImpl sol son t) (shiftImpl sol son s)
shiftImpl sol son (SLam b x t y) = SLam b x t (shiftImpl (suc sol) son y)
shiftImpl sol son (SPrim b p)    = SPrim b p
shiftImpl sol son (SIf b i t e)  = SIf b (shiftImpl sol son i) (shiftImpl sol son t) (shiftImpl sol son e)
shiftImpl sol son (SFix b x)     = SFix b (shiftImpl sol son x)
shiftImpl sol son (SSucc b x)    = SSucc b (shiftImpl sol son x)
shiftImpl sol son (SPred b x)    = SPred b (shiftImpl sol son x)
shiftImpl sol son (SIsZ b x)     = SIsZ b (shiftImpl sol son x)

export %inline
Shiftable TTVar (STerm t) where genShift = shiftImpl

strImpl : GenStrengthen (STerm t)
strImpl s t (SVar b x)     = SVar b <$> genStrengthen s t x
strImpl s t (SApp b x y)   = [| SApp (pure b) (strImpl s t x) (strImpl s t y) |]
strImpl s t (SLam b x p y) = SLam b x p <$> strImpl s (suc t) y
strImpl s t (SPrim b p)    = Just $ SPrim b p
strImpl s t (SIf b i x y)  = [| SIf (pure b) (strImpl s t i) (strImpl s t x) (strImpl s t y) |]
strImpl s t (SFix b x)     = SFix b <$> strImpl s t x
strImpl s t (SSucc b x)    = SSucc b <$> strImpl s t x
strImpl s t (SPred b x)    = SPred b <$> strImpl s t x
strImpl s t (SIsZ b x)     = SIsZ b <$> strImpl s t x

export %inline
Strengthenable TTVar (STerm t) where genStrengthen = strImpl

embedImpl : Embed (STerm t)
embedImpl (SVar b x)      = SVar b (embed x)
embedImpl (SApp b t s)    = SApp b (embedImpl t) (embedImpl s)
embedImpl (SLam b x p y)  = SLam b x p (embedImpl y)
embedImpl (SPrim b p)     = SPrim b p
embedImpl (SIf b i x y)   = SIf b (embedImpl i) (embedImpl x) (embedImpl y)
embedImpl (SFix b x)      = SFix b $ embedImpl x
embedImpl (SSucc b x)     = SSucc b $ embedImpl x
embedImpl (SPred b x)     = SPred b $ embedImpl x
embedImpl (SIsZ b x)      = SIsZ b $ embedImpl x

export %inline
Embeddable TTVar (STerm t) where embed = embedImpl

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
  typecheckAs : {sc : _} -> (t : Tpe) -> Term -> Either LamErr (STerm t sc)

  export
  typecheck : {sc : _} -> Term -> Either LamErr (t ** STerm t sc)
  typecheck (TVar b v) =
    case findNVar ((v ==) . name) sc of
      Just (t ** nv) => Right (_ ** SVar b nv)
      Nothing => case lookup v env of
        Just (D t ct) => Right $ (t ** embed ct)
        Nothing => bindErr b v
  typecheck (TApp b (TVar b2 "fix") arg)  = Prelude.do
    (TFun s t ** sarg) <- typecheck arg | (t ** _) => funErr arg t
    case hdecEq s t of
      Just0 p  => Right (t ** SFix b2 (replace {p = \x => STerm (TFun x t) sc} p sarg))
      Nothing0 => typeErr arg s t
  typecheck (TApp b fun arg)  = Prelude.do
    (TFun s t ** sfun) <- typecheck fun | (t ** _) => funErr fun t
    sarg <- typecheckAs s arg
    Right (t ** SApp b sfun sarg)
  typecheck (TLam b v t x)= Prelude.do
    (res ** sx) <- typecheck x
    Right (TFun t res ** SLam b v t sx)
  typecheck (TPrim b p)   = Right $ (PrimTpe p ** SPrim b p)
  typecheck (TIf b i x y) = Prelude.do
    si <- typecheckAs TBool i
    (t ** sx) <- typecheck x
    sy <- typecheckAs t y
    Right (t ** SIf b si sx sy)

  typecheckAs t (TLam b v at z)  =
    case t of
      TFun eat ert => case hdecEq eat at of
        Nothing0 => typeErr b eat at
        Just0 _  => Prelude.do
          sz <- typecheckAs ert z
          Right (SLam b v eat sz)
      _ => unexpFunErr b t

  typecheckAs t (TApp b fun arg) = Prelude.do
    (TFun at rt ** sfun) <- typecheck fun | (t ** _) => funErr fun t
    sarg <- typecheckAs at arg
    check t b (SApp b sfun sarg)
  typecheckAs t (TIf b i x y)   = Prelude.do
    si <- typecheckAs TBool i
    sx <- typecheckAs t x
    sy <- typecheckAs t y
    Right (SIf b si sx sy)
  typecheckAs t trm = Prelude.do
    (ft ** strm) <- typecheck trm
    check t (cast trm) strm

  export
  definition : Term -> Either LamErr Def
  definition t = map (\(tpe ** trm) => D tpe trm) (typecheck t)

--------------------------------------------------------------------------------
-- Evaluation
--------------------------------------------------------------------------------

export
subst :
     {sc : Scope TTVar}
  -> {t1 : TTVar}
  -> NVar t1 sc
  -> STerm (type t1) sc
  -> STerm t sc
  -> STerm t sc
subst v s (SVar b x)    =
  case sameNVar x v of
    Just0 prf => rewrite cong type prf in s
    Nothing0  => SVar b x
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
    True  => fromMaybe t $ strengthen (suc zero) $ subst nzero (shift arg) sc
    False => SApp b fun (step arg)
step (SApp b fun arg) = SApp b (step fun) arg
step (SIf b pred fst snd) =
  case pred of
    SPrim _ (PBool True)  => fst
    SPrim _ (PBool False) => snd
    _                     => SIf b (step pred) fst snd
step t@(SFix b y)          =
  case y of
    SLam _ v tp sc   => fromMaybe t $ strengthen (suc zero) $ subst nzero (shift t) sc
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
data Value : (t : Tpe) -> (sc : Scope TTVar) -> Type where
  VPrim : (p : Prim) -> Value (PrimTpe p) sc
  VLam  :
       (v : VarName)
    -> (t1 : Tpe)
    -> STerm t2 (sc:<V v t1)
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
