module TPL.Lambda.Typed.Eval

import Data.Maybe
import Data.Nat
import public TPL.Lambda.Typed.TT

%default total

public export
data VRecord : List (VarName, Tpe) -> (sc : Scope TTVar) -> Type

public export
data Value : (t : Tpe) -> (sc : Scope TTVar) -> Type where
  VPrim : (p : Prim) -> Value (PrimTpe p) sc
  VRec  : (r : VRecord ps sc) -> Value (TRec ps) sc
  VLam  :
       (v : BindName)
    -> (t1 : Tpe)
    -> STerm t2 (sc:<V v t1)
    -> Value (TFun t1 t2) sc

data VRecord : List (VarName, Tpe) -> (sc : Scope TTVar) -> Type where
  Nil  : VRecord [] sc
  (::) : (p : (VarName,Value t sc)) -> VRecord ps sc -> VRecord ((fst p, t)::ps) sc

export
getVField : IsField v ps t -> VRecord ps sc -> Value t sc
getVField IFZ     ((_,t)::_) = t
getVField (IFS x) (_::ps)    = getVField x ps

torec : VRecord ps sc -> SRecord ps sc

export
toTerm : Value t sc -> STerm t sc
toTerm (VPrim p)     = SPrim NoBB p
toTerm (VRec r)      = SRec NoBB (torec r)
toTerm (VLam v t sc) = SLam NoBB v t sc

torec []          = []
torec ((v,t)::ps) = (v,toTerm t) :: torec ps

export
{sc : _} -> Interpolation (Value t sc) where
  interpolate = interpolate . restore . toTerm

tovalrec : SRecord ps sc -> Maybe (VRecord ps sc)

export
toValue : STerm t sc -> Maybe (Value t sc)
toValue (SLam _ v s y)   = Just (VLam v s y)
toValue (SPrim _ p)      = Just (VPrim p)
toValue (SRec _ r)       = VRec <$> tovalrec r
toValue _                = Nothing

tovalrec [] = Just []
tovalrec ((v,t)::ps) =
 let Just vt := toValue t    | _ => Nothing
     Just vps := tovalrec ps | _ => Nothing
  in Just ((v,vt)::vps)

--------------------------------------------------------------------------------
-- Small-step Evaluation
--------------------------------------------------------------------------------

substRec :
     {sc : Scope TTVar}
  -> {t1 : TTVar}
  -> NVar t1 sc
  -> STerm (type t1) sc
  -> SRecord ps sc
  -> SRecord ps sc

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
subst v s (SApp b t x)      = SApp b (subst v s t) (subst v s x)
subst v s (SField b y p x)  = SField b y p (subst v s x)
subst v s (SLam b x p y)    = SLam b x p $ subst (shift v) (shift s) y
subst v s (SPrim b p)       = SPrim b p
subst v s (SRec b p)        = SRec b (substRec v s p)
subst v s (SIf b i x y)     = SIf b (subst v s i) (subst v s x) (subst v s y)
subst v s (SFix b x)        = SFix b $ subst v s x
subst v s (SSucc b x)       = SSucc b $ subst v s x
subst v s (SPred b x)       = SPred b $ subst v s x
subst v s (SIsZ b x)        = SIsZ b $ subst v s x

substRec v s [] = []
substRec v s ((x,y)::ps) = (x,subst v s y)::substRec v s ps

isValRec : SRecord ps sc -> Bool

isVal : STerm t sc -> Bool
isVal (SLam {})   = True
isVal (SPrim {})  = True
isVal (SRec _ ps) = isValRec ps
isVal _           = False

isValRec []          = True
isValRec ((v,t)::ps) = isVal t && isValRec ps

steprec : {sc : _} -> SRecord ps sc -> SRecord ps sc

export
step : {sc : _} -> STerm t sc -> STerm t sc
step t@(SApp b fun@(SLam _ v tp sc) arg) =
  case isVal arg of
    True  => fromMaybe t $ strengthen (suc zero) $ subst nzero (shift arg) sc
    False => SApp b fun (step arg)
step (SApp b fun arg) = SApp b (step fun) arg

step (SField b v p t) =
  case isVal t of
    True => case t of
      SRec _ ps => getField p ps
      _         => SField b v p t
    False => SField b v p (step t)

step (SIf b pred fst snd) =
  case pred of
    SPrim _ (PBool True)  => fst
    SPrim _ (PBool False) => snd
    _                     => SIf b (step pred) fst snd
step t@(SFix b y)          =
  case y of
    SLam _ v tp sc   => fromMaybe t $ strengthen (suc zero) $ subst nzero (shift t) sc
    _                => SFix b $ step y
step (SSucc b y)         =
  case y of
    SPrim b (PNat n) => SPrim b $ PNat (S n)
    _                => SSucc b $ step y
step (SPred b y)         =
  case y of
    SPrim b (PNat n) => SPrim b $ PNat (pred n)
    _                => SPred b $ step y
step (SIsZ b y)          =
  case y of
    SPrim b (PNat n) => SPrim b $ PBool (isZero n)
    _                => SIsZ b $ step y
step (SRec b ps)         = SRec b (steprec ps)
step t = t

steprec [] = []
steprec ((v,t)::ps) =
  case isVal t of
    True  => (v,t) :: steprec ps
    False => (v,step t) :: ps

export covering
eval : {sc : _} -> STerm t sc -> Value t sc
eval trm =
  case toValue trm of
    Just v  => v
    Nothing => eval (step trm)

--------------------------------------------------------------------------------
-- Big-step Evaluation
--------------------------------------------------------------------------------

covering
bigrec : {sc : _} -> SRecord ps sc -> SRecord ps sc

export covering
bigEval : {sc : _} -> STerm t sc -> STerm t sc
bigEval (SField b v y z) =
  case bigEval z of
    SRec _ r => getField y r
    t        => SField b v y t
bigEval (SApp b y z) =
 let vz := bigEval z
     vy := bigEval y
  in case vy of
       SLam _ v _ scope =>
         bigEval $ fromMaybe (SApp b vy vz) $
           strengthen (suc zero) $ subst nzero (shift vz) scope
       _                => SApp b vy vz
bigEval (SRec b y) = SRec b (bigrec y)
bigEval (SIf b pred fst snd) =
  case bigEval pred of
    SPrim _ (PBool True)  => bigEval fst
    SPrim _ (PBool False) => bigEval snd
    t                   => SIf b t fst snd
bigEval t@(SFix b y) =
 let vy := bigEval y
  in case vy of
       SLam _ v tp sc   =>
         bigEval $ fromMaybe t $ strengthen (suc zero) $ subst nzero (shift t) sc
       _                => SFix b vy
bigEval (SSucc b y) =
 let SPrim b (PNat n) := bigEval y | t => SSucc b t
  in SPrim b (PNat $ S n)
bigEval (SPred b y) =
 let SPrim b (PNat n) := bigEval y | t => SPred b t
  in SPrim b (PNat $ pred n)
bigEval (SIsZ b y) =
 let SPrim b (PNat n) := bigEval y | t => SIsZ b t
  in SPrim b (PBool $ isZero n)
bigEval t = t

bigrec [] = []
bigrec ((v,t)::ps) = (v,bigEval t)::bigrec ps
