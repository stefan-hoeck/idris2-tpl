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
  name : BindName
  type : Tpe

public export
PrimTpe : Prim -> Tpe
PrimTpe (PNat _)  = TNat
PrimTpe (PBool _) = TBool
PrimTpe PUnit     = TUnit

public export
data SRecord : List (VarName, Tpe) -> (sc : Scope TTVar) -> Type

public export
data STerm : (t : Tpe) -> (sc : Scope TTVar) -> Type where
  SVar   : {n : _} -> {t : _} -> ByteBounds -> NVar (V (NM n) t) sc -> STerm t sc
  SField :
       ByteBounds
    -> (v : ByteBounded VarName)
    -> IsField v.val ps t
    -> STerm (TRec ps) sc
    -> STerm t sc
  SLam   :
       ByteBounds
    -> (v : BindName)
    -> (s : Tpe)
    -> STerm t (sc:<V v s)
    -> STerm (TFun s t) sc
  SApp   : ByteBounds -> STerm (TFun s t) sc -> STerm s sc -> STerm t sc
  SPrim  : ByteBounds -> (p : Prim) -> STerm (PrimTpe p) sc
  SRec   : ByteBounds -> SRecord ps sc -> STerm (TRec ps) sc
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

data SRecord : List (VarName, Tpe) -> (sc : Scope TTVar) -> Type where
  Nil  : SRecord [] sc
  (::) : (p : (VarName,STerm t sc)) -> SRecord ps sc -> SRecord ((fst p, t) :: ps) sc

getField : IsField v ps t -> SRecord ps sc -> STerm t sc
getField IFZ     ((_,t)::_) = t
getField (IFS x) (_::ps)    = getField x ps

||| Top-level definitions
public export
data Entry : Type where
  Def : (type : Tpe) -> (term : STerm type [<]) -> Entry
  Dec : (type : Tpe) -> Entry
  Als : (type : Tpe) -> Entry

restoreRec :
     {sc : _}
  -> ByteBounds
  -> SnocList (VarName,Term)
  -> SRecord ps sc
  -> Term

export
restore : {sc : _} -> STerm t sc -> Term
restore (SVar {n} b _)   = TVar b n
restore (SField b v _ t) = TField b (restore t) v
restore (SApp b t s)     = TApp b (restore t) (restore s)
restore (SLam b x t y)   = TLam b x (cast t) (restore y)
restore (SPrim b p)      = TPrim b p
restore (SRec b r)       = restoreRec b [<] r
restore (SIf b i x y)    = TIf b (restore i) (restore x) (restore y)
restore (SFix b x)       = TApp b "fix" (restore x)
restore (SSucc b x)      = TApp b "succ" (restore x)
restore (SPred b x)      = TApp b "pred" (restore x)
restore (SIsZ b x)       = TApp b "iszero" (restore x)

restoreRec b sp [] = TRec b (sp <>> [])
restoreRec b sp ((v,t)::ps) = restoreRec b (sp:<(v,restore t)) ps

--------------------------------------------------------------------------------
-- Handling Scope
--------------------------------------------------------------------------------

shiftRec : GenShift (SRecord ps)

shiftImpl : GenShift (STerm t)
shiftImpl sol son (SVar b x)       = SVar b (genShift sol son x)
shiftImpl sol son (SField b v p x) = SField b v p (shiftImpl sol son x)
shiftImpl sol son (SApp b t s)     = SApp b (shiftImpl sol son t) (shiftImpl sol son s)
shiftImpl sol son (SLam b x t y)   = SLam b x t (shiftImpl (suc sol) son y)
shiftImpl sol son (SPrim b p)      = SPrim b p
shiftImpl sol son (SRec b p)       = SRec b (shiftRec sol son p)
shiftImpl sol son (SIf b i t e)    = SIf b (shiftImpl sol son i) (shiftImpl sol son t) (shiftImpl sol son e)
shiftImpl sol son (SFix b x)       = SFix b (shiftImpl sol son x)
shiftImpl sol son (SSucc b x)      = SSucc b (shiftImpl sol son x)
shiftImpl sol son (SPred b x)      = SPred b (shiftImpl sol son x)
shiftImpl sol son (SIsZ b x)       = SIsZ b (shiftImpl sol son x)

shiftRec sol son []          = []
shiftRec sol son ((v,t)::ps) = (v,shiftImpl sol son t) :: shiftRec sol son ps

export %inline
Shiftable TTVar (STerm t) where genShift = shiftImpl

strRec : GenStrengthen (SRecord ps)

strImpl : GenStrengthen (STerm t)
strImpl s t (SVar b x)       = SVar b <$> genStrengthen s t x
strImpl s t (SField b v p x) = SField b v p <$> strImpl s t x
strImpl s t (SApp b x y)     = [| SApp (pure b) (strImpl s t x) (strImpl s t y) |]
strImpl s t (SLam b x p y)   = SLam b x p <$> strImpl s (suc t) y
strImpl s t (SPrim b p)      = Just $ SPrim b p
strImpl s t (SRec b p)       = SRec b <$> strRec s t p
strImpl s t (SIf b i x y)    = [| SIf (pure b) (strImpl s t i) (strImpl s t x) (strImpl s t y) |]
strImpl s t (SFix b x)       = SFix b <$> strImpl s t x
strImpl s t (SSucc b x)      = SSucc b <$> strImpl s t x
strImpl s t (SPred b x)      = SPred b <$> strImpl s t x
strImpl s t (SIsZ b x)       = SIsZ b <$> strImpl s t x

strRec s t [] = Just []
strRec s t ((v,r)::ps) =
  let Just sr  := strImpl s t r | _ => Nothing
      Just sps := strRec s t ps | _ => Nothing
   in Just $ (v,sr)::sps

export %inline
Strengthenable TTVar (STerm t) where genStrengthen = strImpl

embedRec : Embed (SRecord ps)

embedImpl : Embed (STerm t)
embedImpl (SVar b x)         = SVar b (embed x)
embedImpl (SField b v p x)   = SField b v p (embedImpl x)
embedImpl (SApp b t s)       = SApp b (embedImpl t) (embedImpl s)
embedImpl (SLam b x p y)     = SLam b x p (embedImpl y)
embedImpl (SPrim b p)        = SPrim b p
embedImpl (SRec b p)         = SRec b (embedRec p)
embedImpl (SIf b i x y)      = SIf b (embedImpl i) (embedImpl x) (embedImpl y)
embedImpl (SFix b x)         = SFix b $ embedImpl x
embedImpl (SSucc b x)        = SSucc b $ embedImpl x
embedImpl (SPred b x)        = SPred b $ embedImpl x
embedImpl (SIsZ b x)         = SIsZ b $ embedImpl x

embedRec [] = []
embedRec ((v,t)::ps) = (v,embedImpl t) :: embedRec ps

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

fun : (0 prf : s === t) -> STerm (TFun s t) sc -> STerm (TFun t t) sc
fun Refl x = x

parameters (env : Env Entry)
  resolvePairs :
       SnocList (VarName,Tpe)
    -> List (VarName,RawTpe)
    -> Either LamErr Tpe

  export
  resolveTpe : RawTpe -> Either LamErr Tpe
  resolveTpe (PVar b v)   =
    case lookup v env of
      Just (Als tpe) => Right tpe
      _              => unknown b v
  resolveTpe (PFun b y z) = [| TFun (resolveTpe y) (resolveTpe z) |]
  resolveTpe (PRec _ ps)  = resolvePairs [<] ps

  resolvePairs sp []          = Right (TRec $ sp <>> [])
  resolvePairs sp ((v,t)::ps) =
    case resolveTpe t of
      Left x  => Left x
      Right x => resolvePairs (sp:<(v,x)) ps

  export
  typecheck : {sc : _} -> Term -> Either LamErr (t ** STerm t sc)

  tcrec : {sc : _} -> List (VarName,Term) -> Either LamErr (ps ** SRecord ps sc)
  tcrec []          = Right (_ ** [])
  tcrec ((v,t)::ps) = Prelude.do
    (ht ** h) <- typecheck t
    (tt ** pt) <- tcrec ps
    Right (_ ** ((v,h)::pt))

  export
  typecheckAs : {sc : _} -> (t : Tpe) -> Term -> Either LamErr (STerm t sc)
  typecheckAs t (TVar b v) =
    case findNVar ((NM v ==) . name) sc of
      Just (V (NM n) tp ** nv) => check t b (SVar b nv)
      _                        => case lookup v env of
        Just (Def _ ct) => check t b (embed ct)
        _               => bindErr b v

  typecheckAs t (TField b x v) = Prelude.do
    (TRec ps ** x2) <- typecheck x | (t ** _) => notField v t
    case isField v.val ps of
      Just (s ** prf) => check t b (SField b v prf x2)
      Nothing         => notField v (TRec ps)

  typecheckAs t (TLam b v rt scope)   = Prelude.do
    tpe <- resolveTpe rt
    case t of
      TFun eat ert => case hdecEq eat tpe of
        Nothing0 => typeErr rt eat tpe
        Just0 _  => Prelude.do
            sscope <- typecheckAs ert scope
            Right (SLam b v eat sscope)
      _ => unexpFunErr b t

  typecheckAs t (TApp b (TVar b2 (VN "fix")) arg) = Prelude.do
    sarg <- typecheckAs (TFun t t) arg
    Right (SFix b2 sarg)

  typecheckAs t (TApp b fun arg) = Prelude.do
    (ta ** sarg) <- typecheck arg
    sfun <- typecheckAs (TFun ta t) fun
    Right (SApp b sfun sarg)

  typecheckAs t (TPrim b y)    = check t b (SPrim b y)

  typecheckAs t (TRec b y)     = Prelude.do
    (ps ** r) <- tcrec y
    check t b (SRec b r)

  typecheckAs t (TIf b i y e)  = Prelude.do
    si <- typecheckAs TBool i
    sy <- typecheckAs t y
    se <- typecheckAs t e
    Right (SIf b si sy se)

  typecheck (TVar b v)     =
    case findNVar ((NM v ==) . name) sc of
      Just (V (NM n) tp ** nv) => Right (_ ** SVar b nv)
      _                        => case lookup v env of
        Just (Def _ ct) => Right (_ ** embed ct)
        _               => bindErr b v

  typecheck (TField b x v) = Prelude.do
    (TRec ps ** x2) <- typecheck x | (t ** _) => notField v t
    case isField v.val ps of
      Just (t ** prf) => Right (t ** SField b v prf x2)
      Nothing         => notField v (TRec ps)

  typecheck (TApp b (TVar b2 (VN "fix")) arg) = Prelude.do
    (TFun s t ** sarg) <- typecheck arg | (t ** _) => funErr arg t
    case hdecEq s t of
      Nothing0 => typeErr arg s t
      Just0 p  => Right (_ ** SFix b2 $ fun p sarg)

  typecheck (TLam b v rt scope) = Prelude.do
    tp              <- resolveTpe rt
    (res ** sscope) <- typecheck scope
    Right (TFun tp res ** SLam b v tp sscope)

  typecheck (TApp b fun arg)   = Prelude.do
    (TFun at rt ** sfun) <- typecheck fun | (t ** _) => funErr fun t
    sarg <- typecheckAs at arg
    Right (rt ** SApp b sfun sarg)

  typecheck (TPrim b y)    = Right (_ ** SPrim b y)

  typecheck (TRec b y)     = Prelude.do
    (ps ** r) <- tcrec y
    Right (_ ** SRec b r)

  typecheck (TIf b i y e)  = Prelude.do
    si        <- typecheckAs TBool i
    (t ** sy) <- typecheck y
    se        <- typecheckAs t e
    Right (t ** SIf b si sy se)

--------------------------------------------------------------------------------
-- Evaluation
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

namespace Value
  public export
  data VRecord : List (VarName, Tpe) -> (sc : Scope TTVar) -> Type

  public export
  data Value : (t : Tpe) -> (sc : Scope TTVar) -> Type where
    VPrim : (p : Prim) -> Value (PrimTpe p) sc
    VRec  : (r : VRecord ps sc) -> Value (TRec ps) sc
    VFld  :
         (v : VarName)
      -> (p : IsField v ps t)
      -> Value (TRec ps) sc
      -> Value t sc
    VLam  :
         (v : BindName)
      -> (t1 : Tpe)
      -> STerm t2 (sc:<V v t1)
      -> Value (TFun t1 t2) sc

  data VRecord : List (VarName, Tpe) -> (sc : Scope TTVar) -> Type where
    Nil  : VRecord [] sc
    (::) : (p : (VarName,Value t sc)) -> VRecord ps sc -> VRecord ((fst p, t)::ps) sc

torec : VRecord ps sc -> SRecord ps sc

export
toTerm : Value t sc -> STerm t sc
toTerm (VPrim p)     = SPrim NoBB p
toTerm (VRec r)      = SRec NoBB (torec r)
toTerm (VLam v t sc) = SLam NoBB v t sc
toTerm (VFld v p t)  = SField NoBB (pure v) p (toTerm t)

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

export covering
eval : {sc : _} -> STerm t sc -> Value t sc
eval trm =
  case toValue trm of
    Just v  => v
    Nothing => eval (step trm)
