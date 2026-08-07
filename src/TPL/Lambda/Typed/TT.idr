module TPL.Lambda.Typed.TT

import Data.List.Quantifiers
import TPL.Match
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
data RecEntry : (sc : Scope TTVar) -> (VarName, Tpe) -> Type

public export
data SClause  : (t : Tpe) -> (sc : Scope TTVar) -> (p : (VarName,Tpe)) -> Type

public export
0 SClauses : List (VarName, Tpe) -> (t : Tpe) -> (sc : Scope TTVar) -> Type
SClauses ps t sc = All (SClause t sc) ps

public export
0 SRecord : List (VarName, Tpe) -> (sc : Scope TTVar) -> Type
SRecord ps sc = All (RecEntry sc) ps

public export
data STerm : (t : Tpe) -> (sc : Scope TTVar) -> Type where
  SVar   : {n : _} -> {t : _} -> ByteBounds -> NVar (V (NM n) t) sc -> STerm t sc
  SField :
       ByteBounds
    -> (v : ByteBounded VarName)
    -> IsField v.val ps t
    -> STerm (TRec ps) sc
    -> STerm t sc
  SSum :
       ByteBounds
    -> (v : ByteBounded VarName)
    -> IsField v.val ps t
    -> STerm t sc
    -> STerm (TSum ps) sc
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
  SCase  :
       ByteBounds
    -> STerm (TSum ps) sc
    -> SClauses ps t sc
    -> STerm t sc
  SFix   : ByteBounds -> STerm (TFun t t) sc -> STerm t sc
  SSucc  : ByteBounds -> STerm TNat sc -> STerm TNat sc
  SPred  : ByteBounds -> STerm TNat sc -> STerm TNat sc
  SIsZ   : ByteBounds -> STerm TNat sc -> STerm TBool sc

data RecEntry : (sc : Scope TTVar) -> (p : (VarName, Tpe)) -> Type where
  RE : (n : VarName) -> (t : Tpe) -> STerm t sc -> RecEntry sc (n,t)

data SClause : (t : Tpe) -> (sc : Scope TTVar) -> (p : (VarName, Tpe)) -> Type where
  SC : (p : _) -> (name : BindName) -> STerm t (sc:<V name (snd p)) -> SClause t sc p

export
getClause : IsField v ps t -> SClauses ps tp sc -> (n ** STerm tp (sc:<V n t))
getClause IFZ     (SC (v,t) n x :: _) = (n ** x)
getClause (IFS x) (_            ::cs) = getClause x cs

fix :
     ByteBounds
  -> (t : Tpe)
  -> (v : BindName)
  -> (x : STerm t (sc:<V v t))
  -> (y : STerm s (sc:<V v t))
  -> STerm s sc
fix b t v x y = SApp b (SLam NoBB v t y) (SFix NoBB (SLam NoBB v t x))

export
getField : IsField v ps t -> SRecord ps sc -> STerm t sc
getField IFZ     (RE _ _ t::_) = t
getField (IFS x) (_::ps)       = getField x ps

||| Top-level definitions
public export
data Entry : Type where
  Def : (type : Tpe) -> (term : STerm type [<]) -> Entry
  Dec : (type : Tpe) -> Entry
  Als : (type : Tpe) -> Entry

restoreRec :
     ByteBounds
  -> SnocList (VarName,Term)
  -> SRecord ps sc
  -> Term

restoreCases :
     SnocList (ByteBounded VarName,BindName,Term)
  -> SClauses ps t sc
  -> List (ByteBounded VarName,BindName,Term)

export
restore : STerm t sc -> Term
restore (SVar {n} b _)   = TVar b n
restore (SField b v _ t) = TField b (restore t) v
restore (SApp b t s)     = TApp b (restore t) (restore s)
restore (SLam b x t y)   = TLam b x (cast t) (restore y)
restore (SPrim b p)      = TPrim b p
restore (SRec b r)       = restoreRec b [<] r
restore (SSum b v _ t)   = TSum b v (restore t)
restore (SIf b i x y)    = TIf b (restore i) (restore x) (restore y)
restore (SCase b x cs)   = TCase b (restore x) (restoreCases [<] cs)
restore (SFix b x)       = TApp b "fix" (restore x)
restore (SSucc b x)      = TApp b "succ" (restore x)
restore (SPred b x)      = TApp b "pred" (restore x)
restore (SIsZ b x)       = TApp b "iszero" (restore x)

restoreRec b sp [] = TRec b (sp <>> [])
restoreRec b sp (RE v _ t::ps) = restoreRec b (sp:<(v,restore t)) ps

restoreCases sc [] = sc <>> []
restoreCases sc (SC p n t::ts) = restoreCases (sc:<(pure (fst p),n,restore t)) ts

--------------------------------------------------------------------------------
-- Handling Scope
--------------------------------------------------------------------------------

shiftRec : GenShift (SRecord ps)

shiftClauses : GenShift (SClauses ps t)

shiftImpl : GenShift (STerm t)
shiftImpl sol son (SVar b x)         = SVar b (genShift sol son x)
shiftImpl sol son (SField b v p x)   = SField b v p (shiftImpl sol son x)
shiftImpl sol son (SApp b t s)       = SApp b (shiftImpl sol son t) (shiftImpl sol son s)
shiftImpl sol son (SLam b x t y)     = SLam b x t (shiftImpl (suc sol) son y)
shiftImpl sol son (SPrim b p)        = SPrim b p
shiftImpl sol son (SRec b p)         = SRec b (shiftRec sol son p)
shiftImpl sol son (SSum b v p t)     = SSum b v p (shiftImpl sol son t)
shiftImpl sol son (SIf b i t e)      = SIf b (shiftImpl sol son i) (shiftImpl sol son t) (shiftImpl sol son e)
shiftImpl sol son (SCase b t cs)     = SCase b (shiftImpl sol son t) (shiftClauses sol son cs)
shiftImpl sol son (SFix b x)         = SFix b (shiftImpl sol son x)
shiftImpl sol son (SSucc b x)        = SSucc b (shiftImpl sol son x)
shiftImpl sol son (SPred b x)        = SPred b (shiftImpl sol son x)
shiftImpl sol son (SIsZ b x)         = SIsZ b (shiftImpl sol son x)

shiftRec sol son []             = []
shiftRec sol son (RE v t x::ps) = RE v t (shiftImpl sol son x) :: shiftRec sol son ps

shiftClauses sol son [] = []
shiftClauses sol son (SC p t trm :: cs) =
  SC p t (shiftImpl (suc sol) son trm) :: shiftClauses sol son cs

export %inline
Shiftable TTVar (STerm t) where genShift = shiftImpl

strRec : GenStrengthen (SRecord ps)

strClauses : GenStrengthen (SClauses ps t)

strImpl : GenStrengthen (STerm t)
strImpl s t (SVar b x)       = SVar b <$> genStrengthen s t x
strImpl s t (SField b v p x) = SField b v p <$> strImpl s t x
strImpl s t (SApp b x y)     = [| SApp (pure b) (strImpl s t x) (strImpl s t y) |]
strImpl s t (SLam b x p y)   = SLam b x p <$> strImpl s (suc t) y
strImpl s t (SPrim b p)      = Just $ SPrim b p
strImpl s t (SRec b p)       = SRec b <$> strRec s t p
strImpl s t (SSum b v p x)   = SSum b v p <$> strImpl s t x
strImpl s t (SIf b i x y)    = [| SIf (pure b) (strImpl s t i) (strImpl s t x) (strImpl s t y) |]
strImpl s t (SCase b i cs)   = [| SCase (pure b) (strImpl s t i) (strClauses s t cs) |]
strImpl s t (SFix b x)       = SFix b <$> strImpl s t x
strImpl s t (SSucc b x)      = SSucc b <$> strImpl s t x
strImpl s t (SPred b x)      = SPred b <$> strImpl s t x
strImpl s t (SIsZ b x)       = SIsZ b <$> strImpl s t x

strRec s t [] = Just []
strRec s t (RE v tp r::ps) =
  let Just sr  := strImpl s t r | _ => Nothing
      Just sps := strRec s t ps | _ => Nothing
   in Just $ RE v tp sr::sps

strClauses s t [] = Just []
strClauses s t (SC p tp x :: cs) =
  let Just sx  := strImpl s (suc t) x | _ => Nothing
      Just scs := strClauses s t cs   | _ => Nothing
   in Just $ SC p tp sx :: scs

export %inline
Strengthenable TTVar (STerm t) where genStrengthen = strImpl

embedRec : Embed (SRecord ps)

embedClauses : Embed (SClauses ps t)

embedImpl : Embed (STerm t)
embedImpl (SVar b x)         = SVar b (embed x)
embedImpl (SField b v p x)   = SField b v p (embedImpl x)
embedImpl (SApp b t s)       = SApp b (embedImpl t) (embedImpl s)
embedImpl (SLam b x p y)     = SLam b x p (embedImpl y)
embedImpl (SPrim b p)        = SPrim b p
embedImpl (SRec b p)         = SRec b (embedRec p)
embedImpl (SSum b v p t)     = SSum b v p (embedImpl t)
embedImpl (SIf b i x y)      = SIf b (embedImpl i) (embedImpl x) (embedImpl y)
embedImpl (SCase b x cs)     = SCase b (embedImpl x) (embedClauses cs)
embedImpl (SFix b x)         = SFix b $ embedImpl x
embedImpl (SSucc b x)        = SSucc b $ embedImpl x
embedImpl (SPred b x)        = SPred b $ embedImpl x
embedImpl (SIsZ b x)         = SIsZ b $ embedImpl x

embedRec [] = []
embedRec (RE v t x::ps) = RE v t (embedImpl x) :: embedRec ps

embedClauses [] = []
embedClauses (SC p tp x::cs) = SC p tp (embedImpl x) :: embedClauses cs

export %inline
Embeddable TTVar (STerm t) where embed = embedImpl

--------------------------------------------------------------------------------
-- Type Checking
--------------------------------------------------------------------------------

0 TCRes : Maybe Tpe -> Scoped TTVar
TCRes Nothing  sc = (t ** STerm t sc)
TCRes (Just t) sc = STerm t sc

check :
     {found : _}
  -> (m     : Maybe Tpe)
  -> ByteBounds
  -> STerm found sc
  -> Either LamErr (TCRes m sc)
check Nothing    bb t = Right (_ ** t)
check (Just exp) bb t =
  case hdecEq exp found of
    Just0 prf => Right (rewrite prf in t)
    Nothing0  => typeErr bb exp found

fun : (0 prf : s === t) -> STerm (TFun s t) sc -> STerm (TFun t t) sc
fun Refl x = x

parameters (env : Env Entry)
  resolvePairs :
       SnocList (VarName,Tpe)
    -> List (VarName,RawTpe)
    -> Either LamErr (List (VarName,Tpe))

  export
  resolveTpe : RawTpe -> Either LamErr Tpe
  resolveTpe (PVar b v)   =
    case lookup v env of
      Just (Als tpe) => Right tpe
      _              => unknown b v
  resolveTpe (PFun b y z) = [| TFun (resolveTpe y) (resolveTpe z) |]
  resolveTpe (PRec _ ps)  = TRec <$> resolvePairs [<] ps
  resolveTpe (PSum _ ps)  = TSum <$> resolvePairs [<] ps

  resolvePairs sp []          = Right (sp <>> [])
  resolvePairs sp ((v,t)::ps) =
    case resolveTpe t of
      Left x  => Left x
      Right x => resolvePairs (sp:<(v,x)) ps

  tc : {sc : _} -> (m : Maybe Tpe) -> Term -> Either LamErr (TCRes m sc)

  tcrec : {sc : _} -> List (VarName,Term) -> Either LamErr (ps ** SRecord ps sc)
  tcrec []          = Right (_ ** [])
  tcrec ((v,t)::ps) = Prelude.do
    (ht ** h) <- tc Nothing t
    (tt ** pt) <- tcrec ps
    Right (_ ** (RE v ht h::pt))

  tcclausesAs :
       {sc : _}
    -> (res : Tpe)
    -> All (Matching (BindName,Term)) ps
    -> Either LamErr (SClauses ps res sc)
  tcclausesAs res []                  = Right []
  tcclausesAs res (M v t (n,x) :: xs) = Prelude.do
    sx  <- assert_total $ tc {sc = sc :< V n t} (Just res) x
    sys <- tcclausesAs res xs
    pure (SC _ n sx::sys)

  tcclauses :
       {sc : _}
    -> All (Matching (BindName,Term)) ps
    -> Either LamErr (res ** SClauses ps res sc)
  tcclauses (M v t (n,x) :: xs) = Prelude.do
    (res ** sx) <- assert_total $ tc {sc = sc :< V n t} Nothing x
    sys <- tcclausesAs res xs
    pure (res ** (SC _ n sx::sys))
  tcclauses [] = (\x => (_ ** x)) <$> tcclausesAs TUnit []

  tc m (TVar b v)     =
    case findNVar ((NM v ==) . name) sc of
      Just (V (NM n) tp ** nv) => check m b (SVar b nv)
      _                        => case lookup v env of
        Just (Def _ ct) => check m b (embed ct)
        _               => bindErr b v

  tc m (TAs b t rt) = Prelude.do
    tp <- resolveTpe rt
    tt <- tc (Just tp) t
    check m b tt

  tc m (TField b x v) = Prelude.do
    (TRec ps ** x2) <- tc Nothing x | (t ** _) => notField v t
    case isField v.val ps of
      Just (s ** prf) => check m b (SField b v prf x2)
      Nothing         => notField v (TRec ps)

  tc m (TLam b v rt sc) = Prelude.do
    tp <- resolveTpe rt
    case m of
      Just (TFun eat ert) => case hdecEq eat tp of
        Nothing0 => typeErr rt eat tp
        Just0 _  => Prelude.do
            sscope <- tc (Just ert) sc
            Right (SLam b v eat sscope)
      Just t              => unexpFunErr b t
      Nothing             => Prelude.do
        (res ** sscope) <- tc Nothing sc
        Right (TFun tp res ** SLam b v tp sscope)

  tc m (TLet b v rt scope) = Prelude.do
    (targ ** arg) <- tc {sc} Nothing rt
    case m of
      Just t  => Prelude.do
        scp <- tc (Just t) scope
        pure (SApp b (SLam NoBB v targ scp) arg)
      Nothing => Prelude.do
        (tscp ** scp) <- tc Nothing scope
        pure (tscp ** SApp b (SLam NoBB v targ scp) arg)

  tc m (TLetrec b v rt x scope)   = Prelude.do
    tp <- resolveTpe rt
    tx <- tc {sc = sc:<V v tp} (Just tp) x
    case m of
      Just t => Prelude.do
        ts <- tc m scope
        pure $ fix b tp v tx ts
      Nothing => Prelude.do
        (t ** ts) <- tc m scope
        pure $ (t ** fix b tp v tx ts)

  tc m (TApp b fun arg) =
    case m of
      Just t => Prelude.do
        (ta ** sarg) <- tc Nothing arg
        sfun <- tc (Just $ TFun ta t) fun
        Right (SApp b sfun sarg)
      Nothing => Prelude.do
        (TFun at rt ** sfun) <- tc Nothing fun | (t ** _) => funErr fun t
        sarg <- tc (Just at) arg
        Right (rt ** SApp b sfun sarg)

  tc m (TPrim b y)    = check m b (SPrim b y)

  tc m (TRec b y)    = Prelude.do
    (ps ** r) <- tcrec y
    check m b (SRec b r)

  tc m (TSum b v t) =
    case m of
      Just (TSum ps) => case isField v.val ps of
        Just (ft ** prf) => SSum b v prf <$> tc (Just ft) t
        Nothing          => notCon v (TSum ps)
      Just tp        => errExpSum b tp
      _              => errSum b

  tc m (TIf b i y e)  = Prelude.do
    si <- tc {sc} (Just TBool) i
    case m of
      Just t => Prelude.do
        sy <- tc (Just t) y
        se <- tc (Just t) e
        Right (SIf b si sy se)
      Nothing => Prelude.do
        (t ** sy) <- tc Nothing y
        se        <- tc (Just t) e
        Right (t ** SIf b si sy se)

  tc m (TCase b x cs) = Prelude.do
    (TSum ps ** x2) <- tc {sc} Nothing x | (tp ** _) => errExpSum x tp
    ms              <- match b (TSum ps) ps cs
    case m of
      Just t  => SCase b x2 <$> tcclausesAs t ms
      Nothing => (\(t ** scs) => (t ** SCase b x2 scs)) <$> tcclauses ms

  export %inline
  typecheck : {sc : _} -> Term -> Either LamErr (t ** STerm t sc)
  typecheck = tc Nothing

  export %inline
  typecheckAs : {sc : _} -> (t : Tpe) -> Term -> Either LamErr (STerm t sc)
  typecheckAs t = tc (Just t)
