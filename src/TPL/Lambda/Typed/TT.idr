module TPL.Lambda.Typed.TT

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

export
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
     ByteBounds
  -> SnocList (VarName,Term)
  -> SRecord ps sc
  -> Term

export
restore : STerm t sc -> Term
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

  tc : {sc : _} -> (m : Maybe Tpe) -> Term -> Either LamErr (TCRes m sc)

  tcrec : {sc : _} -> List (VarName,Term) -> Either LamErr (ps ** SRecord ps sc)
  tcrec []          = Right (_ ** [])
  tcrec ((v,t)::ps) = Prelude.do
    (ht ** h) <- tc Nothing t
    (tt ** pt) <- tcrec ps
    Right (_ ** ((v,h)::pt))

  tc m (TVar b v)     =
    case findNVar ((NM v ==) . name) sc of
      Just (V (NM n) tp ** nv) => check m b (SVar b nv)
      _                        => case lookup v env of
        Just (Def _ ct) => check m b (embed ct)
        _               => bindErr b v

  tc m (TField b x v) = Prelude.do
    (TRec ps ** x2) <- tc Nothing x | (t ** _) => notField v t
    case isField v.val ps of
      Just (s ** prf) => check m b (SField b v prf x2)
      Nothing         => notField v (TRec ps)

  tc m (TLam b v rt scope) = Prelude.do
    tp <- resolveTpe rt
    case m of
      Just (TFun eat ert) => case hdecEq eat tp of
        Nothing0 => typeErr rt eat tp
        Just0 _  => Prelude.do
            sscope <- tc (Just ert) scope
            Right (SLam b v eat sscope)
      Just t              => unexpFunErr b t
      Nothing             => Prelude.do
        (res ** sscope) <- tc Nothing scope
        Right (TFun tp res ** SLam b v tp sscope)

  tc m (TLet b v rt scope) = Prelude.do
    (targ ** arg) <- tc Nothing rt
    (tscp ** scp) <- tc Nothing scope
    check m b (SApp b (SLam NoBB v targ scp) arg)

  tc m (TApp b (TVar b2 (VN "fix")) arg)   =
    case m of
      Just t => Prelude.do
        sarg <- tc (Just $ TFun t t) arg
        Right (SFix b2 sarg)
      Nothing => Prelude.do
        (TFun s t ** sarg) <- tc Nothing arg | (t ** _) => funErr arg t
        case hdecEq s t of
          Nothing0 => typeErr arg s t
          Just0 p  => Right (_ ** SFix b2 $ fun p sarg)

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

  export %inline
  typecheck : {sc : _} -> Term -> Either LamErr (t ** STerm t sc)
  typecheck = tc Nothing

  export %inline
  typecheckAs : {sc : _} -> (t : Tpe) -> Term -> Either LamErr (STerm t sc)
  typecheckAs t = tc (Just t)
