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

  typecheckAs t (TLet b v rt scope) = Prelude.do
    (targ ** arg) <- typecheck rt
    (tscp ** scp) <- typecheck scope
    check t b (SApp b (SLam NoBB v targ scp) arg)

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

  typecheck (TLet b v rt scope) = Prelude.do
    (targ ** arg) <- typecheck rt
    (tscp ** scp) <- typecheck scope
    Right (tscp ** SApp b (SLam NoBB v targ scp) arg)

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
