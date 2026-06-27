module TPL.Lambda.Typed.TT

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
  SSucc  : ByteBounds -> STerm TNat sc -> STerm TNat sc
  SPred  : ByteBounds -> STerm TNat sc -> STerm TNat sc
  SIsZ   : ByteBounds -> STerm TNat sc -> STerm TBool sc

||| Top-level definitions
public export
record Def where
  constructor D
  type : Tpe
  term : STerm type [<]

shiftImpl : GenShift (STerm t)
shiftImpl sol son (SVar b t x)   = SVar b t (genShift sol son x)
shiftImpl sol son (SApp b t s)   = SApp b (shiftImpl sol son t) (shiftImpl sol son s)
shiftImpl sol son (SLam b x t y) = SLam b x t (shiftImpl (suc sol) son y)
shiftImpl sol son (SPrim b p)    = SPrim b p
shiftImpl sol son (SIf b i t e)  = SIf b (shiftImpl sol son i) (shiftImpl sol son t) (shiftImpl sol son e)
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
embedImpl (SSucc b x)     = SSucc b $ embedImpl x
embedImpl (SPred b x)     = SPred b $ embedImpl x
embedImpl (SIsZ b x)      = SIsZ b $ embedImpl x

export %inline
Embeddable (STerm t) where embed = embedImpl

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
