module TPL.Lambda.Typed.Eval

import Data.Maybe
import Data.Nat
import public TPL.Lambda.Typed.TT

%default total

public export
data VRecord : List (VarName, Tpe) -> Type

public export
data Value : (t : Tpe) -> Type where
  VPrim : (p : Prim) -> Value (PrimTpe p)
  VRec  : (r : VRecord ps) -> Value (TRec ps)
  VLam  :
       {0 sc : Scope TTVar}
    -> (v   : BindName)
    -> (t1  : Tpe)
    -> (env : ScopedEnv (Value . TTVar.type) sc)
    -> STerm t2 (sc:<V v t1)
    -> Value (TFun t1 t2)

data VRecord : List (VarName, Tpe) -> Type where
  Nil  : VRecord []
  (::) : (p : (VarName,Value t)) -> VRecord ps -> VRecord ((fst p, t)::ps)

public export
0 TEnv : Scope TTVar -> Type
TEnv sc = ScopedEnv (Value . TTVar.type) sc

export
getVField : IsField v ps t -> VRecord ps -> Value t
getVField IFZ     ((_,t)::_) = t
getVField (IFS x) (_::ps)    = getVField x ps

torec : VRecord ps -> List (VarName,Term)

export
toTerm : Value t -> Term
toTerm (VPrim p)      = TPrim NoBB p
toTerm (VRec r)       = TRec NoBB (torec r)
toTerm (VLam v t _ x) = TLam NoBB v (cast t) (restore x)

torec []          = []
torec ((v,t)::ps) = (v,toTerm t) :: torec ps

export
Interpolation (Value t) where
  interpolate = interpolate . toTerm

--------------------------------------------------------------------------------
-- Big-step Evaluation
--------------------------------------------------------------------------------

field : IsField v ps t -> Value (TRec ps) -> Value t
field x (VRec r) = getVField x r
field x (VLam _ _ _ _)    impossible
field x (VPrim $ PNat _)  impossible
field x (VPrim $ PBool _) impossible
field x (VPrim   PUnit)   impossible

covering
bigrec : TEnv sc -> SRecord ps sc -> VRecord ps

export covering
bigEval : TEnv sc -> STerm t sc -> Value t
bigEval env (SField b v y z) = field y (bigEval env z)
bigEval env (SApp b y z) =
  case bigEval env y of
    VLam v t1 env2 scope => bigEval (env2 :< bigEval env z) scope
    VRec _          impossible
    VPrim (PNat _)  impossible
    VPrim (PBool _) impossible
    VPrim PUnit     impossible
bigEval env (SRec b y) = VRec (bigrec env y)
bigEval env (SIf b pred fst snd) =
  case bigEval env pred of
    VPrim (PBool True)  => bigEval env fst
    VPrim (PBool False) => bigEval env snd
bigEval env (SFix b y) =
  case bigEval env y of
    VLam v t1 env2 scope => bigEval (env2 :< bigEval env (SFix b y)) scope
    VRec _          impossible
    VPrim (PNat _)  impossible
    VPrim (PBool _) impossible
    VPrim PUnit     impossible
bigEval env (SVar _ x) = envVal x env
bigEval env (SLam _ v t sc) = VLam v t env sc
bigEval env (SPrim _ p) = VPrim p
bigEval env (SSucc b y) =
 let VPrim (PNat n) := bigEval env y
  in VPrim (PNat $ S n)
bigEval env (SPred b y) =
 let VPrim (PNat n) := bigEval env y
  in VPrim (PNat $ pred n)
bigEval env (SIsZ b y) =
 let VPrim (PNat n) := bigEval env y
  in VPrim (PBool $ isZero n)

bigrec env [] = []
bigrec env ((v,t)::ps) = (v,bigEval env t)::bigrec env ps
