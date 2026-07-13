module TPL.Lambda.Typed.Eval

import Data.Maybe
import Data.Nat
import public TPL.Lambda.Typed.TT

%default total

||| A term reduced to normal form
public export
data Value : (t : Tpe) -> Type

||| A heterogeneous list of values
public export
data VRecord : List (VarName, Tpe) -> Type where
  Nil  : VRecord []
  (::) : (p : (VarName,Value t)) -> VRecord ps -> VRecord ((fst p, t)::ps)

||| An entry in the scoped environment used during evaluation.
|||
||| Using `ScopedEnv` instead of substitution (as done in the TAPL book)
||| has a dramatic effect on performance. However, we must take care
||| to only be as strict as necessary. When evaluating fixpoints,
||| we *must not* eagerly evaluate the continuation, as this would
||| lead to non-termination in the evaluation loop. That's why we
||| use a second data constructor for lazy evaluation.
|||
||| Everything else *must* be wrapped with `Strict`, however, to make
||| sure costly stuff is not computed more than once.
public export
data Entry : Tpe -> Type where
  Strict  : Value t -> Entry t
  Delayed : Lazy (Value t) -> Entry t

data Value : (t : Tpe) -> Type where
  VNat  : (n : Nat) -> Value TNat
  VBool : (v : Bool) -> Value TBool
  VUnit : Value TUnit
  VRec  : (r : VRecord ps) -> Value (TRec ps)
  VLam  :
       {0 sc : Scope TTVar}
    -> (v   : BindName)
    -> (t1  : Tpe)
    -> (env : ScopedEnv (Entry . TTVar.type) sc)
    -> STerm t2 (sc:<V v t1)
    -> Value (TFun t1 t2)

public export
0 TEnv : Scope TTVar -> Type
TEnv sc = ScopedEnv (Entry . TTVar.type) sc

export
getVField : IsField v ps t -> VRecord ps -> Value t
getVField IFZ     ((_,t)::_) = t
getVField (IFS x) (_::ps)    = getVField x ps

torec : VRecord ps -> List (VarName,Term)

export
toTerm : Value t -> Term
toTerm (VNat v)       = TPrim NoBB (PNat v)
toTerm (VBool v)      = TPrim NoBB (PBool v)
toTerm VUnit          = TPrim NoBB PUnit
toTerm (VRec r)       = TRec NoBB (torec r)
toTerm (VLam v t _ x) = TLam NoBB v (cast t) (restore x)

torec []          = []
torec ((v,t)::ps) = (v,toTerm t) :: torec ps

export
Interpolation (Value t) where
  interpolate = interpolate . resugar . toTerm

export
fromPrim : (p : Prim) -> Value (PrimTpe p)
fromPrim (PNat k)  = VNat k
fromPrim (PBool x) = VBool x
fromPrim PUnit     = VUnit
--------------------------------------------------------------------------------
-- Big-step Evaluation
--------------------------------------------------------------------------------

value : Entry t -> Value t
value (Strict x)  = x
value (Delayed x) = x

field : IsField v ps t -> Value (TRec ps) -> Value t
field x (VRec r) = getVField x r

covering
rec : TEnv sc -> SRecord ps sc -> VRecord ps

export covering
eval : TEnv sc -> STerm t sc -> Value t
eval e (SField b v y z) = field y (eval e z)
eval e (SApp b y z) =
  case eval e y of
    VLam v t1 e2 scope => eval (e2 :< Strict (eval e z)) scope
eval e (SRec b y) = VRec (rec e y)
eval e (SIf b pred fst snd) =
  case eval e pred of
    VBool True  => eval e fst
    VBool False => eval e snd
eval e (SFix b y) =
  case eval e y of
    VLam v t1 e2 scope => eval (e2 :< Delayed (eval e (SFix b y))) scope
eval e (SVar _ x) = value $ envVal x e
eval e (SLam _ v t sc) = VLam v t e sc
eval e (SPrim _ p) = fromPrim p
eval e (SSucc b y) = let VNat n := eval e y in VNat (S n)
eval e (SPred b y) = let VNat n := eval e y in VNat (pred n)
eval e (SIsZ b y)  = let VNat n := eval e y in VBool (isZero n)

rec e [] = []
rec e ((v,t)::ps) = (v,eval e t)::rec e ps
