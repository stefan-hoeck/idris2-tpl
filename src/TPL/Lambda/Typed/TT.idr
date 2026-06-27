module TPL.Lambda.Typed.TT

import public TPL.Env
import public TPL.Lambda.Typed.Term

%default total
%language ElabReflection

public export
0 PrimTpe : Prim -> Tpe

public export
data STerm : (t : Tpe) -> (sc : Scope) -> Type where
  SVar   : ByteBounds -> (v : Var sc) -> (t : Tpe) -> STerm t sc
  SLam   :
       ByteBounds
    -> (v : VarName)
    -> (s : Tpe)
    -> STerm t (sc:<v)
    -> STerm (TFun s t) sc
  SApp   : ByteBounds -> STerm (TFun s t) sc -> STerm t sc -> STerm t sc
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

public export
0 ClosedTerm : Tpe -> Type
ClosedTerm t = STerm t [<]
