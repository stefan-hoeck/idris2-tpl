module TPL.Lambda.Typed.Declaration

import Derive.Prelude
import public TPL.Lambda.Typed.Term

%default total
%language ElabReflection

public export
data Declaration : Type where
  Decl  : ByteBounds -> VarName -> RawTpe -> Declaration
  Alias : ByteBounds -> VarName -> RawTpe -> Declaration
  Defn  : ByteBounds -> VarName -> Term -> Declaration
  Eval  : Term -> Declaration

%runElab derive "Declaration" [Show,Eq]
