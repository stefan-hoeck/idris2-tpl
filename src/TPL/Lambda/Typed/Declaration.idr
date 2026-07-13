module TPL.Lambda.Typed.Declaration

import Derive.Prelude
import public TPL.Lambda.Typed.Syntax

%default total
%language ElabReflection

public export
data Declaration : Type where
  Decl  : ByteBounds -> VarName -> RawTpe -> Declaration
  Alias : ByteBounds -> VarName -> RawTpe -> Declaration
  Defn  : ByteBounds -> VarName -> PTerm -> Declaration
  Eval  : PTerm -> Declaration

%runElab derive "Declaration" [Show,Eq]

export
Interpolation Declaration where
  interpolate (Decl _ n z)  = "\{n} : \{z};"
  interpolate (Alias _ n z) = "%alias \{n} : \{z};"
  interpolate (Defn _ n z)  = "\{n} = \{z};"
  interpolate (Eval t)      = "%eval \{t};"

export
MapBounds Declaration where
  mapBounds f (Decl b y z) = Decl (f b) y (mapBounds f z)
  mapBounds f (Alias b y z) = Alias (f b) y (mapBounds f z)
  mapBounds f (Defn b y z) = Defn (f b) y (mapBounds f z)
  mapBounds f (Eval t) = Eval (mapBounds f t)
