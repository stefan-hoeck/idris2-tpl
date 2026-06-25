module TPL.Error

import Derive.Prelude
import TPL.Name

%default total
%language ElabReflection

public export
data TplErr : Type -> Type where
  ErrUnify : (exp, found : t) -> TplErr t
  ErrBind  : (n : VarName) -> TplErr t

%runElab derive "TplErr" [Show,Eq]

export
Interpolation t => Interpolation (TplErr t) where
  interpolate (ErrUnify e f) =
    "type mismatch; can't unify \{e} (expected) with \{f} (found)"
  interpolate (ErrBind v) = "unknown variable: '\{v}'"
