module TPL.Error

import Derive.Prelude
import TPL.Name
import public Text.ByteBounds

%default total
%language ElabReflection

public export
data TplErr : Type -> Type where
  ErrUnify    : (exp, found : t) -> TplErr t
  ErrFun      : (found : t) -> TplErr t
  ErrUnexpFun : (exp : t) -> TplErr t
  ErrArg      : (exp, found : t) -> TplErr t
  ErrRes      : (exp, found : t) -> TplErr t
  ErrBind     : (n : VarName) -> TplErr t

%runElab derive "TplErr" [Show,Eq]

parameters {0 trm    : Type}
           {auto cst : Cast trm ByteBounds}

  export
  typeErr : trm -> t -> t -> Either (BBErr $ TplErr t) a
  typeErr t e f = Left $ B (Custom $ ErrUnify e f) (cast t)

  export
  argErr : trm -> t -> t -> Either (BBErr $ TplErr t) a
  argErr t e f = Left $ B (Custom $ ErrArg e f) (cast t)

  export
  resErr : trm -> t -> t -> Either (BBErr $ TplErr t) a
  resErr t e f = Left $ B (Custom $ ErrRes e f) (cast t)

  export
  funErr : trm -> t -> Either (BBErr $ TplErr t) a
  funErr t f = Left $ B (Custom $ ErrFun f) (cast t)

  export
  unexpFunErr : trm -> t -> Either (BBErr $ TplErr t) a
  unexpFunErr t e = Left $ B (Custom $ ErrUnexpFun e) (cast t)

  export
  bindErr : trm -> VarName -> Either (BBErr $ TplErr t) a
  bindErr t v = Left $ B (Custom $ ErrBind v) (cast t)

typeMsg : Interpolation e => Interpolation f => e -> f -> String
typeMsg e f = "Type mismatch: can't unify \{e} (expected) with \{f} (found)"

export
Interpolation t => Interpolation (TplErr t) where
  interpolate (ErrUnify e f) = typeMsg e f
  interpolate (ErrFun f) = typeMsg "_ -> _" f
  interpolate (ErrUnexpFun e) = typeMsg e "_ -> _"
  interpolate (ErrArg e f) = typeMsg "\{e} -> _" "\{f} -> _"
  interpolate (ErrRes e f) = typeMsg "_ -> \{e}" "_ -> \{f}"
  interpolate (ErrBind v) = "Unknown variable: '\{v}'"
