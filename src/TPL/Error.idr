module TPL.Error

import Derive.Prelude
import TPL.Name
import public Text.ByteBounds

%default total
%language ElabReflection

public export
data TplErr : Type -> Type where
  ErrUnify          : (exp, found : t) -> TplErr t
  ErrNotField       : VarName -> t -> TplErr t
  ErrFun            : (found : t) -> TplErr t
  ErrUnexpFun       : (exp : t) -> TplErr t
  ErrArg            : (exp, found : t) -> TplErr t
  ErrRes            : (exp, found : t) -> TplErr t
  ErrInfer          : (n : BindName) -> TplErr t
  ErrBind           : (n : VarName) -> TplErr t
  ErrDefined        : (n : VarName) -> TplErr t
  ErrUndef          : (n : VarName) -> TplErr t
  ErrUnknown        : (n : VarName) -> TplErr t
  ErrUnsupported    : TplErr t

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

  export
  cantInfer : trm -> BindName -> Either (BBErr $ TplErr t) a
  cantInfer t v = Left $ B (Custom $ ErrInfer v) (cast t)

  export
  defined : trm -> VarName -> Either (BBErr $ TplErr t) a
  defined t v = Left $ B (Custom $ ErrDefined v) (cast t)

  export
  undef : trm -> VarName -> Either (BBErr $ TplErr t) a
  undef t v = Left $ B (Custom $ ErrUndef v) (cast t)

  export
  unknown : trm -> VarName -> Either (BBErr $ TplErr t) a
  unknown t v = Left $ B (Custom $ ErrUnknown v) (cast t)

  export
  unsupported : trm -> Either (BBErr $ TplErr t) a
  unsupported t = Left $ B (Custom ErrUnsupported) (cast t)

export
notField : ByteBounded VarName -> t -> Either (BBErr $ TplErr t) a
notField (B v b) rec =  Left $ B (Custom $ ErrNotField v rec) b

typeMsg : Interpolation e => Interpolation f => e -> f -> String
typeMsg e f = "Type mismatch: can't unify \{f} (found) with \{e} (expected)"

export
Interpolation t => Interpolation (TplErr t) where
  interpolate (ErrUnify e f)    = typeMsg e f
  interpolate (ErrNotField v t) = "'\{v}' is not a record field of \{t}"
  interpolate (ErrFun f)        = typeMsg "a function type" f
  interpolate (ErrUnexpFun e)   = typeMsg e "a function type"
  interpolate (ErrArg e f)      = typeMsg "\{e} -> _" "\{f} -> _"
  interpolate (ErrRes e f)      = typeMsg "_ -> \{e}" "_ -> \{f}"
  interpolate (ErrInfer v)      = "Can't infer type for '\{v}'"
  interpolate (ErrBind v)       = "Unknown variable: '\{v}'"
  interpolate (ErrDefined v)    = "Function already defined: '\{v}'"
  interpolate (ErrUnknown v)    = "Unknown name: '\{v}'"
  interpolate (ErrUndef v)      = "Missing function definition for '\{v}'"
  interpolate ErrUnsupported  = "Feature not implemened yet"
