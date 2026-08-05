module TPL.Error

import Derive.Prelude
import TPL.Name
import public Text.ByteBounds

%default total
%language ElabReflection

public export
data TplErr : Type -> Type where
  ErrUnify          : (exp, found : t) -> TplErr t
  ErrSum            : TplErr t
  ErrExpSum         : t -> TplErr t
  ErrNotField       : VarName -> t -> TplErr t
  ErrNotCon         : VarName -> t -> TplErr t
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
  ErrCovering       : List VarName -> TplErr t

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
  errSum : trm -> Either (BBErr $ TplErr t) a
  errSum t = Left $ B (Custom ErrSum) (cast t)

  export
  errExpSum : trm -> t -> Either (BBErr $ TplErr t) a
  errExpSum t tp = Left $ B (Custom $ ErrExpSum tp) (cast t)

  export
  errCovering : trm -> List VarName -> Either (BBErr $ TplErr t) a
  errCovering t ns = Left $ B (Custom $ ErrCovering ns) (cast t)

export
notField : ByteBounded VarName -> t -> Either (BBErr $ TplErr t) a
notField (B v b) rec =  Left $ B (Custom $ ErrNotField v rec) b

export
notCon : ByteBounded VarName -> t -> Either (BBErr $ TplErr t) a
notCon (B v b) rec =  Left $ B (Custom $ ErrNotCon v rec) b

typeMsg : Interpolation e => Interpolation f => e -> f -> String
typeMsg e f = "Type mismatch: can't unify \{f} (found) with \{e} (expected)"

cases : List VarName -> String
cases = unlines . map interpolate

export
Interpolation t => Interpolation (TplErr t) where
  interpolate (ErrUnify e f)    = typeMsg e f
  interpolate (ErrNotField v t) = "'\{v}' is not a record field of \{t}"
  interpolate (ErrNotCon v t)   = "'\{v}' is not a constructor of \{t}"
  interpolate (ErrFun f)        = typeMsg "a function type" f
  interpolate (ErrUnexpFun e)   = typeMsg e "a function type"
  interpolate (ErrArg e f)      = typeMsg "\{e} -> _" "\{f} -> _"
  interpolate (ErrRes e f)      = typeMsg "_ -> \{e}" "_ -> \{f}"
  interpolate (ErrInfer v)      = "Can't infer type for '\{v}'"
  interpolate (ErrBind v)       = "Unknown variable: '\{v}'"
  interpolate (ErrDefined v)    = "Function already defined: '\{v}'"
  interpolate (ErrUnknown v)    = "Unknown name: '\{v}'"
  interpolate (ErrUndef v)      = "Missing function definition for '\{v}'"
  interpolate ErrUnsupported    = "Feature not implemened yet"
  interpolate ErrSum            = "Can't infer type of sum type"
  interpolate (ErrExpSum t)     = "Expected sum type but got \{t}"
  interpolate (ErrCovering ns)  = "Pattern match is not covering. Missing cases: \{cases ns}"
