module TPL.Name

import Decidable.HDecEq
import Derive.Prelude

%default total
%language ElabReflection

public export
record VarName where
  constructor VN
  name : String

%runElab derive "VarName" [Show,Eq,Ord,FromString,Semigroup,Monoid]

export %inline
Interpolation VarName where interpolate = name

export %inline
HDecEq VarName where
  hdecEq (VN x) (VN y) = maybeCong VN (hdecEq x y)
