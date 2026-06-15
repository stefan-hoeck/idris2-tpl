module TPL.Name.Scope

import public TPL.Name

%default total

public export
0 Scope : Type
Scope = SnocList VarName

public export
0 Scoped : Type
Scoped = Scope -> Type
