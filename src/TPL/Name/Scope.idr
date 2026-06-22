module TPL.Name.Scope

import public TPL.Name
import public TPL.Name.SizeOf

%default total

public export
0 Scope : Type
Scope = SnocList VarName

public export
0 Scoped : Type
Scoped = Scope -> Type

--------------------------------------------------------------------------------
-- Shifting
--------------------------------------------------------------------------------

-- Node: "Shifting" is called "Weakening" in the Idris compiler, but we are
--       sticking to the terminology from "Types and Programming Languages"
--       here.

public export
0 GenShift : Scoped -> Type
GenShift tm = {0 outer, ns, local : Scope} ->
  SizeOf local -> SizeOf ns -> tm (outer++local) -> tm ((outer++ns)++local)

public export
0 Shift : Scoped -> Type
Shift tm = {0 vars, ns : Scope} -> SizeOf ns -> tm vars -> tm (vars++ns)

public export
interface Shiftable (0 tm : Scoped) where
  genShift : GenShift tm

export %inline
shiftNs : Shiftable tm => Shift tm
shiftNs = genShift [<]

export %inline
shift : Shiftable tm => tm sc -> tm (sc:<n)
shift = shiftNs (suc zero)
