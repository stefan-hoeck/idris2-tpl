module TPL.Name.Scope

import public TPL.Name
import public TPL.Name.SizeOf

%default total

public export
0 Scope : Type -> Type
Scope = SnocList

public export
0 Scoped : Type -> Type
Scoped t = Scope t -> Type

--------------------------------------------------------------------------------
-- Embedding
--------------------------------------------------------------------------------

public export
0 Embed : Scoped t -> Type
Embed tm = {0 outer, ns: Scope t} -> tm ns -> tm (outer++ns)

public export
interface Embeddable (0 t : Type) (0 tm : Scoped t) | tm where
  embed : Embed tm

--------------------------------------------------------------------------------
-- Strengthening
--------------------------------------------------------------------------------

public export
0 GenStrengthen : Scoped t -> Type
GenStrengthen tm = {0 outer, ns, vars : Scope t} ->
  SizeOf ns -> SizeOf vars -> tm ((outer++ns)++vars) -> Maybe (tm (outer++vars))

public export
interface Strengthenable (0 t : Type) (0 tm : Scoped t) | tm where
  genStrengthen : GenStrengthen tm

export %inline
strengthen : Strengthenable t tm => SizeOf ns -> tm (outer++ns) -> Maybe (tm outer)
strengthen s = genStrengthen s zero

--------------------------------------------------------------------------------
-- Shifting
--------------------------------------------------------------------------------

-- Node: "Shifting" is called "Weakening" in the Idris compiler, but we are
--       sticking to the terminology from "Types and Programming Languages"
--       here.

public export
0 GenShift : Scoped t -> Type
GenShift tm = {0 outer, ns, local : Scope t} ->
  SizeOf local -> SizeOf ns -> tm (outer++local) -> tm ((outer++ns)++local)

public export
0 Shift : Scoped t -> Type
Shift tm = {0 vars, ns : Scope t} -> SizeOf ns -> tm vars -> tm (vars++ns)

public export
interface Shiftable (0 t : Type) (0 tm : Scoped t) | tm where
  genShift : GenShift tm

export %inline
shiftNs : Shiftable t tm => Shift tm
shiftNs = genShift [<]

export %inline
shift : Shiftable t tm => tm sc -> tm (sc:<n)
shift = shiftNs (suc zero)
