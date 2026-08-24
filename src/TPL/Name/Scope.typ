#import "template.typ": *

=== Scope

We encode the scope of a term as a `SnocList` of the bound variables.
Currently, in the #Idris2 compiler the scope of a term is just a list
of `Name`s, but there is progress in converting this to a `SnocList`
of names, because in the literature scopes in general are extended
by _appending_ new variables. Therefore, a `SnocList` is a more natural
match and leads to less confusion.

In my experiments, I found it convenient to include additional
information such as the type or value of a bound variable
in a term's scope (which can then be interpreted as a typing
or evaluation context), so we abstract over the exact data types
contained in a scope.

```idris
module TPL.Name.Scope

import public TPL.Name
import public TPL.Name.SizeOf

%default total

public export
0 Scope : Type -> Type
Scope = SnocList
```

Likewise, a `Scoped` type is a type indexed by its scope. Again,
we abstract over the information the scope holds:

```idris
public export
0 Scoped : Type -> Type
Scoped t = Scope t -> Type
```

It is often necessary to adjust the scope of a term, for instance,
because it might be embedded in a larger scope (think of replacing
a variable with the closed term of a top-level definition). We
define several type aliases and interfaces for such operations.

Embedding a term in an outer scope is expected to be a no-op, since
the de Bruijn indices (which count from the right) are unaffected by this.
Ideally, embedding functions should be optimized away be the #Idris2
identity optimizer.

```idris
public export
0 Embed : Scoped t -> Type
Embed tm = {0 outer, ns: Scope t} -> tm ns -> tm (outer++ns)

public export
interface Embeddable (0 t : Type) (0 tm : Scoped t) | tm where
  embed : Embed tm
```

A _strengthening_ places a term into a scope where some of the
bound variables where removed. Since the term in question might
hold some of the removed variables, this operation can
fail.

```idris
public export
0 GenStrengthen : Scoped t -> Type
GenStrengthen tm =
     {0 outer, ns, vars : Scope t}
  -> SizeOf ns
  -> SizeOf vars
  -> tm ((outer++ns)++vars)
  -> Maybe (tm (outer++vars))

public export
interface Strengthenable (0 t : Type) (0 tm : Scoped t) | tm where
  genStrengthen : GenStrengthen tm

export %inline
strengthen :
     {auto str : Strengthenable t tm}
  -> SizeOf ns
  -> tm (outer++ns)
  -> Maybe (tm outer)
strengthen s = genStrengthen s zero
```

_Shifting_ means embedding a term in a larger scope. Unlike with
a trivial embedding (see above), the variables in the `outer` scope
need to be adjusted here. Note:
"Shifting" is called "Weakening" in the Idris compiler, but we are
sticking to the terminology from the book here.

```idris
public export
0 GenShift : Scoped t -> Type
GenShift tm =
     {0 outer, ns, local : Scope t}
  -> SizeOf local
  -> SizeOf ns
  -> tm (outer++local)
  -> tm ((outer++ns)++local)

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
```

// vi: filetype=idris2:syntax=typst
