#import "template.typ": *

#pagebreak()

= Untyped Lambda Terms

After tinkering with very simple boolean and arithmetic terms,
we are now ready to dive into something much more powerful:
Untyped lambda terms. Since the lambda calculus is Turing complete,
this actually allows us to encode arbitrarily complex computations.
As such, we'll want to extend it a bit to allow some experimentation.

== Variables and Scope

The first significant change compared to simple arithmetic expressions
is the support for variable abstraction in lambda terms. The book describes
several ways of handling variables and performing operations like shifting
and substitution, some of which are quite finicky to implement.

Fortunately, the #Idris2 compiler sources provide a very nice approach
towards handling this complexity: There, terms are indexed by the scope
of local variables, and bound variables are encoded as _de Bruijn_ indices
into that scope

=== Names

For the time being (this might change in the future), we keep
things simple and provide just a newtype wrapper for variable
names.

```idris
module TPL.Name

import Decidable.HDecEq
import Derive.Prelude
import Text.ByteBounds

%default total
%language ElabReflection

public export
record VarName where
  constructor VN
  name : String

%runElab derive "VarName" [Show,Eq,Ord,FromString,Semigroup,Monoid]

export %inline
Interpolation VarName where interpolate = name
```

The following implementation of `Cast` allows us to conveniently
extract variable names from related values during parsing:

```idris
export %inline
Cast a VarName => Cast (ByteBounded a) VarName where
  cast = cast . val
```

We sometimes need to come up with our own variable names. The following
function converts a natural number to a `VarName` that cannot possibly
occurr during parsing (we do not allow variable names to begin with a `$`).

```idris
export
machineName : Nat -> VarName
machineName n = VN "$\{show n}"
```

Finally, we must verify if two variable names are provably total when
looking for a variable's name in the current scope:

```idris
export %inline
HDecEq VarName where
  hdecEq (VN x) (VN y) = maybeCong VN (hdecEq x y)
```

At the binding site, we add support for wildcard syntax, where
a placeholder (usually an underscore `_`) can be used instead of
a variable name that is never going to be used.

```idris
public export
data BindName : Type where
  PH : BindName
  NM : VarName -> BindName

%runElab derive "BindName" [Show,Eq,Ord]

export %inline
FromString BindName where fromString = NM . fromString

export
Interpolation BindName where
  interpolate PH     = "_"
  interpolate (NM v) = interpolate v

export %inline
Cast a VarName => Cast a BindName where
  cast = NM . cast
```

// vi: filetype=idris2:syntax=typst
