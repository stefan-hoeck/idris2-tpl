#import "template.typ": *
#pagebreak()

= Arithmetic Terms

This section contains a direct translation of the arithmetic
terms consisting of natural numbers and boolean values plus
some basic operations on them. It is the first example where
evaluation can get stuck, which justifies the introduction
of type checking.

The technique shown here will be also used in later sections:
Untyped terms representing unmodified syntax trees are introduced
as a plain Idris type together with a parser and pretty printer.

Algorithms for desugaring, type checking, and evaluation follow.

== A Type for Arithmetic Terms

Type `Term` directly corresponds to the tiny language's syntax:
We have primitives for natural numbers and boolean values,
primitive functions `succ`, `pred`, and `iszero`, as well as
the ternary `if` expression that could already be found in boolean
terms.

```idris
module TPL.ArExp.Term

import Data.SortedSet
import Derive.Prelude
import Text.ByteBounds

%default total
%language ElabReflection

public export
data Term : Type where
  TTrue  : ByteBounds -> Term -- true
  TFalse : ByteBounds -> Term -- false
  TIf    : ByteBounds -> (i,t,e : Term) -> Term -- if then else
  TZ     : ByteBounds -> Term -- zero
  TSucc  : ByteBounds -> Term -> Term -- succ
  TPred  : ByteBounds -> Term -> Term -- pred
  TIsZ   : ByteBounds -> Term -> Term -- iszero

%runElab derive "Term" [Show,Eq]
```

Although this closely resembles the data type from @boolean_term, there
is an important difference: All data constructors wrap a `ByteBounds` value
describing the boundaries of the sub-expression as a pair of byte positions.
These allow us to properly show the locations of type errors in the
source code. In general, we'd like to implement two interfaces for
manipulating these bounds:

```idris
export
Cast Term ByteBounds where
  cast (TTrue x)     = x
  cast (TFalse x)    = x
  cast (TZ x)     = x
  cast (TSucc x _)   = x
  cast (TPred x _)   = x
  cast (TIsZ x _)    = x
  cast (TIf x _ _ _) = x

export
MapBounds Term where
  mapBounds f (TTrue x)     = TTrue (f x)
  mapBounds f (TFalse x)    = TFalse (f x)
  mapBounds f (TIf x i t e) =
    TIf (f x) (mapBounds f i) (mapBounds f t) (mapBounds f e)
  mapBounds f (TZ x)        = TZ (f x)
  mapBounds f (TSucc x y)   = TSucc (f x) (mapBounds f y)
  mapBounds f (TPred x y)   = TPred (f x) (mapBounds f y)
  mapBounds f (TIsZ x y)    = TIsZ (f x) (mapBounds f y)
```

=== Induction on Terms

We again define some utilities for inspecting terms.

```idris
export
isConst : Term -> Bool
isConst (TTrue {})  = True
isConst (TFalse {}) = True
isConst (TZ {})     = True
isConst _           = False

export
size : Term -> Nat
size (TTrue {})    = 1
size (TFalse {})   = 1
size (TZ {})       = 1
size (TIf _ i t e) = size i + size t + size e + 1
size (TSucc _ x)   = size x + 1
size (TPred _ x)   = size x + 1
size (TIsZ _ x)    = size x + 1

export
depth : Term -> Nat
depth (TTrue {})    = 1
depth (TFalse {})   = 1
depth (TZ {})       = 1
depth (TIf _ i t e) = max (depth i) (max (depth t) (depth e))
depth (TSucc _ x)   = depth x + 1
depth (TPred _ x)   = depth x + 1
depth (TIsZ _ x)    = depth x + 1
```

=== Conversions

The following utility functions will be useful for parsing. In particular,
we slightly extend the syntax from the TAPL book by adding support for
integer literals. These get converted to an inefficient tree representation
of natural numbers: This example is so basic that any further optimizations
are of no interest to us. A proper programming language would benefit
from an optimized representation of natural numbers, just like Idris
does it.

```idris
export
nat : ByteBounds -> Nat -> Term
nat bb Z     = TZ bb
nat bb (S k) = TSucc bb (nat bb k)

export %inline
int : ByteBounded Integer -> Term
int (B i bb) = nat bb $ cast i

export %inline
bool : ByteBounded Bool -> Term
bool (B True bb)  = TTrue bb
bool (B False bb) = TFalse bb
```

=== Pretty Printing

For the same reasons described in @bool_pretty, we provide a pretty printer
for terms and - via the `Cast` implementation - values:

```idris
pretty : Term -> String

paren : Term -> String
paren t = if isConst t then pretty t else "(\{pretty t})"

pretty (TTrue _)     = "true"
pretty (TFalse _)    = "false"
pretty (TIf _ i t e) = "if \{pretty i} then \{pretty t} else \{pretty e}"
pretty (TZ _)        = "0"
pretty (TSucc _ x)   = "succ \{paren x}"
pretty (TPred _ x)   = "pred \{paren x}"
pretty (TIsZ _ x)    = "iszero \{paren x}"

export %inline
Interpolation Term where interpolate = pretty
```

// vi: filetype=idris2:syntax=typst
