#import "template.typ": *

=== Environments

There are two kinds of environment we typically make use of:

- Global environments map names to top-level definitions.
  These have already been processed and validated, so they are
  ready to be called from other functions.
- Scoped or local environments map bound variables in scope to
  values in a type-safe manner.

For regular environments, we can use a `SortedMap` or other
data structure with good lookup performance:

```idris
module TPL.Env

import public Data.SnocList.Quantifiers as SQ
import public Data.SortedMap
import public TPL.Name.Var

%default total

export
infixl 3 ::=

public export
0 Env : Type -> Type
Env = SortedMap VarName
```

The following utilities allow us to setup an environment
programmatically with a bit of syntactic sugar:

```idris
public export
record Entry a where
  constructor (::=)
  name : VarName
  val  : a

public export
0 Entries : Type -> Type
Entries = List . Entry
```

Most of the time, adding a value to the global environment involves
some form of conversion based on the already existing environment
(type checking, for instance) and therefore can fail. The following
utility converts and adds predefined entries to a growing environment:

```idris
export
mkEnv : Env b -> (Env b -> a -> Either e b) -> Entries a -> Either e (Env b)
mkEnv ini fun = go ini
  where
    go : Env b -> Entries a -> Either e (Env b)
    go gamma []        = Right gamma
    go gamma (x :: xs) =
      case fun gamma x.val of
        Right vb => go (insert x.name vb gamma) xs
        Left  x  => Left x
```

Local environments are indexed by the local scope. This allows us
to safely look up a bound variable without risk of failure.

```idris
public export
0 ScopedEnv : (p : t -> Type) -> Scope t -> Type
ScopedEnv p sc = SQ.All.All p sc

envValImpl : ScopedEnv p sc -> IsVar n x sc -> p x
envValImpl (_:<trm) IZ = trm
envValImpl (i:<_)   (IS prf) = envValImpl i prf

export %inline
envVal : Var v sc -> ScopedEnv p sc -> p v
envVal (V p prf) env = envValImpl env (fromNat p prf)
```

// vi: filetype=idris2:syntax=typst
