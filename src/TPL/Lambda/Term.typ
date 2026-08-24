#import "template.typ": *

== Lambda Terms

We are now ready to encode and process untyped lambda terms.
In order to facilitate the full reduction of values, we
add support for boolean and natural number primitives from
the beginning.

```idris
module TPL.Lambda.Term

import Data.FilePath.File
import Derive.Prelude
import TPL.Env
import TPL.Name.Var
import Text.ByteBounds
import public TPL.Error

%default total
%language ElabReflection

public export
data Prim : Type where
  PNat  : Nat -> Prim
  PBool : Bool -> Prim

%runElab derive "Prim" [Show,Eq]

export
Interpolation Prim where
  interpolate (PNat v)  = show v
  interpolate (PBool v) = show v
```

The following type represents the full syntax of terms. Please
note that primitive operations on booleans and natural numbers
are not explicitly included here. They will be dealt with when we
resolve variable names.

```idris
public export
data Term : Type where
  TVar   : ByteBounds -> (v : VarName) -> Term
  TLam   : ByteBounds -> (v : VarName) -> (sc : Term) -> Term
  TApp   : ByteBounds -> (t,s : Term) -> Term
  TPrim  : ByteBounds -> Prim -> Term
  TIf    : ByteBounds -> (i,t,e : Term) -> Term

%runElab derive "Term" [Show,Eq]
```

As with arithmetic terms, we implement some additional interfaces
and provide a few utility functions that will be handy when
writing the parser:

```idris
public export %inline
FromString Term where fromString = TVar NoBB . fromString

export %inline
Cast VarName Term where
  cast = TVar NoBB

export
Cast Term ByteBounds where
  cast (TVar x _)    = x
  cast (TLam x _ _)  = x
  cast (TApp x _ _)  = x
  cast (TPrim x _)   = x
  cast (TIf x _ _ _) = x

export
nat : ByteBounds -> Nat -> Term
nat bb n = TPrim bb (PNat n)

export %inline
int : ByteBounded Integer -> Term
int (B i bb) = nat bb $ cast i

export %inline
bool : ByteBounded Bool -> Term
bool (B b bb) = TPrim bb (PBool b)

export
appAll : Term -> List Term -> Term
appAll s []      = s
appAll s (t::ts) = appAll (TApp (cast s <+> cast t) s t) ts

export %inline
appAllSnoc : Term -> SnocList Term -> Term
appAllSnoc s = appAll s . (<>>[])
```

And once again we provide a very basic pretty printer:

```idris
isAtom : Term -> Bool
isAtom (TVar {})  = True
isAtom (TPrim {}) = True
isAtom _          = False

appL : Term -> String

paren : Term -> String

pretty : Term -> String
pretty (TVar _ v)    = v.name
pretty (TLam _ v sc) = "λ\{v}. \{pretty sc}"
pretty (TApp _ t s)  = "\{appL t} \{paren s}"
pretty (TPrim _ p)   = interpolate p
pretty (TIf _ i t e) = "if \{pretty i} then \{pretty t} else \{pretty e}"

paren t = if isAtom t then pretty t else "(\{pretty t})"

appL (TApp _ t s) = "\{appL t} \{paren s}"
appL t            = paren t

export %inline
Interpolation Term where interpolate = pretty
```

=== Scoped Terms

Even though there will be no type checker for this tiny language,
we still have to test whether all defined variables are in
scope. Therefore, we provide a second tree type, this one indexed
by the local scope:

```idris
public export
data STerm : (sc : Scope VarName) -> Type where
  SVar   : {nm : _} -> ByteBounds -> (v : Var nm sc) -> STerm sc
  SLam   : ByteBounds -> (v : VarName) -> STerm (sc:<v) -> STerm sc
  SApp   : ByteBounds -> (t,s : STerm sc) -> STerm sc
  SPrim  : ByteBounds -> Prim -> STerm sc
  SIf    : ByteBounds -> (i,t,e : STerm sc) -> STerm sc
  SSucc  : ByteBounds -> STerm sc -> STerm sc
  SPred  : ByteBounds -> STerm sc -> STerm sc
  SIsZ   : ByteBounds -> STerm sc -> STerm sc

public export
0 ClosedTerm : Type
ClosedTerm = STerm [<]
```

When resolving top-level definitions, closed terms need to be
embedded into the current local scope:

```idris
embedImpl : Embed STerm
embedImpl (SVar b x)      = SVar b (embed x)
embedImpl (SApp b t s)    = SApp b (embedImpl t) (embedImpl s)
embedImpl (SLam b x y)    = SLam b x (embedImpl y)
embedImpl (SPrim b p)     = SPrim b p
embedImpl (SIf b i x y)   = SIf b (embedImpl i) (embedImpl x) (embedImpl y)
embedImpl (SSucc b x)     = SSucc b $ embedImpl x
embedImpl (SPred b x)     = SPred b $ embedImpl x
embedImpl (SIsZ b x)      = SIsZ b $ embedImpl x

export %inline
Embeddable VarName STerm where embed = embedImpl
```

Converting a term to a closed term can go wrong: We might encounter
a free variable. Therefore, this conversion can fail with an error.

```idris
public export
0 TpeErr : Type
TpeErr = TplErr Void

public export
0 LamErr : Type
LamErr = BBErr TpeErr
```

In `Term`, a variable can mean one of two things:
It either refers to an already defined top-level term, in which
case we embed the term in the local scope and return it,
or it could refer to a bound variable, which we can lookup in
the local scope. If neither is the case, we abort with an
error.

```idris
parameters (env : Env ClosedTerm)

  export
  scoped : {sc : _} -> Term -> Either LamErr (STerm sc)
  scoped (TVar b v)   =
    case findVar (v==) sc of
      Just (nm ** vr) => Right (SVar b vr)
      Nothing => case lookup v env of
        Just ct => Right $ embed ct
        Nothing => bindErr b v
  scoped (TApp b t s)  = [| SApp (pure b) (scoped t) (scoped s) |]
  scoped (TLam b v x)  = SLam b v <$> scoped x
  scoped (TPrim b p)   = Right $ SPrim b p
  scoped (TIf b i x y) = [|SIf (pure b) (scoped i) (scoped x) (scoped y) |]

  export %inline
  closed : Term -> Either LamErr ClosedTerm
  closed = scoped
```

Note, that with the above definition of `scoped`, top-level definitions
are always inlined by calling `embed` when being resolved. This is fine
when writing an interpreter as we do here: Memory consumption will only
be affected, if the identity optimizer does not kick in for our implementation
of `embed`. For a proper compiler, however, this could lead to a dramatic
blowup in the generated code. For such a use case, it might be better
to define an additional data constructor for `STerm`, where the embedded
subterm is paired with its fully qualified name.

Another thing to note: There is not optimization or preliminary
evaluation of top-level definitions. This can have a negative impact
on performance, for instance, when we later add `let` bindings to
the syntax of our langauge. It could be wasteful to re-evaluate a top-level
constant every time it is required. We are going to explore some options
in a later section.

Given an environment of terms bound to local variables, we can
convert any scoped term back to a regular term. Such an environment
will be built up during evaluation, where we also want to restore
stuck terms or lambda values.

```idris
public export
0 TEnv : Scope VarName -> Type
TEnv = ScopedEnv (const Term)

export
restore : {0 sc : _} -> TEnv sc -> STerm sc -> Term
restore e (SVar b v)      = envVal v e
restore e (SApp b t s)    = TApp b (restore e t) (restore e s)
restore e (SLam b x y)    = TLam b x (restore (e:<cast x) y)
restore e (SPrim b p)     = TPrim b p
restore e (SIf b i x y)   = TIf b (restore e i) (restore e x) (restore e y)
restore e (SSucc b x)     = TApp b "succ" (restore e x)
restore e (SPred b x)     = TApp b "pred" (restore e x)
restore e (SIsZ b x)      = TApp b "iszero" (restore e x)
```

Since top-level definitions where inlined in the `STerm` with no chance
of converting them back to their qualified function names,
the restored term, too, will still hold the inlined expressions.

=== Evaluation

We again use big-step operational semantics. In addition, instead of
substituting values when applying values to lambda terms,
we continue evaluation of the variable's scope by passing along
the applied value in a local environment. This has a dramatic impact
on performance, and allows us to - for instance - compute the
tenth factorial (see the example module), a computation that would
otherwise fail to come up with a result for `n = 7` due to exponential
blowup.

We start with defining a data type for values:

```idris
public export
data Value : Type

public export
0 VEnv : Scope VarName -> Type
VEnv sc = ScopedEnv (const Value) sc

data Value : Type where
  VNat  : (n : Nat) -> Value
  VBool : (b : Bool) -> Value
  VLam  :
       {0 sc : Scope VarName}
    -> (v    : VarName)
    -> (env  : VEnv sc)
    -> STerm (sc:<v)
    -> Value
```

It is important to note that we do _not_ index a value over its scope
but - in case of lambda values - wrap up the current
scoped environment together with the inner term.

We can convert values back to regular terms, which allows us to
conveniently pretty print our results:

```idris
export
Cast Prim Value where
  cast (PNat k)  = VNat k
  cast (PBool x) = VBool x

export covering
tenv : VEnv sc -> TEnv sc

export covering
Cast Value Term where
  cast (VNat n)       = TPrim NoBB (PNat n)
  cast (VBool b)      = TPrim NoBB (PBool b)
  cast (VLam v env x) = TLam NoBB v (restore (tenv env :< cast v) x)

tenv [<]      = [<]
tenv (x :< y) = tenv x :< cast y
```

Finally, the evaluation function just pattern matches on `STerm`'s
constructors. If we ever get stuck, we restore the current term
and return it in a `Left`, otherwise we proceed until we arrive
at a value.

```idris
covering
failEval : VEnv sc -> STerm sc -> Either Term a
failEval e = Left . restore (tenv e)

export covering
eval : VEnv sc -> STerm sc -> Either Term Value
eval e t =
  case t of
    SVar _ v    => Right (envVal v e)
    SLam _ v y  => Right (VLam v e y)
    SApp _ y s  => Prelude.do
      VLam v e2 sx <- eval e y | _ => failEval e t
      arg          <- eval {sc} e s
      eval (e2 :< arg) sx
    SPrim _ y   => Right (cast y)
    SIf _ i y z => Prelude.do
      VBool b <- eval e i | _ => failEval e t
      if b then eval e y else eval e z
    SSucc _ y   => Prelude.do
      VNat n <- eval e y | _ => failEval e t
      pure (VNat $ S n)
    SPred _ y   => Prelude.do
      VNat n <- eval e y | _ => failEval e t
      pure (VNat $ pred n)
    SIsZ _ y    => Prelude.do
      VNat n <- eval e y | _ => failEval e t
      pure (VBool $ isZero n)
```

=== Top-level Declarations

We now define a simple data type for top-level declarations,
which will allow us to write proper source files with
global definitions, evaluation statements, and `#include`
statements.

```idris
public export
data Declaration : Type where
  Include : AnyFile -> Declaration
  Defn    : VarName -> Term -> Declaration
  Eval    : Term -> Declaration

%runElab derive "Declaration" [Show,Eq]
```

We are now ready to write a parser for our source files.

// vi: filetype=idris2:syntax=typst
