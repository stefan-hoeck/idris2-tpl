#import "template.typ": *

#pagebreak()

= Boolean Terms

In this very basic example, we are going to learn
how to model and parse a very simple language of boolean expressions.
These expressions are always well-typed, so there is
no need for a type checker. In addition, expressions can always
be evaluated to boolean values in a finite number of steps.

In the TAPL book, this is the very first example demonstrating
baisc concepts like definitions of syntactic forms, inference rules,
and induction on terms. These things translate naturally and easily
to Idris.

== A Type for Boolean Terms <boolean_term>

To keep things simple, we restrict this example to only
boolean expressions. Arithmetic expressions with natural
numbers and booleans will be dealt with in @arithmetic.

Syntactically, boolean terms are either values (`true` or `false`)
or `if ... then ... else` expressions:

```idris
module TPL.BoolExp.Term

import Derive.Prelude

%default total
%language ElabReflection

public export
data Value : Type where
  VTrue  : Value
  VFalse : Value

%runElab derive "Value" [Show,Eq,Ord]

public export
data Term : Type where
  TVal   : Value -> Term
  TIf    : (i,t,e : Term) -> Term

%runElab derive "Term" [Show,Eq,Ord]
```

Throughout this project, I'm going to use elaborator reflection
to derive basic interface implementations. The necessary functionality
is provided by the #elab_util library.

=== Induction on Terms

Data type `Term` is the _syntax tree_ we are going to work
with. By induction over terms, we can immediately compute
a couple of utilities.

```idris
export
isConst : Term -> Bool
isConst (TVal v) = True
isConst _        = False

export
constants : Term -> List Value
constants (TVal v)    = [v]
constants (TIf i t e) = constants i `union` (constants t `union` constants e)

export
size : Term -> Nat
size (TVal _)    = 1
size (TIf i t e) = size i + size t + size e + 1

export
depth : Term -> Nat
depth (TVal _)    = 1
depth (TIf i t e) = max (depth i) (max (depth t) (depth e))
```

=== Casts

It is often useful to convert between values, terms, and Idris
values. The following casts will be useful. Utility `bool` is
just a specialised version of `cast` with better type inference
behavior.

```idris
export
Cast Bool Value where
  cast True  = VTrue
  cast False = VFalse

export
Cast Bool Term where
  cast = TVal . cast

export %inline
bool : Bool -> Term
bool = cast
```

=== Evaluation

The following two functions implement the small-step evaluation rules
described in the book. As can be seen by the use of `assert_smaller`,
the Idris totality checker cannot easily figure out on its own that
`eval` is provably total. In addition, the constant wrapping and
unwrapping via `Either` is not very efficient.

```idris
export
step : Term -> Either Value Term
step (TVal x)    = Left x
step (TIf i t e) =
  case step i of
    Left VTrue  => Right t
    Left VFalse => Right e
    Right x     => Right (TIf x t e)

export
eval : Term -> Value
eval t =
  case step t of
    Left v  => v
    Right x => eval (assert_smaller t x)
```

While we could use advanced techniques such as well-founded recursion
to help Idris verify that `eval` is total without resorting to `assert_smaller`,
the resulting code would be cluttered with utility lemmatas to help
Idris figure out that stuff is in fact getting strictly smaller.

As a simpler, more convenient alternative, we can implement big-step evaluation, which is
both more efficient and obviously total:

```idris
export
evalBigStep : Term -> Value
evalBigStep (TVal x)    = x
evalBigStep (TIf i t e) =
  case evalBigStep i of
    VTrue  => evalBigStep t
    VFalse => evalBigStep e
```

The nice thing about this example is that many of the theorems
discussed in the book immediately follow from the types and the
fact, that Idris accepts things as provably total.

=== Pretty Printing Terms <bool_pretty>

As we are going to see when we discuss parsing, coming up with grammar
rules and writing a parser for the syntax of our languages can be
quite a challenge. It is therefore important that parsers are
rigorously tested.

A straight forward way for testing the parser in the presence of
correct syntax is to randomly generate syntax trees, convert them
to string representation via a pretty printer (or several pretty
printers) and verify that the parser returns exactly the syntax
tree we started with (a concept called _round tripping_).

Here is a very simple pretty printer, which just prints
expressions on a single line and wraps nested `if` expressions
in parentheses (which helps readability but is not strictly
necessary from the parser's point of view):


```idris
export %inline
Interpolation Value where
  interpolate VTrue  = "true"
  interpolate VFalse = "false"

paren : Term -> String

pretty : Term -> String
pretty (TVal v)    = interpolate v
pretty (TIf i t e) = "if \{paren i} then \{paren t} else \{paren e}"

paren x = if isConst x then pretty x else "(\{pretty x})"

export %inline
Interpolation Term where interpolate = pretty
```

// vi: filetype=idris2:syntax=typst
