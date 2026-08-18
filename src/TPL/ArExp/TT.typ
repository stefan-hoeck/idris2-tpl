#import "template.typ": *

== Type Checking

Although not present in the book, this section provides a
type checker for arithmetic expressions, demonstrating
techniques that will also be used in more complex cases
later on as well as proving probably the most important
aspect of typed programs: They do not get stuck during
evaluation.

=== Arithmetic Types

While our surface language does not have expressions
for types - they are simply not required - we can still
define a simple enum type for the kind of value an
expression is being reduced to during evaluation.

```idris
module TPL.ArExp.TT

import Derive.HDecEq
import Derive.Prelude
import TPL.ArExp.Term
import Text.ByteBounds
import public TPL.Error

%default total
%language ElabReflection

public export
data Tpe = TNat | TBool

%runElab derive "Tpe" [Show,Eq,Ord,HDecEq]

export
Interpolation Tpe where
  interpolate TNat  = "Nat"
  interpolate TBool = "Bool"
```

The first thing to note is that `Tpe` implements `HDecEq`, an
interface for hemi-decidable equality from the _refined_ library.
This is a critical thing to have to verify the propositional
equality between two types while at the same time being easier
to implement than proper decidable equality. In fact, implementing
hemi-decidable equality consists of exactly the same comparisons
at runtime as mere boolean equality and is therefore equally
performant but significantly more powerful.

Type checking comes with the potential of failure. That's the
whole _raison d'etre_ of having a type checker: to raise certain
potential runtime errors at compile time. We therefore need an error
type for specifying and pretty printing type errors (coming from
module `TPL.Error`):

```idris
public export
0 TpeErr : Type
TpeErr = TplErr Tpe

public export
0 ArErr : Type
ArErr = BBErr (TplErr Tpe)
```

We also need a way to specify the Idris types a term will be
reduced to during evaluation: a correspondence between Idris types
and `Tpe`:

```idris
||| The Idris type corresponding to a `Tpe`
public export
0 IType : Tpe -> Type
IType TNat  = Nat
IType TBool = Bool
```

=== Typed Terms

For the very simple language of arithmetic expressions, we can
define typed terms just by indexing a data type with `Tpe`.
In later examples, adding variables and scope will increase the
complexity of typing rules significantly.

```idris
public export
data ArTT : Tpe -> Type where
  ATrue  : ByteBounds -> ArTT TBool
  AFalse : ByteBounds -> ArTT TBool

  AZero  : ByteBounds -> ArTT TNat
  ASucc  : ByteBounds -> ArTT TNat -> ArTT TNat
  APred  : ByteBounds -> ArTT TNat -> ArTT TNat
  AIsZ   : ByteBounds -> ArTT TNat -> ArTT TBool

  AIf    : ByteBounds -> ArTT TBool -> ArTT t -> ArTT t -> ArTT t

%runElab deriveIndexed "ArTT" [Show]

export
fromBool : ByteBounds -> Bool -> ArTT TBool
fromBool b True  = ATrue b
fromBool b False = AFalse b

export
Cast (ArTT t) ByteBounds where
  cast (ATrue x)     = x
  cast (AFalse x)    = x
  cast (AZero x)     = x
  cast (ASucc x _)   = x
  cast (APred x _)   = x
  cast (AIsZ x _)    = x
  cast (AIf x _ _ _) = x
```

=== Type Checking

Our type checking algorithm just maps the data constructors
of `Term` to the ones of `ATerm`, making sure sub-terms with
incompatible types are rejected.

A key component is function `check`, which compares the found
type of an already processed term with its expected type, raising
a type error in case the two do not match. This is the place where
propositional equality is required.

```idris
check : (exp : Tpe) -> (found ** ArTT found) -> Either ArErr (ArTT exp)
check exp (found ** t) =
  case hdecEq exp found of
    Just0 prf => Right (rewrite prf in t)
    Nothing0  => typeErr t exp found

wrap : {t : _} -> ArTT t -> (x ** ArTT x)
wrap x = (t ** x)

typeCheckAs : (t : Tpe) -> Term -> Either ArErr (ArTT t)

export
typeCheck : Term -> Either ArErr (t ** ArTT t)
typeCheck (TTrue b)   = Right (_ ** ATrue b)
typeCheck (TFalse b)  = Right (_ ** AFalse b)
typeCheck (TZ b)      = Right (_ ** AZero b)
typeCheck (TSucc b x) = (wrap . ASucc b) <$> typeCheckAs TNat x
typeCheck (TPred b x) = (wrap . APred b) <$> typeCheckAs TNat x
typeCheck (TIsZ b x)  = (wrap . AIsZ b)  <$> typeCheckAs TNat x
typeCheck (TIf b i t e) = Prelude.do
  i2         <- typeCheckAs TBool i
  (tt ** t2) <- typeCheck t
  e2         <- typeCheckAs tt e
  Right (tt ** AIf b i2 t2 e2)

typeCheckAs t x = typeCheck x >>= check t
```

=== Evaluation

Using big-step operational semantics, we can easily verify in Idris
that properly typed terms can be reduced to Idris values of the
predicted types in a finite number of computational steps:

```idris
export
eval : ArTT t -> IType t
eval (ATrue _)     = True
eval (AFalse _)    = False
eval (AZero _)     = Z
eval (ASucc _ y)   = S (eval y)
eval (APred _ y)   = pred (eval y)
eval (AIsZ _ y)    = isZero (eval y)
eval (AIf _ y z w) = if eval y then eval z else eval w
```

// vi: filetype=idris2:syntax=typst
