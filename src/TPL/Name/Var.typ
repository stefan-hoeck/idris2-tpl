#import "template.typ": *

=== Variables

A bound variable is encoded as a natural number
(the variable's de Bruijn index) together with a proof that
the variable is indeed at the given position in the current
scope.

```idris
module TPL.Name.Var

import Data.DPair
import Data.Either0
import Data.Nat
import Data.SnocList.HasLength
import Data.So
import Decidable.HDecEq
import public TPL.Name
import public TPL.Name.LSizeOf
import public TPL.Name.Scope

%default total

public export
data IsVar : (n : Nat) -> (v : t) -> (sc : Scope t) -> Type where
  IZ : IsVar Z v (sc:<v)
  IS : IsVar n v sc -> IsVar (S n) v (sc:<m)
```

At runtime, `IsVar` is just a natural number and we can freely
convert between `IsVar` and `Nat` at no cost.

```idris
export
toNat : IsVar n v sc -> Nat
toNat IZ     = Z
toNat (IS n) = S (toNat n)

||| We can always manifest the `IsVar` proof from the corresponding
||| natural number.
|||
||| O(1), because this is recognized as the identity function by the
||| Idris compiler.
export
fromNat : (n : Nat) -> (0 prf : IsVar n v sc) -> IsVar n v sc
fromNat {sc = _:<v} 0     IZ       = IZ
fromNat             (S k) (IS prf) = IS (fromNat k prf)
```

We can also use a proof of type `IsVar` to safely extract a
variable from its scope:

```idris
export
getVal : (sc : Scope t) -> (n : Nat) -> (0 p : IsVar n v sc) => t
getVal (_  :< v)  Z             = v
getVal (sc :< _)  (S x) @{IS p} = getVal sc x @{p}
```

The source code contains some additional utilities for embedding
and shifting `IsVar` proofs. While vital for the usability of
the data type, they are not very interesting to discuss here,
so they are omitted from the generated docs.

/* idris
export
0 sameIsVar :
     {sc : Scope t}
  -> (p1, p2 : Nat)
  -> (prf1 : IsVar p1 v1 sc)
  -> (prf2 : IsVar p2 v2 sc)
  -> p1 === p2
  -> prf1 ~=~ prf2
sameIsVar Z     Z     IZ     IZ     Refl = Refl
sameIsVar (S k) (S k) (IS x) (IS y) Refl =
  case sameIsVar k k x y Refl of
    Refl => Refl

export
mkIsVar :
     {auto hd : HDecEq t}
  -> (sc : Scope t)
  -> (v  : t)
  -> Maybe (Subset Nat (\n => IsVar n v sc))
mkIsVar [<]       nm = Nothing
mkIsVar (sx :< x) nm =
  case hdecEq x nm of
    Just0 prf => Just (Element 0 $ replace {p = \y => IsVar 0 y (sx:<x)} prf IZ)
    Nothing0  => (\(Element n iv) => Element (S n) (IS iv)) <$> mkIsVar sx nm

export
0 embedIsVar : IsVar n v sc -> IsVar n v (outer++sc)
embedIsVar IZ     = IZ
embedIsVar (IS x) = IS (embedIsVar x)

export
0 weakenIsVar : (s : SizeOf ns) -> IsVar n x xs -> IsVar (size s+n) x (xs++ns)
weakenIsVar (SO Z Z)         p = p
weakenIsVar (SO (S k) (S l)) p = IS (weakenIsVar (SO k l) p)

0 locateIsVarLT :
     (s : SizeOf local)
  -> So (n < size s)
  -> IsVar n x (outer++local)
  -> IsVar n x local
locateIsVarLT (SO Z Z) so v =
  case v of
    IZ impossible
    IS v impossible
locateIsVarLT (SO (S k) (S l)) so v =
  case v of
    IZ => IZ
    IS v => IS (locateIsVarLT (SO k l) so v)

0 locateIsVarGE :
     (s : SizeOf local)
  -> So (n >= size s)
  -> IsVar n x (outer++local)
  -> IsVar (n `minus` size s) x outer
locateIsVarGE (SO Z Z) so v = rewrite minusZeroRight n in v
locateIsVarGE (SO (S k) (S l)) so v =
  case v of
   IS v => locateIsVarGE (SO k l) so v

export
locateIsVar :
     {n : _}
  -> {0 outer, local : Scope t}
  -> (s : SizeOf local)
  -> (0 prf : IsVar n nm (outer++local))
  -> Either0 (IsVar n nm local) (IsVar (n `minus` size s) nm outer)
locateIsVar s v =
  case choose (n < size s) of
    Left  so => Left0 (locateIsVarLT s so v)
    Right so => Right0 (locateIsVarGE s so v)

export
strengthenIsVar :
     {n : _}
  -> {0 outer,ns,vars : Scope t}
  -> (s : SizeOf ns)
  -> (t : SizeOf vars)
  -> (0 prf : IsVar n nm ((outer++ns)++vars))
  -> Maybe (Either0 (IsVar n nm vars) (IsVar (size t + ((n `minus` size t) `minus` size s)) nm (outer++vars)))
strengthenIsVar s t prf =
  case locateIsVar t prf of
    Left0 q  => Just (Left0 q)
    Right0 q => case locateIsVar s q of
      Left0 q => Nothing
      Right0 q => Just (Right0 $ weakenIsVar t q)
*/

We can now pair a de Bruijn index with its `IsVar` proof to get
a properly validated representation of a bound variable:

```idris
||| A variable in scope represented as a de Bruijn index into said scope.
public export
record Var (v : t) (sc : Scope t) where
  constructor V
  pos    : Nat
  0 prf  : IsVar pos v sc

export
nzero : Var v (sc:<v)
nzero = V 0 IZ
```

We add a utility for finding a variable in scope:

```idris
export
findVar : (t -> Bool) -> (sc : Scope t) -> Maybe (v ** Var v sc)
findVar f [<]       = Nothing
findVar f (sx :< x) =
  case f x of
    True  => Just (x ** nzero)
    False => case findVar f sx of
      Just (v ** V pos prf) => Just (v ** V (S pos) (IS prf))
      Nothing               => Nothing
```

/* idris
0 sameVarLemma :
     {sc : Scope t}
  -> (p1, p2 : Nat)
  -> (prf1 : IsVar p1 v1 sc)
  -> (prf2 : IsVar p2 v2 sc)
  -> p1 === p2
  -> v1 === v2
sameVarLemma p1 p2 prf1 prf2 prf =
  case sameIsVar p1 p2 prf1 prf2 prf of
    Refl => Refl

export
sameVar : (x : Var v1 sc) -> (y : Var v2 sc) -> Maybe0 (v1 === v2)
sameVar (V p1 prf1) (V p2 prf2) =
  case hdecEq p1 p2 of
    Nothing0  => Nothing0
    Just0 prf => Just0 (sameVarLemma p1 p2 prf1 prf2 prf)
*/

Finally, we implement the interfaces for adjusting the scope of
a bound variables:

```idris
export
locateVar :
     SizeOf local
  -> Var v (outer++local)
  -> Either (Var v local) (Var v outer)
locateVar s (V pos prf) =
  case locateIsVar s prf of
    Left0  q => Left (V _ q)
    Right0 q => Right (V _ q)

export
weakenVar : (s : SizeOf ns) -> Var v outer -> Var v (outer++ns)
weakenVar s (V p prf) = V (size s+p) (weakenIsVar s prf)

export
Embeddable t (Var v) where
  embed (V p prf) = V p (embedIsVar prf)

export
Shiftable t (Var v) where
  genShift sol son v =
    case locateVar sol v of
      Left  v2 => embed v2
      Right v2 => weakenVar sol $ weakenVar son v2

export
Strengthenable t (Var v) where
  genStrengthen s t (V n prf) =
    case strengthenIsVar s t prf of
      Just (Left0 q)  => Just (V _ $ embedIsVar q)
      Just (Right0 q) => Just (V _ q)
      Nothing         => Nothing
```

// vi: filetype=idris2:syntax=typst
