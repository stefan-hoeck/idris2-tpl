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
toNat : IsVar n v sc -> Nat
toNat IZ     = Z
toNat (IS n) = S (toNat n)

export
getVal : (sc : Scope t) -> (n : Nat) -> (0 p : IsVar n v sc) => t
getVal (_  :< v)  Z             = v
getVal (sc :< _)  (S x) @{IS p} = getVal sc x @{p}

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

--------------------------------------------------------------------------------
-- Var
--------------------------------------------------------------------------------

||| A variable in scope represented as a de Bruijn index into said scope.
public export
record Var (sc : Scope t) where
  constructor V
  pos    : Nat
  0 val  : t
  0 prf  : IsVar pos val sc

export %inline
Eq (Var sc) where V p1 _ _ == V p2 _ _ = p1 == p2

0 same :
     {sc : Scope t}
  -> (p1, p2 : Nat)
  -> (prf1 : IsVar p1 v1 sc)
  -> (prf2 : IsVar p2 v2 sc)
  -> p1 === p2
  -> V {sc} p1 v1 prf1 === V {sc} p2 v2 prf2
same p1 p2 prf1 prf2 prf =
  case sameIsVar p1 p2 prf1 prf2 prf of
    Refl => Refl

export
HDecEq (Var sc) where
  hdecEq (V p1 v1 prf1) (V p2 v2 prf2) =
    case hdecEq p1 p2 of
      Just0 prf => Just0 (same p1 p2 prf1 prf2 prf)
      Nothing0  => Nothing0

export
zero : Var (sc:<n)
zero = V 0 n IZ

||| Tries to find a name in a scope and convert it to a de Bruijn index.
export %inline
mkVar : HDecEq t => (sc : Scope t) -> (v : t) -> Maybe (Var sc)
mkVar sc nm = (\(Element n prf) => V n nm prf) <$> mkIsVar sc nm

export
GetVar : (sc : Scope t) -> Var sc -> t
GetVar sc (V pos _ prf) = getVal sc pos @{prf}

export
{sc : Scope t} -> Interpolation t => Interpolation (Var sc) where
  interpolate (V pos _ p) = "\{getVal sc pos @{p}} (\{show pos})"

export
locateVar :
     SizeOf local
  -> Var (outer++local)
  -> Either (Var local) (Var outer)
locateVar s (V pos name prf) =
  case locateIsVar s prf of
    Left0  q => Left (V _ name q)
    Right0 q => Right (V _ name q)

export
weakenVar : (s : SizeOf ns) -> Var outer -> Var (outer++ns)
weakenVar s (V p nm prf) = V (size s+p) nm (weakenIsVar s prf)

export
Embeddable t Var where
  embed (V p n prf) = V p n (embedIsVar prf)

export
Shiftable t Var where
  genShift sol son v =
    case locateVar sol v of
      Left  v2 => embed v2
      Right v2 => weakenVar sol $ weakenVar son v2

export
Strengthenable t Var where
  genStrengthen s t (V n nm prf) =
    case strengthenIsVar s t prf of
      Just (Left0 q)  => Just (V _ nm $ embedIsVar q)
      Just (Right0 q) => Just (V _ nm q)
      Nothing         => Nothing

--------------------------------------------------------------------------------
-- NVar
--------------------------------------------------------------------------------

||| A variable in scope represented as a de Bruijn index into said scope.
|||
||| Unlike `Var`, this is also indexed by the value at the given position
||| in scope.
public export
record NVar (v : t) (sc : Scope t) where
  constructor NV
  pos    : Nat
  0 prf  : IsVar pos v sc

export
nzero : NVar v (sc:<v)
nzero = NV 0 IZ

export
findNVar : (t -> Bool) -> (sc : Scope t) -> Maybe (v ** NVar v sc)
findNVar f [<]       = Nothing
findNVar f (sx :< x) =
  case f x of
    True  => Just (x ** nzero)
    False => case findNVar f sx of
      Just (v ** NV pos prf) => Just (v ** NV (S pos) (IS prf))
      Nothing                => Nothing

0 sameNVarLemma :
     {sc : Scope t}
  -> (p1, p2 : Nat)
  -> (prf1 : IsVar p1 v1 sc)
  -> (prf2 : IsVar p2 v2 sc)
  -> p1 === p2
  -> v1 === v2
sameNVarLemma p1 p2 prf1 prf2 prf =
  case sameIsVar p1 p2 prf1 prf2 prf of
    Refl => Refl

export
sameNVar : (x : NVar v1 sc) -> (y : NVar v2 sc) -> Maybe0 (v1 === v2)
sameNVar (NV p1 prf1) (NV p2 prf2) =
  case hdecEq p1 p2 of
    Nothing0  => Nothing0
    Just0 prf => Just0 (sameNVarLemma p1 p2 prf1 prf2 prf)

export
locateNVar :
     SizeOf local
  -> NVar v (outer++local)
  -> Either (NVar v local) (NVar v outer)
locateNVar s (NV pos prf) =
  case locateIsVar s prf of
    Left0  q => Left (NV _ q)
    Right0 q => Right (NV _ q)

export
weakenNVar : (s : SizeOf ns) -> NVar v outer -> NVar v (outer++ns)
weakenNVar s (NV p prf) = NV (size s+p) (weakenIsVar s prf)

export
Embeddable t (NVar v) where
  embed (NV p prf) = NV p (embedIsVar prf)

export
Shiftable t (NVar v) where
  genShift sol son v =
    case locateNVar sol v of
      Left  v2 => embed v2
      Right v2 => weakenNVar sol $ weakenNVar son v2

export
Strengthenable t (NVar v) where
  genStrengthen s t (NV n prf) =
    case strengthenIsVar s t prf of
      Just (Left0 q)  => Just (NV _ $ embedIsVar q)
      Just (Right0 q) => Just (NV _ q)
      Nothing         => Nothing
