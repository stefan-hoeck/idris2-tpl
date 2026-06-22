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
data IsVar : (n : Nat) -> (nm : VarName) -> (sc : Scope) -> Type where
  IZ : IsVar Z nm (sc:<nm)
  IS : IsVar n nm sc -> IsVar (S n) nm (sc:<m)

export
toNat : IsVar n nm sc -> Nat
toNat IZ     = Z
toNat (IS n) = S (toNat n)

export
getName : (sc : Scope) -> (n : Nat) -> (0 p : IsVar n nm sc) => VarName
getName (_  :< nm) Z             = nm
getName (sc :< _)  (S x) @{IS p} = getName sc x @{p}

export
mkIsVar :
     (sc : Scope)
  -> (nm : VarName)
  -> Maybe (Subset Nat (\n => IsVar n nm sc))
mkIsVar [<]       nm = Nothing
mkIsVar (sx :< x) nm =
  case hdecEq x nm of
    Just0 prf => Just (Element 0 $ replace {p = \y => IsVar 0 y (sx:<x)} prf IZ)
    Nothing0  => (\(Element n iv) => Element (S n) (IS iv)) <$> mkIsVar sx nm

export
0 embedIsVar : IsVar n nm sc -> IsVar n nm (outer++sc)
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
  -> {0 outer, local : Scope}
  -> (s : SizeOf local)
  -> (0 prf : IsVar n nm (outer++local))
  -> Either0 (IsVar n nm local) (IsVar (n `minus` size s) nm outer)
locateIsVar s v =
  case choose (n < size s) of
    Left  so => Left0 (locateIsVarLT s so v)
    Right so => Right0 (locateIsVarGE s so v)

--------------------------------------------------------------------------------
-- Var
--------------------------------------------------------------------------------

||| A variable in scope represented as a de Bruijn index into said scope.
public export
record Var (sc : Scope) where
  constructor V
  pos    : Nat
  0 name : VarName
  0 prf  : IsVar pos name sc

export %inline
Eq (Var sc) where V p1 _ _ == V p2 _ _ = p1 == p2

||| Tries to find a name in a scope and convert it to a de Bruijn index.
export
mkVar : (sc : Scope) -> VarName -> Maybe (Var sc)
mkVar sc nm = (\(Element n prf) => V n nm prf) <$> mkIsVar sc nm

export
{sc : _} -> Interpolation (Var sc) where
  interpolate (V pos _ p) = "\{getName sc pos @{p}} (\{show pos})"

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
Embeddable Var where
  embed (V p n prf) = V p n (embedIsVar prf)

export
Shiftable Var where
  genShift sol son v =
    case locateVar sol v of
      Left  v2 => embed v2
      Right v2 => weakenVar sol $ weakenVar son v2
