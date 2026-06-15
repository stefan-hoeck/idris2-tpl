module TPL.Name.Var

import Data.DPair
import Decidable.HDecEq
import public TPL.Name
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

--------------------------------------------------------------------------------
-- Var
--------------------------------------------------------------------------------

||| A variable in scope represented as a de Bruijn index into said scope.
public export
record Var (sc : Scope) where
  constructor V
  pos    : Nat
  0 name : VarName
  0 prf  : IsVar n name sc

||| Tries to find a name in a scope and convert it to a de Bruijn index.
export
mkVar : (sc : Scope) -> VarName -> Maybe (Var sc)
mkVar sc nm = (\(Element n prf) => V n nm prf) <$> mkIsVar sc nm
