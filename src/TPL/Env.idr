module TPL.Env

import public Data.SortedMap
import public TPL.Name.Var

%default total

export
infixl 3 ::=

public export
0 Env : Type -> Type
Env = SortedMap VarName

public export
record Entry a where
  constructor (::=)
  name : VarName
  val  : a

public export
0 Entries : Type -> Type
Entries = List . Entry

export %inline
toPair : Functor f => (a -> f b) -> Entry a -> f (VarName, b)
toPair g (name ::= val) = (name,) <$> g val

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

--------------------------------------------------------------------------------
-- Local Env
--------------------------------------------------------------------------------

public export
data Local : (a : Type) -> Scope -> Type where
  Lin  : Local a [<]
  (:<) : {0 n : VarName} -> (sv : Local a sc) -> (v : a) -> Local a (sc:<n)

export
getIsVar : (n : Nat) -> (0 p : IsVar n nm sc) -> Local a sc -> a
getIsVar 0     IZ     (_:<v)  = v
getIsVar (S k) (IS p) (sv:<_) = getIsVar k p sv

export %inline
getVar : Var sc -> Local a sc -> a
getVar (V pos _ p) sv = getIsVar pos p sv

