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

public export
data ScopedEnv : (p : t -> Type) -> Scope t -> Type where
  Lin  : ScopedEnv p [<]
  (:<) : {0 v : t} -> ScopedEnv p sc -> (term : p v) -> ScopedEnv p (sc:<v)

envValImpl : ScopedEnv p sc -> IsVar pos x sc -> p x
envValImpl (_:<trm) IZ = trm
envValImpl (i:<_)   (IS prf) = envValImpl i prf

export %inline
envVal : NVar v sc -> ScopedEnv p sc -> p v
envVal (NV p prf) env = envValImpl env (fromNat p prf)
