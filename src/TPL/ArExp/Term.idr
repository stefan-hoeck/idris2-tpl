module TPL.ArExp.Term

import Data.SortedSet
import Derive.Prelude

%default total
%language ElabReflection

public export
data Term : Type where
  TTrue  : Term -- true
  TFalse : Term -- false
  TIf    : (i,t,e : Term) -> Term -- if then else
  TZ     : Term -- zero
  TSucc  : Term -> Term -- succ
  TPred  : Term -> Term -- pred
  TIsZ   : Term -> Term -- iszero

%runElab derive "Term" [Show,Eq,Ord]

export
isConst : Term -> Bool
isConst TTrue  = True
isConst TFalse = True
isConst TZ     = True
isConst _      = False

export
constants : Term -> SortedSet Term
constants TTrue       = singleton TTrue
constants TFalse      = singleton TFalse
constants TZ          = singleton TZ
constants (TIf i t e) = constants i `union` (constants t `union` constants e)
constants (TSucc x)   = constants x
constants (TPred x)   = constants x
constants (TIsZ x)    = constants x

export
size : Term -> Nat
size TTrue       = 1
size TFalse      = 1
size TZ          = 1
size (TIf i t e) = size i + size t + size e + 1
size (TSucc x)   = size x + 1
size (TPred x)   = size x + 1
size (TIsZ x)    = size x + 1

export
depth : Term -> Nat
depth TTrue       = 1
depth TFalse      = 1
depth TZ          = 1
depth (TIf i t e) = max (depth i) (max (depth t) (depth e))
depth (TSucc x)   = depth x + 1
depth (TPred x)   = depth x + 1
depth (TIsZ x)    = depth x + 1

--------------------------------------------------------------------------------
-- Casts
--------------------------------------------------------------------------------

export
Cast Nat Term where
  cast Z     = TZ
  cast (S k) = TSucc (cast k)

export
Cast Bool Term where
  cast True  = TTrue
  cast False = TFalse

export %inline
nat : Nat -> Term
nat = cast

export %inline
bool : Bool -> Term
bool = cast

--------------------------------------------------------------------------------
-- Pretty Printing
--------------------------------------------------------------------------------

pretty : Term -> String

paren : Term -> String
paren t = if isConst t then pretty t else "(\{pretty t})"

pretty TTrue       = "true"
pretty TFalse      = "false"
pretty (TIf i t e) = "if \{pretty i} then \{pretty t} else \{pretty e}"
pretty TZ          = "0"
pretty (TSucc x)   = "succ \{paren x}"
pretty (TPred x)   = "pred \{paren x}"
pretty (TIsZ x)    = "iszero \{paren x}"

export %inline
Interpolation Term where interpolate = pretty
