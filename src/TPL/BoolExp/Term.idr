module TPL.BoolExp.Term

import Data.SortedSet
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

export
isConst : Term -> Bool
isConst (TVal v) = True
isConst _        = False

export
constants : Term -> SortedSet Value
constants (TVal v)    = singleton v
constants (TIf i t e) = constants i `union` (constants t `union` constants e)

export
size : Term -> Nat
size (TVal _)    = 1
size (TIf i t e) = size i + size t + size e + 1

export
depth : Term -> Nat
depth (TVal _)    = 1
depth (TIf i t e) = max (depth i) (max (depth t) (depth e))

--------------------------------------------------------------------------------
-- Casts
--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------
-- Evaluation
--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------
-- Pretty Printing
--------------------------------------------------------------------------------

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
