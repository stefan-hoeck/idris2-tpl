module TPL.ArExp.Term

import Data.SortedSet
import Derive.Prelude
import Text.ByteBounds

%default total
%language ElabReflection

public export
data Term : Type where
  TTrue  : ByteBounds -> Term -- true
  TFalse : ByteBounds -> Term -- false
  TIf    : ByteBounds -> (i,t,e : Term) -> Term -- if then else
  TZ     : ByteBounds -> Term -- zero
  TSucc  : ByteBounds -> Term -> Term -- succ
  TPred  : ByteBounds -> Term -> Term -- pred
  TIsZ   : ByteBounds -> Term -> Term -- iszero

%runElab derive "Term" [Show,Eq]

export
Cast Term ByteBounds where
  cast (TTrue x)     = x
  cast (TFalse x)    = x
  cast (TZ x)     = x
  cast (TSucc x _)   = x
  cast (TPred x _)   = x
  cast (TIsZ x _)    = x
  cast (TIf x _ _ _) = x

export
adjBounds : (ByteBounds -> ByteBounds) -> Term -> Term
adjBounds f (TTrue x)     = TTrue (f x)
adjBounds f (TFalse x)    = TFalse (f x)
adjBounds f (TIf x i t e) =
  TIf (f x) (adjBounds f i) (adjBounds f t) (adjBounds f e)
adjBounds f (TZ x)        = TZ (f x)
adjBounds f (TSucc x y)   = TSucc (f x) (adjBounds f y)
adjBounds f (TPred x y)   = TPred (f x) (adjBounds f y)
adjBounds f (TIsZ x y)    = TIsZ (f x) (adjBounds f y)

export %inline
emptyBounds : Term -> Term
emptyBounds = adjBounds (const NoBB)

export
isConst : Term -> Bool
isConst (TTrue {})  = True
isConst (TFalse {}) = True
isConst (TZ {})     = True
isConst _           = False

export
size : Term -> Nat
size (TTrue {})    = 1
size (TFalse {})   = 1
size (TZ {})       = 1
size (TIf _ i t e) = size i + size t + size e + 1
size (TSucc _ x)   = size x + 1
size (TPred _ x)   = size x + 1
size (TIsZ _ x)    = size x + 1

export
depth : Term -> Nat
depth (TTrue {})    = 1
depth (TFalse {})   = 1
depth (TZ {})       = 1
depth (TIf _ i t e) = max (depth i) (max (depth t) (depth e))
depth (TSucc _ x)   = depth x + 1
depth (TPred _ x)   = depth x + 1
depth (TIsZ _ x)    = depth x + 1

--------------------------------------------------------------------------------
-- Casts
--------------------------------------------------------------------------------

export
nat : ByteBounds -> Nat -> Term
nat bb Z     = TZ bb
nat bb (S k) = TSucc bb (nat bb k)

export %inline
int : ByteBounded Integer -> Term
int (B i bb) = nat bb $ cast i

export %inline
bool : ByteBounded Bool -> Term
bool (B True bb)  = TTrue bb
bool (B False bb) = TFalse bb

--------------------------------------------------------------------------------
-- Values
--------------------------------------------------------------------------------

public export
data Value : Type where
  VTrue  : Value
  VFalse : Value
  VZero  : Value
  VSucc  : Value -> Value

%runElab derive "Value" [Show,Eq,Ord]

--------------------------------------------------------------------------------
-- Pretty Printing
--------------------------------------------------------------------------------

pretty : Term -> String

paren : Term -> String
paren t = if isConst t then pretty t else "(\{pretty t})"

pretty (TTrue _)     = "true"
pretty (TFalse _)    = "false"
pretty (TIf _ i t e) = "if \{pretty i} then \{pretty t} else \{pretty e}"
pretty (TZ _)        = "0"
pretty (TSucc _ x)   = "succ \{paren x}"
pretty (TPred _ x)   = "pred \{paren x}"
pretty (TIsZ _ x)    = "iszero \{paren x}"

export %inline
Interpolation Term where interpolate = pretty

prettyV : Value -> String

parenV : Value -> String
parenV v@(VSucc {}) = "(\{prettyV v})"
parenV v            = prettyV v

prettyV VTrue       = "true"
prettyV VFalse      = "false"
prettyV VZero       = "0"
prettyV (VSucc x)   = "succ \{parenV x}"

export %inline
Interpolation Value where interpolate = prettyV
