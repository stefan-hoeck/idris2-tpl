-- Taken from the Idris compiler sources
module TPL.Name.LSizeOf

import Data.List
import Data.List.HasLength
import Data.Nat

%default total

public export
record LSizeOf {a : Type} (xs : List a) where
  constructor LSO
  size        : Nat
  0 hasLength : HasLength size xs

export
castHL : {ys : _} -> (0 _ : List.length xs = List.length ys) -> HasLength m xs -> HasLength m ys
castHL {ys = []}      eq Z = Z
castHL {ys = y :: ys} eq (S p) = S (castHL (injective eq) p)

export
0 theList : LSizeOf {a} xs -> List a
theList _ = xs

public export
zero : LSizeOf []
zero = LSO Z Z

public export
suc : LSizeOf as -> LSizeOf (a :: as)
suc (LSO n p) = LSO (S n) (S p)

-- ||| suc but from the right
export
sucR : LSizeOf as -> LSizeOf (as ++ [a])
sucR (LSO n p) = LSO (S n) (sucR p)

export
(+) : LSizeOf xs -> LSizeOf ys -> LSizeOf (xs ++ ys)
LSO m p + LSO n q = LSO (m + n) (hasLengthAppend p q)

export
mkSizeOf : (xs : List a) -> LSizeOf xs
mkSizeOf xs = LSO (length xs) (hasLength xs)

export
reverse : LSizeOf xs -> LSizeOf (reverse xs)
reverse (LSO n p) = LSO n (hasLengthReverse p)

export
map : LSizeOf xs -> LSizeOf (map f xs)
map (LSO n p) = LSO n (castHL (sym $ lengthMap xs) p)
