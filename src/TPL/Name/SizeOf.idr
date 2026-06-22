-- shamelessly stolen from the Idris compiler sources
module TPL.Name.SizeOf

import Data.SnocList
import Data.SnocList.HasLength
import TPL.Name.LSizeOf

%default total

public export
record SizeOf {a : Type} (sx : SnocList a) where
  constructor SO
  size        : Nat
  0 hasLength : HasLength size sx

export
0 theList : SizeOf {a} sx -> SnocList a
theList _ = sx

public export
Lin : SizeOf [<]
Lin = SO Z Z

public export
(:<) : SizeOf as -> (0 a : _) -> SizeOf (as :< a)
SO n p :< _ = SO (S n) (S p)

public export
zero : SizeOf [<]
zero = SO Z Z

public export
suc : SizeOf as -> SizeOf (as :< a)
suc (SO n p) = SO (S n) (S p)

-- ||| suc but from the right
export
sucL : SizeOf as -> SizeOf ([<a] ++ as)
sucL (SO n p) = SO (S n) (sucL p)

public export
(<><) : SizeOf {a} sx -> LSizeOf {a} ys -> SizeOf (sx <>< ys)
SO m p <>< LSO n q = SO (n + m) (hlFish p q)

public export
(<>>) : SizeOf {a} sx -> LSizeOf {a} ys -> LSizeOf (sx <>> ys)
SO m p <>> LSO n q = LSO (m + n) (hlChips p q)

export
cast : LSizeOf {a} xs -> SizeOf {a} (cast xs)
cast = ([<] <><)

export
(+) : SizeOf sx -> SizeOf sy -> SizeOf (sx ++ sy)
SO m p + SO n q = SO (n + m) (hlAppend p q)

export
mkSizeOf : (sx : SnocList a) -> SizeOf sx
mkSizeOf sx = SO (length sx) (mkHasLength sx)

export
reverse : SizeOf sx -> SizeOf (reverse sx)
reverse (SO n p) = SO n (hlReverse p)

export
map : SizeOf sx -> SizeOf (map f sx)
map (SO n p) = SO n (cast (sym $ lengthMap sx) p) where

  lengthMap : (sx : _) -> SnocList.length (map f sx) === SnocList.length sx
  lengthMap [<] = Refl
  lengthMap (sx :< x) = cong S (lengthMap sx)
