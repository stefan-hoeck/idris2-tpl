module TypedLambda.Gen

import public Data.Vect
import public Hedgehog
import public TPL.Lambda.Typed.Declaration
import public TPL.Lambda.Typed.Term
import public Text.ByteBounds

%default total

export
bb : Gen ByteBounds
bb = pure NoBB

export
identchar : Gen Char
identchar = frequency [(10,alphaNum),(1, element ['_', '\''])]

export
varname : Gen VarName
varname = (VN . fastPack) <$> [| alpha :: list (linear 0 6) identchar |]

export
tpename : Gen VarName
tpename = (VN . fastPack) <$> [| upper :: list (linear 0 6) identchar |]

export
tpeVar : Gen RawTpe
tpeVar =
  frequency
    [ (1, PVar NoBB <$> element ["Nat", "Bool", "Unit"])
    , (1, PVar NoBB <$> tpename)
    ]

export
tpe : Gen RawTpe
tpe = go 5
  where
    go : Nat -> Gen RawTpe
    go 0 = tpeVar
    go (S k) = frequency [(1,tpeVar),(2,[| PFun bb (go k) (go k) |])]

export
aliases : Gen Declaration
aliases = [| Alias bb tpename tpe |]

export
decl : Gen Declaration
decl = [| Decl bb tpename tpe |]
