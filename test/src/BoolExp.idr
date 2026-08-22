module BoolExp

import Util
import TPL.BoolExp.Parser

%default total

MapBounds Term where
  mapBounds f t = t

values : Gen Value
values = element [VTrue, VFalse]

terms : Gen Term
terms = go 4
  where
    go : Nat -> Gen Term
    go 0     = map TVal values
    go (S k) =
      frequency
        [ (1, map TVal values)
        , (2, [| TIf (go k) (go k) (go k) |])
        ]

prop_roundtrip : Property
prop_roundtrip = roundtrip term terms

prop_roundtripBlock : Property
prop_roundtripBlock = roundtripBlock term terms

export
props : Group
props =
  MkGroup "TPL.BoolExp.Term"
    [ ("prop_roundtrip", prop_roundtrip)
    , ("prop_roundtripBlock", prop_roundtripBlock)
    ]
