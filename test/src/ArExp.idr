module ArExp

import Util
import TPL.ArExp.Parser

%default total

values : Gen Term
values = element [TTrue NoBB, TFalse NoBB, TZ NoBB]

terms : Gen Term
terms = go 5
  where
    go : Nat -> Gen Term
    go 0     = values
    go (S k) =
      frequency
        [ (1, values)
        , (2, TSucc NoBB <$> go k)
        , (2, TPred NoBB <$> go k)
        , (2, TIsZ NoBB <$> go k)
        , (2, [| TIf (pure NoBB) (go k) (go k) (go k) |])
        ]

prop_roundtrip : Property
prop_roundtrip = roundtrip term terms

prop_roundtripBlock : Property
prop_roundtripBlock = roundtripBlock term terms

export
props : Group
props =
  MkGroup "TPL.ArExp.Term"
    [ ("prop_roundtrip", prop_roundtrip)
    , ("prop_roundtripBlock", prop_roundtripBlock)
    ]
