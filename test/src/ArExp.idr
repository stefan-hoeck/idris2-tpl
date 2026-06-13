module ArExp

import Data.Vect
import Hedgehog
import TPL.ArExp.Parser
import Text.ILex

%default total

values : Gen Term
values = element [TTrue, TFalse, TZ]

terms : Gen Term
terms = go 5
  where
    go : Nat -> Gen Term
    go 0     = values
    go (S k) =
      frequency
        [ (1, values)
        , (2, TSucc <$> go k)
        , (2, TPred <$> go k)
        , (2, TIsZ <$> go k)
        , (2, [| TIf (go k) (go k) (go k) |])
        ]

prop_roundtrip : Property
prop_roundtrip =
  property $ Prelude.do
    t <- forAll terms
    Right t === parseString term Virtual "\{t}"

export
props : Group
props =
  MkGroup "TPL.ArExp.Term"
    [ ("prop_roundtrip", prop_roundtrip)
    ]
