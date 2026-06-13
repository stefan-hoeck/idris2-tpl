module BoolExp

import Data.Vect
import Hedgehog
import TPL.BoolExp.Parser
import Text.ILex

%default total

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
prop_roundtrip =
  property $ Prelude.do
    t <- forAll terms
    Right t === parseString term Virtual "\{t}"

export
props : Group
props =
  MkGroup "TPL.BoolExp.Term"
    [ ("prop_roundtrip", prop_roundtrip)
    ]
