module Util

import public Data.List.Quantifiers
import public Data.Vect
import public Hedgehog
import public Text.ILex

%default total

export
blockChar : Gen Char
blockChar =
  frequency
    [ (10, printableUnicode)
    , (1, element ['\n', '\t', '\r'])
    ]

export
blockEnd : Gen String
blockEnd = ("/*" ++) <$> string (linear 0 20) blockChar

logErr : Interpolation e => Either (ParseError e) a -> PropertyT ()
logErr (Left x)  = footnote "\{x}"
logErr (Right _) = pure ()

parameters {auto sa : Show a}
           {auto ea : Eq a}
           {auto se : Show e}
           {auto ee : Eq e}
           {auto ia : Interpolation a}
           {auto ie : Interpolation e}
           {auto mb : MapBounds a}

  export
  roundtrip : Parser1 (BBErr e) a -> Gen a -> Property
  roundtrip p g =
    property $ Prelude.do
      t <- forAll g
      let res := parseString p Virtual "\{t}"
      logErr res
      Right t === map clearBounds res

  export
  roundtripBlock : Parser1 (BBErr e) a -> Gen a -> Property
  roundtripBlock p g =
    property $ Prelude.do
      [t,b] <- forAll $ hlist [g, blockEnd]
      let res := parseString p Virtual "\{t}\{b}"
      logErr res
      Right t === map clearBounds res
