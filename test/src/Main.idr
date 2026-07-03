module Main

import ArExp
import BoolExp
import TypedLambda
import Hedgehog

%default total

main : IO ()
main =
  test
    [ ArExp.props
    , BoolExp.props
    , TypedLambda.props
    ]
