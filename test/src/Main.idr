module Main

import BoolExp
import Hedgehog

%default total

main : IO ()
main =
  test
    [ BoolExp.props
    ]
