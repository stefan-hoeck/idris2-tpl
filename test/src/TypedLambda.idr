module TypedLambda

import Text.ILex
import TPL.Lambda.Typed.Parser
import TypedLambda.Gen

%default total

prop_aliasRoundTrip : Property
prop_aliasRoundTrip =
  property $ Prelude.do
    d <- forAll aliases
    Right [d] === map clearBounds (parseString decls Virtual "\{d}")

prop_declRoundTrip : Property
prop_declRoundTrip =
  property $ Prelude.do
    d <- forAll decl
    Right [d] === map clearBounds (parseString decls Virtual "\{d}")

prop_defnRoundTrip : Property
prop_defnRoundTrip =
  property $ Prelude.do
    d <- forAll defn
    Right [d] === map clearBounds (parseString decls Virtual "\{d}")

prop_evalRoundTrip : Property
prop_evalRoundTrip =
  property $ Prelude.do
    d <- forAll eval
    Right [d] === map clearBounds (parseString decls Virtual "\{d}")


export
props : Group
props =
  MkGroup "TPL.Lambda.Typed"
    [ ("prop_aliasRoundTrip", prop_aliasRoundTrip)
    , ("prop_declRoundTrip", prop_declRoundTrip)
    , ("prop_defnRoundTrip", prop_defnRoundTrip)
    , ("prop_evalRoundTrip", prop_evalRoundTrip)
    ]
