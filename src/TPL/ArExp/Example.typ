#import "template.typ": *

== Example Applications

Below are a couple of example applications plus
a utility for testing them at the REPL. Of special
interest are the ill-typed example programs:
These demonstrate the proper highliting of the invalid
regions in the source code.

```idris
module TPL.ArExp.Example

import public TPL.ArExp.Parser

%default total

twelve : String
twelve =
  """
  if (iszero (pred (pred (pred 3))))
     then 12
     else (if false then 0b101 else 0b111)
  """

typeErr : String
typeErr =
  """
  if (iszero (pred (pred (pred 3))))
     then 12
     else (if false then true else 0b111)
  """

typeErr2 : String
typeErr2 =
  """
  if (pred (pred (pred 3)))
     then 12
     else (if false then true else 0b111)
  """

typeErrMultiline : String
typeErrMultiline =
  """
  if (pred
       (pred
         (pred 3)))
     then 12
     else (if false then true else 0b111)
  """

export
parseEval : String -> Either ArErr String
parseEval s = Prelude.do
  t <- runString term s
  (tpe ** v) <- typeCheck t
  Right $ case tpe of
    TNat  => "Nat: \{show $ eval v}"
    TBool => "Bool: \{show $ eval v}"

export
testAr : String -> IO ()
testAr s =
  case parseEval s of
    Left x  => putStrLn "\{toParseError Virtual s x}"
    Right s => putStrLn s
```

// vi: filetype=idris2:syntax=typst
