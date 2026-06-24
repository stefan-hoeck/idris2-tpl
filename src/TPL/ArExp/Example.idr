module TPL.ArExp.Example

import public TPL.ArExp.Parser

%default total

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

