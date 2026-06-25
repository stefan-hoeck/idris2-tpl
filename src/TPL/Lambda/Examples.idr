module TPL.Lambda.Examples

import Text.ILex
import public TPL.Env
import public TPL.Lambda.Parser
import public TPL.Name.Var

%default total

predef : Env ClosedTerm
predef =
  fromList
    [ ("succ",   SLam NoBB "x" $ SSucc NoBB $ SVar NoBB zero)
    , ("pred",   SLam NoBB "x" $ SPred NoBB $ SVar NoBB zero)
    , ("iszero", SLam NoBB "x" $ SIsZ  NoBB $ SVar NoBB zero)
    ]

toTerm : Env ClosedTerm -> String -> Either String ClosedTerm
toTerm env s = Prelude.do
  t <- mapFst interpolate $ parseString term Virtual s
  closed env t

testEnv : Either String (Env ClosedTerm)
testEnv =
  mkEnv predef toTerm
    [ "zero" ::= "λs.λz.z"
    , "one"  ::= "λs.λz.s z"
    , "two"  ::= "λs.λz.s (s z)"
    , "scc"  ::= "λn.λs.λz.s (n s z)"
    , "plus" ::= "λm.λn.λs.λz.m s (n s z)"
    , "tru"  ::= "λx.λy.x"
    , "fls"  ::= "λx.λy.y"
    , "and"  ::= "λx.λy.x y fls"
    , "not"  ::= "λb.λx.λy.b y x"
    , "test" ::= "λb.λx.λy.b x y"
    , "realbool" ::= "λb.b true false"
    , "realnat"  ::= "λs.s succ 0"
    , "churchbool" ::= "λb.if b then tru else fls"
    ]

covering
run : String -> Either String Term
run s = Prelude.do
  env <- testEnv
  ct  <- toTerm env s
  pure (restore $ eval ct)

covering
testEval : String -> IO ()
testEval s =
  case run s of
    Left x  => putStrLn "\{x}"
    Right t => putStrLn "\{t}"
