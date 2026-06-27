module TPL.Lambda.Typed.Examples

import Text.ILex
import TPL.Lambda.Typed.Parser
import TPL.Lambda.Typed.TT

%default total

succDef : Def
succDef =
  D (TFun TNat TNat) (SLam NoBB "x" TNat $ SSucc NoBB $ SVar NoBB TNat zero)

predDef : Def
predDef =
  D (TFun TNat TNat) (SLam NoBB "x" TNat $ SPred NoBB $ SVar NoBB TNat zero)

iszeroDef : Def
iszeroDef =
  D (TFun TNat TBool) (SLam NoBB "x" TNat $ SIsZ NoBB $ SVar NoBB TNat zero)

predef : Env Def
predef =
  fromList
    [ ("succ",   succDef)
    , ("pred",   predDef)
    , ("iszero", iszeroDef)
    ]

toDef : Env Def -> String -> Either (ParseError TpeErr) Def
toDef env s =
  mapFst (toParseError Virtual s) $ Prelude.do
    t <- runString term s
    definition env t

testEnv : Either (ParseError TpeErr) (Env Def)
testEnv =
  mkEnv predef toDef
    [ "c0"        ::= "λs : Nat -> Nat . λz : Nat . z"
    , "c1"        ::= "λs : Nat -> Nat . λz : Nat . s (c0 s z)"
    , "c2"        ::= "λs : Nat -> Nat . λz : Nat . s (c1 s z)"
    , "c3"        ::= "λs : Nat -> Nat . λz : Nat . s (c2 s z)"
    , "c4"        ::= "λs : Nat -> Nat . λz : Nat . s (c3 s z)"
    , "c5"        ::= "λs : Nat -> Nat . λz : Nat . s (c4 s z)"
    , "plus"      ::= "λm : (Nat -> Nat) -> Nat -> Nat . λn : (Nat -> Nat) -> Nat -> Nat . λs : Nat -> Nat . λz : Nat . m s (n s z)"
    , "times"     ::= "λm : (Nat -> Nat) -> Nat -> Nat . λn : (Nat -> Nat) -> Nat -> Nat . λs : Nat -> Nat . λz : Nat . m (n s) z"
    , "realnat"   ::= "λf : (Nat -> Nat) -> Nat -> Nat . f succ 0"
    ]

covering
run : String -> Either (ParseError TpeErr) (t ** Value t [<])
run s = Prelude.do
  env     <- testEnv
  D t trm <- toDef env s
  pure (t ** eval trm)

covering
testEval : String -> IO ()
testEval s =
  case run s of
    Left x           => putStrLn "\{x}"
    Right (t ** trm) => putStrLn "Type: \{t}, Value: \{trm}"
