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

toTerm : Env ClosedTerm -> String -> Either (ParseError TpeErr) ClosedTerm
toTerm env s =
  mapFst (toParseError Virtual s) $ Prelude.do
    t <- runString term s
    closed env t

testEnv : Either (ParseError TpeErr) (Env ClosedTerm)
testEnv =
  mkEnv predef toTerm
    [ "zero"       ::= "λs.λz.z"
    , "one"        ::= "λs.λz.s z"
    , "two"        ::= "λs.λz.s (s z)"
    , "scc"        ::= "λn.λs.λz.s (n s z)"
    , "plus"       ::= "λm.λn.λs.λz.m s (n s z)"
    , "times"      ::= "λm.λn.m (plus n) zero"
    , "times2"     ::= "λm.λn.λs.λz. m (n s) z"
    , "pow"        ::= "λm.λn.m n"

    -- church bools
    , "tru"        ::= "λx.λy.x"
    , "fls"        ::= "λx.λy.y"
    , "and"        ::= "λx.λy.x y fls"
    , "not"        ::= "λb.λx.λy.b y x"
    , "test"       ::= "λb.λx.λy.b x y"

    -- pairs
    , "pair"       ::= "λx. λy. λb. b x y"
    , "fst"        ::= "λp. p tru"
    , "snd"        ::= "λp. p fls"

    -- combined stuff
    , "isz"        ::= "λn.n (and fls) tru"
    , "zz"         ::= "pair zero zero"
    , "ss"         ::= "λp.pair (snd p) (scc (snd p))"
    , "prd"        ::= "λn. fst (n ss zz)"
    , "sub"        ::= "λm. λn. n prd m"
    , "equal"      ::= "λm. λn. and (isz (sub m n)) (isz (sub n m))"

    -- recursion
    , "fix"        ::= "λf. (λx. f(λy. x x y)) (λx. f (λy. x x y))"

    -- conversions
    , "realbool"   ::= "λb.b true false"
    , "churchbool" ::= "λb.if b then tru else fls"
    , "realnat"    ::= "λs.s succ 0"
    , "natg"       ::= "λrec. λn. if iszero n then zero else scc (rec (pred n))"
    , "churchnat"  ::= "fix natg"
    , "realeq"     ::= "λm. λn. realbool (equal (churchnat m) (churchnat n))"
    , "factr"      ::= "λfct. λn. if realbool (equal n zero) then one else times2 n (fct (pred n))"
    , "fact"       ::= "fix factr"
    ]

covering
run : String -> Either (ParseError TpeErr) Term
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
