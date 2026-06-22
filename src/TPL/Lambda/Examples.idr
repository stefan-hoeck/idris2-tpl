module TPL.Lambda.Examples

import Text.ILex
import public TPL.Lambda.Parser
import public TPL.Name.Var

%default total

export
zero : String
zero = "λs.λz.z"

export
scc : String
scc = "λn.λs.λz.s (n s z)"

export
one : String
one = "λs.λz.s z"

export
two : String
two = "λs.λz.s (s z)"

export
pls : String
pls = "λm.λn.λs.λz.m s (n s z)"

export
tru : String
tru = "λx.λy.x"

export
fls : String
fls = "λx.λy.y"

export
and : String
and = "λx.λy.x y (\{fls})"

export
test : String
test = "λb.λx.λy.b x y"

export
not : String
not = "λb.λx.λy.b y x"

covering
testEval : String -> IO ()
testEval s =
  case parseString term Virtual s of
    Left x => putStrLn "\{x}"
    Right t =>
      traverse_ (putStrLn . interpolate . restore . eval) (closed t)
