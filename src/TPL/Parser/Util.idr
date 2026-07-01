module TPL.Parser.Util

import public TPL.Name
import public Text.ILex
import public Text.ILex.DStack
import Syntax.T1

%default total
%hide Data.Linear.(.)

--------------------------------------------------------------------------------
-- Regular Expressions
--------------------------------------------------------------------------------

export
binNat : RExp True
binNat = like "0b" >> binary

export
octNat : RExp True
octNat = like "0o" >> octal

export
hexNat : RExp True
hexNat = like "0x" >> hexadecimal

export
ident : RExp True
ident = alpha >> star (alphaNum <|> '_' <|> '\'')

export
uident : RExp True
uident = upper >> star (alphaNum <|> '_' <|> '\'')

export
linecomment : RExp True
linecomment = "--" >> star dot

--------------------------------------------------------------------------------
-- Literals
--------------------------------------------------------------------------------

parameters {auto hb : HasBytes s}

  export %inline
  nats : (f : s q => Integer -> F1 q (Index sz)) -> Steps q sz s
  nats f =
    [ bytes binNat (f . binary . drop 2)
    , bytes octNat (f . octal . drop 2)
    , bytes hexNat (f . hexadecimal . drop 2)
    , bytes decimal (f . decimal)
    ]

  export %inline
  bools : (f : s q => Bool -> F1 q (Index sz)) -> Steps q sz s
  bools f =
    [ step (like "true") (f True)
    , step (like "false") (f False)
    ]

--------------------------------------------------------------------------------
-- Identifiers
--------------------------------------------------------------------------------

  export %inline
  idents : (f : s q => String -> F1 q (Index sz)) -> Steps q sz s
  idents f = [string ident f]

  export %inline
  varName : (f : s q => ByteBounded VarName -> F1 q (Index sz)) -> Steps q sz s
  varName f = [string ident (\s => bounded' (VN s) >>= f)]

  export %inline
  upperName : (f : s q => ByteBounded VarName -> F1 q (Index sz)) -> Steps q sz s
  upperName f = [string uident (\s => bounded' (VN s) >>= f)]

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

  export %inline
  spaced : Steps q r s -> DFA q r s
  spaced ss = dfa $ jsonSpaced (ignore' linecomment :: ss)
