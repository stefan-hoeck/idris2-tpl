module TPL.Parser.Util

import public Text.ILex
import public Text.ILex.DStack

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
ident = (alpha <|> '_') >> star (alphaNum <|> '_' <|> '\'')

--------------------------------------------------------------------------------
-- Literals
--------------------------------------------------------------------------------

parameters {auto hp : HasPosition sk}
           {auto hb : HasBytes sk}

  export %inline
  nats : (f : sk q => Integer -> F1 q (Index sz)) -> Steps q sz sk
  nats f =
    [ conv binNat (f . binary . drop 2)
    , conv octNat (f . octal . drop 2)
    , conv hexNat (f . hexadecimal . drop 2)
    , conv decimal (f . decimal)
    ]

  export %inline
  bools : (f : sk q => Bool -> F1 q (Index sz)) -> Steps q sz sk
  bools f =
    [ cexpr (like "true") (f True)
    , cexpr (like "false") (f False)
    ]

--------------------------------------------------------------------------------
-- Identifiers
--------------------------------------------------------------------------------

  export %inline
  idents : (f : sk q => String -> F1 q (Index sz)) -> Steps q sz sk
  idents f = [read ident f]
