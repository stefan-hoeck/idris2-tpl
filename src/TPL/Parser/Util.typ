== Parsing

Before we dive into the first examples from the book, we are going
to have a look at a fundamental and non-trivial
aspect of writing a programming language: Parsing.

Writing a correct, performant parser is a non-trivial task in my experience,
no matter the tools and libraries we are going to be using. A lot of ink
has been spilt on the topic, and I did my own share of experimenting
with different approaches in #Idris2.

```idris
module TPL.Parser.Util

import public Data.DPair
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
identchar : RExp True
identchar = alphaNum <|> '_' <|> '\''

export
ident : RExp True
ident = alpha >> star identchar

export
proj : RExp True
proj = '.' >> ident

export
uident : RExp True
uident = upper >> star identchar

export
linecomment : RExp True
linecomment = "--" >> star dot

export
lambda : RExp True
lambda = '\\' <|> 'λ'

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
  spaced ss = dfa $ jsonSpaced (ignore linecomment :: ss)

parameters {auto hs : HasStack s (Exists p)}
           {auto sk : s q}

  export %inline
  eputAs : p x -> a -> F1 q a
  eputAs v r = putStackAs (Evidence _ v) r

  export %inline
  ewithStack : ({0 x : _} -> p x -> F1 q a) -> F1 q a
  ewithStack f = withStack $ \(Evidence _ v) => f v

parameters {auto hs : HasStack s (Exists p)}
           {auto sk : s q}
           {auto hb : HasBytes s}

  export %inline
  eboundsWithStack : ({0 x : _} -> ByteBounds -> p x -> F1 q b) -> F1 q b
  eboundsWithStack f = bounds >>= \b => ewithStack (f b)

  export %inline
  eboundedWithStack : ({0 x : _} -> ByteBounded a -> p x -> F1 q b) -> a -> F1 q b
  eboundedWithStack f v = bounds >>= \b => ewithStack (f $ B v b)
```

// vi: filetype=idris2:syntax=typst

