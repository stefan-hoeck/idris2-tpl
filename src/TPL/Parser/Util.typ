#import "template.typ": *

== Parsing <parsing>

Before we dive into the first examples from the book, we are going
to have a look at a fundamental and non-trivial
aspect of writing a programming language: Parsing.

Writing a correct, performant parser is a non-trivial task in my experience,
no matter the tools and libraries we are going to be using. A lot of ink
has been spilt on the topic, and I did my own share of experimenting
with different approaches in #Idris2. Currently, my favorite way of
writing parsers is to manually implement an LR parser @LR_parser, using
#ilex for defining the lexical analyzers plus a dedicated sum
type representing a parser stack of partially assembled syntax trees.

While probably more cumbersome to write as when using a parser
generator @Compiler_compiler, this approach benefits from the guidance
provided by the #Idris2 type checker and in general results in
small and efficient parser implementations.

In addition, the approach presented here comes with some important
benefits. Parsers written in this style

- are provably total
- are stack safe even in the presence of deeply nested syntax trees
- can be used to stream huge amounts of data in constant
  memory with no or only minor adjustments
- have been shown to process dozens to hundreds of
  megabytes of data per second on modern hardware
- have UTF-8 support builtin

=== Lexicographic Tokens

The core idea is to use different DFA (deterministic finite automata @DFA)
depending on the current parser state and assign a state transition
function operating on the (mutable) parser state to each lexicographic
token recognized by such an automaton.

#ilex provides a simple, convenient DSL (domain specific langauge) for
describing the regular expressions @regular_expression corresponding to
a lexicographic token.

For instance, we can describe the different forms of natural number
literals accepted by the languages described in this project using
ABNF (augmented Backus-Naur form @ABNF) as follows:

```abnf
NAT       = "0"
          / %x31-39 1*DIGIT
          / "0x" 1*HEXIT
          / "0o" 1*OCTIT
          / "0b" 1*BIT

DIGIT     = %x30-39 ; '0'-'9'
OCTIT     = %x30-37 ; '0'-'7'
BIT       = %x30-31 ; '0'-'1'
HEXIT     = DIGIT
          / %x41-46 ; 'A'-'F'
          / %x61-66 ; 'a'-'f'
```

Using the DSL from #ilex, these expressions can be described as follows
(`binary`, `octal`, and `hexadecimal` are predefined in #ilex as is
the expression for natural numbers in decimal form).

```idris
module TPL.Parser.Util

import public Data.DPair
import public TPL.Name
import public Text.ILex
import public Text.ILex.DStack
import Syntax.T1

%default total
%hide Data.Linear.(.)


export
binNat : RExp True
binNat = like "0b" >> binary

export
octNat : RExp True
octNat = like "0o" >> octal

export
hexNat : RExp True
hexNat = like "0x" >> hexadecimal
```

Likewise, we can define the expressions for lower- and upper-case
identifiers:

```abnf
IDENT      = LOWER *IDENT_CHAR

UIDENT     = UPPER *IDENT_CHAR

IDENT_CHAR = ALPHA / DIGIT / '_' / %x27
ALPHA      = UPPER / LOWER
UPPER      = %x41-5a ; 'A'-'Z'
LOWER      = %x61-7a ; 'a'-'z'
```

An with the #ilex DSL:


```idris
export
identchar : RExp True
identchar = alphaNum <|> '_' <|> '\''

export
ident : RExp True
ident = alpha >> star identchar

export
uident : RExp True
uident = upper >> star identchar
```

Some languages will also have support for record field projections:

```abnf
PROJ = '.' IDENT
```

And in #ilex:

```idris
export
proj : RExp True
proj = '.' >> ident
```

Finally, a common part of lexing is to recognize and drop arbitrary
whitespace and comments between proper tokens:

```abnf
WS        = *(WHITE / COMMENT)
WHITE     = 1*(%x0a / %x0d / %x09 / %x20); whitespace
COMMENT   = %x2d.2d *PRINTABLE; line comment starting with '--'
PRINTABLE = %x20-7e / %xa0-d7ff / %xe000-10ffff; non-control codepoints
```

The definition of whitespace corresponds to the one of
JSON, which is already available from #ilex. Comments can be defined
as follows:

```idris
export
linecomment : RExp True
linecomment = "--" >> star dot
```

Finally, lambda abstractions:

```idris
export
lambda : RExp True
lambda = '\\' <|> 'λ'
```

=== State Transitions

In order to define proper lexers, we have to pair regular expressions
with (linear) functions, which will update the mutable parser state
and return an index representing the next lexer to use.

Here's an example dealing with natural number literals:

```idris
parameters {auto hb : HasBytes s}

  export %inline
  nats : (f : s q => Integer -> F1 q (Index sz)) -> Steps q sz s
  nats f =
    [ bytes binNat (f . binary . drop 2)
    , bytes octNat (f . octal . drop 2)
    , bytes hexNat (f . hexadecimal . drop 2)
    , bytes decimal (f . decimal)
    ]
```

This requires some explanation: `s q` is the current mutable parser stack.
It is parameterized over state thread `q` and updating it is a linear function
again parameterized over `q` (see the #ref1 library for a
thorough discussion about this technique).

Value `sz` (of type `Bits32`) is the number of different lexers used by
the parser in question and `Index sz` wraps a value strictly smaller than
`sz` and represents one of these lexers (they are stored in an array and
can be conveniently and safely accessed vias this index).

So, in order to parse natural number literals, we need a linear function
that takes an integer as input and updates the parser state returning
the next lexer to use in the process. Using this function (`f` in the code
above), we can pair our regular expressions with proper state updating
functions and group them in a list.

Parsing boolean constants work similarly, but the regular expressions
are much simpler (we slightly extend ABNF here and add support for
case-sensitive string literals, which must be prefixed with `%s`):

```abnf
BOOL     = %s"true" / %s"false"
```

In #Idris2, the regular expressions are so simple that there is no
need to defined them outside the list of parser steps:

```idris
  export %inline
  bools : (f : s q => Bool -> F1 q (Index sz)) -> Steps q sz s
  bools f =
    [ step "true" (f True)
    , step "false" (f False)
    ]
```

Unlike function `bytes`, which was used for recognizing and handling
integer literals, function `step` does not provide the byte vector
corresponding to the recognized expressions, which is convenient
if the expression correspond to a constant literal.

Next come utilities for recognizing identifiers and
variables:

```idris
  export %inline
  idents : (f : s q => String -> F1 q (Index sz)) -> Steps q sz s
  idents f = [string ident f]

  export %inline
  varName : (f : s q => ByteBounded VarName -> F1 q (Index sz)) -> Steps q sz s
  varName f = [string ident (\s => bounded' (VN s) >>= f)]

  export %inline
  upperName : (f : s q => ByteBounded VarName -> F1 q (Index sz)) -> Steps q sz s
  upperName f = [string uident (\s => bounded' (VN s) >>= f)]
```

And finally, a lexing table entry for lexers that recognize and
discard whitespace and comments:

```idris
  export %inline
  spaced : Index r -> Steps q r s -> Entry r (DFA q r s)
  spaced x ss = E x $ dfa $ jsonSpaced (ignore linecomment :: ss)
```

// vi: filetype=idris2:syntax=typst

