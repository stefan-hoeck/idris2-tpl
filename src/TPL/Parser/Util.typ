#import "template.typ": *

== Parsing <parsing>

Before we dive into the first examples from the book, we are going
to have a look at a fundamental and non-trivial
aspect of writing a programming language: Parsing.

Writing a correct, performant parser is a non-trivial task in my experience,
no matter the tools and libraries we are using. A lot of ink
has been spilt on the topic, and I did my own share of experimenting
with different approaches in #Idris2. Currently, my favorite way of
writing parsers is to manually implement an LR parser @LR_parser, using
#ilex for defining the lexical analyzers plus a dedicated sum
type representing a parser stack of partially assembled syntax trees.

While probably more cumbersome to write than using a parser
generator @Compiler_compiler, this approach benefits from the guidance
provided by the #Idris2 type checker and in general results in
small and efficient parser implementations. Parsing also feels less
like a black box in my opinion.

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

#ilex provides a simple, convenient DSL (domain specific language) for
describing the regular expressions @regular_expression corresponding to
the lexicographic tokens.

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
import Text.ILex.Derive
import Syntax.T1

%default total
%language ElabReflection
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

Likewise, we can define expressions for lower- and upper-case
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
WS      = *(WHITE / COMMENT / BLOCK)
WHITE   = 1*(%x0a / %x0d / %x09 / %x20); whitespace
COMMENT = %x2d.2d *DOT; line comment starting with '--'
DOT     = %x20-7e / %xa0-d7ff / %xe000-10ffff; non-control codepoints
BLOCK   = "/*" *(*BCHAR / BLOCK) "*/"
BCHAR   = DOT / %x0a / %x0d / %x09
```

The definition of whitespace corresponds to the one of
JSON, which is already available from #ilex. Comments can be defined
as follows:

```idris
export
linecomment : RExp True
linecomment = "--" >> star dot

blockChar : RExp True
blockChar = (dot && not '*' &&  not '/') <|> oneof ['\n', '\r', '\t']
```

Finally, lambda abstractions:

```idris
export
lambda : RExp True
lambda = '\\' <|> 'λ'
```

=== Parser State

An #ilex parser consists of a non-empty array of lexers, where
each lexer is defined as a list of regular expressions paired
with a parser state transition function. These state transition
functions read and update the mutable parser state and
return an index into the array of lexers, thus telling the
#ilex runloop with which lexer to continue after a token was
recognized and processed.

The parser state typically is a record consisting of mutable
and immutable fields, some of which are mandatory while others
can be used for custom usage. Here is the definition of the
parser state we are going to use in this project:

```idris
public export
record TPLState (e,s,a : Type) (r : Bits32) (q : Type) where
  [search q]
  constructor TS
  -- Position and token bounds
  bufSize_    : Nat
  prev_       : ByteString
  cur_        : IBuffer bufSize_
  prevOffset_ : Nat
  curOffset_  : Nat
  from_       : Ref q (LTENat bufSize_)
  till_       : Ref q (LTENat bufSize_)
  positions_  : Ref q (SnocList BytePos)

  -- Current state
  stack_     : Ref q s
  state_     : Ref q (Index r)
  decls      : Ref q (SnocList a)

  -- Working with string literals
  strings_   : Ref q (SnocList String)

  -- Error handling
  error_     : Ref q (Maybe $ BBErr e)

  -- Block comments
  comment    : Index r
  depth      : Ref q Nat

%runElab derive "TPLState" [FullStack]
```

Let's digest this a bit. The first couple of fields are mandatory, as they
allow the #ilex run loop to update the byte position of the start and
end byte of the current token (`from_` and `till_`) and to keep track
of the opening positions of things like nested parentheses (`positions_`).
The immutable fields represent the buffer currently being processed
(`cur_`) plus its size (`bufSize_`). Stuff prefixed with `prev` is used
for streaming: It is used to keep track of the running total position of
the tokens as well as the byte prefix of the current token (if any).
All this is handled by the #ilex run loop. Client code should access
the relevant information via high-level functions provided through
the `HasBytes` interface.

Fields `stack_`, `state_`, and `decls` represent the accumulated
parser state: `stack_` holds the parser stack of partially processed
syntax trees, `state_` can be used to store the current lexer
(in general, we only use this when processing block comments),
and `decl` allows us to store and extract
the top level declarations processed so far.

For convenient parsing and un-escaping of string literals,
#ilex offers the `HasStringLits` interface, which requires the
parser state to have a field called `strings_` of the given type.
Likewise, interface `HasBBErr` is used for error handling and
requires a field called `error_` of the given type.

In addition to these, we provide two custom fields for working
with block comments: `comment` is the index of the block comment
lexer, and `depth` is used to keep track of nested block comments.

Implementations of the interfaces mentioned above
(`HasBytes`, `HasStringLits`, `HasStack`, and `HasBBErr`) can
be derived automatically using elaborator reflection. All that's
required is that the state fields have the correct names and types.

Before we can look at state transition functions, we need to
provide an initialization function for the parser state:

```idris
export
init :
     (comment : Index r)
  -> (stack   : s)
  -> (n : Nat)
  -> IBuffer n
  -> F1 q (TPLState e s a r q)
init c v n buf = T1.do
  rf <- ref1 (first n)
  rt <- ref1 (first n)
  ps <- ref1 [<]
  sk <- ref1 v
  st <- ref1 c
  ds <- ref1 [<]
  ss <- ref1 [<]
  er <- ref1 Nothing
  dp <- ref1 Z
  pure (TS n empty buf 0 0 rf rt ps sk st ds ss er c dp)
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

This requires some explanation: `s q` is the current mutable parser state.
It is parameterized over state thread `q` and updating it is a linear function
again parameterized over `q` (see the #ref1 library for a
thorough discussion of this technique).

Value `sz` (of type `Bits32`) is the number of different lexers used by
the parser in question and `Index sz` wraps a value strictly smaller than
`sz` and represents one of these lexers (they are stored in an array and
can be conveniently and safely accessed via this index).

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
discard whitespace and comments. For (potentially nested) block
comments, we need to keep track of the level of nesting.

```idris
%inline
startCmt : TPLState e s a r q => Index r -> F1 q (Index r)
startCmt @{st} x = writeAs st.state_ x st.comment

export %inline
spaced :
     Index r
  -> Steps q r (TPLState e s a r)
  -> Entry r (DFA q r $ TPLState e s a r)
spaced x ss =
  E x $ dfa $ jsonSpaced $
    ignore linecomment :: step "/*" (startCmt x) :: ss
```

We also need to provide a lexer for recognizing tokens within
a block comment. #ilex runs all its lexers without looking
ahead or backtracking while using a maximum munch strategy.
This means, that if we are not careful, a string like `abc*/` will not be
recognized as the end of a block comment, unless we make sure,
we handle the special characters `*` and `/` separately.

If we encounter another opening tag, we increase the parser state's
`depth` counter by one. On the other hand, if we encounter a
closing tag, we exit and restore the previous lexer unless
we are in a nested block comment (in which case the counter
at `depth` is larger than zero), in which case we decrease the
depth by one.

Note, how we add specific expressions for single asterisk (`*`)
and forward slash characters. These must not be unified with the
other characters accepted in a block comment as this would
lead to the issues mentioned above with recognizing opening
and closing tags.

```idris
%inline
cmt : TPLState e s a r q => F1 q (Index r)
cmt @{st} t = st.comment # t

%inline
incDepth : TPLState e s a r q => F1 q (Index r)
incDepth @{st} = read1 st.depth >>= \x => writeAs st.depth (S x) st.comment

%inline
decDepth : TPLState e s a r q => F1 q (Index r)
decDepth @{st} =
  read1 st.depth >>= \case
    0   => read1 st.state_
    S k => writeAs st.depth k st.comment

export
block : DFA q r (TPLState e s a r)
block =
  dfa
    [ step (plus blockChar <|> "/" <|> "*") cmt
    , step "/*" incDepth
    , step "*/" decDepth
    ]
```

// vi: filetype=idris2:syntax=typst

