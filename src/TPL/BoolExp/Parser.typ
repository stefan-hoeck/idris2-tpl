#import "../../../doc/template.typ": *

== Parsing Boolean Terms

In this section we are using the #ilex library to write a parser for
simple boolean terms. We will first specify the syntax in ABNF form before
defining a data type for the parser stack, state transition rules, and
finally assign regular expressions to state transitions.

While not as straight forward as using a library of parser combinators or
manually writing a recursive descent parser, this approach has several
advantages:

/ Totality: #ilex parsers are provably total.
/ Stack safety: #ilex parsers are stack safe even in the presence of deeply nested
  syntax trees.
/ Streaming: #ilex parsers can be used to stream huge amounts of data in constant
  memory with no or only minor adjustments.
/ Performance: #ilex parsers have been shown to process dozens to hundreds of
  megabytes of data per second on modern hardware.

=== Syntax

Below are the production rules in ABNF form:

```abnf
WS_TERM   = WS TERM WS

TERM      = VALUE
          / '(' WS_TERM ')'
          / %s"if" WS_TERM %s"then" WS_TERM %s"else" WS_TERM

VALUE     = %s"true" / %s"false"

WS        = *(WHITE / COMMENT)
WHITE     = 1*(%x0a / %x0d / %x09 / %x20); whitespace
COMMENT   = %x2d.2d *PRINTABLE; line comment starting with '--'
PRINTABLE = %x20-%x7e / %xa0-%xd7ff / %xe000-%x10ffff; non-control codepoints
```

As can be seen, the terminals are just `true` and `false`, with the non-terminals
being terms wrapped in parentheses and `if` expressions. Tokens can be separated
by whitespace and line comments.

It is not strictly necessary to add support for wrapping terms in parentheses,
but it can help with readability.

=== Types of Lexers

The syntax of our boolean expressions is simple enough that it follows just
from the top item of the parser stack what syntactic tokens are expected next.
The different sets of tokens give rise to six lexers:

```idris
module TPL.BoolExp.Parser

import Derive.Prelude
import Text.ILex.Derive
import TPL.Parser.Util
import Syntax.T1
import public TPL.BoolExp.Term

%default total
%language ElabReflection

%runElab deriveParserState "Lexers" "Lexer"
  ["TERM","THEN","ELSE","CLOSE","DONE","ERR"]
```

This defines six numeric constants representing the different
lexers that we are going to use when parsing expressions. The
actual lexers will be defined further below.

Let's have a quick look at these:

/ `TERM` : recognises `true`, `false`, `if`, or `(`
/ `THEN` : recognises `then`
/ `ELSE` : recognises `else`
/ `CLOSE`: recognises `)`
/ `DONE `: recognises only whitespace and comments
/ `ERR ` : recognises nothing, not even whitespace or comments

All lexers except `ERR` recognize and ignore whitespace and line comments.

Having an error lexer is beneficial for readability as well as
performance, because it allows us to write exceptions
to a mutable reference and continue with a lexer that will fail immediately,
without all state transition functions having to return an `Either` for error
handling.

=== Parser Stack

We define an Idris data type for representing well-typed parser stacks.
This data type only encapsulates the partial syntax trees we have parsed
so far. State transitions that produce no additional Idris values such
as recognising an `else` token will not affect the parser stack but only
switch to a different lexer.

I _think_, there should be a direct correlation between the parser
stack and the syntax tree, so it _should_ be possible to derive the
structure of the parser stack automatically. I don't think this would
simplify things by a lot, though, therefore I'll stick to defining the data type
manually.

```idris
data STACK : Type where
  Top   : STACK
  If    : STACK -> STACK
  Open  : STACK -> STACK
  Paren : STACK -> Term -> STACK
  Then  : STACK -> Term -> STACK
  Else  : STACK -> Term -> Term -> STACK
  Done  : Term -> STACK

%runElab derive "STACK" [Show,Eq]

0 SK : Type -> Type
SK = Stack Void STACK Lexers
```

Alias `SK q` is used for the _mutable parser state_ running in state thread
`q` (see the #ref1 library) that keeps track of the internal state of
the parser (current byte vector, start and end position of the current
token, a mutable reference holding the parser stack, and other utilities).

=== State Transitions

We define what happens when we recognize a token with one of our
lexers by defining several state transition functions. The most important
of these is `onTerm`, which puts a new `Term` on the parser stack. This
is invoked whenever we encounter a terminal (`true` or `false`) but also
when the end of an `if` expression or an expression in parentheses is
encountered.

Note how this state transition not only updates the parser stack but
also specifies the lexer that is to be used next. In #ilex, it is
common practise to use many different specialized lexers depending
on the current parser state. This way, the parser state is actually
defined by the parser stack plus the lexer we are currently using.


```idris
parameters {auto sk : SK q}

  onTerm : Term -> STACK -> F1 q Lexer
  onTerm t (If p)       = putStackAs (Then p t) THEN
  onTerm t (Then p x)   = putStackAs (Else p x t) ELSE
  onTerm t (Else p x y) = onTerm (TIf x y t) p
  onTerm t (Open p)     = putStackAs (Paren p t) CLOSE
  onTerm t _            = putStackAs (Done t) DONE
```

There is only one more state transition we need to define:
Closing a pair of parentheses. Unfortunately, I could not yet figure out
a convenient (and performant!) way to show at the type level that only
the `Paren {}` case is possible at this stage:

```idris
  onClose : F1 q Lexer
  onClose =
    getStack >>= \case
      Paren p t => onTerm t p
      _         => pure ERR -- not possible
```

=== Lexers

We can now pair regular expressions with the different state transitions,
thus implementing the lexers we so far only defined as numeric constants.
These lexers are grouped in an array with the numeric constants serving
as safe indices into this array:

```idris
ptrans : Lex1 q Lexers SK
ptrans =
  lex1
    [ E TERM $
        spaced
          [ step "true"  $ withStack $ onTerm (bool True)
          , step "false" $ withStack $ onTerm (bool False)
          , step "if"    $ modStackAs SK If TERM
          , opn '('      $ modStackAs SK Open TERM
          ]
    , E THEN  $ spaced [step' "then" TERM]
    , E ELSE  $ spaced [step' "else" TERM]
    , E CLOSE $ spaced [close ")" onClose]
    ]
```

=== Error Handling

For every lexer, we define the exceptions that are being raised in case
we encounter an invalid token. These are functions that have access to
the full mutable parser state, so they can be arbitrarily complex. In
this simple example, we can just specify the strings we would have expected.
In case of an unclosed parenthesis, we opt to highlight it if we reached the
end of input.

```idris
perr : Arr32 Lexers (SK q -> F1 q (BBErr Void))
perr =
  errs
    [ E TERM  $ unexpected ["if", "true", "false", "("]
    , E THEN  $ unexpected ["then"]
    , E ELSE  $ unexpected ["else"]
    , E CLOSE $ unclosedIfEOI ")" [")"]
    ]
```

=== Putting it all together

We wrap things up by defining the "end of input" function and packing
everything into a `P1` record:


```idris
peoi : Lexer -> SK q -> F1 q (Either (BBErr Void) Term)
peoi st sk t =
 let Done x # t := read1 sk.stack_ t | _ # t => arrFail SK perr st sk t
  in Right x # t

public export
term : P1 q (BBErr Void) Term
term = P TERM (init Top) ptrans (\x => (Nothing #)) perr peoi
```

=== Testing the Parser

The following utilities can be used for some quick tests at the REPL.
Rigorous property tests can be found in the library's test suite.

```idris
example : String
example =
  """
  if true
     then (if false then true else false)
     else if false then false else true
  """

typo : String
typo =
  """
  if true
     then (if false thon true else false)
     else if false then false else true
  """

unclosed1 : String
unclosed1 =
  """
  if true
     then (if false then true else false
     else if false then false else true
  """

unclosed2 : String
unclosed2 = "if true then false else (if true then false else false"

export
testTerm : String -> IO ()
testTerm =
  putStrLn . either interpolate interpolate . parseString term Virtual
```

// vi: filetype=idris2:syntax=typst
