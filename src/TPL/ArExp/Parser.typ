#import "template.typ": *

== Parsing Airthmetic Terms

We use the same approach for parsing arithmetic terms as for
boolean terms (@bool_parse): A couple of dedicated lexers, a properly typed
parser stack, plus the necessary state transitions.

=== Syntax

The syntax is similar to the one for boolean expressions, but there are
some additional production rules for natural numbers and primitive
functions. The rules for whitespace and comments are not repeated below:

```abnf
WS_TERM   = WS TERM WS

TERM      = ATOM
          / FUN WS_TERM ATOM
          / "if" WS_TERM "then" WS_TERM "else" WS_TERM

FUN       = "succ" / "pred" / "iszero"

ATOM      = VALUE
          / '(' WS_TERM ')'

VALUE     = "true" / "false" / NAT

NAT       = "0"
          / %x31-%x39 1*DIGIT
          / "0x" 1*HEXIT
          / "0o" 1*OCTIT
          / "0b" 1*BIT

DIGIT     = %x30-%x39
OCTIT     = %x30-%x37
BIT       = %x30-%x31
HEXIT     =
```

=== Types of Lexers

Unlike with mere boolean terms, we already have some limited forms of
function application in arithmetic terms, namemly passing arguments
to primitive functions like `succ`, `pred`, or `iszero`. In general,
the argument of a function must be a distinguishable unit: An expression
like `succ succ 0` could be interpreted as the well-formed `succ (succ 0)`
but also the nonsensical `(succ succ) 0`. We might be able (I haven't
verified this) to get away without parentheses in this primitive language,
but in later examples we are going to have arbitrary numbers of function
arguments. Then, proper grouping of a composite argument by wrapping it
in parentheses will be mandatory. We call such a grouping an _atom_,
and it comes with its own restricted lexer.

```idris
module TPL.ArExp.Parser

import Derive.Prelude
import Text.ILex.Derive
import Syntax.T1
import public TPL.ArExp.TT
import public TPL.ArExp.Term
import public TPL.Parser.Util

%default total
%hide Data.Linear.(.)
%language ElabReflection

%runElab deriveParserState "Lexers" "Lexer"
  ["TERM","ATOM","THEN","ELSE","CLOSE","DONE","ERR"]
```

=== Parser Stack

There is only one additional stack item for representing primitive function calls,
the rest is identical to the stack type for boolean expressions:

```idris
data STACK : Type where
  Top   : STACK
  If    : STACK -> ByteBounds -> STACK
  Fun   : STACK -> (Term -> Term) -> STACK
  Open  : STACK -> STACK
  Paren : STACK -> Term -> STACK
  Then  : STACK -> ByteBounds -> Term -> STACK
  Else  : STACK -> ByteBounds -> Term -> Term -> STACK
  Done  : Term -> STACK

0 SK : Type -> Type
SK = Stack (TplErr Tpe) STACK Lexers
```

=== State Transitions

In addition to the already familiar state transitions for
completing terms and closing parentheses, there are two additional
utilities: one for starting an `if` expression, the other for
introducing a primitive function call. Note how we request
an `ATOM` lexer after encountering a primitive function.

```idris
parameters {auto sk : SK q}

  onTerm : Term -> STACK -> F1 q Lexer
  onTerm x (If p b)       = putStackAs (Then p b x) THEN
  onTerm x (Fun p f)      = onTerm (f x) p
  onTerm x (Open p)       = putStackAs (Paren p x) CLOSE
  onTerm x (Then p b y)   = putStackAs (Else p b y x) ELSE
  onTerm x (Else p b y z) = onTerm (TIf (b <+> cast x) y z x) p
  onTerm x _              = putStackAs (Done x) DONE

  onClose : F1 q Lexer
  onClose =
    getStack >>= \case
      Paren p t => onTerm t p
      _         => pure ERR -- not possible

  onFun : (ByteBounds -> Term -> Term) -> F1 q Lexer
  onFun f = bounds >>= \b => modStackAs SK (`Fun` f b) ATOM

  onIf : F1 q Lexer
  onIf = bounds >>= \b => modStackAs SK (`If` b) TERM
```

=== Lexers

The lexers are also similar to the ones for boolean terms but
we now need to keep track of the byte bounds of the tokens we
encountered. Note also that the keywords of our simple grammar
are not case sensitive in accordance with the syntax rules given
above. The book might be more strict here, but I just couldn't
care.

```idris
atomSteps : Steps q Lexers SK
atomSteps =
     opn '(' (modStackAs SK Open TERM)
  :: bools (boundedWithStack $ onTerm . bool)
  ++ nats  (boundedWithStack $ onTerm . int)


ptrans : Lex1 q Lexers SK
ptrans =
  lex1
    [ E TERM $ spaced $
        [ step (like "if")     onIf
        , step (like "succ")   (onFun TSucc)
        , step (like "pred")   (onFun TPred)
        , step (like "iszero") (onFun TIsZ)
        ] ++ atomSteps
    , E ATOM $ spaced atomSteps
    , E THEN  $ spaced [step' (like "then") TERM]
    , E ELSE  $ spaced [step' (like "else") TERM]
    , E CLOSE $ spaced [close ")" onClose]
    ]
```

=== Putting it all together

After adding some utilities for error handling as well as dealing with
the end of input, we can assemble our parser for arithmetic terms.

As with boolean terms it is straight forward to write round-tripping tests
for the parser. See the project's test module.

```idris
atms : List String
atms = ["true", "false", "0", "("]

values : List String
values = ["if", "succ", "pred", "iszero"] ++ atms

perr : Arr32 Lexers (SK q -> F1 q ArErr)
perr =
  errs
    [ E TERM  $ unexpected values
    , E ATOM  $ unexpected atms
    , E THEN  $ unexpected ["then"]
    , E ELSE  $ unexpected ["else"]
    , E CLOSE $ unclosedIfEOI ")" [")"]
    ]

peoi : Lexer -> SK q -> F1 q (Either ArErr Term)
peoi st sk t =
 let Done x # t := getStack t | _ # t => arrFail SK perr st sk t
  in Right x # t

public export
term : P1 q ArErr Term
term = P TERM (init Top) ptrans (\x => (Nothing #)) perr peoi
```

// vi: filetype=idris2:syntax=typst
