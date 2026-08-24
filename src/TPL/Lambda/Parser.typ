#import "template.typ": *

== Parsing Lambda Declarations

For untyped lambda terms, we are for the first time going
to implement a parser that not only reads single expressions
but lists of top-level declarations. This will allow us
to group several definitions in a source file, include
definitions from other source files, and run evaluation
statements.

As usual, we begin with the different types of lexers we
are going to need:

```idris
module TPL.Lambda.Parser

import Derive.Prelude
import Syntax.T1
import Text.ILex.Derive
import TPL.Parser.Util
import public TPL.Lambda.Term

%default total
%hide Data.Linear.(.)
%language ElabReflection

%runElab deriveParserState "Lexers" "Lexer"
  ["TOP","EQ","TERM","ATOM","ATOM_OR_CLOSE","VAR","DOT","COMMENT","ERR"]
```

The parser stack again represents the different stages of
reading a top-level declaration from left to right.

```idris
data STACK : Type where
  Top   : STACK
  Def   : ByteBounded VarName -> STACK
  Eval  : STACK
  App   : STACK -> Term -> SnocList Term -> STACK
  Term  : STACK -> Term -> STACK
  Lam   : STACK -> BytePos -> STACK
  LamV  : STACK -> BytePos -> VarName -> STACK
  Open  : STACK -> STACK
  If    : STACK -> BytePos -> STACK
  Then  : STACK -> BytePos -> Term -> STACK
  Else  : STACK -> BytePos -> Term -> Term -> STACK
  Err   : STACK

public export
0 SK : Type -> Type
SK = TPLState TpeErr STACK Declaration Lexers
```

There are two constructors of special note: `App` describes
a non-empty sequence of applied terms. Only atomic terms can
appear in such a sequence: Any non-atomic token such as - for example - the
keywords in an `if` expression, a lambda abstraction, or
a semicolon end the current application sequence.

The second is `Term`, which will only ever be an intermediate
reduction step (see `endTerm` below).

=== State Transisions

First, since sequences of function application are open and can
end at one of several special tokens, we require two utility
functions that end the current function application and therefore
the current larger term.

For instance, in `(λx. λy. fls x y) 1 2`, when we arrive at the
closing paren, we end the application sequence (`fls y z`),
followed by inner lambda, followed by the outer lambda. This is
handled in function `endTerm`, which is always invoked from
`endApp`:

```idris
endTerm : Term -> STACK -> STACK
endTerm t (LamV p s v)   = endTerm (TLam (fromPos s t) v t) p
endTerm t (Else p s x y) = endTerm (TIf (fromPos s t) x y t) p
endTerm t s              = Term s t

endApp : STACK -> STACK
endApp (App s t st) = endTerm (appAllSnoc t st) s
endApp s            = Err
```

After encountering an atomic term (a literal or a term in
parentheses), we append it to the current application sequence,
or start a new such sequence if there is none at the top of
the stack. In either case, we expect additional atoms or a
token that can end an application sequence.

```idris
parameters {auto sk : SK q}

  onAtom : Term -> STACK -> F1 q Lexer
  onAtom t (App p x sx) = putStackAs (App p x (sx:<t)) ATOM_OR_CLOSE
  onAtom t p            = putStackAs (App p t [<]) ATOM_OR_CLOSE
```

When we encounter a variable name that is not also a keyword, we
invoke utility `var`, which either starts a new top-level definition
or treats the variable as an atom.

```idris
  var : ByteBounded VarName -> STACK -> F1 q Lexer
  var v (Lam p b) = putStackAs (LamV p b v.val) DOT
  var v Top       = putStackAs (Def v) EQ
  var v s         = onAtom (TVar v.bounds v.val) s
```

There are four tokens that end an application sequence: A
semicolon (`;`) ends any top-level definition, keywords
`then` and `else` end the sub-terms of an `if` expression,
and a closing parenthesis (`)`) obviously ends an atomic expression.

In all these cases, we finalize the current term and verify
that the parent stack is of the correct shape to continue:

```idris
  semicolon : STACK -> F1 q Lexer
  semicolon s =
    case endApp s of
      Term (Def n) t => pushDecl (Defn n.bounds n.val t) Top TOP
      Term Eval    t => pushDecl (Eval t) Top TOP
      _              => failUnexpected [] ERR

  then' : STACK -> F1 q Lexer
  then' s =
    case endApp s of
      Term (If s b) t => putStackAs (Then s b t) TERM
      _               => failUnexpected [] ERR

  else' : STACK -> F1 q Lexer
  else' s =
    case endApp s of
      Term (Then s b x) t => putStackAs (Else s b x t) TERM
      _                   => failUnexpected [] ERR

  closeTerm : STACK -> F1 q Lexer
  closeTerm s =
    case endApp s of
      Term (Open s) t => onAtom t s
      _               => failUnexpected [] ERR
```

=== Lexers

Lexing variables is done by using the `var` regular expression. However,
we have to make sure we did not encounter one of the reserved keywords,
all of which will immediately raise an exception.

```idris
vars : Steps q Lexers SK
vars =
     step "if" (failUnexpected [] ERR)
  :: step "then" (failUnexpected [] ERR)
  :: step "else" (failUnexpected [] ERR)
  :: varName (withStack . var)
```

An atom is a literal or an expression in parentheses:

```idris
atoms : Steps q Lexers SK
atoms =
     opn '(' (modStackAs SK Open TERM)
  :: bools (boundedWithStack $ onAtom . bool)
  ++ nats  (boundedWithStack $ onAtom . int)
  ++ vars
```

All the other lexers are unique and are grouped directly in the array of
available lexers. Note how keywords override the default behavior
of raising an error in some of these lexers:

```idris
%inline
toks : Lexer -> Steps q Lexers SK -> Entry Lexers (DFA q Lexers SK)
toks = spaced

ptrans : Lex1 q Lexers SK
ptrans =
  lex1
    [ toks TOP $ step "#eval" (putStackAs Eval TERM) :: vars
    , toks TERM $
           step lambda (posModStack SK Lam VAR)
        :: step "if" (posModStack SK If TERM)
        :: atoms
    , toks ATOM atoms
    , toks ATOM_OR_CLOSE $
           step ';' (withStack semicolon)
        :: step ')' (withStack closeTerm)
        :: step "else" (withStack else')
        :: step "then" (withStack then')
        :: atoms
    , toks VAR  vars
    , toks DOT  [step' '.' TERM]
    , toks EQ   [step' '=' TERM]
    , E COMMENT block
    ]
```

=== Lexers

```idris
perr : Arr32 Lexers (SK q -> F1 q LamErr)
perr =
  arr32 Lexers (unexpected [])
    [ E DOT $ unexpected ["."]
    , E EQ $ unexpected ["="]
    ]

peoi : Lexer -> SK q -> F1 q (Either LamErr $ List Declaration)
peoi st sk t =
 let Top # t := read1 sk.stack_ t | _ # t => arrFail SK perr st sk t
  in decls sk t

export
decls : P1 q LamErr (List Declaration)
decls = P TERM (init COMMENT Top) ptrans declChunk perr peoi
```

// vi: filetype=idris2:syntax=typst
