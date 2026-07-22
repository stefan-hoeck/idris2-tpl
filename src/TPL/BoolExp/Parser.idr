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

--------------------------------------------------------------------------------
-- Parser Stack
--------------------------------------------------------------------------------

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

parameters {auto sk : SK q}

  onTerm : Term -> STACK -> F1 q Lexer
  onTerm t (If p)       = putStackAs (Then p t) THEN
  onTerm t (Then p x)   = putStackAs (Else p x t) ELSE
  onTerm t (Else p x y) = onTerm (TIf x y t) p
  onTerm t (Open p)     = putStackAs (Paren p t) CLOSE
  onTerm t _            = putStackAs (Done t) DONE

  onClose : F1 q Lexer
  onClose =
    getStack >>= \case
      Paren p t => onTerm t p
      _         => pure ERR -- not possible

ptrans : Lex1 q Lexers SK
ptrans =
  lex1
    [ E TERM $
        spaced
          [ step "true"  $ getStack >>= onTerm (bool True)
          , step "false" $ getStack >>= onTerm (bool False)
          , step "if"    $ getStack >>= \p => putStackAs (If p) TERM
          , opn '('      $ getStack >>= \p => putStackAs (Open p) TERM
          ]
    , E THEN  $ spaced [step' "then" TERM]
    , E ELSE  $ spaced [step' "else" TERM]
    , E CLOSE $ spaced [close ")" onClose]
    ]

perr : Arr32 Lexers (SK q -> F1 q (BBErr Void))
perr =
  errs
    [ E TERM  $ unexpected ["if", "true", "false", "("]
    , E THEN  $ unexpected ["then"]
    , E ELSE  $ unexpected ["else"]
    , E CLOSE $ unclosedIfEOI ")" [")"]
    ]

peoi : Lexer -> SK q -> F1 q (Either (BBErr Void) Term)
peoi st sk t =
 let Done x # t := read1 sk.stack_ t | _ # t => arrFail SK perr st sk t
  in Right x # t

public export
term : P1 q (BBErr Void) Term
term = P TERM (init Top) ptrans (\x => (Nothing #)) perr peoi

example : String
example =
  """
  if true
     then (if false then true else false)
     else if false then false else true
  """

export
testTerm : String -> IO ()
testTerm =
  putStrLn . either interpolate interpolate . parseString term Virtual
