module TPL.Lambda.Typed.Parser

import Text.ILex.Debug
import Syntax.T1
import TPL.Lambda.Typed.Parser.State
import TPL.Parser.Util
import public TPL.Lambda.Typed.Declaration

%default total
%hide Data.Linear.(.)

field : ByteString -> VarName
field bs = VN (toString $ drop 1 bs)

vars : Steps q Lexers ST
vars =
     step "if" (failUnexpected [] ERR)
  :: step "then" (failUnexpected [] ERR)
  :: step "else" (failUnexpected [] ERR)
  :: step "let" (failUnexpected [] ERR)
  :: step "letrec" (failUnexpected [] ERR)
  :: step "in" (failUnexpected [] ERR)
  :: step "as" (failUnexpected [] ERR)
  :: step "case" (failUnexpected [] ERR)
  :: step "of" (failUnexpected [] ERR)
  :: varName (withStack . var)

atoms : Steps q Lexers ST
atoms =
     step '(' (posModStack ST OpnTrm TERM)
  :: step '{' (posModStack ST record' VAR)
  :: step '<' (posModStack ST Sum VAR)
  :: step "unit" (boundsWithStack $ onAtom . unit)
  :: nats  (boundedWithStack $ onAtom . int)
  ++ vars

bindsteps : Steps q Lexers ST
bindsteps = step '_' (withStack placeholder) :: vars

%inline
toks : Lexer -> Steps q Lexers ST -> Entry Lexers (DFA q Lexers ST)
toks = spaced

ptrans : Lex1 q Lexers ST
ptrans =
  lex1
    [ toks TOP $
           step' "%alias" ALIAS_NAME
        :: step "%eval" (modStackAs ST Eval TERM)
        :: vars
    , toks TOP_SEP [step' '=' TERM, step' ':' TYPE]
    , toks TERM $
           step lambda (posModStack ST Lam PATTERN)
        :: step "if" (posModStack ST If TERM)
        :: step "let" (posModStack ST Let PATTERN)
        :: step "letrec" (posModStack ST Letrec BINDNAME)
        :: step "case" (posModStack ST Case TERM)
        :: atoms
    , toks ATOM atoms
    , toks ATOM_OR_CLOSE $
           step ';' (withStack termSemicolon)
        :: step ')' (withStack closeTerm)
        :: step '}' (posWithStack closeRecord)
        :: step '>' (posWithStack closeSum)
        :: step ',' (withStack recordComma)
        :: step '|' (withStack endCase)
        :: step "else" (withStack else')
        :: step "then" (withStack then')
        :: step "in" (withStack in')
        :: step "as" (withStack as)
        :: step "of" (withStack of')
        :: bytes proj (\b => bounded' (field b) >>= withStack . projection)
        :: atoms
    , toks EQ [step' '=' TERM]
    , toks SUM_EQ [step' '=' TERM, step '>' (posWithStack closeSum)]

    , toks VAR vars
    , toks BINDNAME bindsteps
    , toks PATTERN $ step '{' (posModStack ST pat PAT_NEW) :: bindsteps
    , toks PAT_NEW $ step '}' (withStack closePattern) :: vars
    , toks PAT_EQ [step' '=' PATTERN]
    , toks PAT_END [step' ',' VAR, step '}' (withStack closePattern)]

    , toks ANGLE_OPEN [step' '<' VAR]
    , toks CASE_EQ [step' '=' PATTERN, step '>' $ withStack noCasePat]
    , toks ANGLE_CLOSE [step' '>' DBL_ARROW]
    , toks DBL_ARROW [step' "=>" ATOM]

    , toks TYPE $
          step "(" (posModStack ST OpnTpe TYPE)
       :: step "{" (posModStack ST recordTpe VAR)
       :: step "<" (posModStack ST sumTpe VAR)
       :: upperName (withStack . typeAtom . pvar)

    , toks ALIAS_NAME $ upperName (withStack . alias)
    , toks COLON [step' ':' TYPE]
    , toks ARROW $
        [ step' "->" TYPE
        , step ')' (withStack closeType)
        , step '}' (posWithStack closeRecordType)
        , step '>' (posWithStack closeSumType)
        , step '.' (withStack dot)
        , step ';' (withStack typeSemicolon)
        , step '=' (withStack typeEq)
        , step ',' (withStack typeComma)
        , step '|' (withStack $ endCase . endAs)
        , step "else" (withStack $ else' . endAs)
        , step "then" (withStack $ then' . endAs)
        , step "in" (withStack $ in' . endAs)
        , step "of" (withStack $ of' . endAs)
        ]
    , E COMMENT block
    ]

perr : Arr32 Lexers (ST q -> F1 q LamErr)
perr =
  arr32 Lexers (unexpected [])
    [ E DOT $ unexpected ["."]
    , E EQ  $ unexpected ["="]
    ]

peoi : Lexer -> ST q -> F1 q (Either LamErr $ List Declaration)
peoi st sk t =
 let sx # t := read1 sk.stack_ t
  in case sx of
       Top sd => Right (sd <>> []) # t
       _      => arrFail ST perr st sk t

public export
decls : P1 q LamErr (List Declaration)
decls = P TOP (init COMMENT $ Top [<]) ptrans (\x => (Nothing #)) perr peoi
