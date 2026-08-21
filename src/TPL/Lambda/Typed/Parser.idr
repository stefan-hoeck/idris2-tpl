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

vars : Steps q Lexers SK
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

atoms : Steps q Lexers SK
atoms =
     step '(' (posModStack SK OpnTrm TERM)
  :: step '{' (posModStack SK record' VAR)
  :: step '<' (posModStack SK Sum VAR)
  :: step "unit" (boundsWithStack $ onAtom . unit)
  :: nats  (boundedWithStack $ onAtom . int)
  ++ vars

bindsteps : Steps q Lexers SK
bindsteps = step '_' (withStack placeholder) :: vars

ptrans : Lex1 q Lexers SK
ptrans =
  lex1
    [ spaced TOP $
           step' "%alias" ALIAS_NAME
        :: step "%eval" (modStackAs SK Eval TERM)
        :: vars
    , spaced TOP_SEP [step' '=' TERM, step' ':' TYPE]
    , spaced TERM $
           step lambda (posModStack SK Lam PATTERN)
        :: step "if" (posModStack SK If TERM)
        :: step "let" (posModStack SK Let PATTERN)
        :: step "letrec" (posModStack SK Letrec BINDNAME)
        :: step "case" (posModStack SK Case TERM)
        :: atoms
    , spaced ATOM atoms
    , spaced ATOM_OR_CLOSE $
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
    , spaced EQ [step' '=' TERM]
    , spaced SUM_EQ [step' '=' TERM, step '>' (posWithStack closeSum)]

    , spaced VAR vars
    , spaced BINDNAME bindsteps
    , spaced PATTERN $ step '{' (posModStack SK pat PAT_NEW) :: bindsteps
    , spaced PAT_NEW $ step '}' (withStack closePattern) :: vars
    , spaced PAT_EQ [step' '=' PATTERN]
    , spaced PAT_END [step' ',' VAR, step '}' (withStack closePattern)]

    , spaced ANGLE_OPEN [step' '<' VAR]
    , spaced CASE_EQ [step' '=' PATTERN, step '>' $ withStack noCasePat]
    , spaced ANGLE_CLOSE [step' '>' DBL_ARROW]
    , spaced DBL_ARROW [step' "=>" ATOM]

    , spaced TYPE $
          step "(" (posModStack SK OpnTpe TYPE)
       :: step "{" (posModStack SK recordTpe VAR)
       :: step "<" (posModStack SK sumTpe VAR)
       :: upperName (withStack . typeAtom . pvar)

    , spaced ALIAS_NAME $ upperName (withStack . alias)
    , spaced COLON [step' ':' TYPE]
    , spaced ARROW $
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
    ]

perr : Arr32 Lexers (SK q -> F1 q LamErr)
perr =
  arr32 Lexers (unexpected [])
    [ E DOT $ unexpected ["."]
    , E EQ  $ unexpected ["="]
    ]

peoi : Lexer -> SK q -> F1 q (Either LamErr $ List Declaration)
peoi st sk t =
 let sx # t := read1 sk.stack_ t
  in case sx of
       Top sd => Right (sd <>> []) # t
       _      => arrFail SK perr st sk t

public export
decls : P1 q LamErr (List Declaration)
decls = P TOP (init $ Top [<]) ptrans (\x => (Nothing #)) perr peoi
