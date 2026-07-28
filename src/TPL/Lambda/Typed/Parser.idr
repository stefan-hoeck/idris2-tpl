module TPL.Lambda.Typed.Parser

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
  :: varName (withStack . var)

atoms : Steps q Lexers SK
atoms =
     step '(' (posModStack SK OpnTrm TERM)
  :: step '{' (posModStack SK record' VAR)
  :: step "unit" (boundsWithStack $ onAtom . unit)
  :: bools (boundedWithStack $ onAtom . bool)
  ++ nats  (boundedWithStack $ onAtom . int)
  ++ vars

bindsteps : Steps q Lexers SK
bindsteps = step '_' (withStack placeholder) :: vars

ptrans : Lex1 q Lexers SK
ptrans =
  lex1
    [ E TOP $ spaced $
           step' "%alias" ALIAS_NAME
        :: step "%eval" (modStackAs SK Eval TERM)
        :: vars
    , E TOP_SEP $ spaced $ [step' '=' TERM, step' ':' TYPE]
    , E TERM $ spaced $
           step lambda (posModStack SK Lam PATTERN)
        :: step "if" (posModStack SK If TERM)
        :: step "let" (posModStack SK Let PATTERN)
        :: step "letrec" (posModStack SK Letrec BINDNAME)
        :: atoms
    , E ATOM $ spaced atoms
    , E ATOM_OR_CLOSE $ spaced $
           step ';' (withStack termSemicolon)
        :: step ')' (withStack closeTerm)
        :: step '}' (posWithStack closeRecord)
        :: step ',' (withStack recordComma)
        :: step "else" (withStack else')
        :: step "then" (withStack then')
        :: step "in" (withStack in')
        :: bytes proj (\b => bounded' (field b) >>= withStack . projection)
        :: atoms
    , E EQ $ spaced [step' '=' TERM]

    , E VAR $ spaced vars
    , E BINDNAME $ spaced bindsteps
    , E PATTERN $ spaced $ step '{' (posModStack SK pat PAT_NEW) :: bindsteps
    , E PAT_NEW $ spaced $ step '}' (withStack closePattern) :: vars
    , E PAT_EQ $ spaced [step' '=' PATTERN]
    , E PAT_END $ spaced [step' ',' VAR, step '}' (withStack closePattern)]

    , E TYPE $ spaced $
          step "(" (posModStack SK OpnTpe TYPE)
       :: step "{" (posModStack SK recordTpe VAR)
       :: upperName (withStack . typeAtom . pvar)

    , E ALIAS_NAME $ spaced $ upperName (withStack . alias)
    , E COLON $ spaced [step' ':' TYPE]
    , E ARROW $ spaced $
        [ step' "->" TYPE
        , step ')' (withStack closeType)
        , step '}' (posWithStack closeRecordType)
        , step '.' (withStack dot)
        , step ';' (withStack typeSemicolon)
        , step '=' (withStack typeEq)
        , step ',' (withStack typeComma)
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
