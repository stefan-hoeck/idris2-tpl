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
           step "%alias" (modStackAs SK Alias TYPE_NAME)
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
        -- :: bytes proj (\b => bounded' (field b) >>= dtrans . projection)
        :: atoms

    , E VAR $ spaced vars
    , E BINDNAME $ spaced bindsteps
    , E PATTERN $ spaced $ step '{' (posModStack SK pat VAR) :: bindsteps

    , E TYPE $ spaced $
          step "(" (posModStack SK OpnTpe TYPE)
       :: step "{" (posModStack SK recordTpe VAR)
       :: upperName (withStack . typeAtom . pvar)
    ]

-- afterType : DFA q Lexers SK
-- afterType =
--   spaced
--     [ step ')' (dtrans closeType)
--     , step '}' (bounds >>= dtrans . closeRecordType)
--     , step '.' (dtrans dot)
--     , step ',' (dtrans recordTypeComma)
--     , step ';' (dtrans typeSemicolon)
--     , step '=' (dtrans eq)
--     , step "->" (dtrans arrow)
--     ]
--
-- ptrans : Lex1 q Lexers SK
-- ptrans =
--   lex1
--     [ entry TOP               top
--
--     , entry TOP_FUNNAME       $ spaced [step '=' (dtrans eq), step ':' (dtrans colon)]
--     , entry DECL_COLON        typeAtoms
--     , entry DEFN_EQ           terms
--
--     , entry EVAL              terms
--
--     , entry ALIAS             $ spaced $ upperName (dtrans . typename)
--     , entry ALIAS_TYPENAME    $ spaced [step ':' (dtrans colon)]
--     , entry ALIAS_COLON       typeAtoms
--
--     , entry LAMBDA            startPattern
--     , entry LAMBDA_PAT        $ spaced [step ':' (dtrans colon)]
--     , entry LAMBDA_COLON      typeAtoms
--     , entry LAMBDA_DOT        terms
--
--     , entry LET               startPattern
--     , entry LET_PAT           $ spaced [step '=' (dtrans eq)]
--     , entry LET_EQ            terms
--     , entry LET_IN            terms
--     , entry LETREC            bindvars
--     , entry LETREC_VAR        $ spaced [step ':' (dtrans colon)]
--     , entry LETREC_COLON      typeAtoms
--     , entry LETREC_EQ         terms
--     , entry LETREC_IN         terms
--
--     , entry PATTERN           $ spaced $ step '}' (dtrans closePattern) :: vars
--     , entry PATTERN_FIELD     $ spaced [step '=' (dtrans eq)]
--     , entry PATTERN_EQ        startPattern
--     , entry PATTERN_PAT       $ spaced [step '}' (dtrans closePattern), step ',' (dtrans patternComma)]
--     , entry PATTERN_COMMA     $ spaced vars
--
--     , entry APP               atomOrClose
--     , entry TERM_OPEN         terms
--     , entry SEQ               terms
--
--     , entry IF                terms
--     , entry THEN              terms
--     , entry ELSE              terms
--
--     , entry RECORD            $ spaced vars
--     , entry RECORD_FIELD      $ spaced [step '=' (dtrans eq)]
--     , entry RECORD_COMMA      $ spaced vars
--     , entry RECORD_EQ         terms
--
--     , entry TYPE_SEQ          afterType
--     , entry TYPE_ARROW        typeAtoms
--     , entry TYPE_OPEN         typeAtoms
--     , entry RECORD_TYPE       $ spaced vars
--     , entry RECORD_TYPE_FIELD $ spaced [step ':' (dtrans colon)]
--     , entry RECORD_TYPE_COMMA $ spaced vars
--     , entry RECORD_TYPE_COLON typeAtoms
--     ]
--
-- peoi : Index Lexers -> SK q -> F1 q (Either LamErr $ List Declaration)
-- peoi st sk t =
--  let sx # t := read1 sk.stack_ t
--   in case sx of
--        [<sd]:>TOP => Right (sd <>> []) # t
--        _          => arrFail SK perr st sk t
--
-- public export
-- decls : P1 q LamErr (List Declaration)
-- decls = P (cast TOP) (init $ [<[<]]:>TOP) ptrans (\x => (Nothing #)) perr peoi
