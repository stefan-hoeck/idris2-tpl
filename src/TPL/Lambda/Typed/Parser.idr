module TPL.Lambda.Typed.Parser

import Syntax.T1
import TPL.Lambda.Typed.Parser.State
import TPL.Parser.Util
import public TPL.Lambda.Typed.Declaration

%default total
%hide Data.Linear.(.)

--------------------------------------------------------------------------------
-- Parser Stack
--------------------------------------------------------------------------------

PSz : Bits32
PSz = 1 + cast (conIndexSTATE ERR)

inBoundsSTATE : (s : STATE ts) -> (cast (conIndexSTATE s) < PSz) === True

export %inline
Cast (STATE ts) (Index PSz) where
  cast v = I (cast $ conIndexSTATE v) @{mkLT $ inBoundsSTATE v}

public export
0 SK : Type -> Type
SK = DStack STATE TpeErr

lamErr : List String -> SK q -> F1 q LamErr
lamErr ss sk = T1.do
  st <- getStack
  case openBounds st of
    Just (BB p _) => push1 (positions sk) p >> unclosedIfEOI "(" ss sk
    _             => unexpected ss sk

perr : Arr32 PSz (SK q -> F1 q LamErr)
perr = arr32 PSz (lamErr []) []

onerr : STATE st -> SK q => F1 q (Index PSz)
onerr st @{sk} = T1.do
 let eo      := at perr (cast st)
 err <- eo sk
 failWith err (cast ERR)

%inline
dtrans : SK q => StateTrans STATE -> F1 q (Index PSz)
dtrans f t =
 let (sx:>st) # t := getStack t
  in case f st sx of
       _:>ERR     => onerr st t
       sx@(_:>st) => putStackAs sx (cast st) t

vars : Steps q PSz SK
vars =
     step "if" (bounds >>= dtrans . if')
  :: step "then" (dtrans then')
  :: step "else" (dtrans else')
  :: varName (dtrans . var)

atoms : Steps q PSz SK
atoms =
     step '(' (bounds >>= dtrans . openTerm)
  :: step '<' (bounds >>= dtrans . openRecord)
  :: step "unit" (bounds >>= dtrans . atom . unit)
  :: bools (\b => bounded' b >>= dtrans . atom . bool)
  ++ nats  (\b => bounded' b >>= dtrans . atom . int)
  ++ vars

terms : DFA q PSz SK
terms = spaced $ step ('\\' <|> 'λ') (bounds >>= dtrans . lambda) :: atoms

atomOrClose : DFA q PSz SK
atomOrClose =
  spaced $
       step ';' (dtrans termSemicolon)
    :: step ')' (dtrans closeTerm)
    :: step '>' (bounds >>= dtrans . closeRecord)
    :: step ',' (dtrans recordComma)
    :: atoms

typeAtoms : DFA q PSz SK
typeAtoms =
  spaced $
       step "(" (bounds >>= dtrans . openType)
    :: step "<" (bounds >>= dtrans . openRecordType)
    :: upperName (dtrans . typeAtom . pvar)

afterType : DFA q PSz SK
afterType =
  spaced
    [ step ')' (dtrans closeType)
    , step '>' (bounds >>= dtrans . closeRecordType)
    , step '.' (dtrans dot)
    , step ',' (dtrans recordTypeComma)
    , step ';' (dtrans typeSemicolon)
    , step "->" (dtrans arrow)
    ]

top : DFA q PSz SK
top =
  spaced $
       step "%alias" (dtrans alias)
    :: step "%eval" (dtrans eval)
    :: vars


ptrans : Lex1 q PSz SK
ptrans =
  lex1
    [ entry TOP               top

    , entry TOP_FUNNAME       $ spaced [step '=' (dtrans eq), step ':' (dtrans colon)]
    , entry DECL_COLON        typeAtoms
    , entry DEFN_EQ           terms

    , entry EVAL              terms

    , entry ALIAS             $ spaced $ upperName (dtrans . typename)
    , entry ALIAS_TYPENAME    $ spaced [step ':' (dtrans colon)]
    , entry ALIAS_COLON       typeAtoms

    , entry LAMBDA            $ spaced (step '_' (dtrans placeholder) :: vars)
    , entry LAMBDA_VAR        $ spaced [step ':' (dtrans colon)]
    , entry LAMBDA_COLON      typeAtoms
    , entry LAMBDA_DOT        terms

    , entry TERM              atomOrClose
    , entry TERM_OPEN         terms
    , entry SEQ               terms

    , entry IF                terms
    , entry THEN              terms
    , entry ELSE              terms

    , entry RECORD            $ spaced vars
    , entry RECORD_FIELD      $ spaced [step '=' (dtrans eq)]
    , entry RECORD_COMMA      $ spaced vars
    , entry RECORD_EQ         terms

    , entry TYPE_SEQ          afterType
    , entry TYPE_ARROW        typeAtoms
    , entry TYPE_OPEN         typeAtoms
    , entry RECORD_TYPE       $ spaced vars
    , entry RECORD_TYPE_FIELD $ spaced [step ':' (dtrans colon)]
    , entry RECORD_TYPE_COMMA $ spaced vars
    , entry RECORD_TYPE_COLON typeAtoms
    ]

peoi : Index PSz -> SK q -> F1 q (Either LamErr $ List Declaration)
peoi st sk t =
 let sx # t := read1 sk.stack_ t
  in case sx of
       [<sd]:>TOP => Right (sd <>> []) # t
       _          => arrFail SK perr st sk t

public export
decls : P1 q LamErr (List Declaration)
decls = P (cast TOP) (init $ [<[<]]:>TOP) ptrans (\x => (Nothing #)) perr peoi

--------------------------------------------------------------------------------
-- Proofs
--------------------------------------------------------------------------------

inBoundsSTATE TOP               = Refl
inBoundsSTATE TOP_FUNNAME       = Refl
inBoundsSTATE DECL_COLON        = Refl
inBoundsSTATE DEFN_EQ           = Refl
inBoundsSTATE EVAL              = Refl
inBoundsSTATE ALIAS             = Refl
inBoundsSTATE ALIAS_TYPENAME    = Refl
inBoundsSTATE ALIAS_COLON       = Refl
inBoundsSTATE LAMBDA            = Refl
inBoundsSTATE LAMBDA_VAR        = Refl
inBoundsSTATE LAMBDA_COLON      = Refl
inBoundsSTATE LAMBDA_DOT        = Refl
inBoundsSTATE TERM              = Refl
inBoundsSTATE TERM_OPEN         = Refl
inBoundsSTATE SEQ               = Refl
inBoundsSTATE IF                = Refl
inBoundsSTATE THEN              = Refl
inBoundsSTATE ELSE              = Refl
inBoundsSTATE RECORD            = Refl
inBoundsSTATE RECORD_FIELD      = Refl
inBoundsSTATE RECORD_EQ         = Refl
inBoundsSTATE RECORD_COMMA      = Refl
inBoundsSTATE TYPE              = Refl
inBoundsSTATE TYPE_SEQ          = Refl
inBoundsSTATE TYPE_ARROW        = Refl
inBoundsSTATE TYPE_OPEN         = Refl
inBoundsSTATE RECORD_TYPE       = Refl
inBoundsSTATE RECORD_TYPE_FIELD = Refl
inBoundsSTATE RECORD_TYPE_COLON = Refl
inBoundsSTATE RECORD_TYPE_COMMA = Refl
inBoundsSTATE ERR               = Refl
