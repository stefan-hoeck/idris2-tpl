module TPL.Lambda.Typed.Parser.State

import Derive.Prelude
import Text.ILex.DStack
import public Data.SnocList.Quantifiers
import public TPL.Lambda.Typed.Declaration

%default total
%language ElabReflection

public export
0 RecField : Type
RecField = (VarName,PTerm)

public export
0 RecTypeField : Type
RecTypeField = (VarName,RawTpe)

public export
data STATE : SnocList Type -> Type where
  TOP                 : STATE [<SnocList Declaration]

  TOP_FUNNAME         : STATE [<SnocList Declaration,ByteBounded VarName]
  DECL_COLON          : STATE [<SnocList Declaration,ByteBounded VarName]
  DEFN_EQ             : STATE [<SnocList Declaration,ByteBounded VarName]

  EVAL                : STATE [<SnocList Declaration]

  ALIAS               : STATE [<SnocList Declaration]
  ALIAS_TYPENAME      : STATE [<SnocList Declaration,ByteBounded VarName]
  ALIAS_COLON         : STATE [<SnocList Declaration,ByteBounded VarName]

  LAMBDA              : STATE [<ByteBounds]
  LAMBDA_VAR          : STATE [<ByteBounds,BindName]
  LAMBDA_COLON        : STATE [<ByteBounds,BindName]
  LAMBDA_DOT          : STATE [<ByteBounds,BindName,RawTpe]

  LET                 : STATE [<ByteBounds]
  LET_PATTERN         : STATE [<ByteBounds,Pattern]
  LET_EQ              : STATE [<ByteBounds,Pattern]
  LET_IN              : STATE [<ByteBounds,Pattern,PTerm]

  LETREC              : STATE [<ByteBounds]
  LETREC_VAR          : STATE [<ByteBounds,BindName]
  LETREC_COLON        : STATE [<ByteBounds,BindName]
  LETREC_EQ           : STATE [<ByteBounds,BindName,RawTpe]
  LETREC_IN           : STATE [<ByteBounds,BindName,RawTpe,PTerm]

  PATTERN             : STATE [<ByteBounds,SnocList PatField]
  PATTERN_FIELD       : STATE [<ByteBounds,SnocList PatField,ByteBounded VarName]
  PATTERN_EQ          : STATE [<ByteBounds,SnocList PatField,ByteBounded VarName]
  PATTERN_PAT         : STATE [<ByteBounds,SnocList PatField]
  PATTERN_COMMA       : STATE [<ByteBounds,SnocList PatField]

  TERM                : STATE [<PTerm]
  APP                 : STATE [<PTerm,SnocList PTerm]
  TERM_OPEN           : STATE [<ByteBounds]
  SEQ                 : STATE [<ByteBounds,PTerm]

  RECORD              : STATE [<ByteBounds,SnocList RecField]
  RECORD_FIELD        : STATE [<ByteBounds,SnocList RecField,VarName]
  RECORD_EQ           : STATE [<ByteBounds,SnocList RecField,VarName]
  RECORD_COMMA        : STATE [<ByteBounds,SnocList RecField]

  IF                  : STATE [<ByteBounds]
  THEN                : STATE [<ByteBounds,PTerm]
  ELSE                : STATE [<ByteBounds,PTerm,PTerm]

  TYPE                : STATE [<RawTpe]
  TYPE_SEQ            : STATE [<SnocList RawTpe, RawTpe]
  TYPE_ARROW          : STATE [<SnocList RawTpe, RawTpe]
  TYPE_OPEN           : STATE [<ByteBounds]
  RECORD_TYPE         : STATE [<ByteBounds,SnocList RecTypeField]
  RECORD_TYPE_FIELD   : STATE [<ByteBounds,SnocList RecTypeField,VarName]
  RECORD_TYPE_COLON   : STATE [<ByteBounds,SnocList RecTypeField,VarName]
  RECORD_TYPE_COMMA   : STATE [<ByteBounds,SnocList RecTypeField]

  ERR                 : STATE [<]

%runElab deriveIndexed "STATE" [Show,ConIndex]

public export
0 StateTrans : (s : SnocList Type -> Type) -> Type
StateTrans s =
     {0 ss : _}
  -> {0 b  : _}
  -> (st : s ss)
  -> (sx : Stack b s ss)
  -> Stack True s [<]

--------------------------------------------------------------------------------
-- State Transitions
--------------------------------------------------------------------------------

err : StateTrans STATE
err st sx = sx:>st:>ERR

term : PTerm -> StateTrans STATE
term x LAMBDA_DOT (sx:>st:<b:<v:<bt)   = term (PLam b v bt x) st sx
term x APP        (sx:>st:<y:<ys)      = term (appSnoc y (ys:<x)) st sx
term x ELSE       (sx:>st:<b:<i:<t)    = term (tif b i t x) st sx
term x LET_IN     (sx:>st:<b:<p:<s)    = term (PLet (b <+> cast x) p s x) st sx
term x LETREC_IN  (sx:>st:<b:<v:<t:<s) = term (PLetrec (b <+> cast x) v t s x) st sx
term x st         sx                   = sx:>st:<x:>TERM

endTerm : StateTrans STATE
endTerm APP (sx:>st:<x:<sy) = term (appSnoc x sy) st sx
endTerm st   sx              = err st sx

endType : StateTrans STATE
endType TYPE_SEQ (sx:<ss:<s) = sx:<tpeAppAll ss s:>TYPE
endType st   sx              = err st sx

export
funname : ByteBounded VarName -> StateTrans STATE
funname x TOP sx = sx:<x:>TOP_FUNNAME
funname x st  sx = err st sx

export
eval : StateTrans STATE
eval TOP sx = sx:>EVAL
eval st  sx = err st sx

export
alias : StateTrans STATE
alias TOP sx = sx:>ALIAS
alias st  sx = err st sx

export
typename : ByteBounded VarName -> StateTrans STATE
typename v ALIAS sx = sx:<v:>ALIAS_TYPENAME
typename _ st    sx = err st sx

export
colon : StateTrans STATE
colon LAMBDA_VAR        sx = sx:>LAMBDA_COLON
colon TOP_FUNNAME       sx = sx:>DECL_COLON
colon ALIAS_TYPENAME    sx = sx:>ALIAS_COLON
colon RECORD_TYPE_FIELD sx = sx:>RECORD_TYPE_COLON
colon LETREC_VAR        sx = sx:>LETREC_COLON
colon st                sx = err st sx

export
eq : StateTrans STATE
eq TOP_FUNNAME   sx = sx:>DEFN_EQ
eq RECORD_FIELD  sx = sx:>RECORD_EQ
eq LET_PATTERN   sx = sx:>LET_EQ
eq PATTERN_FIELD sx = sx:>PATTERN_EQ
eq st            sx =
  case endType st sx of
    sx:>LETREC_COLON:<t:>TYPE => sx:<t:>LETREC_EQ
    _ => err st sx

export
lambda : ByteBounds -> StateTrans STATE
lambda b st sx = sx:>st:<b:>LAMBDA

export
dot : StateTrans STATE
dot TYPE_SEQ (sx:>LAMBDA_COLON:<ss:<s) = sx:<(tpeAppAll ss s):>LAMBDA_DOT
dot st       sx                        = err st sx

export
atom : PTerm -> StateTrans STATE
atom x APP (sx:<y) = sx:<(y:<x):>APP
atom x st  sx      = sx:>st:<x:<[<]:>APP

export
typeAtom : RawTpe -> StateTrans STATE
typeAtom t TYPE_ARROW (sx:<ss:<s) = sx:<(ss:<s):<t:>TYPE_SEQ
typeAtom t st         sx          = sx:>st:<[<]:<t:>TYPE_SEQ

export
termSemicolon : StateTrans STATE
termSemicolon st sx =
  case endTerm st sx of
    sy:>TERM_OPEN:<t:>TERM       => sy:<t:>SEQ
    sy:<s:>SEQ:<t:>TERM          => sy:<seq s t:>SEQ
    sy:<sd:>EVAL:<t:>TERM        => sy:<(sd:<Eval t):>TOP
    sy:<sd:<vn:>DEFN_EQ:<t:>TERM => sy:<(sd:<Defn vn.bounds vn.val t):>TOP
    _                            => err st sx

export
typeSemicolon : StateTrans STATE
typeSemicolon st sx =
  case endType st sx of
    sx:<sd:<b:>ALIAS_COLON:<t:>TYPE => sx:<(sd:<Alias b.bounds b.val t):>TOP
    sx:<sd:<b:>DECL_COLON:<t:>TYPE  => sx:<(sd:<Decl b.bounds b.val t):>TOP
    _ => err st sx

export
if' : ByteBounds -> StateTrans STATE
if' b st sx = sx:>st:<b:>IF

export
then' : StateTrans STATE
then' st sx =
  case endTerm st sx of
    sy:>IF:<t:>TERM => sy:<t:>THEN
    _               => err st sx

export
else' : StateTrans STATE
else' st sx =
  case endTerm st sx of
    sy:>THEN:<t:>TERM => sy:<t:>ELSE
    _                 => err st sx

export
in' : StateTrans STATE
in' st sx =
  case endTerm st sx of
    sy:>LET_EQ:<t:>TERM    => sy:<t:>LET_IN
    sy:>LETREC_EQ:<t:>TERM => sy:<t:>LETREC_IN
    _                      => err st sx

export
let' : ByteBounds -> StateTrans STATE
let' b st sx = sx:>st:<b:>LET

export
letrec' : ByteBounds -> StateTrans STATE
letrec' b st sx = sx:>st:<b:>LETREC

pattern : Pattern -> StateTrans STATE
pattern p PATTERN_EQ (sx:<sp:<f) = sx:<(sp:<(f,p)):>PATTERN_PAT
pattern p LET        sx          = sx:<p:>LET_PATTERN
pattern p st sx = err st sx

export
var : ByteBounded VarName -> StateTrans STATE
var v LAMBDA             sx = sx:<NM v.val:>LAMBDA_VAR
var v LET                sx = pattern (PV $ NM v.val) LET sx
var v LETREC             sx = sx:<NM v.val:>LETREC_VAR
var v TOP                sx = sx:<v:>TOP_FUNNAME
var v PATTERN            sx = sx:<v:>PATTERN_FIELD
var v PATTERN_COMMA      sx = sx:<v:>PATTERN_FIELD
var v PATTERN_EQ         sx = pattern (PV $ NM v.val) PATTERN_EQ sx
var v RECORD             sx = sx:<v.val:>RECORD_FIELD
var v RECORD_COMMA       sx = sx:<v.val:>RECORD_FIELD
var v RECORD_TYPE        sx = sx:<v.val:>RECORD_TYPE_FIELD
var v RECORD_TYPE_COMMA  sx = sx:<v.val:>RECORD_TYPE_FIELD
var v st                 sx = atom (PVar v.bounds v.val) st sx

export
placeholder : StateTrans STATE
placeholder LAMBDA      sx = sx:<PH:>LAMBDA_VAR
placeholder LET         sx = pattern (PV PH) LET sx
placeholder LETREC      sx = sx:<PH:>LETREC_VAR
placeholder PATTERN_EQ  sx = pattern (PV PH) PATTERN_EQ sx
placeholder st          sx = err st sx

export
openTerm : ByteBounds -> StateTrans STATE
openTerm b st sx = sx:>st:<b:>TERM_OPEN

export
openType : ByteBounds -> StateTrans STATE
openType b st sx = sx:>st:<b:>TYPE_OPEN

export
openRecord : ByteBounds -> StateTrans STATE
openRecord b st sx = sx:>st:<b:<[<]:>RECORD

export
openRecordType : ByteBounds -> StateTrans STATE
openRecordType b st sx = sx:>st:<b:<[<]:>RECORD_TYPE

export
openPattern : ByteBounds -> StateTrans STATE
openPattern b st sx = sx:>st:<b:<[<]:>PATTERN

export
closePattern : StateTrans STATE
closePattern PATTERN (sx:>st:<_:<sp)     = pattern (PT $ sp <>> []) st sx
closePattern PATTERN_PAT (sx:>st:<_:<sp) = pattern (PT $ sp <>> []) st sx
closePattern st sx = err st sx

export
patternComma : StateTrans STATE
patternComma PATTERN_PAT sx = sx:>PATTERN_COMMA
patternComma st          sx = err st sx

export
projection : ByteBounded VarName -> StateTrans STATE
projection b APP (sx:<t:<ss) =
  case ss of
    i:<l => sx:<t:<(i:<PField (cast l <+> b.bounds) l b):>APP
    [<]  => sx:<PField (cast t <+> b.bounds) t b:<[<]:>APP
projection _ st sx = err st sx

export
closeTerm : StateTrans STATE
closeTerm st sx =
  case endTerm st sx of
    sx:>st:<_:<s:>SEQ:<t:>TERM => atom (seq s t) st sx
    sx:>st:<_:>TERM_OPEN:<t:>TERM => atom t st sx
    _ => err st sx

export
endRecordField : StateTrans STATE
endRecordField st sx =
  case endTerm st sx of
    sx:<sp:<v:>RECORD_EQ:<t:>TERM => sx:<(sp:<(v,t)):>RECORD
    _ => err st sx

export
recordComma : StateTrans STATE
recordComma st sx =
  case endRecordField st sx of
    sx:>RECORD => sx:>RECORD_COMMA
    _ => err st sx

export
closeRecord : ByteBounds -> StateTrans STATE
closeRecord b2 st sx =
  case endRecordField st sx of
    sx:>st:<b:<sp:>RECORD => atom (PRec (b<+>b2) (sp<>>[])) st sx
    _ => err st sx

export
closeType : StateTrans STATE
closeType st sx =
  case endType st sx of
    sx:>st:<b:>TYPE_OPEN:<t:>TYPE => typeAtom t st sx
    _ => err st sx

export
endRecordTypeField : StateTrans STATE
endRecordTypeField st sx =
  case endType st sx of
    sx:<sp:<v:>RECORD_TYPE_COLON:<t:>TYPE => sx:<(sp:<(v,t)):>RECORD_TYPE
    _ => err st sx

export
recordTypeComma : StateTrans STATE
recordTypeComma st sx =
  case endRecordTypeField st sx of
    sx:>RECORD_TYPE => sx:>RECORD_TYPE_COMMA
    _ => err st sx

export
closeRecordType : ByteBounds -> StateTrans STATE
closeRecordType b2 st sx =
  case endRecordTypeField st sx of
    sx:>st:<b:<sp:>RECORD_TYPE => typeAtom (PRec (b<+>b2) (sp<>>[])) st sx
    _ => err st sx

export
arrow : StateTrans STATE
arrow TYPE_SEQ sx = sx:>TYPE_ARROW
arrow st       sx = err st sx

export
openBounds : Stack b STATE ts -> Maybe (ByteBounds,String)
openBounds (sx:<b:>TERM_OPEN)               = Just (b, "(")
openBounds (sx:<b:<_:>SEQ)                  = Just (b, "(")
openBounds (sx:<b:<_:>RECORD)               = Just (b, "{")
openBounds (sx:<b:<_:<_:>RECORD_FIELD)      = Just (b, "{")
openBounds (sx:<b:<_:<_:>RECORD_EQ)         = Just (b, "{")
openBounds (sx:<b:<_:>RECORD_COMMA)         = Just (b, "{")
openBounds (sx:<b:<_:>PATTERN)              = Just (b, "{")
openBounds (sx:<b:<_:<_:>PATTERN_FIELD)     = Just (b, "{")
openBounds (sx:<b:<_:<_:>PATTERN_EQ)        = Just (b, "{")
openBounds (sx:<b:<_:>PATTERN_PAT)          = Just (b, "{")
openBounds (sx:<b:<_:>PATTERN_COMMA)        = Just (b, "{")
openBounds (sx:<b:<_:>RECORD_TYPE)          = Just (b, "{")
openBounds (sx:<b:<_:<_:>RECORD_TYPE_FIELD) = Just (b, "{")
openBounds (sx:<b:<_:<_:>RECORD_TYPE_COLON) = Just (b, "{")
openBounds (sx:<b:<_:>RECORD_TYPE_COMMA)    = Just (b, "{")
openBounds (sx:<_)                          = openBounds sx
openBounds (sx:>_)                          = openBounds sx
openBounds [<]                              = Nothing

test : List (StateTrans STATE)
test =
  [ var (pure "foo")
  , colon
  , openRecordType neutral
  , var (pure "foo")
  , colon
  , typeAtom (pvar $ pure "Nat")
  , typeSemicolon
  ]

run : List (StateTrans STATE) -> Stack True STATE [<]
run = foldl (\s,f => let sx:>st := s in f st sx) ([<[<]]:>TOP)
