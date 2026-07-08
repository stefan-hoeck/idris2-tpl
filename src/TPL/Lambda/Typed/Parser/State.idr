module TPL.Lambda.Typed.Parser.State

import Derive.Prelude
import Text.ILex.DStack
import public Data.SnocList.Quantifiers
import public TPL.Lambda.Typed.Declaration

%default total
%language ElabReflection

public export
data STATE : SnocList Type -> Type where
  TOP              : STATE [<SnocList Declaration]

  TOP_FUNNAME      : STATE [<SnocList Declaration,ByteBounded VarName]
  DECL_COLON       : STATE [<SnocList Declaration,ByteBounded VarName]
  DEFN_EQ          : STATE [<SnocList Declaration,ByteBounded VarName]

  EVAL             : STATE [<SnocList Declaration]

  ALIAS            : STATE [<SnocList Declaration]
  ALIAS_TYPENAME   : STATE [<SnocList Declaration,ByteBounded VarName]
  ALIAS_COLON      : STATE [<SnocList Declaration,ByteBounded VarName]

  LAMBDA           : STATE [<ByteBounds]
  LAMBDA_VAR       : STATE [<ByteBounds,BindName]
  LAMBDA_COLON     : STATE [<ByteBounds,BindName]
  LAMBDA_DOT       : STATE [<ByteBounds,BindName,RawTpe]

  TERM             : STATE [<Term]
  TERM_OPEN        : STATE [<ByteBounds]
  SEQ              : STATE [<ByteBounds,Term]

  IF               : STATE [<ByteBounds]
  THEN             : STATE [<ByteBounds,Term]
  ELSE             : STATE [<ByteBounds,Term,Term]

  TYPE             : STATE [<RawTpe]
  TYPE_SEQ         : STATE [<SnocList RawTpe, RawTpe]
  TYPE_ARROW       : STATE [<SnocList RawTpe, RawTpe]
  TYPE_OPEN        : STATE [<ByteBounds]

  ERR              : STATE [<]

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

term : Term -> StateTrans STATE
term x LAMBDA_DOT (sx:>st:<b:<v:<bt) = term (TLam b v bt x) st sx
term x TERM       (sx:>st:<y)        = term (app y x) st sx
term x ELSE       (sx:>st:<b:<i:<t)  = term (tif b i t x) st sx
term x st         sx                 = sx:>st:<x:>TERM

endTerm : StateTrans STATE
endTerm TERM (sx:>st:<x) = term x st sx
endTerm st   sx          = err st sx

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
colon LAMBDA_VAR     sx = sx:>LAMBDA_COLON
colon TOP_FUNNAME    sx = sx:>DECL_COLON
colon ALIAS_TYPENAME sx = sx:>ALIAS_COLON
colon st             sx = err st sx

export
eq : StateTrans STATE
eq TOP_FUNNAME sx = sx:>DEFN_EQ
eq st          sx = err st sx

export
lambda : ByteBounds -> StateTrans STATE
lambda b st sx = sx:>st:<b:>LAMBDA

export
dot : StateTrans STATE
dot TYPE_SEQ (sx:>LAMBDA_COLON:<ss:<s) = sx:<(tpeAppAll ss s):>LAMBDA_DOT
dot st       sx                        = err st sx

export
atom : Term -> StateTrans STATE
atom x TERM (sx:<y) = sx:<app y x:>TERM
atom x st   sx      = sx:>st:<x:>TERM

export
typeAtom : RawTpe -> StateTrans STATE
typeAtom t TYPE_ARROW (sx:<ss:<s) = sx:<(ss:<s):<t:>TYPE_SEQ
typeAtom t st         sx          = sx:>st:<[<]:<t:>TYPE_SEQ

export
termSemicolon : StateTrans STATE
termSemicolon st sx =
  case endTerm st sx of
    sy:>TERM_OPEN:<t:>TERM       => sy:<t:>SEQ
    sy:<s:>SEQ:<t:>TERM          => sy:<(seq s t):>SEQ
    sy:<sd:>EVAL:<t:>TERM        => sy:<(sd:<Eval t):>TOP
    sy:<sd:<vn:>DEFN_EQ:<t:>TERM => sy:<(sd:<Defn vn.bounds vn.val t):>TOP
    _                            => err st sx

export
typeSemicolon : StateTrans STATE
typeSemicolon st sx =
  case endType st sx of
    sx:<sd:<(B v b):>ALIAS_COLON:<t:>TYPE => sx:<(sd:<Alias b v t):>TOP
    sx:<sd:<(B v b):>DECL_COLON:<t:>TYPE  => sx:<(sd:<Decl b v t):>TOP
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
var : ByteBounded VarName -> StateTrans STATE
var v st sx =
  case v.val.name of
    "if"   => if' v.bounds st sx
    "then" => then' st sx
    "else" => else' st sx
    _      => case st of
      LAMBDA => sx:<NM v.val:>LAMBDA_VAR
      TOP    => sx:<v:>TOP_FUNNAME
      _      => atom (TVar v.bounds v.val) st sx

export
placeholder : StateTrans STATE
placeholder LAMBDA sx = sx:<PH:>LAMBDA_VAR
placeholder st     sx = err st sx

export
openTerm : ByteBounds -> StateTrans STATE
openTerm b st sx = sx:>st:<b:>TERM_OPEN

export
openType : ByteBounds -> StateTrans STATE
openType b st sx = sx:>st:<b:>TYPE_OPEN

export
closeTerm : StateTrans STATE
closeTerm st sx =
  case endTerm st sx of
    sx:>st:<_:<s:>SEQ:<t:>TERM => atom (seq s t) st sx
    sx:>st:<_:>TERM_OPEN:<t:>TERM => atom t st sx
    _ => err st sx

export
closeType : StateTrans STATE
closeType st sx =
  case endType st sx of
    sx:>st:<b:>TYPE_OPEN:<t:>TYPE => typeAtom t st sx
    _ => err st sx

export
arrow : StateTrans STATE
arrow TYPE_SEQ sx = sx:>TYPE_ARROW
arrow st       sx = err st sx

export
openBounds : Stack b STATE st -> Maybe ByteBounds
openBounds [<]               = Nothing
openBounds (_:<b:>TERM_OPEN) = Just b
openBounds (_:<b:>TYPE_OPEN) = Just b
openBounds (_:<b:<_:>SEQ)    = Just b
openBounds (x:>_)            = openBounds x
openBounds (x:<_)            = openBounds x


seq : List (StateTrans STATE) -> Stack True STATE [<]
seq = foldl (\sk,f => let sx:>st := sk in f st sx) ([<[<]]:>TOP)

test : Stack True STATE [<]
test =
  seq
    [ eval
    , openTerm NoBB
    , if' NoBB
    , atom (unit NoBB)
    , then'
    , atom (unit NoBB)
    , else'
    , atom (unit NoBB)
    , openTerm NoBB
    , atom (unit NoBB)
    , atom (unit NoBB)
    , closeTerm
    , atom (unit NoBB)
    , closeTerm
    , atom (unit NoBB)
    , termSemicolon
    ]
