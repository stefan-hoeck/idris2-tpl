module TPL.Lambda.Typed.Parser.State

import Text.ILex.DStack
import public Data.SnocList.Quantifiers
import public TPL.Lambda.Typed.Declaration

%default total

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

  APP              : STATE [<Term]
  TERM_OPEN        : STATE [<ByteBounds]
  SEQ              : STATE [<ByteBounds,Term]

  IF               : STATE [<ByteBounds]
  THEN             : STATE [<ByteBounds,Term]
  ELSE             : STATE [<ByteBounds,Term,Term]

  TYPE_SEQ         : STATE [<SnocList RawTpe, RawTpe]
  TYPE_ARROW       : STATE [<SnocList RawTpe, RawTpe]
  TYPE_OPEN        : STATE [<ByteBounds]

  ERR              : STATE [<]

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

reduceTerm : Term -> STATE ss -> Stack b STATE ss -> Stack False STATE [<Term]
reduceTerm x LAMBDA_DOT sx      = ?reduceTerm_rhs_11
reduceTerm x APP        (sx:<y) = ?reduceTerm_rhs_12
reduceTerm x ELSE       sx      = ?reduceTerm_rhs_17
reduceTerm x st         sx      = sx:>st:<x

funname : ByteBounded VarName -> StateTrans STATE
funname x TOP sx = sx:<x:>TOP_FUNNAME
funname x st  sx = err st sx

eval : StateTrans STATE
eval TOP sx = sx:>EVAL
eval st  sx = err st sx

colon : StateTrans STATE
colon LAMBDA_VAR     sx = sx:>LAMBDA_COLON
colon TOP_FUNNAME    sx = sx:>DECL_COLON
colon ALIAS_TYPENAME sx = sx:>ALIAS_COLON
colon st             sx = err st sx

eq : StateTrans STATE
eq TOP_FUNNAME sx = sx:>DEFN_EQ
eq st          sx = err st sx

lambda : ByteBounds -> StateTrans STATE
lambda b st sx = sx:>st:<b:>LAMBDA

term : Term -> StateTrans STATE
term x APP (sx:<y) = sx:<TApp (cast x <+> cast y) x y:>APP
term x st  sx      = sx:>st:<x:>APP

semicolon : StateTrans STATE
semicolon APP (sx:>st:<x) =
  case reduceTerm x st sx of
    v => ?foo
