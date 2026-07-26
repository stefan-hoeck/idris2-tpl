module TPL.Lambda.Typed.Parser.State

import Derive.Prelude
import Text.ILex.Derive
import TPL.Parser.Util
import public TPL.Lambda.Typed.Declaration

%default total
%language ElabReflection

%runElab deriveParserState "Lexers" "Lexer"
  [ "TOP", "TOP_SEP", "TERM", "ATOM", "ATOM_OR_CLOSE", "DOT", "EQ"
  , "VAR", "BINDNAME", "PATTERN"
  , "TYPE", "ARROW", "TYPE_NAME"
  , "ERR"
  ]

public export
0 RecField : Type
RecField = (VarName,PTerm)

public export
0 RecTypeField : Type
RecTypeField = (VarName,RawTpe)

public export
data STACK : Type where
  Top                 : SnocList Declaration -> STACK
  TopFun              : STACK -> ByteBounded VarName -> STACK
  Eval                : STACK -> STACK
  Alias               : STACK -> STACK
  AliasName           : STACK -> ByteBounded VarName -> STACK

  App                 : STACK -> PTerm -> SnocList PTerm -> STACK
  Term                : STACK -> PTerm -> STACK

  Lam                 : STACK -> BytePos -> STACK
  LamPat              : STACK -> BytePos -> Pattern -> STACK
  LamTpe              : STACK -> BytePos -> Pattern -> RawTpe -> STACK

  Let                 : STACK -> BytePos -> STACK
  LetPat              : STACK -> BytePos -> Pattern -> STACK
  LetTrm              : STACK -> BytePos -> Pattern -> PTerm -> STACK

  Letrec              : STACK -> BytePos -> STACK
  LetrecVar           : STACK -> BytePos -> BindName -> STACK
  LetrecTpe           : STACK -> BytePos -> BindName -> RawTpe -> STACK
  LetrecTrm           : STACK -> BytePos -> BindName -> RawTpe -> PTerm -> STACK

  If                  : STACK -> BytePos -> STACK
  Then                : STACK -> BytePos -> PTerm -> STACK
  Else                : STACK -> BytePos -> PTerm -> PTerm -> STACK

  Record              : STACK -> BytePos -> SnocList RecField -> STACK
  RecordField         : STACK -> BytePos -> SnocList RecField -> VarName -> STACK

  Pat                 : STACK -> BytePos -> SnocList PatField -> STACK
  PatFld              : STACK -> BytePos -> SnocList PatField -> ByteBounded VarName -> STACK

  OpnTrm              : STACK -> BytePos -> STACK
  Seq                 : STACK -> BytePos -> PTerm -> STACK

  Tpe                 : STACK -> RawTpe -> STACK
  TpeSeq              : STACK -> SnocList RawTpe -> RawTpe -> STACK
  OpnTpe              : STACK -> BytePos -> STACK
  RecordTpe           : STACK -> BytePos -> SnocList RecTypeField -> STACK
  RecordFld           : STACK -> BytePos -> SnocList RecTypeField -> VarName -> STACK

  Err                 : STACK

export %inline
recordTpe : STACK -> BytePos -> STACK
recordTpe s p = RecordTpe s p [<]

export %inline
record' : STACK -> BytePos -> STACK
record' s p = Record s p [<]

export %inline
pat : STACK -> BytePos -> STACK
pat s p = Pat s p [<]

public export
0 SK : Type -> Type
SK = Stack TpeErr STACK Lexers

endTerm : PTerm -> STACK -> STACK
endTerm t (LamTpe s b p tp)     = endTerm (PLam (fromPos b t) p tp t) s
endTerm t (LetTrm s b p x)      = endTerm (PLet (fromPos b t) p x t) s
endTerm t (LetrecTrm s b p x y) = endTerm (PLetrec (fromPos b t) p x y t) s
endTerm t (Else s b x y)        = endTerm (PIf (fromPos b t) x y t) s
endTerm t s                     = Term s t

endApp : STACK -> STACK
endApp (App s t st) = endTerm (appSnoc t st) s
endApp s            = Err

--------------------------------------------------------------------------------
-- State Transitions
--------------------------------------------------------------------------------

parameters {auto sk : SK q}

  --------
  -- Terms

  export
  onAtom : PTerm -> STACK -> F1 q Lexer
  onAtom t (App p x sx) = putStackAs (App p x (sx:<t)) ATOM_OR_CLOSE
  onAtom t p            = putStackAs (App p t [<]) ATOM_OR_CLOSE

  export
  termSemicolon : STACK -> F1 q Lexer
  termSemicolon s =
    case endApp s of
      Term (Seq s p x) y               => putStackAs (Seq s p $ seq x y) TERM
      Term (OpnTrm s p) x              => putStackAs (Seq s p x) TERM
      Term (Eval $ Top ds) x           => putStackAs (Top $ ds:<Eval x) TOP
      Term (TopFun (Top ds) (B v b)) x => putStackAs (Top $ ds:<Defn b v x) TOP
      _                                => failUnexpected [] ERR

  export
  closeTerm : STACK -> F1 q Lexer
  closeTerm s =
    case endApp s of
      Term (Seq s p x) y  => onAtom (seq x y) s
      Term (OpnTrm s p) x => onAtom x s
      _                   => failUnexpected [] ERR

  export
  closeRecord : BytePos -> STACK -> F1 q Lexer

  export
  recordComma : STACK -> F1 q Lexer

  export
  projection : ByteBounded VarName -> STACK -> F1 q Lexer

-- export
-- endRecordField : StateTrans STATE
-- endRecordField st sx =
--   case endTerm st sx of
--     sx:<sp:<v:>RECORD_EQ:<t:>TERM => sx:<(sp:<(v,t)):>RECORD
--     _ => err st sx
--
-- export
-- funname : ByteBounded VarName -> StateTrans STATE
-- funname x TOP sx = sx:<x:>TOP_FUNNAME
-- funname x st  sx = err st sx
--
-- export
-- colon : StateTrans STATE
-- colon LAMBDA_PAT        sx = sx:>LAMBDA_COLON
-- colon TOP_FUNNAME       sx = sx:>DECL_COLON
-- colon ALIAS_TYPENAME    sx = sx:>ALIAS_COLON
-- colon RECORD_TYPE_FIELD sx = sx:>RECORD_TYPE_COLON
-- colon LETREC_VAR        sx = sx:>LETREC_COLON
-- colon st                sx = err st sx
--
-- export
-- eq : StateTrans STATE
-- eq TOP_FUNNAME   sx = sx:>DEFN_EQ
-- eq RECORD_FIELD  sx = sx:>RECORD_EQ
-- eq LET_PAT       sx = sx:>LET_EQ
-- eq PATTERN_FIELD sx = sx:>PATTERN_EQ
-- eq st            sx =
--   case endType st sx of
--     sx:>LETREC_COLON:<t:>TYPE => sx:<t:>LETREC_EQ
--     _ => err st sx

  export
  then' : STACK -> F1 q Lexer
  then' s =
    case endApp s of
      Term (If p b) t => putStackAs (Then p b t) TERM
      _               => failUnexpected [] ERR

  export
  else' : STACK -> F1 q Lexer
  else' s =
    case endApp s of
      Term (Then p b x) y => putStackAs (Else p b x y) TERM
      _                   => failUnexpected [] ERR

  export
  in' : STACK -> F1 q Lexer
  in' s =
    case endApp s of
      Term (LetPat p b x) y => putStackAs (LetTrm p b x y) TERM
      _                     => failUnexpected [] ERR

  -----------
  -- Patterns

-- pattern : Pattern -> StateTrans STATE
-- pattern p PATTERN_EQ (sx:<sp:<f) = sx:<(sp:<(f,p)):>PATTERN_PAT
-- pattern p LET        sx          = sx:<p:>LET_PAT
-- pattern p LAMBDA     sx          = sx:<p:>LAMBDA_PAT
-- pattern p st sx = err st sx

  export
  openPattern : BytePos -> STACK -> F1 q Lexer
-- openPattern b st sx = sx:>st:<b:<[<]:>PATTERN
--
-- export
-- closePattern : StateTrans STATE
-- closePattern PATTERN (sx:>st:<_:<sp)     = pattern (PT $ sp <>> []) st sx
-- closePattern PATTERN_PAT (sx:>st:<_:<sp) = pattern (PT $ sp <>> []) st sx
-- closePattern st sx = err st sx
--
-- export
-- patternComma : StateTrans STATE
-- patternComma PATTERN_PAT sx = sx:>PATTERN_COMMA
-- patternComma st          sx = err st sx

  --------
  -- Types
--
-- export
-- typename : ByteBounded VarName -> StateTrans STATE
-- typename v ALIAS sx = sx:<v:>ALIAS_TYPENAME
-- typename _ st    sx = err st sx

-- endType : StateTrans STATE
-- endType TYPE_SEQ (sx:<ss:<s) = sx:<tpeAppAll ss s:>TYPE
-- endType st   sx              = err st sx

  export
  typeAtom : RawTpe -> STACK -> F1 q Lexer
-- typeAtom t TYPE_ARROW (sx:<ss:<s) = sx:<(ss:<s):<t:>TYPE_SEQ
-- typeAtom t st         sx          = sx:>st:<[<]:<t:>TYPE_SEQ

-- export
-- dot : StateTrans STATE
-- dot TYPE_SEQ (sx:>LAMBDA_COLON:<ss:<s) = sx:<(tpeAppAll ss s):>LAMBDA_DOT
-- dot st       sx                        = err st sx
--
-- export
-- typeSemicolon : StateTrans STATE
-- typeSemicolon st sx =
--   case endType st sx of
--     sx:<sd:<b:>ALIAS_COLON:<t:>TYPE => sx:<(sd:<Alias b.bounds b.val t):>TOP
--     sx:<sd:<b:>DECL_COLON:<t:>TYPE  => sx:<(sd:<Decl b.bounds b.val t):>TOP
--     _ => err st sx

-- export
-- closeType : StateTrans STATE
-- closeType st sx =
--   case endType st sx of
--     sx:>st:<b:>TYPE_OPEN:<t:>TYPE => typeAtom t st sx
--     _ => err st sx
--
-- export
-- endRecordTypeField : StateTrans STATE
-- endRecordTypeField st sx =
--   case endType st sx of
--     sx:<sp:<v:>RECORD_TYPE_COLON:<t:>TYPE => sx:<(sp:<(v,t)):>RECORD_TYPE
--     _ => err st sx
--
-- export
-- recordTypeComma : StateTrans STATE
-- recordTypeComma st sx =
--   case endRecordTypeField st sx of
--     sx:>RECORD_TYPE => sx:>RECORD_TYPE_COMMA
--     _ => err st sx
--
-- export
-- closeRecordType : ByteBounds -> StateTrans STATE
-- closeRecordType b2 st sx =
--   case endRecordTypeField st sx of
--     sx:>st:<b:<sp:>RECORD_TYPE => typeAtom (PRec (b<+>b2) (sp<>>[])) st sx
--     _ => err st sx
--
-- export
-- arrow : StateTrans STATE
-- arrow TYPE_SEQ sx = sx:>TYPE_ARROW
-- arrow st       sx = err st sx

  export
  var : ByteBounded VarName -> STACK -> F1 q Lexer
-- var v LAMBDA             sx = pattern (PV $ NM v.val) LAMBDA sx
-- var v LET                sx = pattern (PV $ NM v.val) LET sx
-- var v LETREC             sx = sx:<NM v.val:>LETREC_VAR
-- var v TOP                sx = sx:<v:>TOP_FUNNAME
-- var v PATTERN            sx = sx:<v:>PATTERN_FIELD
-- var v PATTERN_COMMA      sx = sx:<v:>PATTERN_FIELD
-- var v PATTERN_EQ         sx = pattern (PV $ NM v.val) PATTERN_EQ sx
-- var v RECORD             sx = sx:<v.val:>RECORD_FIELD
-- var v RECORD_COMMA       sx = sx:<v.val:>RECORD_FIELD
-- var v RECORD_TYPE        sx = sx:<v.val:>RECORD_TYPE_FIELD
-- var v RECORD_TYPE_COMMA  sx = sx:<v.val:>RECORD_TYPE_FIELD
-- var v st                 sx = atom (PVar v.bounds v.val) st sx
--
  export
  placeholder : STACK -> F1 q Lexer
-- placeholder LAMBDA      sx = pattern (PV PH) LAMBDA sx
-- placeholder LET         sx = pattern (PV PH) LET sx
-- placeholder LETREC      sx = sx:<PH:>LETREC_VAR
-- placeholder PATTERN_EQ  sx = pattern (PV PH) PATTERN_EQ sx
-- placeholder st          sx = err st sx
