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
  , "TYPE", "ARROW", "ALIAS_NAME", "COLON"
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
  Alias               : STACK -> ByteBounded VarName -> STACK

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
  RecordFld           : STACK -> BytePos -> SnocList RecField -> VarName -> STACK

  Pat                 : STACK -> BytePos -> SnocList PatField -> STACK
  PatFld              : STACK -> BytePos -> SnocList PatField -> ByteBounded VarName -> STACK

  OpnTrm              : STACK -> BytePos -> STACK
  Seq                 : STACK -> BytePos -> PTerm -> STACK

  Tpe                 : STACK -> RawTpe -> STACK
  TpeSeq              : STACK -> SnocList RawTpe -> RawTpe -> STACK
  OpnTpe              : STACK -> BytePos -> STACK
  RecordTpe           : STACK -> BytePos -> SnocList RecTypeField -> STACK
  RecordTpeFld        : STACK -> BytePos -> SnocList RecTypeField -> VarName -> STACK

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

endType : STACK -> STACK
endType (TpeSeq p ss s) = Tpe p (tpeAppAll ss s)
endType _               = Err

--------------------------------------------------------------------------------
-- State Transitions
--------------------------------------------------------------------------------

parameters {auto sk : SK q}
  export %inline
  die : F1 q Lexer
  die = failUnexpected [] ERR

  export %inline
  pushDecl : Declaration -> STACK -> F1 q Lexer
  pushDecl d (Top sd) = putStackAs (Top $ sd:<d) TOP
  pushDecl _ _        = die

  export %inline
  alias : ByteBounded VarName -> STACK -> F1 q Lexer
  alias b s = putStackAs (Alias s b) COLON

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
      Term (Seq s p x) y        => putStackAs (Seq s p $ seq x y) TERM
      Term (OpnTrm s p) x       => putStackAs (Seq s p x) TERM
      Term (Eval p) x           => pushDecl (Eval x) p
      Term (TopFun p (B v b)) x => pushDecl (Defn b v x) p
      _                         => die

  export
  closeTerm : STACK -> F1 q Lexer
  closeTerm s =
    case endApp s of
      Term (Seq s p x) y  => onAtom (seq x y) s
      Term (OpnTrm s p) x => onAtom x s
      _                   => die

  export
  closeRecord : BytePos -> STACK -> F1 q Lexer
  closeRecord y s =
    case endApp s of
      Term (RecordFld s x sp f) t => onAtom (PRec (BB x y) (sp<>>[(f,t)])) s
      _                           => die

  export
  recordComma : STACK -> F1 q Lexer
  recordComma s =
    case endApp s of
      Term (RecordFld s x sp f) t => putStackAs (Record s x $ sp:<(f,t)) VAR
      _                           => die

--   export
--   projection : ByteBounded VarName -> STACK -> F1 q Lexer

  export
  then' : STACK -> F1 q Lexer
  then' s =
    case endApp s of
      Term (If p b) t => putStackAs (Then p b t) TERM
      _               => die

  export
  else' : STACK -> F1 q Lexer
  else' s =
    case endApp s of
      Term (Then p b x) y => putStackAs (Else p b x y) TERM
      _                   => die

  export
  in' : STACK -> F1 q Lexer
  in' s =
    case endApp s of
      Term (LetPat p b x) y => putStackAs (LetTrm p b x y) TERM
      _                     => die

  -----------
  -- Patterns

-- pattern : Pattern -> StateTrans STATE
-- pattern p PATTERN_EQ (sx:<sp:<f) = sx:<(sp:<(f,p)):>PATTERN_PAT
-- pattern p LET        sx          = sx:<p:>LET_PAT
-- pattern p LAMBDA     sx          = sx:<p:>LAMBDA_PAT
-- pattern p st sx = err st sx

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


  export
  typeAtom : RawTpe -> STACK -> F1 q Lexer
  typeAtom t (TpeSeq p st s) = putStackAs (TpeSeq p (st:<s) t) ARROW
  typeAtom t p               = putStackAs (TpeSeq p [<] t) ARROW

  export
  dot : STACK -> F1 q Lexer
  dot s =
    case endType s of
      Tpe (LamPat s p x) t => putStackAs (LamTpe s p x t) TERM
      _                    => die

  export
  typeSemicolon : STACK -> F1 q Lexer
  typeSemicolon s =
    case endType s of
      Tpe (TopFun p b) t => pushDecl (Decl b.bounds b.val t) p
      Tpe (Alias p b)  t => pushDecl (Alias b.bounds b.val t) p
      _                  => die

  export
  closeType : STACK -> F1 q Lexer
  closeType s =
    case endType s of
      Tpe (OpnTpe p _) t => typeAtom t p
      _                  => die

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

  export
  placeholder : STACK -> F1 q Lexer
  placeholder s = die
  -- placeholder LAMBDA      sx = pattern (PV PH) LAMBDA sx
  -- placeholder LET         sx = pattern (PV PH) LET sx
  -- placeholder LETREC      sx = sx:<PH:>LETREC_VAR
  -- placeholder PATTERN_EQ  sx = pattern (PV PH) PATTERN_EQ sx
  -- placeholder st          sx = err st sx

  export
  var : ByteBounded VarName -> STACK -> F1 q Lexer
  var b (Top sx)           = putStackAs (TopFun (Top sx) b) TOP_SEP
  var b (Record x y sx)    = putStackAs (RecordFld x y sx b.val) EQ
  var b (RecordTpe x y sx) = putStackAs (RecordTpeFld x y sx b.val) COLON
  var b s                  = onAtom (PVar b.bounds b.val) s
