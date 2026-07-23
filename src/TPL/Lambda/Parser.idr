module TPL.Lambda.Parser

import Derive.Prelude
import Syntax.T1
import Text.ILex.Derive
import TPL.Parser.Util
import public TPL.Lambda.Term

%default total
%hide Data.Linear.(.)
%language ElabReflection

%runElab deriveParserState "Lexers" "Lexer"
  ["TERM","ATOM","VAR","DOT","ERR"]

data STACK : Type where
  Top   : STACK
  App   : STACK -> Term -> SnocList Term -> STACK
  Term  : STACK -> Term -> STACK
  Lam   : STACK -> ByteBounds -> STACK
  LamV  : STACK -> ByteBounds -> VarName -> STACK
  Open  : STACK -> STACK
  If    : STACK -> ByteBounds -> STACK
  Then  : STACK -> ByteBounds -> Term -> STACK
  Else  : STACK -> ByteBounds -> Term -> Term -> STACK
  Err   : STACK

public export
0 SK : Type -> Type
SK = Stack TpeErr STACK Lexers

endTerm : Term -> STACK -> STACK
endTerm t (LamV s b v)   = endTerm (TLam (b <+> cast t) v t) s
endTerm t (Else s b x y) = endTerm (TIf (b <+> cast t) x y t) s
endTerm t s              = Term s t

endApp : STACK -> STACK
endApp (App s t st) = endTerm (appAllSnoc t st) s
endApp s            = Err

parameters {auto sk : SK q}

  onAtom : Term -> STACK -> F1 q Lexer
  onAtom t (App p x sx) = putStackAs (App p x (sx:<t)) ATOM
  onAtom t p            = putStackAs (App p t [<]) ATOM

  onIf   : ByteBounds -> STACK -> F1 q Lexer
  onIf b (Lam {}) = failUnexpected [] ERR
  onIf b s        = putStackAs (If s b) TERM

  onThen : STACK -> F1 q Lexer
  onThen s =
    case endApp s of
      Term (If s b) t => putStackAs (Then s b t) TERM
      _               => failUnexpected [] ERR

  onElse : STACK -> F1 q Lexer
  onElse s =
    case endApp s of
      Term (Then s b x) t => putStackAs (Else s b x t) TERM
      _                   => failUnexpected [] ERR

  onLambda : ByteBounds -> STACK -> F1 q Lexer
  onLambda b s = putStackAs (Lam s b) VAR

  onClose : STACK -> F1 q Lexer
  onClose s =
    case endApp s of
      Term (Open s) t => onAtom t s
      _               => failUnexpected [] ERR

  onVar : ByteBounded VarName -> STACK -> F1 q Lexer
  onVar v s =
    case v.val.name of
      "if"   => onIf v.bounds s
      "then" => onThen s
      "else" => onElse s
      _      => case s of
        Lam p b => putStackAs (LamV p b v.val) DOT
        _       => onAtom (TVar v.bounds v.val) s

atoms : Steps q Lexers SK
atoms =
     opn '(' (modStackAs SK Open TERM)
  :: bools (boundedWithStack $ onAtom . bool)
  ++ nats  (boundedWithStack $ onAtom . int)
  ++ varName (withStack . onVar)

ptrans : Lex1 q Lexers SK
ptrans =
  lex1
    [ E TERM $ spaced $ step ('\\' <|> 'λ') (boundsWithStack onLambda) :: atoms
    , E ATOM $ spaced $ close ')' (withStack onClose) :: atoms
    , E VAR  $ spaced $ varName (withStack . onVar)
    , E DOT  $ spaced [step' '.' TERM]
    ]

perr : Arr32 Lexers (SK q -> F1 q LamErr)
perr = arr32 Lexers (unexpected []) [E DOT $ unexpected ["."]]

peoi : Lexer -> SK q -> F1 q (Either LamErr Term)
peoi st sk t =
 let s # t := read1 sk.stack_ t
  in case endApp s of
       Term Top x      => Right x # t
       Term (Open _) _ => let x # t := Interfaces.unclosed ")" sk t in Left x # t
       _               => arrFail SK perr st sk t

public export
term : P1 q LamErr Term
term = P TERM (init Top) ptrans (\x => (Nothing #)) perr peoi
