module TPL.ArExp.Parser

import Derive.Prelude
import Text.ILex.Derive
import Syntax.T1
import public TPL.ArExp.TT
import public TPL.ArExp.Term
import public TPL.Parser.Util

%default total
%hide Data.Linear.(.)
%language ElabReflection

%runElab deriveParserState "Lexers" "Lexer"
  ["TERM","ATOM","THEN","ELSE","CLOSE","DONE","ERR"]

--------------------------------------------------------------------------------
-- Parser Stack
--------------------------------------------------------------------------------

data STACK : Type where
  Top   : STACK
  If    : STACK -> ByteBounds -> STACK
  Fun   : STACK -> (Term -> Term) -> STACK
  Open  : STACK -> STACK
  Paren : STACK -> Term -> STACK
  Then  : STACK -> ByteBounds -> Term -> STACK
  Else  : STACK -> ByteBounds -> Term -> Term -> STACK
  Done  : Term -> STACK

0 SK : Type -> Type
SK = Stack (TplErr Tpe) STACK Lexers

parameters {auto sk : SK q}

  onTerm : Term -> STACK -> F1 q Lexer
  onTerm x (If p b)       = putStackAs (Then p b x) THEN
  onTerm x (Fun p f)      = onTerm (f x) p
  onTerm x (Open p)       = putStackAs (Paren p x) CLOSE
  onTerm x (Then p b y)   = putStackAs (Else p b y x) ELSE
  onTerm x (Else p b y z) = onTerm (TIf (b <+> cast x) y z x) p
  onTerm x _              = putStackAs (Done x) DONE

  onClose : F1 q Lexer
  onClose =
    getStack >>= \case
      Paren p t => onTerm t p
      _         => pure ERR -- not possible

  onFun : (ByteBounds -> Term -> Term) -> F1 q Lexer
  onFun f = bounds >>= \b => modStackAs SK (`Fun` f b) ATOM

  onIf : F1 q Lexer
  onIf = bounds >>= \b => modStackAs SK (`If` b) TERM

atomSteps : Steps q Lexers SK
atomSteps =
     opn '(' (modStackAs SK Open TERM)
  :: bools (boundedWithStack $ onTerm . bool)
  ++ nats  (boundedWithStack $ onTerm . int)


ptrans : Lex1 q Lexers SK
ptrans =
  lex1
    [ E TERM $ spaced $
        [ step (like "if")     onIf
        , step (like "succ")   (onFun TSucc)
        , step (like "pred")   (onFun TPred)
        , step (like "iszero") (onFun TIsZ)
        ] ++ atomSteps
    , E ATOM $ spaced atomSteps
    , E THEN  $ spaced [step' (like "then") TERM]
    , E ELSE  $ spaced [step' (like "else") TERM]
    , E CLOSE $ spaced [close ")" onClose]
    ]

atms : List String
atms = ["true", "false", "0", "("]

values : List String
values = ["if", "succ", "pred", "iszero"] ++ atms

perr : Arr32 Lexers (SK q -> F1 q ArErr)
perr =
  errs
    [ E TERM  $ unexpected values
    , E ATOM  $ unexpected atms
    , E THEN  $ unexpected ["then"]
    , E ELSE  $ unexpected ["else"]
    , E CLOSE $ unclosedIfEOI ")" [")"]
    ]

peoi : Lexer -> SK q -> F1 q (Either ArErr Term)
peoi st sk t =
 let Done x # t := getStack t | _ # t => arrFail SK perr st sk t
  in Right x # t

||| Syntax for arithmetic terms (ABNF)
|||
||| Terms:
|||   term        = atom / func / "if" ws term ws "then" ws term ws "else" ws term
|||   func        = funname ws atom
|||   atom        = "true" / "false" / nat / "(" ws term ws ")"
|||   funname     = "succ" / "pred" / "iszero"
|||
||| Literals:
|||   nat         = decimal / binary / octal / hexadecimal
|||   binary      = "0b" *1bit
|||   octal       = "0o" *1octit
|||   hexadecimal = "0x" *1hexit
|||   decimal     = "0" / nonzero *digit
|||   bit         = %x30 / %x31; '0' or '1'
|||   octit       = %x30-37; '0' to '7'
|||   nonzero     = %x31-39; '1' to '9'
|||   digit       = %x30-39; '0' to '9'
|||   hexit       = digit / "a" / "b" / "c" / "d" / "e" / "f"
|||
||| White space:
|||   ws          = *wschar
|||   wschar      = %x0a / %x0d / %x09 / %x20
public export
term : P1 q ArErr Term
term = P TERM (init Top) ptrans (\x => (Nothing #)) perr peoi
