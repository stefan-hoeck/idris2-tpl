module TPL.ArExp.Parser

import Derive.Prelude
import Text.ILex
import Text.ILex.DStack
import public TPL.ArExp.Term

%default total
%hide Data.Linear.(.)
%language ElabReflection

--------------------------------------------------------------------------------
-- Parser Stack
--------------------------------------------------------------------------------

data PState : List Type -> Type where
  PIni   : PState []
  POpn   : PState []
  PIsZ   : PState []
  PSucc  : PState []
  PIf    : PState []
  PPred  : PState []
  PCls   : PState [Term]
  PIfV   : PState [Term]
  PThen  : PState [Term]
  PThenV : PState [Term,Term]
  PElse  : PState [Term,Term]
  PTerm  : PState [Term]
  PErr   : PState []

%runElab deriveIndexed "PState" [Show,ConIndex]

PSz : Bits32
PSz = 1 + cast (conIndexPState PErr)

inBoundsPState : (s : PState ts) -> (cast (conIndexPState s) < PSz) === True

export %inline
Cast (PState ts) (Index PSz) where
  cast v = I (cast $ conIndexPState v) @{mkLT $ inBoundsPState v}

public export
0 SK : Type -> Type
SK = DStack PState Void

parameters {auto sk : SK q}
  onTerm : Term -> StateAct q PState PSz
  onTerm trm POpn   x               t = dput PCls (trm::x) t
  onTerm trm PIni   x               t = dput PTerm [trm] t
  onTerm trm PIf    x               t = dput PIfV (trm::x) t
  onTerm trm PThen  x               t = dput PThenV (trm::x) t
  onTerm trm PSucc  (pst:>st)       t = onTerm (TSucc trm) pst st t
  onTerm trm PPred  (pst:>st)       t = onTerm (TPred trm) pst st t
  onTerm trm PIsZ   (pst:>st)       t = onTerm (TIsZ trm) pst st t
  onTerm trm PElse  [x,y]           t = dput PTerm [TIf y x trm] t
  onTerm trm PElse  (x::y::pst:>st) t = onTerm (TIf y x trm) pst st t
  onTerm trm st     x               t = derr PErr st x t

  onInt : Integer -> F1 q (Index PSz)
  onInt = dact . onTerm . int

  onThen : StateAct q PState PSz
  onThen PIfV x t = dput PThen x t
  onThen st   x t = derr PErr st x t

  onElse : StateAct q PState PSz
  onElse PThenV x t = dput PElse x t
  onElse st     x t = derr PErr st x t

  onClose : StateAct q PState PSz
  onClose PCls (v::st:>x) t = onTerm v st x t
  onClose st   x          t = derr PErr st x t

%inline
spaced : PState s -> Steps q PSz SK -> DFA q PSz SK
spaced x = dfa . jsonSpaced x

atom : Steps q PSz SK
atom =
  [ cexpr (like "true")  (dact $ onTerm (bool True))
  , cexpr (like "false") (dact $ onTerm (bool False))
  , conv (like "0b" >> binary) (onInt . binary . drop 2)
  , conv (like "0o" >> octal) (onInt . octal . drop 2)
  , conv (like "0x" >> hexadecimal) (onInt . hexadecimal . drop 2)
  , conv decimal (dact . onTerm . int . decimal)
  , copen '(' (dpush0 POpn)
  ]

value : PState s -> DFA q PSz SK
value x =
  spaced x $
    [ cexpr (like "if")     (dpush0 PIf)
    , cexpr (like "succ")   (dpush0 PSucc)
    , cexpr (like "pred")   (dpush0 PPred)
    , cexpr (like "iszero") (dpush0 PIsZ)
    ] ++ atom

ptrans : Lex1 q PSz SK
ptrans =
  lex1
    [ entry PIni   $ value PIni
    , entry POpn   $ value POpn
    , entry PIf    $ value PIf
    , entry PThen  $ value PThen
    , entry PElse  $ value PElse
    , entry PSucc  $ spaced PSucc atom
    , entry PPred  $ spaced PPred atom
    , entry PIsZ   $ spaced PIsZ atom
    , entry PCls   $ spaced PCls [cclose ')' $ dact onClose]
    , entry PIfV   $ spaced PIfV [cexpr (like "then") $ dact onThen]
    , entry PThenV $ spaced PThenV [cexpr (like "else") $ dact onElse]
    ]

atms : List String
atms = ["true", "false", "0", "("]

values : List String
values = ["if", "succ", "pred", "iszero"] ++ atms

perr : Arr32 PSz (SK q -> F1 q (BoundedErr Void))
perr =
  arr32 PSz (unexpected values)
    [ entry PIfV   $ unexpected ["then"]
    , entry PThenV $ unexpected ["else"]
    , entry PCls   $ unclosedIfEOI "(" [")"]
    , entry PSucc  $ unexpected atms
    , entry PPred  $ unexpected atms
    , entry PIsZ   $ unexpected atms
    ]

peoi : Index PSz -> SK q -> F1 q (Either (BoundedErr Void) Term)
peoi st sk t =
 let (PTerm:>[x]) # t := read1 sk.stack_ t | _ # t => arrFail SK perr st sk t
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
term : P1 q (BoundedErr Void) Term
term = P (cast PIni) (init $ PIni:>[]) ptrans (\x => (Nothing #)) perr peoi

example : String
example =
  """
  if (iszero (succ 0xf))
     then 100
     else (pred 0b10011)
  """

export
testParse : String -> IO ()
testParse =
  putStrLn . either interpolate interpolate . parseString term Virtual

export
testEval : String -> IO ()
testEval s =
  case parseString term Virtual s of
    Left err => putStrLn "\{err}"
    Right t  => case eval t of
      Left  t2 => putStrLn "STUCK: \{t2}"
      Right v => putStrLn "\{v}"

--------------------------------------------------------------------------------
-- Proofs
--------------------------------------------------------------------------------

inBoundsPState PIni   = Refl
inBoundsPState POpn   = Refl
inBoundsPState PIsZ   = Refl
inBoundsPState PSucc  = Refl
inBoundsPState PIf    = Refl
inBoundsPState PPred  = Refl
inBoundsPState PCls   = Refl
inBoundsPState PIfV   = Refl
inBoundsPState PThen  = Refl
inBoundsPState PThenV = Refl
inBoundsPState PElse  = Refl
inBoundsPState PTerm  = Refl
inBoundsPState PErr   = Refl
