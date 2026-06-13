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

value : PState s -> DFA q PSz SK
value x =
  spaced x
    [ cexpr "true"  (dact $ onTerm (bool True))
    , cexpr "false" (dact $ onTerm (bool False))
    , cexpr "if" (dpush0 PIf)
    , cexpr "succ" (dpush0 PSucc)
    , cexpr "pred" (dpush0 PPred)
    , cexpr "iszero" (dpush0 PIsZ)
    , conv (like "0b" >> binary) (onInt . binary . drop 2)
    , conv (like "0o" >> octal) (onInt . octal . drop 2)
    , conv (like "0x" >> hexadecimal) (onInt . hexadecimal . drop 2)
    , conv decimal (dact . onTerm . int . decimal)
    , copen '(' (dpush0 POpn)
    ]

ptrans : Lex1 q PSz SK
ptrans =
  lex1
    [ entry PIni   $ value PIni
    , entry POpn   $ value POpn
    , entry PIf    $ value PIf
    , entry PThen  $ value PThen
    , entry PElse  $ value PElse
    , entry PSucc  $ value PSucc
    , entry PPred  $ value PPred
    , entry PIsZ   $ value PIsZ
    , entry PCls   $ spaced PCls [cclose ')' $ dact onClose]
    , entry PIfV   $ spaced PIfV [cexpr "then" $ dact onThen]
    , entry PThenV $ spaced PThenV [cexpr "else" $ dact onElse]
    ]

values : List String
values =
  ["if", "true", "false", "succ", "pred", "iszero", "0", "("]

perr : Arr32 PSz (SK q -> F1 q (BoundedErr Void))
perr =
  arr32 PSz (unexpected values)
    [ entry PIfV   $ unexpected ["then"]
    , entry PThenV $ unexpected ["else"]
    , entry PCls   $ unclosedIfEOI "(" [")"]
    ]

peoi : Index PSz -> SK q -> F1 q (Either (BoundedErr Void) Term)
peoi st sk t =
 let (PTerm:>[x]) # t := read1 sk.stack_ t | _ # t => arrFail SK perr st sk t
  in Right x # t

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
testTerm : String -> IO ()
testTerm =
  putStrLn . either interpolate interpolate . parseString term Virtual

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
