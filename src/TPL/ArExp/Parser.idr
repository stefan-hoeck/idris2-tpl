module TPL.ArExp.Parser

import Derive.Prelude
import Syntax.T1
import public TPL.ArExp.TT
import public TPL.ArExp.Term
import public TPL.Parser.Util

%default total
%hide Data.Linear.(.)
%language ElabReflection

--------------------------------------------------------------------------------
-- Parser Stack
--------------------------------------------------------------------------------

data PState : SnocList Type -> Type where
  PIni   : PState [<]
  POpn   : PState [<]
  PIsZ   : PState [<ByteBounds]
  PSucc  : PState [<ByteBounds]
  PIf    : PState [<ByteBounds]
  PPred  : PState [<ByteBounds]
  PCls   : PState [<Term]
  PIfV   : PState [<ByteBounds,Term]
  PThen  : PState [<ByteBounds,Term]
  PThenV : PState [<ByteBounds,Term,Term]
  PElse  : PState [<ByteBounds,Term,Term]
  PTerm  : PState [<Term]
  PErr   : PState [<]

%runElab deriveIndexed "PState" [Show,ConIndex]

PSz : Bits32
PSz = 1 + cast (conIndexPState PErr)

inBoundsPState : (s : PState ts) -> (cast (conIndexPState s) < PSz) === True

export %inline
Cast (PState ts) (Index PSz) where
  cast v = I (cast $ conIndexPState v) @{mkLT $ inBoundsPState v}

public export
0 SK : Type -> Type
SK = DStack PState TpeErr

parameters {auto sk : SK q}
  onTerm : Term -> StateAct q PState PSz
  onTerm trm POpn   sx                  t = dput PCls (sx:<trm) t
  onTerm trm PIni   sx                  t = dput PTerm [<trm] t
  onTerm trm PIf    sx                  t = dput PIfV (sx:<trm) t
  onTerm trm PThen  sx                  t = dput PThenV (sx:<trm) t
  onTerm trm PSucc  (sx:>pst:<bb)       t =
    onTerm (TSucc (bb <+> cast trm) trm) pst sx t
  onTerm trm PPred  (sx:>pst:<bb)       t =
    onTerm (TPred (bb <+> cast trm) trm) pst sx t
  onTerm trm PIsZ   (sx:>pst:<bb)       t =
    onTerm (TIsZ (bb <+> cast trm) trm) pst sx t
  onTerm trm PElse  [<bb,x,y]           t =
    dput PTerm [<TIf (bb <+> cast trm) x y trm] t
  onTerm trm PElse  (sx:>pst:<bb:<x:<y) t =
    onTerm (TIf (bb <+> cast trm) x y trm) pst sx t
  onTerm trm st     sx                  t = derr PErr sx st t

  onThen : StateAct q PState PSz
  onThen PIfV sx t = dput PThen sx t
  onThen st   sx t = derr PErr sx st t

  onElse : StateAct q PState PSz
  onElse PThenV sx t = dput PElse sx t
  onElse st     sx t = derr PErr sx st t

  onClose : StateAct q PState PSz
  onClose PCls (sx:>st:<v) t = onTerm v st sx t
  onClose st   sx          t = derr PErr sx st t

atomSteps : Steps q PSz SK
atomSteps =
     opn '(' (dpush0 POpn)
  :: bools (\b => bounded' b >>= dact . onTerm . bool)
  ++ nats  (\b => bounded' b >>= dact . onTerm . int)

atom : DFA q PSz SK
atom = spaced atomSteps

value : DFA q PSz SK
value =
  spaced $
    [ step (like "if")     (bounds >>= dpush PIf)
    , step (like "succ")   (bounds >>= dpush PSucc)
    , step (like "pred")   (bounds >>= dpush PPred)
    , step (like "iszero") (bounds >>= dpush PIsZ)
    ] ++ atomSteps

ptrans : Lex1 q PSz SK
ptrans =
  lex1
    [ entry PIni     value
    , entry POpn     value
    , entry PIf      value
    , entry PThen    value
    , entry PElse    value
    , entry PSucc    atom
    , entry PPred    atom
    , entry PIsZ     atom
    , entry PCls   $ spaced [close ')' $ dact onClose]
    , entry PIfV   $ spaced [step (like "then") $ dact onThen]
    , entry PThenV $ spaced [step (like "else") $ dact onElse]
    ]

atms : List String
atms = ["true", "false", "0", "("]

values : List String
values = ["if", "succ", "pred", "iszero"] ++ atms

perr : Arr32 PSz (SK q -> F1 q ArErr)
perr =
  arr32 PSz (unexpected values)
    [ entry PIfV   $ unexpected ["then"]
    , entry PThenV $ unexpected ["else"]
    , entry PCls   $ unclosedIfEOI "(" [")"]
    , entry PSucc  $ unexpected atms
    , entry PPred  $ unexpected atms
    , entry PIsZ   $ unexpected atms
    ]

peoi : Index PSz -> SK q -> F1 q (Either ArErr Term)
peoi st sk t =
 let ([<x]:>PTerm) # t := read1 sk.stack_ t | _ # t => arrFail SK perr st sk t
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
term = P (cast PIni) (init $ [<]:>PIni) ptrans (\x => (Nothing #)) perr peoi

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
