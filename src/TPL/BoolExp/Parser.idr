module TPL.BoolExp.Parser

import Derive.Prelude
import TPL.Parser.Util
import public TPL.BoolExp.Term

%default total
%language ElabReflection

--------------------------------------------------------------------------------
-- Parser Stack
--------------------------------------------------------------------------------

data PState : SnocList Type -> Type where
  PIni   : PState [<]
  POpn   : PState [<]
  PCls   : PState [<Term]
  PIf    : PState [<]
  PIfV   : PState [<Term]
  PThen  : PState [<Term]
  PThenV : PState [<Term,Term]
  PElse  : PState [<Term,Term]
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
SK = DStack PState Void

parameters {auto sk : SK q}
  onTerm : Term -> StateAct q PState PSz
  onTerm trm POpn   sx              t = dput PCls (sx:<trm) t
  onTerm trm PIni   sx              t = dput PTerm [<trm] t
  onTerm trm PIf    sx              t = dput PIfV (sx:<trm) t
  onTerm trm PThen  sx              t = dput PThenV (sx:<trm) t
  onTerm trm PElse  [<x,y]          t = dput PTerm [<TIf x y trm] t
  onTerm trm PElse  (sx:>pst:<x:<y) t = onTerm (TIf x y trm) pst sx t
  onTerm trm st     sx              t = derr PErr sx st t

  onThen : StateAct q PState PSz
  onThen PIfV sx t = dput PThen sx t
  onThen st   sx t = derr PErr sx st t

  onElse : StateAct q PState PSz
  onElse PThenV sx t = dput PElse sx t
  onElse st     sx t = derr PErr sx st t

  onClose : StateAct q PState PSz
  onClose PCls (sx:>st:<v) t = onTerm v st sx t
  onClose st   sx          t = derr PErr sx st t

value : DFA q PSz SK
value =
  spaced
    [ step "true"  (dact $ onTerm (bool True))
    , step "false" (dact $ onTerm (bool False))
    , step "if" (dpush0 PIf)
    , opn '(' (dpush0 POpn)
    ]

ptrans : Lex1 q PSz SK
ptrans =
  lex1
    [ entry PIni   $ value
    , entry POpn   $ value
    , entry PIf    $ value
    , entry PThen  $ value
    , entry PElse  $ value
    , entry PCls   $ spaced [close ')' $ dact onClose]
    , entry PIfV   $ spaced [step "then" $ dact onThen]
    , entry PThenV $ spaced [step "else" $ dact onElse]
    ]

perr : Arr32 PSz (SK q -> F1 q (BBErr Void))
perr =
  errs
    [ entry PIni   $ unexpected ["if", "true", "false", "("]
    , entry POpn   $ unexpected ["if", "true", "false", "("]
    , entry PIf    $ unexpected ["if", "true", "false", "("]
    , entry PThen  $ unexpected ["if", "true", "false", "("]
    , entry PElse  $ unexpected ["if", "true", "false", "("]
    , entry PIfV   $ unexpected ["then"]
    , entry PThenV $ unexpected ["else"]
    , entry PCls   $ unclosedIfEOI "(" [")"]
    ]

peoi : Index PSz -> SK q -> F1 q (Either (BBErr Void) Term)
peoi st sk t =
 let ([<x]:>PTerm) # t := read1 sk.stack_ t | _ # t => arrFail SK perr st sk t
  in Right x # t

public export
term : P1 q (BBErr Void) Term
term = P (cast PIni) (init $ [<]:>PIni) ptrans (\x => (Nothing #)) perr peoi

example : String
example =
  """
  if true
     then (if false then true else false)
     else (if false then false else true)
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
inBoundsPState PCls   = Refl
inBoundsPState PIf    = Refl
inBoundsPState PIfV   = Refl
inBoundsPState PThen  = Refl
inBoundsPState PThenV = Refl
inBoundsPState PElse  = Refl
inBoundsPState PTerm  = Refl
inBoundsPState PErr   = Refl
