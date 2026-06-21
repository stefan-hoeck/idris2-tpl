module TPL.Lambda.Parser

import Derive.Prelude
import TPL.Parser.Util
import public TPL.Lambda.Term

%default total
%hide Data.Linear.(.)
%hide Language.Reflection.Types.PLam
%language ElabReflection

--------------------------------------------------------------------------------
-- Parser Stack
--------------------------------------------------------------------------------

data PState : SnocList Type -> Type where
  PIni   : PState [<]
  PIniT  : PState [<Term,SnocList Term]
  POpn   : PState [<]
  POpnT  : PState [<Term,SnocList Term]
  PLam   : PState [<]
  PLamV  : PState [<VarName]
  PLamD  : PState [<Void]
  PLamT  : PState [<VarName,Term,SnocList Term]
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
  onTerm s PIni [<]       t = dput PIniT [<s,[<]] t
  onTerm s PIniT (sx:<ss) t = dput PIniT (sx:<(ss:<s)) t
  onTerm s POpn sx        t = dput POpnT (sx:<s:<[<]) t
  onTerm s POpnT (sx:<ss) t = dput POpnT (sx:<(ss:<s)) t
  onTerm s PLamV sx       t = dput PLamT (sx:<s:<[<]) t
  onTerm s PLamT (sx:<ss) t = dput PLamT (sx:<(ss:<s)) t
  onTerm s st sx          t = derr PErr sx st t

  onVar : VarName -> StateAct q PState PSz
  onVar v PLam sx t = dput PLamV (sx:<v) t
  onVar v st   sx t = onTerm (TVar v) st sx t

  onCloseT : Term -> StateAct q PState PSz
  onCloseT trm POpn (sx:>st)     t = onTerm trm st sx t
  onCloseT trm PLamV (sx:>st:<v) t = onCloseT (TLam v trm) st sx t
  onCloseT trm POpnT (sx:>st:<s:<ss) t =
    onTerm (appAllSnoc s $ ss:<trm) st sx t
  onCloseT trm PLamT (sx:>st:<v:<s:<ss) t =
    onCloseT (TLam v $ appAllSnoc s $ ss :< trm) st sx t
  onCloseT trm st    sx                 t = derr PErr sx st t

  onClose : StateAct q PState PSz
  onClose POpnT (sx:>st:<s:<ss)    t = onTerm (appAllSnoc s ss) st sx t
  onClose PLamT (sx:>st:<v:<s:<ss) t =
    onCloseT (TLam v $ appAllSnoc s ss) st sx t
  onClose st    sx                 t = derr PErr sx st t

atoms : Steps q PSz SK
atoms = opn '(' (dpush0 POpn) :: (varName $ dact . onVar)

terms : DFA q PSz SK
terms = spaced $ step ('\\' <|> 'λ') (dpush0 PLam) :: atoms

atomOrClose : DFA q PSz SK
atomOrClose = spaced $ close ')' (dact onClose) :: atoms

ptrans : Lex1 q PSz SK
ptrans =
  lex1
    [ entry PIni     terms
    , entry PIniT    atomOrClose
    , entry POpn     terms
    , entry POpnT  $ atomOrClose
    , entry PLam   $ spaced (varName $ dact . onVar)
    , entry PLamV  $ spaced [step' '.' PLamD]
    , entry PLamD    terms
    , entry PLamT  $ atomOrClose
    ]

perr : Arr32 PSz (SK q -> F1 q (BBErr Void))
perr =
  arr32 PSz (unexpected [])
    [ entry POpnT  $ unclosedIfEOI "(" [")"]
    , entry PLamV  $ unexpected ["."]
    ]

reduceT : Stack b PState [<] -> Term -> Maybe Term
reduceT ([<]:>PIni)           t = Just t
reduceT ([<s,ss]:>PIniT)      t = Just (appAllSnoc s $ ss:<t)
reduceT (sx:<v:>PLamV)        t = reduceT sx (TLam v t)
reduceT (sx:<v:<s:<ss:>PLamT) t = reduceT sx (TLam v (appAllSnoc s $ ss:<t))
reduceT _                     _ = Nothing

reduce : Stack b PState [<] -> Maybe Term
reduce ([<s,ss]:>PIniT)      = Just (appAllSnoc s ss)
reduce (sx:<v:<s:<ss:>PLamT) = reduceT sx (TLam v $ appAllSnoc s ss)
reduce _                     = Nothing

peoi : Index PSz -> SK q -> F1 q (Either (BBErr Void) Term)
peoi st sk t =
 let sx # t := read1 sk.stack_ t
  in case reduce sx of
       Just s  => Right s # t
       Nothing => arrFail SK perr st sk t

public export
term : P1 q (BBErr Void) Term
term = P (cast PIni) (init $ [<]:>PIni) ptrans (\x => (Nothing #)) perr peoi

example : String
example =
  """
  """

export
testParse : String -> IO ()
testParse =
  putStrLn . either interpolate interpolate . parseString term Virtual

export
testScoped : String -> IO ()
testScoped s =
  case parseString term Virtual s of
    Left x  => putStrLn "\{x}"
    Right t => case closed t of
      Nothing => putStrLn "variable not in scope"
      Just st => putStrLn "\{st}"

--------------------------------------------------------------------------------
-- Proofs
--------------------------------------------------------------------------------

inBoundsPState PIni   = Refl
inBoundsPState PIniT  = Refl
inBoundsPState POpn   = Refl
inBoundsPState POpnT  = Refl
inBoundsPState PLam   = Refl
inBoundsPState PLamV  = Refl
inBoundsPState PLamD  = Refl
inBoundsPState PLamT  = Refl
inBoundsPState PErr   = Refl
