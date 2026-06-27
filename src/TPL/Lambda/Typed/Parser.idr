module TPL.Lambda.Typed.Parser

import Derive.Prelude
import Syntax.T1
import TPL.Parser.Util
import public TPL.Lambda.Typed.Term

%default total
%hide Data.Linear.(.)
%hide Language.Reflection.Types.PLam
%hide Language.Reflection.Types.PApp
%language ElabReflection

--------------------------------------------------------------------------------
-- Parser Stack
--------------------------------------------------------------------------------

data PState : SnocList Type -> Type where
  PApp   : PState [<]
  PAppT  : PState [<Term,SnocList Term]
  POpn   : PState [<]
  PLam   : PState [<ByteBounds]
  PLamV  : PState [<ByteBounds,VarName]
  PLamT  : PState [<ByteBounds,VarName,Tpe]
  PIf    : PState [<ByteBounds]
  PThen  : PState [<ByteBounds,Term]
  PElse  : PState [<ByteBounds,Term,Term]
  PTpe   : PState [<]
  PTpeT  : PState [<SnocList Tpe,Tpe]
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
  onTerm s PApp  sx       t = dput PAppT (sx:<s:<[<]) t
  onTerm s PAppT (sx:<ss) t = dput PAppT (sx:<(ss:<s)) t
  onTerm s st sx          t = derr PErr sx st t

  onCloseT : Term -> StateAct q PState PSz
  onCloseT trm POpn  (sx:>st)          t = onTerm trm st sx t
  onCloseT trm PApp  (sx:>st)          t = onCloseT trm st sx t
  onCloseT trm PAppT (sx:>st:<s:<ss)   t = onCloseT (appAllSnoc s ss) st sx t
  onCloseT trm PLamT (sx:>st:<b:<v:<p) t = onCloseT (TLam b v p trm) st sx t
  onCloseT trm PElse (sx:>st:<b:<x:<y) t = onCloseT (TIf b x y trm) st sx t
  onCloseT trm st    sx                t = derr PErr sx st t

  onTpe : Tpe -> StateAct q PState PSz
  onTpe tpe PTpe  sx          t = dput PTpeT (sx:<[<]:<tpe) t
  onTpe tpe PTpeT (sx:<ss:<s) t = dput PTpeT (sx:<(ss:<s):<tpe) t
  onTpe tpe st    sx          t = derr PErr sx st t

  onCloseTpe : Tpe -> StateAct q PState PSz
  onCloseTpe tpe POpn  (sx:>st)        t = onTpe tpe st sx t
  onCloseTpe tpe PTpe  (sx:>st)        t = onCloseTpe tpe st sx t
  onCloseTpe tpe PTpeT (sx:>st:<ss:<s) t = onCloseTpe (tpeAppAll (ss:<s) tpe) st sx t
  onCloseTpe tpe st    sx              t = derr PErr sx st t

  onClose : StateAct q PState PSz
  onClose PAppT (sx:>st:<s:<ss) t = onCloseT (appAllSnoc s ss) st sx t
  onClose PTpeT (sx:>st:<ss:<s) t = onCloseTpe (tpeAppAll ss s) st sx t
  onClose st    sx              t = derr PErr sx st t

  onDot : StateAct q PState PSz
  onDot PTpeT (sx:>PLamV:<ss:<s) t = dput PApp (sx:<(tpeAppAll ss s):>PLamT) t
  onDot st    sx                 t = derr PErr sx st t

  onIf : ByteBounds -> StateAct q PState PSz
  onIf b PApp  sx t = dput PApp (sx:>PApp:<b:>PIf) t
  onIf b PLamT sx t = dput PApp (sx:>PLamT:<b:>PIf) t
  onIf b POpn  sx t = dput PApp (sx:>POpn:<b:>PIf) t
  onIf b st    sx t = derr PErr sx st t

  onThen : StateAct q PState PSz
  onThen PAppT (sx:>PIf:<s:<ss) t = dput PApp (sx:<appAllSnoc s ss:>PThen) t
  onThen st    sx               t = derr PErr sx st t

  onElse : StateAct q PState PSz
  onElse PAppT (sx:>PThen:<s:<ss) t = dput PApp (sx:<appAllSnoc s ss:>PElse) t
  onElse st    sx                 t = derr PErr sx st t

  onVar : ByteBounded VarName -> StateAct q PState PSz
  onVar v st sx t =
    case v.val.name of
      "if"   => onIf v.bounds st sx t
      "then" => onThen st sx t
      "else" => onElse st sx t
      _      => case st of
        PLam => dput PLamV (sx:<v.val) t
        _    => onTerm (TVar v.bounds v.val) st sx t

atoms : Steps q PSz SK
atoms =
     opn '(' (getStack >>= \st => dput PApp (st:>POpn))
  :: bools (\b => bounded' b >>= dact . onTerm . bool)
  ++ nats  (\b => bounded' b >>= dact . onTerm . int)
  ++ varName (\b => bounded' b >>= dact . onVar)

terms : DFA q PSz SK
terms = spaced $ step ('\\' <|> 'λ') (bounds >>= dpush PLam) :: atoms

atomOrClose : DFA q PSz SK
atomOrClose = spaced $ close ')' (dact onClose) :: atoms

types : DFA q PSz SK
types =
  spaced
    [ step "Nat" (dact $ onTpe TNat)
    , step "Bool" (dact $ onTpe TBool)
    , opn "(" (getStack >>= \st => dput PTpe (st:>POpn))
    ]

ptrans : Lex1 q PSz SK
ptrans =
  lex1
    [ entry PApp     terms
    , entry PAppT    atomOrClose
    , entry PLam   $ spaced (varName $ \b => bounded' b >>= dact . onVar)
    , entry PLamV  $ spaced [step ':' $ dpush0 PTpe]
    , entry PTpe     types
    , entry PTpeT  $ spaced [step '.' $ dact onDot, step' "->" PTpe]
    ]

perr : Arr32 PSz (SK q -> F1 q LamErr)
perr = arr32 PSz (unclosedIfEOI "(" []) []

reduceT : Stack b PState [<] -> Term -> Maybe Term
reduceT [<]                  t = Just t
reduceT (st:>PApp)           t = reduceT st t
reduceT (st:<s:<ss:>PAppT)   t = reduceT st (appAllSnoc s $ ss:<t)
reduceT (sx:<b:<v:<p:>PLamT) t = reduceT sx (TLam b v p t)
reduceT (sx:<b:<x:<y:>PElse) t = reduceT sx (TIf b x y t)
reduceT _                    _ = Nothing

reduce : Stack b PState [<] -> Maybe Term
reduce (sx:<s:<ss:>PAppT) = reduceT sx (appAllSnoc s ss)
reduce _                  = Nothing

peoi : Index PSz -> SK q -> F1 q (Either LamErr Term)
peoi st sk t =
 let sx # t := read1 sk.stack_ t
  in case reduce sx of
       Just s  => Right s # t
       Nothing => arrFail SK perr st sk t

public export
term : P1 q LamErr Term
term = P (cast PApp) (init $ [<]:>PApp) ptrans (\x => (Nothing #)) perr peoi

--------------------------------------------------------------------------------
-- Proofs
--------------------------------------------------------------------------------

inBoundsPState PApp   = Refl
inBoundsPState PAppT  = Refl
inBoundsPState POpn   = Refl
inBoundsPState PLam   = Refl
inBoundsPState PLamV  = Refl
inBoundsPState PLamT  = Refl
inBoundsPState PIf    = Refl
inBoundsPState PThen  = Refl
inBoundsPState PElse  = Refl
inBoundsPState PTpe   = Refl
inBoundsPState PTpeT  = Refl
inBoundsPState PErr   = Refl
