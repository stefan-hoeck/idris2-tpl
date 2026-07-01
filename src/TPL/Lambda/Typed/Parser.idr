module TPL.Lambda.Typed.Parser

import Derive.Prelude
import Syntax.T1
import TPL.Parser.Util
import public TPL.Lambda.Typed.Declaration

%default total
%hide Data.Linear.(.)
%hide Language.Reflection.Types.PLam
%hide Language.Reflection.Types.PApp
%language ElabReflection

--------------------------------------------------------------------------------
-- Parser Stack
--------------------------------------------------------------------------------

data PState : SnocList Type -> Type where
  PIni   : PState [<SnocList Declaration]
  PIniN  : PState [<SnocList Declaration,ByteBounds,VarName]
  PEval  : PState [<SnocList Declaration]
  PApp   : PState [<]
  PAppT  : PState [<Term,SnocList Term]
  POpn   : PState [<]
  PLam   : PState [<ByteBounds]
  PLamV  : PState [<ByteBounds,BindName]
  PLamT  : PState [<ByteBounds,BindName,ByteBounded Tpe]
  PIf    : PState [<ByteBounds]
  PThen  : PState [<ByteBounds,Term]
  PElse  : PState [<ByteBounds,Term,Term]
  PTpe   : PState [<]
  PTpeT  : PState [<SnocList (ByteBounded Tpe), ByteBounded Tpe]
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
  onEndTerm : Term -> StateAct q PState PSz
  onEndTerm trm PIniN (sx:<sd:<b:<v)     t = dput PIni (sx:<(sd:<Defn b v trm)) t
  onEndTerm trm PEval (sx:<sd)           t = dput PIni (sx:<(sd:<Eval trm)) t
  onEndTerm trm PApp  (sx:>st)           t = onEndTerm trm st sx t
  onEndTerm trm PAppT (sx:>st:<s:<ss)    t = onEndTerm (appAllSnoc s ss) st sx t
  onEndTerm trm PLamT (sx:>st:<b:<v:<bt) t = onEndTerm (TLam b v bt trm) st sx t
  onEndTerm trm PElse (sx:>st:<b:<x:<y)  t = onEndTerm (TIf b x y trm) st sx t
  onEndTerm trm st    sx                 t = derr PErr sx st t

  onEndTpe : ByteBounded Tpe -> StateAct q PState PSz
  onEndTpe tpe PIniN (sx:<sd:<b:<v)  t = dput PIni (sx:<(sd:<Decl b v tpe.val)) t
  onEndTpe tpe PTpe  (sx:>st)        t = onEndTpe tpe st sx t
  onEndTpe tpe PTpeT (sx:>st:<ss:<s) t = onEndTpe (tpeAppAll (ss:<s) tpe) st sx t
  onEndTpe _   st    sx              t = derr PErr sx st t

  onEnd : StateAct q PState PSz
  onEnd PTpeT (sx:>st:<ss:<s) t = onEndTpe (tpeAppAll ss s) st sx t
  onEnd PAppT (sx:>st:<s:<ss) t = onEndTerm (appAllSnoc s ss) st sx t
  onEnd st    sx              t = derr PErr sx st t

  onTerm : Term -> StateAct q PState PSz
  onTerm s PApp  sx       t = dput PAppT (sx:<s:<[<]) t
  onTerm s PAppT (sx:<ss) t = dput PAppT (sx:<(ss:<s)) t
  onTerm s st sx          t = derr PErr sx st t

  onCloseT : Term -> StateAct q PState PSz
  onCloseT trm POpn  (sx:>st)           t = onTerm trm st sx t
  onCloseT trm PApp  (sx:>st)           t = onCloseT trm st sx t
  onCloseT trm PAppT (sx:>st:<s:<ss)    t = onCloseT (appAllSnoc s ss) st sx t
  onCloseT trm PLamT (sx:>st:<b:<v:<bt) t = onCloseT (TLam b v bt trm) st sx t
  onCloseT trm PElse (sx:>st:<b:<x:<y)  t = onCloseT (TIf b x y trm) st sx t
  onCloseT trm st    sx                 t = derr PErr sx st t

  onTpe : ByteBounded Tpe -> StateAct q PState PSz
  onTpe tpe PTpe  sx          t = dput PTpeT (sx:<[<]:<tpe) t
  onTpe tpe PTpeT (sx:<ss:<s) t = dput PTpeT (sx:<(ss:<s):<tpe) t
  onTpe tpe st    sx          t = derr PErr sx st t

  onCloseTpe : ByteBounded Tpe -> StateAct q PState PSz
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
  onDot PLamV sx                 t = dput PApp (sx:>PLamV) t
  onDot st    sx                 t = derr PErr sx st t

  onIf : ByteBounds -> StateAct q PState PSz
  onIf b PApp  sx t = dput PApp (sx:>PApp:<b:>PIf) t
  onIf b PLamV sx t = dput PApp (sx:>PLamV:<b:>PIf) t
  onIf b PLamT sx t = dput PApp (sx:>PLamT:<b:>PIf) t
  onIf b POpn  sx t = dput PApp (sx:>POpn:<b:>PIf) t
  onIf b st    sx t = derr PErr sx st t

  onThen : StateAct q PState PSz
  onThen PAppT (sx:>PIf:<s:<ss) t = dput PApp (sx:<appAllSnoc s ss:>PThen) t
  onThen st    sx               t = derr PErr sx st t

  onElse : StateAct q PState PSz
  onElse PAppT (sx:>PThen:<s:<ss) t = dput PApp (sx:<appAllSnoc s ss:>PElse) t
  onElse st    sx                 t = derr PErr sx st t

  onEval : StateAct q PState PSz
  onEval PIni sx t = dput PApp (sx:>PEval) t
  onEval st   sx t = derr PErr sx st t

  onVar : ByteBounded VarName -> StateAct q PState PSz
  onVar v st sx t =
    case v.val.name of
      "if"   => onIf v.bounds st sx t
      "then" => onThen st sx t
      "else" => onElse st sx t
      _      => case st of
        PLam => dput PLamV (sx:<NM v.val) t
        PIni => dput PIniN (sx:<v.bounds:<v.val) t
        _    => onTerm (TVar v.bounds v.val) st sx t

  placeholder : StateAct q PState PSz
  placeholder PLam sx t = dput PLamV (sx:<PH) t
  placeholder st   sx t = derr PErr sx st t

vars : Steps q PSz SK
vars = varName (\b => bounded' b >>= dact . onVar)

atoms : Steps q PSz SK
atoms =
     opn '(' (getStack >>= \st => dput PApp (st:>POpn))
  :: step "unit" (bounds >>= dact . onTerm . unit)
  :: bools (\b => bounded' b >>= dact . onTerm . bool)
  ++ nats  (\b => bounded' b >>= dact . onTerm . int)
  ++ vars

terms : DFA q PSz SK
terms = spaced $ step ('\\' <|> 'λ') (bounds >>= dpush PLam) :: atoms

atomOrClose : DFA q PSz SK
atomOrClose =
  spaced $ step ';' (dact onEnd) :: close ')' (dact onClose) :: atoms

types : DFA q PSz SK
types =
  spaced
    [ step "Nat"  (bounds >>= dact . onTpe . B TNat)
    , step "Bool" (bounds >>= dact . onTpe . B TBool)
    , step "Unit" (bounds >>= dact . onTpe . B TUnit)
    , opn "(" (getStack >>= \st => dput PTpe (st:>POpn))
    ]

afterType : DFA q PSz SK
afterType =
  spaced
    [ step ')' (dact onClose)
    , step '.' (dact onDot)
    , step ';' (dact onEnd)
    , step' "->" PTpe
    ]

ptrans : Lex1 q PSz SK
ptrans =
  lex1
    [ entry PIni   $ spaced $ step "%eval" (dact onEval) :: vars
    , entry PIniN  $ spaced [step '=' $ dpush0 PApp, step ':' $ dpush0 PTpe]
    , entry PApp     terms
    , entry PAppT    atomOrClose
    , entry PLam   $ spaced (step "_" (dact placeholder) :: vars)
    , entry PLamV  $ spaced [step ':' $ dpush0 PTpe]
    , entry PTpe     types
    , entry PTpeT    afterType
    ]

openParen : Stack b PState st -> Bool
openParen [<]         = False
openParen (x :> POpn) = True
openParen (x :> _)    = openParen x
openParen (x :< _)    = openParen x

lamErr : List String -> SK q -> F1 q LamErr
lamErr ss sk = T1.do
  st <- getStack
  case openParen st of
    True  => unclosedIfEOI "(" ss sk
    False => unexpected ss sk

perr : Arr32 PSz (SK q -> F1 q LamErr)
perr =
  arr32 PSz (lamErr [])
    [ entry PLamV $ lamErr [":"]
    , entry PTpe  $ lamErr ["Nat", "Bool", "("]
    , entry PTpeT $ lamErr ["->", ".", ")"]
    ]

peoi : Index PSz -> SK q -> F1 q (Either LamErr $ List Declaration)
peoi st sk t =
 let sx # t := read1 sk.stack_ t
  in case sx of
       [<sd]:>PIni => Right (sd <>> []) # t
       _           => arrFail SK perr st sk t

public export
decls : P1 q LamErr (List Declaration)
decls = P (cast PApp) (init $ [<[<]]:>PIni) ptrans (\x => (Nothing #)) perr peoi

--------------------------------------------------------------------------------
-- Proofs
--------------------------------------------------------------------------------

inBoundsPState PIni   = Refl
inBoundsPState PIniN  = Refl
inBoundsPState PEval  = Refl
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
