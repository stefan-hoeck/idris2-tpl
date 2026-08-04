module TPL.Lambda.Typed.Term

import Derive.Prelude
import public TPL.Lambda.Typed.Syntax

%default total
%language ElabReflection

||| Desugared terms
public export
data Term : Type where
  ||| Variables
  TVar   : ByteBounds -> (v : VarName) -> Term

  ||| Type annotations
  TAs   : ByteBounds -> (t : Term) -> (tp : RawTpe) -> Term

  ||| Record field projection
  TField : ByteBounds -> Term -> ByteBounded VarName -> Term

  ||| Abstraction: A bound variable, its type, and its scope
  TLam   : ByteBounds -> (v : BindName) -> (t : RawTpe) -> (sc : Term) -> Term

  ||| Let binding
  TLet   : ByteBounds -> (v : BindName) -> (x : Term) -> (sc : Term) -> Term

  ||| Recursive let binding
  TLetrec :
       ByteBounds
    -> (v : BindName)
    -> (t : RawTpe)
    -> (x : Term)
    -> (sc : Term)
    -> Term

  ||| Function application
  TApp   : ByteBounds -> (t,s : Term) -> Term

  ||| Primitive values
  TPrim  : ByteBounds -> Prim -> Term

  ||| record constructor
  TRec   : ByteBounds -> List (VarName, Term) -> Term

  ||| record constructor
  TSum   : ByteBounds -> ByteBounded VarName -> Term -> Term

  ||| `if ... then ... else` function. Eventually, this could be
  ||| desugared into a pattern match on bools.
  TIf    : ByteBounds -> (i,t,e : Term) -> Term

  ||| `case ... of` expressions.
  TCase  : ByteBounds -> Term -> List (ByteBounded VarName, BindName, Term) -> Term

%runElab derive "Term" [Show,Eq]

export
FromString Term where
  fromString s = TVar NoBB (fromString s)

export
Cast Term ByteBounds where
  cast (TVar b _)          = b
  cast (TAs b _ _)         = b
  cast (TField b _ _)      = b
  cast (TLam b _ _ _)      = b
  cast (TLet b _ _ _)      = b
  cast (TLetrec b _ _ _ _) = b
  cast (TApp b _ _)        = b
  cast (TPrim b _)         = b
  cast (TRec b _)          = b
  cast (TSum b _ _)        = b
  cast (TIf b _ _ _)       = b
  cast (TCase b _ _)       = b

unpats :
     SnocList (BindName,Term)
  -> Nat
  -> List (ByteBounded VarName,Pattern)
  -> Term
  -> (Nat, List (BindName, Term))

unpat : Nat -> Pattern -> Term -> (Nat, List (BindName, Term))
unpat n (PV x)  t = (n, [(x,t)])
unpat n (PT xs) t =
 let vn     := machineName n
     (r,ps) := unpats [<] (S n) xs (TVar NoBB vn)
  in (r, (NM vn, t) :: ps)

unpats sp n []           t = (n, sp <>> [])
unpats sp n ((vn,p)::ps) t =
 let fn := TField NoBB t vn
     (n2,xs) := unpat n p fn
  in unpats (sp<><xs) n2 ps t

unpatLet : ByteBounds -> List (BindName,Term) -> Term -> Term
unpatLet bb []             x = x
unpatLet bb ((bn,t) :: ps) x = TLet bb bn t (unpatLet NoBB ps x)

desugarRec : List (VarName,PTerm) -> List (VarName,Term)

desugarCase :
     List (ByteBounded VarName,Pattern,PTerm)
  -> List (ByteBounded VarName,BindName,Term)

export
desugar : PTerm -> Term
desugar (PVar b v)           = TVar b v
desugar (PAs b t tp)         = TAs b (desugar t) tp
desugar (PField b y v)       = TField b (desugar y) v
desugar (PLam b (PV x) t sc) = TLam b x t (desugar sc)
desugar (PLam b p t sc)      =
 let v      := machineName 0
     (_,ps) := unpat 1 p (TVar NoBB v)
  in TLam b (NM v) t (unpatLet NoBB ps (desugar sc))
desugar (PLet b (PV x) y sc) = TLet b x (desugar y) (desugar sc)
desugar (PLet b p y sc)      =
 let (_,ps) := unpat 0 p (desugar y)
  in unpatLet b ps (desugar sc)
desugar (PLetrec b v t y sc) = TLetrec b v t (desugar y) (desugar sc)
desugar (PApp b t s)         = TApp b (desugar t) (desugar s)
desugar (PPrim b y)          = TPrim b y
desugar (PRec b xs)          = TRec b (desugarRec xs)
desugar (PSum b v t)         = TSum b v (desugar t)
desugar (PIf b i t e)        = TIf b (desugar i) (desugar t) (desugar e)
desugar (PCase b t ts)       = TCase b (desugar t) (desugarCase ts)

desugarRec [] = []
desugarRec ((v,t)::ps) = (v,desugar t) :: desugarRec ps

desugarCase [] = []
desugarCase ((v,PV b,t)::ts) = (v,b,desugar t) :: desugarCase ts
desugarCase ((v,p,t)::ts)    =
 let n      := machineName 0
     (_,ps) := unpat 1 p (TVar NoBB n)
  in (v,cast n,unpatLet NoBB ps (desugar t)) :: desugarCase ts

resugarRec : List (VarName,Term) -> List (VarName,PTerm)

resugarCase :
     List (ByteBounded VarName, BindName, Term)
  -> List (ByteBounded VarName, Pattern, PTerm)

export
resugar : Term -> PTerm
resugar (TVar b v)           = PVar b v
resugar (TAs b t tp)         = PAs b (resugar t) tp
resugar (TField b y v)       = PField b (resugar y) v
resugar (TLam b v t sc)      = PLam b (PV v) t (resugar sc)
resugar (TLet b p y sc)      = PLet b (PV p) (resugar y) (resugar sc)
resugar (TLetrec b v t y sc) = PLetrec b v t (resugar y) (resugar sc)
resugar (TApp b t s)         = PApp b (resugar t) (resugar s)
resugar (TPrim b y)          = PPrim b y
resugar (TRec b xs)          = PRec b (resugarRec xs)
resugar (TSum b v t)         = PSum b v (resugar t)
resugar (TIf b i t e)        = PIf b (resugar i) (resugar t) (resugar e)
resugar (TCase b t ts)       = PCase b (resugar t) (resugarCase ts)

resugarRec [] = []
resugarRec ((v,t)::ps) = (v,resugar t) :: resugarRec ps

resugarCase [] = []
resugarCase ((v,b,t)::ts) = (v,cast b, resugar t) :: resugarCase ts
