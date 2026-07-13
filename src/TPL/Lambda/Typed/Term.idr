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

  ||| `if ... then ... else` function. Eventually, this could be
  ||| desugared into a pattern match on bools.
  TIf    : ByteBounds -> (i,t,e : Term) -> Term

%runElab derive "Term" [Show,Eq]

export
FromString Term where
  fromString s = TVar NoBB (fromString s)

export
Cast Term ByteBounds where
  cast (TVar b _)          = b
  cast (TField b _ _)      = b
  cast (TLam b _ _ _)      = b
  cast (TLet b _ _ _)      = b
  cast (TLetrec b _ _ _ _) = b
  cast (TApp b _ _)        = b
  cast (TPrim b _)         = b
  cast (TRec b _)          = b
  cast (TIf b _ _ _)       = b

desugarRec : List (VarName,PTerm) -> List (VarName,Term)

export
desugar : PTerm -> Term
desugar (PVar b v)           = TVar b v
desugar (PField b y v)       = TField b (desugar y) v
desugar (PLam b v t sc)      = TLam b v t (desugar sc)
desugar (PLet b v y sc)      = TLet b v (desugar y) (desugar sc)
desugar (PLetrec b v t y sc) = TLetrec b v t (desugar y) (desugar sc)
desugar (PApp b t s)         = TApp b (desugar t) (desugar s)
desugar (PPrim b y)          = TPrim b y
desugar (PRec b xs)          = TRec b (desugarRec xs)
desugar (PIf b i t e)        = TIf b (desugar i) (desugar t) (desugar e)

desugarRec [] = []
desugarRec ((v,t)::ps) = (v,desugar t) :: desugarRec ps

resugarRec : List (VarName,Term) -> List (VarName,PTerm)

export
resugar : Term -> PTerm
resugar (TVar b v)           = PVar b v
resugar (TField b y v)       = PField b (resugar y) v
resugar (TLam b v t sc)      = PLam b v t (resugar sc)
resugar (TLet b v y sc)      = PLet b v (resugar y) (resugar sc)
resugar (TLetrec b v t y sc) = PLetrec b v t (resugar y) (resugar sc)
resugar (TApp b t s)         = PApp b (resugar t) (resugar s)
resugar (TPrim b y)          = PPrim b y
resugar (TRec b xs)          = PRec b (resugarRec xs)
resugar (TIf b i t e)        = PIf b (resugar i) (resugar t) (resugar e)

resugarRec [] = []
resugarRec ((v,t)::ps) = (v,resugar t) :: resugarRec ps
