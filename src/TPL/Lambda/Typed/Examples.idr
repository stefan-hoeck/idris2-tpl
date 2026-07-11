module TPL.Lambda.Typed.Examples

import Text.ILex
import TPL.Lambda.Typed.Eval
import TPL.Lambda.Typed.Parser

%default total

%inline
lamx : (t1 : Tpe) -> STerm t2 [<V "x" t1] -> STerm (TFun t1 t2) [<]
lamx = SLam NoBB "x"

%inline
varx : (t1 : Tpe) -> STerm t1 [<V "x" t1]
varx t1 = SVar NoBB nzero

succDef : Entry
succDef = Def _ (lamx TNat $ SSucc NoBB $ varx TNat)

predDef : Entry
predDef = Def _ (lamx TNat $ SPred NoBB $ varx TNat)

iszeroDef : Entry
iszeroDef = Def _ (lamx TNat $ SIsZ NoBB $ varx TNat)

predef : Env Entry
predef =
  fromList
    [ ("succ",   succDef)
    , ("pred",   predDef)
    , ("iszero", iszeroDef)
    , ("Nat",    Als TNat)
    , ("Bool",   Als TBool)
    , ("Unit",   Als TUnit)
    ]

covering
process : Env Entry -> Declaration -> Either LamErr (Env Entry, Maybe String)
process env (Decl bb nm tpe) =
  case lookup nm env of
    Just _  => defined bb nm
    Nothing => (\t => (insert nm (Dec t) env, Nothing)) <$> resolveTpe env tpe
process env (Alias bb nm tpe) =
  case lookup nm env of
    Just _  => defined bb nm
    Nothing => (\t => (insert nm (Als t) env, Nothing)) <$> resolveTpe env tpe
process env (Defn bb nm trm) =
  case lookup nm env of
    Just (Dec t)  =>
      map
        (\v => (insert nm (Def t v) env, Nothing))
        (typecheckAs {sc = [<]} env t trm)
    Just _   => defined bb nm
    Nothing  => unknown bb nm
process env (Eval x)   =
  map
    (\(t ** v) => (env, Just "Type: \{t}, Value: \{eval [<] v}"))
    (typecheck {sc = [<]} env x)

covering
processIO : IORef (Env Entry) -> String -> Declaration -> IO ()
processIO ref s decl = Prelude.do
  env <- readref ref
  case process env decl of
    Left x           => putStrLn "\{toParseError Virtual s x}"
    Right (env2,res) => writeref ref env2 >> traverse_ putStrLn res

example : String
example =
  """
  %alias NatFun : Nat -> Nat;
  %alias ChurchNat : NatFun -> NatFun;

  c0 : ChurchNat;
  c0 = λs : NatFun . λz : Nat . z;

  c1 : ChurchNat;
  c1 = λs : NatFun . λz : Nat . s z;

  c2 : ChurchNat;
  c2 = λs : NatFun . λz : Nat . s (c1 s z);

  plus : Nat -> Nat -> Nat;
  plus =
    fix
      ( λrec : Nat -> Nat -> Nat
      . λm   : Nat
      . λn   : Nat
      . if iszero m then n else rec (pred m) (succ n)
      );

  times : Nat -> Nat -> Nat;
  times =
    fix
      ( λrec : Nat -> Nat -> Nat
      . λm   : Nat
      . λn   : Nat
      . if iszero m then 0 else plus n (rec (pred m) n)
      );

  factorial : Nat -> Nat;
  factorial =
    fix
      ( λrec : Nat->Nat
      . λn   : Nat
      . if iszero n then 1 else times (rec (pred n)) n
      );

  %alias EvenOdd : {iseven : Nat -> Bool, isodd : Nat -> Bool};

  evenOdd : EvenOdd;
  evenOdd =
    fix
      ( λio : EvenOdd
      . { iseven = λn: Nat . if iszero n then True  else io.isodd  (pred n)
        , isodd  = λn: Nat . if iszero n then False else io.iseven (pred n)
        }
      );

  %alias BoolNat : {bool: Bool, nat: Nat};
  %alias Complex : {fst: Nat, snd: BoolNat};

  %eval (unit;unit;unit;(λ_:Nat . unit) 12; 20);
  %eval c2 succ 0;
  %eval c2 succ 4;
  %eval plus 100 200;
  %eval times 200 200;
  %eval factorial (times 3 3);
  %eval (λ_: Nat. λx: Nat. x) 12 13;
  %eval
    (λx: Complex . {fact = x.snd.nat, strict = x.snd.bool})
      { fst = 0
      , snd =
          { bool = iszero 3
          , nat = factorial 4
          }
      };
  %eval evenOdd.isodd {fst = factorial 5, snd = False}.fst;
  """

unclosedTypeParen : String
unclosedTypeParen =
  """
  %alias Foo : ((Nat -> Nat) -> Nat;
  """

unclosedTypeBrace : String
unclosedTypeBrace =
  """
  foo : {foo : Nat ;
  """

unclosedValBrace : String
unclosedValBrace =
  """
  foo : {foo: Nat, bar : Bool};
  foo = {foo = 12, bar = True
  """

covering
testRun : String -> IO ()
testRun s = Prelude.do
  ref <- newref predef
  case parseString decls Virtual s of
    Left x   => putStrLn "\{x}"
    Right ds => traverse_ (processIO ref s) ds
