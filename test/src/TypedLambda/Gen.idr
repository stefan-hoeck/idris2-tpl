module TypedLambda.Gen

import public Data.Vect
import public Hedgehog
import public TPL.Lambda.Typed.Declaration
import public TPL.Lambda.Typed.Syntax
import public Text.ByteBounds

%default total

export
bb : Gen ByteBounds
bb = pure NoBB

export
bounded : Gen a -> Gen (ByteBounded a)
bounded = map pure

export
identchar : Gen Char
identchar = frequency [(10,alphaNum),(1, element ['_', '\''])]

notKeyword : String -> VarName
notKeyword "if"     = "if_"
notKeyword "then"   = "then_"
notKeyword "else"   = "else_"
notKeyword "let"    = "let_"
notKeyword "letrec" = "letrec_"
notKeyword "in"     = "in_"
notKeyword s        = VN s

export
varname : Gen VarName
varname = (notKeyword . fastPack) <$> [| alpha :: list (linear 0 6) identchar |]

export
bindname : Gen BindName
bindname =
  frequency
    [ (1, pure PH)
    , (10, map NM varname)
    ]

export
pattern : Gen Pattern
pattern = PV <$> bindname

export
tpename : Gen VarName
tpename = (VN . fastPack) <$> [| upper :: list (linear 0 6) identchar |]

export
tpeVar : Gen RawTpe
tpeVar =
  frequency
    [ (1, PVar NoBB <$> element ["Nat", "Bool", "Unit"])
    , (1, PVar NoBB <$> tpename)
    ]

export
tpe : Gen RawTpe
tpe = go 5
  where
    go : Nat -> Gen RawTpe

    recType : Nat -> Gen RawTpe
    recType k = PRec NoBB <$> list (linear 1 5) [| (varname, go k) |]

    go 0 = tpeVar
    go (S k) =
      frequency
        [ (1,tpeVar)
        , (2,[| PFun bb (go k) (go k) |])
        , (2,recType k)
        ]

export
prim : Gen PTerm
prim =
  frequency
    [ (1, pure (PPrim NoBB PUnit))
    , (1, (PPrim NoBB . PBool) <$> bool)
    , (3, (PPrim NoBB . PNat) <$> nat (linear 0 100))
    , (3, PVar NoBB <$> varname)
    ]

export
term : Gen PTerm
term = go 5
  where
    go : Nat -> Gen PTerm

    rec : Nat -> Gen PTerm
    rec k = PRec NoBB <$> list (linear 1 5) [| (varname, go k) |]

    go 0     = prim
    go (S k) =
      frequency
        [ (1, prim)
        , (2, [| PApp bb (go k) (go k) |])
        , (2, [| PIf  bb (go k) (go k) (go k) |])
        , (2, [| PLam bb bindname tpe (go k) |])
        , (2, [| PLet bb pattern (go k) (go k) |])
        , (2, [| PLetrec bb bindname tpe (go k) (go k) |])
        , (2, [| PField bb (go k) (bounded varname) |])
        , (2, rec k)
        ]

export
aliases : Gen Declaration
aliases = [| Alias bb tpename tpe |]

export
decl : Gen Declaration
decl = [| Decl bb varname tpe |]

export
defn : Gen Declaration
defn = [| Defn bb varname term |]

export
eval : Gen Declaration
eval = [| Eval term |]
