module TypedLambda.Gen

import public Data.Vect
import public Hedgehog
import public TPL.Lambda.Typed.Declaration
import public TPL.Lambda.Typed.Term
import public Text.ByteBounds

%default total

export
bb : Gen ByteBounds
bb = pure NoBB

export
identchar : Gen Char
identchar = frequency [(10,alphaNum),(1, element ['_', '\''])]

notKeyword : String -> VarName
notKeyword "if" = "if_"
notKeyword "then" = "then_"
notKeyword "else" = "else_"
notKeyword s      = VN s

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
    go 0 = tpeVar
    go (S k) = frequency [(1,tpeVar),(2,[| PFun bb (go k) (go k) |])]

export
prim : Gen Term
prim =
  frequency
    [ (1, pure (TPrim NoBB PUnit))
    , (1, (TPrim NoBB . PBool) <$> bool)
    , (3, (TPrim NoBB . PNat) <$> nat (linear 0 100))
    , (3, TVar NoBB <$> varname)
    ]

export
term : Gen Term
term = go 5
  where
    go : Nat -> Gen Term
    go 0     = prim
    go (S k) =
      frequency
        [ (1, prim)
        , (2, [| TApp bb (go k) (go k) |])
        , (2, [| TIf  bb (go k) (go k) (go k) |])
        , (2, [| TLam  bb bindname tpe (go k) |])
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
