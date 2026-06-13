module TPL.ArExp.Term

import Derive.Prelude

%default total
%language ElabReflection

public export
data Term : Type where
  TTrue  : Term -- true
  TFalse : Term -- false
  TIf    : (i,t,e : Term) -> Term -- if then else
  TZ     : Term -- zero
  TSucc  : Term -> Term -- succ
  TPred  : Term -> Term -- pred
  TIsZ   : Term -> Term -- iszero

%runElab derive "Term" [Show,Eq]

paren : Term -> String -> String
paren TTrue s = s
paren TFalse s = s
paren TZ s = s
paren _  s = "(\{s})"

export
Interpolation Term where
  interpolate TTrue       = "true"
  interpolate TFalse      = "false"
  interpolate (TIf i t e) = "if \{i} then \{t} else \{e}"
  interpolate TZ          = "0"
  interpolate (TSucc x)   = "succ \{paren x (interpolate x)}"
  interpolate (TPred x)   = "pred \{paren x (interpolate x)}"
  interpolate (TIsZ x)    = "iszero \{paren x (interpolate x)}"

export
Cast Nat Term where
  cast Z     = TZ
  cast (S k) = TSucc (cast k)
