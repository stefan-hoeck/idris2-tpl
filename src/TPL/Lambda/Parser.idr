module TPL.Lambda.Parser

import Derive.Prelude
import Text.ILex
import Text.ILex.DStack
import public TPL.Lambda.Term

%default total
%hide Data.Linear.(.)
%language ElabReflection

-- --------------------------------------------------------------------------------
-- -- Parser Stack
-- --------------------------------------------------------------------------------
--
-- data PState : List Type -> Type where
--   PIni   : PState [SnocList Term]
--   POpn   : PState [SnocList Term]
--   PLam   : PState []
--   PLamV  : PState [Var]
--   PLamD  : PState [SnocList Term,Var]
--   PErr   : PState []
--
-- %runElab deriveIndexed "PState" [Show,ConIndex]
