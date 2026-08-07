module TPL.Match

import Data.List.Quantifiers
import Data.SortedMap
import public TPL.Name
import public TPL.Error

%default total

public export
data Matching : Type -> (VarName, t) -> Type where
  M : (n : VarName) -> (type : t) -> (val : x) -> Matching x (n,type)

0 MatchMap : Type -> Type
MatchMap t = SortedMap VarName (ByteBounds, t)

0 Res : Type -> Type -> Type
Res t x = Either (BBErr $ TplErr t) x

parameters {0 t,x    : Type}
           (trm      : ByteBounds)
           (sum      : t)

  matchMap : MatchMap x -> List (ByteBounded VarName, x) -> Res t (MatchMap x)
  matchMap m []            = Right m
  matchMap m ((b,v) :: xs) =
    case lookup b.val m of
      Nothing => matchMap (insert b.val (b.bounds, v) m) xs
      Just _  => errUnreachable b.bounds

  missing : SnocList VarName -> List (VarName,t) -> MatchMap x -> Match.Res t s
  missing sm []          m = errCovering trm (sm <>> [])
  missing sm ((v,_)::xs) m =
    case lookup v m of
      Nothing => missing (sm:<v) xs m
      Just _  => missing sm xs m

  accum : (ps : List (VarName,t)) -> MatchMap x -> Res t (All (Matching x) ps)
  accum [] m =
    case kvList m of
      []         => Right []
      (v,b,_)::_ => notCon (B v b) sum
  accum ((v,tp) :: xs) m =
    case lookup v m of
      Nothing    => missing [<v] xs m
      Just (b,w) => (M v tp w ::) <$> accum xs (delete v m)

  export %inline
  match :
       (ps : List (VarName, t))
    -> List (ByteBounded VarName, x)
    -> Either (BBErr $ TplErr t) (All (Matching x) ps)
  match ps vs = matchMap empty vs >>= accum ps
