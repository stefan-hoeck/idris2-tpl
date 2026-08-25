#import "template.typ": *

== Processing Source Files

In this section we are going to have a look at how to
stream process the declarations in a source file.

Starting with the untyped lambda calculus, we will provide a simple
syntax for top-level declarations, which will allow us to at least
define and reuse top-level definitions as well as add evaluation
statements to print out the results of our computations.

We are going to abstract over the programming language in question,

```idris
module TPL.Process

import public Data.FilePath.File
import public FS.Posix
import public TPL.Env

import Data.Linear.Ref1
import Data.SortedMap
import FS.Posix.Internal
import IO.Async.Loop.Posix
import System
import System.Posix.Dir
import Text.ILex.FS

%default total

public export
interface Interpolation x => Interpolation v => Language x d t v | d where
  builtin : Env t

  parser  : Parser1 (BBErr x) (List d)

  eval    : Env t -> d -> Either (BBErr x) (Env t, Maybe v)

proc1 :
     {auto lang : Language x d t v}
  -> SnocList v
  -> Origin
  -> Env t
  -> List d
  -> Either (ByteErr x) (Env t, List v)
proc1 sv o env []        = Right (env, sv <>> [])
proc1 sv o env (x :: xs) =
  case eval env x of
    Left  err    => Left (byteError o err)
    Right (e2,m) => proc1 (maybe sv (sv:<) m) o e2 xs

parameters (0 d : Type)
           {auto lang : Language x d t v}
           {auto hasn : Has Errno es}
           {auto hasb : Has (ByteErr x) es}
           {auto polh : PollH e}

  proc : Origin -> IORef (Env t) -> List d -> Async e es (List v)
  proc o ref vs = Prelude.do
    env        <- readref ref
    (env2, vs) <- injectEither (proc1 [<] o env vs)
    writeref ref env2
    pure vs

  export
  streamDecls : File Abs -> AsyncPull e (List v) es (Env t)
  streamDecls f =
   let pth := interpolate f
       o   := FileSrc pth
    in locError {x = InnerError x} $ Prelude.do
         env <- newref {s = World} (builtin @{lang})
         readBytes pth
           |> streamParseFrom o (parser @{lang})
           |> evalMap (proc o env)
           |> (>> readref env)

  export
  processSrcFile : File Abs -> AsyncStream e es Void
  processSrcFile f =
    streamDecls f
      |> C.mapOutput interpolate
      |> foreach (writeLines Stdout)
      |> ignore

public export
0 Errs : Type -> List Type
Errs e = [Errno, ByteErr e,String]

handlers : (0 e : _) -> Interpolation e => All (\e => e -> Async Poll [] ()) (Errs e)
handlers _ = mapProperty (stderrLn .) [interpolate, interpolate, interpolate]

public export
0 Prog : Type -> Type -> Type
Prog e a = Async Poll (Errs e) a

public export
0 Strm : Type -> Type -> Type
Strm e o = AsyncStream Poll (Errs e) o

export covering
runProg : Interpolation e => Prog e () -> IO ()
runProg prog = simpleApp $ handle (handlers e) prog

parameters (0 d : Type)
           {auto lang : Language x d t v}

  export covering
  source : Prog x ()
  source = Prelude.do
    [_,p] <- liftIO getArgs | _ => throw "Invalid args"
    case AnyFile.parse p of
      Nothing => throw "Invalid source file path: '\{p}'"
      Just (AF f@(MkF (PAbs {}) _)) => mpullErr (processSrcFile d f)
      Just (AF f@(MkF (PRel {}) _)) => Prelude.do
        s <- getcwd String
        case AbsPath.parse s of
          Just p  => mpullErr (processSrcFile d $ p </> f)
          Nothing => throw "Invalid working dir: '\{s}'"
```

// vi: filetype=idris2:syntax=typst
