#import "template.typ": *

== Processing Source Files

In this section we are going to have a look at how to
stream process the declarations in a source file.

Starting with the untyped lambda calculus, we will provide a simple
syntax for top-level declarations, which will allow us to at least
define and reuse top-level definitions as well as add evaluation
statements to print out the results of our computations.

We are going to abstract over the programming language in question,
and request a couple of capabilities from each of the tiny
languages we will explor:

- they must have a parseable syntax of top-level declarations
- they must provide an environment of builtin functions
  (usually, these are operations on values of primitive types)
- given an environment of top-level definitions, they must be
  able to process a new such definition, update the environment
  accordingly, and produce some optional output

These capabilities are grouped in interface `Language`:

```idris
module TPL.Process

import public Data.FilePath.File
import public FS.Posix
import public IO.Async.Console
import public IO.Async.Logging
import public IO.Async.Loop.Posix
import public TPL.Env

import Data.Linear.Ref1
import Data.SortedMap
import FS.Posix.Internal
import System
import System.Posix.Dir
import Text.ILex.FS

%default total

||| An interface for tiny programming languages
|||
||| @x : the language's error type
||| @d : type of top-level declarations
||| @t : type of processed top-level definitions
||| @v : type of values terms are being evaluated to
public export
interface Interpolation x => Interpolation v => Language x d t v | d where
  builtin : Env t

  parser  : Parser1 (BBErr x) (List d)

  eval    : Env t -> d -> Either (BBErr x) (Maybe v, Env t)

export %inline
evalRes :
     {auto lang : Language x d t v}
  -> {auto has  : Has (ByteErr x) es}
  -> Origin
  -> Env t
  -> d
  -> Result es (Maybe v, Env t)
evalRes o env = mapFst (inject . byteError o) . eval env
```

We can use interface `Language` to stream declarations from a source
file or other stream of byte strings.

```idris
writeResults : Interpolation t => ConsoleOut e => List t -> Async e es ()
writeResults [] = pure ()
writeResults vs = (cputStr . unlines . map interpolate) vs

parameters (0 d : Type)
           {0 f : List Type -> Type -> Type}
           {auto elin : ELift1 q f}
           {auto lang : Language x d t v}
           {auto hasb : Has (ByteErr x) es}

  export
  streamDecls : Origin -> Stream f es ByteString -> Pull f (List v) es (Env t)
  streamDecls o bs =
    streamParseFrom o (parser @{lang}) bs
      |> C.escanReturn (builtin @{lang}) (evalRes o)
      |> P.mapOutput catMaybes

parameters (0 d : Type)
           {auto lang : Language x d t v}
           {auto hasn : Has Errno es}
           {auto hasb : Has (ByteErr x) es}
           {auto hasf : Has (ParseError x) es}
           {auto polh : PollH e}
           {auto cnsl : ConsoleOut e}

  export
  streamSrcFile : File Abs -> AsyncPull e (List v) es (Env t)
  streamSrcFile f =
   let pth := interpolate f
    in locError (InnerError x) $ streamDecls d (FileSrc pth) (readBytes pth)

  export
  processSrcFile : File Abs -> AsyncStream e es Void
  processSrcFile f = streamSrcFile f |> foreach writeResults |> ignore
```

For running our streaming programs, we provide some additional utilities:

```idris
parameters {auto log : Logger Poll}
  export %inline
  Interpolation t => Loggable Poll t where
    logLoggable = ierror

public export
0 Errs : Type -> List Type
Errs e = [Errno, ByteErr e,ParseError e,String]

public export
0 Prog : Type -> Type -> Type
Prog e a = ConsoleOut Poll => Async Poll (Errs e) a

export covering
runProg : Interpolation e => Prog e () -> IO ()
runProg prog =
  simpleApp $ use1 Console.stdOut $ \c =>
   let logger := filter Info $ colorConsoleLogger c
    in logErrs prog

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
