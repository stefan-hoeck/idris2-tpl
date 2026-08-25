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

import Data.FilePath.File
import FS.Posix
import TPL.Env
import Text.ILex

%default total

public export
interface Interpolation e => Language (0 e, d, t : Type) | d where
  parser  : Parser1 (BBErr e) (List d)

  eval    : Env t -> d -> Either (BBErr e) (Env t, Maybe String)

```

// vi: filetype=idris2:syntax=typst
