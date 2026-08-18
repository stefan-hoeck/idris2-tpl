#let padblock(cont) = pad(x: 2em, y: 1em, cont)

#let template = doc => {
  set page(
    paper : "a4"
  )
  set text(
    font : "Liberation Sans"
  )

  let num(..nums) = {
    if nums.len() == 1 {numbering("I", ..nums)} else {numbering("1.", ..nums)}
  }

  set heading(
    numbering : num
  )

  set par(
    justify : true
  )

  show raw.where(block : true): it => {
    padblock(it)
  }

  set terms(
    hanging-indent: 0.5cm,
    spacing: 0.5cm,
    indent: 1cm,
  )

  doc
}

#let lib(str) = emph(str)

#let hockLib(str) = {
  emph(str)
  footnote(link("https://github.com/stefan-hoeck/idris2-" + str + ".git"))
}

#let ilex     = lib("ilex")
#let ref1     = lib("ref1")
#let ilex_ref = hockLib("ilex")
#let ref1_ref = hockLib("ref1")

#let IdrisCodeFont        = "Liberation Mono"
#let IdrisColourData      = rgb("#ff6a6a")
#let IdrisColourType      = rgb("#009acd")
#let IdrisColourBound     = rgb("#9a32cd")
#let IdrisColourFunction  = rgb("#458b00")
#let IdrisColourKeyword   = color.black
#let IdrisColourImplicit  = rgb("#9a32cd")
#let IdrisColourComment   = rgb("#cdcdc1")
#let IdrisColourHole      = color.yellow
#let IdrisColourNamespace = color.black
#let IdrisColourPostulate = rgb("#9a32cd")
#let IdrisColourModule    = color.black

#let IdrisHighlight(col, styl, wei, cont) = {
  set text(fill: col, style: styl, weight: wei)
  cont
}

#let IdrisHole(cont) = {
  set text(fill: IdrisColourHole, "normal", "bold")
  cont
}

#let IdrisCode(cont) = {
  set text(font: IdrisCodeFont, size: 0.8em)
  padblock(cont)
}

#let IdrisData(txt)      = IdrisHighlight(IdrisColourData, "normal", "medium",txt)
#let IdrisType(txt)      = IdrisHighlight(IdrisColourType, "normal", "medium",txt)
#let IdrisBound(txt)     = IdrisHighlight(IdrisColourBound, "normal", "medium",txt)
#let IdrisFunction(txt)  = IdrisHighlight(IdrisColourFunction, "normal", "medium",txt)
#let IdrisKeyword(txt)   = IdrisHighlight(IdrisColourKeyword, "normal", "bold",txt)
#let IdrisImplicit(txt)  = IdrisHighlight(IdrisColourImplicit, "normal", "medium",txt)
#let IdrisComment(txt)   = IdrisHighlight(IdrisColourComment, "italic", "medium",txt)
#let IdrisNamespace(txt) = IdrisHighlight(IdrisColourNamespace, "italic", "medium",txt)
#let IdrisPostulate(txt) = IdrisHighlight(IdrisColourPostulate, "normal", "bold",txt)
#let IdrisModule(txt)    = IdrisHighlight(IdrisColourModule, "italic", "medium",txt)
