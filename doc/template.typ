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
    pad(x: 2em, y: 1em, it)
  }

  set terms(
    hanging-indent: 0.5cm,
    spacing: 0.5cm,
    indent: 1cm,
  )

  doc
}

#let ilex = [_ilex_]
#let ref1 = [_ref1_]
