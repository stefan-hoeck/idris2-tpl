#import "template.typ": *

#show title: it => {
  set text(size : 1.5em);
  set align(center);
  set par(justify : false);
  it
}

#title[Types and Programming Languages in Idris2]
#v(3cm)
#align(center)[
  #par(justify : false)[
    by Stefan Höck \
    #text(size: 0.8em)[#link("https://github.com/stefan-hoeck")]
  ]
]
