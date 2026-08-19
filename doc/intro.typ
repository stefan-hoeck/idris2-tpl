#import "template.typ": *

#pagebreak()

= Introduction

I've been working through Benjamin Pierce's "Types and Programming Languages" @tapl (TAPL)
for several years now, never making it too far for the usual reasons: Lack of time,
losing interest. In this project, I'm going to take another shot and this time
feels different. I'm serious about doing this and about doing it in #Idris2:
Not only following along in the book and doing (some of) the exercises but
actually implementing the various toy languages from scratch in a language
with dependent types. This is therefore bound to take another couple of years
before it is done.

Along the way, however, I'm planning to tinker with various techniques for
writing parsers, type checkers, and evaluation functions in a purely functional
style making use of #Idris2's elaborator and totality checking machinery to
implement some of the functionality discussed in the book in such a way that
the implementation is at the same time a proof of validity.
