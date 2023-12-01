#lang scribble/manual
@title[#:style '(toc unnumbered)]{Null Terminated Array Pointers in Checked C}

@local-table-of-contents[#:style 'immediate-only]

This paper gives a formalization of null terminated array
pointers in Checked C.  We give an operational semantics
and type system and prove type soundness.


@include-section["scaled-up.scrbl"]

@include-section["compiled-check.scrbl"]


@include-section["post.scrbl"]

