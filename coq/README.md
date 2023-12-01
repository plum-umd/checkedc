# Checked C Formalism Metatheory

This repository contains a mechanization of the syntax,
semantics (dynamic and static), and metatheory of core Checked C for new RLBox tainted typed development.
Mechanization was carried out with The Coq Proof Assistant,
version 8.12 (Sep 2021).

The development depends only on the Coq standard library, and related tooling (`coqdoc`, `coq_makefile`, etc.)

## Building

To build the actually proof development, run

    % make

Open A Coq Assistent, and then Open CheckedC.v file, and then you can see the step by step proof result.

## Overview

The main theorems of the development are *progress* and *preservation* of the static semantics.
Together, these lemmas imply a *blame* theorem. This theorem is the important safety property that
the static semantics ensure. In short, it says if a configuration is "stuck" then code in an unchecked
region is to blame.

### Blame

The *blame* theorem relies on both progress and preservation. The only non-trivial, unproven lemma which it
relies on is decidability of typechecking. We are confident that typechecking is decidable.

### Progress

The *progress* theorem is fully mechanized.

### Preservation

The *preservation* theorem is fully mechanized.
The only admitted lemma it relies on is a proposition on coq maps (represented as sorted lists without
duplicates), that if a map already contains a specific key, then adding another binding for that key
does not change it's cardinality. This lemma cannot be proven without diving into the internals of maps
and should probably be part of the standard library.
   
  Lemma heap_add_in_cardinal : forall n v H,
    Heap.In n H -> 
    Heap.cardinal (elt:=nat * type) (Heap.add n v H) =
    Heap.cardinal (elt:=nat * type) H.


## On Literacy

The development was initially developed with literacy as a priority. Unfortunately, as deadlines grow closer, proofs get sloppier.
This means that (a) we strive to have the structure of the Coq proofs look very similar to their counterparts on paper and (b) that
the development is written using `coqdoc` documentation.

There is much work left to be done, but this remains a priority with this proof development moving forward.
