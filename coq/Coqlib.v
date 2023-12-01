(** * Coqlib : Coq Libraries *)

From Coq Require Export
  FSets.FMapFacts
  Bool
  Arith
  Psatz
  Program
  Program.Equality
  List
  ZArith
  ZArith.BinIntDef .

Export ListNotations. 

From ExtLib Require Export
  Data.Monads.OptionMonad
  Structures.Monads.

From Coq Require Export
     ssreflect
     ssrfun
     ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
