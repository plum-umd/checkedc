(** * Checked C: List Utilities *)

From CHKC Require Import Tactics.
Require Export Coq.Lists.List.
Import ListNotations.

Set Implicit Arguments.

Section Lists.

  Variable A : Type.

  Fixpoint replicate (n : nat) (a : A) : list A :=
    match n with
    | O => []
    | S n' => a :: (replicate n' a)
    end.

  Lemma replicate_length : forall n a,
      length (replicate n a) = n.
  Proof.
    intros n a.
    induction n.
    - reflexivity.
    - simpl. rewrite IHn. reflexivity.
  Qed.

  Lemma replicate_nth : forall (n k : nat) (w x : A),
    nth_error (replicate n w) k = Some x -> w = x.
  Proof.
    intro n; induction n; intros k w x H.
    - simpl in *.
      destruct k; simpl in *; inv H.
    - destruct k; simpl in *.
      + inv H; auto.
      + eauto.
  Qed.      
  
End Lists.