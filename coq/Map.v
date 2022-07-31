Require Export CHKC.MapS.
Require Import Coq.FSets.FMapList.

Module Make (X : OrderedType) <: MapS.S X.
  Include FMapList.Make X.

  Section elt.
    Variable elt : Type.

    Lemma find_add : forall k v m,
        find (elt := elt) k (add k v m) = Some v.
    Proof.
      intros.
      apply find_1.
      apply add_1.
      apply E.eq_refl.
    Qed.

    Lemma mapsto_add1 : forall k v1 v2 s,
        MapsTo (elt := elt) k v1 (add k v2 s) -> v1 = v2.
    Proof.
      intros.
      apply find_1 in H.
      rewrite find_add in H.
      inversion H.
      reflexivity.
    Qed.

    Lemma mapsto_always_same : forall k v1 v2 s,
           MapsTo (elt := elt) k v1 s ->
            MapsTo (elt := elt) k v2 s -> 
                       v1 = v2.
    Proof.
     intros.
     apply find_1 in H.
     apply find_1 in H0.
     rewrite H in H0.
     injection H0.
     easy.
    Qed.

    Definition eq := E.eq.

    Lemma mapsto_add2 : forall k1 k2 v1 v2 s,
        MapsTo (elt := elt) k1 v1 (add k2 v2 s) ->
        ~ E.eq k1 k2 ->
        MapsTo k1 v1 s.
    Proof.
      intros.
      apply add_3 with (x := k2) (e' := v2).
      unfold not.
      intros.
      apply H0.
      symmetry.
      assumption.
      assumption.
    Qed.

    Lemma mapsto_equal : forall k v s1 s2,
        MapsTo (elt := elt) k v s1 ->
        Equal s1 s2 ->
        MapsTo k v s2.
    Proof.
      intros.
      unfold Equal in H0.
      apply find_2. rewrite <- H0.
      apply find_1.
      assumption.
    Qed.
    
    Lemma mapsto_in:forall k v s1, MapsTo (elt := elt) k v s1 -> In k s1.
    Proof.
     intros. exists v. easy.
    Qed.

Lemma find_add1 : forall x (t : elt) env,
    find (elt := elt) x (add x t env) = Some t.
Proof.
  intros.
  apply find_1.
  apply add_1.
  reflexivity.
Qed.

Lemma find1 : forall x env,
    find x env = None -> (forall (t : elt), ~ MapsTo (elt := elt) x t env).
Proof.
  intros.
  unfold not.
  intros.
  apply find_1 in H0.
  rewrite -> H0 in H.
  inversion H.
Qed.

Lemma find2 : forall x env,
    (forall (t : elt), ~ MapsTo x t env) -> find x env = None.
Proof.
  intros.
  destruct (find (elt := elt) x env) eqn:Hd.
  - exfalso. eapply H.
    apply find_2 in Hd.
    apply Hd.
  - reflexivity.
Qed.

  End elt.
End Make.