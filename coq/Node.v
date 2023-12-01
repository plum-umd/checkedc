From CHKC Require Import CheckedC.

Definition list : struct := 0.
Definition val  : field := 0.
Definition next : field := 1.
Definition list_fields :=
  Fields.add val TNat (Fields.add next (TPtr Checked (TStruct list)) (@Fields.empty type)).
             
Definition D : structdef :=
  StructDef.add list list_fields (StructDef.empty fields).

Definition p : var := 0.
Definition x : var := 1.
Definition node :=
   ELet p (EMalloc (TStruct list))
          (EAssign (EFieldAddr (EVar p) next) (EVar p)).

Definition heap_empty := Heap.empty (nat * type).
Definition heap_final := Heap.add 1 (0, TNat) (Heap.add 2 (1, TPtr Checked (TStruct list)) heap_empty).

Require Import Omega.
Definition list_ptr := TPtr Checked (TStruct list).
Example well_typed_cyclic :
  @well_typed D heap_final (Env.empty type) Checked
              (ELit 1 list_ptr) list_ptr.
Proof.
  constructor.
  eapply TyLitC; simpl in *; eauto; simpl in *.
  intros k Hk.
  assert (k = 0 \/ k = 1) by omega.
  inv H.
  - (* val *)
    exists 0. exists TNat.
    repeat (split; eauto).
    unfold heap_final.
    apply Heap.add_1; auto.
  - (* next *)
    exists 1. exists list_ptr.
    repeat (split; eauto).
    + unfold heap_final, list_ptr.
      apply Heap.add_2; auto.
      apply Heap.add_1; auto.
    + unfold list_ptr.
      constructor.
      left; auto.
Qed.
      
Example well_typed_node :
  @well_typed D (Heap.empty (nat * type)) (Env.empty type) Checked
              node (TPtr Checked (TStruct list)).
Proof.
  unfold node.
  eapply TyLet with (t1 := TPtr Checked (TStruct list)); eauto.
  - eapply TyMalloc.
    intros; congruence.
  - eapply TyAssign; eauto.
    + eapply TyFieldAddr with (i := next); eauto.
      * apply TyVar.
        apply Env.add_1; auto.
      * unfold D.
          apply StructDef.add_1; auto.
      * unfold list_fields.
        apply Fields.add_2; auto.
        apply Fields.add_1; auto.
      * auto.
    + apply TyVar.
      apply Env.add_1; auto.
Unshelve. exact 0. 
Qed.


Example reduce_node :
  reduce D heap_empty node Checked heap_final (RExpr (ELit 1 list_ptr)).
Proof.
  ctx (in_hole (EMalloc (TStruct list))
               (CLet p CHole (EAssign (EFieldAddr (EVar p) next) (EVar p))))
      (node).
  unfold node in *.
  rewrite <- HCtx.
  eapply RSExp.
  ctx (subst p (ELit 1 list_ptr) (EVar p)) (ELit 1 list_ptr).
  rewrite <- HCtx.
  apply SLet.