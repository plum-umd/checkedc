(** * CheckedCProp : Checked C Model Properties *)

From CHKC Require Import
  Coqlib
  Tactics
  ListUtil
  Map
  CheckedCDef.
Require Import Coq.Logic.Classical_Prop.

Create HintDb heap.

Ltac solveMaps :=
  match goal with
  | |- Env.In ?x ?m =>
      unfold Env.In, Env.Raw.PX.In; eexists; eauto
  | |- Stack.In ?x ?m =>
      unfold Stack.In, Stack.Raw.PX.In; eexists; eauto
  | |- Heap.In ?x ?m =>
      unfold Heap.In, Heap.Raw.PX.In; eexists; eauto
  end; auto.


Section HeapProp.
  Local Open Scope Z_scope.
  Variable D : structdef.
  Variable F : FEnv.
  Variable Q : theta.
  Variable m : mode.

  Definition heap_wf (H : heap) : Prop := forall (addr : Z),
      0 < addr <= (Z.of_nat (Heap.cardinal H)) <-> Heap.In addr H.

  Definition heap_consistent_checked (H' : heap) (H : heap) : Prop :=
    forall n t,
      well_typed_lit_checked D F H empty_scope n t->
      well_typed_lit_checked D F H' empty_scope n t.


  Definition heap_well_typed_checked (H:heap)
    (n:Z) (t:type) :=
    simple_type t -> well_typed_lit_checked D F H empty_scope n t.

  Inductive heap_wt_arg (H:heap)
    : expression -> Prop :=
  | HtArgLit : forall n t,
      heap_well_typed_checked H n t -> heap_wt_arg H (ELit n t)
  | HtArgVar : forall x, heap_wt_arg H (EVar x).

  Inductive heap_wt_args (H:heap)
    : list expression -> Prop :=
    heap_wt_empty : heap_wt_args H ([])
  | heap_wt_many : forall e el,
      heap_wt_arg H e -> heap_wt_args H el -> heap_wt_args H (e::el).

(*
  Inductive heap_wt (H:heap) : expression -> Prop :=
  | HtLit : forall n t, heap_well_typed_checked H n t -> heap_wt H (ELit n t)
  | HtVar : forall x, heap_wt H (EVar x)
  | HtStrlen : forall x, heap_wt H (EStrlen x)
  | HtCall : forall f el, heap_wt_args H el -> heap_wt H (ECall f el)
  | HtRet : forall x old e, heap_wt H e -> heap_wt H (ERet x old e)
  | HtDynCast : forall t e, heap_wt H e -> heap_wt H (EDynCast t e)
  | HtLet : forall x e1 e2,
      heap_wt H e1 -> heap_wt H e2 -> heap_wt H (ELet x e1 e2)
  | HtMalloc : forall t, heap_wt H (EMalloc m t)
  | HtCast : forall t e, heap_wt H e -> heap_wt H (ECast t e)
  | HtPlus : forall e1 e2,
      heap_wt H e1 -> heap_wt H e2 -> heap_wt H (EPlus e1 e2)
  | HtFieldAddr : forall e f, heap_wt H e -> heap_wt H (EFieldAddr e f)
  | HtDeref : forall e, heap_wt H e -> heap_wt H (EDeref e)
  | HtAssign : forall e1 e2,
      heap_wt H e1 -> heap_wt H e2 -> heap_wt H (EAssign e1 e2)
  | HtIf : forall x e1 e2,
      heap_wt H e1 -> heap_wt H e2 -> heap_wt H (EIf x e1 e2)
  | HtUnChecked : forall e, heap_wt H e -> heap_wt H (EUnchecked e).
*)
  Definition heap_wt_all (H : heap) :=
    forall x n t,
      Heap.MapsTo x (n,t) H ->
      word_type t /\ type_wf D m t /\ simple_type t
      /\ well_typed_lit_checked D F H empty_scope n t.

  Definition heap_wt_tainted (H : heap) :=
    forall x n t,
      Heap.MapsTo x (n,t) H ->
      word_type t /\ type_wf D m t /\ simple_type t.

  Local Close Scope Z_scope.
End HeapProp.


(** ** Real Heap Properties *)
(** This section contains heap and stack properties lifted to real heaps. *)
Section RealHeapProp.
  Variable D : structdef.
  Variable F : FEnv.
  Variable Q : theta.
  Variable m : mode.

  Definition rheap_wf (R : real_heap) : Prop := forall Hchk Htnt,
      R = (Hchk, Htnt) -> heap_wf Hchk.

(*
  Definition is_checked (t:type) := match t with TNat => True | TPtr m w => (m = Checked) | _ => False end.
*)

  (** Types on the stack agree with those on the rheap. *)
  Definition stack_rheap_consistent (R : real_heap) S :=
    forall Hchk Htnt x n t,
      R = (Hchk, Htnt) ->
      Stack.MapsTo x (n,t) S -> well_typed_lit_checked D F Hchk empty_scope n t.


  (* FIXME: hold the definition for now *)
  Definition rheap_consistent (R' : real_heap) (R : real_heap) : Prop :=
    forall Hchk' Htnt' Hchk Htnt,
      R' = (Hchk', Htnt') -> R = (Hchk, Htnt) -> 
      heap_consistent_checked D F Hchk' Hchk.

  Lemma rheap_consistent_refl : forall R, rheap_consistent R R.
  Proof.
    unfold rheap_consistent. intros [H1 H2] * E1 E2.  inv E1. inv E2.
    unfold heap_consistent_checked. intuition.
  Qed.
  
  Definition rheap_wt_all (R : real_heap) := forall Hchk Htnt,
    R = (Hchk, Htnt) ->
    heap_wt_all D F Checked Hchk /\ heap_wt_tainted D Tainted Htnt.

End RealHeapProp.

#[export] Hint Unfold rheap_wf : heap.
#[export] Hint Unfold stack_rheap_consistent : heap.
#[export] Hint Unfold rheap_consistent : heap.
#[export] Hint Unfold rheap_wt_all : heap.
#[export] Hint Resolve rheap_consistent_refl : heap.

  
Section StackProp.
  Variable D : structdef.
  Variable Q : theta.

  Definition stack_wf env s := forall x t,
      Env.MapsTo x t env -> exists (v:Z) t',
        eq_subtype D Q t' t 
        /\ Stack.MapsTo x (v, t') s.

  Lemma stack_wf_sub_domain : forall env s, stack_wf env s -> sub_domain env s.
  Proof.
  intros. unfold stack_wf, sub_domain in *.
  intros. destruct H0. apply H in H0. destruct H0. destruct H0. destruct H0.
  exists (x1,x2). easy.
  Qed.

End StackProp. 


(* Env consistency *)
Definition both_simple (t t' :type) := simple_type t -> simple_type t'.

Definition env_consistent D Q (env env' : env) := 
      (forall x, Env.In x env <-> Env.In x env')
      /\ (forall x t , ~ is_nt_ptr t -> Env.MapsTo x t env ->  Env.MapsTo x t env')
      /\ (forall x t t', is_nt_ptr t -> Env.MapsTo x t env 
                 ->  Env.MapsTo x t' env' -> subtype_core D Q t' t /\ both_simple t t').

Lemma env_consist_refl : forall D Q env, env_consistent D Q env env.
Proof.
  intros. unfold env_consistent. split.
  intros. split. intros. easy. intros; easy.
  split. intros. easy.
  intros. apply Env.mapsto_always_same with (v1:= t') in H0; try easy. subst.
  split.
  constructor. unfold both_simple; intros; easy.
Qed.

Lemma env_wf_consist: forall es D Q env env', env_consistent D Q env env' ->
      Forall (fun e => env_wf e env) es -> Forall (fun e => env_wf e env') es.
Proof.
  induction es;intros;simpl in *;try easy.
  inv H0. inv H. constructor.
  unfold env_wf in *. intros. apply H3 in H.
  apply H0 in H. easy.
  apply (IHes D Q env); easy.
Qed.

Definition simple_means_not_freeVars:
   forall t, simple_type t -> freeTypeVars t = [].
Proof.
  intros. induction H;simpl in *. easy.
Qed.
  

Lemma well_typed_bound : forall D F R env Q m e t,
      well_typed D F R env Q m e t ->  env_wf e env.
Proof.
 intros. induction H;unfold env_wf;intros;simpl in *; eauto.
 apply simple_means_not_freeVars in H0. rewrite H0 in H2. simpl in *. easy.
 apply simple_means_not_freeVars in H0. rewrite H0 in H1. simpl in *. easy.
 destruct H1;subst.
 unfold Env.In,Env.Raw.PX.In. exists t; easy. easy.
 apply in_app_iff in H3. destruct H3.
 unfold env_wf in *. apply IHwell_typed; easy.
 clear H1. clear H2. clear IHwell_typed.
 induction es;intros;simpl in *. easy.
 inv H0.
 apply in_app_iff in H3. destruct H3.
 apply H4. easy.
 apply IHes; try easy.
 destruct H1;subst.
 unfold Env.In,Env.Raw.PX.In. exists (TPtr m' (TNTArray h l t)); easy. easy.
(*
 destruct H3;subst.
 unfold Env.In,Env.Raw.PX.In. exists (TPtr m' (TNTArray l h ta)); easy.
 apply ListSet.set_diff_iff in H3. destruct H3. simpl in *.
 apply not_or_and in H4. destruct H4.
 specialize (IHwell_typed x0).
 apply IHwell_typed in H3.
 unfold Env.In, Env.Raw.PX.In in *.
 destruct H3.
 apply Env.add_3 in H3 ; try easy.
 destruct (Nat.eq_dec x0 y); subst.
 exists (TPtr m' (TNTArray l h ta)). easy.
 apply Env.add_3 in H3 ; try easy. exists x1. easy. lia.
*)
 apply in_app_iff in H3. destruct H3.
 apply IHwell_typed1; easy.
 apply ListSet.set_diff_iff in H3. destruct H3. simpl in *.
 apply not_or_and in H4. destruct H4.
 apply IHwell_typed2 in H3.
 unfold Env.In, Env.Raw.PX.In in *.
 destruct H3.
 apply Env.add_3 in H3 ; try easy.
 exists x1. easy.
 apply in_app_iff in H3. destruct H3.
 apply IHwell_typed1; easy.
 apply ListSet.set_diff_iff in H3. destruct H3. simpl in *.
 apply not_or_and in H4. destruct H4.
 apply IHwell_typed2 in H3.
 unfold Env.In, Env.Raw.PX.In in *.
 destruct H3.
 apply Env.add_3 in H3 ; try easy.
 exists x1. easy.
 apply ListSet.set_diff_iff in H1. destruct H1. simpl in *.
 apply not_or_and in H2. destruct H2.
 apply IHwell_typed in H1.
 unfold Env.In, Env.Raw.PX.In in *.
 destruct H1.
 apply Env.add_3 in H1 ; try easy.
 exists x1. easy.
 apply ListSet.set_diff_iff in H3. destruct H3. simpl in *.
 apply in_app_iff in H3. destruct H3.
 apply simple_means_not_freeVars in H0 ; simpl in *. rewrite H0 in H3. simpl in *. easy.
 apply not_or_and in H4. destruct H4.
 apply IHwell_typed in H3.
 unfold Env.In, Env.Raw.PX.In in *.
 destruct H3.
 apply Env.add_3 in H3 ; try easy.
 exists x1. easy.
 apply ListSet.set_diff_iff in H4. destruct H4. simpl in *.
 apply in_app_iff in H4. destruct H4.
 apply simple_means_not_freeVars in H2 ; simpl in *. rewrite H2 in H4. simpl in *. easy.
 apply not_or_and in H5. destruct H5.
 apply IHwell_typed in H4.
 unfold Env.In, Env.Raw.PX.In in *.
 destruct H4.
 apply Env.add_3 in H4 ; try easy.
 exists x1. easy.
 apply in_app_iff in H1. destruct H1.
 apply IHwell_typed1; easy.
 apply IHwell_typed2; easy.
 apply H1 in H2. exists TNat. easy.
 apply in_app_iff in H2. destruct H2.
 apply H in H2. exists TNat. easy.
 apply IHwell_typed; easy.
 apply in_app_iff in H2. destruct H2.
 apply H in H2. exists TNat. easy.
 apply IHwell_typed; easy.
 apply in_app_iff in H3. destruct H3.
 exists TNat.
 apply H. simpl. easy.
 apply IHwell_typed; easy.
 apply in_app_iff in H4. destruct H4.
 exists TNat.
 apply H1. simpl. easy.
 apply IHwell_typed; easy.
 apply in_app_iff in H3. destruct H3.
 exists TNat.
 apply H. simpl. easy.
 apply IHwell_typed; easy.
 apply in_app_iff in H4. destruct H4.
 apply IHwell_typed1; easy.
 apply IHwell_typed2; easy.
 apply in_app_iff in H4. destruct H4.
 apply IHwell_typed1; easy.
 apply IHwell_typed2; easy.
 apply in_app_iff in H4. destruct H4.
 apply IHwell_typed1; easy.
 apply IHwell_typed2; easy.
 apply in_app_iff in H5. destruct H5.
 apply IHwell_typed1; easy.
 apply IHwell_typed2; easy.
 apply in_app_iff in H5. destruct H5.
 apply IHwell_typed1; easy.
 apply IHwell_typed2; easy.
 apply in_app_iff in H6. destruct H6.
 apply in_app_iff in H6. destruct H6.
 apply IHwell_typed1; easy.
 apply IHwell_typed2; easy.
 apply IHwell_typed3; easy.
 apply in_app_iff in H6. destruct H6.
 apply in_app_iff in H6. destruct H6.
 apply IHwell_typed1; easy.
 apply IHwell_typed2; easy.
 apply IHwell_typed3; easy.
 destruct H5; subst. exists t. easy.
 apply in_app_iff in H5. destruct H5.
 apply IHwell_typed1; easy.
 apply IHwell_typed2; easy.
 destruct H3; subst. exists (TPtr m' (TNTArray l (Var x0 0) t)). easy.
 apply in_app_iff in H3. destruct H3.
 apply IHwell_typed1 in H3.
 destruct H3.
 destruct (Nat.eq_dec x x0); subst.
 exists ((TPtr m' (TNTArray l (Var x0 0) t))). easy.
 apply Env.add_3 in H3. exists x1. easy. easy.
 apply IHwell_typed2; easy.
 apply in_app_iff in H2. destruct H2.
 apply IHwell_typed1; easy.
 apply in_app_iff in H2. destruct H2.
 apply IHwell_typed2; easy.
 apply IHwell_typed3; easy.
Qed.

(* theta and stack relationship *)
Definition stack_theta_wf s Q := forall x v, Stack.MapsTo x (v,TNat) s -> Theta.MapsTo x (NumEq v) Q.

Definition stack_consist D (s s': stack) := 
    (forall x, Stack.In x s <-> Stack.In x s')
   /\ (forall x v t, ~ is_nt_ptr t
              -> Stack.MapsTo x (v,t) s -> Stack.MapsTo x (v,t) s')
   /\ (forall x v v' t t', is_nt_ptr t
              -> Stack.MapsTo x (v,t) s -> Stack.MapsTo x (v',t') s' -> v = v' /\ eq_subtype D empty_theta t' t).

Lemma stack_consist_refl: forall D s, stack_consist D s s.
Proof.
  intros. unfold stack_consist.
  split. intros. split;intros; easy.
  split. intros. easy.
  intros. apply Stack.mapsto_always_same with (v1:= (v,t)) in H1; try easy. inv H1. split; try easy.
  exists t'. split. apply type_eq_refl. constructor. constructor.
Qed. 

Lemma or_nt_ptr: forall t, is_nt_ptr t \/ ~ is_nt_ptr t.
Proof.
  intros. destruct t; simpl in *; try (right;easy).
  destruct t; try (right;easy). left. easy.
Qed.

Lemma type_eq_word: forall Q t t', word_type t -> type_eq Q t' t -> word_type t'.
Proof.
  intros. inv H0; try easy.
Qed.

Lemma subtype_core_word: forall D Q t t', word_type t -> subtype_core D Q t' t -> word_type t'.
Proof with (try eauto with ty; try easy).
  intros. inv H0...
Qed.

Lemma subtype_word: forall D Q t t', word_type t -> subtype D Q t' t -> word_type t'.
Proof with (try eauto with ty; try easy).
  intros. inv H0; inv H1...
Qed.

Lemma eq_subtype_word: forall D Q t t', word_type t -> eq_subtype D Q t' t -> word_type t'.
Proof.
  intros. destruct H0. destruct H0. apply subtype_word in H1; try easy.
  apply type_eq_word in H0; try easy.
Qed.


Lemma type_eq_type_wf: forall D m t t', type_wf D m t -> type_eq empty_theta t' t -> type_wf D m t'.
Proof with (try eauto with ty; try easy).
  intros. generalize dependent m. induction H0; intros...
  inv H. constructor. apply IHtype_eq; try easy.
  apply WFTPtrUnChecked; try easy. apply IHtype_eq; try easy.
  inv H2. constructor. apply type_eq_word with (Q := empty_theta) (t := t2); try easy.
  apply IHtype_eq. easy.
  inv H2. constructor. apply type_eq_word with (Q := empty_theta) (t := t2); try easy.
  apply IHtype_eq. easy.
Qed.

Lemma type_eq_type_wf_1: forall D Q m t t', type_wf D m t -> type_eq Q t' t -> type_wf D m t'.
Proof with (try eauto with ty; try easy).
  intros. generalize dependent m. induction H0; intros...
  inv H. constructor. apply IHtype_eq; try easy.
  apply WFTPtrUnChecked; try easy. apply IHtype_eq; try easy.
  inv H2. constructor. apply type_eq_word with (Q := Q) (t := t2); try easy.
  apply IHtype_eq. easy.
  inv H2. constructor. apply type_eq_word with (Q := Q) (t := t2); try easy.
  apply IHtype_eq. easy.
Qed.


Lemma subtype_core_type_wf: forall D m t t', type_wf D m t -> subtype_core D empty_theta t' t -> type_wf D m t'.
Proof with (try eauto with ty; try easy).
  intros. generalize dependent m. induction H0; intros...
  destruct (m0); try easy.
  apply WFTPtrChecked. inv H2. inv H5; try easy. inv H8; try easy.
  apply WFTPtrUnChecked; try easy. inv H2; try easy.
  inv H2;try easy. inv H8; try easy.
  apply WFTPtrUnChecked; try easy. inv H2; try easy.
  inv H2;try easy. inv H8; try easy.
  destruct (m0); try easy.
  apply WFTPtrChecked. inv H2. constructor; try easy. 
  constructor; try easy. 
  apply WFTPtrUnChecked; try easy. inv H2; try easy.
  inv H2;try easy.
  constructor; try easy. 
  apply WFTPtrUnChecked; try easy. inv H2; try easy.
  inv H2;try easy.
  constructor; try easy. 
  inv H2;try easy. 
  constructor; try easy. 
  constructor; try easy. 
  constructor; try easy. 
  constructor; try easy. 
  destruct (m0); try easy.
  apply WFTPtrChecked. inv H1. inv H4; try easy.
  constructor; try easy.
  inv H7; try easy. inv H1; try easy. 
  constructor; try easy. 
  inv H7;try easy. 
  constructor; try easy. 
  apply WFTPtrUnChecked; try easy. inv H1; try easy.
  inv H1;try easy.
  inv H7;try easy. 
  constructor; try easy. 
  destruct (m0); try easy.
  apply WFTPtrChecked. inv H1. inv H4; try easy.
  constructor; try easy.
  inv H7; try easy. inv H1; try easy. 
  constructor; try easy. 
  inv H7;try easy. 
  constructor; try easy. 
  apply WFTPtrUnChecked; try easy. inv H1; try easy.
  inv H1;try easy.
  inv H7;try easy. 
  constructor; try easy. 
  destruct (m0); try easy.
  apply WFTPtrChecked. inv H1. inv H4; try easy.
  constructor; try easy.
  inv H7; try easy. inv H1; try easy. 
  constructor; try easy. 
  inv H7;try easy. 
  constructor; try easy. 
  apply WFTPtrUnChecked; try easy. inv H1; try easy.
  inv H1;try easy.
  inv H7;try easy. 
  constructor; try easy. 
  destruct (m0); try easy.
  apply WFTPtrChecked. constructor. exists fs. easy.
  inv H1.
  apply WFTPtrUnChecked; try easy. constructor. exists fs. easy.
  inv H1.
  apply WFTPtrUnChecked; try easy. constructor. exists fs. easy.
  destruct (m0); try easy.
  apply WFTPtrChecked. constructor. exists fs. easy.
  inv H3.
  apply WFTPtrUnChecked; try easy. constructor. exists fs. easy.
  inv H3.
  apply WFTPtrUnChecked; try easy. constructor. exists fs. easy.
Qed.

Lemma subtype_type_wf: forall D m t t', type_wf D m t -> subtype D empty_theta t' t -> type_wf D m t'.
Proof with (try eauto with ty; try easy).
  intros. generalize dependent m. remember empty_theta as Q. induction H0; intros; subst...
  eapply subtype_core_type_wf; eauto.
  inv H3. constructor. inv H6. constructor; try easy.
  apply IHsubtype; try easy.
Admitted.


Lemma eq_subtype_type_wf: forall D m t t', type_wf D m t -> eq_subtype D empty_theta t' t -> type_wf D m t'.
Proof.
  intros. destruct H0. destruct H0. eapply subtype_type_wf in H1; eauto.
  eapply type_eq_type_wf in H0; eauto.
Qed.

Lemma simple_nat_leq: forall b b', freeBoundVars b = [] -> nat_leq empty_theta b' b -> freeBoundVars b' = [].
Proof.
  intros. inv H0;simpl in *; eauto.
  apply Theta.find_1 in H1. simpl in *.
  rewrite ThetaFacts.empty_o in H1. inv H1.
  apply Theta.find_1 in H1.
  rewrite ThetaFacts.empty_o in H1. inv H1.
  apply Theta.find_1 in H1.
  rewrite ThetaFacts.empty_o in H1. inv H1.
  apply Theta.find_1 in H1.
  rewrite ThetaFacts.empty_o in H1. inv H1.
Qed.

Lemma simple_nat_leq_1: forall b b', freeBoundVars b = [] -> nat_leq empty_theta b b' -> freeBoundVars b' = [].
Proof.
  intros. inv H0;simpl in *; eauto.
  apply Theta.find_1 in H1. simpl in *.
  rewrite ThetaFacts.empty_o in H1. inv H1.
  apply Theta.find_1 in H1.
  rewrite ThetaFacts.empty_o in H1. inv H1.
  apply Theta.find_1 in H1.
  rewrite ThetaFacts.empty_o in H1. inv H1.
  apply Theta.find_1 in H1.
  rewrite ThetaFacts.empty_o in H1. inv H1.
  apply Theta.find_1 in H1.
  rewrite ThetaFacts.empty_o in H1. inv H1.
Qed.

Lemma type_eq_simple: forall t t', simple_type t -> type_eq empty_theta t' t -> simple_type t'.
Proof with (try eauto with ty; try easy).
  intros. induction H0; unfold simple_type in *; intros; simpl in *...
  apply app_eq_nil in H. destruct H.
  apply app_eq_nil in H3. destruct H3.
  destruct H1. destruct H2.
  apply simple_nat_leq in H1; try easy.
  apply simple_nat_leq in H2; try easy. rewrite H1. rewrite H2.
  simpl. eauto.
  apply app_eq_nil in H. destruct H.
  apply app_eq_nil in H3. destruct H3.
  destruct H1. destruct H2.
  apply simple_nat_leq in H1; try easy.
  apply simple_nat_leq in H2; try easy. rewrite H1. rewrite H2.
  simpl. eauto.
Qed.

Lemma subtype_core_simple: forall D t t', simple_type t -> subtype_core D empty_theta t' t -> simple_type t'.
Proof with (try eauto with ty; try easy).
  intros. induction H0; unfold simple_type in *; intros; simpl in *...
  apply app_eq_nil in H. destruct H.
  apply app_eq_nil in H3. destruct H3.
  apply simple_nat_leq_1 in H1; try easy.
  apply simple_nat_leq in H1; try easy.
  apply simple_nat_leq_1 in H2; try easy. rewrite H1. rewrite H2.
  simpl. eauto.
  apply simple_nat_leq in H1; try easy.
  apply simple_nat_leq_1 in H2; try easy. rewrite H1. rewrite H2.
  simpl. eauto.
  apply app_eq_nil in H. destruct H.
  apply app_eq_nil in H2. destruct H2.
  apply simple_nat_leq in H0; try easy.
  apply simple_nat_leq_1 in H1; try easy. rewrite H0. rewrite H1.
  eauto.
  apply app_eq_nil in H. destruct H.
  apply app_eq_nil in H2. destruct H2.
  apply simple_nat_leq in H0; try easy.
  apply simple_nat_leq_1 in H1; try easy. rewrite H0. rewrite H1.
  eauto.
  apply app_eq_nil in H. destruct H.
  apply app_eq_nil in H2. destruct H2.
  apply simple_nat_leq in H0; try easy.
  apply simple_nat_leq_1 in H1; try easy. rewrite H0. rewrite H1.
  eauto.
Qed.

Lemma subtype_simple: forall D t t', simple_type t -> subtype D empty_theta t' t -> simple_type t'.
Proof with (try eauto with ty; try easy).
  intros. remember empty_theta as Q.
  induction H0; unfold simple_type in *; intros; simpl in *; subst...
  eapply subtype_core_simple; eauto.
Admitted.

Lemma subtype_simple_1: forall D t t', simple_type t' -> subtype D empty_theta t' t -> simple_type t.
Proof with (try eauto with ty; try easy).
  intros. remember empty_theta as Q.
  induction H0; unfold simple_type in *; intros; simpl in *; subst...
  eapply subtype_core_simple; eauto.
Admitted.

Lemma eq_subtype_simple: forall D t t', simple_type t -> eq_subtype D empty_theta t' t -> simple_type t'.
Proof.
  intros. destruct H0. destruct H0. eapply subtype_simple in H1; eauto.
  eapply type_eq_simple in H0; eauto.
Qed.

Lemma stack_consist_wt: forall D m s s', stack_consist D s s' -> stack_wt D m s -> stack_wt D m s'.
Proof.
  intros. unfold stack_consist, stack_wt in *. intros.
  destruct H as [X1 [X2 X3]].
  assert (Stack.In x s'). exists (v,t). easy.
  apply X1 in H as X5. destruct X5. destruct x0.
  specialize (or_nt_ptr t0) as X4. destruct X4.
  apply H0 in H2 as X6.
  apply X3 with (t' := t) (v' := v) in H2; try easy. destruct H2; subst.
  destruct X6 as [B1 [B2 B3]].
  split. eapply eq_subtype_word; eauto.
  split. eapply eq_subtype_type_wf; eauto.
  eapply eq_subtype_simple; eauto.
  apply H0 in H2 as X5.
  apply X2 in H2; eauto.
  apply Stack.mapsto_always_same with (v1 := (z, t0)) in H1; eauto. inv H1. easy. 
Qed. 

#[export] Hint Resolve stack_consist_refl : ty.

Lemma step_stack_consist: forall D F M e M' r,
       step D F M e M' r -> stack_consist D (fst M) (fst M').
Proof with (eauto with ty; try easy).
  intros. induction H; simpl in *...
  unfold stack_consist in *.
  split. intros. admit. admit. admit.
Admitted.

Lemma simple_subst_bound_same: forall t x v, freeBoundVars t = [] -> subst_bound t x v = t.
Proof with (try eauto with ty; try easy).
  induction t;intros;simpl in *... 
Qed.

Lemma simple_subst_type_same: forall t x v, simple_type t -> subst_type t x v = t.
Proof with (try eauto with ty; try easy).
  induction t;intros;simpl in *... rewrite IHt; try easy.
  unfold simple_type in H. simpl in *.
  apply app_eq_nil in H. destruct H.
  apply app_eq_nil in H0. destruct H0.
  rewrite simple_subst_bound_same; try easy.
  rewrite simple_subst_bound_same; try easy.
  rewrite IHt; try easy.
  unfold simple_type in H. simpl in *.
  apply app_eq_nil in H. destruct H.
  apply app_eq_nil in H0. destruct H0.
  rewrite simple_subst_bound_same; try easy.
  rewrite simple_subst_bound_same; try easy.
  rewrite IHt; try easy.
Qed.


Ltac find_Hstep :=
  match goal with
  | [H : step _ _ _ _ _ _ |- _] =>
      let Hstep := fresh "Hstep" in
      rename H into Hstep
  end.

Ltac solve_step :=
  match goal with
  | [Hstep : step _ _ _ _ _ _ |- _] =>
      (* Leave [Hstep] there for goal information *)
      inversion Hstep; subst; rename Hstep into _Hstep
  end; 
  try solve [cbn in *; subst; congruence];
  repeat match goal with
    | [H : in_hole _ _ = _ |- _ ] => inv H
    end.

Section GeneralProp.
  Variable D : structdef.
  Variable F : FEnv.
  Variable cm : mode.

  Lemma lit_are_nf : forall R s n t,
      ~ exists R' s' m' r, reduce D F cm (s, R) (ELit n t) m' (s', R') r.
  Proof.
   intros. intros H. destruct H as [R' [s' [m' [r X1]]]].
   remember (ELit n t) as q. inv X1; simpl in *.
   destruct E; try congruence; try solve [solve_step].
   destruct E; try congruence; try solve [solve_step].
   destruct E; try congruence; try solve [solve_step].
   destruct E;simpl in *; inv H1;try easy.
  Qed.
  (* intros R s n t Contra. *)
  (* destruct Contra as [R' [ s' [ m [ r Contra ] ] ] ]. *)
  (* inv Contra; find_Hstep; destruct E; cbn in *; subst; *)
  (*   try solve [inv Hstep; congruence]. *)
  (*  inv Hstep. *)
  (* Qed. *)

End GeneralProp.


Section FunctionProp.
  Lemma gen_arg_env_good : forall tvl enva, exists env, gen_arg_env enva tvl env.
  Proof.
    intros.
    induction tvl. exists enva. subst. constructor.
    destruct IHtvl.
    destruct a.
    exists (Env.add v t x).
    constructor. easy.
  Qed.
(*
  Lemma sub_domain_grow : forall env S x t,
      sub_domain env S -> sub_domain (Env.add x t env) (x::S).
  Proof with auto.
    intros.
    unfold sub_domain in *.
    intros.
    unfold Env.In,Env.Raw.PX.In in H0.
    destruct H0.
    unfold Stack.In,Stack.Raw.PX.In.
    destruct (Nat.eq_dec x x0).
    + subst. simpl. left. easy.
    + apply Env.add_3 in H0...
      assert (Env.In x0 env)... 
      unfold Env.In,Env.Raw.PX.In.
      exists x1...
      apply H in H1. simpl. right. easy.
  Qed.

  Lemma sub_domain_grows : forall tvl es env env' s s' e e',
      gen_arg_env env tvl env' -> eval_el s es tvl e e' -> sub_domain env s ->
      sub_domain env' s'.
  Abort.
*)
  (* Proof with auto. *)
  (*   induction tvl; intros * Henv Heval Hsub. *)
  (*   + inv Heval. inv Henv. *)
  (*   induction tvl; intros; inv H0; inv H... *)
  (*   apply sub_domain_grow. *)
  (*   exact (IHtvl _ env env'0 s s'0 AS H7 H8 H1) . *)
  (* Qed. *)
End FunctionProp.

Section TypeProp.
  Variable D : structdef.
  Variable F : FEnv.
  Variable Q : theta.

  Lemma eval_bound_simple: forall s b b',
       eval_bound s b = Some b' -> (exists n, b' = Num n).
  Proof.
   intros. unfold eval_bound,simple_bound in *. destruct b.
   inv H. exists z. easy.
   destruct (Stack.find (elt:=Z * type) v s) eqn:eq1. destruct p.
   inv H. exists ((z0 + z)%Z). easy.
   inv H.
  Qed.

  Lemma not_in_empty {A : Type}: forall (l:list A), (forall x, ~ In x l) -> l = [].
  Proof.
   induction l;intros; simpl in *. easy.
   specialize (H a).
   apply not_or_and in H.
   destruct H. easy.
  Qed.

  Lemma eval_type_bound_simple:
     forall m s t t', type_wf D m t -> eval_type_bound s t t' -> simple_type t'.
  Proof.
    intros.
    unfold simple_type in *.
    generalize dependent m.
    induction H0;intros;simpl in *; try easy.
    inv H.
    rewrite (IHeval_type_bound c); try easy.
    rewrite (IHeval_type_bound m); try easy.
    inv H2.
    apply eval_bound_simple in H as X1.
    apply eval_bound_simple in H0 as X2.
    destruct X1; subst. destruct X2; subst.
    simpl in *. 
    rewrite (IHeval_type_bound m); try easy.
    inv H2.
    apply eval_bound_simple in H as X1.
    apply eval_bound_simple in H0 as X2.
    destruct X1; subst. destruct X2; subst.
    simpl in *. 
    rewrite (IHeval_type_bound m); try easy.
    inv H.
    apply not_in_empty. intros.
    intros R.
    apply ListSet.set_diff_iff in R.
    destruct R.
    apply H7 in H. easy.
  Qed.

  Lemma eval_bound_valid:
     forall env s b, stack_wf D Q env s -> well_bound_in env b -> (exists b', eval_bound s b = Some b').
  Proof.
   intros. 
   unfold stack_wf, well_bound_in,eval_bound in *.
   destruct b. exists (Num z). easy.
   destruct (Stack.find (elt:=Z * type) v s) eqn:eq1. destruct p.
   exists ((Num (z0 + z))). easy.
   specialize (H0 v). simpl in H0.
   assert (v = v \/ False). left. easy.
   apply H0 in H1. apply H in H1. destruct H1 as [va [ta [X1 X2]]].
   inv X1. destruct H1. inv H2. inv H3. inv H1.
   apply Stack.find_1 in X2.
   rewrite eq1 in X2. easy.
  Qed.

  Lemma eval_type_bound_valid:
     forall env s t, stack_wf D Q env s -> well_type_bound_in env t -> (exists t', eval_type_bound s t t').
  Proof.
    intros.
    induction t;intros;simpl in *; try easy.
    exists TNat. constructor.
    apply IHt in H0. destruct H0.
    exists (TPtr m x). constructor. easy.
    exists (TStruct s0). constructor.
    unfold well_type_bound_in in *.
    specialize (eval_bound_valid env s b H) as X1.
    assert (well_bound_in env b).
    unfold well_bound_in in *.
    intros. apply H0. simpl.
    apply in_app_iff. left. easy.
    apply X1 in H1. destruct H1.
    specialize (eval_bound_valid env s b0 H) as X2.
    assert (well_bound_in env b0).
    unfold well_bound_in in *.
    intros. apply H0. simpl.
    apply in_app_iff. right.
    apply in_app_iff. left. easy.
    apply X2 in H2. destruct H2.
    assert ((forall x : var,
       In x (freeTypeVars t) -> Env.MapsTo (elt:=type) x TNat env)).
    intros.
    apply H0.
    apply in_app_iff. right.
    apply in_app_iff. right. easy.
    apply IHt in H3. destruct H3.
    exists (TArray x x0 x1). constructor; easy.
    unfold well_type_bound_in in *.
    specialize (eval_bound_valid env s b H) as X1.
    assert (well_bound_in env b).
    unfold well_bound_in in *.
    intros. apply H0. simpl.
    apply in_app_iff. left. easy.
    apply X1 in H1. destruct H1.
    specialize (eval_bound_valid env s b0 H) as X2.
    assert (well_bound_in env b0).
    unfold well_bound_in in *.
    intros. apply H0. simpl.
    apply in_app_iff. right.
    apply in_app_iff. left. easy.
    apply X2 in H2. destruct H2.
    assert ((forall x : var,
       In x (freeTypeVars t) -> Env.MapsTo (elt:=type) x TNat env)).
    intros.
    apply H0.
    apply in_app_iff. right.
    apply in_app_iff. right. easy.
    apply IHt in H3. destruct H3.
    exists (TNTArray x x0 x1). constructor; easy.
    exists ((TFun l t l0)). constructor.
  Qed.

  Lemma eval_type_bound_idempotent : forall s t,
      simple_type t ->
      eval_type_bound s t t.
  Proof with auto.
    induction t using type_ind';intros;unfold simple_type in *;simpl in *; try easy.
    constructor.
    constructor. apply IHt. easy.
    constructor.
    apply app_eq_nil in H. destruct H.
    apply app_eq_nil in H0. destruct H0.
    constructor.
    unfold eval_bound.
    destruct b. easy. simpl in *. inv H.
    unfold eval_bound.
    destruct b0. easy. simpl in *. inv H0.
    apply IHt;try easy.
    apply app_eq_nil in H. destruct H.
    apply app_eq_nil in H0. destruct H0.
    constructor.
    unfold eval_bound.
    destruct b. easy. simpl in *. inv H.
    unfold eval_bound.
    destruct b0. easy. simpl in *. inv H0.
    apply IHt;try easy.
    constructor.
  Qed.

  Lemma eval_type_bound_preserve : forall s t t' t'',
      eval_type_bound s t t' -> eval_type_bound s t t'' -> t' = t''.
  Proof with auto.
    intros. generalize dependent t''. induction H; intros; try easy... inv H0. easy.
    inv H0. apply IHeval_type_bound in H4; try easy. subst. easy.
    inv H2. rewrite H in H6. rewrite H0 in H8. inv H6. inv H8.
    apply IHeval_type_bound in H9; try easy; subst. easy.
    inv H2. rewrite H in H6. rewrite H0 in H8. inv H6. inv H8.
    apply IHeval_type_bound in H9; try easy; subst. easy.
    inv H0. easy. inv H0. easy.
  Qed.

(*
  Lemma simple_eval_bound : forall s b,
      eval_bound s b = b -> exists n, b = Num n.
  Proof.
    destruct b; intros; eauto.
    inv H. solveopt in *. destruct p. congruence.
  Qed.

  Lemma simple_eval_type_bound : forall s t,
      eval_type_bound s t = t <-> simple_type t.
  Proof with (cbn; auto).
    intros s t. split.
    - Ltac solveleft :=
        cbn in *; repeat solveopt in *;
        repeat
          (match goal with
           | [H : eval_bound _ ?b = Some ?b |- _] =>
               let n := fresh "n" in
               let H' := fresh "Hbd" in
               destruct (simple_eval_bound _ _ H) as [n [=]]; clear H; subst
           end); constructor; intuition.
      intros Hbd. induction t using type_ind'; solveleft.
      induction l; constructor; inv H; solveleft.
    - Ltac solveright :=
        cbn in *; auto;
        repeat (match goal with
                | [ H : _ = Some ?b |- _] =>
                    rewrite H
                end);
        auto.
      intros. induction t using type_ind'; inv H; intuition; solveright.
      induction l... inv H0; inv H5; intuition.
      solveopt in *.  solveright.
  Qed.

  Lemma checked_wt_tainted_lit : forall R S Htnt t v env,
      simple_type t ->  
      well_typed_lit_tainted D F Q Htnt empty_scope v t ->
      well_typed D F S R env Q Checked (ELit v t) t.
  Proof.
    intros * Hsimple Hwt; eapply TyLitChecked.
    apply simple_eval_type_bound; assumption.
    inv Hwt; constructor; congruence.
  Qed.
*)
End TypeProp.

#[export] Hint Resolve eval_type_bound_idempotent : ty.
#[export] Hint Resolve eval_type_bound_simple : ty.

Local Open Scope Z_scope.

Lemma cardinal_not_in :
  forall H, heap_wf H -> ~ Heap.In (Z.of_nat(Heap.cardinal H) + 1) H.
Proof.
  intros H Hwf Contra.
  destruct (Hwf (Z.of_nat(Heap.cardinal H) + 1)) as [H1 H2].
  specialize (H2 Contra).
  lia.
Qed.

Module HeapFacts := WFacts_fun Heap.E Heap.
Module HeapProp := WProperties_fun Heap.E Heap.
Lemma cardinal_plus_one :
  forall (H : heap) n v, ~ Heap.In n H ->
                         (Z.of_nat(Heap.cardinal (Heap.add n v H)) = Z.of_nat(Heap.cardinal H) + 1).
Proof.
  intros H n v NotIn.
  pose proof HeapProp.cardinal_2 as Fact.
  specialize (Fact _ H (Heap.add n v H) n v NotIn).
  assert (Hyp: HeapProp.Add n v H (Heap.add n v H)).
  {
    intros y.
    auto.
  } 
  specialize (Fact Hyp).
  lia.
Qed.

Lemma length_nth : forall {A} (l : list A) (k : nat),
    0 <= Z.of_nat(k) < Z.of_nat(length l) -> exists n, nth_error l k = Some n.
Proof.
  intros A l; induction l; intros k Hyp; simpl in *.
  - lia.
  - destruct k; simpl.
    + exists a; eauto.
    + assert (H: 0 <= Z.of_nat(k) < Z.of_nat(S k)). {split.
      *lia. 
      *zify. lia. }
     destruct H. assert (H2: Z.of_nat(k) < Z.of_nat (length l)). {zify. lia. }
     assert (H3: 0 <= Z.of_nat(k) < Z.of_nat (length l)). {split; assumption. }
     apply (IHl k H3).
Qed.      

Lemma nth_length : forall {A} (l : list A) (k : nat) n,
    nth_error l k = Some n -> 0 <= Z.of_nat(k) < Z.of_nat(length l).
Proof.
  intros A l; induction l; intros k n Hyp; simpl in *.
  - apply nth_error_In in Hyp; inv Hyp.
  - destruct k; simpl in *.
    +zify. lia.
    + edestruct IHl; eauto. zify.
      lia.
Qed.

Lemma Zlength_nth : forall {A} (l : list A) (z : Z),
0 <= z < Z.of_nat(length l) -> exists n, nth_error l (Z.to_nat z) = Some n.
Proof.
intros. destruct z.
  -apply (length_nth l (Z.to_nat 0) H).
  -assert (H1: Z.of_nat (Z.to_nat (Z.pos p)) = (Z.pos p)).
    {destruct (Z.pos p) eqn:P; inv P.
      +simpl. rewrite positive_nat_Z. reflexivity. }
   rewrite <- H1 in H. apply (length_nth l (Z.to_nat (Z.pos p)) H).
  -exfalso. inv H. apply H0. simpl. reflexivity.
Qed.

Lemma replicate_length : forall (n : nat) (T : type),
(length (replicate n T)) = n.
Proof.
  intros n T. induction n.
    -simpl. reflexivity.
    -simpl. rewrite IHn. reflexivity.
Qed.

Lemma eval_type_bound_word_type: forall s t t', eval_type_bound s t t' 
    -> word_type t -> word_type t'.
Proof.
  intros. 
  induction H; intros;simpl in *; try easy.
Qed.

Lemma eval_type_bound_type_wf: forall D s m t t', eval_type_bound s t t' 
    -> type_wf D m t -> type_wf D m t'.
Proof.
  intros. generalize dependent m.
  induction H; intros;simpl in *; try easy.
  inv H0. constructor. eauto.
  apply WFTPtrUnChecked; eauto.
  inv H2. constructor;eauto.
  eapply eval_type_bound_word_type; eauto.
  inv H2. constructor;eauto.
  eapply eval_type_bound_word_type; eauto.
Qed.

Lemma eval_type_bound_tfun: forall s t t', eval_type_bound s t t' 
    -> ~ is_fun_type t -> ~ is_fun_type t'.
Proof.
  intros. induction H; intros;simpl in *; try easy.
Qed.

Lemma type_eq_not_checked: forall Q t t', type_eq Q t t' 
    -> ~ is_checked t' -> ~ is_checked t.
Proof.
  intros. induction H; intros;simpl in *; try easy.
  intros R. inv R. assert (is_checked (TPtr Checked t2)). constructor. easy.
Qed.

Lemma subtype_core_not_check: forall D Q t t', subtype_core D Q t t' 
    -> ~ is_checked t' -> ~ is_checked t.
Proof.
  intros. inv H; eauto.
  intros R. inv R. 
  assert (is_checked (TPtr Checked (TArray l h t0))). constructor. easy.
  intros R. inv R.
  assert (is_checked (TPtr Checked t0)). constructor. easy.
  intros R. inv R.
  assert (is_checked (TPtr Checked t0)). constructor. easy.
  intros R. inv R.
  assert (is_checked (TPtr Checked (TArray l' h' t0))). constructor. easy.
  intros R. inv R.
  assert (is_checked (TPtr Checked (TArray l' h' t0))). constructor. easy.
  intros R. inv R.
  assert (is_checked (TPtr Checked (TNTArray l' h' t0))). constructor. easy.
  intros R. inv R.
  assert (is_checked (TPtr Checked TNat)). constructor. easy.
  intros R. inv R.
  assert (is_checked (TPtr Checked (TArray l h TNat))). constructor. easy.
Qed.

Lemma subtype_not_check: forall D Q t t', subtype D Q t t' 
    -> ~ is_checked t' -> ~ is_checked t.
Proof.
  intros. inv H; try easy. apply subtype_core_not_check in H1; try easy.
  assert (is_checked (TPtr Checked (TFun xl t'0 tl'))).
  constructor. easy.
Qed.

Lemma eq_subtype_not_checked: forall D Q t t', eq_subtype D Q t t' 
    -> ~ is_checked t' -> ~ is_checked t.
Proof.
  intros. destruct H as [ta [X1 X2]].
  apply subtype_not_check in X2; try easy.
  apply type_eq_not_checked in X1; try easy.
Qed.

Lemma eq_subtype_not_checked_1: forall D Q t t', eq_subtype D Q t' t 
    -> ~ is_checked t' -> ~ is_checked t.
Proof.
Admitted.

Lemma eq_subtype_is_checked_1: forall D Q t t', eq_subtype D Q t' t 
    -> is_checked t' -> is_checked t.
Proof.
Admitted.

Lemma eval_type_bound_not_checked: forall s t t', eval_type_bound s t t' 
    -> ~ is_checked t -> ~ is_checked t'.
Proof.
  intros. induction H; intros;simpl in *; try easy.
  intros R. inv R. assert (is_checked (TPtr Checked t)). constructor. easy.
Qed.

Lemma eval_type_bound_is_checked: forall s t t', eval_type_bound s t t' 
    -> is_checked t -> is_checked t'.
Proof.
  intros. induction H; intros;simpl in *; try easy.
  inv H0. constructor.
Qed.

Lemma type_eq_well_bound: forall Q env t t', 
    (forall x, Theta.In x Q <-> Env.MapsTo x TNat env) ->
     nat_leq Q t t' -> freeBoundVars t = [] -> well_bound_in env t'.
Proof.
  intros. induction H0; try easy.
  apply Theta.mapsto_in in H0. apply H in H0.
  unfold well_bound_in. intros.
  simpl in *. destruct H3. subst. easy. easy.
  apply Theta.mapsto_in in H0. apply H in H0.
  unfold well_bound_in in *. intros. simpl in *.
  destruct H3;subst. easy. easy.
  apply Theta.mapsto_in in H0. apply H in H0.
  unfold well_bound_in in *. intros. simpl in *.
  destruct H3;subst. easy. easy.
Qed.

Lemma type_eq_well_bound_1: forall Q env t t', 
    (forall x, Theta.In x Q <-> Env.MapsTo x TNat env) ->
     nat_leq Q t t' -> freeBoundVars t' = [] -> well_bound_in env t.
Proof.
  intros. induction H0; try easy.
  apply Theta.mapsto_in in H0. apply H in H0.
  unfold well_bound_in. intros.
  simpl in *. destruct H3. subst. easy. easy.
  apply Theta.mapsto_in in H0. apply H in H0.
  unfold well_bound_in in *. intros. simpl in *.
  destruct H3;subst. easy. easy.
Qed.

Lemma type_eq_well_type_bound: forall Q env t t', 
    (forall x, Theta.In x Q <-> Env.MapsTo x TNat env) ->
     type_eq Q t t' -> simple_type t -> well_type_bound_in env t'.
Proof.
  intros. induction H0; try easy.
  unfold simple_type in *. simpl in H1.
  apply IHtype_eq in H1.
  unfold well_type_bound_in in *.
  intros. apply H1. simpl in *. easy.
  unfold simple_type in *. simpl in *.
  apply app_eq_nil in H1. destruct H1. apply app_eq_nil in H4. destruct H4.
  apply IHtype_eq in H5. unfold well_type_bound_in in *.
  intros ; simpl in *.
  apply in_app_iff in H6. destruct H6.
  inv H2. apply type_eq_well_bound with (env := env) in H7; try easy.
  unfold well_bound_in in *. apply H7 in H6. easy.
  apply in_app_iff in H6. destruct H6.
  inv H3. apply type_eq_well_bound with (env := env) in H7; try easy.
  unfold well_bound_in in *. apply H7 in H6. easy.
  apply H5 in H6. easy.
  unfold simple_type in *. simpl in *.
  apply app_eq_nil in H1. destruct H1. apply app_eq_nil in H4. destruct H4.
  apply IHtype_eq in H5. unfold well_type_bound_in in *.
  intros ; simpl in *.
  apply in_app_iff in H6. destruct H6.
  inv H2. apply type_eq_well_bound with (env := env) in H7; try easy.
  unfold well_bound_in in *. apply H7 in H6. easy.
  apply in_app_iff in H6. destruct H6.
  inv H3. apply type_eq_well_bound with (env := env) in H7; try easy.
  unfold well_bound_in in *. apply H7 in H6. easy.
  apply H5 in H6. easy.
  unfold simple_type in *.
  unfold well_type_bound_in in *. intros. rewrite H1 in H0. simpl in *. easy.
Qed.


Lemma subtype_core_well_type_bound: forall D Q env t t', 
    (forall x, Theta.In x Q <-> Env.MapsTo x TNat env) ->
     subtype_core D Q t t' -> simple_type t -> well_type_bound_in env t'.
Proof.
  intros. inv H0; try easy.
  unfold simple_type in *.
  unfold well_type_bound_in in *. intros. rewrite H1 in H0. simpl in *. easy.
  unfold well_type_bound_in in *. intros; simpl in *. 
  apply in_app_iff in H0. destruct H0.
  apply type_eq_well_bound with (env := env) in H3; try easy.
  apply H3. easy.
  apply in_app_iff in H0. destruct H0.
  apply type_eq_well_bound_1 with (env := env) in H4; try easy.
  apply H4. easy.
  unfold simple_type in *. simpl in H1. rewrite H1 in H0. simpl in *. easy.
  unfold simple_type in *. simpl in *.
  apply app_eq_nil in H1. destruct H1.
  apply app_eq_nil in H1. destruct H1.
  unfold well_type_bound_in. intros.
  simpl in *.
  rewrite H5 in H6. simpl in *. easy.
  unfold simple_type in *. simpl in *.
  apply app_eq_nil in H1. destruct H1.
  apply app_eq_nil in H1. destruct H1.
  unfold well_type_bound_in. intros.
  simpl in *.
  rewrite H5 in H6. simpl in *. easy.
  unfold simple_type in *. simpl in *.
  apply app_eq_nil in H1. destruct H1.
  apply app_eq_nil in H1. destruct H1.
  unfold well_type_bound_in. intros.
  simpl in *.
  apply in_app_iff in H5. destruct H5.
  apply type_eq_well_bound with (env := env) in H2; try easy.
  apply H2. easy.
  apply in_app_iff in H5. destruct H5.
  apply type_eq_well_bound_1 with (env := env) in H3; try easy.
  apply H3. easy.
  rewrite H4 in H5. simpl in *. easy.
  unfold simple_type in *. simpl in *.
  apply app_eq_nil in H1. destruct H1.
  apply app_eq_nil in H1. destruct H1.
  unfold well_type_bound_in. intros.
  simpl in *.
  apply in_app_iff in H5. destruct H5.
  apply type_eq_well_bound with (env := env) in H2; try easy.
  apply H2. easy.
  apply in_app_iff in H5. destruct H5.
  apply type_eq_well_bound_1 with (env := env) in H3; try easy.
  apply H3. easy.
  rewrite H4 in H5. simpl in *. easy.
  unfold simple_type in *. simpl in *.
  apply app_eq_nil in H1. destruct H1.
  apply app_eq_nil in H1. destruct H1.
  unfold well_type_bound_in. intros.
  simpl in *.
  apply in_app_iff in H5. destruct H5.
  apply type_eq_well_bound with (env := env) in H2; try easy.
  apply H2. easy.
  apply in_app_iff in H5. destruct H5.
  apply type_eq_well_bound_1 with (env := env) in H3; try easy.
  apply H3. easy.
  rewrite H4 in H5. simpl in *. easy.
  unfold well_type_bound_in. intros.
  simpl in *.
  apply in_app_iff in H0. destruct H0.
  apply type_eq_well_bound with (env := env) in H4; try easy.
  apply H4. easy.
  apply in_app_iff in H0. destruct H0.
  apply type_eq_well_bound_1 with (env := env) in H5; try easy.
  apply H5. easy. simpl in *. easy.
Qed.


Lemma subtype_well_type_bound: forall D Q env t t', 
    (forall x, Theta.In x Q <-> Env.MapsTo x TNat env) ->
     subtype D Q t t' -> simple_type t -> well_type_bound_in env t'.
Proof.
  intros. inv H0; simpl in *; try easy.
  eapply subtype_core_well_type_bound; eauto.
  assert (subtype D empty_theta (TPtr Checked (TFun xl t0 tl)) (TPtr Checked (TFun xl t'0 tl'))).
  apply SubTypeFunChecked; try easy.
  apply subtype_simple_1 in H0; try easy.
  unfold simple_type in H0.
  unfold well_type_bound_in in *. intros.
  rewrite H0 in H6. simpl in *. easy.
  assert (subtype D empty_theta (TPtr Tainted (TFun xl t0 tl)) (TPtr Tainted (TFun xl t'0 tl'))).
  apply SubTypeFunTainted; try easy.
  apply subtype_simple_1 in H0; try easy.
  unfold simple_type in H0.
  unfold well_type_bound_in in *. intros.
  rewrite H0 in H6. simpl in *. easy.
Qed.

Lemma eq_subtype_well_type_bound: forall D Q env t t', 
    (forall x, Theta.In x Q <-> Env.MapsTo x TNat env) ->
     eq_subtype D Q t t' -> simple_type t -> well_type_bound_in env t'.
Proof.
  intros.
  inv H0 as [ta [X1 X2]].
  apply type_eq_well_type_bound with (env := env) in X1; try easy.
Admitted.

Lemma eq_subtype_empty: forall D Q env t t', 
    (forall x, Theta.In x Q <-> Env.MapsTo x TNat env) ->
     eq_subtype D Q t t' -> simple_type t -> simple_type t' -> eq_subtype D empty_theta t t'.
Proof.
  intros.
Admitted.

Lemma well_type_eval_leq: forall D Q env s w w',
      eval_bound s w = Some w' -> well_bound_in env w -> stack_wf D Q env s ->
    (forall x n, Stack.MapsTo x (n,TNat) s -> Theta.MapsTo x (NumEq (Num n)) Q)
      -> nat_eq Q w' w.
Proof.
  intros. 
  unfold eval_bound in *. destruct w. inv H.
  split. constructor. easy. constructor. easy.
  destruct (Stack.find (elt:=Z * type) v s) eqn:eq1. destruct p.
  inv H. split. apply Stack.find_2 in eq1.
  unfold well_bound_in in *.
  specialize (H0 v). simpl in *. assert (v = v \/ False). left. easy.
  apply H0 in H. apply H1 in H. destruct H. destruct H. destruct H.
  destruct H. destruct H. apply subtype_nat in H4. subst. inv H.
  apply Stack.mapsto_always_same with (v1 := (x, TNat)) in eq1. inv eq1. 
  eapply nat_leq_var_2; eauto. constructor. lia. easy.
  apply Stack.find_2 in eq1.
  unfold well_bound_in in *.
  specialize (H0 v). simpl in *. assert (v = v \/ False). left. easy.
  apply H0 in H. apply H1 in H. destruct H. destruct H. destruct H.
  destruct H. destruct H. apply subtype_nat in H4. subst. inv H.
  apply Stack.mapsto_always_same with (v1 := (x, TNat)) in eq1. inv eq1. 
  eapply nat_leq_var_1; eauto. constructor. lia. easy. inv H.
Qed.


Lemma well_type_eval_type_eq: forall D Q env s w w',
      eval_type_bound s w w' -> well_type_bound_in env w -> stack_wf D Q env s ->
    (forall x n, Stack.MapsTo x (n,TNat) s -> Theta.MapsTo x (NumEq (Num n)) Q)
      -> type_eq Q w' w.
Proof.
  intros. generalize dependent Q. generalize dependent env.
  induction H; intros;simpl in *; eauto.
  constructor.
  constructor. eapply IHeval_type_bound; eauto.
  constructor. unfold well_type_bound_in in *.
  eapply IHeval_type_bound; eauto. intros. apply H2.
  simpl. apply in_app_iff. right. apply in_app_iff. right. easy.
  eapply well_type_eval_leq; try easy; eauto.
  unfold well_type_bound_in in *. unfold well_bound_in in *. intros. apply H2.
  simpl. apply in_app_iff. left. easy.
  eapply well_type_eval_leq; try easy; eauto.
  unfold well_type_bound_in in *. unfold well_bound_in in *. intros. apply H2.
  simpl. apply in_app_iff. right. apply in_app_iff. left. easy.
  constructor. unfold well_type_bound_in in *.
  eapply IHeval_type_bound; eauto. intros. apply H2.
  simpl. apply in_app_iff. right. apply in_app_iff. right. easy.
  eapply well_type_eval_leq; try easy; eauto.
  unfold well_type_bound_in in *. unfold well_bound_in in *. intros. apply H2.
  simpl. apply in_app_iff. left. easy.
  eapply well_type_eval_leq; try easy; eauto.
  unfold well_type_bound_in in *. unfold well_bound_in in *. intros. apply H2.
  simpl. apply in_app_iff. right. apply in_app_iff. left. easy.
  constructor. constructor.
Qed.

Local Close Scope Z_scope.
