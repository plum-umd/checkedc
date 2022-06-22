(** * CheckedCProp : Checked C Model Properties *)

From CHKC Require Import
  Coqlib
  Tactics
  ListUtil
  Map
  CheckedCDef.

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
      well_typed_lit_checked D F Q H empty_scope n t->
      well_typed_lit_checked D F Q H' empty_scope n t.


  Definition heap_well_typed_checked (H:heap)
    (n:Z) (t:type) :=
    simple_type t -> well_typed_lit_checked D F Q H empty_scope n t.

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

  Inductive heap_wt (H:heap) : expression -> Prop :=
  | HtLit : forall n t, heap_well_typed_checked H n t -> heap_wt H (ELit n t)
  | HtVar : forall x, heap_wt H (EVar x)
  | HtStrlen : forall x, heap_wt H (EStrlen x)
  | HtCall : forall f el, heap_wt_args H el -> heap_wt H (ECall f el)
  | HtRet : forall x old a e, heap_wt H e -> heap_wt H (ERet x old a e)
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

  Definition heap_wt_all (H : heap) :=
    forall x n t,
      Heap.MapsTo x (n,t) H ->
      word_type t /\ type_wf D m t /\ simple_type t
      /\ well_typed_lit_checked D F Q H empty_scope n t.

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
      R = (Hchk, Htnt) -> heap_wf Hchk /\ heap_wf Htnt.

  (** Types on the stack agree with those on the rheap. *)
  Definition stack_rheap_consistent (R : real_heap) S :=
    forall Hchk Htnt x n t,
      R = (Hchk, Htnt) ->
      Stack.MapsTo x (n,t) S ->
      (well_typed_lit_checked D F Q Hchk empty_scope n t
       \/ well_typed_lit_tainted D F Q Htnt empty_scope n t).


  (* FIXME: hold the definition for now *)
  Definition rheap_consistent (R' : real_heap) (R : real_heap) : Prop :=
    forall Hchk' Htnt' Hchk Htnt,
      R' = (Hchk', Htnt') -> R = (Hchk, Htnt) -> 
      heap_consistent_checked D F Q Hchk' Hchk.

  Lemma rheap_consistent_refl : forall R, rheap_consistent R R.
  Proof.
    unfold rheap_consistent. intros [H1 H2] * E1 E2.  inv E1. inv E2.
    unfold heap_consistent_checked. intuition.
  Qed.
  
  Definition rheap_wt_all (R : real_heap) := forall Hchk Htnt,
    R = (Hchk, Htnt) ->
    heap_wt_all D F Q m Hchk.

End RealHeapProp.

#[export] Hint Unfold rheap_wf : heap.
#[export] Hint Unfold stack_rheap_consistent : heap.
#[export] Hint Unfold rheap_consistent : heap.
#[export] Hint Unfold rheap_wt_all : heap.
#[export] Hint Resolve rheap_consistent_refl : heap.

  
Section StackProp.
  Variable D : structdef.
  Variable F : FEnv.
  Variable Q : theta.
  Variable m : mode.

  Definition stack_wf env s := forall x t,
      Env.MapsTo x t env -> exists v t' t'',
        eval_type_bound s t = Some t'
        /\ subtype D Q t'' t' 
        /\ Stack.MapsTo x (v, t'') s.
End StackProp. 


Ltac find_Hstep :=
  match goal with
  | [H : step _ _ _ _ _ _ |- _] =>
      let Hstep := fresh "Hstep" in
      rename H into Hstep
  end.


Section GeneralProp.
  Variable D : structdef.
  Variable F : FEnv.

  Lemma lit_are_nf : forall R s n t,
      ~ exists R' s' m r, reduce D F (s, R) (ELit n t) m (s', R') r.
  Proof.
  Abort.
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


  Lemma sub_domain_grow : forall env S x v t,
      sub_domain env S -> sub_domain (Env.add x t env) (Stack.add x v S).
  Proof with auto.
    intros.
    unfold sub_domain in *.
    intros.
    unfold Env.In,Env.Raw.PX.In in H0.
    destruct H0.
    unfold Stack.In,Stack.Raw.PX.In.
    destruct (Nat.eq_dec x x0).
    + subst.
      exists v.
      apply Stack.add_1...
    + apply Env.add_3 in H0...
      assert (Env.In x0 env)... 
      unfold Env.In,Env.Raw.PX.In.
      exists x1...
      apply H in H1.
      unfold Stack.In,Stack.Raw.PX.In in H1.
      destruct H1.
      exists x2.
      apply Stack.add_2...
  Qed.

  Lemma sub_domain_grows : forall tvl es env env' s s' e e',
      gen_arg_env env tvl env' -> eval_el s es tvl e e' -> sub_domain env s ->
      sub_domain env' s'.
  Abort.
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

  Lemma eval_bound_idempotent : forall s b b', 
      eval_bound s b = Some b' ->
      eval_bound s b' = Some b'.
  Proof with auto.
    induction b; intros b' Hbound; inv Hbound; try solve [cbn; auto].
    cbn. solveopt in *. destruct p. inv H2. cbn...
  Qed.

  Lemma eval_type_bound_idempotent : forall s t t',
      eval_type_bound s t = Some t' ->
      eval_type_bound s t' = Some t'.
  Proof with auto.
    induction t using type_ind'; intros * Hbound; inv Hbound; try solve [cbn; auto].
    + solveopt in H0. cbn; rewrite (IHt t0)...
    + repeat solveopt in *. cbn. rewrite IHt...
      do 2 erewrite (eval_bound_idempotent); eauto.
    + repeat solveopt in *. cbn. rewrite (IHt t0)...
      do 2 erewrite (eval_bound_idempotent); eauto.
    + repeat solveopt in *. cbn. rewrite (IHt t0)...
      erewrite (eval_bound_idempotent); eauto.
      generalize dependent l0; induction l; intros l' Hfold.
      * inv Hfold...
      * cbn in Hfold. solveopt in Hfold. solveopt in H3.
        inv H as [| _a _l Hcons HAll].
        specialize (IHl HAll l0 eq_refl). solveopt in IHl.
        specialize (Hcons t1 H2).
        cbn. rewrite IHl0. rewrite Hcons. reflexivity.
  Qed.

  Lemma simple_eval_bound : forall s b,
      eval_bound s b = Some b -> exists n, b = Num n.
  Proof.
    destruct b; intros; eauto.
    inv H. solveopt in *. destruct p. congruence.
  Qed.

  Lemma simple_eval_type_bound : forall s t,
      eval_type_bound s t = Some t <-> simple_type t.
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
End TypeProp.

#[export] Hint Resolve eval_type_bound_idempotent : ty.
#[export] Hint Resolve <- simple_eval_type_bound : ty.
#[export] Hint Resolve -> simple_eval_type_bound : ty.
