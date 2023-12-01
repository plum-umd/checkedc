From CHKC Require Import
  Coqlib
  Tactics
  ListUtil
  Map
  CheckedCDef
  CheckedCProp.
  (* CheckedCPropDev. *)

Require Export Bool.
Require Export Arith.
Require Export Psatz.
Require Export Program.
Require Export List.
Require Import ZArith.
Require Import ZArith.BinIntDef.
Require Export BinNums.
Require Import BinPos BinNat.

#[global]
Hint Unfold rheap_consistent : Preservation.
Hint Unfold heap_consistent_checked : Preservation.
Local Open Scope Z_scope.

Ltac solve_ctxt :=
  match goal with
  | [E : ctxt |- _] =>
      destruct E; try congruence; solve_step
  end.  
         

Lemma step_implies_reduces : forall D F cm H s e H' s' r E m,
    mode_of' E cm = m ->
    @step D F (s,H) e (s',H') r ->
    reduces D F cm (s,H) (in_hole e E) m.
Proof.
  intros.
  destruct r.
  exists (s',H'), (RExpr (in_hole e0 E)).
  constructor; easy.
  exists (s',H'), RNull.
  constructor; easy.
  exists (s',H'), RBounds.
  constructor; easy.
Qed.

Lemma step_implies_reduces_1 : forall D F cm H s e H' s' E m e',
    mode_of' E cm = m ->
    @step D F (s,H) e (s',H') (RExpr e') ->
    reduce D F cm (s,H) (in_hole e E) m (s',H') (RExpr (in_hole e' E)).
Proof.
  intros.
  constructor; easy.
Qed.

Hint Resolve step_implies_reduces : Preservation.

(*
Lemma reduces_congruence : forall D F H s e0 e,
    (exists E, in_hole e0 E = e) ->
    reduces D F (s,H) e0 ->
    reduces D F (s,H) e.
Proof.
  intros.
  destruct H0 as [ E Hhole ].
  destruct H1 as [ m' [ H' [r  HRed ]] ].
  inv HRed as [ ? e0' ? ? e0'' E' | ? e0' ? ? E' | ? e0' ? ? E'  | ? e0' ? ? E' ]; rewrite compose_correct; eauto 20.
Admitted.

Hint Resolve reduces_congruence : Preservation.
*)
Lemma eval_arg_lit: forall S e t e', eval_arg S e t e' -> exists n, e' = ELit n t.
Proof.
 intros. inv H. exists n; easy. exists n; easy.
Qed.


Lemma eval_arg_same: forall S e t t' v v', eval_arg S e t (ELit v t) -> eval_arg S e t' (ELit v' t') -> v = v'.
Proof.
 intros. inv H. inv H0. easy.
 inv H0. apply Stack.mapsto_always_same with (v1 := (v', t'1)) in H4; try easy.
 inv H4. easy.
Qed.

Lemma eval_el_vl_1: forall S es tvl xl e t ea ta, 
   eval_el S es tvl xl e t ea ta -> 
   (exists vl, Forall2 (fun e v => forall t v', eval_arg S e t (ELit v' t) -> v = v') es vl).
Proof.
  intros.
  induction H;simpl in *.
  exists []. constructor.
  apply eval_arg_lit in H0 as X1.
  destruct X1; subst.
  destruct IHeval_el. exists (x0::x1).
  constructor;try easy.
  intros. apply eval_arg_same with (t := t) (v := x0) in H3; try easy.
  destruct IHeval_el. exists (v::x0).
  constructor;try easy.
  intros. apply eval_arg_same with (t := TNat) (v := v) in H2; try easy.
Qed.

Lemma eval_el_vl: forall S es vl tvl xl e t ea ta, 
   Forall2 (fun e v => forall t v', eval_arg S e t (ELit v' t) -> v = v') es vl ->
   eval_el S es tvl xl e t ea ta -> eval_vl vl tvl xl e t ea ta.
Proof.
  intros.
  generalize dependent tvl.
  generalize dependent xl.
  generalize dependent e.
  generalize dependent t.
  generalize dependent ea.
  generalize dependent ta.
  induction H; intros;simpl in *.
  inv H0. constructor.
  inv H1.
  apply  eval_arg_lit in H5 as X1. destruct X1; subst.
  apply H  in H5 as X2. subst.
  apply eval_vl_many_1; try easy.
  apply IHForall2; try easy.
  apply H  in H4 as X2. subst.
  apply eval_vl_many_2; try easy.
  apply IHForall2; try easy.
Qed.

Lemma split_zero {A B:Type}: forall (l:list (A*B)), (List.split l).2 = [] -> l = [].
Proof.
  induction l;intros;simpl in *; try easy.
  destruct a. 
  destruct (split l) eqn:eq1. inv H.
Qed.

(*
Lemma well_typed_arg_ex: forall D U Q H env m e t x t',
                  @well_typed_arg D U Q H env m e t
           -> @well_typed_arg D U Q H (Env.add x t' env) m e t.
Proof.
  intros. inv H0; simpl in *.
  constructor; try easy.
  constructor.
Qed.
*)

(*
Lemma well_typed_args_ex: forall D U H Q env m es vl xl t ta x t',
                  @well_typed_args D U H Q env m es vl xl t ta
           -> @well_typed_args D U H Q (Env.add x t' env) m es vl xl t ta.
Proof.
  intros. induction H0; simpl in *.
  constructor.
  constructor; try easy.
  inv H1. constructor; try easy.
  apply ArgLitUnchecked; try easy.
  destruct (Nat.eq_dec x x0); subst.
  constructor; try easy.
Admitted.
*)

Lemma well_typed_eval_vs: forall D F Q R env S m es xl ts tvl t t' ta ta' e ea,
    (forall x n, Stack.MapsTo x (n,TNat) S -> Theta.MapsTo x (NumEq (Num n)) Q) ->
    subtype empty_theta t' t ->
    Forall2 (subtype empty_theta) ts ((split tvl).2) ->
    @well_typed_args D F R Q env m es ts xl t ta -> eval_el S es tvl xl e t' ea ta'
    -> eq_subtype Q ta' ta.
Proof.
 intros.
  generalize dependent e.
  generalize dependent t'.
  generalize dependent ea.
  generalize dependent ta'.
  generalize dependent tvl.
 induction H2;intros;simpl in *.
 inv H3. unfold eq_subtype. exists ta'. split. 
 apply type_eq_refl.
 apply subtype_q_empty.  easy.
 inv H5. inv H3.
 destruct (split tvl0) eqn:eq1. inv H7.
 apply IHwell_typed_args with (tvl := tvl0) (ea := ea') (t' := t') (e:= e0); try easy.
 rewrite eq1; easy.
 inv H3.
 destruct (split tvl0) eqn:eq1. inv H7.
 apply subtype_nat in H9; subst. easy.
 inv H5.
 inv H3.
 destruct (split tvl0) eqn:eq1. inv H7.
 apply subtype_nat_1 in H10; subst. easy.
 inv H3.
 destruct (split tvl0) eqn:eq1. inv H7.
 apply IHwell_typed_args with (tvl := (map (fun a : var * type => (a.1, subst_type a.2 x (Num v)))
           tvl0)) (t' := (subst_type t' x (Num v))) (ea := ea') (e:= e0); try easy.
 assert ((split
     (map (fun a : var * type => (a.1, subst_type a.2 x (Num v)))
        tvl0)).2 = map (fun a => subst_type a x (Num v)) l0).
 clear H H0 H1 H2 IHwell_typed_args H4 H15 H16 H8 H9.
 assert (l0 = (split tvl0).2). rewrite eq1. easy. rewrite H. clear eq1 H.
 induction tvl0;intros;simpl in *; try easy.
 destruct (split
     (map (fun a : var * type => (a.1, subst_type a.2 x (Num v)))
        tvl0)) eqn:eq3.
 destruct a. destruct (split tvl0) eqn:eq2.
 simpl in *. rewrite  IHtvl0. easy.
 rewrite H3. clear H3.
 clear H2 IHwell_typed_args H16 H8 H4 eq1.
 induction H9; simpl in *. constructor.
 constructor; try easy.
 inv H15. simpl in *. inv H0.
Admitted.


Lemma well_typed_args_sub : forall D F Q R R' env m es xl ts tlb t tb ta, 
       rheap_consistent D F R' R ->
       subtype empty_theta tb t ->
       Forall2 (subtype empty_theta) ts tlb ->
       @well_typed_args D F R Q env m es ts xl t ta -> 
       (exists ta', @well_typed_args D F R' Q env m es tlb xl tb ta' /\ subtype Q ta' ta). 
Proof.
Admitted.

Lemma well_typed_arg_consist: forall D Q F R env env' m e t, env_consistent Q env env'
      -> well_typed_arg D F R Q env m e t ->
         well_typed_arg D F R Q env' m e t.
Proof.
 intros. inv H0. constructor; try easy.
 constructor; try easy.
 destruct H as [X1 [X2 X3]].
 destruct (X1 x).
 assert (Env.In x env). exists t'. easy.
 apply H in H3. destruct H3.
 assert (is_nt_ptr t' \/ ~ is_nt_ptr t').
 destruct t'; try (right ; easy).
 destruct t'; try (right; easy). left; easy.
 destruct H4.
 apply X3 with (t' := x0) in H1; try easy.
 apply ArgVar with (t' := x0); try easy.
 assert (eq_subtype Q x0 t').
 unfold eq_subtype. exists x0. split. apply type_eq_refl. constructor. easy.
 apply eq_subtype_trans with (t2 := t'); try easy.
 apply X2 in H1; try easy. apply ArgVar with (t' := t'); try easy.
Qed.

Lemma well_typed_args_consist: forall D Q F R env env' m es ts xl t ta, env_consistent Q env env'
      -> @well_typed_args D F R Q env m es ts xl t ta ->
        @well_typed_args D F R Q env' m es ts xl t ta.
Proof.
 intros. induction H0; simpl in *; try easy.
 constructor. constructor; try easy.
 apply well_typed_arg_consist with (env0 := env); try easy.
 auto.
 apply args_many_2 with (b0 := b);try easy.
 apply well_typed_arg_consist with (env0 := env) ; try easy.
 auto.
Qed.

Lemma replicate_gt_eq : forall x t, 0 < x -> Z.of_nat (length (Zreplicate (x) t)) = x.
Proof.
  intros.
  unfold Zreplicate.
  destruct x eqn:eq1. lia.
  simpl. 
  rewrite replicate_length. lia.
  lia.
Qed.

Lemma replicate_nth_anti {A:Type} : forall (n k : nat) (x : A),
    (k < n)%nat -> nth_error (replicate n x) k = Some x.
  Proof.
    induction n; intros k w H.
    - lia.
    - simpl. destruct k. simpl. easy.
      assert (k < n)%nat by lia.
      apply IHn with (x := w) in H0. simpl. easy. 
Qed.

Lemma well_typed_arg_q_eq: forall D Q Q' F R env m e t, Theta.Equal Q Q' 
      -> well_typed_arg D F R Q env m e t ->
         well_typed_arg D F R Q' env m e t.
Proof.
 intros. inv H0. constructor; try easy. 
 eapply eq_subtype_q_eq; eauto.
 apply ArgLitUnchecked; try easy.
 eapply eq_subtype_q_eq; eauto.
 apply ArgVar with (t' := t'); try easy.
 eapply eq_subtype_q_eq; eauto.
Qed.

Lemma well_typed_args_q_eq: forall D Q Q' F R env m es ts vs t ta, Theta.Equal Q Q' 
      -> @well_typed_args D F R Q env m es ts vs t ta ->
         @well_typed_args D F R Q' env m es ts vs t ta.
Proof.
 intros. induction H0; try easy.
 constructor. constructor; try easy.
 eapply well_typed_arg_q_eq; eauto.
 eapply args_many_2; try easy. apply H0.
 eapply well_typed_arg_q_eq; eauto.
 apply IHwell_typed_args.
Qed.

Lemma well_typed_q_eq: forall D F R env Q Q' m e t, Theta.Equal Q Q' 
   -> well_typed D F R env Q m e t -> well_typed D F R env Q' m e t.
Proof.
  intros. generalize dependent Q'. induction H0; intros; auto.
  constructor; try easy.
  apply TyLitTainted; try easy.
  apply TyVar with (t := t); try easy.
  apply subtype_core_q_eq with (Q := Q); try easy.
  eapply TyCall; try easy. apply H. apply IHwell_typed. easy.
  eapply well_typed_args_q_eq; eauto.
  eapply TyStrlen. apply H. easy.
(*
  eapply TyLetStrlen. apply H. apply H0.
  apply IHwell_typed.
  apply equiv_theta_add. easy. easy.
*)
  apply TyLetNat; eauto.
  apply IHwell_typed2.
  apply equiv_theta_add. easy.
  intros R1. destruct R1.
  eapply Theta.mapsto_equal with (s2 := Q) in H2.
  assert (Theta.In x Q). exists x0. easy. easy.
  apply ThetaFacts.Equal_sym. easy.
  eapply TyLet; eauto.
  intros R1. destruct R1. apply Theta.mapsto_equal with (s2 := Q) in H2; try easy.
  assert (Theta.In x Q). exists x0. easy. easy.
  eapply TyRetTNat; eauto.
  intros R1. destruct R1. apply Theta.mapsto_equal with (s2 := Q) in H2.
  assert (Theta.In x Q). exists x0. easy. easy.
  apply ThetaFacts.Equal_sym. easy.
  apply IHwell_typed.
  apply equiv_theta_add. easy.
  apply TyRetChecked; eauto.
  intros R1. destruct R1. apply Theta.mapsto_equal with (s2 := Q) in H4; try easy.
  assert (Theta.In x Q). exists x0. easy. easy.
  apply TyRet; eauto.
  intros R1. destruct R1. apply Theta.mapsto_equal with (s2 := Q) in H5; try easy.
  assert (Theta.In x Q). exists x0. easy. easy.
  apply TyPlus; eauto.
  eapply TyFieldAddr; eauto.
  eapply TyMalloc; eauto.
  eapply TyUnchecked; eauto.
  apply eq_subtype_q_eq with (Q := Q); try easy.
  eapply Tychecked; eauto.
  apply eq_subtype_q_eq with (Q := Q); try easy.
  eapply TyCast1; eauto.
  eapply TyCast2; eauto.
  eapply eq_subtype_q_eq; eauto.
  eapply TyDynCast1; eauto.
  apply type_eq_q_eq with (Q := Q); try easy.
  eapply TyDynCast2; eauto.
  apply type_eq_q_eq with (Q := Q); try easy.
  eapply TyDynCast3; eauto.
  apply type_eq_q_eq with (Q := Q); try easy.
  eapply TyDynCast4; eauto.
  apply type_eq_q_eq with (Q := Q); try easy.
  eapply TyDeref; eauto.
  eapply TyIndex1; eauto.
  eapply TyIndex2; eauto.
  eapply TyAssign1; eauto.
  eapply subtype_q_eq; eauto.
  eapply TyAssign2; eauto.
  eapply subtype_q_eq; eauto.
  eapply TyAssign3; eauto.
  eapply subtype_q_eq; eauto.
  eapply TyIndexAssign1; eauto.
  eapply subtype_q_eq; eauto.
  eapply TyIndexAssign2; eauto.
  eapply subtype_q_eq; eauto.
  eapply TyIfDef; eauto.
  eapply subtype_q_eq; eauto.
  eapply TyIfDefNT; eauto.
  eapply TyIf; eauto.
Qed.

Lemma well_typed_arg_q_conv: forall D Q F R env m e t x v, 0 <= v
      -> well_typed_arg D F R (Theta.add x GeZero Q) env m e t ->
         well_typed_arg D F R (Theta.add x (NumEq (Num v)) Q) env m e t.
Proof.
 intros. inv H0. constructor; try easy. 
 eapply eq_subtype_q_conv; eauto.
 apply ArgLitUnchecked; try easy.
 eapply eq_subtype_q_conv; eauto.
 apply ArgVar with (t' := t'); try easy.
 eapply eq_subtype_q_conv; eauto.
Qed.

Lemma well_typed_args_q_conv: forall D Q F R env m es ts vs t ta x v, 0 <= v 
      -> @well_typed_args D F R (Theta.add x GeZero Q) env m es ts vs t ta ->
         @well_typed_args D F R (Theta.add x (NumEq (Num v)) Q) env m es ts vs t ta.
Proof.
 intros. induction H0; try easy.
 constructor. constructor; try easy.
 eapply well_typed_arg_q_conv; eauto.
 eapply args_many_2; try easy. apply H0.
 eapply well_typed_arg_q_conv; eauto.
 apply IHwell_typed_args.
Qed.

Lemma well_typed_q_conv: forall D F R env Q m e t x v, 0 <= v ->
   well_typed D F R env (Theta.add x GeZero Q) m e t -> well_typed D F R env (Theta.add x (NumEq (Num v)) Q) m e t.
Proof.
  intros. remember (Theta.add x GeZero Q) as Q'.
  assert (Theta.Equal Q' (Theta.add x GeZero Q)).
  subst. easy. clear HeqQ'.
  generalize dependent Q. induction H0; intros; subst;eauto.
  constructor; try easy.
  apply TyLitTainted; try easy.
  apply TyVar with (t := t); try easy.
  apply subtype_core_q_conv;try easy.
  apply subtype_core_q_eq with (Q := Q); try easy.
  eapply TyCall; try easy. apply H0. apply IHwell_typed. easy.
  apply well_typed_args_q_eq with (Q' := (@Theta.add theta_elem x GeZero Q0)) in H3; try easy.
  eapply well_typed_args_q_conv; eauto.
  eapply TyStrlen. apply H0. easy.
(*
  eapply TyLetStrlen. apply H0. apply H1.
  destruct (Nat.eq_dec x0 x); subst.
  assert (Theta.Equal (Theta.add x GeZero Q) (Theta.add x GeZero (Theta.add x GeZero Q0))).
  apply equiv_theta_add. easy.
  apply well_typed_q_eq with 
        (Q' := (Theta.add x GeZero (Theta.add x GeZero Q0))) in H2; try easy.
  apply well_typed_q_eq with 
        (Q := (Theta.add x GeZero (Theta.add x GeZero Q0))); try easy.
  apply theta_shadow_eq with (t2 := GeZero); try easy.
  apply ThetaFacts.Equal_sym.
  apply theta_shadow_eq with (t2 := (NumEq v)); try easy.
  apply well_typed_q_eq with 
        (Q := (Theta.add x (NumEq v) (Theta.add x0 GeZero Q0))); try easy.
  apply theta_neq_commute; try easy. lia.
  apply well_typed_q_eq with 
        (Q' := (Theta.add x GeZero (Theta.add x0 GeZero Q0))) in H2; try easy.
  apply IHwell_typed.
  assert (Theta.Equal (Theta.add x0 GeZero Q) (Theta.add x0 GeZero (Theta.add x GeZero Q0))).
  apply equiv_theta_add. easy.
  apply ThetaFacts.Equal_trans with (m' := (Theta.add x0 GeZero (Theta.add x GeZero Q0))); try easy.
  apply theta_neq_commute. lia.
  assert (Theta.Equal (Theta.add x0 GeZero Q) (Theta.add x0 GeZero (Theta.add x GeZero Q0))).
  apply equiv_theta_add. easy.
  apply ThetaFacts.Equal_trans with (m' := (Theta.add x0 GeZero (Theta.add x GeZero Q0))); try easy.
  apply theta_neq_commute. lia.
  easy.
*)
  apply TyLetNat; eauto.
  assert (Theta.Equal (Theta.add x0 (NumEq b) Q) (Theta.add x0 (NumEq b) (Theta.add x GeZero Q0))).
  apply equiv_theta_add. easy.
  destruct (Nat.eq_dec x0 x); subst.
  apply well_typed_q_eq with 
        (Q := (Theta.add x (NumEq b) Q)); try easy.
  apply ThetaFacts.Equal_trans with (m' := (Theta.add x (NumEq b) (Theta.add x GeZero Q0))); try easy.
  apply theta_shadow_eq with (t2 := GeZero); try easy.
  apply ThetaFacts.Equal_sym. apply theta_shadow.
  apply well_typed_q_eq with 
        (Q := (Theta.add x (NumEq (Num v)) (Theta.add x0 (NumEq b) Q0))); try easy.
  apply theta_neq_commute. lia.
  apply IHwell_typed2.
  apply ThetaFacts.Equal_trans with (m' := (Theta.add x0 (NumEq b) (Theta.add x GeZero Q0))); try easy.
  apply theta_neq_commute. lia.
  intros R1. destruct R1.
  destruct (Nat.eq_dec x0 x); subst.
  assert (Theta.In x Q).
  exists GeZero.
  apply Theta.mapsto_equal with (s1 := (Theta.add x GeZero Q0)); try easy.
  apply Theta.add_1. easy. easy.
  assert (~ Theta.In x0 Q0).
  intros R2. destruct R2.
  apply Theta.add_2 with (x := x) (e' := GeZero) in H4; try easy.
  apply Theta.mapsto_equal with (s2 := Q) in H4; try easy. 
  assert (Theta.In x0 Q). exists x2. easy. easy. lia.
  apply Theta.add_3 in H3.
  assert (Theta.In x0 Q0). exists x1. easy. easy. lia.
  eapply TyLet; eauto.
  intros R1. destruct R1.
  destruct (Nat.eq_dec x0 x); subst.
  assert (Theta.In x Q).
  exists GeZero.
  apply Theta.mapsto_equal with (s1 := (Theta.add x GeZero Q0)); try easy.
  apply Theta.add_1. easy. easy.
  assert (~ Theta.In x0 Q0).
  intros R2. destruct R2.
  apply Theta.add_2 with (x := x) (e' := GeZero) in H4; try easy.
  apply Theta.mapsto_equal with (s2 := Q) in H4; try easy. 
  assert (Theta.In x0 Q). exists x2. easy. easy. lia.
  apply Theta.add_3 in H3.
  assert (Theta.In x0 Q0). exists x1. easy. easy. lia.
  eapply TyRetTNat; eauto.
  intros R1. destruct R1.
  destruct (Nat.eq_dec x0 x); subst.
  assert (Theta.In x Q).
  exists GeZero.
  apply Theta.mapsto_equal with (s1 := (Theta.add x GeZero Q0)); try easy.
  apply Theta.add_1. easy. easy.
  assert (~ Theta.In x0 Q0).
  intros R2. destruct R2.
  apply Theta.add_2 with (x := x) (e' := GeZero) in H4; try easy.
  apply Theta.mapsto_equal with (s2 := Q) in H4; try easy. 
  assert (Theta.In x0 Q). exists x2. easy. easy. lia.
  apply Theta.add_3 in H3.
  assert (Theta.In x0 Q0). exists x1. easy. easy. lia.
  assert (Theta.Equal (Theta.add x0 (NumEq (Num na)) Q) (Theta.add x0 (NumEq (Num na)) (Theta.add x GeZero Q0))).
  apply equiv_theta_add. easy.
  destruct (Nat.eq_dec x0 x); subst.
  apply well_typed_q_eq with 
        (Q := (Theta.add x (NumEq (Num na)) Q)); try easy.
  apply ThetaFacts.Equal_trans with (m' := (Theta.add x (NumEq (Num na)) (Theta.add x GeZero Q0))); try easy.
  apply theta_shadow_eq with (t2 := GeZero); try easy.
  apply ThetaFacts.Equal_sym. apply theta_shadow.
  apply well_typed_q_eq with 
        (Q := (Theta.add x (NumEq (Num v)) (Theta.add x0 (NumEq (Num na)) Q0))); try easy.
  apply theta_neq_commute. lia.
  apply IHwell_typed.
  apply ThetaFacts.Equal_trans with (m' := (Theta.add x0 (NumEq (Num na)) (Theta.add x GeZero Q0))); try easy.
  apply theta_neq_commute. lia.
  apply TyRetChecked; eauto.
  intros R1. destruct R1.
  destruct (Nat.eq_dec x0 x); subst.
  assert (Theta.In x Q).
  exists GeZero.
  apply Theta.mapsto_equal with (s1 := (Theta.add x GeZero Q0)); try easy.
  apply Theta.add_1. easy. easy.
  assert (~ Theta.In x0 Q0).
  intros R2. destruct R2.
  apply Theta.add_2 with (x := x) (e' := GeZero) in H6; try easy.
  apply Theta.mapsto_equal with (s2 := Q) in H6; try easy. 
  assert (Theta.In x0 Q). exists x2. easy. easy. lia.
  apply Theta.add_3 in H5.
  assert (Theta.In x0 Q0). exists x1. easy. easy. lia.
  apply TyRet; eauto.
  intros R1. destruct R1.
  destruct (Nat.eq_dec x0 x); subst.
  assert (Theta.In x Q).
  exists GeZero.
  apply Theta.mapsto_equal with (s1 := (Theta.add x GeZero Q0)); try easy.
  apply Theta.add_1. easy. easy.
  assert (~ Theta.In x0 Q0).
  intros R2. destruct R2.
  apply Theta.add_2 with (x := x) (e' := GeZero) in H7; try easy.
  apply Theta.mapsto_equal with (s2 := Q) in H7; try easy. 
  assert (Theta.In x0 Q). exists x2. easy. easy. lia.
  apply Theta.add_3 in H6.
  assert (Theta.In x0 Q0). exists x1. easy. easy. lia.
  apply TyPlus; eauto.
  eapply TyFieldAddr; eauto.
  eapply TyMalloc; eauto.
  eapply TyUnchecked; eauto.
  apply eq_subtype_q_eq with (Q' := (Theta.add x GeZero Q0)) in H2; try easy.
  apply eq_subtype_q_conv; try easy.
  eapply Tychecked; eauto.
  apply eq_subtype_q_eq with (Q' := (Theta.add x GeZero Q0)) in H2; try easy.
  apply eq_subtype_q_conv; try easy.
  eapply TyCast1; eauto.
  eapply TyCast2; eauto.
  apply eq_subtype_q_eq with (Q' := (Theta.add x GeZero Q0)) in H2; try easy.
  eapply eq_subtype_q_conv; eauto.
  eapply TyDynCast1; eauto.
  apply type_eq_q_eq with (Q' := (Theta.add x GeZero Q0)) in H2; try easy.
  apply type_eq_q_conv; try easy.
  eapply TyDynCast2; eauto.
  apply type_eq_q_eq with (Q' := (Theta.add x GeZero Q0)) in H1; try easy.
  apply type_eq_q_conv; try easy.
  eapply TyDynCast3; eauto.
  apply type_eq_q_eq with (Q' := (Theta.add x GeZero Q0)) in H1; try easy.
  apply type_eq_q_conv; try easy.
  eapply TyDynCast4; eauto.
  apply type_eq_q_eq with (Q' := (Theta.add x GeZero Q0)) in H1; try easy.
  apply type_eq_q_conv; try easy.
  eapply TyDeref; eauto.
  eapply TyIndex1; eauto.
  eapply TyIndex2; eauto.
  eapply TyAssign1; eauto.
  apply subtype_q_eq with (Q' := (Theta.add x GeZero Q0)) in H0; try easy.
  eapply subtype_q_conv; eauto.
  eapply TyAssign2; eauto.
  apply subtype_q_eq with (Q' := (Theta.add x GeZero Q0)) in H2; try easy.
  eapply subtype_q_conv; eauto.
  eapply TyAssign3; eauto.
  apply subtype_q_eq with (Q' := (Theta.add x GeZero Q0)) in H2; try easy.
  eapply subtype_q_conv; eauto.
  eapply TyIndexAssign1; eauto.
  apply subtype_q_eq with (Q' := (Theta.add x GeZero Q0)) in H2; try easy.
  eapply subtype_q_conv; eauto.
  eapply TyIndexAssign2; eauto.
  apply subtype_q_eq with (Q' := (Theta.add x GeZero Q0)) in H2; try easy.
  eapply subtype_q_conv; eauto.
  eapply TyIfDef; eauto.
  apply subtype_q_eq with (Q' := (Theta.add x GeZero Q0)) in H1; try easy.
  eapply subtype_q_conv; eauto.
  eapply TyIfDefNT; eauto.
  eapply TyIf; eauto.
Qed.

Lemma well_typed_q_real: forall D F R env Q m e t x y v, Theta.MapsTo y (NumEq (Num v)) Q ->
   well_typed D F R env (Theta.add x (NumEq (Var y 0)) Q) m e t 
         -> well_typed D F R env (Theta.add x (NumEq (Num v)) Q) m e t.
Proof.
Admitted.

Lemma well_typed_env_consist: forall D F R env env' Q m e t,
   env_consistent Q env env' ->
   well_typed D F R env Q m e t -> well_typed D F R env' Q m e t.
Proof.
  intros. generalize dependent env'.
  induction H0; intros; simpl in *; try easy.
  constructor;try easy.
  apply TyLitTainted; try easy.
  unfold env_consistent in *.
  destruct H1 as [X1 [X2 X3]].
  specialize (X1 x). destruct X1.
  specialize (or_nt_ptr t) as X4.
  destruct X4. assert (Env.In x env).
  exists t. easy. apply H1 in H4.
  destruct H4.
  apply X3 with (t' := x0) in H as X4; try easy. 
  apply TyVar with (t := x0); try easy.
  apply subtype_core_trans with (t1 := t); try easy.
  apply X2 in H; try easy.
  apply TyVar with (t := t); try easy.
  eapply TyCall; try easy. apply H.
  apply env_wf_consist with (Q := Q) (env0 := env); try easy.
  eauto. apply well_typed_args_consist with (env0 := env); try easy.
  unfold env_consistent in *.
  destruct H1 as [X1 [X2 X3]].
  specialize (X1 x).
  assert (Env.In x env). exists (TPtr m' (TNTArray h l t)). easy.
  apply X1 in H1. destruct H1.
  apply X3 with (t' := x0) in H; try easy. destruct H.
  apply subtype_core_nt in H; try easy. destruct H as [la [ha X4]]; subst.
  eapply TyStrlen; try easy. apply H1. easy. 
  eapply TyLetNat; try easy.
  apply  IHwell_typed1; try easy.
  apply IHwell_typed2; try easy.
Admitted.

Lemma well_typed_env_consist_1: forall D F R env Q m e t x v,
   Theta.MapsTo x (NumEq (Num v)) Q ->
   well_typed D F R env Q m e t -> well_typed D F R (subst_env env x (Num v)) Q m e t.
Proof.
  intros. 
  induction H0; intros; simpl in *; try easy.
  constructor;try easy.
  apply TyLitTainted; try easy.
  apply TyVar with (t := subst_type t x (Num v)); try easy.
  apply EnvFacts.map_mapsto_iff. exists t. easy.
Admitted.

Lemma well_typed_heap_consist: forall D F R R' env Q m e t,
   rheap_consistent D F R' R ->
   well_typed D F R env Q m e t -> well_typed D F R' env Q m e t.
Proof.
  intros.
  induction H0; intros; simpl in *; try easy.
  constructor;try easy.
  unfold rheap_consistent in *. destruct R. destruct R'.
  specialize (H h1 h2 h h0). unfold heap_consistent_checked in *.
  simpl in *. apply H; try easy.
  apply TyLitTainted; try easy.
  apply TyVar with (t := t); try easy.
  eapply TyCall; try easy. apply H0. apply IHwell_typed.
Admitted.


Lemma well_typed_env_grow: forall D F R env env' Q m e t,
   (forall x t t', Env.MapsTo x t env -> Env.MapsTo x t' env' -> eq_subtype Q t' t) ->
   well_typed D F R env Q m e t -> well_typed D F R env' Q m e t.
Proof.
  intros.
  induction H0; intros; simpl in *; try easy.
  constructor;try easy.
  apply TyLitTainted; try easy.
Admitted.

Lemma preservation_fieldaddr : forall (D : structdef) F H n T (fs : fields),
  @well_typed_lit_checked D F (fst H) empty_scope n (TPtr Checked (TStruct T)) ->
  forall i fi ti,
  n <> 0 ->
  StructDef.MapsTo T fs D ->
  Fields.MapsTo fi ti fs ->
  nth_error (Fields.this fs) i = Some (fi, ti) ->
  rheap_wf H ->
  structdef_wf D ->
  fields_wf D fs ->
  word_type ti ->
  @well_typed_lit_checked D F (fst H) empty_scope (n + (Z.of_nat i)) (TPtr Checked ti).
Proof.
  intros D F H n T fs HWT.
  inversion HWT;
  intros i fi ti Hn HS HF Hnth Hhwf HDwf Hfwf Hwt; eauto.
  - exfalso ; eauto.
  - easy.
  - inv H1.
  - inv H3. inv H9; try easy. inv H4.
    apply StructDef.find_1 in HS. rewrite HS in H3. inv H3.
    specialize (H8 (Z.of_nat i)).
    rewrite map_length in H8.
    assert (0 <= Z.of_nat i < 0 + Z.of_nat (length (Fields.elements (elt:=type) fs))).
    split. lia.
    rewrite Z.add_0_l.
    assert (i < (length (Fields.elements (elt:=type) fs)))%nat.
    apply nth_error_Some.
    assert (Hyp: Fields.this fs = Fields.elements fs) by auto.
    rewrite <- Hyp. rewrite Hnth. easy. lia.
    destruct (H8  H0) as [N' [T' [HNth [HMap HWT']]]]; subst.
    assert (Z.to_nat (Z.of_nat i - 0) = i) by lia.
    rewrite H3 in HNth. 
    assert (Hyp: Fields.this fs = Fields.elements fs) by auto.
    rewrite <- Hyp in HNth.
    apply map_nth_error with (f := snd) in Hnth. 
    rewrite Hnth in HNth. simpl in *. inv HNth.
    inv Hwt.
      * eapply TyLitC_C with (w := TNat); simpl in *; try easy.
        constructor. constructor.
        intros k Hk; simpl in *.
        assert (k = 0) by lia; subst.
        exists N'. exists TNat.
        repeat (split; eauto).
        rewrite Z.add_0_r; eauto. constructor.

Admitted.



Lemma well_typed_preserved : forall D F H t, heap_wf H ->
  @heap_consistent_checked D F (Heap.add (Z.of_nat(Heap.cardinal H) + 1) (0, t) H) H.
Proof.
  intros D F H t0 Hwf n t HT.
  induction HT using well_typed_lit_c_ind'; pose proof (cardinal_not_in H Hwf); eauto.
  eapply TyLitInt_C; eauto.
  eapply TyLitU_C; eauto.
  eapply TyLitZero_C; eauto.
  eapply TyLitFun_C; eauto.
  eapply TyLitRec_C; eauto.
  eapply TyLitC_C; eauto.
  unfold nt_array_prop in *.
  destruct t;try easy. destruct b0; try easy. destruct b1;try easy.
  destruct (n =? (Z.of_nat (Heap.cardinal (elt:=Z * type) H) + 1)) eqn:eq1.
  apply Z.eqb_eq in eq1; subst.
  exists 0,t0. split. easy.
  split. rewrite Z.add_0_r. apply Heap.add_1. easy.
  intros. lia.
  destruct H4 as [na [ta [X1 [X2 X3]]]];subst.
  apply Z.eqb_neq in eq1.
  exists na,ta. split. easy. split.
  apply Heap.add_2; try easy.
  intros R. rewrite <- R in X2.
  apply Heap.mapsto_in in X2. easy.
  intros. apply X3 in H4. destruct H4 as [nb [X4 X5]].
  exists nb. split. apply Heap.add_2; try lia.
  intros R. rewrite <- R in X4. apply Heap.mapsto_in in X4. easy.
  easy. easy.
  intros k HK.  
  destruct (H5 k HK) as [n' [t' [HNth [HMap [HWT1 HWT2]]]]].
  exists n'. exists t'.
  repeat split; eauto.
  apply Heap.add_2; eauto.
  intros R. rewrite <- R in HMap.
  apply Heap.mapsto_in in HMap. easy.
Qed.

Lemma heap_add_preserves_wf : forall H n v, heap_wf H ->
  heap_wf (Heap.add (Z.of_nat(Heap.cardinal H) + 1) (n, v) H).
Proof.
  intros H n v Hwf.
  split; intros; simpl; eauto.
  * rewrite cardinal_plus_one in H0.
    unfold heap_wf in *. intros R. apply Hwf in R. lia.
    destruct (addr =? Z.of_nat (Heap.cardinal (elt:=Z * type) H) + 1) eqn:eq1.
    apply Z.eqb_eq in eq1; subst.
    exists (n, v). apply Heap.add_1. easy.
    apply Z.eqb_neq in eq1.
    assert (0 < addr <= Z.of_nat (Heap.cardinal (elt:=Z * type) H)) by lia.
    apply Hwf in H1. destruct H1. exists x.
    apply Heap.add_2; try easy. lia.
  * apply HeapFacts.add_in_iff in H0.
    destruct H0; subst.
    rewrite cardinal_plus_one; try (zify; lia).
    intros R. apply Hwf in R. lia.
    rewrite cardinal_plus_one; try (zify; lia).
    intros R.
    apply Hwf in R. lia.
    apply Hwf in H0. lia.
Qed.

Lemma backwards_consistency :
  forall D F H' H v,
    @heap_consistent_checked D F H' (Heap.add (Z.of_nat(Heap.cardinal H) + 1) v H) ->
    heap_wf H ->
    @heap_consistent_checked D F H' H.
Proof.
  intros D F H' H v HC Hwf.
  intros n t HWT.
  eapply HC; eauto.
  induction HWT using well_typed_lit_c_ind'; pose proof (cardinal_not_in H Hwf); eauto.
  eapply TyLitInt_C; eauto.
  eapply TyLitU_C; eauto.
  eapply TyLitZero_C; eauto.
  eapply TyLitFun_C; eauto.
  eapply TyLitRec_C; eauto.
  eapply TyLitC_C; eauto.
  unfold nt_array_prop in *.
  destruct t;try easy. destruct b0; try easy. destruct b1;try easy.
  destruct H4 as [na [ta [X1 [X2 X3]]]].
  exists na,ta. split; try easy.
  split. apply Heap.add_2; try easy.
  intros R. rewrite <- R in X2.
  apply Heap.mapsto_in in X2. easy.
  intros. apply X3 in H4. destruct H4 as [nb [X4 X5]].
  exists nb. split. apply Heap.add_2; try easy.
  intros R. rewrite <- R in X4. apply Heap.mapsto_in in X4. easy.
  easy.
  intros k HK.  
  destruct (H5 k HK) as [n' [t' [HNth [HMap [HWT1 HWT2]]]]].
  exists n'. exists t'.
  repeat split; eauto.
  apply Heap.add_2; eauto.
  intros R. rewrite <- R in HMap.
  apply Heap.mapsto_in in HMap. easy.
Qed.

Lemma fold_preserves_consistency : forall l D F H ptr, heap_wf H ->
  let (_, H') :=
      fold_left
        (fun (acc : Z * heap) (t : type) =>
           let (sizeAcc, heapAcc) := acc in
           (sizeAcc + 1, Heap.add (sizeAcc + 1) (0, t) heapAcc))
        l
        (Z.of_nat(Heap.cardinal H), H) in
  Some ((Z.of_nat(Heap.cardinal H) + 1), H') = Some (ptr, H')
 ->
  @heap_consistent_checked D F H' H.
Proof.
  intro l; induction l; intros; simpl; eauto.
  intros. inv H1. unfold heap_consistent_checked. intuition.

  assert (Hwf : heap_wf (Heap.add (Z.of_nat(Heap.cardinal H) + 1) (0, a) H))
    by (apply heap_add_preserves_wf; auto).
  specialize (IHl D F (Heap.add (Z.of_nat(Heap.cardinal H) + 1) (0, a) H) (ptr + 1) Hwf).
  remember (Heap.add (Z.of_nat(Heap.cardinal H) + 1) (0, a) H) as H1.

  Set Printing All.
  remember ((fun (acc : prod Z heap) (t : type) =>
     match acc return (prod Z heap) with
     | pair sizeAcc heapAcc =>
         @pair Z (Heap.t (prod Z type)) (BinInt.Z.add sizeAcc (Zpos xH))
           (@Heap.add (prod Z type) (BinInt.Z.add sizeAcc (Zpos xH))
              (@pair Z type Z0 t) heapAcc)
     end) ) as fold_fun.
  Unset Printing All.
  clear Heqfold_fun. 
  assert (Z.of_nat(Heap.cardinal H1) = (Z.of_nat(Heap.cardinal H) + 1)).
  {
    subst; apply cardinal_plus_one; eauto.
    intro Contra. 
    destruct (H0 (Z.of_nat(Heap.cardinal H) + 1)) as [H1 H2].
    specialize (H2 Contra).
    lia.
  } 
  rewrite H2 in IHl.

  assert (HEq:
      (  fold_left fold_fun l
            (@pair Z heap (Z.of_nat(Heap.cardinal H) + 1) H1) ) =
      (    @fold_left (prod Z heap) type fold_fun l
                      (@pair Z (Heap.t (prod Z type)) (Z.of_nat(Heap.cardinal H) + 1) H1))
    ). {zify. eauto. }


  rewrite HEq in IHl.


  match goal with
  | |- (match ?X with _ => _ end) => destruct X
  end.
  intro Hyp.
  inv Hyp.
   
  assert (Z.of_nat(Heap.cardinal H) + 1 + 1 = Z.of_nat((Heap.cardinal H + 1)) + 1) by (zify; lia).
  rewrite H1 in IHl.

  specialize (IHl eq_refl).

  eapply backwards_consistency; eauto.
Qed.


Lemma fold_summary : forall l H ptr,
  heap_wf H ->
  let (_, H') :=
      fold_left
        (fun (acc : Z * heap) (t : type) =>
           let (sizeAcc, heapAcc) := acc in
           (sizeAcc + 1, Heap.add (sizeAcc + 1) (0, t) heapAcc))
        l
        (Z.of_nat(Heap.cardinal  H), H) in
  Some (Z.of_nat(Heap.cardinal  H)+ 1, H') = Some (ptr, H') ->
  heap_wf H' /\
  ptr = Z.of_nat(Heap.cardinal  H) + 1 /\
  (Heap.cardinal  H') = ((Heap.cardinal H) + length l)%nat /\
  (forall (k : nat) v,
      (0 <= k < (length l))%nat -> nth_error l k = Some v ->
               Heap.MapsTo (Z.of_nat(Heap.cardinal  H) + 1 + Z.of_nat(k)) (0,v) H') /\
  forall x v, Heap.MapsTo x v H -> Heap.MapsTo x v H'.                                               
Proof.
  intro l; induction l; simpl; intros H ptr Hwf.
  - intros Eq. inv Eq; repeat (split; eauto).
    intros k v Contra _.
    inv Contra.
    inv H1.
  - remember 
      (fun (acc : prod Z heap) (t : type) =>
         match acc return (prod Z heap) with
         | pair sizeAcc heapAcc =>
           @pair Z (Heap.t (prod Z type)) (sizeAcc + 1)
                 (@Heap.add (prod Z type) (sizeAcc + 1)
                            (@pair Z type 0 t) heapAcc)
         end) as fold_fun.
    clear Heqfold_fun.
    assert (Hwf' : heap_wf (Heap.add (Z.of_nat(Heap.cardinal H) + 1) (0, a) H))
      by (apply heap_add_preserves_wf; eauto).
    specialize (IHl (Heap.add (Z.of_nat(Heap.cardinal H) + 1) (0, a) H) (ptr + 1) Hwf').
    remember (Heap.add (Z.of_nat(Heap.cardinal H) +1) (0, a) H) as H1.
    assert (Z.of_nat(Heap.cardinal H1) = Z.of_nat(Heap.cardinal H) + 1).
    {
      subst; apply cardinal_plus_one; eauto.
      intro Contra.
      destruct (Hwf (Z.of_nat(Heap.cardinal H) + 1)) as [H1 H2].
      specialize (H2 Contra).
      lia.
    } 
    rewrite H0 in IHl.

    assert (HEq:
        (  @fold_left (prod Z heap) type fold_fun l
              (@pair Z heap ((Z.of_nat(@Heap.cardinal (prod Z type) H)) + 1) H1) ) =
        (    @fold_left (prod Z heap) type fold_fun l
                        (@pair Z (Heap.t (prod Z type)) (Z.of_nat(@Heap.cardinal (prod Z type) H) + 1) H1))
      ) by auto.
   
    rewrite HEq in IHl.

  Set Printing All.

  remember (
    @fold_left (prod Z heap) type fold_fun l
               (@pair Z (Heap.t (prod Z type)) ( Z.of_nat(@Heap.cardinal (prod Z type) H) + 1) H1)
    ) as fold_call.

  Unset Printing All.

  clear Heqfold_call.
  destruct fold_call.
  intro Hyp.
  inv Hyp.

  assert (Z.of_nat(Heap.cardinal H) + 1 + 1 = ((Z.of_nat(Heap.cardinal H)) + 1) + 1) by lia.
  (*rewrite H1 in IHl.*)
  destruct (IHl eq_refl) as [hwf [Card [Card' [HField HMap]]]].

  repeat (split; eauto).
  + lia.
  + intros k v Hk HF.
    destruct k.
    * simpl in *.
      inv HF.
      specialize (HMap (Z.of_nat(Heap.cardinal H) + 1) (0,v)).
      rewrite Z.add_0_r.
      eapply HMap.
      apply Heap.add_1; eauto.
    * simpl in *.
      assert (HS: (Z.of_nat(Heap.cardinal H) + 1 + Z.pos (Pos.of_succ_nat k)) = (Z.of_nat(Heap.cardinal H) + 1 + 1 + Z.of_nat(k))). {
      zify. lia. }
      rewrite HS.
      apply HField; eauto.
      lia.
  + intros x v HM.
    eapply HMap.
    apply Heap.add_2; eauto.
    intro Contra.
    destruct (Hwf x) as [_ Contra'].
    destruct Contra'; [eexists; eauto | ].
    lia.
Qed.



Lemma alloc_correct : forall w D F H ptr H',
    allocate D H w = Some (ptr, H') ->
    structdef_wf D ->
    heap_wf H ->
    ~ is_fun_type w ->
    simple_type (TPtr Checked w) ->
    malloc_bound w ->
    @heap_consistent_checked D F H' H /\
    @well_typed_lit_checked D F H' empty_scope ptr (TPtr Checked w) /\
    heap_wf H'.
Proof.
  intros w D F H ptr H' Alloc HSd HWf Hfun HSim HBound.
  unfold allocate in *.
  unfold allocate_meta in *.
  unfold bind in *; simpl in *.
  destruct w; simpl in *; eauto; inv Alloc; simpl in *; eauto.
  - split; [| split].
    * apply well_typed_preserved; eauto.
    * eapply TyLitC_C with (w := TNat); simpl; eauto.
      repeat constructor. intros. simpl in *. assert (k = 0) by lia; subst.
      exists 0,TNat.
      repeat split; try easy. rewrite Z.add_0_r. apply Heap.add_1. easy.
      apply TyLitZero_C; easy.
    * apply heap_add_preserves_wf; auto.
  - split; [ | split].
    * apply well_typed_preserved; eauto.
    * eapply TyLitC_C with (w := (TPtr m w)); simpl; eauto.
      repeat constructor. intros. simpl in *. assert (k = 0) by lia; subst.
      exists 0,(TPtr m w).
      repeat split; try easy. rewrite Z.add_0_r. apply Heap.add_1. easy.
      apply TyLitZero_C; easy.
    * apply heap_add_preserves_wf; auto.
  - split.
    * destruct (StructDef.find s D) eqn:Find; simpl in *; try congruence.
      remember (Fields.elements f) as l.
      pose proof (fold_preserves_consistency (map snd l) D F H ptr HWf).
      
      remember (fold_left
         (fun (acc : Z * heap) (t : type) =>
          let (sizeAcc, heapAcc) := acc in
          (sizeAcc + 1, Heap.add (sizeAcc + 1) (0, t) heapAcc)) 
         (map snd l) (Z.of_nat (Heap.cardinal (elt:=Z * type) H), H)) as p.
      
      destruct p.
      clear Heqp.      
      inv H1.
      eauto.
    
    * destruct (StructDef.find s D) eqn:Find; try congruence.
      pose proof (fold_summary (map snd (Fields.elements f)) H ptr HWf) as Hyp.

      remember
        (fold_left
          (fun (acc : Z * heap) (t : type) =>
           let (sizeAcc, heapAcc) := acc in
           (sizeAcc + 1, Heap.add (sizeAcc + 1) (0, t) heapAcc))
          (map snd (Fields.elements (elt:=type) f))
          (Z.of_nat (Heap.cardinal (elt:=Z * type) H), H)) as p.
      destruct p as [z h].
      clear Heqp.
      inv H1.

      destruct Hyp as [H'wf  [Card1 [Card2 [HF HM]]]]; eauto.

      split; auto.
      eapply TyLitC_C with (w := (TStruct s)); simpl in *; eauto.
      repeat constructor.
      rewrite Find; eauto.
      intros k HK.
      apply StructDef.find_2 in Find.
      remember Find as Fwf; clear HeqFwf.
      apply HSd in Fwf.
      assert (HOrd: 0 < Z.of_nat(Heap.cardinal H) + 1 + k <= Z.of_nat(Heap.cardinal H')) by lia.
      pose proof (H'wf (Z.of_nat(Heap.cardinal H) + 1 + k)) as Hyp.
      apply Hyp in HOrd.
      destruct HOrd as [[n' t'] HM'].
      (*This bit is very annoying, quite a bit of converting back and forth
        between ints and nats. This could definately be more automated DP*)
      exists n'. exists t'.
      rewrite Z.sub_0_r.
      destruct (Zlength_nth (map snd (Fields.elements f)) k HK) as [x Hnth].
      assert (HK': (0 <= (Z.to_nat k) < (length (map snd (Fields.elements (elt:=type) f))))%nat). {
        destruct k.
          +zify. simpl. lia. 
          +simpl. zify. lia.
          + exfalso. inv HK. apply H0. simpl. reflexivity. }
      specialize (HF (Z.to_nat k) x HK' Hnth).
      assert (K0 : k = Z.of_nat (Z.to_nat k)). {
      destruct k.
        +simpl. reflexivity.
        +simpl. zify. reflexivity.
        +inv HK. exfalso. apply H0. simpl. reflexivity. }
      rewrite <- K0 in HF.
      pose proof (HeapFacts.MapsTo_fun HM' HF) as Eq.
      inv Eq.
      repeat (split; eauto). apply TyLitZero_C.
  - split.
    * apply simple_type_array in HSim as X1. destruct X1 as [z [z0 [X1 X2]]];subst.
      remember (Zreplicate (z0 - z) w) as l.
      pose proof (fold_preserves_consistency l D F H ptr HWf) as X3.

      remember (fold_left
         (fun (acc : Z * heap) (t : type) =>
          let (sizeAcc, heapAcc) := acc in
          (sizeAcc + 1, Heap.add (sizeAcc + 1) (0, t) heapAcc))
         l
         (Z.of_nat (Heap.cardinal (elt:=Z * type) H), H)) as p.
      
      destruct p as (n1, h). (*n0 already used???*)
      clear Heqp.
      destruct z; inv H1.
      apply X3; eauto.
    * apply simple_type_array in HSim as X1. destruct X1 as [z [z0 [X1 X2]]];subst.
      remember (Zreplicate (z0 - z) w) as l.
      pose proof (fold_summary l H ptr HWf) as Hyp.
      remember
        (fold_left
          (fun (acc : Z * heap) (t : type) =>
           let (sizeAcc, heapAcc) := acc in
           (sizeAcc + 1, Heap.add (sizeAcc + 1) (0, t) heapAcc)) l
          (Z.of_nat (Heap.cardinal (elt:=Z * type) H), H)) as p.
      destruct p.
      clear Heqp.
      destruct z; inv H1; eauto.
      destruct Hyp as [H'wf  [Card1 [Card2 [HF HM]]]]; eauto.
      split; auto.
      eapply TyLitC_C with (w := (TArray (Num 0) (Num z0) w)); simpl in *; eauto.
      repeat constructor.
      intros k HK.
      simpl in *.
      pose proof (H'wf (Z.of_nat(Heap.cardinal H) + 1 + k)) as Hyp.
      repeat rewrite Z.sub_0_r. rewrite Z.sub_0_r in Card2 HF HK.
      remember (Heap.cardinal H ) as c.
      remember (Heap.cardinal H') as c'.
      assert (HOrd : 0 < Z.of_nat c + 1 + k <= Z.of_nat c')
        by (zify; lia).
      
      destruct Hyp as [HIn Useless].
      destruct (HIn HOrd) as [[n' t'] HM'].

      destruct HK as [HP1 HP2].

      destruct z0 as [ | p | ?]; simpl in *; [ lia | | lia].
      rewrite replicate_length in Card2 HF HP2.

      destruct (length_nth (replicate (Pos.to_nat p) w) (Z.to_nat k)) as [t Hnth].
      { rewrite replicate_length ; zify; split; try lia. }      
      rewrite Hnth.
      remember Hnth as Hyp; clear HeqHyp.
      apply replicate_nth in Hnth; subst.
      exists n'; exists t.
      split; [ reflexivity | ].
      specialize (HF (Z.to_nat k) t).
      assert (HF1 : (0 <= Z.to_nat k < Pos.to_nat p)%nat). {
        split; zify; (try lia).
      }
      specialize (HF HF1 Hyp).
      assert (HId: Z.of_nat (Z.to_nat k) = k). {
        destruct k; simpl.
          + reflexivity.
          + zify. lia.
          + exfalso. zify. lia. }
      rewrite HId in HF.
      
      pose proof (HeapFacts.MapsTo_fun HM' HF) as Eq.
      inv Eq.
      split; auto.
      apply TyLitZero_C.
  - apply simple_type_tnt in HSim as X1. destruct X1 as [z [z0 [X1 X2]]];subst.
    destruct HBound;subst.
    split.
    * remember (Zreplicate (z0 - 0 + 1) w) as l.
      pose proof (fold_preserves_consistency l D F H ptr HWf) as X3.

      remember (fold_left
         (fun (acc : Z * heap) (t : type) =>
          let (sizeAcc, heapAcc) := acc in
          (sizeAcc + 1, Heap.add (sizeAcc + 1) (0, t) heapAcc))
         l
         (Z.of_nat (Heap.cardinal (elt:=Z * type) H), H)) as p.
      
      destruct p as (n1, h). (*n0 already used???*)
      clear Heqp.
      inv H1.
      apply X3; eauto.
    * remember (Zreplicate (z0 - 0 + 1) w) as l.
      pose proof (fold_summary l H ptr HWf) as Hyp.
      remember
        (fold_left
          (fun (acc : Z * heap) (t : type) =>
           let (sizeAcc, heapAcc) := acc in
           (sizeAcc + 1, Heap.add (sizeAcc + 1) (0, t) heapAcc)) l
          (Z.of_nat (Heap.cardinal (elt:=Z * type) H), H)) as p.
      destruct p.
      clear Heqp.
      inv H1; eauto.
      destruct Hyp as [H'wf  [Card1 [Card2 [HF HM]]]]; eauto.
      split; auto.
      eapply TyLitC_C with (w := (TNTArray (Num 0) (Num z0) w)); simpl in *; eauto.
      repeat constructor.
      specialize (HF 0%nat w).
      assert ((z0 - 0 + 1) = z0 + 1) by lia.
      rewrite H0 in HF Card2.
      assert ((0 <= 0 < length (Zreplicate (z0 + 1) w))%nat).
      split. lia. simpl. apply Nat2Z.inj_lt. rewrite replicate_gt_eq.
      lia. lia. apply HF in H1; try easy.
      exists 0,w. split. lia. split.
      rewrite Z.add_0_r.
      rewrite Z.add_0_r in H1. easy.
      intros. lia. unfold Zreplicate.
      destruct (z0 + 1) eqn:eq1. lia.
      rewrite replicate_nth_anti; try lia. easy. lia.
      intros k HK.
      simpl in *.
      pose proof (H'wf (Z.of_nat(Heap.cardinal H) + 1 + k)) as Hyp.
      repeat rewrite Z.sub_0_r. rewrite Z.sub_0_r in Card2 HF HK.
      remember (Heap.cardinal H ) as c.
      remember (Heap.cardinal H') as c'.
      assert (HOrd : 0 < Z.of_nat c + 1 + k <= Z.of_nat c')
        by (zify; lia).
      
      destruct Hyp as [HIn Useless].
      destruct (HIn HOrd) as [[n' t'] HM'].

      destruct HK as [HP1 HP2].

      destruct z0 as [ | p | ?]; simpl in *; [ lia | | lia].
      rewrite replicate_length in Card2 HF HP2.

      destruct (length_nth (replicate (Pos.to_nat (p+1)) w) (Z.to_nat k)) as [t Hnth].
      { rewrite replicate_length ; zify; split; try lia. }      
      rewrite Hnth.
      remember Hnth as Hyp; clear HeqHyp.
      apply replicate_nth in Hnth; subst.
      exists n'; exists t.
      split; [ reflexivity | ].
      specialize (HF (Z.to_nat k) t).
      assert (HF1 : (0 <= Z.to_nat k < Pos.to_nat (p+1))%nat). {
        split; zify; (try lia).
      }
      specialize (HF HF1 Hyp).
      assert (HId: Z.of_nat (Z.to_nat k) = k). {
        destruct k; simpl.
          + reflexivity.
          + zify. lia.
          + exfalso. zify. lia. }
      rewrite HId in HF.
      
      pose proof (HeapFacts.MapsTo_fun HM' HF) as Eq.
      inv Eq.
      split; auto.
      apply TyLitZero_C.
  - easy.
Qed.

Lemma reduce_list_sub: forall D F cm M e m M' e' vl,
 reduce D F cm M e m M' (RExpr e') -> list_sub (freeVars e) vl
   ->list_sub (freeVars e') vl.
Proof.
  intros. induction H; simpl in *.
Admitted.


Lemma env_consist_is_tainteds: forall Q env env' vl, env_consistent Q env env' 
   -> Forall (fun x => forall t, Env.MapsTo x t env -> is_tainted t) vl
   -> Forall (fun x => forall t, Env.MapsTo x t env' -> is_tainted t) vl.
Proof.
  intros. induction H0; intros;simpl in *.
  constructor.
  constructor. intros.
  destruct H as [X1 [X2 X3]].
  apply Env.mapsto_in in H2 as X4.
  apply X1 in X4 as X5.
  destruct X5.
  apply H0 in H as X6.
Admitted.


(** Type Preservation Theorem. *)
Section Preservation. 
  Variable D : structdef.
  Variable F : FEnv.
  Variable cm : mode.
  Hypothesis HDwf : structdef_wf D.
  Lemma preservation : forall s R env Q e t s' R' e',
      rheap_wf R ->
      rheap_wt_all D F R ->
      expr_wf D cm e ->
      stack_wt D Checked s ->
      env_wt D Checked env ->
      theta_wt Q env s ->
      same_domain env s ->
      stack_wf Q env s ->
      stack_rheap_consistent D F R s ->
      fun_wf D F R ->
      well_typed D F R env Q cm e t ->
      reduce D F cm
        (s, R) e Checked
        (s', R') (RExpr e') ->
      exists env' t',
           same_domain env' s'
        /\ stack_wf Q env' s'
        /\ theta_wt Q env' s'
        /\ rheap_consistent D F R' R
        /\ stack_rheap_consistent D F R' s'
        /\ env_consistent Q env env'
        /\ well_typed D F R' env' Q cm e' t'
        /\ eq_subtype Q t' t
        /\ type_wf D cm t'.
  Proof with (eauto with ty sem heap Preservation).
    intros s R env Q e t s' R' e'
      HRwf HRWt HEwf Hswt Henvt HQt HDom Hswf HsHwf Hwf Hwt.
    generalize dependent R'. generalize dependent s'.  generalize dependent e'.
    generalize dependent s.
    induction Hwt as
      [
        env Q n t Hmode HQ HTyLit                                  | (* Literals Checked *)
        env Q m n t Hmode HQ                                         | (* Literals Tainted *)
        env Q m x t t' Hx HSub                                     | (* Variables *)
        env Q m m' es x xl ts t ta HMode Wb HTyf IH1 HArgs         | (* Call *)
        env Q x m m' h l t Wb HMode                                | (* Strlen *)
       (* env Q m m' x y e l h t ta HMode Wb HTy HIn Hx              | (* LetStrlen *) *)
        env Q m x e1 e2 t b HTy1 IH1 HTy2 IH2 Hdept Hx             | (* Let-Nat-Expr *)
        env Q m x e1 m' t1 e2 t Hx HMode HTy1 IH1 HTy2 IH2         | (* Let-Expr *)
        env Q m x na e t Hx HTy1 IH1                               | (* RetTNat *)
        env Q x na ta e t Hx HSim HTyLit HTy1 IH1                  | (* RetChecked *)
        env Q m m' x na ta e t Hx Hnc HMode HSim HTy1 IH1          | (* Ret *)
        env Q m e1 e2 HTy1 IH1 HTy2 IH2                            | (* Addition *)
        env Q m e m' T fs i fi ti HMode HTy IH HWf1 HWf2 HList     | (* Field Addr *)
        env Q m m' w HMode Wb                                    | (* Malloc *)
        env Q m vl t t' e Hl HTy IH Heq Htl Ht                     | (* Unchecked *)
        env Q m vl t t' e Hl HTy IH Heq Htl Ht                     | (* checked *)
        env Q t e t' Wb HMode HTy IH                               | (* Cast - nat *)
        env Q m t e t' Wb HTy IH HSub                              | (* Cast - subtype *)
        env Q m e x y u v t t' Wb HTy IH Teq HMode                 | (* DynCast - ptr array *)
        env Q m e x y t t' HNot Teq Wb HTy IH HMode                | (* DynCast - ptr array from ptr *)
        env Q m e x y u v t t' Wb Teq HTy IH HMode                 | (* DynCast - ptr nt-array *)
        env Q m e x y u v t t' Wb Teq HTy IH HMode                 | (* DynCast - ptr nt-to-array *)
        env Q m e m' t l h t' HTy IH HPtrType HMode                | (* Deref *)

        env Q m e1 m' l h e2 t WT Twf HTy1 IH1 HTy2 IH2 HMode                      | (* Index for array pointers *)
        env Q m e1 m' l h e2 t WT Twf HTy1 IH1 HTy2 IH2 HMode                      | (* Index for ntarray pointers *)


        env Q m e1 e2 m' t t1 HSub WT HTy1 IH1 HTy2 IH2 HMode                      | (* Assign normal *)
        env Q m e1 e2 m' l h t t' WT Twf HSub HTy1 IH1 HTy2 IH2 HMode              | (* Assign array *)
        env Q m e1 e2 m' l h t t' WT Twf HSub HTy1 IH1 HTy2 IH2 HMode              | (* Assign nt-array *)
        
        env Q m e1 e2 e3 m' l h t t' WT Twf TSub HTy1 IH1 HTy2 IH2 HTy3 IH3 HMode      |  (* IndAssign for array pointers *)
        env Q m e1 e2 e3 m' l h t t' WT Twf TSub HTy1 IH1 HTy2 IH2 HTy3 IH3 HMode      |  (* IndAssign for ntarray pointers *)
        env Q m m' x t t1 e1 e2 t2 t3 t4 HEnv TSub HPtr HTy1 IH1 HTy2 IH2 HJoin HMode  | (* IfDef *)
        env Q m m' x l t e1 e2 t2 t3 t4 HEnv HTy1 IH1 HTy2 IH2 HJoin HMode             | (* IfDefNT *)
        env Q m e1 e2 e3 t2 t3 t4 HTy1 IH1 HTy2 IH2 HTy3 IH3 HJoin                       (* If *)
      ]; intros s Hswt HQt HDom Hswf HsHwf e' s' R' Hreduces; subst.
    (* T-Lit, impossible because values do not step *)
    - inv Hreduces; solve_ctxt.
    (* T-LitTainted *)
    - inv Hreduces; solve_ctxt.
    (* T-Var *)
    -  inv Hreduces; solve_ctxt.
      inv H5. exists env, t0.
      destruct R' as [Hchk Htnt]; subst; intuition...
      apply env_consist_refl.
      cbn.
      apply Hswt in H4 as eq1. destruct eq1 as [X1 [X2 X3]].
      simpl in H; subst.
      inv X1.
      constructor. constructor. constructor.
      constructor. destruct m;try easy.
      constructor. constructor. easy.
      intuition...
      apply TyLitTainted. intros R. inv R. easy.
      apply TyLitTainted. intros R. inv R. easy.
      apply Hswf in Hx. destruct Hx as [v1 [t1 [HSub1 HM]]]. 
      apply Stack.mapsto_always_same with (v1 := (v1, t1)) in H4; try easy.
      inv H4. apply eq_subtype_trans with (t2 := t); try easy. 
      unfold eq_subtype. exists t. split. apply type_eq_refl.
      constructor. easy. simpl in *. subst.
      inv HEwf. apply Hswt in H4. destruct H4 as [X1 [X2 X3]]. easy.
    (*T-Call*)
    - inv HMode.
      inv Hreduces. destruct E; try congruence; try solve [solve_step].
      simpl in *; subst.
      inv  H4. inv HTyf.
      inv H13; eauto; try easy.
      destruct Hwf. rewrite H1 in H5. easy. rewrite H5 in H6.
      inv H6.
      apply subtype_fun in H8 as Y1; try easy. 
      destruct Y1 as [yl [tb [tlb Y1]]];subst.
      specialize (get_fun_type_fun tvl0 ta0 Checked) as X1.
      rewrite X1 in H8. rewrite X1 in Y1.
      inv Y1.
      apply subtype_fun_1 in H8 as X2; try easy.
      destruct X2 as [X2 [X3 X4]]; subst.
      exists env,ta'.
      split; try easy. split; try easy.
      split; try easy. 
      split. apply rheap_consistent_refl.
      split; try easy.
      split. apply env_consist_refl.
      apply eval_el_vl_1 in H10 as X5.
      destruct X5 as [vl X5].
      apply eval_el_vl with (xl := (get_xl tvl0)) (tvl := tvl0) (e := e0) 
        (t := tb) (ea:=e'0) (ta:=ta') in X5 as X6; try easy.
      destruct Hwf as [Y1 Y2].
      assert (mode_leq Checked Checked) by easy.
      destruct (Y2 env Q x0 tvl0 tb ta' 
        e0 vl e'0 Checked Checked H1 H5 X6) as [Y3 [Y4 [Y5 [Y6 [Y7 [Y8 Y9]]]]]].
      clear H1.
      split; try easy. split.
      eapply well_typed_eval_vs with (F := F) (R := R') (env := env) (S := s').
      destruct HQt as [eq1 [eq2 eq3]].
      intros. apply eq3. easy.
      apply X3. apply X4. apply HArgs. apply H10.
      apply subtype_fun in H4.
      destruct H4 as [yl [tb [tlb Y1]]];subst. inv Y1.
      unfold is_fun_type in *. easy.
      assert (CheckedCDef.is_checked (TPtr Checked (TFun xl t ts))).
      constructor. easy.
      inv HTyf. inv H11.
      inv H13; eauto; try easy.
      destruct Hwf. rewrite H3 in H9. easy. rewrite H9 in H7.
      inv H7.
      apply subtype_fun in H11 as Y1; try easy. destruct Y1 as [yl [tb [tlb Y1]]];subst.
      specialize (get_fun_type_fun tvl0 ta0 Tainted) as X1.
      rewrite X1 in H11. rewrite X1 in Y1.
      inv Y1.
      apply subtype_fun_1 in H11 as X2; try easy.
      destruct X2 as [X2 [X3 X4]]; subst.
      exists env,ta'.
      split; try easy. split; try easy.
      split; try easy.
      split. apply rheap_consistent_refl.
      split; try easy.
      split. apply env_consist_refl.
      apply eval_el_vl_1 in H12 as X5.
      destruct X5 as [vl X5].
      apply eval_el_vl with (xl := (get_xl tvl0)) (tvl := tvl0) (e := e0) 
        (t := tb) (ea:=e'0) (ta:=ta') in X5 as X6; try easy.
      destruct Hwf as [Y1 Y2].
      assert (mode_leq Tainted Checked) by easy.
      destruct (Y2 env Q x0 tvl0 tb ta' 
        e0 vl e'0 Checked Tainted H3 H9 X6) as [Y3 [Y4 [Y5 [Y6 [Y7 [Y8 Y9]]]]]].
      clear H3.
      split; try easy.
      eapply well_typed_eval_vs with (F := F) (R := (H1, H2)) (env := env) (S := s').
      destruct HQt as [eq1 [eq2 eq3]].
      intros. apply eq3. easy.
      apply X3. apply X4. apply HArgs. apply H12.
      apply subtype_fun in H6.
      destruct H6 as [yl [tb [tlb Y1]]];subst. inv Y1.
      unfold is_fun_type in *. easy.
      inv HTyf; try easy. assert (Checked = Checked) by easy. apply H in H1. easy.
      inv H1.
      edestruct IH1; try easy.
      inv HEwf; easy.
      easy. easy.
      apply step_implies_reduces_1; try easy. apply H4.
      destruct H1 as [ta' [X1 [X2 [X3 [X4 [X5 [X6 [X7 X8]]]]]]]].
      simpl. apply eq_subtype_fun in X8.
      destruct X8 as [tb [tlb [X8 [X9 X10]]]];subst; try easy.
      apply well_typed_args_sub 
        with (tlb := tlb) (tb := tb) (Q := Q) (R' := R') in HArgs as X11; try easy.
      destruct X11 as [ta' [X11 X12]].
      exists x,ta'.
      split; try easy.
      split; try easy.
      split; try easy.
      split; try easy.
      split; try easy.
      split; try easy.
      split.
      apply TyCall with (m' := m') (xl := xl) (ts := tlb) (t := tb); try easy.
      eapply env_wf_consist. apply X6. easy.
      apply well_typed_args_consist with (env' := x) in X11;try easy.
      unfold eq_subtype. exists ta'. split. apply type_eq_refl.
      easy.
    (*T-Strlen*)
    - inv HMode. inv Hreduces; solve_ctxt.
      simpl in *; subst.
     *
      exists env,TNat; simpl in *.
      unfold stack_wf in Hswf.
      eapply Hswf in Wb as X1; try easy.
      destruct X1 as [va [ta [X1 X2]]].
      apply Stack.mapsto_always_same with (v1 := (va, ta)) in H15 as X3; try easy.
      inv X3.
      split.
      unfold same_domain,change_strlen_stack; intros. split; intros.
      destruct (n' <=? h0 ) eqn:eq1.
      apply HDom; easy.
      destruct (Nat.eq_dec x0 x); subst.
      exists (n, TPtr Checked (TNTArray (Num l0) (Num n') t0)).
      apply Stack.add_1. easy.
      apply HDom in H1. destruct H1.
      exists x1.
      apply Stack.add_2. lia. easy.
      destruct (n' <=? h0 ) eqn:eq1.
      apply HDom; easy.
      destruct (Nat.eq_dec x0 x); subst. exists (TPtr m' (TNTArray h l t)). easy.
      destruct H1.
      apply Stack.add_3 in H1; try lia. apply Stack.mapsto_in in H1.
      apply HDom in H1. destruct H1. exists x2;easy.
      split. unfold stack_wf,change_strlen_stack in *. intros.
      destruct (Nat.eq_dec x0 x); subst.
      apply Env.mapsto_always_same with (v1 := t2) in Wb as X4; try easy;subst.
      destruct (n' <=? h0 ) eqn:eq1.
      exists n,(TPtr Checked (TNTArray (Num l0) (Num h0) t0)); easy.
      exists n,(TPtr Checked (TNTArray (Num l0) (Num n') t0)).
      split. apply eq_subtype_trans with (t2:=(TPtr Checked (TNTArray (Num l0) (Num h0) t0))); try easy.
      unfold eq_subtype. exists (TPtr Checked (TNTArray (Num l0) (Num n') t0)).
      split. apply type_eq_refl.
      constructor. apply SubTyNtSubsume; try easy.
      constructor. easy.
      constructor. lia.
      apply Stack.add_1. easy.
      apply Hswf in H1. destruct H1 as [va [ta [Y1 Y2]]].
      exists va, ta; try easy.
      split. easy.
      destruct (n' <=? h0). try easy.
      apply Stack.add_2. lia. easy.
      split. unfold theta_wt in *.
      destruct HQt.
      split. easy. split.
      destruct H4. intros.
      unfold change_strlen_stack in *.
      destruct (n' <=? h0).
      apply H4 with (x := x0); try easy.
      destruct (Nat.eq_dec x x0). subst.
      apply Stack.mapsto_add1 in H7. inv H7.
      apply Stack.add_3 in H7.
      apply H4 with (x := x0); try easy. easy.
      intros.
      unfold change_strlen_stack in *. destruct H4.
      destruct (n' <=? h0). 
      apply H6 with (x := x0); try easy.
      destruct (Nat.eq_dec x x0). subst.
      apply Stack.mapsto_add1 in H5. inv H5.
      apply Stack.add_3 in H5.
      apply H6 with (x := x0); try easy. easy.
      split. apply rheap_consistent_refl.
      split.
      unfold stack_rheap_consistent, change_strlen_stack in *.
      intros.
      destruct (n' <=? h0) eqn:eq1.
      eapply HsHwf. apply H1. apply H4.
      destruct (Nat.eq_dec x x0); subst.
      apply Stack.mapsto_add1 in H4. inv H4.
      apply HsHwf with (Hchk := Hchk) (Htnt := Htnt) in X2; try easy. inv H1.
      apply Hswt in H15. destruct H15 as [Y3 [Y4 Y5]].
      inv X2; try easy. apply TyLitZero_C. 
      unfold scope_set_add in *. inv H4. inv H1. inv H5.
      apply TyLitC_C with (w := ((TNTArray (Num l0) (Num n') t0)))
       (b := l0) (ts := (Zreplicate (n' - l0 + 1) t0)); eauto.
      constructor. apply SubTyRefl. simpl.
      intros.
      unfold scope_set_add.
      rewrite replicate_gt_eq in H1; try lia.
      assert (l0 + (n' - l0 + 1) = n' + 1) by lia.
      rewrite H4 in H1. clear H4.
      destruct (Z.eq_dec n' 0). subst.
      rewrite replicate_gt_eq in H9; try lia.
      specialize (H16 n) as eq2.
      assert (n <= n < n + n') by lia.
      apply eq2 in H4. clear eq2.
      specialize (H9 0) as eq2.
      assert (l0 <= 0 < l0 + Z.of_nat (length (Zreplicate (h0 - l0 + 1) t0))).
      rewrite replicate_gt_eq; try lia.
      apply eq2 in H5. clear eq2.
      destruct H5 as [na [ta [A1 [A2 A3]]]].
      destruct H4 as [nb [A4 A5]].
      rewrite Z.add_0_r in A2.
      apply Heap.mapsto_always_same with (v1 := (nb,t1)) in A2; try easy. inv A2.
      symmetry in A1.
      destruct (h0 - l0 + 1) as [| p1 | ?] eqn:Hp1; zify; [lia | |lia].
      unfold Zreplicate in A1.
      apply replicate_nth in A1. subst.
      destruct (Z_ge_dec h0 k).
      specialize (H9 k).
      assert (l0 <= k < l0 + Z.of_nat (length (Zreplicate (Z.pos p1) ta))).
      rewrite replicate_gt_eq; try lia.
      apply H9 in H4. destruct H4 as [nc [tc [B1 [B2 B3]]]].
      exists nc. exists tc.
      split. unfold Zreplicate in *.
      symmetry in B1.
      apply replicate_nth in B1. subst.
      destruct (n' - l0 + 1) as [| p | ?] eqn:Hp; zify; [lia | |lia].
      rewrite replicate_nth_anti; try easy. lia. easy.
      destruct (Z.eq_dec n' k). subst.
      exists 0. exists ta.
      destruct (k - l0 + 1) as [| p | ?] eqn:Hp; zify; [lia | |lia].
      unfold Zreplicate. split.
      rewrite replicate_nth_anti; try easy. lia. split. easy.
      constructor.
      specialize (H16 (n+k)).
      assert (n <= n + k < n + n') by lia.
      apply H16 in H4.
      destruct H4 as [nb [Y1 Y2]].
      destruct HRWt with (Hchk0 := Hchk) (Htnt0 := Htnt); try easy.
      apply H4 in Y1 as eq2.
      exists nb. exists ta.
      destruct (n' - l0 + 1) as [| p | ?] eqn:Hp; zify; [lia | |lia].
      split. unfold Zreplicate.
      rewrite replicate_nth_anti; try easy. lia. easy.
      inv H10. inv H10. apply simple_type_tnt in H2.
      destruct H2 as [l2 [h2 [A1 A2]]];subst. inv H18. inv H10.
      destruct (Z_ge_dec h2 n').
      apply checked_subtype_well_type
        with (t := (TPtr Checked (TNTArray (Num l2) (Num h2) t0))); try easy.
      inv Y4. inv H8. constructor. constructor; easy. easy.
      apply TyLitC_C with (w := (TNTArray (Num l2) 
           (Num h2) t0)) (b := l2) (ts := Zreplicate (h2 - l2 + 1) t0); try easy.
      constructor. constructor.
      intros.
      unfold scope_set_add.
      inv H5.
      specialize (H9 k H1). easy.
      exists ((TPtr Checked (TNTArray (Num l2) (Num h2) t0))). split. apply type_eq_refl.
      constructor. apply SubTyNtSubsume. constructor. lia. constructor. lia.
      inv H5.
      apply TyLitC_C with (w := ((TNTArray (Num l0) (Num n') t0)))
       (b := l0) (ts := (Zreplicate (n' - l0 + 1) t0)); eauto.
      constructor. constructor.
      intros.
      unfold scope_set_add.
      destruct (n' - l0 + 1) as [| p | ?] eqn:Hp; zify; [lia | |lia].
      rewrite replicate_gt_eq in H1; try easy.
      rewrite <- Hp in *. assert (l0 + (n' - l0 + 1) = n' + 1) by lia.
      rewrite H2 in H1. clear H2.
      destruct (Z.eq_dec n' 0). subst. lia.
      specialize (H16 n) as eq2.
      assert (n <= n < n + n') by lia.
      apply eq2 in H2. clear eq2.
      specialize (H9 0) as eq2.
      assert (l2 <= 0 < l2 + Z.of_nat (length (Zreplicate (h2 - l2 + 1) t0))).
      rewrite replicate_gt_eq; try lia.
      apply eq2 in H5. clear eq2.
      destruct H5 as [na [ta [A1 [A2 A3]]]].
      destruct H2 as [nb [A4 A5]].
      rewrite Z.add_0_r in A2.
      apply Heap.mapsto_always_same with (v1 := (nb,t1)) in A2; try easy. inv A2.
      symmetry in A1.
      destruct (h2 - l2 + 1) as [| p1 | ?] eqn:Hp1; zify; [lia | |lia].
      unfold Zreplicate in A1.
      apply replicate_nth in A1. subst.
      destruct (Z_ge_dec h2 k).
      specialize (H9 k).
      assert (l2 <= k < l2 + Z.of_nat (length (Zreplicate (Z.pos p1) ta))).
      rewrite replicate_gt_eq; try lia.
      apply H9 in H2. destruct H2 as [nc [tc [B1 [B2 B3]]]].
      exists nc. exists tc.
      rewrite Hp.
      split. unfold Zreplicate in *.
      symmetry in B1.
      apply replicate_nth in B1. subst.
      rewrite replicate_nth_anti; try easy. lia. easy.
      destruct (Z.eq_dec n' k). subst.
      exists 0. exists ta.
      unfold Zreplicate.
      destruct (k - l0 + 1) as [| p2 | ?] eqn:Hp2; zify; [lia | |lia].
      rewrite replicate_nth_anti; try easy. lia.
      split. easy. split. easy. apply TyLitZero_C.
      specialize (H16 (n+k)).
      assert (n <= n + k < n + n') by lia.
      apply H16 in H2.
      destruct H2 as [nb [Y1 Y2]].
      destruct HRWt with (Hchk0 := Hchk) (Htnt0 := Htnt); try easy.
      apply H2 in Y1 as eq2.
      exists nb. exists ta.
      split. unfold Zreplicate. rewrite Hp.
      rewrite replicate_nth_anti; try easy. lia. easy.
      apply Stack.add_3 in H4. apply HsHwf with (Hchk := Hchk) (Htnt := Htnt) in H4; try easy.
      easy. unfold rheap_consistent.
      split. apply env_consist_refl.
      split. constructor. constructor. easy. constructor.
      exists TNat. split. apply type_eq_refl. constructor. constructor.
    *
      exists env,TNat; simpl in *.
      unfold stack_wf in Hswf.
      eapply Hswf in Wb as X1; try easy.
      destruct X1 as [va [ta [X1 X2]]].
      apply Stack.mapsto_always_same with (v1 := (va, ta)) in H15 as X3; try easy.
      inv X3.
      split.
      unfold same_domain,change_strlen_stack; intros. split; intros.
      destruct (n' <=? h0 ) eqn:eq1.
      apply HDom; easy.
      destruct (Nat.eq_dec x0 x); subst.
      exists (n, TPtr Tainted (TNTArray (Num l0) (Num n') t0)).
      apply Stack.add_1. easy.
      apply HDom in H1. destruct H1.
      exists x1.
      apply Stack.add_2. lia. easy.
      destruct (n' <=? h0 ) eqn:eq1.
      apply HDom; easy.
      destruct (Nat.eq_dec x0 x); subst. exists (TPtr m' (TNTArray h l t)). easy.
      destruct H1.
      apply Stack.add_3 in H1; try lia. apply Stack.mapsto_in in H1.
      apply HDom in H1. destruct H1. exists x2;easy.
      split. unfold stack_wf,change_strlen_stack in *. intros.
      destruct (Nat.eq_dec x0 x); subst.
      apply Env.mapsto_always_same with (v1 := t2) in Wb as X4; try easy;subst.
      destruct (n' <=? h0 ) eqn:eq1.
      exists n,(TPtr Tainted (TNTArray (Num l0) (Num h0) t0)); easy.
      exists n,(TPtr Tainted (TNTArray (Num l0) (Num n') t0)).
      split. apply eq_subtype_trans with (t2:=(TPtr Tainted (TNTArray (Num l0) (Num h0) t0))); try easy.
      unfold eq_subtype. exists (TPtr Tainted (TNTArray (Num l0) (Num n') t0)).
      split. apply type_eq_refl.
      constructor. apply SubTyNtSubsume; try easy.
      constructor. easy.
      constructor. lia.
      apply Stack.add_1. easy.
      apply Hswf in H1. destruct H1 as [va [ta [Y1 Y2]]].
      exists va, ta; try easy.
      split. easy.
      destruct (n' <=? h0). try easy.
      apply Stack.add_2. lia. easy.
      split. unfold theta_wt in *.
      destruct HQt.
      split. easy. split.
      destruct H4. intros.
      unfold change_strlen_stack in *.
      destruct (n' <=? h0).
      apply H4 with (x := x0); try easy.
      destruct (Nat.eq_dec x x0). subst.
      apply Stack.mapsto_add1 in H7. inv H7.
      apply Stack.add_3 in H7.
      apply H4 with (x := x0); try easy. easy.
      intros.
      unfold change_strlen_stack in *. destruct H4.
      destruct (n' <=? h0). 
      apply H6 with (x := x0); try easy.
      destruct (Nat.eq_dec x x0). subst.
      apply Stack.mapsto_add1 in H5. inv H5.
      apply Stack.add_3 in H5.
      apply H6 with (x := x0); try easy. easy.
      split. apply rheap_consistent_refl.
      split.
      unfold stack_rheap_consistent, change_strlen_stack in *.
      intros.
      destruct (n' <=? h0) eqn:eq1.
      eapply HsHwf. apply H1. apply H4.
      destruct (Nat.eq_dec x x0); subst.
      apply Stack.mapsto_add1 in H4. inv H4.
      apply TyLitU_C. easy.
      apply Stack.add_3 in H4.
      eapply HsHwf. apply H1. apply H4.
      easy.
      split. apply env_consist_refl.
      split. constructor. constructor. easy. constructor.
      exists TNat. split. apply type_eq_refl. constructor. constructor.
    * apply Hswf in Wb. destruct Wb as [va [ta [X1 X2]]].
      apply Stack.mapsto_always_same with (v1 := (va, ta)) in H13; try easy.
      inv H13. apply eq_subtype_mode_same in X1. subst.
      assert (Checked = Checked) by easy.
      simpl in *; subst. apply H in H1. easy.
(*
    (*T-LetStrlen*)
*)
   (* T-Let *)
   - inv Hreduces. destruct E; inv H; simpl in *; subst; try easy.
     unfold get_good_dept in *. destruct e1; try easy.
     inv H2; auto. 
     inv HTy1. inv H0. inv HEwf. inv Hdept.
     exists env, (subst_type t x (Num z)); eauto.
     split; try easy.
     split; try easy.
     split; try easy.
     split. apply rheap_consistent_refl.
     split; try easy.
     split. apply env_consist_refl.
     split. apply TyRetTNat; try easy.
     unfold eq_subtype. exists (subst_type t x (Num z)). 
     split. apply type_eq_refl.  constructor. constructor. 
     assert (is_checked TNat). constructor. easy.
     unfold get_good_dept in *.
     destruct (in_hole e E) eqn:eq1; try easy. inv Hdept.
     destruct E; try easy. simpl in *; subst.
     inv H2. inv Hdept.
     destruct E; try easy; simpl in *; subst.
     inv H2. inv HTy1. inv H5. apply Hswf in H1 as X1.
     destruct X1 as [va [ta [X1 X2]]];subst.
     apply eq_subtype_nat_1 in X1; subst.
     apply Stack.mapsto_always_same with (v1 := (v0, t0)) in X2; try easy. inv X2.
     exists env,(subst_type t x (Num va)).
     split; try easy.
     split; try easy.
     split; try easy.
     split. apply rheap_consistent_refl.
     split; try easy.
     split. apply env_consist_refl.
     destruct HQt as [X1 [X2 X3]].
     apply X3 in H0 as X4.
     split. apply TyLetNat; try easy. constructor.
     constructor. constructor. constructor. 
     apply well_typed_q_real with (y := v); try easy.
     exists (subst_type t x (Var v 0)).
     split. apply type_eq_q_subst; try easy.
     apply subtype_refl.
   (* T-Let *)
   - inv Hreduces. destruct E; inv H; simpl in *; subst; try easy.
     inv H2. inv HTy1; try easy. inv H2.
     apply eval_type_bound_idempotent with (s := s') in H5 as X1.
     inv HEwf. inv H3.
     apply eval_type_bound_preserve  with (t' := t') in X1; try easy; subst.
     exists env, t.
     split; try easy.
     split; try easy.
     split; try easy.
     split. apply rheap_consistent_refl.
     split; try easy.
     split. apply env_consist_refl.
     split. constructor; try easy.
     exists t. split. apply type_eq_refl. constructor. constructor.
     apply eval_type_bound_idempotent with (s := s') in H7 as X1; try easy.
     apply eval_type_bound_preserve with (t' := t') in X1; try easy; subst.
     exists env, t.
     split; try easy.
     split; try easy.
     split; try easy.
     split. apply rheap_consistent_refl.
     split; try easy.
     split. apply env_consist_refl.
     split. apply TyRet; try easy. intros R1;subst. 
     assert (is_checked (TPtr Checked t1)). constructor. easy.
     exists t. split. apply type_eq_refl. constructor. constructor.
     apply step_implies_reduces_1 with (cm := m) (E := E) (m := Checked) in H2; try easy.
     edestruct IH1; eauto. inv HEwf. easy.
     destruct H as [ta [X1 [X2 [X3 [X4 [X5 [X6 [X7 X8]]]]]]]].
     exists x0, t; auto.
     split; try easy.
     split; try easy.
     split; try easy.
     split; try easy.
     split; try easy.
     split; try easy.
     split. apply eq_subtype_ptr in X8 as X9. destruct X9; subst.
     apply TyLet with (m' := m') (t1 := x1); try easy.
     apply well_typed_env_grow with (env := (Env.add x (TPtr m' t1) x0)).
     intros. destruct (Nat.eq_dec x2 x); subst.
     apply Env.mapsto_add1 in H0.
     apply Env.mapsto_add1 in H. subst. easy.
     apply Env.add_3 in H. apply Env.add_3 in H0.
     apply Env.mapsto_always_same with (v1 := t') in H; try easy; subst.
     exists t0. split. apply type_eq_refl. constructor. constructor. lia. lia.
     apply well_typed_env_consist with (env0 := (Env.add x (TPtr m' t1) env)); try easy.
     unfold env_consistent in *. destruct X6.
     split. intros. split. intros.
     destruct (Nat.eq_dec x2 x); subst.
     destruct H1. apply Env.mapsto_add1 in H1;subst.
     exists (TPtr m' t1). apply Env.add_1. easy.
     destruct H1. apply Env.add_3 in H1; try lia.
     assert (Env.In x2 env). exists x3. easy. apply H in H3. destruct H3.
     exists x4. apply Env.add_2; try easy. lia.
     intros.
     destruct (Nat.eq_dec x2 x); subst.
     destruct H1. apply Env.mapsto_add1 in H1;subst.
     exists (TPtr m' t1). apply Env.add_1. easy.
     destruct H1. apply Env.add_3 in H1; try lia.
     assert (Env.In x2 x0). exists x3. easy. apply H in H3. destruct H3.
     exists x4. apply Env.add_2; try easy. lia.
     destruct H0. split. intros.
     destruct (Nat.eq_dec x2 x); subst. apply Env.mapsto_add1 in H4; subst.
     apply Env.add_1. easy. apply Env.add_3 in H4 ; try lia.
     apply Env.add_2; try lia. apply H0; try easy.
     intros. destruct (Nat.eq_dec x2 x); subst.
     apply Env.mapsto_add1 in H6. apply Env.mapsto_add1 in H4. subst.
     split.
     constructor. easy.
     apply Env.add_3 in H6. apply Env.add_3 in H4.
     eapply H1; try easy. apply H4. apply H6. lia. lia.
     apply well_typed_heap_consist with (R := R); try easy.
     exists t. split. apply type_eq_refl. constructor. constructor.


    (* T-RetNat *)
   - assert (X1 := Hreduces). inv Hreduces. destruct E;inv H; simpl in *; subst; try easy.
     assert (Env.In x env \/ ~ Env.In x env) as G1.
     destruct (Env.find x env) eqn:eq1. apply Env.find_2 in eq1. left. exists t0. easy.
     apply EnvFacts.not_find_in_iff in eq1. right. easy.
     destruct G1 as [G1 | G1].
   *
     inv H2. unfold inject_ret in *; destruct re; try easy; inv H9.
     inv HEwf.
     assert (env_wt D Checked (Env.add x TNat env)).
     unfold env_wt in *. intros. destruct (Nat.eq_dec x0 x); subst.
     apply Env.mapsto_add1 in H; subst. split. easy. split. constructor.
     unfold well_type_bound_in. intros. simpl in *. easy.
     apply Env.add_3 in H. apply Henvt in H. destruct H as [X2 [X3 X4]].
     split. easy. split. easy. unfold well_type_bound_in. intros.
     destruct (Nat.eq_dec x1 x); subst. apply Env.add_1. easy.
     apply X4 in H. apply Env.add_2. lia. easy. lia.
     specialize (IH1 H5 H (Stack.add x (na, TNat) s)).
     edestruct IH1; eauto.
     unfold stack_wt in *. intros. destruct (Nat.eq_dec x0 x); subst. apply Stack.mapsto_add1 in H0.
     inv H0. split. easy. split. constructor. easy.
     apply Stack.add_3 in H0. apply Hswt in H0; try easy. lia.
     destruct HQt as [A1 [A2 A3]].
     unfold theta_wt in *. split. intros. split. intros.
     destruct (Nat.eq_dec x0 x); subst. apply Env.add_1. easy.
     destruct H0. apply Theta.add_3 in H0. assert (Theta.In x0 Q). exists x1. easy.
     apply A1 in H1. apply Env.add_2. lia. easy. lia.
     intros. destruct (Nat.eq_dec x0 x); subst. exists (NumEq (Num na)). apply Theta.add_1. easy.
     apply Env.add_3 in H0. apply A1 in H0. destruct H0. exists x1.
     apply Theta.add_2; try lia. easy. lia.
     split. intros. destruct (Nat.eq_dec x0 x); subst. apply Theta.mapsto_add1 in H0.
     inv H0. apply Theta.add_3 in H0. apply Stack.add_3 in H1. eapply A2; eauto. lia. lia.
     intros. destruct (Nat.eq_dec x0 x); subst. apply Stack.mapsto_add1 in H0.
     inv H0. apply Theta.add_1. easy. apply Stack.add_3 in H0. apply Theta.add_2. lia.
     apply A3 in H0. easy. lia.
     unfold same_domain; split; intros. destruct (Nat.eq_dec x0 x); subst. exists (na,TNat). apply Stack.add_1. easy.
     destruct H0. apply Env.add_3 in H0. assert (Env.In x0 env). exists x1. easy. apply HDom in H1.
     destruct H1. exists x2. apply Stack.add_2. lia. easy. lia.
     destruct (Nat.eq_dec x0 x); subst. exists TNat. apply Env.add_1. easy.
     destruct H0. apply Stack.add_3 in H0. assert (Stack.In x0 s). exists x1. easy. apply HDom in H1.
     destruct H1. exists x2. apply Env.add_2. lia. easy. lia.
     unfold stack_wf in *. intros.
     destruct (Nat.eq_dec x0 x); subst. apply Env.mapsto_add1 in H0. subst.
     exists na, TNat. split. exists TNat. split. apply type_eq_refl. constructor. constructor.
     apply Stack.add_1. easy. apply Env.add_3 in H0. apply Hswf in H0.
     destruct H0 as [va [ta [B1 B2]]]. exists va,ta. split. destruct B1. destruct H0.
     exists x1. split. apply type_eq_q_add; try easy. apply subtype_q_add; try easy.
     apply Stack.add_2. lia. easy. lia.
     unfold stack_rheap_consistent in *. intros.
     destruct (Nat.eq_dec x0 x); subst. apply Stack.mapsto_add1 in H1. inv H1.
     constructor. eapply HsHwf; eauto. apply Stack.add_3 in H1; try easy. apply H1. lia.
     apply step_implies_reduces_1 with (cm:=Checked) (E := CHole) (m := Checked) in H11. simpl in *. apply H11. easy.
     destruct H0 as [ta [Y1 [Y2 [Y3 [Y4 [Y5 [Y6 [Y7 Y8]]]]]]]].
     apply step_stack_consist in H11 as Y9. simpl in *.
     apply stack_consist_wt with (D:=D) (m := Checked) in Y9 as Y10; try easy.
     2: { unfold stack_wt in *. intros. destruct (Nat.eq_dec x1 x);subst.
          apply Stack.mapsto_add1 in H0;subst. inv H0. split. easy. split. easy. easy.
          apply Stack.add_3 in H0. apply Hswt in H0. easy. lia.
        }
     assert (nb' = na /\ tb' = TNat).
     destruct Y9 as [B1 [B2 B3]].
     assert (Stack.MapsTo x (na, TNat) (Stack.add x (na, TNat) s)). apply Stack.add_1. easy.
     apply B2 in H0; try easy. apply Stack.mapsto_always_same with (v1 := (na,TNat)) in H10; try easy. inv H10. easy.
     destruct H0 as [B1 B2];subst.
     destruct G1 as [tc G1]. apply Hswf in G1 as G2. destruct G2 as [vc [tc' [G2 G3]]].
     apply Stack.mapsto_always_same with (v1 := (vc,tc')) in H4; try easy. inv H4.
     exists (Env.add x tc (subst_env x0 x (Num na))),(subst_type ta x (Num na)).
     split. unfold same_domain; split;intros.
     destruct (Nat.eq_dec x1 x); subst. exists (a', ta'). apply Stack.add_1. easy.
     destruct H0. apply Env.add_3 in H0; try lia.
     assert (Env.In x1 x0). apply EnvFacts.map_mapsto_iff in H0. destruct H0 as [tx [A1 A2]]; subst.
     exists tx. easy. apply Y1 in H1.
     destruct H1. exists x3. apply Stack.add_2. lia. easy.
     destruct (Nat.eq_dec x1 x); subst. exists tc. apply Env.add_1. easy.
     destruct H0. apply Stack.add_3 in H0. assert (Stack.In x1 s'0). exists x2. easy. apply Y1 in H1.
     destruct H1. apply Env.map_1 with (f := fun a => subst_type a x (Num na)) in H1.
     exists (subst_type x3 x (Num na)). apply Env.add_2. lia. easy. lia.
     split. unfold stack_wf in *. intros.
     destruct (Nat.eq_dec x1 x); subst. apply Env.mapsto_add1 in H0; subst.
     exists a',ta'. split. easy. apply Stack.add_1. easy.
     apply Env.add_3 in H0; try lia.
     apply EnvFacts.map_mapsto_iff in H0 as G4.
     destruct G4 as [t0a [G4 G5]]; subst. apply Y2 in G5 as G6. destruct G6 as [va [t0b [G6 G7]]].
     apply eq_subtype_subst_1 in G6; try easy.
     apply Y10 in G7 as G8. destruct G8 as [G8 [G9 G10]].
     rewrite simple_subst_type_same in G6; try easy.
     exists va,t0b. split. easy. apply Stack.add_2; try lia. easy.
     split. unfold theta_wt in *.
     destruct Y3 as [B1 [B2 B3]]. split. intros. split. intros.
     destruct (Nat.eq_dec x1 x); subst. easy.
     specialize (B1 x1). assert (Theta.In (elt:=theta_elem) x1 (Theta.add x (NumEq (Num na)) Q)).
     destruct H0. exists x2. apply Theta.add_2. lia. easy.
     apply B1 in H1. apply Env.add_2. lia.
     apply Env.map_1 with (f := (fun t => subst_type t x (Num na))) in H1. eauto.
     intros. destruct (Nat.eq_dec x1 x); subst. apply Env.mapsto_add1 in H0; subst.
     destruct HQt. apply H0 in G1. easy.
     apply Env.add_3 in H0; try lia.
     unfold subst_env in H0. apply EnvFacts.map_mapsto_iff in H0.
     destruct H0. destruct H0. destruct x2; try easy.
     apply B1 in H1.
     destruct H1. apply Theta.add_3 in H1; try lia. exists x2; try easy.
     split. intros.
     assert (x1 <> x). intros R1; subst.
     assert (Theta.In x Q). exists GeZero. easy. easy.
     assert (Theta.MapsTo x1 GeZero (Theta.add x (NumEq (Num na)) Q)).
     apply Theta.add_2. lia. easy. apply B2 with (n := n) in H4; try easy.
     apply Stack.add_3 in H1; try easy. lia.
     intros. 
     destruct (Nat.eq_dec x1 x); subst.
     apply Stack.mapsto_add1 in H0. inv H0.
     destruct HQt as [B4 [B5 B6]].
     apply B6 in G3; try easy.
     apply Stack.add_3 in H0; try lia. apply B3 in H0; try easy.
     apply Theta.add_3 in H0; try easy. lia.
     split. easy.
     split. destruct R as [Hchk Htnt].
     unfold stack_rheap_consistent in *. intros. 
     destruct (Nat.eq_dec x1 x); subst. apply Stack.mapsto_add1 in H1. inv H1.
     apply (HsHwf Hchk Htnt) in G3; try easy.
     unfold rheap_consistent in *. 
     apply (Y4 Hchk0 Htnt0 Hchk Htnt) in G3; try easy.
     apply Stack.add_3 in H1; try lia. apply (Y5 Hchk0 Htnt0) in H1; try easy.
     split. 
     unfold env_consistent in *. destruct Y6 as [B1 [B2 B3]].
     split. intros. split. intros.
     destruct (Nat.eq_dec x1 x); subst. exists tc.
     apply Env.add_1. easy.
     assert (Env.In (elt:=type) x1 (Env.add x TNat env)).
     destruct H0. exists x2. apply Env.add_2; try lia. easy.
     apply B1 in H1. destruct H1. exists (subst_type x2 x (Num na)).
     apply Env.add_2; try lia.
     unfold subst_env. apply Env.map_1 with (f := (fun t0 => subst_type t0 x (Num na))) in H1; try easy.
     intros. destruct H0.
     destruct (Nat.eq_dec x1 x); subst. exists tc; easy.
     apply Env.add_3 in H0; try lia.
     apply EnvFacts.map_mapsto_iff in H0. destruct H0 as [tb [B4 B5]];subst.
     assert (Env.In x1 x0). exists tb. easy. apply B1 in H0.
     destruct H0. apply Env.add_3 in H0; try lia. exists x2. easy.
     split; intros. destruct (Nat.eq_dec x1 x); subst.
     apply Env.mapsto_always_same with (v1 := tc) in H1; subst. apply Env.add_1. easy.
     easy. apply Env.add_2; try lia. apply Henvt in H1 as B4.
     destruct B4 as [B4 [B5 B6]].
     unfold well_type_bound_in in B6.
     assert (~ Env.MapsTo x TNat env). intros R1.
     destruct HQt. apply H3 in R1. easy.
     assert (~ In x (freeTypeVars t0)). intros R1. apply B6 in R1. easy.
     rewrite <- not_in_subst_same with (t := t0) (x := x) (v := (Num na)); try easy.
     assert (Env.MapsTo x1 t0 (Env.add x TNat env)).
     apply Env.add_2; try lia. easy. apply B2 in H6.
     apply Env.map_1 with (f := fun a => subst_type a x (Num na)) in H6. eauto. easy.
     destruct (Nat.eq_dec x1 x); subst. 
     apply Env.mapsto_always_same with (v1 := tc) in H1; try easy; subst.
     apply Env.mapsto_add1 in H3; subst. split.
     constructor. unfold both_simple;intros;easy. apply Env.add_3 in H3; try lia.
     apply EnvFacts.map_mapsto_iff in H3 as A1.
     destruct A1 as [td [A1 A2]]; subst.
     apply B3 with (t := t0) in A2 ; try easy. destruct A2 as [A2 A3].
     apply subtype_core_q_subst in A2; try easy. destruct HQt.
     assert (~ Env.MapsTo x TNat env). intros R1. apply H4 in R1. easy.
     assert (~ In x (freeTypeVars t0)). intros R1. apply Henvt in H1.
     destruct H1 as [A4 [A5 A6]]. unfold well_type_bound_in in A6. apply A6 in R1. easy.
     split.
     rewrite (not_in_subst_same t0) in A2; try easy. unfold both_simple in *; intros. apply A3 in H9. 
     rewrite simple_subst_type_same. easy. easy.
     apply Env.add_2; try easy. lia.
     split. apply TyRetTNat; try easy.
     apply well_typed_env_consist with (env0 := (subst_env x0 x (Num na))).
     unfold env_consistent. split. intros.
     split. intros. destruct H0. destruct (Nat.eq_dec x1 x); subst. exists TNat.
     apply Env.add_1. easy. exists x2. repeat apply Env.add_2; try lia. easy.
     intros. destruct (Nat.eq_dec x1 x); subst. destruct H0. 
     destruct Y6. specialize (H1 x). assert (Env.In x (Env.add x TNat env)). exists TNat.
     apply Env.add_1. easy. apply H1 in H4. destruct H4. exists (subst_type x2 x (Num na)).
     apply EnvFacts.map_mapsto_iff. exists x2; try easy.
     destruct H0. apply Env.add_3 in H0; try lia. apply Env.add_3 in H0; try lia.
     exists x2. easy. split; intros. destruct (Nat.eq_dec x1 x); subst.
     destruct Y6. destruct H4. assert (Env.MapsTo x TNat (Env.add x TNat env)).
     apply Env.add_1. easy. apply H4 in H7; try easy.
     apply Env.map_1 with (f := fun a => subst_type a x (Num na)) in H7; try easy.
     simpl in H7. unfold subst_env in H1. apply Env.mapsto_always_same with (v1 := t0) in H7; try easy; subst.
     apply Env.add_1. easy.
     repeat apply Env.add_2; try lia. easy.
     destruct (Nat.eq_dec x1 x); subst.
     apply Env.mapsto_add1 in H3; subst.
     destruct Y6. destruct H4. assert (Env.MapsTo x TNat (Env.add x TNat env)).
     apply Env.add_1. easy. apply H4 in H7; try easy.
     apply Env.map_1 with (f := fun a => subst_type a x (Num na)) in H7; try easy.
     simpl in H7. unfold subst_env in H1. apply Env.mapsto_always_same with (v1 := t0) in H7; try easy; subst.
     split.
     constructor. unfold both_simple in *; intros; easy.
     apply Env.add_3 in H3; try lia. apply Env.add_3 in H3; try lia.
     apply Env.mapsto_always_same with (v1 := t0) in H3; try easy; subst.
     split. constructor. unfold both_simple in *; intros; easy.
     apply well_typed_env_consist_1. apply Theta.add_1. easy. easy.
     apply eq_subtype_subst_1; try easy.
     destruct G1. apply Hswf in H. destruct H as [va [ta [A1 A2]]]. 
     assert (Stack.In (elt:=Z * type) x s). exists (va,ta). easy. easy.
     inv X1. destruct E; try easy. simpl in H; subst. inv H2; try easy.
     destruct G1. simpl in *. inv HTy1. exists env,t.
     split; try easy.
     split; try easy.
     split; try easy.
     split. apply rheap_consistent_refl.
     split; try easy.
     split. apply env_consist_refl. split. constructor; try easy.
     apply simple_means_not_freeVars in H7.
     assert (~ In x (freeTypeVars t)). rewrite H7. simpl. easy.
     rewrite (not_in_subst_same); try easy. exists t. split. apply type_eq_refl.
     constructor. constructor.
     exists env,t.
     split; try easy.
     split; try easy.
     split; try easy.
     split. apply rheap_consistent_refl.
     split; try easy.
     split. apply env_consist_refl. split. apply TyLitTainted; try easy.
     apply simple_means_not_freeVars in H9.
     assert (~ In x (freeTypeVars t)). rewrite H9. simpl. easy.
     rewrite (not_in_subst_same); try easy. exists t. split. apply type_eq_refl.
     constructor. constructor.
   *
     inv H2. assert (Stack.In x s). exists (a',ta'). easy. apply HDom in H. easy.
     unfold inject_ret in *; destruct re; try easy; inv H9.
     inv HEwf.
     assert (env_wt D Checked (Env.add x TNat env)).
     unfold env_wt in *. intros. destruct (Nat.eq_dec x0 x); subst.
     apply Env.mapsto_add1 in H; subst. split. easy. split. constructor.
     unfold well_type_bound_in. intros. simpl in *. easy.
     apply Env.add_3 in H. apply Henvt in H. destruct H as [X2 [X3 X4]].
     split. easy. split. easy. unfold well_type_bound_in. intros.
     destruct (Nat.eq_dec x1 x); subst. apply Env.add_1. easy.
     apply X4 in H. apply Env.add_2. lia. easy. lia.
     specialize (IH1 H5 H (Stack.add x (na, TNat) s)).
     edestruct IH1; eauto.
     unfold stack_wt in *. intros. destruct (Nat.eq_dec x0 x); subst. apply Stack.mapsto_add1 in H0.
     inv H0. split. easy. split. constructor. easy.
     apply Stack.add_3 in H0. apply Hswt in H0; try easy. lia.
     destruct HQt as [A1 [A2 A3]].
     unfold theta_wt in *. split. intros. split. intros.
     destruct (Nat.eq_dec x0 x); subst. apply Env.add_1. easy.
     destruct H0. apply Theta.add_3 in H0. assert (Theta.In x0 Q). exists x1. easy.
     apply A1 in H1. apply Env.add_2. lia. easy. lia.
     intros. destruct (Nat.eq_dec x0 x); subst. exists (NumEq (Num na)). apply Theta.add_1. easy.
     apply Env.add_3 in H0. apply A1 in H0. destruct H0. exists x1.
     apply Theta.add_2; try lia. easy. lia.
     split. intros. destruct (Nat.eq_dec x0 x); subst. apply Theta.mapsto_add1 in H0.
     inv H0. apply Theta.add_3 in H0. apply Stack.add_3 in H1. eapply A2; eauto. lia. lia.
     intros. destruct (Nat.eq_dec x0 x); subst. apply Stack.mapsto_add1 in H0.
     inv H0. apply Theta.add_1. easy. apply Stack.add_3 in H0. apply Theta.add_2. lia.
     apply A3 in H0. easy. lia.
     unfold same_domain; split; intros. destruct (Nat.eq_dec x0 x); subst. exists (na,TNat). apply Stack.add_1. easy.
     destruct H0. apply Env.add_3 in H0. assert (Env.In x0 env). exists x1. easy. apply HDom in H1.
     destruct H1. exists x2. apply Stack.add_2. lia. easy. lia.
     destruct (Nat.eq_dec x0 x); subst. exists TNat. apply Env.add_1. easy.
     destruct H0. apply Stack.add_3 in H0. assert (Stack.In x0 s). exists x1. easy. apply HDom in H1.
     destruct H1. exists x2. apply Env.add_2. lia. easy. lia.
     unfold stack_wf in *. intros.
     destruct (Nat.eq_dec x0 x); subst. apply Env.mapsto_add1 in H0. subst.
     exists na, TNat. split. exists TNat. split. apply type_eq_refl. constructor. constructor.
     apply Stack.add_1. easy. apply Env.add_3 in H0. apply Hswf in H0.
     destruct H0 as [va [ta [B1 B2]]]. exists va,ta. split. destruct B1. destruct H0.
     exists x1. split. apply type_eq_q_add; try easy. apply subtype_q_add; try easy.
     apply Stack.add_2. lia. easy. lia.
     unfold stack_rheap_consistent in *. intros.
     destruct (Nat.eq_dec x0 x); subst. apply Stack.mapsto_add1 in H1. inv H1.
     constructor. eapply HsHwf; eauto. apply Stack.add_3 in H1; try easy. apply H1. lia.
     apply step_implies_reduces_1 with (cm:=Checked)
         (E := CHole) (m := Checked) in H11. simpl in *. apply H11. easy.
     destruct H0 as [ta [Y1 [Y2 [Y3 [Y4 [Y5 [Y6 [Y7 Y8]]]]]]]].
     apply step_stack_consist in H11 as Y9. simpl in *.
     apply stack_consist_wt with (D:=D) (m := Checked) in Y9 as Y10; try easy.
     2: { unfold stack_wt in *. intros. destruct (Nat.eq_dec x1 x);subst.
          apply Stack.mapsto_add1 in H0;subst. inv H0. split. easy. split. easy. easy.
          apply Stack.add_3 in H0. apply Hswt in H0. easy. lia.
        }
     assert (nb' = na /\ tb' = TNat).
     destruct Y9 as [B1 [B2 B3]].
     assert (Stack.MapsTo x (na, TNat) (Stack.add x (na, TNat) s)). apply Stack.add_1. easy.
     apply B2 in H0; try easy. apply Stack.mapsto_always_same with (v1 := (na,TNat)) in H10; try easy. inv H10. easy.
     destruct H0 as [B1 B2];subst. rename H4 into G2.
     exists (Env.remove x (subst_env x0 x (Num na))),(subst_type ta x (Num na)).
     split. unfold same_domain; split;intros.
     destruct (Nat.eq_dec x1 x); subst.
     assert (~ Env.In (elt:=type) x
       (Env.remove (elt:=type) x (subst_env x0 x (Num na)))).
     apply Env.remove_1. easy. easy. destruct H0. apply Env.remove_3 in H0.
     apply EnvFacts.map_mapsto_iff in H0.
     destruct H0 as [tx [A1 A2]];subst. assert (Env.In x1 x0). exists tx. easy.
     apply Y1 in H0. destruct H0. exists x2. apply Stack.remove_2; try lia. easy.
     destruct (Nat.eq_dec x1 x); subst.
     assert (~ Stack.In (elt:=Z * type) x (Stack.remove (elt:=Z * type) x s'0)).
     apply Stack.remove_1; try easy. easy.
     destruct H0. apply Stack.remove_3 in H0. assert (Stack.In x1 s'0). exists x2. easy.
     apply Y1 in H1. destruct H1. exists (subst_type x3 x (Num na)).
     apply Env.remove_2; try lia. apply Env.map_1 with (f := fun a => subst_type a x (Num na)) in H1; try easy.
     split. unfold stack_wf in *. intros.
     destruct (Nat.eq_dec x1 x); subst.
     assert (Env.In x (Env.remove (elt:=type) x (subst_env x0 x (Num na)))).
     exists t0. easy.
     assert (~ Env.In x (Env.remove (elt:=type) x (subst_env x0 x (Num na)))).
     apply Env.remove_1; try easy. easy.
     apply Env.remove_3 in H0; try lia.
     apply EnvFacts.map_mapsto_iff in H0 as G4.
     destruct G4 as [t0a [G4 G5]]; subst. apply Y2 in G5 as G6. destruct G6 as [va [t0b [G6 G7]]].
     apply eq_subtype_subst_1 in G6; try easy.
     apply Y10 in G7 as G8. destruct G8 as [G8 [G9 G10]].
     rewrite simple_subst_type_same in G6; try easy.
     exists va,t0b. split. easy. apply Stack.remove_2; try lia. easy.
     split. unfold theta_wt in *.
     destruct Y3 as [B1 [B2 B3]]. split. intros. split. intros.
     destruct (Nat.eq_dec x1 x); subst. easy.
     specialize (B1 x1). assert (Theta.In (elt:=theta_elem) x1 (Theta.add x (NumEq (Num na)) Q)).
     destruct H0. exists x2. apply Theta.add_2. lia. easy.
     apply B1 in H1. apply Env.remove_2. lia.
     apply Env.map_1 with (f := (fun t => subst_type t x (Num na))) in H1. eauto.
     intros. destruct (Nat.eq_dec x1 x); subst.
     assert (Env.In x
       (Env.remove (elt:=type) x (subst_env x0 x (Num na)))).
     exists TNat. easy.
     assert (~ Env.In x
       (Env.remove (elt:=type) x (subst_env x0 x (Num na)))).
     apply Env.remove_1. easy. easy.
     apply Env.remove_3 in H0; subst.
     assert (TNat = subst_type TNat x (Num na)). easy. rewrite H1 in H0.
     apply EnvFacts.map_mapsto_iff in H0. destruct H0 as [tx [A1 A2]];subst.
     rewrite <- H1 in A1. destruct tx; try easy.
     apply B1 in A2. destruct A2. apply Theta.add_3 in H0; try lia. exists x2. easy.
     split. intros.
     assert (x1 <> x). intros R1; subst.
     assert (Theta.In x Q). exists GeZero. easy. easy.
     assert (Theta.MapsTo x1 GeZero (Theta.add x (NumEq (Num na)) Q)).
     apply Theta.add_2. lia. easy. apply B2 with (n := n) in H4; try easy.
     apply Stack.remove_3 in H1; try easy.
     intros. 
     destruct (Nat.eq_dec x1 x); subst.
     assert (Stack.In x (Stack.remove (elt:=Z * type) x s'0)).
     exists (n,TNat). easy.
     assert (~ Stack.In x (Stack.remove (elt:=Z * type) x s'0)).
     apply Stack.remove_1; try easy. easy.
     apply Stack.remove_3 in H0. apply B3 in H0. apply Theta.add_3 in H0; try lia. easy.
     split. easy.
     split. unfold stack_rheap_consistent in *. intros.
     destruct (Nat.eq_dec x1 x); subst.
     assert (Stack.In x (Stack.remove (elt:=Z * type) x s'0)). exists (n,t0). easy.
     assert (~ Stack.In x (Stack.remove (elt:=Z * type) x s'0)). apply Stack.remove_1; try easy. easy.
     apply Stack.remove_3 in H1. apply (Y5 Hchk Htnt) in H1; try easy. 
     split. 
     unfold env_consistent in *. destruct Y6 as [B1 [B2 B3]].
     split. intros. split. intros.
     destruct (Nat.eq_dec x1 x); subst. easy. 
     assert (Env.In (elt:=type) x1 (Env.add x TNat env)).
     destruct H0. exists x2. apply Env.add_2; try lia. easy.
     apply B1 in H1. destruct H1. exists (subst_type x2 x (Num na)).
     apply Env.remove_2; try lia.
     unfold subst_env. apply Env.map_1 with (f := (fun t0 => subst_type t0 x (Num na))) in H1; try easy.
     intros. 
     destruct (Nat.eq_dec x1 x); subst.
     assert (~ Env.In (elt:=type) x
       (Env.remove (elt:=type) x (subst_env x0 x (Num na)))).
     apply Env.remove_1; try easy. easy.
     destruct H0.
     apply Env.remove_3 in H0; try lia.
     apply EnvFacts.map_mapsto_iff in H0. destruct H0 as [tb [B4 B5]];subst.
     assert (Env.In x1 x0). exists tb. easy. apply B1 in H0.
     destruct H0. apply Env.add_3 in H0; try lia. exists x2. easy.
     split; intros. destruct (Nat.eq_dec x1 x); subst.
     assert (Env.In x env). exists t0. easy. easy.
     apply Env.remove_2; try lia. apply Henvt in H1 as B4.
     destruct B4 as [B4 [B5 B6]].
     unfold well_type_bound_in in B6.
     assert (~ Env.MapsTo x TNat env). intros R1.
     destruct HQt. apply H3 in R1. easy.
     assert (~ In x (freeTypeVars t0)). intros R1. apply B6 in R1. easy.
     rewrite <- not_in_subst_same with (t := t0) (x := x) (v := (Num na)); try easy.
     assert (Env.MapsTo x1 t0 (Env.add x TNat env)).
     apply Env.add_2; try lia. easy. apply B2 in H6.
     apply Env.map_1 with (f := fun a => subst_type a x (Num na)) in H6. eauto. easy.
     destruct (Nat.eq_dec x1 x); subst. 
     assert (Env.In x env). exists t0. easy. easy.
     apply Env.remove_3 in H3; try lia.
     apply EnvFacts.map_mapsto_iff in H3 as A1.
     destruct A1 as [td [A1 A2]]; subst.
     apply B3 with (t := t0) in A2 ; try easy. destruct A2 as [A2 A3].
     apply subtype_core_q_subst in A2; try easy. destruct HQt.
     assert (~ Env.MapsTo x TNat env). intros R1. apply H4 in R1. easy.
     assert (~ In x (freeTypeVars t0)). intros R1. apply Henvt in H1.
     destruct H1 as [A4 [A5 A6]]. unfold well_type_bound_in in A6. apply A6 in R1. easy.
     split.
     rewrite (not_in_subst_same t0) in A2; try easy.
     unfold both_simple in *;intros. rewrite simple_subst_type_same; try easy. auto. auto.
     apply Env.add_2; try easy. lia.
     split. apply TyRetTNat; try easy.
     apply well_typed_env_consist with (env0 := (subst_env x0 x (Num na))).
     unfold env_consistent. split. intros.
     split. intros. destruct H0. destruct (Nat.eq_dec x1 x); subst. exists TNat.
     apply Env.add_1. easy. exists x2. apply Env.add_2; try lia. apply Env.remove_2; try lia. easy.
     intros. destruct (Nat.eq_dec x1 x); subst. destruct H0. 
     destruct Y6. specialize (H1 x). assert (Env.In x (Env.add x TNat env)). exists TNat.
     apply Env.add_1. easy. apply H1 in H4. destruct H4. exists (subst_type x2 x (Num na)).
     apply EnvFacts.map_mapsto_iff. exists x2; try easy.
     destruct H0. apply Env.add_3 in H0; try lia. apply Env.remove_3 in H0; try lia.
     exists x2. easy. split; intros. destruct (Nat.eq_dec x1 x); subst.
     destruct Y6. destruct H4. assert (Env.MapsTo x TNat (Env.add x TNat env)).
     apply Env.add_1. easy. apply H4 in H7; try easy.
     apply Env.map_1 with (f := fun a => subst_type a x (Num na)) in H7; try easy.
     simpl in H7. unfold subst_env in H1. apply Env.mapsto_always_same with (v1 := t0) in H7; try easy; subst.
     apply Env.add_1. easy.
     apply Env.add_2; try lia. apply Env.remove_2; try lia. easy.
     destruct (Nat.eq_dec x1 x); subst.
     apply Env.mapsto_add1 in H3; subst.
     destruct Y6. destruct H4. assert (Env.MapsTo x TNat (Env.add x TNat env)).
     apply Env.add_1. easy. apply H4 in H7; try easy.
     apply Env.map_1 with (f := fun a => subst_type a x (Num na)) in H7; try easy.
     simpl in H7. unfold subst_env in H1. apply Env.mapsto_always_same with (v1 := t0) in H7; try easy; subst.
     split.
     constructor. unfold both_simple; intros;easy.
     apply Env.add_3 in H3; try lia. apply Env.remove_3 in H3; try lia.
     apply Env.mapsto_always_same with (v1 := t0) in H3; try easy; subst.
     split. constructor. unfold both_simple in *; intros; easy.
     apply well_typed_env_consist_1. apply Theta.add_1. easy. easy.
     apply eq_subtype_subst_1; try easy.
     inv HTy1. exists env,t.
     split; try easy.
     split; try easy.
     split; try easy.
     split. apply rheap_consistent_refl.
     split; try easy.
     split. apply env_consist_refl. split. constructor; try easy.
     apply simple_means_not_freeVars in H4.
     assert (~ In x (freeTypeVars t)). rewrite H4. simpl. easy.
     rewrite (not_in_subst_same); try easy. exists t. split. apply type_eq_refl.
     constructor. constructor.
     exists env,t.
     split; try easy.
     split; try easy.
     split; try easy.
     split. apply rheap_consistent_refl.
     split; try easy.
     split. apply env_consist_refl. split. apply TyLitTainted; try easy.
     apply simple_means_not_freeVars in H6.
     assert (~ In x (freeTypeVars t)). rewrite H6. simpl. easy.
     rewrite (not_in_subst_same); try easy. exists t. split. apply type_eq_refl.
     constructor. constructor.
    (* T-RetChecked *)
   - assert (X1 := Hreduces). inv Hreduces. destruct E;inv H; simpl in *; subst; try easy.
     assert (Env.In x env \/ ~ Env.In x env) as G1.
     destruct (Env.find x env) eqn:eq1. apply Env.find_2 in eq1. left. exists t0. easy.
     apply EnvFacts.not_find_in_iff in eq1. right. easy.
     destruct G1 as [G1 | G1].
   *
     inv H2. unfold inject_ret in *; destruct re; try easy; inv H10.
     inv HEwf.
     assert (env_wt D Checked (Env.add x (TPtr Checked ta) env)).
     unfold env_wt in *. intros. destruct (Nat.eq_dec x0 x); subst.
     apply Env.mapsto_add1 in H; subst. split. easy.
     destruct H2 as [A1 [A2 A3]].
     split. easy.
     unfold well_type_bound_in. intros.
     apply simple_means_not_freeVars in A3; try easy. rewrite A3 in H. simpl in *. easy.
     apply Env.add_3 in H. apply Henvt in H. destruct H as [X2 [X3 X4]].
     split. easy. split. easy. unfold well_type_bound_in. intros.
     destruct (Nat.eq_dec x1 x); subst.
     destruct HQt as [B1 [B2 B3]].
     assert (~ Env.MapsTo x TNat env). intros R1. apply B1 in R1. easy.
     destruct G1. assert (x1 <> TNat). intros R2; subst. easy.
     apply X4 in H as G2. easy.
     apply Env.add_2. lia. apply X4. easy. lia. 
     assert (Checked = Checked) by easy.
     specialize (IH1 H6 H (Stack.add x (na, TPtr Checked ta) s)).
     edestruct IH1; eauto.
     unfold stack_wt in *. intros. destruct (Nat.eq_dec x0 x); subst. apply Stack.mapsto_add1 in H1.
     inv H1. split. easy. destruct H2 as [A1 [A2 A3]]. split. easy. easy.
     apply Stack.add_3 in H1. apply Hswt in H1; try easy. lia.
     destruct HQt as [A1 [A2 A3]].
     unfold theta_wt in *. split. intros. split; intros.
     destruct (Nat.eq_dec x0 x); subst. easy. apply Env.add_2; try lia. apply A1. easy.
     destruct (Nat.eq_dec x0 x); subst. apply Env.mapsto_add1 in H1. inv H1.
     apply Env.add_3 in H1; try lia. apply A1 in H1. destruct H1. exists x1.
     easy.
     split. intros. destruct (Nat.eq_dec x0 x); subst. apply Stack.mapsto_add1 in H3; try easy.
     apply Stack.add_3 in H3. eapply A2; eauto. lia.
     intros. destruct (Nat.eq_dec x0 x); subst. apply Stack.mapsto_add1 in H1; try easy.
     apply Stack.add_3 in H1.
     apply A3 in H1. easy. lia.
     unfold same_domain; split; intros. destruct (Nat.eq_dec x0 x); subst. exists (na, TPtr Checked ta).
     apply Stack.add_1. easy.
     destruct H1. apply Env.add_3 in H1. assert (Env.In x0 env). exists x1. easy. apply HDom in H3.
     destruct H3. exists x2. apply Stack.add_2. lia. easy. lia.
     destruct (Nat.eq_dec x0 x); subst. exists (TPtr Checked ta). apply Env.add_1. easy.
     destruct H1. apply Stack.add_3 in H1. assert (Stack.In x0 s). exists x1. easy. apply HDom in H3.
     destruct H3. exists x2. apply Env.add_2. lia. easy. lia.
     unfold stack_wf in *. intros.
     destruct (Nat.eq_dec x0 x); subst. apply Env.mapsto_add1 in H1. subst.
     exists na, (TPtr Checked ta). split. exists (TPtr Checked ta). split.
     apply type_eq_refl. constructor. constructor.
     apply Stack.add_1. easy. apply Env.add_3 in H1. apply Hswf in H1.
     destruct H1 as [va [tx [B1 B2]]]. exists va,tx. split. destruct B1. destruct H1.
     exists x1; try easy.
     apply Stack.add_2. lia. easy. lia.
     unfold stack_rheap_consistent in *. intros.
     destruct (Nat.eq_dec x0 x); subst. apply Stack.mapsto_add1 in H3. inv H3. eauto.
     eapply HsHwf; eauto. apply Stack.add_3 in H3; try easy. apply H3. lia.
     apply step_implies_reduces_1 with (cm:=Checked) (E := CHole) (m := Checked) in H12. simpl in *. apply H12. easy.
     destruct H1 as [tx [Y1 [Y2 [Y3 [Y4 [Y5 [Y6 [Y7 Y8]]]]]]]].
     apply step_stack_consist in H12 as Y9. simpl in *.
     apply stack_consist_wt with (D:=D) (m := Checked) in Y9 as Y10; try easy.
     2: { unfold stack_wt in *. intros. destruct (Nat.eq_dec x1 x);subst.
          apply Stack.mapsto_add1 in H1;subst. inv H1. split. easy. split. easy. easy.
          apply Stack.add_3 in H1. apply Hswt in H1. easy. lia.
        }
     destruct G1 as [tv G1]. apply Hswf in G1 as K1.
     destruct K1 as [a'0 [ta'0 [K1 K2]]].
     apply Stack.mapsto_always_same with (v1 := (a'0, ta'0)) in H4; try easy. inv H4; subst.
     rename K2 into H4.
     destruct Y9 as [B1 [B2 B3]].
     exists (Env.add x tv x0),tx.
     split. unfold same_domain; split;intros.
     destruct (Nat.eq_dec x1 x); subst. exists (a', ta'). apply Stack.add_1. easy.
     destruct H1. apply Env.add_3 in H1; try lia.
     assert (Env.In x1 x0). 
     exists x2. easy. apply Y1 in H3.
     destruct H3. exists x3. apply Stack.add_2. lia. easy.
     destruct (Nat.eq_dec x1 x); subst. exists tv. apply Env.add_1. easy.
     destruct H1. apply Stack.add_3 in H1. assert (Stack.In x1 s'0). exists x2. easy. apply Y1 in H3.
     destruct H3. exists x3. apply Env.add_2. lia. easy. lia.
     split. unfold stack_wf in *. intros.
     destruct (Nat.eq_dec x1 x); subst. apply Env.mapsto_add1 in H1; subst.
     exists a',ta'. split. easy. apply Stack.add_1. easy.
     apply Env.add_3 in H1; try lia.
     apply Y2 in H1 as G5. destruct G5 as [vq [tq [G5 G6]]].
     exists vq,tq. split. easy. apply Stack.add_2; try lia. easy.
     split. unfold theta_wt in *.
     destruct Y3 as [A1 [A2 A3]]. split. intros. split. intros.
     destruct (Nat.eq_dec x1 x); subst. easy. apply Env.add_2; try lia.
     apply A1. easy.
     intros. destruct (Nat.eq_dec x1 x); subst. apply Env.mapsto_add1 in H1; subst.
     destruct HQt. apply H1 in G1. easy.
     apply Env.add_3 in H1; try lia.
     apply A1 in H1. easy.
     split. intros.
     assert (x1 <> x). intros R1; subst.
     assert (Theta.In x Q). exists GeZero. easy. easy.
     apply Stack.add_3 in H3; try lia.
     eapply A2; eauto.
     intros. 
     destruct (Nat.eq_dec x1 x); subst.
     apply Stack.mapsto_add1 in H1. inv H1.
     destruct HQt as [B4 [B5 B6]].
     apply B6 in H4; try easy.
     apply Stack.add_3 in H1; try lia. apply A3 in H1; try easy.
     split. easy.
     split. unfold stack_rheap_consistent in *. intros.
     destruct R. subst.
     destruct (Nat.eq_dec x1 x); subst. apply Stack.mapsto_add1 in H3. inv H3.
     apply (HsHwf h h0) in H4; try easy.
     apply (Y4 Hchk Htnt h h0) in H4; try easy.
     apply Stack.add_3 in H3. apply (Y5 Hchk Htnt) in H3; try easy. lia.
     split. 
     unfold env_consistent in *. destruct Y6 as [A1 [A2 A3]].
     split. intros. split. intros.
     destruct (Nat.eq_dec x1 x); subst. exists tv.
     apply Env.add_1. easy.
     assert (Env.In (elt:=type) x1 (Env.add x (TPtr Checked ta) env)).
     destruct H1. exists x2. apply Env.add_2; try lia. easy.
     apply A1 in H3. destruct H3. exists x2.
     apply Env.add_2; try lia. easy.
     intros. destruct H1.
     destruct (Nat.eq_dec x1 x); subst. exists tv; easy.
     apply Env.add_3 in H1; try lia. 
     assert (Env.In x1 x0). exists x2. easy. apply A1 in H3. destruct H3.
     apply Env.add_3 in H3; try lia. exists x3. easy.
     split; intros. destruct (Nat.eq_dec x1 x); subst.
     apply Env.mapsto_always_same with (v1 := tv) in H3; subst. apply Env.add_1. easy.
     easy. apply Env.add_2; try lia.
     apply A2; try easy. apply Env.add_2; try lia. easy.
     destruct (Nat.eq_dec x1 x); subst. 
     apply Env.mapsto_always_same with (v1 := tv) in H3; try easy; subst.
     apply Env.mapsto_add1 in H7; subst. split.
     constructor. unfold both_simple in *; intros;easy.
     apply Env.add_3 in H7; try lia.
     apply A3 with (t := t0) in H7 ; try easy. apply Env.add_2; try lia. easy.
     split.
     specialize (or_nt_ptr (TPtr Checked ta)) as A1.
     destruct A1.
     assert (Stack.MapsTo x (na, TPtr Checked ta) (Stack.add x (na, TPtr Checked ta) s)).
     apply Stack.add_1. easy.
     apply B3 with (v' := nb') (t' := tb') in H3; try easy. destruct H3 as [H3 X4]; subst.
     apply eq_subtype_ptr in X4 as X5. destruct X5 as [tq X5]; subst.
     apply eq_subtype_nt_ptr in X4 as X5; try easy.
     apply TyRetChecked; try easy. apply Y10 in H11. destruct H11 as [X6 [X7 X8]]; try easy.
     destruct R'. destruct R.
     eapply Y5 in H11; try easy. auto. 
     apply well_typed_env_consist with (env0 := x0).
     unfold env_consistent. split. intros.
     split. intros. destruct H3. destruct (Nat.eq_dec x1 x); subst. exists (TPtr Checked tq).
     apply Env.add_1. easy. exists x2. repeat apply Env.add_2; try lia. easy.
     intros. destruct (Nat.eq_dec x1 x); subst. destruct H3. 
     destruct Y6. specialize (H7 x). assert (Env.In x (Env.add x (TPtr Checked ta) env)).
     exists (TPtr Checked ta).
     apply Env.add_1. easy. apply H7 in H9. easy.
     destruct H3. apply Env.add_3 in H3; try lia. apply Env.add_3 in H3; try lia.
     exists x2. easy.
     split; intros.
     destruct (Nat.eq_dec x1 x); subst.
     destruct Y6. destruct H9.
     assert (Env.MapsTo x (TPtr Checked ta) (Env.add x (TPtr Checked ta) env)).
     apply Env.add_1; try easy. apply H10 with (t' := t0) in H13; try easy.
     unfold is_nt_ptr in H1. destruct ta; try easy. destruct H13. inv H13; try easy.
     repeat apply Env.add_2; try lia. easy.
     destruct Y6. destruct H10.
     destruct (Nat.eq_dec x1 x); subst.
     apply Y2 in H7 as A1. destruct A1 as [vaa [taa [A1 A2]]].
     apply Stack.mapsto_always_same with (v1 := (vaa,taa)) in H11 ; try easy. inv H11.
     apply Env.mapsto_add1 in H8;subst. 
     assert (simple_type t0).
     assert (Env.MapsTo x (TPtr Checked ta) (Env.add x (TPtr Checked ta) env)). apply Env.add_1; try easy.
     apply H13 with (t' := t0) in H8 ; try easy. destruct H8. apply H11; easy.
     apply eq_subtype_simple_same in A1; try easy.
     apply subtype_nt_ptr_1 in A1; try easy. split. easy.
     apply Y10 in A2; try easy.
     apply Y10 in A2; try easy.
     apply Env.add_3 in H8; try lia.
     apply Env.add_3 in H8; try lia.
     apply Env.mapsto_always_same with (v1 := t0) in H8; subst. split. constructor.
     easy. easy. easy.
     assert (Stack.MapsTo x (na, TPtr Checked ta) (Stack.add x (na, TPtr Checked ta) s)).
     apply Stack.add_1. easy. apply B2 in H3.
     apply Stack.mapsto_always_same with (v1:= (nb', tb')) in H3; try easy. inv H3. 
     destruct Y6 as [A1 [A2 A3]].
     assert (Env.MapsTo x (TPtr Checked ta) (Env.add x (TPtr Checked ta) env)).
     apply Env.add_1; try easy.
     apply A2 in H3;try easy.
     apply TyRetChecked; try easy. 
     destruct R. destruct R'.  apply (Y4 h1 h2 h h0) ; try easy.
     apply well_typed_env_consist with (env0 := x0).
     unfold env_consistent. split. intros.
     split. intros. destruct H7. destruct (Nat.eq_dec x1 x); subst. exists (TPtr Checked ta).
     apply Env.add_1. easy. exists x2. repeat apply Env.add_2; try lia. easy.
     intros. destruct (Nat.eq_dec x1 x); subst. destruct H7. exists (TPtr Checked ta). easy. 
     destruct H7. exists x2. apply Env.add_3 in H7; try lia. apply Env.add_3 in H7; try lia.
     easy.
     split; intros.
     destruct (Nat.eq_dec x1 x); subst. apply Env.mapsto_always_same with (v1 := t0) in H3; try easy;subst.
     apply Env.add_1; try easy. repeat apply Env.add_2;try lia. easy.
     destruct (Nat.eq_dec x1 x); subst. apply Env.mapsto_add1 in H9; subst.
     apply Env.mapsto_always_same with (v1 := t0) in H3; try easy; subst.
     split. constructor. easy.
     apply Env.add_3 in H9; try lia.
     apply Env.add_3 in H9; try lia.
     apply Env.mapsto_always_same with (v1:=t') in H8; try easy; subst.
     split. constructor. easy. easy. easy. easy.
     apply HDom in G1. easy.
     inv HTy1.
     exists env,t.
     split; try easy.
     split; try easy.
     split; try easy.
     split. apply rheap_consistent_refl.
     split; try easy.
     split. apply env_consist_refl.
     split. constructor; try easy. exists t. split. apply type_eq_refl.  constructor. constructor.
     exists env,t.
     split; try easy.
     split; try easy.
     split; try easy.
     split. apply rheap_consistent_refl.
     split; try easy.
     split. apply env_consist_refl.
     split. apply TyLitTainted; try easy.
     exists t. split. apply type_eq_refl.  constructor. constructor.
   * 
     inv H2.
     assert (Stack.In x s). exists (a',ta'). easy. apply HDom in H; try easy.
     unfold inject_ret in *; destruct re; try easy; inv H10.
     inv HEwf.
     assert (env_wt D Checked (Env.add x (TPtr Checked ta) env)).
     unfold env_wt in *. intros. destruct (Nat.eq_dec x0 x); subst.
     apply Env.mapsto_add1 in H; subst. split. easy.
     destruct H2 as [A1 [A2 A3]].
     split. easy.
     unfold well_type_bound_in. intros.
     apply simple_means_not_freeVars in A3; try easy. rewrite A3 in H. simpl in *. easy.
     apply Env.add_3 in H as A1. apply Henvt in A1. destruct A1 as [X2 [X3 X4]].
     split. easy. split. easy. unfold well_type_bound_in. intros.
     apply Env.add_3 in H; try lia.
     destruct (Nat.eq_dec x1 x); subst.
     destruct HQt as [B1 [B2 B3]].
     unfold well_type_bound_in in *. apply X4 in H0. assert (Env.In x env). exists TNat. easy. easy.
     apply Env.add_2. lia. apply X4. easy. lia. 
     assert (Checked = Checked) by easy.
     specialize (IH1 H6 H (Stack.add x (na, TPtr Checked ta) s)).
     edestruct IH1; eauto.
     unfold stack_wt in *. intros. destruct (Nat.eq_dec x0 x); subst. apply Stack.mapsto_add1 in H1.
     inv H1. split. easy. destruct H2 as [A1 [A2 A3]]. split. easy. easy.
     apply Stack.add_3 in H1. apply Hswt in H1; try easy. lia.
     destruct HQt as [A1 [A2 A3]].
     unfold theta_wt in *. split. intros. split; intros.
     destruct (Nat.eq_dec x0 x); subst. easy. apply Env.add_2; try lia. apply A1. easy.
     destruct (Nat.eq_dec x0 x); subst. apply Env.mapsto_add1 in H1. inv H1.
     apply Env.add_3 in H1; try lia. apply A1 in H1. destruct H1. exists x1.
     easy.
     split. intros. destruct (Nat.eq_dec x0 x); subst. apply Stack.mapsto_add1 in H3; try easy.
     apply Stack.add_3 in H3. eapply A2; eauto. lia.
     intros. destruct (Nat.eq_dec x0 x); subst. apply Stack.mapsto_add1 in H1; try easy.
     apply Stack.add_3 in H1.
     apply A3 in H1. easy. lia.
     unfold same_domain; split; intros. destruct (Nat.eq_dec x0 x); subst. exists (na, TPtr Checked ta).
     apply Stack.add_1. easy.
     destruct H1. apply Env.add_3 in H1. assert (Env.In x0 env). exists x1. easy. apply HDom in H3.
     destruct H3. exists x2. apply Stack.add_2. lia. easy. lia.
     destruct (Nat.eq_dec x0 x); subst. exists (TPtr Checked ta). apply Env.add_1. easy.
     destruct H1. apply Stack.add_3 in H1. assert (Stack.In x0 s). exists x1. easy. apply HDom in H3.
     destruct H3. exists x2. apply Env.add_2. lia. easy. lia.
     unfold stack_wf in *. intros.
     destruct (Nat.eq_dec x0 x); subst. apply Env.mapsto_add1 in H1. subst.
     exists na, (TPtr Checked ta). split. exists (TPtr Checked ta). split.
     apply type_eq_refl. constructor. constructor.
     apply Stack.add_1. easy. apply Env.add_3 in H1. apply Hswf in H1.
     destruct H1 as [va [tx [B1 B2]]]. exists va,tx. split. destruct B1. destruct H1.
     exists x1; try easy.
     apply Stack.add_2. lia. easy. lia.
     unfold stack_rheap_consistent in *. intros.
     destruct (Nat.eq_dec x0 x); subst. apply Stack.mapsto_add1 in H3. inv H3. eauto.
     eapply HsHwf; eauto. apply Stack.add_3 in H3; try easy. apply H3. lia.
     apply step_implies_reduces_1 with (cm:=Checked) (E := CHole) (m := Checked) in H12.
     simpl in *. apply H12. easy.
     destruct H1 as [tx [Y1 [Y2 [Y3 [Y4 [Y5 [Y6 [Y7 Y8]]]]]]]].
     apply step_stack_consist in H12 as Y9. simpl in *.
     apply stack_consist_wt with (D := D) (m := Checked) in Y9 as Y10; try easy.
     2: { unfold stack_wt in *. intros. destruct (Nat.eq_dec x1 x);subst.
          apply Stack.mapsto_add1 in H1;subst. inv H1. split. easy. split. easy. easy.
          apply Stack.add_3 in H1. apply Hswt in H1. easy. lia.
        }
     exists (Env.remove x x0),tx.
     split. unfold same_domain; split;intros.
     destruct (Nat.eq_dec x1 x); subst. 
     apply Env.remove_1 in H1; try easy.
     destruct H1. apply Env.remove_3 in H1.
     assert (Env.In x1 x0). 
     exists x2. easy. apply Y1 in H3.
     destruct H3. exists x3. apply Stack.remove_2. lia. easy.
     destruct (Nat.eq_dec x1 x); subst.
     apply Stack.remove_1 in H1; try easy.
     destruct H1. apply Stack.remove_3 in H1. assert (Stack.In x1 s'0). exists x2. easy. apply Y1 in H3.
     destruct H3. exists x3. apply Env.remove_2; try lia. easy.
     split. unfold stack_wf in *. intros.
     destruct (Nat.eq_dec x1 x); subst.
     assert (Env.In x (Env.remove (elt:=type) x x0)). exists t0. easy. apply Env.remove_1 in H3; easy.
     apply Env.remove_3 in H1; try lia.
     apply Y2 in H1 as G5. destruct G5 as [vq [tq [G5 G6]]].
     exists vq,tq. split. easy. apply Stack.remove_2; try lia. easy.
     split. unfold theta_wt in *.
     destruct Y3 as [A1 [A2 A3]]. split. intros. split. intros.
     destruct (Nat.eq_dec x1 x); subst. easy. apply Env.remove_2; try lia.
     apply A1. easy.
     intros. destruct (Nat.eq_dec x1 x); subst.
     assert (Env.In x (Env.remove (elt:=type) x x0)). exists TNat. easy.
     apply Env.remove_1 in H3; try easy.
     apply Env.remove_3 in H1; try lia.
     apply A1 in H1. easy.
     split. intros.
     assert (x1 <> x). intros R1; subst.
     assert (Theta.In x Q). exists GeZero. easy. easy.
     apply Stack.remove_3 in H3; try lia.
     eapply A2; eauto.
     intros. 
     destruct (Nat.eq_dec x1 x); subst.
     assert (Stack.In x (Stack.remove (elt:=Z * type) x s'0)). exists (n,TNat). easy.
     apply Stack.remove_1 in H3; try easy.
     apply Stack.remove_3 in H1; try lia. apply A3 in H1; try easy.
     split. easy.
     split. unfold stack_rheap_consistent in *. intros.
     destruct R. subst.
     destruct (Nat.eq_dec x1 x); subst.
     assert (Stack.In x (Stack.remove (elt:=Z * type) x s'0)). exists (n, t0). easy.
     apply Stack.remove_1 in H1; try easy.
     apply Stack.remove_3 in H3. apply (Y5 Hchk Htnt) in H3; try easy.
     split. 
     unfold env_consistent in *. destruct Y6 as [A1 [A2 A3]].
     split. intros. split. intros.
     destruct (Nat.eq_dec x1 x); subst. easy. 
     destruct H1.
     assert (Env.In x1 (Env.add x (TPtr Checked ta) env)).
     exists x2. apply Env.add_2; try lia. easy.
     apply A1 in H3. destruct H3. exists x3.
     apply Env.remove_2; try lia. easy.
     intros. destruct H1.
     destruct (Nat.eq_dec x1 x); subst.
     assert (Env.Raw.PX.In x (Env.this (Env.remove (elt:=type) x x0))). exists x2. easy.
     apply Env.remove_1 in H3; try easy.
     apply Env.remove_3 in H1.
     apply Env.mapsto_in in H1.
     apply A1 in H1. destruct H1. apply Env.add_3 in H1; try lia. exists x3;easy.
     split; intros. destruct (Nat.eq_dec x1 x); subst.
     apply Env.mapsto_in in H3. easy.
     apply Env.remove_2;try lia. eapply A2; eauto. apply Env.add_2;try easy. lia.
     destruct (Nat.eq_dec x1 x); subst. apply Env.mapsto_in in H7. apply Env.remove_1 in H7; try easy.
     apply Env.remove_3 in H7. apply A3 with (t := t0) in H7; try easy. apply Env.add_2;try easy. lia.
     split; try easy.
     specialize (or_nt_ptr (TPtr Checked ta)) as A1.
     destruct A1.
     assert (Stack.MapsTo x (na, TPtr Checked ta) (Stack.add x (na, TPtr Checked ta) s)).
     apply Stack.add_1. easy.
     destruct Y9 as [B1 [B2 B3]].
     apply B3 with (v' := nb') (t' := tb') in H3; try easy. destruct H3 as [H3 X4]; subst.
     apply eq_subtype_ptr in X4 as X5. destruct X5 as [tq X5]; subst.
     apply eq_subtype_nt_ptr in X4 as X5; try easy.
     apply TyRetChecked; try easy. apply Y10 in H11. destruct H11 as [X6 [X7 X8]]; try easy.
     destruct R'. destruct R.
     eapply Y5 in H11; try easy. auto. 
     apply well_typed_env_consist with (env0 := x0).
     unfold env_consistent. split. intros.
     split. intros. destruct H3. destruct (Nat.eq_dec x1 x); subst. exists (TPtr Checked tq).
     apply Env.add_1. easy. exists x2. apply Env.add_2; try lia.
     apply Env.remove_2; try lia. easy.
     intros. destruct (Nat.eq_dec x1 x); subst. destruct H3. 
     destruct Y6. specialize (H7 x). assert (Env.In x (Env.add x (TPtr Checked ta) env)).
     exists (TPtr Checked ta).
     apply Env.add_1. easy. apply H7 in H9. easy.
     destruct H3. apply Env.add_3 in H3; try lia. apply Env.remove_3 in H3; try lia.
     exists x2. easy.
     split; intros.
     destruct (Nat.eq_dec x1 x); subst.
     destruct Y6. destruct H9.
     assert (Env.MapsTo x (TPtr Checked ta) (Env.add x (TPtr Checked ta) env)).
     apply Env.add_1; try easy. apply H10 with (t' := t0) in H13; try easy.
     unfold is_nt_ptr in H1. destruct ta; try easy. destruct H13. inv H13; try easy.
     apply Env.add_2; try lia. apply Env.remove_2; try lia. easy.
     destruct Y6. destruct H10.
     destruct (Nat.eq_dec x1 x); subst.
     apply Y2 in H7 as A1. destruct A1 as [vaa [taa [A1 A2]]].
     apply Stack.mapsto_always_same with (v1 := (vaa,taa)) in H11 ; try easy. inv H11.
     apply Env.mapsto_add1 in H8;subst. 
     assert (simple_type t0).
     assert (Env.MapsTo x (TPtr Checked ta) (Env.add x (TPtr Checked ta) env)). apply Env.add_1; try easy.
     apply H13 with (t' := t0) in H8 ; try easy. destruct H8. apply H11; easy.
     apply eq_subtype_simple_same in A1; try easy.
     apply subtype_nt_ptr_1 in A1; try easy. split. easy.
     apply Y10 in A2; try easy.
     apply Y10 in A2; try easy.
     apply Env.add_3 in H8; try lia.
     apply Env.remove_3 in H8; try lia.
     apply Env.mapsto_always_same with (v1 := t0) in H8; subst. split. constructor.
     easy. easy. easy.
     destruct Y9 as [B1 [B2 B3]].
     assert (Stack.MapsTo x (na, TPtr Checked ta) (Stack.add x (na, TPtr Checked ta) s)).
     apply Stack.add_1. easy. apply B2 in H3.
     apply Stack.mapsto_always_same with (v1:= (nb', tb')) in H3; try easy. inv H3. 
     destruct Y6 as [A1 [A2 A3]].
     assert (Env.MapsTo x (TPtr Checked ta) (Env.add x (TPtr Checked ta) env)).
     apply Env.add_1; try easy.
     apply A2 in H3;try easy.
     apply TyRetChecked; try easy. 
     destruct R. destruct R'.  apply (Y4 h1 h2 h h0) ; try easy.
     apply well_typed_env_consist with (env0 := x0).
     unfold env_consistent. split. intros.
     split. intros. destruct H7. destruct (Nat.eq_dec x1 x); subst. exists (TPtr Checked ta).
     apply Env.add_1. easy. exists x2. apply Env.add_2; try lia.
     apply Env.remove_2;try lia. easy.
     intros. destruct (Nat.eq_dec x1 x); subst. destruct H7. exists (TPtr Checked ta). easy. 
     destruct H7. exists x2. apply Env.add_3 in H7; try lia. apply Env.remove_3 in H7; try lia.
     easy.
     split; intros.
     destruct (Nat.eq_dec x1 x); subst.
     apply Env.mapsto_always_same with (v1 := t0) in H3; try easy;subst.
     apply Env.add_1; try easy. apply Env.add_2;try lia. apply Env.remove_2; try lia. easy.
     destruct (Nat.eq_dec x1 x); subst. apply Env.mapsto_add1 in H9; subst.
     apply Env.mapsto_always_same with (v1 := t0) in H3; try easy; subst.
     split. constructor. easy.
     apply Env.add_3 in H9; try lia.
     apply Env.remove_3 in H9; try lia.
     apply Env.mapsto_always_same with (v1:=t') in H8; try easy; subst.
     split. constructor. easy. easy. easy.
     inv HTy1.
     exists env,t.
     split; try easy.
     split; try easy.
     split; try easy.
     split. apply rheap_consistent_refl.
     split; try easy.
     split. apply env_consist_refl.
     split. constructor; try easy. exists t. split. apply type_eq_refl.  constructor. constructor.
     exists env,t.
     split; try easy.
     split; try easy.
     split; try easy.
     split. apply rheap_consistent_refl.
     split; try easy.
     split. apply env_consist_refl.
     split. apply TyLitTainted; try easy.
     exists t. split. apply type_eq_refl.  constructor. constructor.
    (* T-Ret *)
   - assert (X1 := Hreduces). inv Hreduces. destruct E;inv H; simpl in *; subst;  try easy.
     assert (m' = Tainted). inv HMode. assert (Checked = Checked) by easy. apply H in H1; try easy.
     destruct m'; try easy. subst.
     assert (Env.In x env \/ ~ Env.In x env) as G1.
     destruct (Env.find x env) eqn:eq1. apply Env.find_2 in eq1. left. exists t0. easy.
     apply EnvFacts.not_find_in_iff in eq1. right. easy.
     destruct G1 as [G1 | G1].
   *
     inv H2. unfold inject_ret in *; destruct re; try easy; inv H9.
     inv HEwf.
     assert (env_wt D Checked (Env.add x (TPtr Tainted ta) env)).
     unfold env_wt in *. intros. destruct (Nat.eq_dec x0 x); subst.
     apply Env.mapsto_add1 in H; subst. split. easy.
     destruct H2 as [A1 [A2 A3]].
     split. easy.
     unfold well_type_bound_in. intros.
     apply simple_means_not_freeVars in A3; try easy. rewrite A3 in H. simpl in *. easy.
     apply Env.add_3 in H. apply Henvt in H. destruct H as [X2 [X3 X4]].
     split. easy. split. easy. unfold well_type_bound_in. intros.
     destruct (Nat.eq_dec x1 x); subst.
     destruct HQt as [B1 [B2 B3]].
     assert (~ Env.MapsTo x TNat env). intros R1. apply B1 in R1. easy.
     destruct G1. assert (x1 <> TNat). intros R2; subst. easy.
     apply X4 in H as G2. easy.
     apply Env.add_2. lia. apply X4. easy. lia. 
     assert (Checked = Checked) by easy.
     specialize (IH1 H5 H (Stack.add x (na, TPtr Tainted ta) s)).
     edestruct IH1; eauto.
     unfold stack_wt in *. intros. destruct (Nat.eq_dec x0 x); subst. apply Stack.mapsto_add1 in H1.
     inv H1. split. easy. destruct H2 as [A1 [A2 A3]]. split. easy. easy.
     apply Stack.add_3 in H1. apply Hswt in H1; try easy. lia.
     destruct HQt as [A1 [A2 A3]].
     unfold theta_wt in *. split. intros. split; intros.
     destruct (Nat.eq_dec x0 x); subst. easy. apply Env.add_2; try lia. apply A1. easy.
     destruct (Nat.eq_dec x0 x); subst. apply Env.mapsto_add1 in H1. inv H1.
     apply Env.add_3 in H1; try lia. apply A1 in H1. destruct H1. exists x1.
     easy.
     split. intros. destruct (Nat.eq_dec x0 x); subst. apply Stack.mapsto_add1 in H3; try easy.
     apply Stack.add_3 in H3. eapply A2; eauto. lia.
     intros. destruct (Nat.eq_dec x0 x); subst. apply Stack.mapsto_add1 in H1; try easy.
     apply Stack.add_3 in H1.
     apply A3 in H1. easy. lia.
     unfold same_domain; split; intros. destruct (Nat.eq_dec x0 x); subst. exists (na, TPtr Tainted ta).
     apply Stack.add_1. easy.
     destruct H1. apply Env.add_3 in H1. assert (Env.In x0 env). exists x1. easy. apply HDom in H3.
     destruct H3. exists x2. apply Stack.add_2. lia. easy. lia.
     destruct (Nat.eq_dec x0 x); subst. exists (TPtr Tainted ta). apply Env.add_1. easy.
     destruct H1. apply Stack.add_3 in H1. assert (Stack.In x0 s). exists x1. easy. apply HDom in H3.
     destruct H3. exists x2. apply Env.add_2. lia. easy. lia.
     unfold stack_wf in *. intros.
     destruct (Nat.eq_dec x0 x); subst. apply Env.mapsto_add1 in H1. subst.
     exists na, (TPtr Tainted ta). split. exists (TPtr Tainted ta). split.
     apply type_eq_refl. constructor. constructor.
     apply Stack.add_1. easy. apply Env.add_3 in H1. apply Hswf in H1.
     destruct H1 as [va [tx [B1 B2]]]. exists va,tx. split. destruct B1. destruct H1.
     exists x1; try easy.
     apply Stack.add_2. lia. easy. lia.
     unfold stack_rheap_consistent in *. intros.
     destruct (Nat.eq_dec x0 x); subst. apply Stack.mapsto_add1 in H3. inv H3. apply TyLitU_C; try easy.
     eapply HsHwf; eauto. apply Stack.add_3 in H3; try easy. apply H3. lia.
     apply step_implies_reduces_1 with (cm:=Checked) (E := CHole) (m := Checked) in H11. simpl in *. apply H11. easy.
     destruct H1 as [tx [Y1 [Y2 [Y3 [Y4 [Y5 [Y6 [Y7 Y8]]]]]]]].
     apply step_stack_consist in H11 as Y9. simpl in *.
     apply stack_consist_wt with (D := D) (m := Checked) in Y9 as Y10; try easy.
     2: { unfold stack_wt in *. intros. destruct (Nat.eq_dec x1 x);subst.
          apply Stack.mapsto_add1 in H1;subst. inv H1. split. easy. split. easy. easy.
          apply Stack.add_3 in H1. apply Hswt in H1. easy. lia.
        }
     destruct G1 as [tv G1]. apply Hswf in G1 as K1.
     destruct K1 as [a'0 [ta'0 [K1 K2]]].
     apply Stack.mapsto_always_same with (v1 := (a'0, ta'0)) in H4; try easy. inv H4; subst.
     rename K2 into H4.
     destruct Y9 as [B1 [B2 B3]].
     exists (Env.add x tv x0),tx.
     split. unfold same_domain; split;intros.
     destruct (Nat.eq_dec x1 x); subst. exists (a', ta'). apply Stack.add_1. easy.
     destruct H1. apply Env.add_3 in H1; try lia.
     assert (Env.In x1 x0). 
     exists x2. easy. apply Y1 in H3.
     destruct H3. exists x3. apply Stack.add_2. lia. easy.
     destruct (Nat.eq_dec x1 x); subst. exists tv. apply Env.add_1. easy.
     destruct H1. apply Stack.add_3 in H1. assert (Stack.In x1 s'0). exists x2. easy. apply Y1 in H3.
     destruct H3. exists x3. apply Env.add_2. lia. easy. lia.
     split. unfold stack_wf in *. intros.
     destruct (Nat.eq_dec x1 x); subst. apply Env.mapsto_add1 in H1; subst.
     exists a',ta'. split. easy. apply Stack.add_1. easy.
     apply Env.add_3 in H1; try lia.
     apply Y2 in H1 as G5. destruct G5 as [vq [tq [G5 G6]]].
     exists vq,tq. split. easy. apply Stack.add_2; try lia. easy.
     split. unfold theta_wt in *.
     destruct Y3 as [A1 [A2 A3]]. split. intros. split. intros.
     destruct (Nat.eq_dec x1 x); subst. easy. apply Env.add_2; try lia.
     apply A1. easy.
     intros. destruct (Nat.eq_dec x1 x); subst. apply Env.mapsto_add1 in H1; subst.
     destruct HQt. apply H1 in G1. easy.
     apply Env.add_3 in H1; try lia.
     apply A1 in H1. easy.
     split. intros.
     assert (x1 <> x). intros R1; subst.
     assert (Theta.In x Q). exists GeZero. easy. easy.
     apply Stack.add_3 in H3; try lia.
     eapply A2; eauto.
     intros. 
     destruct (Nat.eq_dec x1 x); subst.
     apply Stack.mapsto_add1 in H1. inv H1.
     destruct HQt as [B4 [B5 B6]].
     apply B6 in H4; try easy.
     apply Stack.add_3 in H1; try lia. apply A3 in H1; try easy.
     split. easy.
     split. unfold stack_rheap_consistent in *. intros.
     destruct R. subst.
     destruct (Nat.eq_dec x1 x); subst. apply Stack.mapsto_add1 in H3. inv H3.
     apply (HsHwf h h0) in H4; try easy.
     apply (Y4 Hchk Htnt h h0) in H4; try easy.
     apply Stack.add_3 in H3. apply (Y5 Hchk Htnt) in H3; try easy. lia.
     split. 
     unfold env_consistent in *. destruct Y6 as [A1 [A2 A3]].
     split. intros. split. intros.
     destruct (Nat.eq_dec x1 x); subst. exists tv.
     apply Env.add_1. easy.
     assert (Env.In (elt:=type) x1 (Env.add x (TPtr Tainted ta) env)).
     destruct H1. exists x2. apply Env.add_2; try lia. easy.
     apply A1 in H3. destruct H3. exists x2.
     apply Env.add_2; try lia. easy.
     intros. destruct H1.
     destruct (Nat.eq_dec x1 x); subst. exists tv; easy.
     apply Env.add_3 in H1; try lia. 
     assert (Env.In x1 x0). exists x2. easy. apply A1 in H3. destruct H3.
     apply Env.add_3 in H3; try lia. exists x3. easy.
     split; intros. destruct (Nat.eq_dec x1 x); subst.
     apply Env.mapsto_always_same with (v1 := tv) in H3; subst. apply Env.add_1. easy.
     easy. apply Env.add_2; try lia.
     apply A2; try easy. apply Env.add_2; try lia. easy.
     destruct (Nat.eq_dec x1 x); subst. 
     apply Env.mapsto_always_same with (v1 := tv) in H3; try easy; subst.
     apply Env.mapsto_add1 in H6; subst. split.
     constructor. unfold both_simple in *; intros;easy.
     apply Env.add_3 in H6; try lia.
     apply A3 with (t := t0) in H6 ; try easy. apply Env.add_2; try lia. easy.
     split.
     specialize (or_nt_ptr (TPtr Tainted ta)) as A1.
     destruct A1.
     assert (Stack.MapsTo x (na, TPtr Tainted ta) (Stack.add x (na, TPtr Tainted ta) s)).
     apply Stack.add_1. easy.
     apply B3 with (v' := nb') (t' := tb') in H3; try easy. destruct H3 as [H3 X4]; subst.
     apply eq_subtype_ptr in X4 as X5. destruct X5 as [tq X5]; subst.
     apply eq_subtype_nt_ptr in X4 as X5; try easy.
     apply TyRet; try easy. apply Y10 in H10. destruct H10 as [X6 [X7 X8]]; try easy.
     destruct R'. destruct R.
     eapply Y5 in H10 as X6; try easy. 
     apply well_typed_env_consist with (env0 := x0).
     unfold env_consistent. split. intros.
     split. intros. destruct H3. destruct (Nat.eq_dec x1 x); subst. exists (TPtr Tainted tq).
     apply Env.add_1. easy. exists x2. repeat apply Env.add_2; try lia. easy.
     intros. destruct (Nat.eq_dec x1 x); subst. destruct H3. 
     destruct Y6. specialize (H6 x). assert (Env.In x (Env.add x (TPtr Tainted ta) env)).
     exists (TPtr Tainted ta).
     apply Env.add_1. easy. apply H6 in H8. easy.
     destruct H3. apply Env.add_3 in H3; try lia. apply Env.add_3 in H3; try lia.
     exists x2. easy.
     split; intros.
     destruct (Nat.eq_dec x1 x); subst.
     destruct Y6. destruct H8.
     assert (Env.MapsTo x (TPtr Tainted ta) (Env.add x (TPtr Tainted ta) env)).
     apply Env.add_1; try easy. apply H9 with (t' := t0) in H12; try easy.
     unfold is_nt_ptr in H1. destruct ta; try easy. destruct H12. inv H12; try easy.
     repeat apply Env.add_2; try lia. easy.
     destruct Y6. destruct H9.
     destruct (Nat.eq_dec x1 x); subst.
     apply Y2 in H6 as A1. destruct A1 as [vaa [taa [A1 A2]]].
     apply Stack.mapsto_always_same with (v1 := (vaa,taa)) in H10 ; try easy. inv H10.
     apply Env.mapsto_add1 in H7;subst. 
     assert (simple_type t0).
     assert (Env.MapsTo x (TPtr Tainted ta) (Env.add x (TPtr Tainted ta) env)). apply Env.add_1; try easy.
     apply H12 with (t' := t0) in H7 ; try easy. destruct H7. apply H10; easy.
     apply eq_subtype_simple_same in A1; try easy.
     apply subtype_nt_ptr_1 in A1; try easy. split. easy.
     apply Y10 in A2; try easy.
     apply Y10 in A2; try easy.
     apply Env.add_3 in H7; try lia.
     apply Env.add_3 in H7; try lia.
     apply Env.mapsto_always_same with (v1 := t0) in H7; subst. split. constructor.
     easy. easy. easy.
     assert (Stack.MapsTo x (na, TPtr Tainted ta) (Stack.add x (na, TPtr Tainted ta) s)).
     apply Stack.add_1. easy. apply B2 in H3.
     apply Stack.mapsto_always_same with (v1:= (nb', tb')) in H3; try easy. inv H3. 
     destruct Y6 as [A1 [A2 A3]].
     assert (Env.MapsTo x (TPtr Tainted ta) (Env.add x (TPtr Tainted ta) env)).
     apply Env.add_1; try easy.
     apply A2 in H3;try easy.
     apply TyRet; try easy. 
     apply well_typed_env_consist with (env0 := x0).
     unfold env_consistent. split. intros.
     split. intros. destruct H6. destruct (Nat.eq_dec x1 x); subst. exists (TPtr Tainted ta).
     apply Env.add_1. easy. exists x2. repeat apply Env.add_2; try lia. easy.
     intros. destruct (Nat.eq_dec x1 x); subst. destruct H6. exists (TPtr Tainted ta). easy. 
     destruct H6. exists x2. apply Env.add_3 in H6; try lia. apply Env.add_3 in H6; try lia.
     easy.
     split; intros.
     destruct (Nat.eq_dec x1 x); subst. apply Env.mapsto_always_same with (v1 := t0) in H3; try easy;subst.
     apply Env.add_1; try easy. repeat apply Env.add_2;try lia. easy.
     destruct (Nat.eq_dec x1 x); subst. apply Env.mapsto_add1 in H8; subst.
     apply Env.mapsto_always_same with (v1 := t0) in H3; try easy; subst.
     split. constructor. easy.
     apply Env.add_3 in H8; try lia.
     apply Env.add_3 in H8; try lia.
     apply Env.mapsto_always_same with (v1:=t') in H7; try easy; subst.
     split. constructor. easy. easy. easy. easy.
     apply HDom in G1. easy.
     inv HTy1.
     exists env,t.
     split; try easy.
     split; try easy.
     split; try easy.
     split. apply rheap_consistent_refl.
     split; try easy.
     split. apply env_consist_refl.
     split. constructor; try easy. exists t. split. apply type_eq_refl.  constructor. constructor.
     exists env,t.
     split; try easy.
     split; try easy.
     split; try easy.
     split. apply rheap_consistent_refl.
     split; try easy.
     split. apply env_consist_refl.
     split. apply TyLitTainted; try easy.
     exists t. split. apply type_eq_refl.  constructor. constructor.
   * 
     inv H2.
     assert (Stack.In x s). exists (a',ta'). easy. apply HDom in H; try easy.
     unfold inject_ret in *; destruct re; try easy; inv H9.
     inv HEwf.
     assert (env_wt D Checked (Env.add x (TPtr Tainted ta) env)).
     unfold env_wt in *. intros. destruct (Nat.eq_dec x0 x); subst.
     apply Env.mapsto_add1 in H; subst. split. easy.
     destruct H2 as [A1 [A2 A3]].
     split. inv A2. constructor. easy. easy.
     unfold well_type_bound_in. intros.
     apply simple_means_not_freeVars in A3; try easy. rewrite A3 in H. simpl in *. easy.
     apply Env.add_3 in H as A1. apply Henvt in A1. destruct A1 as [X2 [X3 X4]].
     split. easy. split. easy. unfold well_type_bound_in. intros.
     apply Env.add_3 in H; try lia.
     destruct (Nat.eq_dec x1 x); subst.
     destruct HQt as [B1 [B2 B3]].
     unfold well_type_bound_in in *. apply X4 in H0. assert (Env.In x env). exists TNat. easy. easy.
     apply Env.add_2. lia. apply X4. easy. lia. 
     assert (Checked = Checked) by easy.
     specialize (IH1 H5 H (Stack.add x (na, TPtr Tainted ta) s)).
     edestruct IH1; eauto.
     unfold stack_wt in *. intros. destruct (Nat.eq_dec x0 x); subst. apply Stack.mapsto_add1 in H1.
     inv H1. split. easy. destruct H2 as [A1 [A2 A3]]. split. easy. easy.
     apply Stack.add_3 in H1. apply Hswt in H1; try easy. lia.
     destruct HQt as [A1 [A2 A3]].
     unfold theta_wt in *. split. intros. split; intros.
     destruct (Nat.eq_dec x0 x); subst. easy. apply Env.add_2; try lia. apply A1. easy.
     destruct (Nat.eq_dec x0 x); subst. apply Env.mapsto_add1 in H1. inv H1.
     apply Env.add_3 in H1; try lia. apply A1 in H1. destruct H1. exists x1.
     easy.
     split. intros. destruct (Nat.eq_dec x0 x); subst. apply Stack.mapsto_add1 in H3; try easy.
     apply Stack.add_3 in H3. eapply A2; eauto. lia.
     intros. destruct (Nat.eq_dec x0 x); subst. apply Stack.mapsto_add1 in H1; try easy.
     apply Stack.add_3 in H1.
     apply A3 in H1. easy. lia.
     unfold same_domain; split; intros. destruct (Nat.eq_dec x0 x); subst. exists (na, TPtr Tainted ta).
     apply Stack.add_1. easy.
     destruct H1. apply Env.add_3 in H1. assert (Env.In x0 env). exists x1. easy. apply HDom in H3.
     destruct H3. exists x2. apply Stack.add_2. lia. easy. lia.
     destruct (Nat.eq_dec x0 x); subst. exists (TPtr Tainted ta). apply Env.add_1. easy.
     destruct H1. apply Stack.add_3 in H1. assert (Stack.In x0 s). exists x1. easy. apply HDom in H3.
     destruct H3. exists x2. apply Env.add_2. lia. easy. lia.
     unfold stack_wf in *. intros.
     destruct (Nat.eq_dec x0 x); subst. apply Env.mapsto_add1 in H1. subst.
     exists na, (TPtr Tainted ta). split. exists (TPtr Tainted ta). split.
     apply type_eq_refl. constructor. constructor.
     apply Stack.add_1. easy. apply Env.add_3 in H1. apply Hswf in H1.
     destruct H1 as [va [tx [B1 B2]]]. exists va,tx. split. destruct B1. destruct H1.
     exists x1; try easy.
     apply Stack.add_2. lia. easy. lia.
     unfold stack_rheap_consistent in *. intros.
     destruct (Nat.eq_dec x0 x); subst. apply Stack.mapsto_add1 in H3. inv H3. apply TyLitU_C; try easy.
     eapply HsHwf; eauto. apply Stack.add_3 in H3; try easy. apply H3. lia.
     apply step_implies_reduces_1 with (cm := Checked) (E := CHole) (m := Checked) in H11. simpl in *. apply H11. easy.
     destruct H1 as [tx [Y1 [Y2 [Y3 [Y4 [Y5 [Y6 [Y7 Y8]]]]]]]].
     apply step_stack_consist in H11 as Y9. simpl in *.
     apply stack_consist_wt with (D := D) (m := Checked) in Y9 as Y10; try easy.
     2: { unfold stack_wt in *. intros. destruct (Nat.eq_dec x1 x);subst.
          apply Stack.mapsto_add1 in H1;subst. inv H1. split. easy. split. easy. easy.
          apply Stack.add_3 in H1. apply Hswt in H1. easy. lia.
        }
     exists (Env.remove x x0),tx.
     split. unfold same_domain; split;intros.
     destruct (Nat.eq_dec x1 x); subst. 
     apply Env.remove_1 in H1; try easy.
     destruct H1. apply Env.remove_3 in H1.
     assert (Env.In x1 x0). 
     exists x2. easy. apply Y1 in H3.
     destruct H3. exists x3. apply Stack.remove_2. lia. easy.
     destruct (Nat.eq_dec x1 x); subst.
     apply Stack.remove_1 in H1; try easy.
     destruct H1. apply Stack.remove_3 in H1. assert (Stack.In x1 s'0). exists x2. easy. apply Y1 in H3.
     destruct H3. exists x3. apply Env.remove_2; try lia. easy.
     split. unfold stack_wf in *. intros.
     destruct (Nat.eq_dec x1 x); subst.
     assert (Env.In x (Env.remove (elt:=type) x x0)). exists t0. easy. apply Env.remove_1 in H3; easy.
     apply Env.remove_3 in H1; try lia.
     apply Y2 in H1 as G5. destruct G5 as [vq [tq [G5 G6]]].
     exists vq,tq. split. easy. apply Stack.remove_2; try lia. easy.
     split. unfold theta_wt in *.
     destruct Y3 as [A1 [A2 A3]]. split. intros. split. intros.
     destruct (Nat.eq_dec x1 x); subst. easy. apply Env.remove_2; try lia.
     apply A1. easy.
     intros. destruct (Nat.eq_dec x1 x); subst.
     assert (Env.In x (Env.remove (elt:=type) x x0)). exists TNat. easy.
     apply Env.remove_1 in H3; try easy.
     apply Env.remove_3 in H1; try lia.
     apply A1 in H1. easy.
     split. intros.
     assert (x1 <> x). intros R1; subst.
     assert (Theta.In x Q). exists GeZero. easy. easy.
     apply Stack.remove_3 in H3; try lia.
     eapply A2; eauto.
     intros. 
     destruct (Nat.eq_dec x1 x); subst.
     assert (Stack.In x (Stack.remove (elt:=Z * type) x s'0)). exists (n,TNat). easy.
     apply Stack.remove_1 in H3; try easy.
     apply Stack.remove_3 in H1; try lia. apply A3 in H1; try easy.
     split. easy.
     split. unfold stack_rheap_consistent in *. intros.
     destruct R. subst.
     destruct (Nat.eq_dec x1 x); subst.
     assert (Stack.In x (Stack.remove (elt:=Z * type) x s'0)). exists (n, t0). easy.
     apply Stack.remove_1 in H1; try easy.
     apply Stack.remove_3 in H3. apply (Y5 Hchk Htnt) in H3; try easy.
     split. 
     unfold env_consistent in *. destruct Y6 as [A1 [A2 A3]].
     split. intros. split. intros.
     destruct (Nat.eq_dec x1 x); subst. easy. 
     destruct H1.
     assert (Env.In x1 (Env.add x (TPtr Tainted ta) env)).
     exists x2. apply Env.add_2; try lia. easy.
     apply A1 in H3. destruct H3. exists x3.
     apply Env.remove_2; try lia. easy.
     intros. destruct H1.
     destruct (Nat.eq_dec x1 x); subst.
     assert (Env.Raw.PX.In x (Env.this (Env.remove (elt:=type) x x0))). exists x2. easy.
     apply Env.remove_1 in H3; try easy.
     apply Env.remove_3 in H1.
     apply Env.mapsto_in in H1.
     apply A1 in H1. destruct H1. apply Env.add_3 in H1; try lia. exists x3;easy.
     split; intros. destruct (Nat.eq_dec x1 x); subst.
     apply Env.mapsto_in in H3. easy.
     apply Env.remove_2;try lia. eapply A2; eauto. apply Env.add_2;try easy. lia.
     destruct (Nat.eq_dec x1 x); subst. apply Env.mapsto_in in H6. apply Env.remove_1 in H6; try easy.
     apply Env.remove_3 in H6. apply A3 with (t := t0) in H6; try easy. apply Env.add_2;try easy. lia.
     split; try easy.
     specialize (or_nt_ptr (TPtr Tainted ta)) as A1.
     destruct A1.
     assert (Stack.MapsTo x (na, TPtr Tainted ta) (Stack.add x (na, TPtr Tainted ta) s)).
     apply Stack.add_1. easy.
     destruct Y9 as [B1 [B2 B3]].
     apply B3 with (v' := nb') (t' := tb') in H3; try easy. destruct H3 as [H3 X4]; subst.
     apply eq_subtype_ptr in X4 as X5. destruct X5 as [tq X5]; subst.
     apply eq_subtype_nt_ptr in X4 as X5; try easy.
     apply TyRet; try easy. apply Y10 in H10. destruct H10 as [X6 [X7 X8]]; try easy.
     destruct R'. destruct R.
     apply well_typed_env_consist with (env0 := x0).
     unfold env_consistent. split. intros.
     split. intros. destruct H3. destruct (Nat.eq_dec x1 x); subst. exists (TPtr Tainted tq).
     apply Env.add_1. easy. exists x2. apply Env.add_2; try lia.
     apply Env.remove_2; try lia. easy.
     intros. destruct (Nat.eq_dec x1 x); subst. destruct H3. 
     destruct Y6. specialize (H6 x). assert (Env.In x (Env.add x (TPtr Tainted ta) env)).
     exists (TPtr Tainted ta).
     apply Env.add_1. easy. apply H6 in H8. easy.
     destruct H3. apply Env.add_3 in H3; try lia. apply Env.remove_3 in H3; try lia.
     exists x2. easy.
     split; intros.
     destruct (Nat.eq_dec x1 x); subst.
     destruct Y6. destruct H8.
     assert (Env.MapsTo x (TPtr Tainted ta) (Env.add x (TPtr Tainted ta) env)).
     apply Env.add_1; try easy. apply H9 with (t' := t0) in H12; try easy.
     unfold is_nt_ptr in H1. destruct ta; try easy. destruct H12. inv H12; try easy.
     apply Env.add_2; try lia. apply Env.remove_2; try lia. easy.
     destruct Y6. destruct H9.
     destruct (Nat.eq_dec x1 x); subst.
     apply Y2 in H6 as A1. destruct A1 as [vaa [taa [A1 A2]]].
     apply Stack.mapsto_always_same with (v1 := (vaa,taa)) in H10 ; try easy. inv H10.
     apply Env.mapsto_add1 in H7;subst. 
     assert (simple_type t0).
     assert (Env.MapsTo x (TPtr Tainted ta) (Env.add x (TPtr Tainted ta) env)). apply Env.add_1; try easy.
     apply H12 with (t' := t0) in H7 ; try easy. destruct H7. apply H10; easy.
     apply eq_subtype_simple_same in A1; try easy.
     apply subtype_nt_ptr_1 in A1; try easy. split. easy.
     apply Y10 in A2; try easy.
     apply Y10 in A2; try easy.
     apply Env.add_3 in H7; try lia.
     apply Env.remove_3 in H7; try lia.
     apply Env.mapsto_always_same with (v1 := t0) in H7; subst. split. constructor.
     easy. easy. easy.
     destruct Y9 as [B1 [B2 B3]].
     assert (Stack.MapsTo x (na, TPtr Tainted ta) (Stack.add x (na, TPtr Tainted ta) s)).
     apply Stack.add_1. easy. apply B2 in H3.
     apply Stack.mapsto_always_same with (v1:= (nb', tb')) in H3; try easy. inv H3. 
     destruct Y6 as [A1 [A2 A3]].
     assert (Env.MapsTo x (TPtr Tainted ta) (Env.add x (TPtr Tainted ta) env)).
     apply Env.add_1; try easy.
     apply A2 in H3;try easy.
     apply TyRet; try easy. 
     apply well_typed_env_consist with (env0 := x0).
     unfold env_consistent. split. intros.
     split. intros. destruct H6. destruct (Nat.eq_dec x1 x); subst. exists (TPtr Tainted ta).
     apply Env.add_1. easy. exists x2. apply Env.add_2; try lia.
     apply Env.remove_2;try lia. easy.
     intros. destruct (Nat.eq_dec x1 x); subst. destruct H6. exists (TPtr Tainted ta). easy. 
     destruct H6. exists x2. apply Env.add_3 in H6; try lia. apply Env.remove_3 in H6; try lia.
     easy.
     split; intros.
     destruct (Nat.eq_dec x1 x); subst.
     apply Env.mapsto_always_same with (v1 := t0) in H3; try easy;subst.
     apply Env.add_1; try easy. apply Env.add_2;try lia. apply Env.remove_2; try lia. easy.
     destruct (Nat.eq_dec x1 x); subst. apply Env.mapsto_add1 in H8; subst.
     apply Env.mapsto_always_same with (v1 := t0) in H3; try easy; subst.
     split. constructor. easy.
     apply Env.add_3 in H8; try lia.
     apply Env.remove_3 in H8; try lia.
     apply Env.mapsto_always_same with (v1:=t') in H7; try easy; subst.
     split. constructor. easy. easy. easy.
     inv HTy1.
     exists env,t.
     split; try easy.
     split; try easy.
     split; try easy.
     split. apply rheap_consistent_refl.
     split; try easy.
     split. apply env_consist_refl.
     split. constructor; try easy. exists t. split. apply type_eq_refl.  constructor. constructor.
     exists env,t.
     split; try easy.
     split; try easy.
     split; try easy.
     split. apply rheap_consistent_refl.
     split; try easy.
     split. apply env_consist_refl.
     split. apply TyLitTainted; try easy.
     exists t. split. apply type_eq_refl.  constructor. constructor.
    (* T-Plus *)
    - inv Hreduces.
      destruct E; inversion H; simpl in *; subst.
      + inv H2.
        * inv HTy1. unfold is_check_array_ptr in *. easy. easy.
        * inv HTy1.
          exists env,TNat.
          split; try easy.
          split; try easy.
          split; try easy.
          split. apply rheap_consistent_refl.
          split; try easy.
          split. apply env_consist_refl.
          split. constructor; try easy. constructor.
          exists TNat. split. apply type_eq_refl.  constructor. constructor.
          assert (is_checked TNat). constructor. easy.
      + edestruct IH1; idtac... inv HEwf; try easy.
        destruct H0 as [ta [X1 [X2 [X3 [X4 [X5 [X6 [X7 X8]]]]]]]].
        destruct X8 as [tx [X8 X9]]. inv X9. inv H0. inv X8.
        exists x,TNat...
        split; try easy.
        split; try easy.
        split; try easy.
        split; try easy.
        split; try easy.
        split; try easy.
        split. constructor; try easy.
        apply well_typed_env_consist with (env0 := env); try easy.
        apply well_typed_heap_consist with (R := R); try easy.
        exists TNat. split; constructor. constructor.
      + edestruct IH2; idtac...
        inv HEwf; eauto.
        destruct H0 as [ta [X1 [X2 [X3 [X4 [X5 [X6 [X7 X8]]]]]]]].
        destruct X8 as [tx [X8 X9]]. inv X9. inv H0. inv X8.
        exists x,TNat...
        split; try easy.
        split; try easy.
        split; try easy.
        split; try easy.
        split; try easy.
        split; try easy.
        split. constructor; try easy. inv HTy1. constructor; try easy.
        constructor.
        constructor; try easy. 
        exists TNat;constructor. constructor. constructor. constructor.
    (* T-FieldAddr *)
    - inv Hreduces.
      destruct E; inversion H; simpl in *; subst.
      exists env, (TPtr m' ti). 
      + inv H2; try easy.
        * inv HTy.
          (* Gotta prove some equalities *)
          assert (fs = fs0).
          { apply StructDef.find_1 in HWf1.
            match goal with
            | [ H : StructDef.MapsTo _ _ _ |- _ ] =>
              apply StructDef.find_1 in H; rewrite HWf1 in H; inv H
            end; auto.
          } 
          subst.
          assert (fields_wf D fs0) by eauto.
          assert (ti = ti0).
          { apply Fields.find_1 in HWf2.
            apply Fields.find_1 in H11.
            rewrite HWf2 in H11.
            inv H11.
            reflexivity. } subst.
        split; try easy.
        split; try easy.
        split; try easy.
        split. apply rheap_consistent_refl.
        split; try easy.
        split. apply env_consist_refl.
        split. constructor. constructor.
        apply H in H11. destruct H11 as [X1 [X2 X3]];try easy.
        apply preservation_fieldaddr with (T := T) (fs := fs0) (fi := fi); try easy. lia.
        exists (TPtr Checked ti0). split. apply type_eq_refl. constructor. constructor.
        assert (is_checked (TPtr Checked (TStruct T))) by constructor. easy.
      * inv HTy; try easy.
          assert (fs = fs0).
          { apply StructDef.find_1 in HWf1.
            match goal with
            | [ H : StructDef.MapsTo _ _ _ |- _ ] =>
              apply StructDef.find_1 in H; rewrite HWf1 in H; inv H
            end; auto.
          } 
          subst.
          assert (fields_wf D fs0) by eauto.
          assert (ti = ti0).
          { apply Fields.find_1 in HWf2.
            apply Fields.find_1 in H11.
            rewrite HWf2 in H11.
            inv H11.
            reflexivity. } subst.
        split; try easy.
        split; try easy.
        split; try easy.
        split. apply rheap_consistent_refl.
        split; try easy.
        split. apply env_consist_refl.
        split. apply TyLitTainted; try easy.
        apply H in H11. destruct H11 as [X1 [X2 X3]]; try easy.
        exists (TPtr Tainted ti0). split. apply type_eq_refl. repeat constructor.
      * inv HTy; try easy. inv HMode.
        assert (Checked = Checked) by easy. apply H in H2. easy.
      + edestruct IH; eauto.
        inv HEwf; eauto.
        apply step_implies_reduces_1 with (cm :=m) (E := E) (m := Checked) in H2; try easy.
        apply H2.
        destruct H0 as [ta [X1 [X2 [X3 [X4 [X5 [X6 [X7 X8]]]]]]]].
        inv X8. inv H0. inv H3. inv H0; try easy.
        inv H1. inv H4.
        exists x, (TPtr m' ti).
        split; try easy.
        split; try easy.
        split; try easy.
        split; try easy.
        split; try easy.
        split; try easy.
        split. apply TyFieldAddr with (T := T) (fs := fs) (i := i); eauto.
        exists (TPtr m' ti). split. apply type_eq_refl. repeat constructor.
    (* T-Malloc *)
    - inv Hreduces.
      destruct E; inversion H0; simpl in *; subst.
      inv H3. inv HEwf. apply (eval_type_bound_simple D Checked) in H9 as X1; try easy.
      exists env, (TPtr Checked w').
      assert ((H0, H2) = (H0, H2)) by easy.
      specialize (HRwf H0 H2 H3).
      apply eval_type_bound_tfun with (s := s') (t' := w') in Wb as X2; try easy.
      assert (simple_type (TPtr Checked w')). unfold simple_type in *. simpl. easy.
      destruct HRwf as [HRwf HRwf1].
      specialize (alloc_correct w' D F H0 n1 H1' H13 HDwf HRwf X2 H4 H12) as X3.
      destruct X3 as [X3 [X4 X5]].
      split; try easy.
      split; try easy.
      split; try easy.
      split. unfold rheap_consistent.
      intros. inv H6. inv H7. easy.
      split.
      unfold stack_rheap_consistent in *. intros.
      inv H6. apply X3. eapply HsHwf; eauto.
      split. apply env_consist_refl.
      split. constructor; eauto. constructor.
      exists (TPtr Checked w). split.
      eapply well_type_eval_type_eq; eauto. constructor. easy.
      destruct HQt as [A1 [A2 A3]]. easy. repeat constructor.
      assert (m' = Tainted). destruct m'; try easy. inv HMode.
      assert (Checked = Checked); try easy. apply H3 in H5. easy.
      subst.
      apply (eval_type_bound_simple D Tainted) in H11 as X1; try easy.
      exists env, (TPtr Tainted w').
      split; try easy.
      split; try easy.
      split; try easy.
      split. unfold rheap_consistent.
      intros. inv H3. inv H4. unfold heap_consistent_checked. intuition.
      split. unfold stack_rheap_consistent in *.
      intros. inv H3. eapply HsHwf; eauto.
      split. apply env_consist_refl.
      split. apply TyLitTainted.
      intros R. inv R. unfold simple_type in *. simpl. easy.
      exists (TPtr Tainted w). split.
      eapply well_type_eval_type_eq; eauto. constructor. easy.
      destruct HQt as [A1 [A2 A3]]. easy. repeat constructor.
      inv HEwf. easy.

    (* T-Unchecked *)
    - inv Hreduces.
      destruct E; inversion H; simpl in *; subst.
      inv H2. inv HTy. inv HEwf.
      exists env, t''.
      split; try easy.
      split; try easy.
      split; try easy.
      split. apply rheap_consistent_refl.
      split; try easy.
      split. apply env_consist_refl.
      split. apply TyLitTainted.
      apply eval_type_bound_not_checked with (s := s') (t := t); try easy.
      apply eq_subtype_not_checked_1 with (Q := Q) (t' := t'); try easy.
      eapply eval_type_bound_simple; eauto.
      assert (type_eq Q t'' t).
      apply well_type_eval_type_eq with (s := s') (env := env); try easy.
      apply (eq_subtype_well_type_bound Q) with (t := t'); try easy.
      destruct HQt as [X1 [X2 X3]]. easy.
      destruct HQt as [X1 [X2 X3]]. easy.
      exists t. split. easy.
      repeat constructor.
      inv HEwf. 
      apply step_implies_reduces_1 
          with (cm := Unchecked) (m := Checked) (E := E) in H2; try easy.
      edestruct IH; eauto.
      destruct H0 as [ta [X1 [X2 [X3 [X4 [X5 [X6 [X7 X8]]]]]]]].
      exists x,t.
      split; try easy.
      split; try easy.
      split; try easy.
      split; try easy.
      split; try easy.
      split; try easy.
      split. apply TyUnchecked with (t' := ta); try easy.
      eapply reduce_list_sub; eauto.
      eapply eq_subtype_trans; eauto.
      eapply env_consist_is_tainteds; eauto. exists t.
      split. apply type_eq_refl. repeat constructor.

    (* T-Checked *)
    - inv Hreduces.
      destruct E; inversion H; simpl in *; subst.
      inv H2. inv HTy. inv HEwf.
      exists env, t''.
      split; try easy.
      split; try easy.
      split; try easy.
      split. apply rheap_consistent_refl.
      split; try easy.
      split. apply env_consist_refl.
      split. 
      assert (is_checked t'').
      apply eval_type_bound_is_checked with (s := s') (t := t); try easy.
      apply eq_subtype_is_checked_1 with (Q := Q) (t' := t'); try easy.
      assert (simple_type t'').
      eapply eval_type_bound_simple; eauto.
      assert (type_eq Q t'' t).
      apply well_type_eval_type_eq with (s := s') (env := env); try easy.
      apply (eq_subtype_well_type_bound Q) with (t := t'); try easy.
      destruct HQt as [X1 [X2 X3]]. easy.
      destruct HQt as [X1 [X2 X3]]. easy.
      constructor; try easy.
      assert (eq_subtype Q t t''). exists t''. split; try easy.
      apply type_eq_sym. easy.
      repeat constructor.
      apply eq_subtype_trans with (t1 := t') in H5; try easy.
      apply eq_subtype_empty with (env := env) in H5; try easy.
      apply checked_subtype_well_type with (t := t') ; try easy.
      apply type_eq_type_wf_1 with (Q := Q) (t := t); try easy.
      apply type_wf_uc_c with (m := Unchecked); try easy.
      destruct HQt as [X1 [X2 X3]]. easy.
      assert (type_eq Q t'' t).
      apply well_type_eval_type_eq with (s := s') (env := env); try easy.
      apply (eq_subtype_well_type_bound Q) with (t := t'); try easy.
      destruct HQt as [X1 [X2 X3]]. easy.
      destruct HQt as [X1 [X2 X3]]. easy.
      exists t. split. easy. repeat constructor.
      inv HEwf.
      exists env, t''.
      split; try easy.
      split; try easy.
      split; try easy.
      split. apply rheap_consistent_refl.
      split; try easy.
      split. apply env_consist_refl.
      split. apply TyLitTainted.
      apply eval_type_bound_not_checked with (s := s') (t := t); try easy.
      apply eq_subtype_not_checked_1 with (Q := Q) (t' := t'); try easy.
      eapply eval_type_bound_simple; eauto.
      assert (type_eq Q t'' t).
      apply well_type_eval_type_eq with (s := s') (env := env); try easy.
      apply (eq_subtype_well_type_bound Q) with (t := t'); try easy.
      destruct HQt as [X1 [X2 X3]]. easy.
      destruct HQt as [X1 [X2 X3]]. easy.
      exists t. split. easy.
      repeat constructor.
      inv HEwf. 
      apply step_implies_reduces_1 
          with (cm := Checked) (m := Checked) (E := E) in H2; try easy.
      edestruct IH; eauto.
      destruct H0 as [ta [X1 [X2 [X3 [X4 [X5 [X6 [X7 X8]]]]]]]].
      exists x,t.
      split; try easy.
      split; try easy.
      split; try easy.
      split; try easy.
      split; try easy.
      split; try easy.
      split. apply Tychecked with (t' := ta); try easy.
      eapply reduce_list_sub; eauto.
      eapply eq_subtype_trans; eauto.
      eapply env_consist_is_tainteds; eauto. exists t.
      split. apply type_eq_refl. repeat constructor.

    (* T-Cast-Unchecked *)
    - inv Hreduces.
      destruct E; inversion H; simpl in *; subst. easy.
      inv HEwf. specialize (IH H7 Henvt s).
      edestruct IH; eauto.
      apply step_implies_reduces_1 
          with (cm := Unchecked) (m := Checked) (E := E) in H2; try easy.
      apply H2.
      destruct H0 as [ta [X1 [X2 [X3 [X4 [X5 [X6 [X7 X8]]]]]]]].
      exists x, t.
      split; try easy.
      split; try easy.
      split; try easy.
      split; try easy.
      split; try easy.
      split; try easy.
      split. apply TyCast1 with (t' := ta); try easy.
      destruct X6 as [A1 [A2 A3]]. 
      unfold well_type_bound_in in *. intros.
      apply Wb in H0. apply A2 in H0. easy.
      intros R1. unfold is_nt_ptr in *. easy.
      exists t. split. apply type_eq_refl. repeat constructor.

    (* T-Cast-Checked *)
    - inv Hreduces.
      destruct E; inversion H; simpl in *; subst. 
      inv H2. inv HTy.
      exists env,t''.
      split; try easy.
      split; try easy.
      split; try easy.
      split. apply rheap_consistent_refl.
      split. easy.
      split. apply env_consist_refl.
      split. 
      assert (type_eq Q t'' (TPtr m t)).
      apply (well_type_eval_type_eq Q env s'); try easy.
      destruct HQt as [A1 [A2 A3]]. easy.
      apply type_eq_sym in H.
      assert (eq_subtype Q (TPtr m t) t'').
      exists t''. split. easy. repeat constructor.
      apply eq_subtype_trans with (t1 := t') in H2; try easy.
      constructor; try easy.
      eapply eq_subtype_is_checked_1; eauto.
      inv HEwf.
      eapply eval_type_bound_simple in H1; eauto.
      eapply checked_subtype_well_type; eauto.
      inv HEwf.
      eapply eval_type_bound_simple in H1; eauto.
      eapply eval_type_bound_type_wf; eauto. inv HEwf; easy.
      inv HEwf.
      assert (simple_type t'').
      eapply eval_type_bound_simple in H1; eauto.
      eapply eq_subtype_empty; eauto.
      destruct HQt. easy.
      assert (type_eq Q t'' (TPtr m t)).
      apply (well_type_eval_type_eq Q env s'); try easy.
      destruct HQt as [A1 [A2 A3]]. easy.
      exists (TPtr m t). split. easy. repeat constructor.
      inv HEwf.
      exists env,t''.
      split; try easy.
      split; try easy.
      split; try easy.
      split. apply rheap_consistent_refl.
      split. easy.
      split. apply env_consist_refl.
      assert (type_eq Q t'' (TPtr m t)).
      apply (well_type_eval_type_eq Q env s'); try easy.
      destruct HQt as [A1 [A2 A3]]. easy.
      apply type_eq_sym in H.
      assert (eq_subtype Q (TPtr m t) t'').
      exists t''. split. easy. repeat constructor.
      apply eq_subtype_trans with (t1 := t') in H2; try easy.
      constructor; try easy.
      apply TyLitTainted; eauto.
      eapply eq_subtype_not_checked_1; eauto.
      eapply eval_type_bound_simple in H1; eauto.
      assert (type_eq Q t'' (TPtr m t)).
      apply (well_type_eval_type_eq Q env s'); try easy.
      destruct HQt as [A1 [A2 A3]]. easy.
      exists (TPtr m t). split. easy. repeat constructor.
      inv HEwf. specialize (IH H7 Henvt s).
      edestruct IH; eauto.
      apply step_implies_reduces_1 
          with (cm := Checked) (m := Checked) (E := E) in H2; try easy.
      apply H2.
      destruct H0 as [ta [X1 [X2 [X3 [X4 [X5 [X6 [X7 X8]]]]]]]].
      exists x, (TPtr m t).
      split; try easy.
      split; try easy.
      split; try easy.
      split; try easy.
      split; try easy.
      split; try easy.
      split. apply TyCast2 with (t' := ta) ; try easy.
      destruct X6 as [A1 [A2 A3]]. 
      unfold well_type_bound_in in *. intros.
      apply Wb in H0. apply A2 in H0. easy.
      intros R1. unfold is_nt_ptr in *. easy.
      eapply eq_subtype_trans; eauto.
      exists (TPtr m t). split. apply type_eq_refl. repeat constructor.
    (* T-DynCast-Array *)
    - inv Hreduces.
      destruct E; inversion H; simpl in *; subst. 
      inv H2. inv HTy. 
      unfold is_array_ptr in *. easy.
      unfold is_array_ptr in *. easy.
      inv HTy. inv H2. inv H10. inv H9. inv H1. inv H2.
      apply (eval_type_bound_type_eq Q env s' t w t' w' ) in H18 as A1; try easy; subst.
      apply eval_type_bound_idempotent with (s := s') in H6 as A2.
      inv A2. inv H1. apply eval_type_bound_preserve with (t' := t') in H16 as A3; try easy.
      subst. exists env, (TPtr Checked (TArray (Num l) (Num h) w')).
      split; try easy.
      split; try easy.
      split; try easy.
      split. apply rheap_consistent_refl.
      split; try easy. split. apply env_consist_refl.
      split. constructor; try easy. constructor.
      unfold simple_type in *. simpl in *.
      apply app_eq_nil in H6. destruct H6. apply app_eq_nil in H1. destruct H1. easy.
      apply checked_subtype_well_type with (t := (TPtr Checked (TArray u v w'))); eauto.
      apply app_eq_nil in H6. destruct H6. apply app_eq_nil in H1. destruct H1. easy.
      inv HEwf. inv H4. constructor. inv H3. constructor.
      eapply eval_type_bound_word_type with (t := t); eauto.
      eapply eval_type_bound_type_wf with (t := t); eauto.
      constructor. inv H23. constructor.
      eapply eval_type_bound_word_type with (t := t); eauto.
      eapply eval_type_bound_type_wf with (t := t); eauto.
      exists (TPtr Checked (TArray u v w')). split. apply type_eq_refl.
      constructor.
      apply simple_type_array_num in H6 as eq1.
      destruct eq1 as [B1 B2]. destruct B1; subst. destruct B2; subst.
      unfold eval_bound in H9,H15. inv H9. inv H15.
      apply SubTySubsume; try easy. constructor; easy. constructor; easy.
      exists (TPtr Checked (TArray (Num l) (Num h) t)). split.
      constructor. constructor; try easy. apply type_eq_sym; try easy.
      split. constructor; lia. constructor;lia.
      split. constructor; lia. constructor;lia.
      constructor.
      apply SubTySubsume; try easy.
      destruct x. unfold eval_bound in H8. inv H8. constructor;lia.
      unfold eval_bound in H8. destruct (Stack.find (elt:=Z * type) v0 s') eqn:eq1.
      destruct p. apply Stack.find_2 in eq1. inv H8.
      destruct HQt as [A1 [A2 A3]].
      unfold well_type_bound_in in Wb. simpl in *.
      assert (v0 = v0 \/ In v0 (freeBoundVars y ++ freeTypeVars t)). left. easy.
      apply Wb in H. apply Hswf in H.
      destruct H as [va [ta [B1 B2]]]. apply eq_subtype_nat_1 in B1; subst.
      apply Stack.mapsto_always_same with (v1 := (z0, t0)) in B2; try easy. inv B2.
      apply A3 in eq1. eapply nat_leq_var_2; eauto. constructor; lia. easy.
      destruct y. unfold eval_bound in H17. inv H17. constructor;lia.
      unfold eval_bound in H17. destruct (Stack.find (elt:=Z * type) v0 s') eqn:eq1.
      destruct p. apply Stack.find_2 in eq1. inv H17.
      destruct HQt as [A1 [A2 A3]].
      unfold well_type_bound_in in Wb. simpl in *.
      assert (In v0 (freeBoundVars x ++ v0 :: freeTypeVars t)).
      apply in_app_iff. right. simpl. left. easy.
      apply Wb in H. apply Hswf in H.
      destruct H as [va [ta [B1 B2]]]. apply eq_subtype_nat_1 in B1; subst.
      apply Stack.mapsto_always_same with (v1 := (z0, t0)) in B2; try easy. inv B2.
      apply A3 in eq1. eapply nat_leq_var_1; eauto. constructor; lia. easy.
      unfold well_type_bound_in in *.
      intros. apply Wb. simpl.
      apply in_app_iff. right.
      apply in_app_iff. right. easy.
      apply simple_means_not_freeVars in H6. simpl in *. unfold well_type_bound_in. intros.
      apply app_eq_nil in H6. destruct H6. apply app_eq_nil in H2. destruct H2. rewrite H3 in H. simpl in *. easy.
      destruct HQt as [A1 [A2 A3]]; easy.
      assert (m = Tainted). destruct HMode. assert (Checked = Checked) by easy. apply H in H2. destruct m; try easy.
      assert (is_checked (TPtr Checked (TArray u v t'))). constructor. easy. subst. clear H6.
      inv H10. inv H9. inv H1. inv H2.
      apply (eval_type_bound_type_eq Q env s' t w t' w' ) in H17 as A1; try easy; subst.
      apply eval_type_bound_idempotent with (s := s') in H8 as A2.
      inv A2. inv H1. apply eval_type_bound_preserve with (t' := t') in H15 as A3; try easy.
      subst. exists env, (TPtr Tainted (TArray (Num l) (Num h) w')).
      split; try easy.
      split; try easy.
      split; try easy.
      split. apply rheap_consistent_refl.
      split; try easy. split. apply env_consist_refl.
      split. apply TyLitTainted; try easy.
      unfold simple_type in *. simpl in *.
      apply app_eq_nil in H8. destruct H8. apply app_eq_nil in H1. destruct H1. easy.
      exists (TPtr Tainted (TArray (Num l) (Num h) t)). split.
      constructor. constructor; try easy. apply type_eq_sym; try easy.
      split. constructor; lia. constructor;lia.
      split. constructor; lia. constructor;lia.
      constructor.
      apply SubTySubsume; try easy.
      destruct x. unfold eval_bound in H6. inv H6. constructor;lia.
      unfold eval_bound in H6. destruct (Stack.find (elt:=Z * type) v0 s') eqn:eq1.
      destruct p. apply Stack.find_2 in eq1. inv H6.
      destruct HQt as [A1 [A2 A3]].
      unfold well_type_bound_in in Wb. simpl in *.
      assert (v0 = v0 \/ In v0 (freeBoundVars y ++ freeTypeVars t)). left. easy.
      apply Wb in H. apply Hswf in H.
      destruct H as [va [ta [B1 B2]]]. apply eq_subtype_nat_1 in B1; subst.
      apply Stack.mapsto_always_same with (v1 := (z0, t0)) in B2; try easy. inv B2.
      apply A3 in eq1. eapply nat_leq_var_2; eauto. constructor; lia. easy.
      destruct y. unfold eval_bound in H16. inv H16. constructor;lia.
      unfold eval_bound in H16. destruct (Stack.find (elt:=Z * type) v0 s') eqn:eq1.
      destruct p. apply Stack.find_2 in eq1. inv H16.
      destruct HQt as [A1 [A2 A3]].
      unfold well_type_bound_in in Wb. simpl in *.
      assert (In v0 (freeBoundVars x ++ v0 :: freeTypeVars t)).
      apply in_app_iff. right. simpl. left. easy.
      apply Wb in H. apply Hswf in H.
      destruct H as [va [ta [B1 B2]]]. apply eq_subtype_nat_1 in B1; subst.
      apply Stack.mapsto_always_same with (v1 := (z0, t0)) in B2; try easy. inv B2.
      apply A3 in eq1. eapply nat_leq_var_1; eauto. constructor; lia. easy.
      unfold well_type_bound_in in *.
      intros. apply Wb. simpl.
      apply in_app_iff. right.
      apply in_app_iff. right. easy.
      apply simple_means_not_freeVars in H8. simpl in *. unfold well_type_bound_in. intros.
      apply app_eq_nil in H8. destruct H8. apply app_eq_nil in H2. destruct H2. rewrite H3 in H. simpl in *. easy.
      destruct HQt as [A1 [A2 A3]]; easy. 
      inv H9. inv H1. inv HTy. inv H10. inv H1. inv H10. inv H1.
      inv HEwf. specialize (IH H7 Henvt s).
      edestruct IH; eauto.
      apply step_implies_reduces_1 
          with (cm := Checked) (m := Checked) (E := E) in H2; try easy.
      apply H2.
      destruct H0 as [ta [X1 [X2 [X3 [X4 [X5 [X6 [X7 X8]]]]]]]].
      apply eq_subtype_array_form in X8 as eq1.
      destruct eq1 as [tb [A1 A2]].
      exists x0, (TPtr m (TArray x y t)).
      split; try easy.
      split; try easy.
      split; try easy.
      split; try easy.
      split; try easy.
      split; try easy.
      split.
      destruct A2. destruct H0 as [A [A2 [A3 A4]]]; subst.
      apply TyDynCast2 with (t' := tb); try easy.
      apply type_eq_sym in A1. eapply type_eq_trans; eauto.
      eapply env_consist_well_bound; eauto.
      destruct H0. destruct H0 as [ua [va [A2 [A3 A4]]]];subst.
      apply TyDynCast1 with (t' := tb) (u := ua) (v := va); try easy.
      eapply env_consist_well_bound; eauto.
      apply type_eq_sym in A1. eapply type_eq_trans; eauto.
      destruct H0 as [ua [va [A2 [A3 A4]]]];subst.
      apply TyDynCast4 with (t' := tb) (u := ua) (v := va); try easy.
      eapply env_consist_well_bound; eauto.
      apply type_eq_sym in A1. eapply type_eq_trans; eauto.
      exists (TPtr m (TArray x y t)). split. apply type_eq_refl. repeat constructor.
    (* T-DynCast-NotArray *)
    - inv Hreduces.
      destruct E; inversion H; simpl in *; subst. 
      inv H2. inv HTy. inv H6. inv H8. inv H1.
      apply (eval_type_bound_type_eq Q env s' t w t' t' ) in H12 as A1; try easy; subst.
      subst. exists env, (TPtr Checked (TArray (Num l) (Num h) t')).
      split; try easy.
      split; try easy.
      split; try easy.
      split. apply rheap_consistent_refl.
      split; try easy. split. apply env_consist_refl.
      split. constructor; try easy. constructor.
      apply checked_subtype_well_type with (t := (TPtr Checked t')); eauto.
      inv HEwf. inv H4; try easy. inv H3. constructor. constructor.
      eapply eval_type_bound_word_type with (t := t); eauto.
      eapply eval_type_bound_type_wf with (t := t); eauto.
      exists (TPtr Checked t'). split. apply type_eq_refl.
      constructor. apply SubTyBot; try easy.
      constructor; try lia. constructor;try lia.
      exists (TPtr Checked (TArray x y t)). split.
      eapply well_type_eval_type_eq; eauto.
      constructor. constructor; try easy.
      destruct HQt as [X1 [X2 X3]];easy.
      repeat constructor.
      apply eval_type_bound_idempotent with (s := s') in H7. inv H7. easy.
      unfold well_type_bound_in in *. intros. apply Wb. simpl.
      apply in_app_iff. right. apply in_app_iff. right. easy.
      apply simple_means_not_freeVars in H7. simpl in *. 
      unfold well_type_bound_in in *. intros. rewrite H7 in H. simpl in *. easy.
      destruct HQt as [X1 [X2 X3]];easy.
      assert (m = Tainted). destruct HMode. apply H in H5. destruct m; try easy.
      assert (is_checked (TPtr Checked t')). constructor. easy. subst.
      inv H8. inv H1.
      apply (eval_type_bound_type_eq Q env s' t w t' t' ) in H12 as A1; try easy; subst.
      subst. exists env, (TPtr Tainted (TArray (Num l) (Num h) t')).
      split; try easy.
      split; try easy.
      split; try easy.
      split. apply rheap_consistent_refl.
      split; try easy. split. apply env_consist_refl.
      split. apply TyLitTainted; try easy. 
      exists (TPtr Tainted (TArray x y t)). split.
      eapply well_type_eval_type_eq; eauto.
      constructor. constructor; try easy.
      destruct HQt as [X1 [X2 X3]];easy.
      repeat constructor.
      apply eval_type_bound_idempotent with (s := s') in H9. inv H9. easy.
      unfold well_type_bound_in in *. intros. apply Wb. simpl.
      apply in_app_iff. right. apply in_app_iff. right. easy.
      apply simple_means_not_freeVars in H9. simpl in *. 
      unfold well_type_bound_in in *. intros. rewrite H9 in H. simpl in *. easy.
      destruct HQt as [X1 [X2 X3]];easy.
      inv HTy. inv H10. inv H1. easy.
      inv H10. inv H1. easy. inv HTy. inv H10. inv H1. easy.
      inv H10. inv H1. easy. inv HTy. inv H10. inv H1. easy.
      inv H10. inv H1. easy.
      inv HEwf. specialize (IH H7 Henvt s).
      edestruct IH; eauto.
      apply step_implies_reduces_1 
          with (cm := Checked) (m := Checked) (E := E) in H2; try easy.
      apply H2.
      destruct H0 as [ta [X1 [X2 [X3 [X4 [X5 [X6 [X7 X8]]]]]]]].
      apply eq_subtype_ptr_form in X8 as eq1;try easy.
      destruct eq1 as [tb [A1 A2]].
      exists x0, (TPtr m (TArray x y t)).
      split; try easy.
      split; try easy.
      split; try easy.
      split; try easy.
      split; try easy.
      split; try easy.
      split.
      destruct A2. subst. 
      apply TyDynCast2 with (t' := tb); try easy.
      eapply type_eq_word; eauto. apply type_eq_sym in A1. eapply type_eq_trans; eauto.
      eapply env_consist_well_bound; eauto.
      destruct H0. destruct H0 as [ua [va [A2 [A3 A4]]]];subst.
      apply TyDynCast1 with (t' := tb) (u := ua) (v := va); try easy.
      eapply env_consist_well_bound; eauto.
      apply type_eq_sym in A1. eapply type_eq_trans; eauto.
      destruct H0 as [ua [va [A2 [A3 A4]]]];subst.
      apply TyDynCast4 with (t' := tb) (u := ua) (v := va); try easy.
      eapply env_consist_well_bound; eauto.
      apply type_eq_sym in A1. eapply type_eq_trans; eauto.
      exists (TPtr m (TArray x y t)). split. apply type_eq_refl. repeat constructor.
    (* T-DynCast-NTArray *)
    - inv Hreduces.
      destruct E; inversion H; simpl in *; subst. 
      inv H2. inv H9. inv H1. inv HTy. 
      inv H2. inv H10. inv H9. inv H1. inv H2.
      apply (eval_type_bound_type_eq Q env s' t w t' w' ) in H18 as A1; try easy; subst.
      apply eval_type_bound_idempotent with (s := s') in H6 as A2.
      inv A2. inv H1. apply eval_type_bound_preserve with (t' := t') in H16 as A3; try easy.
      subst. exists env, (TPtr Checked (TNTArray (Num l) (Num h) w')).
      split; try easy.
      split; try easy.
      split; try easy.
      split. apply rheap_consistent_refl.
      split; try easy. split. apply env_consist_refl.
      split. constructor; try easy. constructor.
      unfold simple_type in *. simpl in *.
      apply app_eq_nil in H6. destruct H6. apply app_eq_nil in H1. destruct H1. easy.
      apply checked_subtype_well_type with (t := (TPtr Checked (TNTArray u v w'))); eauto.
      apply app_eq_nil in H6. destruct H6. apply app_eq_nil in H1. destruct H1. easy.
      inv HEwf. inv H4. constructor. inv H3. constructor.
      eapply eval_type_bound_word_type with (t := t); eauto.
      eapply eval_type_bound_type_wf with (t := t); eauto.
      constructor. inv H23. constructor.
      eapply eval_type_bound_word_type with (t := t); eauto.
      eapply eval_type_bound_type_wf with (t := t); eauto.
      exists (TPtr Checked (TNTArray u v w')). split. apply type_eq_refl.
      constructor.
      apply simple_type_nt_num in H6 as eq1.
      destruct eq1 as [B1 B2]. destruct B1; subst. destruct B2; subst.
      unfold eval_bound in H9,H15. inv H9. inv H15.
      apply SubTyNtSubsume; try easy. constructor; easy. constructor; easy.
      exists (TPtr Checked (TNTArray (Num l) (Num h) t)). split.
      constructor. constructor; try easy. apply type_eq_sym; try easy.
      split. constructor; lia. constructor;lia.
      split. constructor; lia. constructor;lia.
      constructor.
      apply SubTyNtSubsume; try easy.
      destruct x. unfold eval_bound in H8. inv H8. constructor;lia.
      unfold eval_bound in H8. destruct (Stack.find (elt:=Z * type) v0 s') eqn:eq1.
      destruct p. apply Stack.find_2 in eq1. inv H8.
      destruct HQt as [A1 [A2 A3]].
      unfold well_type_bound_in in Wb. simpl in *.
      assert (v0 = v0 \/ In v0 (freeBoundVars y ++ freeTypeVars t)). left. easy.
      apply Wb in H. apply Hswf in H.
      destruct H as [va [ta [B1 B2]]]. apply eq_subtype_nat_1 in B1; subst.
      apply Stack.mapsto_always_same with (v1 := (z0, t0)) in B2; try easy. inv B2.
      apply A3 in eq1. eapply nat_leq_var_2; eauto. constructor; lia. easy.
      destruct y. unfold eval_bound in H17. inv H17. constructor;lia.
      unfold eval_bound in H17. destruct (Stack.find (elt:=Z * type) v0 s') eqn:eq1.
      destruct p. apply Stack.find_2 in eq1. inv H17.
      destruct HQt as [A1 [A2 A3]].
      unfold well_type_bound_in in Wb. simpl in *.
      assert (In v0 (freeBoundVars x ++ v0 :: freeTypeVars t)).
      apply in_app_iff. right. simpl. left. easy.
      apply Wb in H. apply Hswf in H.
      destruct H as [va [ta [B1 B2]]]. apply eq_subtype_nat_1 in B1; subst.
      apply Stack.mapsto_always_same with (v1 := (z0, t0)) in B2; try easy. inv B2.
      apply A3 in eq1. eapply nat_leq_var_1; eauto. constructor; lia. easy.
      unfold well_type_bound_in in *.
      intros. apply Wb. simpl.
      apply in_app_iff. right.
      apply in_app_iff. right. easy.
      apply simple_means_not_freeVars in H6. simpl in *. unfold well_type_bound_in. intros.
      apply app_eq_nil in H6. destruct H6. apply app_eq_nil in H2. destruct H2. rewrite H3 in H. simpl in *. easy.
      destruct HQt as [A1 [A2 A3]]; easy.
      assert (m = Tainted). destruct HMode. assert (Checked = Checked) by easy. apply H in H2. destruct m; try easy.
      assert (is_checked (TPtr Checked (TNTArray u v t'))). constructor. easy. subst. clear H6.
      inv H10. inv H9. inv H1. inv H2.
      apply (eval_type_bound_type_eq Q env s' t w t' w' ) in H17 as A1; try easy; subst.
      apply eval_type_bound_idempotent with (s := s') in H8 as A2.
      inv A2. inv H1. apply eval_type_bound_preserve with (t' := t') in H15 as A3; try easy.
      subst. exists env, (TPtr Tainted (TNTArray (Num l) (Num h) w')).
      split; try easy.
      split; try easy.
      split; try easy.
      split. apply rheap_consistent_refl.
      split; try easy. split. apply env_consist_refl.
      split. apply TyLitTainted; try easy.
      unfold simple_type in *. simpl in *.
      apply app_eq_nil in H8. destruct H8. apply app_eq_nil in H1. destruct H1. easy.
      exists (TPtr Tainted (TNTArray (Num l) (Num h) t)). split.
      constructor. constructor; try easy. apply type_eq_sym; try easy.
      split. constructor; lia. constructor;lia.
      split. constructor; lia. constructor;lia.
      constructor.
      apply SubTyNtSubsume; try easy.
      destruct x. unfold eval_bound in H6. inv H6. constructor;lia.
      unfold eval_bound in H6. destruct (Stack.find (elt:=Z * type) v0 s') eqn:eq1.
      destruct p. apply Stack.find_2 in eq1. inv H6.
      destruct HQt as [A1 [A2 A3]].
      unfold well_type_bound_in in Wb. simpl in *.
      assert (v0 = v0 \/ In v0 (freeBoundVars y ++ freeTypeVars t)). left. easy.
      apply Wb in H. apply Hswf in H.
      destruct H as [va [ta [B1 B2]]]. apply eq_subtype_nat_1 in B1; subst.
      apply Stack.mapsto_always_same with (v1 := (z0, t0)) in B2; try easy. inv B2.
      apply A3 in eq1. eapply nat_leq_var_2; eauto. constructor; lia. easy.
      destruct y. unfold eval_bound in H16. inv H16. constructor;lia.
      unfold eval_bound in H16. destruct (Stack.find (elt:=Z * type) v0 s') eqn:eq1.
      destruct p. apply Stack.find_2 in eq1. inv H16.
      destruct HQt as [A1 [A2 A3]].
      unfold well_type_bound_in in Wb. simpl in *.
      assert (In v0 (freeBoundVars x ++ v0 :: freeTypeVars t)).
      apply in_app_iff. right. simpl. left. easy.
      apply Wb in H. apply Hswf in H.
      destruct H as [va [ta [B1 B2]]]. apply eq_subtype_nat_1 in B1; subst.
      apply Stack.mapsto_always_same with (v1 := (z0, t0)) in B2; try easy. inv B2.
      apply A3 in eq1. eapply nat_leq_var_1; eauto. constructor; lia. easy.
      unfold well_type_bound_in in *.
      intros. apply Wb. simpl.
      apply in_app_iff. right.
      apply in_app_iff. right. easy.
      apply simple_means_not_freeVars in H8. simpl in *. unfold well_type_bound_in. intros.
      apply app_eq_nil in H8. destruct H8. apply app_eq_nil in H2. destruct H2. rewrite H3 in H. simpl in *. easy.
      destruct HQt as [A1 [A2 A3]]; easy.
      inv H9. inv H1. 
      inv HEwf. specialize (IH H7 Henvt s).
      edestruct IH; eauto.
      apply step_implies_reduces_1 
          with (cm := Checked) (m := Checked) (E := E) in H2; try easy.
      apply H2.
      destruct H0 as [ta [X1 [X2 [X3 [X4 [X5 [X6 [X7 X8]]]]]]]].
      apply eq_subtype_nt_form in X8 as eq1.
      destruct eq1 as [tb [ua [va [A1 [A2 [A3 A4]]]]]]; subst.
      exists x0, (TPtr m (TNTArray x y t)).
      split; try easy.
      split; try easy.
      split; try easy.
      split; try easy.
      split; try easy.
      split; try easy.
      split.
      apply TyDynCast3 with (t' := tb) (u := ua) (v := va); try easy.
      eapply env_consist_well_bound; eauto.
      apply type_eq_sym in A1. eapply type_eq_trans; eauto.
      exists (TPtr m (TNTArray x y t)). split. apply type_eq_refl. repeat constructor.
    (* T-DynCast-NTArray-Array *)
    - inv Hreduces.
      destruct E; inversion H; simpl in *; subst. 
      inv H2. inv HTy. 
      unfold is_array_ptr in *. easy.
      unfold is_array_ptr in *. easy.
      inv HTy. inv H10. inv H1. inv H10. inv H1.
      inv HTy. inv H2. inv H10. inv H9. inv H1. inv H2.
      inv H10. inv H9. inv H1. inv H2.
      inv HTy. inv H2. inv H10. inv H9. inv H1. inv H2.
      apply (eval_type_bound_type_eq Q env s' t w t' w' ) in H18 as A1; try easy; subst.
      apply eval_type_bound_idempotent with (s := s') in H6 as A2.
      inv A2. inv H1. apply eval_type_bound_preserve with (t' := t') in H16 as A3; try easy.
      subst. exists env, (TPtr Checked (TArray (Num l) (Num h) w')).
      split; try easy.
      split; try easy.
      split; try easy.
      split. apply rheap_consistent_refl.
      split; try easy. split. apply env_consist_refl.
      split. constructor; try easy. constructor.
      unfold simple_type in *. simpl in *.
      apply app_eq_nil in H6. destruct H6. apply app_eq_nil in H1. destruct H1. easy.
      apply checked_subtype_well_type with (t := (TPtr Checked (TNTArray u v w'))); eauto.
      apply app_eq_nil in H6. destruct H6. apply app_eq_nil in H1. destruct H1. easy.
      inv HEwf. inv H4. constructor. inv H3. constructor.
      eapply eval_type_bound_word_type with (t := t); eauto.
      eapply eval_type_bound_type_wf with (t := t); eauto.
      constructor. inv H23. constructor.
      eapply eval_type_bound_word_type with (t := t); eauto.
      eapply eval_type_bound_type_wf with (t := t); eauto.
      exists (TPtr Checked (TNTArray u v w')). split. apply type_eq_refl.
      constructor.
      apply simple_type_nt_num in H6 as eq1.
      destruct eq1 as [B1 B2]. destruct B1; subst. destruct B2; subst.
      unfold eval_bound in H9,H15. inv H9. inv H15.
      apply SubTyNtArray; try easy. constructor; easy. constructor; easy.
      exists (TPtr Checked (TArray (Num l) (Num h) t)). split.
      constructor. constructor; try easy. apply type_eq_sym; try easy.
      split. constructor; lia. constructor;lia.
      split. constructor; lia. constructor;lia.
      constructor.
      apply SubTySubsume; try easy.
      destruct x. unfold eval_bound in H8. inv H8. constructor;lia.
      unfold eval_bound in H8. destruct (Stack.find (elt:=Z * type) v0 s') eqn:eq1.
      destruct p. apply Stack.find_2 in eq1. inv H8.
      destruct HQt as [A1 [A2 A3]].
      unfold well_type_bound_in in Wb. simpl in *.
      assert (v0 = v0 \/ In v0 (freeBoundVars y ++ freeTypeVars t)). left. easy.
      apply Wb in H. apply Hswf in H.
      destruct H as [va [ta [B1 B2]]]. apply eq_subtype_nat_1 in B1; subst.
      apply Stack.mapsto_always_same with (v1 := (z0, t0)) in B2; try easy. inv B2.
      apply A3 in eq1. eapply nat_leq_var_2; eauto. constructor; lia. easy.
      destruct y. unfold eval_bound in H17. inv H17. constructor;lia.
      unfold eval_bound in H17. destruct (Stack.find (elt:=Z * type) v0 s') eqn:eq1.
      destruct p. apply Stack.find_2 in eq1. inv H17.
      destruct HQt as [A1 [A2 A3]].
      unfold well_type_bound_in in Wb. simpl in *.
      assert (In v0 (freeBoundVars x ++ v0 :: freeTypeVars t)).
      apply in_app_iff. right. simpl. left. easy.
      apply Wb in H. apply Hswf in H.
      destruct H as [va [ta [B1 B2]]]. apply eq_subtype_nat_1 in B1; subst.
      apply Stack.mapsto_always_same with (v1 := (z0, t0)) in B2; try easy. inv B2.
      apply A3 in eq1. eapply nat_leq_var_1; eauto. constructor; lia. easy.
      unfold well_type_bound_in in *.
      intros. apply Wb. simpl.
      apply in_app_iff. right.
      apply in_app_iff. right. easy.
      apply simple_means_not_freeVars in H6. simpl in *. unfold well_type_bound_in. intros.
      apply app_eq_nil in H6. destruct H6. apply app_eq_nil in H2. destruct H2. rewrite H3 in H. simpl in *. easy.
      destruct HQt as [A1 [A2 A3]]; easy.
      assert (m = Tainted). destruct HMode. assert (Checked = Checked) by easy. apply H in H2. destruct m; try easy.
      assert (is_checked (TPtr Checked (TNTArray u v t'))). constructor. easy. subst. clear H6.
      inv H10. inv H9. inv H1. inv H2.
      apply (eval_type_bound_type_eq Q env s' t w t' w' ) in H17 as A1; try easy; subst.
      apply eval_type_bound_idempotent with (s := s') in H8 as A2.
      inv A2. inv H1. apply eval_type_bound_preserve with (t' := t') in H15 as A3; try easy.
      subst. exists env, (TPtr Tainted (TArray (Num l) (Num h) w')).
      split; try easy.
      split; try easy.
      split; try easy.
      split. apply rheap_consistent_refl.
      split; try easy. split. apply env_consist_refl.
      split. apply TyLitTainted; try easy.
      unfold simple_type in *. simpl in *.
      apply app_eq_nil in H8. destruct H8. apply app_eq_nil in H1. destruct H1. easy.
      exists (TPtr Tainted (TArray (Num l) (Num h) t)). split.
      constructor. constructor; try easy. apply type_eq_sym; try easy.
      split. constructor; lia. constructor;lia.
      split. constructor; lia. constructor;lia.
      constructor.
      apply SubTySubsume; try easy.
      destruct x. unfold eval_bound in H6. inv H6. constructor;lia.
      unfold eval_bound in H6. destruct (Stack.find (elt:=Z * type) v0 s') eqn:eq1.
      destruct p. apply Stack.find_2 in eq1. inv H6.
      destruct HQt as [A1 [A2 A3]].
      unfold well_type_bound_in in Wb. simpl in *.
      assert (v0 = v0 \/ In v0 (freeBoundVars y ++ freeTypeVars t)). left. easy.
      apply Wb in H. apply Hswf in H.
      destruct H as [va [ta [B1 B2]]]. apply eq_subtype_nat_1 in B1; subst.
      apply Stack.mapsto_always_same with (v1 := (z0, t0)) in B2; try easy. inv B2.
      apply A3 in eq1. eapply nat_leq_var_2; eauto. constructor; lia. easy.
      destruct y. unfold eval_bound in H16. inv H16. constructor;lia.
      unfold eval_bound in H16. destruct (Stack.find (elt:=Z * type) v0 s') eqn:eq1.
      destruct p. apply Stack.find_2 in eq1. inv H16.
      destruct HQt as [A1 [A2 A3]].
      unfold well_type_bound_in in Wb. simpl in *.
      assert (In v0 (freeBoundVars x ++ v0 :: freeTypeVars t)).
      apply in_app_iff. right. simpl. left. easy.
      apply Wb in H. apply Hswf in H.
      destruct H as [va [ta [B1 B2]]]. apply eq_subtype_nat_1 in B1; subst.
      apply Stack.mapsto_always_same with (v1 := (z0, t0)) in B2; try easy. inv B2.
      apply A3 in eq1. eapply nat_leq_var_1; eauto. constructor; lia. easy.
      unfold well_type_bound_in in *.
      intros. apply Wb. simpl.
      apply in_app_iff. right.
      apply in_app_iff. right. easy.
      apply simple_means_not_freeVars in H8. simpl in *. unfold well_type_bound_in. intros.
      apply app_eq_nil in H8. destruct H8. apply app_eq_nil in H2. destruct H2. rewrite H3 in H. simpl in *. easy.
      destruct HQt as [A1 [A2 A3]]; easy.
      inv HEwf. specialize (IH H7 Henvt s).
      edestruct IH; eauto.
      apply step_implies_reduces_1 
          with (cm := Checked) (m := Checked) (E := E) in H2; try easy.
      apply H2.
      destruct H0 as [ta [X1 [X2 [X3 [X4 [X5 [X6 [X7 X8]]]]]]]].
      apply eq_subtype_nt_form in X8 as eq1.
      destruct eq1 as [tb [ua [va [A1 [A2 [A3 A4]]]]]]; subst.
      exists x0, (TPtr m (TArray x y t)).
      split; try easy.
      split; try easy.
      split; try easy.
      split; try easy.
      split; try easy.
      split; try easy.
      split.
      apply TyDynCast4 with (t' := tb) (u := ua) (v := va); try easy.
      eapply env_consist_well_bound; eauto.
      apply type_eq_sym in A1. eapply type_eq_trans; eauto.
      exists (TPtr m (TArray x y t)). split. apply type_eq_refl. repeat constructor.
    (* T-Deref *)
    - inv Hreduces.
      destruct E; inversion H; simpl in *; subst.
      destruct HPtrType.
      inv H2; try easy.
      inv HTy. destruct H; inv H2. inv H10.
      inv HEwf. inv H6.
      apply eval_type_bound_idempotent with (s := s') in H17 as X1.
      inv X1. apply eval_type_bound_preserve with (t' := t') in H7; try easy; subst.
      exists env,tv. 
      split; try easy.
      split; try easy.
      split; try easy.
      split. apply rheap_consistent_refl.
      split; try easy.
      split. apply env_consist_refl.
      split. 
      specialize (or_checked tv) as X1.
      destruct X1. constructor; try easy. inv H14; try easy.
      inv H9; try easy.
      assert ((H1,H3) = (H1,H3)) by easy. apply HRwf in H6. destruct H6.
      apply Heap.mapsto_in in H11. apply H6 in H11. lia.
      inv H14; try easy. destruct w; try easy.
      inv H18. inv H6. constructor; try easy. inv H22.
      inv H19. simpl in *.
      specialize (H23 0).
      assert (0 <= 0 < 1) by lia. apply H23 in H6.
      rewrite Z.sub_0_r in H6. simpl in *.
      rewrite Z.add_0_r in H6.
      destruct H6 as [na [ta [X1 [X2 X3]]]]. inv X1.
      apply Heap.mapsto_always_same with (v1 := (n1, t1)) in X2; try easy. inv X2.
      eapply checked_subtype_well_type; eauto. inv H16; easy.
      inv H18; try easy. inv H6; try easy.
      exists (TPtr m w). split. apply type_eq_refl. repeat constructor.
      inv H18; try easy. inv H6; try easy.
      inv H18. inv H6; try easy.
      assert (simple_type (TPtr Checked (TArray b0 b1 tv))).
      unfold simple_type in *; try easy.
      apply simple_type_array_num in H6 as eq1. destruct eq1 as [A1 A2].
      destruct A1 as [ba1 A1];subst.
      destruct A2 as [ba2 A2];subst. inv H26. inv H27.
      inv H19.
      destruct (ba2 - ba1) as [| p | ?] eqn:Hp; zify; [lia | |lia].
      rewrite replicate_length in H23.
      specialize (H23 0).
      assert (ba1 <= 0 < ba1 + Z.of_nat (Pos.to_nat p)) by lia.
      apply H23 in H9.
      destruct H9 as [na [ta [X1 [X2 X3]]]].
      symmetry in X1. apply replicate_nth in X1; subst.
      rewrite Z.add_0_r in X2.
      apply Heap.mapsto_always_same with (v1 := (n1, t1)) in X2; try easy. inv X2.
      unfold scope_set_add in *. easy.
      inv H18. inv H6; try easy.
      assert (simple_type (TPtr Checked (TNTArray b0 b1 tv))).
      unfold simple_type in *; try easy.
      apply simple_type_nt_num in H6 as eq1. destruct eq1 as [A1 A2].
      destruct A1 as [ba1 A1];subst.
      destruct A2 as [ba2 A2];subst. inv H26. inv H27.
      inv H19.
      destruct (ba2 - ba1 + 1) as [| p | ?] eqn:Hp; zify; [lia | |lia].
      rewrite replicate_length in H23.
      specialize (H23 0).
      assert (ba1 <= 0 < ba1 + Z.of_nat (Pos.to_nat p)) by lia.
      apply H23 in H9.
      destruct H9 as [na [ta [X1 [X2 X3]]]].
      symmetry in X1. apply replicate_nth in X1; subst.
      rewrite Z.add_0_r in X2.
      apply Heap.mapsto_always_same with (v1 := (n1, t1)) in X2; try easy. inv X2.
      unfold scope_set_add in *. easy.
      inv H18. inv H6; try easy. inv H22.
      apply TyLitTainted; eauto. inv H14; try easy.
      inv H14; try easy. exists tv. split. apply type_eq_refl. repeat constructor.
      assert (is_checked (TPtr Checked t0)). constructor. easy.
      destruct H; subst. inv H10. inv HTy. inv H10.
      apply eval_type_bound_idempotent with (s := s') in H17 as X1.
      inv X1. apply eval_type_bound_preserve with (t' := t') in H6; try easy; subst.
      exists env,tv.
      split; try easy.
      split; try easy.
      split; try easy.
      split. apply rheap_consistent_refl.
      split; try easy.
      split. apply env_consist_refl.
      split. inv HEwf. inv H6; try easy.
      inv H9; try easy. inv H15; try easy. inv H9.
      constructor; try easy. constructor. constructor.
      apply TyLitTainted; try easy. inv H6. intros R. inv R. easy.
      inv H15; try easy. exists tv. split. apply type_eq_refl. repeat constructor.
      destruct H; subst. inv H10. inv HTy. inv H10. easy. 
      apply eval_type_bound_idempotent with (s := s') in H15 as X1.
      inv X1. apply eval_type_bound_preserve with (t' := t') in H6; try easy; subst.
      inv H13;try easy. exists env,tv.
      split; try easy.
      split; try easy.
      split; try easy.
      split. apply rheap_consistent_refl.
      split; try easy.
      split. apply env_consist_refl.
      split. inv HEwf. inv H6. inv H13; try easy.
      inv H7. constructor; try easy. constructor. constructor.
      apply TyLitTainted; try easy. inv H6. easy. intros R. inv R. easy.
      exists tv. split. apply type_eq_refl. repeat constructor.
      destruct H. destruct H as [A1 [A2 A3]];subst.
      inv H2; try easy. inv HTy; try easy.
      inv H9. inv H5.
      apply simple_type_array_num in H14 as eq1. destruct eq1 as [B1 B2].
      destruct B1 as [ua B1];subst.
      destruct B2 as [va B2];subst. unfold eval_bound in H6, H9. inv H6. inv H9.
      assert (TPtr Checked (TArray (Num ua) (Num va) t'1)  = TPtr Checked (TArray (Num ua) (Num va) t'1)) by easy.
      apply H11 in H. inv H13; try easy.
      inv H15; try easy. apply Heap.mapsto_in in H10.
      assert ((H1,H3) = (H1,H3)) by easy. apply HRwf in H2. destruct H2. apply H2 in H10. lia.
      apply eval_type_bound_idempotent with (s := s') in H14 as X1.
      inv X1. inv H13. apply eval_type_bound_preserve with (t' := t') in H16; try easy; subst.
      exists env,tv.
      split; try easy.
      split; try easy.
      split; try easy.
      split. apply rheap_consistent_refl.
      split; try easy.
      split. apply env_consist_refl.
      split. inv H6. inv H2; try easy.
      inv H7. specialize (H18 0).
      destruct (va - ua) as [| p | ?] eqn:Hp; zify; [lia | |lia].
      rewrite replicate_length in H18.
      assert (ua <= 0 < ua + BinInt.Z.of_nat (Pos.to_nat p)) by lia.
      apply H18 in H2.
      destruct H2 as [na [ta [X1 [X2 X3]]]].
      symmetry in X1. apply replicate_nth in X1; subst.
      rewrite Z.add_0_r in X2.
      apply Heap.mapsto_always_same with (v1 := (n1, t1)) in X2; try easy. inv X2.
      unfold scope_set_add in *.
      specialize (or_checked ta) as A1. destruct A1.
      constructor; try easy.
      apply TyLitTainted; eauto.
      inv H21. inv H22. assert (ua = 0) by lia;subst. assert (va = 1) by lia ; subst.
      inv H17. constructor; try easy. constructor. constructor.
      inv H7. simpl in *. apply H18 in H.
      destruct H as [na [ta [X1 [X2 X3]]]].
      simpl in *. inv X1. rewrite Z.add_0_r in X2.
      specialize (or_checked (TPtr m w)) as A1. destruct A1.
      apply Heap.mapsto_always_same with (v1 := (n1, t1)) in X2; try easy. inv X2.
      constructor; try easy. apply TyLitTainted; try easy.
      assert (simple_type (TPtr Checked (TArray l h tv))).
      unfold simple_type in *. easy.
      apply simple_type_array_num in H2 as A1. clear H2.
      destruct A1 as [B1 B2]. destruct B1 as [la B1]; subst.
      destruct B2 as [ha B2]; subst. inv H16. inv H21. inv H7.
      destruct (ha - la) as [| p | ?] eqn:Hp; zify; [lia | |lia].
      rewrite replicate_length in H18.
      assert (la <= 0 < la + Z.of_nat (Pos.to_nat p)) by lia.
      apply H18 in H2.
      destruct H2 as [na [ta [X1 [X2 X3]]]].
      symmetry in X1. apply replicate_nth in X1; subst.
      rewrite Z.add_0_r in X2. unfold scope_set_add in *.
      apply Heap.mapsto_always_same with (v1 := (n1, t1)) in X2; try easy. inv X2.
      specialize (or_checked ta) as A1. destruct A1.
      constructor; try easy. apply TyLitTainted; eauto.
      assert (simple_type (TPtr Checked (TNTArray l h tv))).
      unfold simple_type in *. easy.
      apply simple_type_nt_num in H2 as A1. clear H2.
      destruct A1 as [B1 B2]. destruct B1 as [la B1]; subst.
      destruct B2 as [ha B2]; subst. inv H16. inv H21. inv H7.
      destruct (ha - la + 1)  as [| p | ?] eqn:Hp; zify; [lia | |lia].
      rewrite replicate_length in H18.
      assert (la <= 0 < la + Z.of_nat (Pos.to_nat p)) by lia.
      apply H18 in H2.
      destruct H2 as [na [ta [X1 [X2 X3]]]].
      symmetry in X1. apply replicate_nth in X1; subst.
      rewrite Z.add_0_r in X2. unfold scope_set_add in *.
      apply Heap.mapsto_always_same with (v1 := (n1, t1)) in X2; try easy. inv X2.
      specialize (or_checked ta) as A1. destruct A1.
      constructor; try easy. apply TyLitTainted; eauto.
      exists tv. split. apply type_eq_refl. repeat constructor.
      assert (is_checked (TPtr Checked (TArray l h t'))). constructor. easy.
      inv H9. inv HTy; try easy. inv H5.
      assert (simple_type t'). unfold simple_type in *.
      simpl in *. apply app_eq_nil in H16. destruct H16.
      apply app_eq_nil in H2. destruct H2. easy.
      apply eval_type_bound_idempotent with (s := s') in H as X1.
      apply eval_type_bound_preserve with (t' := t') in H15; try easy; subst.
      inv H14; try easy. exists env,tv.
      split; try easy.
      split; try easy.
      split; try easy.
      split. apply rheap_consistent_refl.
      split; try easy.
      split. apply env_consist_refl.
      split. inv HEwf. inv H5; try easy. inv H15; try easy.
      inv H5; try easy. inv H15. constructor; try easy. constructor. constructor.
      inv H19.
      apply TyLitTainted; try easy. intros R. inv R. easy.
      exists tv. split. apply type_eq_refl. repeat constructor.
      inv H9.
      inv HTy; try easy. inv H9. easy. inv H5.
      apply eval_type_bound_idempotent with (s := s') in H14 as X1.
      inv X1. inv H2. apply eval_type_bound_preserve with (t' := t') in H13; try easy; subst.
      inv H12; try easy.
      inv HEwf. inv H4; try easy. inv H12; try easy. inv H4; try easy.
      exists env,tv.
      split; try easy.
      split; try easy.
      split; try easy.
      split. apply rheap_consistent_refl.
      split; try easy.
      split. apply env_consist_refl.
      split. inv H12. constructor;try easy. constructor. constructor.
      inv H17; try easy.
      apply TyLitTainted; eauto. intros R. inv R. easy.
      unfold simple_type in *.
      simpl in *. apply app_eq_nil in H14. destruct H14.
      apply app_eq_nil in H2. destruct H2. easy.
      exists tv. split. apply type_eq_refl. repeat constructor.
      destruct H as [X1 [X2 X3]];subst.
      inv H2; try easy. inv HTy; try easy. inv H9. inv H5.
      apply eval_type_bound_idempotent with (s := s') in H14 as X1.
      inv X1. inv H2.
      apply eval_type_bound_preserve with (t' := t') in H16; try easy; subst.
      apply simple_type_nt_num in H14 as X1. destruct X1 as [A1 A2].
      destruct A1 as [ua A1];subst. destruct A2 as [va A2];subst.
      inv H13; try easy.
      exists env,tv.
      split; try easy.
      split; try easy.
      split; try easy.
      split. apply rheap_consistent_refl.
      split; try easy.
      split. apply env_consist_refl.
      split. 
      specialize (or_checked tv) as A1.
      destruct A1. inv X2. constructor; try easy.
      constructor. inv H15; try easy.
      apply Heap.mapsto_in in H10. 
      assert ((H1, H3) = (H1, H3)) by easy. apply HRwf in H2. destruct H2.
      apply H2 in H10. lia. unfold eval_bound in H6, H9. inv H6. inv H9.
      assert (TPtr Checked (TNTArray (Num ua) (Num va) (TPtr m w))
        = TPtr Checked (TNTArray (Num ua) (Num va) (TPtr m w))) by easy.
      apply H12 in H2.
      inv H7. inv H6; try easy. inv H13.
      specialize (H22 0).
      destruct (va - ua + 1)  as [| p | ?] eqn:Hp; zify; [lia | |lia].
      rewrite replicate_length in H22.
      assert (ua <= 0 < ua + Z.of_nat (Pos.to_nat p)) by lia.
      apply H22 in H6.
      destruct H6 as [na [ta [A1 [A2 A3]]]].
      symmetry in A1. apply replicate_nth in A1; subst.
      rewrite Z.add_0_r in A2. unfold scope_set_add in *.
      apply Heap.mapsto_always_same with (v1 := (n1, t1)) in A2; try easy. inv A2.
      constructor; try easy.
      assert (simple_type (TPtr Checked (TNTArray l h (TPtr m w)))).
      unfold simple_type in *. easy.
      apply simple_type_nt_num in H6. destruct H6 as [A1 A2]. destruct A1 as [ub A1];subst.
      destruct A2 as [vb A2];subst.
      inv H18. inv H24. inv H13.
      specialize (H22 0).
      destruct (vb - ub + 1)  as [| p | ?] eqn:Hp; zify; [lia | |lia].
      rewrite replicate_length in H22.
      assert (ub <= 0 < ub + Z.of_nat (Pos.to_nat p)) by lia.
      apply H22 in H6.
      destruct H6 as [na [ta [A1 [A2 A3]]]].
      symmetry in A1. apply replicate_nth in A1; subst.
      rewrite Z.add_0_r in A2. unfold scope_set_add in *.
      apply Heap.mapsto_always_same with (v1 := (n1, t1)) in A2; try easy. inv A2.
      constructor; try easy.
      apply TyLitTainted; eauto.
      exists tv. split. apply type_eq_refl. repeat constructor.
      assert (is_checked (TPtr Checked (TNTArray l h t'))). constructor. easy.
      inv HTy; try easy. inv H9. inv H5.
      apply eval_type_bound_idempotent with (s := s') in H16 as X1.
      inv X1. inv H2.
      apply eval_type_bound_preserve with (t' := t') in H15; try easy; subst.
      inv H14; try easy.
      exists env,tv.
      split; try easy.
      split; try easy.
      split; try easy.
      split. apply rheap_consistent_refl.
      split; try easy.
      split. apply env_consist_refl.
      split. inv X2. constructor; try easy. constructor. constructor.
      inv HEwf; try easy. inv H4; try easy.
      inv H14; try easy. inv H4; try easy.
      apply TyLitTainted; try easy.
      intros R. inv R. inv H19. easy.
      unfold simple_type in *. simpl in *.
      apply app_eq_nil in H16. destruct H16. apply app_eq_nil in H2. destruct H2. easy.
      exists tv. split. apply type_eq_refl. repeat constructor.
      inv HEwf. inv H4; try easy. inv H7; try easy. inv H9.
      inv HTy; try easy. inv H7.
      apply eval_type_bound_idempotent with (s := s') in H16 as X1.
      inv X1. inv H2.
      apply eval_type_bound_preserve with (t' := t') in H18; try easy; subst.
      inv H12; try easy.
      exists env,tv.
      split; try easy.
      split; try easy.
      split; try easy.
      split. apply rheap_consistent_refl.
      split; try easy.
      split. apply env_consist_refl.
      split. inv X2. constructor; try easy. constructor. constructor.
      apply TyLitTainted; try easy. intros R. inv R.
      inv H15. easy. unfold simple_type in *. simpl in *.
      apply app_eq_nil in H8. destruct H8. apply app_eq_nil in H2. destruct H2. easy.
      exists tv. split. apply type_eq_refl. repeat constructor.
      apply eval_type_bound_idempotent with (s := s') in H8 as X1.
      inv X1. inv H2. inv H7.
      apply eval_type_bound_preserve with (t' := t') in H18; try easy; subst.
      inv H12; try easy. exists env,tv.
      split; try easy.
      split; try easy.
      split; try easy.
      split. apply rheap_consistent_refl.
      split; try easy.
      split. apply env_consist_refl.
      split. inv X2. constructor; try easy. constructor. constructor.
      apply TyLitTainted; try easy.
      intros R. inv R. inv H4. inv H13. easy. easy.
      unfold simple_type in *. simpl in *.
      apply app_eq_nil in H8. destruct H8. apply app_eq_nil in H2. destruct H2. easy.
      exists tv. split. apply type_eq_refl. repeat constructor.
      inv HEwf. specialize (IH H3 Henvt s).
      edestruct IH; eauto.
      apply step_implies_reduces_1 with (cm := m) (m := Checked) (E := E) in H2; try easy.
      apply H2.
      destruct H0 as [ta [X1 [X2 [X3 [X4 [X5 [X6 [X7 X8]]]]]]]].
      destruct HPtrType. destruct H0; subst.
      apply eq_subtype_ptr_form in X8 as X9; try easy.
      destruct X9 as [tb [A1 A2]].
      exists x,tb.
      split; try easy.
      split; try easy.
      split; try easy.
      split; try easy.
      split; try easy.
      split; try easy.
      split.
      destruct A2;subst.
      apply TyDeref with (m' := m') (t := (TPtr m' tb)) (l := Num 0) (h := Num 0); try easy.
      left. split. eapply type_eq_word; eauto. easy.
      destruct H1. destruct H1 as [ua [va [B1 [B2 B3]]]];subst.
      apply TyDeref with (m' := m') (t := (TPtr m' (TArray ua va tb))) (l := ua) (h := va); try easy.
      right. left. split. easy. split. eapply type_eq_word; eauto. easy.
      
  Abort.
 

(*

    (* T-Deref *) 
    - destruct m'; try (specialize (HMode eq_refl); inversion HMode).
      clear HMode.
      inv HHwf.
      specialize (IH H1 eq_refl).
      inv Hreduces.
      destruct E eqn:He; inversion H2; simpl in *; try congruence.
      + 
        subst.
        clear IH.
        inv H5.
        split; eauto.
        destruct HPtrType as [[Hw Eq] | Hw]; subst.
        *   inv HSubType.  
           ** { inv HTy.
              remember H7 as Backup; clear HeqBackup.
              inv H7.
             - exfalso.
              eapply heap_wf_maps_nonzero; eauto.
             - inv H2.
              
             - inv Hw; simpl in*; subst; simpl in *.
              + inv H0; simpl in *.
                destruct (H5 0) as [N [T' [HT' [HM' HWT']]]]; [inv H2; simpl; omega | ].
               
                inv HT'.
                rewrite Z.add_0_r in HM'.
                assert (Hyp: (N, TNat) = (n1, t1)). {
                eapply HeapFacts.MapsTo_fun. inv H2. inv H0.
                exact HM'. exact H9. }
                inv Hyp; subst; eauto.
              + inv H0; simpl in *.
                destruct (H5 0) as [N [T' [HT' [HM' HWT']]]]; [inv H2; simpl; omega | ].
                inv HT'.
                rewrite Z.add_0_r in HM'.
                assert (Hyp: (N, TPtr m w) = (n1, t1)). {
                  eapply HeapFacts.MapsTo_fun. inv H2.
                  inv H0. exact HM'. exact H9. }
                inv Hyp; subst; eauto.
                apply TyLit.
  
                assert (Hyp: set_remove_all (n, TPtr Checked (TPtr m w))
                                       ((n,TPtr Checked (TPtr m w))::nil) = empty_scope).
                { 
                  destruct (eq_dec_nt (n, TPtr Checked (TPtr m w)) (n, TPtr Checked (TPtr m w))) eqn:EQ; try congruence.
                  unfold set_remove_all.
                  rewrite EQ.
                  auto.
                }
  
                rewrite <- Hyp.
                apply scope_strengthening. inv H2. inv H0.
                exact HWT'. exact HEwf. exact Backup.
              }
             ** { inv HTy.
                remember H10 as Backup; clear HeqBackup.
                inv H10.
                - exfalso.
                  eapply heap_wf_maps_nonzero; eauto.
                - inv H2.
              
                - inv Hw; simpl in*; subst; simpl in *.
              
                }
            ** { inv HTy.
                 remember H12 as Backup; clear HeqBackup.
                 inv H12.
                 - exfalso.
                   eapply heap_wf_maps_nonzero; eauto.
                 - inv H2.
              
                 - inv Hw; simpl in*; subst; simpl in *.
                   + inv H0; simpl in *.
                     destruct (H10 0) as [N [T' [HT' [HM' HWT']]]]; [inv H2; simpl; eauto | ].
                     destruct (StructDef.find (elt:=fields) T D) eqn:H.
                     inv H0. rewrite map_length. 
                     assert (StructDef.MapsTo T f D) by (eapply find_implies_mapsto; eauto).
                     assert (f = fs) by (eapply StructDefFacts.MapsTo_fun; eauto). rewrite <- H2 in *.
                     assert (((length (Fields.elements (elt:=type) f)) > 0)%nat) by (eapply fields_implies_length; eauto).
                     omega. inv H. inv H0.
                     inv HT'.
                     rewrite Z.add_0_r in HM'.
                     assert (Hb : b = 0). 
                     {
                       destruct (StructDef.find (elt:=fields) T D);
                        inv H2. reflexivity.
                     } rewrite Hb in *.
                     simpl in H0. 
                     assert (Hts : StructDef.find (elt:=fields) T D = Some fs) by (eapply StructDef.find_1; eauto).
                     rewrite Hts in H2. inv H2.
                     assert (Some TNat = match map snd (Fields.elements (elt := type) fs)
                      with 
                      | nil => None
                      | x:: _ => Some x
                            end) by (eapply element_implies_element; eauto).
                      rewrite <- H in H0. inv H0. 
                      assert (Hyp: (N, TNat) = (n1, t1)). {
                      eapply HeapFacts.MapsTo_fun.
                      exact HM'. exact H9. }
                      inv Hyp; subst; eauto.
                  }
        *   assert (exists t1, w = (TPtr Checked t1)) by (inv HSubType; eauto).
            destruct H. rewrite H in *. clear H.
          { inv HTy.
            clear H8.
            clear H0.
            clear H1.
            remember H7 as Backup; clear HeqBackup.
            inv H7.
            - exfalso. 
              eapply heap_wf_maps_nonzero; eauto.
            - inversion H0.
            - destruct Hw as [? [? ?]]; subst.
              inv H0; simpl in *.
              inv HSubType.
              -- unfold allocate_meta in H4.
                 destruct (H11 l h t). reflexivity.
                 assert (Hpos : exists p, (h - l) = Z.pos p).
                  {
                     destruct h; destruct l; inv H.
                     + exists p. simpl; reflexivity.
                     + exfalso. eapply H0. simpl. reflexivity.
                     + assert (Z.pos p - Z.neg p0 > 0) by (zify; omega).
                       assert (exists p2, Z.pos p - Z.neg p0 = Z.pos p2).
                       {
                        destruct (Z.pos p - Z.neg p0); inv H. exists p1. reflexivity.
                       } destruct H5. exists x. assumption.
                  }
                  destruct Hpos. rewrite H5 in *. simpl in H4. 
                  inv H4; simpl in *. 
                  assert (exists p, h = Z.pos p).
                  {
                    destruct h; inv H. exists p; reflexivity.
                  }
                  destruct H4. destruct l.
                  * assert (Hpos : exists n, Pos.to_nat x = S n) by apply pos_succ.
                    destruct Hpos.
                    destruct (H3 0) as [N [T' [HT' [HM' HWT']]]]; [ simpl; rewrite H7; simpl; zify; omega  | ].
                    rewrite H7 in HT'.  simpl in HT'. inv HT'.  rewrite Z.add_0_r in HM'.
                    maps_to_fun.
                    constructor.
                    assert (Hyp: set_remove_all (n, TPtr Checked (TArray 0 (Z.pos x0) t))
                                          ((n,TPtr Checked (TArray 0 (Z.pos x0) t))::nil) = empty_scope).
                      { 
                        destruct (eq_dec_nt (n, TPtr Checked (TArray 0 (Z.pos x0) t))
                                      (n, TPtr Checked (TArray 0 (Z.pos x0) t))) eqn:EQ; try congruence.
                        unfold set_remove_all.
                        rewrite EQ.
                        auto.
                      }
                    rewrite <- Hyp.
                    apply scope_strengthening; eauto.
                  * exfalso; eapply H0; eauto.
                  * assert (Hpos : exists n, Pos.to_nat x = S n) by apply pos_succ.
                    destruct Hpos. rewrite H4 in *.  clear H4 H0 H.
                    destruct (H3 0) as [N [T' [HT' [HM' HWT']]]]; [ rewrite H7; rewrite replicate_length; zify; omega | ].
                    rewrite H7 in HT'.
                    rewrite Z.add_0_r in HM'.
                    symmetry in HT'.
                     assert (t = T').
                     { 
                       eapply replicate_nth; eauto.
                     } 
                     subst T'.
                    maps_to_fun.
                     econstructor.
                     assert (Hyp: set_remove_all (n, TPtr Checked (TArray (Z.neg p) (Z.pos x0) t))
                                          ((n,TPtr Checked (TArray (Z.neg p) (Z.pos x0) t))::nil) = empty_scope).
                          { 
                            destruct (eq_dec_nt (n, TPtr Checked (TArray (Z.neg p) (Z.pos x0) t))
                                          (n, TPtr Checked (TArray (Z.neg p) (Z.pos x0) t))) eqn:EQ; try congruence.
                            unfold set_remove_all.
                            rewrite EQ.
                            auto.
                          }
  
                        rewrite <- Hyp.
                        apply scope_strengthening; eauto.
              -- unfold allocate_meta in H4.
                 destruct (H11 l0 h0 t). reflexivity.
                 clear H0.
                 assert (Hpos : exists p, (h0 - l0) = Z.pos p).
                  {
                     destruct h0; destruct l0; inv H.
                     + exists p. simpl; reflexivity.
                     + exfalso. eapply H5. simpl. reflexivity.
                     + assert (Z.pos p - Z.neg p0 > 0) by (zify; omega).
                       assert (exists p2, Z.pos p - Z.neg p0 = Z.pos p2).
                       {
                        destruct (Z.pos p - Z.neg p0); inv H. exists p1. reflexivity.
                       } destruct H0. exists x. assumption.
                  }
                  destruct Hpos. rewrite H0 in *. simpl in H4. 
                  inv H4; simpl in *. 
                  assert (exists p, h0 = Z.pos p).
                  {
                    destruct h0; inv H. exists p; reflexivity.
                  }
                  destruct H4. destruct l0.
                  * assert (Hpos : exists n, Pos.to_nat x = S n) by apply pos_succ.
                    destruct Hpos.
                    destruct (H3 0) as [N [T' [HT' [HM' HWT']]]]; [ simpl; rewrite H7; simpl; zify; omega  | ].
                    rewrite H7 in HT'.  simpl in HT'. inv HT'.  rewrite Z.add_0_r in HM'.
                    maps_to_fun.
                    constructor.
                    assert (Hyp: set_remove_all (n, TPtr Checked (TArray 0 (Z.pos x0) t))
                                          ((n,TPtr Checked (TArray 0 (Z.pos x0) t))::nil) = empty_scope).
                      { 
                        destruct (eq_dec_nt (n, TPtr Checked (TArray 0 (Z.pos x0) t))
                                      (n, TPtr Checked (TArray 0 (Z.pos x0) t))) eqn:EQ; try congruence.
                        unfold set_remove_all.
                        rewrite EQ.
                        auto.
                      }
                    rewrite <- Hyp.
                    apply scope_strengthening; eauto.
                  * exfalso; eapply H5; eauto.
                  * assert (Hpos : exists n, Pos.to_nat x = S n) by apply pos_succ.
                    destruct Hpos. rewrite H4 in *.
                    destruct (H3 0) as [N [T' [HT' [HM' HWT']]]]; [ rewrite H7; rewrite replicate_length; zify; omega | ].
                    rewrite H7 in HT'.
                    rewrite Z.add_0_r in HM'.
                    symmetry in HT'.
                     assert (t = T').
                     { 
                       eapply replicate_nth; eauto.
                     } 
                     subst T'.
                    maps_to_fun.
                     econstructor.
                     assert (Hyp: set_remove_all (n, TPtr Checked (TArray (Z.neg p) (Z.pos x0) t))
                                          ((n,TPtr Checked (TArray (Z.neg p) (Z.pos x0) t))::nil) = empty_scope).
                          { 
                            destruct (eq_dec_nt (n, TPtr Checked (TArray (Z.neg p) (Z.pos x0) t))
                                          (n, TPtr Checked (TArray (Z.neg p) (Z.pos x0) t))) eqn:EQ; try congruence.
                            unfold set_remove_all.
                            rewrite EQ.
                            auto.
                          }
  
                        rewrite <- Hyp.
                        apply scope_strengthening; eauto.
            }
  
      + subst.
        destruct (IH (in_hole e'0 c) H') as [HC HWT]; eauto. 
    - inv HHwf.
  
      assert (exists l0 h0, t = (TPtr m' (TArray l0 h0 t'))).
      {
        inv HSubType. exists l. exists h. reflexivity.
        exists l0. exists h0. reflexivity. 
      }
  
      destruct H0 as [l0 [h0 Hb]].
      rewrite Hb in *. clear Hb HSubType.
      (* TODO: Move outside, cleanup *)
      Ltac invert_expr_wf e :=
        match goal with
        | [ H : expr_wf _ e |- _ ] => inv H
        end.
  
      invert_expr_wf (EPlus e1 e2).
      inv Hreduces.
  
      Ltac invert_ctx_and_hole :=
        match goal with
        | [H : in_hole _ ?C = _ |- _] => destruct C; inversion H; simpl in *; subst; clear H
        end.
  
      invert_ctx_and_hole.
  
      + inv H6. (*TODO: auto *)
      + invert_ctx_and_hole.
        * { (* Plus step *)
            match goal with
            | [ H : step _ _ _ _ _ |- _ ] => inv H
            end; split; eauto...
            - inv HTy1.
              eapply TyDeref; eauto.
              constructor.
  
              Ltac cleanup :=
                repeat (match goal with
                        | [H : ?X =  ?X |- _ ] => clear H
                        | [H : ?X -> ?X |- _ ] => clear H
                        end).
              cleanup.
              
              match goal with
              | [ H : well_typed_lit _ _ _ _ _ |- _ ] =>
                remember H as Backup; clear HeqBackup; inv H; eauto; try omega
              end.
  
              unfold allocate_meta in *.
  
              inversion H0; subst b; subst ts; clear H0.
              
              eapply TyLitC; unfold allocate_meta in *; eauto.
  
              intros k Hk.
              
              assert (Hyp: h0 - n2 - (l0 - n2) = h0 - l0) by omega.
              rewrite Hyp in * ; clear Hyp.
              
              destruct (H6 (n2 + k)) as [n' [t'' [HNth [HMap HWT]]]]; [inv H0; omega | ].
  
              exists n'. exists t''.
  
              rewrite Z.add_assoc in HMap.
              inv H0.
              split; [ | split]; auto.
              + destruct (h0 - l0) eqn:HHL; simpl in *.
                * rewrite Z.add_0_r in Hk.
                  destruct (Z.to_nat (n2 + k - l0)); inv HNth.
                * assert (HR: k - (l0 - n2) = n2 + k - l0) by (zify; omega).
                  rewrite HR.
                  auto.
                * destruct (Z.to_nat (n2 + k - l0)); inv HNth.
              + apply scope_weakening_cons.
  
                eapply scope_strengthening in HWT; eauto.
                assert (HAdd : set_add eq_dec_nt (n1, TPtr Checked (TArray l0 h0 t'))
                                       empty_scope =
                               (n1, TPtr Checked (TArray l0 h0 t')) :: nil) by auto.
                rewrite HAdd in HWT.
                clear HAdd.
  
                assert (HEmpty : empty_scope =
                                 set_remove_all (n1, TPtr Checked (TArray l0 h0 t')) 
                                               ((n1, TPtr Checked (TArray l0 h0 t')) :: nil)).
                {
                  unfold set_remove_all.
                  destruct (eq_dec_nt (n1, TPtr Checked (TArray l0 h0 t'))
                                      (n1, TPtr Checked (TArray l0 h0 t'))); auto.
                  congruence.
                }
                rewrite <- HEmpty in HWT.
                auto.
              + eapply SubTyRefl.
            - inv HTy1.
              destruct m'.
              + exfalso; eapply H10; eauto.
              + specialize (HMode eq_refl). inv HMode.
          }
        * clear l h t. 
          specialize (IH1 H3 eq_refl).
          specialize (IH1 (in_hole e'0 E) H').
          destruct IH1 as [HC HWT]; eauto.
          split; eauto. eapply TyIndex; eauto.
          eapply SubTyRefl. eauto...
        * specialize (IH2 H4 eq_refl (in_hole e'0 E) H').
          destruct IH2 as [HC HWT]; eauto.
          split; eauto. eapply TyIndex; eauto...
          eapply SubTyRefl.
    (* T-Assign *)
    - inv Hreduces.
      inv HHwf.
      destruct E; inversion H4; simpl in *; subst.
      + clear H10 H3.
        inv H7.
        inv Hwt2.
        inv Hwt1.
        destruct H1 as [[HW Eq] | Eq]; subst.
        * {
            destruct m'; [| specialize (H2 eq_refl); inv H2].
            inv H0.
            **
              eapply well_typed_heap_in in H11; eauto.
              destruct H11 as [N HMap].
              split.
              - apply HeapUpd with (n := N); eauto...
                eapply PtrUpd; eauto.
              - constructor.
                eapply PtrUpd; eauto. 
            **
              eapply well_typed_heap_in in H11; eauto.
              destruct H11 as [N HMap].
              split.
              - apply HeapUpd with (n := N); eauto...
                eapply PtrUpd; eauto.
              - constructor.
                eapply PtrUpd; eauto. 
              - eapply subtype_well_type;
                eauto. eapply SubTySubsume; eauto.
            **
              eapply well_typed_heap_in in H11. eauto.
              destruct H11 as [N HMap].
              split; eauto.
              - apply HeapUpd with (n := N); eauto...
              - eauto.
              - eauto.
              - eapply subtype_well_type;
                eauto. eapply SubTyStructArrayField; eauto.
          } 
        * destruct Eq as [? [? ?]]; subst.
          inv H0. 
          ** 
            { destruct m'; [| specialize (H2 eq_refl); inv H2].
              eapply (well_typed_heap_in_array n D H l h) in H11; eauto.
              destruct H11 as [N HMap].
              split.
              - apply HeapUpd with (n := N); eauto...
                eapply PtrUpd; eauto.
              - constructor.
                eapply PtrUpd; eauto.
              - eapply (H13 l h). eauto.
              - eapply H13. eauto.
            }
          ** 
            { clear H7. clear l h.
              destruct m'; [| specialize (H2 eq_refl); inv H2].
              eapply (well_typed_heap_in_array n D H l0 h0) in H11; eauto.
              destruct H11 as [N HMap].
              split.
              - apply HeapUpd with (n := N); eauto...
                eapply PtrUpd; eauto.
              - constructor.
                eapply PtrUpd; eauto.
              - eapply (H13 l0 h0). eauto.
              - eapply H13. eauto.
            }
      + destruct (IHHwt1 H6 eq_refl (in_hole e'0 E) H') as [HC HWT]; eauto.
        split; eauto...
      + destruct (IHHwt2 H8 eq_refl (in_hole e'0 E) H') as [HC HWT]; eauto.
        split; eauto... 
    - inv Hreduces.
      inv HHwf.
      inv H7.
      destruct E; inv H5; subst; simpl in*; subst; eauto.
      + inv H8.
      + assert (exists l0 h0, t = (TPtr m' (TArray l0 h0 t'))).
        {
          inv H2. exists l. exists h. reflexivity.
          exists l0. exists h0. reflexivity. 
        }
        destruct H4 as [l0 [h0 H4]].
        rewrite H4 in *. clear H4 H2.
        destruct E; inversion H6; simpl in *; subst.
        * { (* Plus step *)
            inv H8; split; eauto...
            - inv Hwt1.
              eapply TyAssign; eauto.
              constructor.
              cleanup.
              
              match goal with
              | [ H : well_typed_lit _ _ _ _ _ |- _ ] =>
                remember H as Backup; clear HeqBackup; inv H; eauto; try omega
              end.
  
              unfold allocate_meta in *.
  
              inversion H2; subst b; subst ts; clear H0.
              
              eapply TyLitC; unfold allocate_meta in *; eauto.
  
              intros k Hk.
              
              assert (Hyp: h0 - n2 - (l0 - n2) = h0 - l0) by omega.
              rewrite Hyp in * ; clear Hyp.
              inv H2.
              destruct (H5 (n2 + k)) as [n' [t0 [HNth [HMap HWT]]]]; [omega | ].
  
              exists n'. exists t0.
  
              rewrite Z.add_assoc in HMap.
  
              split; [ | split]; eauto.
              + destruct (h0 - l0) eqn:HHL; simpl in *.
                * rewrite Z.add_0_r in Hk.
                  destruct (Z.to_nat (n2 + k - l0)); inv HNth.
                * assert (HR: k - (l0 - n2) = n2 + k - l0) by (zify; omega).
                  rewrite HR.
                  auto.
                * destruct (Z.to_nat (n2 + k - l0)); inv HNth.
              + apply scope_weakening_cons.
  
                eapply scope_strengthening in HWT; eauto.
                assert (HAdd : set_add eq_dec_nt (n1, TPtr Checked (TArray l0 h0 t'))
                                       empty_scope =
                               (n1, TPtr Checked (TArray l0 h0 t')) :: nil) by auto.
                rewrite HAdd in HWT.
                clear HAdd.
  
                assert (HEmpty : empty_scope =
                                 set_remove_all (n1, TPtr Checked (TArray l0 h0 t')) 
                                               ((n1, TPtr Checked (TArray l0 h0 t')) :: nil)).
                {
                  unfold set_remove_all.
                  destruct (eq_dec_nt (n1, TPtr Checked (TArray l0 h0 t'))
                                      (n1, TPtr Checked (TArray l0 h0 t'))); auto.
                  congruence.
                }
                rewrite <- HEmpty in HWT.
                auto.
              + eapply SubTyRefl; eauto.
            - inv Hwt1.
              destruct m'.
              + exfalso; eapply H14; eauto.
              + specialize (H3 eq_refl). exfalso; inv H3.
                
           }
        * destruct (IHHwt1 H10 eq_refl (in_hole e'0 E) H') as [HC HWT]; eauto.
          split. eauto. eapply TyIndexAssign; eauto.
          eapply SubTyRefl. eauto... eauto... 
        * destruct (IHHwt2 H12 eq_refl (in_hole e'0 E) H') as [HC HWT]; eauto.
          split; eauto. eapply TyIndexAssign; eauto... eapply SubTyRefl.
  Qed.
*)

Section Noncrash. 
  Variable D : structdef.
  Variable F : FEnv.
  Hypothesis HDwf : structdef_wf D.

Definition normal (M : mem) (e : expression) : Prop :=
  ~ exists m' M' r, @reduce D F M e m' M' r.

Definition stuck (M : mem) (r : result) : Prop :=
  match r with
  | RBounds => False
  | RNull => False
  | RExpr e => @normal M e /\ ~ value D e
  end.

Inductive eval: mem -> expression -> mode -> mem -> result -> Prop :=
  | eval_refl   : forall M e m, eval M e m M (RExpr e)
  | eval_transC : forall m M M' M'' e e' r,
      eval M e m M' (RExpr e') ->
      @reduce D F M' e' Checked M'' r ->
      eval M e Checked M'' r
  | eval_transU : forall m M M' M'' e e' r,
      eval M e m M' (RExpr e') ->
      @reduce D F M' e' Unchecked M'' r ->
      eval M e Unchecked M'' r.

Theorem noncrash : forall S Q R e t m S' R' r,
    rheap_wf R ->
    @rheap_wt_all D F Q R ->
    @fun_wf D F R ->
    stack_wt D m S ->
    @expr_wf D e ->
    @well_typed D F R empty_env empty_theta Checked e t ->
    @eval (S,R) e m (S',R') r ->
    ~ @stuck (S',R') r.
Proof.
Admitted.

End Noncrash.

  
