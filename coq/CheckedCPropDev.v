From CHKC Require Import
  Coqlib
  Tactics
  ListUtil
  Map
  MapS
  CheckedCDef
  CheckedCProp.


Section FunctionProp.
  Variable D : structdef.
  Variable Q : theta.
  Variable m : mode.

  Definition stack_consistent_grow (S S' : stack) (env : env) := 
    forall x v t,
      Env.In x env ->
      sub_domain env S ->
      Stack.MapsTo x (v,t) S ->
      Stack.MapsTo x (v,t) S'.

  (* Lemma eval_el_same_length : forall AS S tvl es S', *)
  (*     eval_el AS S tvl es S' -> length es = length tvl. *)
  (* Proof. *)
  (*   intros * H. induction H; cbn; auto. *)
  (* Qed. *)
  

  (* what's in the arguments will not affact what was in the stack
     Q: why is this useful?
   *)
  Lemma stack_env_irrelavent_grow : forall S S' env tvl es e e',
      (forall x t, In (x, t) tvl -> ~ Env.In x env) ->
      eval_el S es tvl e e' -> stack_consistent_grow S S' env.
  Proof.
  Abort.
  (*   intros * Hnotin Hel x v t Henv Hsubdom Hmap. *)
  (*   induction Hel. 2: assumption. *)
  (*   destruct (Nat.eq_dec x0 x).  *)
  (*   { subst. specialize (Hnotin x t0 (in_eq _ tvl)) as Contra. *)
  (*     destruct (Contra Henv). } *)
  (*   apply Stack.add_2; [exact n0 | apply IHHel]; auto. *)
  (*   intros. apply (Hnotin x1 t1). unfold In. right. assumption. *)
  (* Qed. *)
  
  (* Q: what's the purpose of reasoning about the length *)
  Lemma well_typed_arg_same_length : forall R env AS es tvl,
      @well_typed_args D fenv Q R env AS es tvl -> length es = length tvl.
  Proof.
    intros * H. induction H; cbn; auto.
  Qed.


  Lemma stack_wf_core : forall D Q env S,
      stack_wf D Q env S ->
      (forall x n t ta,
          Env.MapsTo x t env ->
          Stack.MapsTo x (n,ta) S ->
          (exists t',
              eval_type_bound S t = Some t' /\ subtype D Q ta t')).
  Proof.
    intros.
    unfold stack_wf in *.
    specialize (H x t H0).
    destruct H as [v [t' [t'' [X1 [X2 X3]]]]].
    exists t'. split. assumption.
    apply Stack.mapsto_always_same with (v1 := (v,t'')) in H1; try easy. inv H1.
    assumption.
  Qed.


  Lemma stack_find_none : forall x S,
      Stack.find x S = None ->
      (forall (t : Z * type), ~ @Stack.In (Z * type) x S).
  Proof.
    intros.
    unfold not.
    intros.
    unfold Stack.In, Stack.Raw.PX.In in *.
    destruct H0 as [e Contra].
    apply Stack.find_1 in Contra.
    congruence.
  Qed.



  Lemma same_eval_bound_in_consistent_stack : forall env S S' l, 
      well_bound_in env l -> 
      sub_domain env S ->
      stack_consistent_grow S S' env ->
      eval_bound S l = eval_bound S' l.
  Proof with auto.
    intros * Hwb. inv Hwb; intros Hdom Hgrow...
    assert (Env.In x env) as Hin by solveMaps.
    unfold stack_consistent_grow in Hgrow.
    cbn. 
    destruct (Stack.find (elt:=Z * type) x S) eqn: Efind.
    + apply Stack.find_2 in Efind. destruct p.
      specialize (Hgrow x z t Hin Hdom Efind).
      apply Stack.find_1 in Hgrow. rewrite Hgrow...
    + specialize (Hdom _ Hin).
      eapply stack_find_none in Efind.
      congruence. intuition. constructor.
  Qed.
  

  Lemma stack_grow_eval_type_same : forall env S S' t,
      well_type_bound_in env t ->
      sub_domain env S ->
      stack_consistent_grow S S' env ->
      forall t',
        eval_type_bound S t = Some t' ->
        eval_type_bound S' t = Some t'.
  Proof with auto.
    Ltac solveIH :=
      match goal with
      | [H : forall t : type, Some ?t1 = Some t -> _ |- _ ] =>
          specialize (H t1 eq_refl)
      end; invOpt.
    intros * Hwt Hsub Hgrow. induction Hwt; intros t' Hev;
      try solve [cbn in *; auto]; specialize (IHHwt Hsub Hgrow).
    - cbn in *. solveopt2; solveIH.
    - cbn in *. solveopt2; solveIH.
      rewrite (same_eval_bound_in_consistent_stack env S S')...
      rewrite (same_eval_bound_in_consistent_stack env S S')...
    - cbn in *. solveopt2; solveIH.
      rewrite (same_eval_bound_in_consistent_stack env S S')...
      rewrite (same_eval_bound_in_consistent_stack env S S')...
    - cbn in *.
      solveopt2;
        pose proof
          ((same_eval_bound_in_consistent_stack env S S') b H Hsub Hgrow)
        as Heq; [idtac | congruence].
      rewrite -> Hev, -> Hev0 in Heq. inv Heq. 
      solveopt in H3. rewrite (IHHwt t0 eq_refl).
      (* now let's reason about fold_right *)
      rewrite H5.
      match goal with
      | [H : match ?P with _ => _ end = _ |- match ?R with _ => _ end = _] =>
          assert (P = R) as Heq
      end.
      {
        generalize dependent t'.
        induction ts; intros; cbn...
        solveopt in H5. cbn in H3. solveopt in H3. 
        mopo IHts.
        {intros. apply in_cons with (a := a) in H3.  apply H0 in H3... }
        mopo IHts by intuition.
        erewrite <- IHts by eauto. 
        solveopt in H6. erewrite (H1 a (in_eq _ _)); eauto.
      }
      by rewrite Heq in H5.
  Qed.


  (* Stack-wellformness for parameter varaibles that's not in current
     env/stack.
   *)
  
  Fixpoint list_map_uniq {X Y} (l : list (X * Y)) : Prop :=
    match l with
    | [] => True
    | (a, _) :: t =>
      (forall b, ~ In (a, b) l) /\ list_map_uniq t
    end.

(*
  Lemma in_eval_el : forall  S S' tvl es AS,
      list_map_uniq tvl -> 
      eval_el AS S tvl es S' ->
      forall x t,
        In (x,t) tvl ->
        exists t' v,
          eval_type_bound S (subst_type AS t) = Some t' /\
            Stack.MapsTo x (v, t') S'.
  Proof.
    intros * Huniq Hel. induction Hel; intros * Hin. destruct Hin.
    destruct Hin as [[=] | Hin]; subst. 
    - inv H; exists t', n; intuition; by apply (Stack.add_1).
    - destruct Huniq as [Hnin Huniq].
      destruct (IHHel Huniq _ _ Hin) as (t'' & v'' & Hetb & Hstk).
      exists t'', v''. intuition.
      destruct (Nat.eq_dec x0 x); subst.
      + destruct (Hnin t (in_eq _ _)). 
      + apply Stack.add_2; auto.
  Qed.
 *)

  Lemma in_eval_el : forall  S S' tvl es AS,
      list_map_uniq tvl -> 
      eval_el AS S tvl es S' ->
      get_dept_map tvl es = Some AS ->
      forall x t,
        In (x,t) tvl ->
        exists t' t'' v,
          eval_type_bound S (subst_type AS t) = Some t' /\
            Stack.MapsTo x (v, t') S' /\
            eval_type_bound S' t = Some t'' /\
            subtype D Q t' t''.
  Proof.
    intros * Huniq Hel. induction Hel; intros Hdept * Hin. destruct Hin.
    destruct Hin as [[=] | Hin]; subst. 
    - inv H; exists t', t', n; intuition.
      + by apply (Stack.add_1).
      +
    - destruct Huniq as [Hnin Huniq].
      destruct (IHHel Huniq _ _ Hin) as (t'' & v'' & Hetb & Hstk).
      exists t'', v''. intuition.
      destruct (Nat.eq_dec x0 x); subst.
      + destruct (Hnin t (in_eq _ _)). 
      + apply Stack.add_2; auto.
  Qed.

  (* Why is this called [trans]? Appearantly, it's more of growing. *)
  Lemma stack_wf_grow :
    forall R env env' S S' AS tvl es ts,
      stack_wt D m S ->
      sub_domain env S -> stack_wf D Q env S ->
      stack_rheap_consistent D fenv Q R S ->
      env_wt D m env ->
      (forall a, In a tvl -> ~ Env.In (fst a) env) ->
      list_map_uniq tvl ->
      (forall x t,
          Env.MapsTo x t env' ->
          Env.MapsTo x t env \/ In (x,t) tvl) ->
      (forall x n ta,
          Theta.MapsTo x GeZero Q -> Stack.MapsTo x (n,ta) S ->
          (0 <= n)%Z) ->
      (forall e,
          In e es ->
          (exists n t,
              e = ELit n t /\ word_type t /\
                type_wf D m t /\ simple_type t) \/ (exists y, e = EVar y)) ->
      @well_typed_args D fenv Q R env m es ts ->
      get_dept_map tvl es = Some AS ->
      eval_el AS S tvl es S' ->
      stack_wf D Q env' S'.
  Proof with auto.
    unfold stack_wf.
    intros * Hwt Hdom Hwf Hsrh Henv Hinnot Huniq Hmap Htheta
               Hty Hargs Hdep Hel.
    intros x t Hmap'.
    destruct (Hmap _ _ Hmap') as [Hmap'' | HIn].
    - specialize (Hwf _ _ Hmap'') as [v [t' [t'' [Hb [ Hs Hm]]]]].
      exists v, t', t''.
      assert (stack_consistent_grow S S' env) as Hcst.
      { apply (stack_env_irrelavent_grow _ _ _ tvl es AS)...
        intros *; apply Hinnot. }
      split.
      apply (stack_grow_eval_type_same env S S')...
      { by decompose [and and] (Henv _ _ Hmap''). }
      split...
      apply Hcst... solveMaps.
    - pose proof (in_eval_el S S' tvl es AS Huniq Hel x t HIn) as
        (t2 & v2 & Hetb2 & Hmap2).
      exists v2, t2, t2.

  Abort.

    (* specialize (stack_consist_trans S S' env0 tvl es AS H1 H5 eq1 H12) as eq2. *)
    (* specialize (stack_wf_core D Q env0 S H2) as eq3. *)
    (* specialize (stack_wf_out tvl es D Q H env0 AS S S' H1 H0 H2 H4 H3 H5 eq3 H8 H6 H9 H10 H12) as eq4. *)
    (* unfold stack_wf in *. *)
    (* intros. *)
    (* apply H7 in H13. *)
    (* destruct H13. apply H2 in H13 as eq5. destruct eq5 as [v [ta [tb [X1 [X2 X3]]]]]. *)
    (* exists v. exists ta. exists tb. *)
    (* split. apply stack_grow_cast_type_same with (env := env0) (S := S); try easy. *)
    (* unfold env_wt in *. *)
    (* apply H4 in H13. easy. split. easy. *)
    (* unfold stack_consistent_grow in *. *)
    (* apply eq2; try easy. exists t. easy. *)
    (* apply eq4 in H13 as eq5. *)
    (* destruct eq5 as [v [ta [X1 [X2 X3]]]]. *)
    (* exists v. exists ta. exists ta. *)
    (* split. *)
    (* apply cast_as_same with (S := S) (AS := AS) (env := env0); try easy. *)
    (* apply (well_type_args_well_bound D Q H env0 AS es tvl) with (x := x); try easy. *)
    (* intros. *)
    (* apply (as_not_in_env AS tvl es env0); try easy. *)
    (* intros. *)
    (* apply (as_well_bound AS D Q H env0 tvl es) with (x := x0); try easy. *)
    (* intros.  *)
    (* apply (as_stack_in AS tvl es S S'); try easy. *)
    (* intros. *)
    (* apply (as_stack_in_2 AS tvl es S S') with (x := x0) (ta := ta0); try easy. *)
    (* apply (as_stack_in AS tvl es S S'); try easy. *)
    (* intros.  *)
    (* apply (as_diff AS tvl es) with (n := n) (n' := n'); try easy. *)
    (* split. constructor. easy. *)
