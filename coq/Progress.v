From CHKC Require Import
  Coqlib
  Tactics
  ListUtil
  Map
  CheckedCDef
  CheckedCProp.


Section Progress.
  Create HintDb Progress.

  Hint Rewrite compose_correct : Progress.  
  
  (* Progress property on the Checked Region *)
  Variable D : structdef.
  Variable F : FEnv.
  Hypothesis HDwf : structdef_wf D.

  Ltac dauto :=
    do 3 (autorewrite with Progress; eauto 10 with sem Progress).
  
  Lemma step_implies_reduces : forall M e M' r,
      step D F M e M' r -> 
      reduces D F M e Checked.
  Proof  with eauto with sem.
    intros M e M' r. rewrite <- (hole_is_id e). destruct r...
  Qed.
  Hint Resolve step_implies_reduces : Progress.


  Lemma compose_mode_agree_inner : forall Eout Ein m,
      mode_of Eout = Checked -> 
      mode_of Ein  = m -> 
      mode_of (compose Eout Ein) = m.
  Proof with (cbn in *; eauto).
    induction Eout; intros...
    induction Eout... inv H.
  Qed.
  Hint Resolve compose_mode_agree_inner : Progress. 

  Lemma compose_mode_agree_inner2 : forall Eout Ein m,
      Checked = mode_of Eout -> 
      m = mode_of Ein -> 
      m = mode_of (compose Eout Ein).
  Proof with dauto.
    symmetry... 
  Qed.
  Hint Resolve compose_mode_agree_inner2 : Progress. 

  Lemma reduces_in_reduces : forall M e e',
      (exists E, mode_of E = Checked  /\ e' = in_hole e E) ->
      reduces D F M e Checked ->
      reduces D F M e' Checked.
  Proof with dauto.
    intros M e e' (E & HChk & Hole) (M' & r & Red).
    exists M'. inv Red... 
  Qed.


  Lemma mk_eval_el : forall s es ftvl fe ft,
    exists re rt, eval_el s es ftvl (get_xl ftvl) fe ft re rt.
  Proof.
    intros s. 
  Admitted.

  Lemma progress : forall Q R s env e t,
      rheap_wf R ->
      fun_wf D F R ->
      expr_wf D Checked e ->
      stack_wt D Checked s ->
      env_wt D Checked env ->
      theta_wt Q env s ->
      stack_wf D Q env s ->
      stack_rheap_consistent D F R s ->
      well_typed D F R env Q Checked e t ->
      value D e \/
        reduces D F (s, R) e Checked.
  Proof with dauto.
    intros Q R s env e t Hhwf Hfwf Hewf Hswt Henvwt Hthwf Hswf Hscon Hwt.
    remember Checked as m. 
    induction Hwt as
      [ env Q n t HChkd HSplTy HTyLit | (* TyLitChecked *)
        env Q m n t HNChkd HSplTy     | (* TyLitTainted *)
        env Q m x t t' HEmap Hsub     | (* TyVar *)
        env Q m m' es x xl ts t ta Hmode HForall Hptr IHptr Hargs | (* TyCall *)
        ? |
        ? |
        ? |
        ? |
        ? |
        ? |
        ? |
        ? |
        ? |
        ? |
        ? |
        ? |
        ? |
        ? |
        ? |
        ? |
        ? |
        ? |
        ? |
        ? |
        ? |
        ? |
        ? |
        ? |
        ? |
        ? |
        ? 
      ].
    (* TyLit *)
    1-2: left; inv Hewf...
    (* TyVar *)
    - right. specialize (Hswf x t); intuition.
      destruct H as (v & t'' & Heq & Hsmap).
      pose proof (SVar D F s R x v t'' Hsmap); rewrite Heqm...
    (* TyCall *)
    - inv Hewf. intuition.
      (* [x] reduces *)
      2: {  right. eapply reduces_in_reduces... exists (CCall CHole es)... }
      (* [x] is a value, expand Call to Let expressions *)
      right.
      (* refine the mode *)
      assert (m' <> Unchecked) as Hmode'. { inv Hmode; intuition. }
      inv H. destruct (F m' n) eqn:Ef.
      (* no impl found for given [n]  *)
      2: { pose proof (SCallNull D F m' s R n t ts es xl Hmode' Ef) as HStep.
           inv Hptr... }
      (* found an impl *)
      destruct f as [[ftvl ft] fe]. inv Hptr.
      (* TyLitChecked *)
      ** destruct Hfwf as [HNull Hfwf].
         inv H10.
         ++ destruct m'; try congruence. 
         

         (* ancilla *)
         specialize (Hfwf env Q n _tvl _t).
      (* TyLitTainted *)
      **

        (*
  | SCallChecked : forall (s : stack) (R : real_heap) (x : Z) (ta : type) (ts : list type) 
                     (el : list expression) (t : type) (tvl : list (var * type)) (e ea : expression) 
                     (ta' : type) (xl : list var),
                   F Checked x = Some (tvl, t, e) ->
                   eval_el s el tvl (get_xl tvl) e t ea ta' ->
                   step D F (s, R) (ECall (ELit x (TPtr Checked (TFun xl ta ts))) el) (s, R) (RExpr ea)
  | SCallNull : forall (m : mode) (s : stack) (R : real_heap) (x : Z) (ta : type) (ts : list type)
                  (el : list expression) (xl : list var),
                m <> Unchecked ->
                F m x = None -> step D F (s, R) (ECall (ELit x (TPtr m (TFun xl ta ts))) el) (s, R) RNull
  | SCallTainted : forall (s : stack) (H1 H2 : heap) (x : Z) (ta : type) (ts : list type) 
                     (el : list expression) (t : type) (tvl : list (var * type)) (e ea : expression) 
                     (ta' : type) (xl : list var),
                   F Tainted x = Some (tvl, t, e) ->
                   eval_el s el tvl (get_xl tvl) e t ea ta' ->
                   well_typed_lit_tainted D F H2 empty_scope x (TPtr Tainted (TFun xl ta ts)) ->
                   step D F (s, (H1, H2)) (ECall (ELit x (TPtr Tainted (TFun xl ta ts))) el) 
                     (s, (H1, H2)) (RExpr ea)
  | SCallTaintedType : forall (s : stack) (R : heap * heap) (x : Z) (ta : type) (ts : list type)
                         (el : list expression) (t : type) (tvl : list (var * type)) 
                         (e : expression) (xl : list var),
                       F Tainted x = Some (tvl, t, e) ->
                       ~ well_typed_lit_tainted D F R.2 empty_scope x (TPtr Tainted (TFun xl ta ts)) ->
                       step D F (s, R) (ECall (ELit x (TPtr Tainted (TFun xl ta ts))) el) (s, R) RBounds
  | SCallUnchecked : forall (s : stack) (R : real_heap) (x : Z) (ta : type) (ts : list type)
                       (el : list expression) (t : type) (tvl : list (var * type)) (e ea : expression)
                       (ta' : type) (xl : list var),
                     F Unchecked x = Some (tvl, t, e) ->
                     eval_el s el tvl (get_xl tvl) e t ea ta' ->
                     step D F (s, R) (ECall (ELit x (TPtr Unchecked (TFun xl ta ts))) el) (s, R) (RExpr ea)
                     
         *)
