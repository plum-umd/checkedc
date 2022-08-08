From CHKC Require Import
  Coqlib
  Tactics
  ListUtil
  Map
  CheckedCDef
  CheckedCProp.

Lemma subtype_xl_refl : forall m xl t ts xl' t' ts',
    subtype empty_theta
      (TPtr m (TFun xl t ts))
      (TPtr m (TFun xl' t' ts')) ->
    xl = xl' /\ Forall2 (subtype empty_theta) ts' ts .
Proof.
  intros * Sub.
  split.
  - inv Sub; try reflexivity. inv H. reflexivity.
  - inv Sub; auto.
    inv H. induction ts'; constructor.
    repeat constructor. assumption.
Qed.

Section Progress.
  Create HintDb Progress.

  Hint Constructors eval_arg : Progress.

  Hint Rewrite compose_correct : Progress.  
  
  (* Progress property on the Checked Region *)
  Variable D : structdef.
  Variable F : FEnv.
  Variable Q : theta.
  Hypothesis HDwf : structdef_wf D.

  Ltac kill_checked :=
    match goal with
    | [H : is_checked (TPtr Tainted _) |- _] => inv H
    | [H : is_checked (TPtr Unchecked _) |- _] => inv H
    end.
  
  Ltac dauto :=
    (try kill_checked);
    autorewrite with Progress; eauto 10 with sem Progress.
  
  Lemma step_implies_reduces : forall M e M' r cm m E,
      step D F M e M' r ->
      m = mode_of' E cm ->
      reduces D F cm M (in_hole e E) m.
  Proof with eauto with sem.
    intros M e M' r cm m E Hstep Hmode; destruct r...
  Qed.

  Hint Resolve step_implies_reduces : Progress.
  
  Lemma step_implies_reduces' : forall M e M' r,
      step D F M e M' r -> 
      reduces D F Checked M e Checked.
  Proof with eauto with sem.
    intros M e M' r Hstep. rewrite <- (hole_is_id e). destruct r...
  Qed.
  Hint Resolve step_implies_reduces' : Progress.


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
      reduces D F Checked M e Checked ->
      reduces D F Checked M e' Checked.
  Proof with dauto.
    intros M e e' (E & HChk & Hole) (M' & r & Red).
    exists M'. inv Red... 
  Qed.

  Lemma get_xl_not_TNat : forall t v tvl,
      t <> TNat ->
      get_xl ((v, t) :: tvl) = get_xl tvl.
  Proof with auto.
    intros. destruct t; try congruence...
  Qed.

  Hint Rewrite get_xl_not_TNat : Progress.

  Lemma mk_eval_el : forall env s R es ts xl t ta,
      (forall e,
          In e es -> (exists (n : Z) (t : type), e = ELit n t) \/
                       (exists y : var, e = EVar y)) ->
      stack_wf Q env s ->
      @well_typed_args D F R Q env Checked es ts xl t ta -> 
      forall ftvl fe ft,
        get_xl ftvl = xl /\ Forall2 (subtype empty_theta) ts (split ftvl).2 ->
        exists re rt, eval_el s es ftvl xl fe ft re rt.
  Proof with dauto.
    Hint Constructors eval_el : Progress.
    intros env s R es. induction es; intros * Hev Hswf Hwt * (Hxl & Hts).
    - inv Hwt. rewrite (split_zero ftvl); inv Hts...
    - inv Hwt; destruct ftvl; try (inv Hts); try solve [cbn in *; congruence].
      (* args_many_1 *)
      + specialize (IHes vl (get_xl ftvl) t ta).
        destruct p eqn:Ep. (* inv H.   *)destruct (split ftvl) eqn:Eftvl. inv H2.
        mopo IHes by intuition.
        assert (HnTNat1 : t1 <> TNat).
        { inv H3; try easy. inv H; easy. }
        specialize (IHes Hswf).
        mopo IHes.
        { cbn. assert (Exl : get_xl ((v, t1) :: ftvl) = get_xl ftvl).
          destruct t1; try congruence; reflexivity.
          rewrite Exl in H9. done. 
        }
        specialize (IHes ftvl fe ft).
        mopo IHes.
        { constructor... rewrite Eftvl... }
        destruct IHes as (re & rt & IHes).
        destruct (Hev a) as [(n' & t' & Eev) | (y & Eev)];
          [intuition | rewrite Eev | rewrite Eev].
        -- exists (ELet v (ELit n' t1) re), rt. constructor...
        -- rewrite -> Eev in *. inv H4.
           apply Hswf in H0. destruct H0 as (v'' & t'' & Hsub & Hmap).
           repeat econstructor...
      (* args_many_2 *)
      + destruct p. inv H6. destruct (split ftvl). (* inv H. *)
        apply subtype_nat_1 in H3. rewrite -> H3 in *. inv H2.
        specialize (IHes vl (get_xl ftvl) t ta).
        (* specialize (IHes *)
        (*               (map (fun a : type => subst_type a v b) vl) *)
        (*               (get_xl ftvl) *)
        (*               (subst_type t v b) ta). *)
        mopo IHes. { intros. apply Hev. intuition. }.
        specialize (IHes Hswf).
        mopo IHes. {admit.}
        specialize (IHes ftvl fe t).
        mopo IHes.
        { split. reflexivity. admit.
        }
        destruct IHes as (re & rt & IHes).
        inv H0.
        destruct (Hev a) as [(n' & t' & Ha) | (y' & Ha)]; 
          [intuition | rewrite -> Ha in * | rewrite -> Ha in * ]...
        * eexists. exists rt.
          eapply eval_el_many_2...
          admit.
        * inv H4. apply Hswf in H0. destruct H0 as (v'' & t'' & Hsub & Hmap).
          eexists. exists rt. apply eval_el_many_2...
          admit.
  Admitted.
  
  Definition unchecked (cm : mode) (e : expression) : Prop :=
    cm = Unchecked /\ exists e' E, e = in_hole e' E /\ mode_of' E cm = Unchecked.
  Hint Unfold unchecked : Progress. 

  Lemma wt_lit_tainted_middle_excluded : forall H2 x tptr xl t ts, 
      tptr = (TPtr Tainted (TFun xl t ts)) -> 
      well_typed_lit_tainted D F H2 empty_scope x tptr
      \/ ~ well_typed_lit_tainted D F H2 empty_scope x tptr.
  Admitted.
  

  Lemma progress : forall R s env e t cm,
      cm <> Tainted ->
      rheap_wf R ->
      fun_wf D F R ->
      expr_wf D Checked e ->
      stack_wt D Checked s ->
      env_wt D Checked env ->
      theta_wt Q env s ->
      stack_wf Q env s ->
      stack_rheap_consistent D F R s ->
      well_typed D F R env Q Checked e t ->
      value D e \/
        reduces D F cm (s, R) e Checked \/
        unchecked cm e.
  Proof with dauto.
    intros R s env e t cm Hcm Hhwf Hfwf Hewf Hswt Henvwt Hthwf Hswf Hscon Hwt.
    remember Checked as m. 
    induction Hwt as
      [ env Q n t HChkd HSplTy HTyLit | (* TyLitChecked *)
        env Q m n t HNChkd HSplTy     | (* TyLitTainted *)
        env Q m x t t' HEmap Hsub     | (* TyVar *)
        env Q m m' es x xl ts t ta Hmode HForall Hptr IHptr Hargs | (* TyCall *)
        env Q x m m' l h t Hmaps Hmode | (* TyStrlen *)
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

    Ltac solve_unchecked :=
      right; split; do 2 econstructor; split; [symmetry; apply hole_is_id | done].
    
    (* TyLit *)
    1-2: left; inv Hewf...
    (* TyVar *)
    - right. specialize (Hswf x t); intuition.
      destruct H as (v & t'' & Heq & Hsmap).
      pose proof (SVar D F s R x v t'' Hsmap); rewrite Heqm.
      destruct cm; try congruence... solve_unchecked.
    (* TyCall *)
    - destruct cm; try congruence...
      2: { right; solve_unchecked. }
      inv Hewf. intuition.
      (* [x] is unchecked; impossible *)
      3: { inv H0. congruence. }
      (* [x] reduces *)
      2: {  right; left; eapply reduces_in_reduces... exists (CCall CHole es)... }
      (* [x] is a value, expand Call to Let expressions *)
      right; left.
      (* refine the mode *)
      assert (m' <> Unchecked) as Hmode'. { inv Hmode; intuition. }
      inv H. destruct (F m' n) eqn:Ef.
      (* no impl found for given [n]  *)
      2: { pose proof (SCallNull D F m' s R n t ts es xl Hmode' Ef) as HStep.
           inv Hptr... }
      (* found an impl *)
      destruct Hfwf as [HNull Hfwf].
      destruct f as [[ftvl ft] fe]. inv Hptr.
      (* TyLitChecked *)
      ++ inv H10.
         ** destruct m'; try congruence...
         ** rewrite (HNull m') in Ef; congruence.
         (* TyLitFun_C *)
         ** rewrite H11 in Ef. inv Ef. unfold get_fun_type in *.
            pose proof (subtype_xl_refl _ _ _ _ _ _ _ H14) as (Exl & ESub).
            rewrite -> Exl in *.
            pose proof (mk_eval_el env s R es ts xl t ta H3 Hswf Hargs
                          ftvl fe ft) as H.
            destruct H as (re & rt & H). intuition.
            eapply step_implies_reduces'.
            eapply SCallChecked. eassumption. rewrite Exl; eassumption.
         (* TyLitRec_C : Impossible in empty theta *)
         ** inv H11. 
         (* TyLitC_C : Impossible for fun ptrs *)
         ** apply subtype_fun in H11. destruct H11 as (? & ? & ? & H). inv H.
            destruct H8...
      (* TyLitTainted *)
      ++ destruct m';
           [destruct H9; constructor; congruence | idtac | congruence].
         remember (TPtr Tainted (TFun xl t ts)) as tfun.
         clear Hmode'. clear H9.
         assert (n <> 0%Z) as Hnneq0.
         { intros Contra. rewrite -> Contra in *.
           rewrite -> (HNull Tainted) in *. congruence.
         }
         edestruct (wt_lit_tainted_middle_excluded R.2 n) as [Htt | Htt].
         { apply Heqtfun. }
         (* wt_tainted *)
         ** inv Htt; try congruence.
            --- rewrite H in Ef. inv Ef. inv H8.
                pose proof (subtype_xl_refl _ _ _ _ _ _ _ H5) as (Exl & ESub).
                pose proof (mk_eval_el env s R es ts xl t ta H3 Hswf Hargs
                              ftvl fe ft) as H'.
                destruct H' as (re & rt & H'). intuition.
                eapply step_implies_reduces'.
                pose proof (SCallTainted D F s R.1 R.2) as Step.
                eapply Step in H; try eassumption.
                2: rewrite Exl; eassumption.
                replace ((R.1, R.2)) with R in * by (destruct R; reflexivity).
                apply H.
                econstructor; eassumption.
            --- inv H.
            --- inv H13. apply subtype_fun in H6.
                destruct H6 as (? & ? & ? & Eptr); inv Eptr. destruct H5...
         (* not wt_tainted *)
         ** replace R with ((R.1, R.2)) by (destruct R; reflexivity).
            eapply step_implies_reduces'. rewrite -> Heqtfun in *.
            eapply SCallTaintedType; try eassumption.
    (* TyStrlen *)
    - destruct cm; [ | intuition | right; solve_unchecked ].
      inv Hmode. right; left. specialize (H (eq_refl _)).
      pose proof (Henvwt _ _ Hmaps) as (Hwt & Hty & Hbd).
      pose proof (Hswf _ _ Hmaps) as (v & t' & Hsub & Hsmaps).
      pose proof (Hswt _ _ _ Hsmaps) as (Hwd & Htwf & Hsimple).
      pose proof (eq_subtype_nt_ptr Q t' (TPtr m' (TNTArray l h t))) as Hnt.
      mopo Hnt by constructor.  specialize (Hnt Hsub).
      destruct t'; try destruct Hnt. destruct t'; try destruct Hnt.
      apply eq_subtype_mode_same in Hsub as Hmode; subst.
      pose proof (simple_type_tnt _ _ _ Hsimple) as (nl' & nh' & ? & ?); subst.
      (* Checked Pointer *)
      + destruct (Z_le_dec nh' 0).
        { (* h' <= 0 *)
          eapply step_implies_reduces'. eapply StrlenHighOOB; eassumption.
        }
        destruct (Z_gt_dec nl' 0).
        { (* l' > 0 *)
          eapply step_implies_reduces'. eapply StrlenLowOOB; eassumption.
        }
        destruct (Z_le_dec v 0).
        { (* v <= 0 *)
          eapply step_implies_reduces'. eapply StrlenNull; eassumption.
        }
        specialize (Hscon R.1 R.2 x v (TPtr m' (TNTArray (Num nl') (Num nh') t'))).
        mopo Hscon by (destruct R; reflexivity).
        mopo Hscon by assumption.
        inv Hscon; [ destruct m'; try congruence | lia | inv H5 | ].
        (* TyLitU_C : tainted pointer *) 
        * 
        (* TyLitC_C *) 
        * cbn in H9. destruct H9 as (n' & t'' & Hzleq & Hhmaps & Hnbd').
          pose (change_strlen_stack s x Checked t nl' v n' nh') as s'.
          assert (R = (R.1, R.2)) as ER by (destruct R; reflexivity).
          rewrite ER.
          eapply step_implies_reduces'.
          pose proof (StrlenChecked D F s R.1 R.2 x v n' nl' nh').
          
          eapply (StrlenChecked D F s R.1 R.2 x v n' nl' nh'); try lia.
          apply Hcut1. apply Hnbd'. assumption.
    -
  Admitted.
  (*

    | StrlenChecked : forall (s : Stack.t (Z * type)) (H1 : Heap.t (Z * type)) 
                      (H2 : heap) (x : Stack.key) (n n' l h : Z) (t t1 : type),
                    (h > 0)%Z ->
                    (l <= 0)%Z ->
                    (0 <= n')%Z ->
                    Stack.MapsTo x (n, TPtr Checked (TNTArray (Num l) (Num h) t)) s ->
                    (forall i : Z,
                     (n <= i < n + n')%Z -> exists n1 : Z, Heap.MapsTo i (n1, t1) H1 /\ n1 <> 0%Z) ->
                    Heap.MapsTo (n + n')%Z (0%Z, t1) H1 ->
                    step D F (s, (H1, H2)) (EStrlen x)
                    (change_strlen_stack s x Checked t l n n' h, (H1, H2)) 
                      (RExpr (ELit n' TNat))
  | StrlenTainted : forall (s : Stack.t (Z * type)) (H1 : heap) (H2 : Heap.t (Z * type))
                      (x : Stack.key) (n n' l h : Z) (t t1 : type),
                    (h > 0)%Z ->
                    (l <= 0)%Z ->
                    (0 <= n')%Z ->
                    Stack.MapsTo x (n, TPtr Tainted (TNTArray (Num l) (Num h) t)) s ->
                    (forall i : Z,
                     (n <= i < n + n')%Z ->
                     exists n1 : Z,
                       Heap.MapsTo i (n1, t1) H2 /\
                       n1 <> 0%Z /\ well_typed_lit_tainted D F H2 empty_scope n1 t1) ->
                    Heap.MapsTo (n + n')%Z (0%Z, t1) H2 ->
                    step D F (s, (H1, H2)) (EStrlen x)
                      (change_strlen_stack s x Tainted t l n n' h, (H1, H2)) 
                      (RExpr (ELit n' TNat))
  | StrlenHighOOB : forall (s : Stack.t (Z * type)) (R : real_heap) (x : Stack.key) (n : Z) 
                      (t : type) (l : bound) (h : Z),
                    (h <= 0)%Z ->
                    Stack.MapsTo x (n, TPtr Checked (TNTArray l (Num h) t)) s ->
                    step D F (s, R) (EStrlen x) (s, R) RBounds
  | StrlenLowOOB : forall (s : Stack.t (Z * type)) (R : real_heap) (x : Stack.key) (n : Z) 
                     (t : type) (l : Z) (h : bound),
                   (l > 0)%Z ->
                   Stack.MapsTo x (n, TPtr Checked (TNTArray (Num l) h t)) s ->
                   step D F (s, R) (EStrlen x) (s, R) RBounds
  | StrlenNull : forall (s : Stack.t (Z * type)) (R : real_heap) (x : Stack.key) (t : type) (n : Z) (l h : bound),
                 (n <= 0)%Z ->
                 Stack.MapsTo x (n, TPtr Checked (TNTArray l h t)) s -> step D F (s, R) (EStrlen x) (s, R) RNull
  | StrlenUnChecked : forall (s : Stack.t (Z * type)) (H1 : heap) (H2 : Heap.t (Z * type))
                        (x : Stack.key) (n n' : Z) (t t1 : type),
                      (0 <= n')%Z ->
                      Stack.MapsTo x (n, TPtr Unchecked t) s ->
                      (forall i : Z,
                       (n <= i < n + n')%Z -> exists n1 : Z, Heap.MapsTo i (n1, t1) H2 /\ n1 <> 0%Z) ->
                      Heap.MapsTo (n + n')%Z (0%Z, t1) H2 ->
                      step D F (s, (H1, H2)) (EStrlen x) (s, (H1, H2)) (RExpr (ELit n' TNat))
*)

