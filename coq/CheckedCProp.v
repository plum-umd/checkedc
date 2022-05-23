(** * CheckedCProp : Checked C Model Properties *)

From CHKC Require Import
  Coqlib
  Tactics
  ListUtil
  Map
  CheckedCDef.

Create HintDb Preservation.


Section HeapProp.
  Local Open Scope Z_scope.
  Variable D : structdef.
  Variable F : FEnv.
  Variable Q : theta.
  Variable m : mode.

  Definition heap_wf (H : heap) : Prop := forall (addr : Z),
      0 < addr <= (Z.of_nat (Heap.cardinal H)) <-> Heap.In addr H.

  Definition stack_heap_consistent H S := forall x n t,
      Stack.MapsTo x (n,t) S ->
      well_typed_lit D F Q H empty_scope n t.

  Definition heap_consistent (H' : heap) (H : heap) : Prop :=
    forall n t,
      @well_typed_lit D F Q H empty_scope n t->
      @well_typed_lit D F Q H' empty_scope n t.

  Definition heap_well_typed (H:heap)
    (n:Z) (t:type) :=
    simple_type t -> well_typed_lit D F Q H empty_scope n t.

  Inductive heap_wt_arg (H:heap)
    : expression -> Prop :=
  | HtArgLit : forall n t,
      heap_well_typed H n t -> heap_wt_arg H (ELit n t)
  | HtArgVar : forall x, heap_wt_arg H (EVar x).

  Inductive heap_wt_args (H:heap)
    : list expression -> Prop :=
    heap_wt_empty : heap_wt_args H ([])
  | heap_wt_many : forall e el,
      heap_wt_arg H e -> heap_wt_args H el -> heap_wt_args H (e::el).

  Inductive heap_wt (H:heap) : expression -> Prop :=
  | HtLit : forall n t, heap_well_typed H n t -> heap_wt H (ELit n t)
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
      /\ well_typed_lit D F Q H empty_scope n t.
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
      (well_typed_lit D F Q Hchk empty_scope n t
       \/ well_typed_lit D F Q Htnt empty_scope n t).


  (* FIXME: hold the definition for now *)
  Definition rheap_consistent (R' : real_heap) (R : real_heap) : Prop :=
    forall Hchk' Htnt' Hchk Htnt,
      R' = (Hchk', Htnt') -> R = (Hchk, Htnt) -> 
      heap_consistent D F Q Hchk' Hchk /\ heap_consistent D F Q Htnt' Htnt.
  Hint Unfold rheap_consistent : Preservation.

  Definition rheap_wt_all (R : real_heap) := forall Hchk Htnt,
    R = (Hchk, Htnt) ->
    heap_wt_all D F Q m Hchk /\ heap_wt_all D F Q m Htnt.

End RealHeapProp.
  
Section StackProp.
  Variable D : structdef.
  Variable F : FEnv.
  Variable Q : theta.
  Variable m : mode.


  (* The following needs to be redefined in the ctx of 2 heaps *)
  (* Inductive stack_wf H : env -> stack -> Prop := *)
  (* | WFS_Stack : forall env s, *)
  (*     (forall x t, *)
  (*         Env.MapsTo x t env -> *)
  (*         exists v t' t'', *)
  (*           eval_type_bound s t = Some t' *)
  (*           /\ subtype D Q t'' t' *)
  (*           /\ Stack.MapsTo x (v, t'') s *)
  (*           /\ well_typed_lit D F Q H empty_scope v t'') *)
  (*     /\ (forall x v t, *)
  (*            Stack.MapsTo x (v, t) s ->  *)
  (*            @well_typed_lit D F Q H empty_scope v t -> *)
  (*            exists t' t'', *)
  (*              @Env.MapsTo type x t' env *)
  (*              /\ eval_type_bound s t' = Some t'' *)
  (*              /\ subtype D Q t t'') -> *)
  (*     stack_wf H env s. *)


  Inductive stack_rwf (R : real_heap) : env -> stack -> Prop :=
  | WFS_Stack : forall env s Hchk Htnt,
      R = (Hchk, Htnt) ->
      (forall x t,
          Env.MapsTo x t env ->
          exists v t' t'',
            eval_type_bound s t = Some t'
            /\ subtype D Q t'' t'
            /\ Stack.MapsTo x (v, t'') s
            /\ (well_typed_lit D F Q Hchk empty_scope v t''
                \/ well_typed_lit D F Q Htnt empty_scope v t''))
      /\ (forall x v t,
             Stack.MapsTo x (v, t) s ->
             (well_typed_lit D F Q Hchk empty_scope v t
              \/ well_typed_lit D F Q Htnt empty_scope v t) ->
             exists t' t'',
               @Env.MapsTo type x t' env
               /\ eval_type_bound s t' = Some t''
               /\ subtype D Q t t'') ->
      stack_rwf R env s.



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
    intros R s n t Contra.
    destruct Contra as [R' [ s' [ m [ r Contra ] ] ] ].
    inversion Contra; find_Hstep;
      destruct E; inversion Hstep; cbn in *; subst; try congruence.
  Qed.
End GeneralProp.

