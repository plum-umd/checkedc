(** * CheckedCDef : Checked C Model Definition *)
From CHKC Require Import
  Coqlib
  Tactics
  ListUtil
  Map.
Require Import Coq.Lists.ListSet.
Require Import Coq.Logic.Classical_Prop.

(** * Document Conventions *)

(** It is common when defining syntax for a language on paper to associate one
    or many simple_type _metavariables_ with each syntactic class. For example,
    the metavariables <<x>>, <<y>>, and <<z>> are often used to represent the
    syntactic class of program variables. It is understood that wherever these
    metavariables appear they indicate an implicit universal quantification over
    all members of the syntactic class they represent. In Coq, however, we have
    no such issue -- all quantification must be made explicit. However, we must
    still grapple with the hardest problem in computer science: naming our
    quantified variables.  To ameliorate this problem, we maintain two stylistic
    invariants.

    - (1) Whenever a new piece of syntax is introduced we we will include, in
          parentheses, its associated metavariable. We will then use this as the
          naming convention for naming universally quantified variables in the
          future.

    - (2) Whenever syntax, semantics, or proofs appear in the associated paper
          ("Checked C for Safety, Gradually") we take this to be an
          authoritative source for naming.
*)

(** * Syntax *)

(** The types [var], [field], and [struct] are the (distinguished) syntactic
    classes of program variables ([x]), fields ([f]), and structures [T])
    respectively. They are all implemented concretely as natural numbers. Each
    is a distinguished class of identifier in the syntax of the language. *)

Create HintDb ty.

Local Open Scope Z_scope.

Definition var    := nat.
Definition field  := nat.
Definition struct := nat.
Definition funid  := nat.

(* Useful shorthand in case we ever change representation. *)
Definition var_eq_dec := Nat.eq_dec.

(** The [mode], indicated by metavariable [m], is either [Checked], [Tainted] or
    [Unchecked]. *)

Inductive mode : Type :=
  | Checked : mode
  | Tainted : mode
  | Unchecked : mode.

(** Types, <<w>>, are either a word type, [TNat, TPtr], a struct type,
    [TStruct], or an array type, [TArray]. Struct types must be annotated with a
    struct identifier.  Array types are annotated with their lower-bound,
    upper-bound, and the (word) type of their elements.

    The metavariable, [w], was chosen to abbreviate "wide" or compound types.

    Notice that struct types can be self-referential. Furthermore, they are the
    only type which may be self-referential.

    Example:

    In

      struct foo { self^struct foo }

      let my_foo = malloc@struct foo in let my_foo_self = &my_foo->self in
      *my_foo_self = my_foo

    the memory location which holds the `self` field of `my_foo` contains a
    pointer which refers back to `my_foo`. Thus, `my_foo` is
    self-referential. *)

(* a bound is either a value or a expression as the form of var + num.
   Num => n
   Var => x + n
   NVar => n + (x + n')
   VVar => x + (x' + n)
*)
Inductive bound : Set := | Num : Z -> bound | Var : var -> Z -> bound.

Definition fun_num := 5.

(*
Inductive bound : Set :=
  | Num : Z -> bound
  | Var : var -> Z -> bound
  | NVar : Z -> var -> Z -> bound
  | VVar : var -> var -> Z -> bound.

Inductive ptrType : Set := StaticType | HeapType.
*)
(*
Inductive ptrName : Set := NumPtr : Z -> ptrName | VarPtr : var -> ptrName.

Definition ptrMode := option (ptrType * ptrName).
 *)

Inductive type : Type :=
  | TNat : type
  | TPtr : mode -> type -> type (* number of byptes. Num 0 represents a null pointer. *)
  | TStruct : struct -> type
  | TArray : bound -> bound -> type -> type
  | TNTArray : bound -> bound -> type -> type
  | TFun : list var -> type -> list type -> type. (* bound refers to the function name. *)

(*
Fixpoint All {A} (P : A -> Prop) (l : list A) : Prop :=
  match l with
  | [] => True
  | x :: xs => P x  /\ All P xs
  end.
 *)

Definition type_ind'
  : forall P : type -> Prop,
    P TNat ->
    (forall (m : mode) (t : type), P t -> P (TPtr m t)) ->
    (forall s : struct, P (TStruct s)) ->
    (forall (b b0 : bound) (t : type), P t -> P (TArray b b0 t)) ->
    (forall (b b0 : bound) (t : type), P t -> P (TNTArray b b0 t)) ->
    (forall (xl:list var) (t : type),
        P t ->
        (forall l, Forall P l -> P (TFun xl t l))) ->
    forall t : type, P t. 
Proof.
  intros P HTNat HTPtr HTStruct HTArray HTNTArray HTFun.
  refine
    (fix F t :=
       match t with
       | TNat => HTNat
       | TPtr m t => HTPtr m t (F t)
       | TStruct s => HTStruct s
       | TArray b1 b2 t => HTArray b1 b2 t (F t)
       | TNTArray b1 b2 t => HTNTArray b1 b2 t (F t)
       | TFun xl t ts =>
           HTFun xl t (F t) ts _
       end).
  induction ts.
  - exact (Forall_nil P).
  - exact (Forall_cons _ (F a) IHts).
Defined.


(*
Definition ptrMode_dec (p1 p2: ptrMode): {p1 = p2} + {~ p1 = p2}.
  repeat decide equality.
Defined.

Definition bound_dec (p1 p2: bound): {p1 = p2} + {~ p1 = p2}.
  repeat decide equality.
Defined.

Definition type_eq_dec (t1 t2 : type): {t1 = t2} + {~ t1 = t2}.
  repeat decide equality.
Defined.
*)

(** Word types, <<t>>, are either numbers, [WTNat], or pointers, [WTPtr].
    Pointers must be annotated with a [mode] and a (compound) [type]. *)

Inductive word_type : type -> Prop :=
  | WTNat : word_type (TNat)
  | WTPtr : forall m w, word_type (TPtr m w).

Inductive word_type_sub : type -> Prop :=
    word_type_sub_nat: word_type_sub (TNat)
  | word_type_sub_ptr: forall m t, word_type t -> word_type_sub (TPtr m t)
  | word_type_sub_struct: forall m T, word_type_sub (TPtr m (TStruct T))
  | word_type_sub_array: forall m b1 b2 t, word_type t -> word_type_sub (TPtr m (TArray b1 b2 t))
  | word_type_sub_ntarray: forall m b1 b2 t, word_type t -> word_type_sub (TPtr m (TNTArray b1 b2 t))
  | word_type_sub_fun: forall m xl t l,
      word_type_sub t -> Forall word_type_sub l -> word_type_sub (TPtr m (TFun xl t l)).

Lemma word_type_sub_imp: forall t, word_type_sub t -> word_type t.
Proof.
  intros. induction H; try constructor.
Qed.

Hint Constructors word_type.

(** Fields, [fs], are a vector of fields paired with their (word) type.

    We represent this as a finite list map. The keys are the field identifier,
    and the values are its (word) type.
*)

Require Import OrderedTypeEx.

Module Fields := FMapList.Make Nat_as_OT.

Definition fields := Fields.t type.

(** Structdefs, [D], are a map of structures to fields.

    Structdefs also have a well-formedness predicate. This says that a structdef
    cannot reference structures that it does not define.
 *)

Module StructDef := Map.Make Nat_as_OT.

Definition structdef := StructDef.t fields.

(*
Inductive none_bound_only : bound -> Prop :=
    | none_bound_only_1: forall n, none_bound_only (Num n)
    | none_bound_only_2: forall x y, none_bound_only (Var x y None).
*)
Definition freeBoundVars b := 
  match b with Num b => [] | Var x y => [x] end.

Fixpoint freeTypeVars t := 
 match t with TNat => []
        | TPtr m t => freeTypeVars t
        | TStruct s => []
        | TArray b1 b2 t => freeBoundVars b1 ++ freeBoundVars b2 ++ freeTypeVars t
        | TNTArray b1 b2 t => freeBoundVars b1 ++ freeBoundVars b2 ++ freeTypeVars t
        | TFun xl t tl => set_diff Nat.eq_dec (freeTypeVars t ++ (fold_right (fun b a => freeTypeVars b ++ a) [] tl)) xl
 end.

Inductive type_wf (D : structdef) : mode -> type -> Prop :=
| WFTNat : forall m, type_wf D m (TNat)
| WFTPtrChecked : forall m w, type_wf D m w -> type_wf D Checked (TPtr m w)
| WFTPtrUnChecked : forall m m' w,
    m <> Checked -> m' <> Checked -> type_wf D m w -> type_wf D m (TPtr m' w)
| WFTStruct : forall m T,
    (exists (fs : fields), StructDef.MapsTo T fs D) ->
    type_wf D m (TStruct T)
| WFArray : forall m l h t,
    word_type t ->
    type_wf D m t ->
    type_wf D m (TArray l h t)
| WFNTArry : forall m l h t,
    word_type t ->
    type_wf D m t ->
    type_wf D m (TNTArray l h t)

| WFTFun : forall m xl t ts,
    word_type t -> type_wf D m t ->
    Forall (fun t' => word_type t' /\ type_wf D m t') ts ->
    (forall x, In x (freeTypeVars t ++ (fold_right (fun b a => freeTypeVars b ++ a) [] ts)) -> In x xl) -> 
    type_wf D m (TFun xl t ts).

Lemma type_wf_tc : forall t D m m', m <> Checked -> m' <> Checked -> type_wf D m t -> type_wf D m' t.
Proof.
  induction t using type_ind'; intros;simpl in *. constructor.
  inv H1. easy. apply WFTPtrUnChecked; try easy. eapply IHt; eauto.
  inv H1. constructor. easy.
  inv H1. constructor; try easy. eapply IHt;eauto.
  inv H1. constructor; try easy. eapply IHt;eauto.
  inv H2. constructor; try easy.
  eapply IHt; eauto. clear H10. clear IHt. clear H6 H8.
  induction l; simpl in *. constructor.
  inv H. inv H9. destruct H3. constructor.
  split. easy. eapply H4; eauto.
  apply IHl. easy. easy.
Qed.

Lemma type_wf_uc_c : forall t D m, m <> Checked -> type_wf D m t -> type_wf D Checked t.
Proof.
  induction t using type_ind';intros;simpl in *; try easy.
  constructor. inv H0. easy.
  destruct m. constructor.
  apply IHt with (m := m0); try easy.
  apply WFTPtrChecked.
  apply type_wf_tc with (m := m0); try easy.
  apply WFTPtrChecked.
  apply type_wf_tc with (m := m0); try easy.
  inv H0. constructor; try easy.
  inv H0. constructor; try easy.
  apply IHt with (m := m); try easy.
  inv H0. constructor; try easy.
  apply IHt with (m := m); try easy.
  inv H1. constructor; try easy.
  eapply IHt; eauto.
  clear IHt H5 H7 H9.
  induction l; intros;simpl in *.
  constructor.
  inv H8. inv H. constructor.
  split. easy. eapply H5; eauto.
  destruct H3; try easy.
  apply IHl; try easy.
Qed.


Module Env := Map.Make Nat_as_OT.
Module EnvFacts := FMapFacts.Facts (Env).
Definition env := Env.t type.

Definition empty_env := @Env.empty type.

Definition venv := Env.t var.

Definition empty_venv := @Env.empty var.

Definition bn_env := Env.t bound.

Definition empty_bn_env := @Env.empty bound.

(* well_bound definition might not needed in the type system, since the new
   [expr_wf] will guarantee that. *)
Definition is_ptr (t : type) : Prop :=
    match t with TPtr m x => True
              | _ => False
    end.
(*
Definition well_ptr_bound_in (env:env) (p:ptrMode) :=
   match p with None => True
           | Some (t,a) =>
            match a with VarPtr x => Env.MapsTo x TNat env
                      | NumPtr n => True
             end
   end.
*)

Section EnvWt.
  Variable D : structdef.
  Variable m : mode.

  Definition well_bound_in (env:env) (b:bound) :=
    (forall x, In x (freeBoundVars b) -> Env.MapsTo x TNat env).

  Definition well_type_bound_in (env:env) (t:type) :=
    (forall x, In x (freeTypeVars t) -> Env.MapsTo x TNat env).

  Definition env_wt (env : env) :=
    forall x t,
      Env.MapsTo x t env ->
      word_type t /\ type_wf D m t /\ well_type_bound_in env t.
End EnvWt.

(* Definition of simple type meaning that has no bound variables. *)
Definition simple_bound (b:bound) := freeBoundVars b = [].

Definition simple_type (t:type) := freeTypeVars t = [].


Lemma simple_type_tnt: forall b1 b2 t, simple_type (TNTArray b1 b2 t)
     -> exists b1' b2', b1 = Num b1' /\ b2 = Num b2'.
Proof.
 intros. inv H.
 apply app_eq_nil in H1.
 destruct H1.
 apply app_eq_nil in H0. destruct H0.
 destruct b1. destruct b2. exists z,z0. easy. 
 simpl in *. inv H0. simpl in *. inv H.
Qed.

Lemma simple_type_array: forall b1 b2 t, simple_type (TArray b1 b2 t)
     -> exists b1' b2', b1 = Num b1' /\ b2 = Num b2'.
Proof.
 intros. inv H.
 apply app_eq_nil in H1.
 destruct H1.
 apply app_eq_nil in H0. destruct H0.
 destruct b1. destruct b2. exists z,z0. easy. 
 simpl in *. inv H0. simpl in *. inv H.
Qed.

(* unproceedable because of ill-formed ind 
Definition simple_type_ind' :
  forall P : type -> Prop,
    P TNat ->
    (forall (m : mode) (w : type), simple_type w -> P w -> P (TPtr m w)) ->
    (forall t : struct, P (TStruct t)) ->
    (forall (l h : Z) (t : type), simple_type t -> P t -> P (TArray (Num l) (Num h) t)) ->
    (forall (l h : Z) (t : type), simple_type t -> P t -> P (TNTArray (Num l) (Num h) t)) ->
    (forall (l : Z) (t : type) (ts : list type),
        simple_type t -> P t ->
        Forall (fun x => simple_type x /\ P x) ts -> 
        P (TFun (Num l) [] t ts)) ->
    forall t : type, simple_type t -> P t.
Proof.
  intros P HNat HPtr HTStruct HArr HNTArr HFun.
  refine
    (fix F t s :=
       match s in (simple_type t0) return (P t0) with
       | SPTNat => HNat
       | SPTPtr m w s0 => HPtr m w s0 (F w s0)
       | SPTStruct t0 => HTStruct t0
       | SPTArray l h t0 s0 => HArr l h t0 s0 (F t0 s0)
       | SPTNTArray l h t0 s0 => HNTArr l h t0 s0 (F t0 s0)
       | SPTFun l t0 ts s0 Fts=> _ 
       end).
  induction ts.
  - apply HFun; try assumption. exact (F t0 s0). constructor.
Abort.
*)
(*
Inductive ext_bound_in : list var -> bound -> Prop :=
  | ext_bound_in_num : forall l n, ext_bound_in l (Num n)
  | ext_bound_in_var : forall l y n, ext_bound_in l (Var y n).

Inductive ext_type_in : list var -> type -> Prop :=
  | ext_type_in_nat : forall l, ext_type_in l (TNat)
  | ext_type_in_ptr : forall l c t, ext_type_in l t -> ext_type_in l (TPtr c t)
  | ext_type_in_struct : forall l t, ext_type_in l (TStruct t)
  | ext_type_in_array : forall l b1 b2 t, ext_bound_in l b1 -> ext_bound_in l b2
                        -> ext_type_in l t -> ext_type_in l (TArray b1 b2 t)
  | ext_type_in_ntarray : forall l b1 b2 t, ext_bound_in l b1 -> ext_bound_in l b2
                        -> ext_type_in l t -> ext_type_in l (TNTArray b1 b2 t).
*)




(*
Definition no_ebound (b:bound): Prop :=
   match b with Num n => True
             | Var x y => True
   end.


Inductive no_etype : type -> Prop :=
  | no_etype_nat : no_etype (TNat)
  | no_etype_ptr : forall m w, no_etype w -> no_etype (TPtr m w)
  | no_etype_struct : forall T, no_etype (TStruct T)
  | no_etype_array : forall l h t, no_etype t -> no_ebound l -> no_ebound h -> no_etype (TArray l h t)
  | no_etype_ntarray : forall l h t,  no_etype t -> no_ebound l -> no_ebound h -> no_etype (TNTArray l h t).
*)

Definition fields_wf (D : structdef) (fs : fields) : Prop :=
  forall f t,
    Fields.MapsTo f t fs ->
    word_type t /\ type_wf D Checked t /\ simple_type t.

Definition structdef_wf (D : structdef) : Prop :=
  forall (T : struct) (fs : fields),
    StructDef.MapsTo T fs D ->
    fields_wf D fs.


Inductive theta_elem : Type := NumEq (n:bound) | GeZero.

Module Theta := Map.Make Nat_as_OT.
Module ThetaFacts := FMapFacts.Facts (Theta).

Definition theta := Theta.t theta_elem.

Definition empty_theta := @Theta.empty theta_elem.

Lemma theta_find_add2 : forall x y (t : theta_elem) env,
    x <> y ->
    Theta.find x (Theta.add y t env) = Theta.find x env.
Proof.
  intros.
  destruct (Theta.find (elt:=theta_elem) x env0) eqn:H1.
  apply Theta.find_1.
  apply Theta.add_2.
  auto.
  apply Theta.find_2.
  assumption.
  apply Theta.find2.
  unfold not.
  intros.
  eapply Theta.add_3 in H0.
  apply Theta.find_1 in H0.
  rewrite -> H1 in H0.
  inversion H0.
  auto.
Qed.

Lemma equiv_theta_add : forall x t Q Q',
    Theta.Equal (elt:=theta_elem) Q Q' ->
    Theta.Equal (elt:=theta_elem) (Theta.add x t Q) (Theta.add x t Q').
Proof.
  intros.
  unfold Theta.Equal.
  intros.
  destruct (Theta.E.eq_dec x y).
  rewrite e.
  rewrite Theta.find_add1.
  rewrite Theta.find_add1.
  auto.
  auto.
  auto.
  rewrite theta_find_add2. lia.
  rewrite theta_find_add2. lia.
  unfold Env.Equal in H.
  apply H.
Qed.

Lemma theta_shadow : forall env x (t1 t2 : theta_elem),
    Theta.Equal (Theta.add x t2 (Theta.add x t1 env)) (Theta.add x t2 env).
Proof.
  intros env x t1 t2 y.
  destruct (Nat.eq_dec x y) eqn:Eq; subst; eauto.
  - do 2 rewrite Theta.find_add1; auto.
  - repeat (rewrite theta_find_add2; eauto).
Qed.

Lemma theta_shadow_eq : forall env0 env1 x (t1 t2 : theta_elem),
    Theta.Equal env0 (Theta.add x t2 env1) ->
    Theta.Equal (Theta.add x t1 env0) (Theta.add x t1 env1).
Proof.
  intros env0 env1 x t1 t2 H y.
  destruct (Nat.eq_dec x y) eqn:Eq; subst; eauto.
  - repeat (rewrite Theta.find_add1; eauto).
  - rewrite theta_find_add2; eauto.
    specialize (H y).
    rewrite theta_find_add2 in H; eauto.
    rewrite theta_find_add2; eauto.
Qed.

Lemma theta_neq_commute : forall x1 x2 (t1 t2 : theta_elem) env,
     x1 <> x2 ->
    Theta.Equal (Theta.add x1 t1 (Theta.add x2 t2 env)) (Theta.add x2 t2 (Theta.add x1 t1 env)).
Proof.
  intros x1 x2 t1 t2 env Eq x.
  destruct (Nat.eq_dec x x1) eqn:Eq1; destruct (Nat.eq_dec x x2) eqn:Eq2; subst; eauto;
  repeat (try rewrite Theta.find_add1; auto; try rewrite theta_find_add2; auto).    
Qed.

Lemma theta_remove_eq : forall Q Q' x,
     @Theta.Equal theta_elem Q Q' -> Theta.Equal (Theta.remove x Q) (Theta.remove x Q').
Proof.
  intros. 
  apply ThetaFacts.Equal_mapsto_iff.
  intros.
  destruct (Nat.eq_dec k x); subst.
  split; intros.
  assert (~ Theta.In x (Theta.remove (elt:=theta_elem) x Q)).
  apply Theta.remove_1. easy. 
  assert (Theta.In x (Theta.remove (elt:=theta_elem) x Q)).
  exists e. easy. easy.
  assert (~ Theta.In x (Theta.remove (elt:=theta_elem) x Q')).
  apply Theta.remove_1. easy. 
  assert (Theta.In x (Theta.remove (elt:=theta_elem) x Q')).
  exists e. easy. easy.
  split. intros. apply Theta.remove_3 in H0.
  apply Theta.remove_2. lia. eapply Theta.mapsto_equal; eauto.
  intros. apply Theta.remove_3 in H0.
  apply Theta.remove_2. lia. eapply Theta.mapsto_equal; eauto.
  apply ThetaFacts.Equal_sym. easy.
Qed.


(* This defines the subtyping relation. *)
Inductive nat_leq (T:theta) : bound -> bound -> Prop :=
| nat_leq_num : forall l h, l <= h -> nat_leq T (Num l) (Num h)
| nat_leq_var : forall x l h, l <= h -> nat_leq T (Var x l) (Var x h)
| nat_leq_num_var : forall x l h,
    Theta.MapsTo x GeZero T -> l <= h -> nat_leq T (Num l) (Var x h)
| nat_leq_var_1: forall x n l v, Theta.MapsTo x (NumEq (Num n)) T -> nat_leq T (Num (n+l)) v -> nat_leq T (Var x l) v
| nat_leq_var_2: forall x n l v, Theta.MapsTo x (NumEq (Num n)) T -> nat_leq T v (Num (n+l)) -> nat_leq T v (Var x l)
| nat_leq_var_3: forall x y n l v, Theta.MapsTo x (NumEq (Var y n)) T -> nat_leq T (Var y (n+l)) v -> nat_leq T (Var x l) v
| nat_leq_var_4: forall x y n l v, Theta.MapsTo x (NumEq (Var y n)) T -> nat_leq T v (Var y (n+l)) -> nat_leq T v (Var x l).

Lemma nat_leq_refl : forall T a, nat_leq T a a.
Proof.
  intros. induction a.
  constructor. easy.
  constructor. easy.
Qed.

Axiom nat_leq_trans : forall a b c T,  nat_leq T a b -> nat_leq T b c -> nat_leq T a c.
(*
Proof.
  intros.  generalize dependent c. induction H;intros;simpl in *.
  inv H0. constructor. lia. 
  apply nat_leq_num_var; try easy. lia.
  apply nat_leq_var_2 with (n := n); try easy.
  inv H2.
  constructor. lia.
  inv H0. constructor. lia.
  inv H5.
  apply nat_leq_var_1 with (n := n); try easy.
  constructor. lia.
  apply nat_leq_var_1 with (n := n); try easy.
  apply nat_leq_num_var; try easy. lia.
  apply nat_leq_var_1 with (n := n); try easy.
  apply nat_leq_var_2 with (n := n0); try easy.
  inv H1.
  constructor. lia.
  inv H2. inv H6.
  apply nat_leq_var_1 with (n := n0); try easy.
  apply nat_leq_var_2 with (n := n); try easy.
  constructor; try easy. lia.
  inv H1.
  apply nat_leq_num_var; try easy. lia.
  apply Theta.mapsto_always_same with (v1 := GeZero) in H4; try easy.
  inv H3.
  apply Theta.mapsto_always_same with (v1 := GeZero) in H5; try easy.
  apply IHnat_leq in H1. inv H1.
  apply nat_leq_var_1 with (n := n); try easy.
  constructor. easy.
  apply nat_leq_var_1 with (n := n); try easy.
  apply nat_leq_num_var; try easy.
  inv H3.
  apply nat_leq_var_1 with (n := n); try easy.
  apply nat_leq_var_2 with (n := n0); try easy.
  constructor. lia.
  apply IHnat_leq.
  inv H1.
  apply nat_leq_var_2 with (n := n); try easy.
  constructor. lia.
  apply Theta.mapsto_always_same with (v1 := (NumEq n)) in H4; try easy.
  inv H4. easy.
  inv H3.
  apply Theta.mapsto_always_same with (v1 := (NumEq n)) in H5; try easy.
  inv H5.
  apply nat_leq_var_2 with (n := n0); try easy.
Qed.
*)

Lemma nat_leq_q_empty: forall Q n n', nat_leq empty_theta n n' -> nat_leq Q n n'.
Proof.
  intros. remember empty_theta as Q'. induction H;intros;simpl in *;subst.
  constructor. easy. constructor. easy.
  apply ThetaFacts.empty_mapsto_iff in H. easy.
  apply ThetaFacts.empty_mapsto_iff in H. easy.
  apply ThetaFacts.empty_mapsto_iff in H. easy.
  apply ThetaFacts.empty_mapsto_iff in H. easy.
  apply ThetaFacts.empty_mapsto_iff in H. easy.
Qed.


Hint Resolve nat_leq_refl : ty.
Hint Resolve nat_leq_trans : ty.

(* subst variables for tfun eq. *)
Definition subst_bound_var (b:bound) (x:var) (b1:var) :=
   match b with Num n => (Num n)
           | Var y n =>
        if Nat.eqb y x then Var b1 n else Var y n
   end.

Fixpoint subst_bounds_var (b:bound) (s: list (var*var)) :=
  match s with [] => b
            | (x,b1)::xs => subst_bounds_var (subst_bound_var b x b1) xs
  end.

Definition subtract_subst_var (s:list (var*var)) (l:list var) :=
   fold_right (fun b a => if set_mem Nat.eq_dec (fst b) l then a else b::a) s [].

Fixpoint subst_type_var (s: list (var*var)) (t:type) :=
   match t with TNat => TNat
            | TPtr m t' => TPtr m (subst_type_var s t')
            | TStruct T => TStruct T
            | TArray b1 b2 t => TArray (subst_bounds_var b1 s) (subst_bounds_var b2 s) (subst_type_var s t)
            | TNTArray b1 b2 t => TNTArray (subst_bounds_var b1 s) (subst_bounds_var b2 s) (subst_type_var s t)
            | TFun xl t tl => TFun xl
                 (subst_type_var (subtract_subst_var s xl) t) (map (fun x => subst_type_var (subtract_subst_var s xl)  x) tl)
  end.

Definition nat_eq (T:theta) (b1 b2:bound) := nat_leq T b1 b2 /\ nat_leq T b2 b1.

Lemma nat_eq_refl (T:theta) : forall b, nat_eq T b b.
Proof.
 intros.
 unfold nat_eq in *. split.
 induction b;try easy. constructor. lia. constructor. lia.
 induction b;try easy. constructor. lia. constructor. lia.
Qed.

Lemma nat_eq_sym (T:theta) : forall b1 b2, nat_eq T b1 b2 -> nat_eq T b2 b1.
Proof.
 intros.
 unfold nat_eq in *. destruct H.
 split. easy. easy.
Qed.

Lemma nat_eq_trans (T:theta) : forall b1 b2 b3, nat_eq T b1 b2 -> nat_eq T b2 b3 -> nat_eq T b1 b3.
Proof.
 intros.
 unfold nat_eq in *. destruct H. destruct H0.
 split. eapply nat_leq_trans. apply H. easy.
 eapply nat_leq_trans. apply H2. easy.
Qed.

#[export] Hint Resolve nat_eq_refl : ty.
#[export] Hint Resolve nat_eq_sym : ty.
#[export] Hint Resolve nat_eq_trans : ty.

Inductive type_eq (T:theta) : type -> type -> Prop := 
   type_eq_nat : type_eq T TNat TNat
   | type_eq_ptr : forall m t1 t2, type_eq T t1 t2 -> type_eq T (TPtr m t1) (TPtr m t2)
   | type_eq_struct: forall t1, type_eq T (TStruct t1) (TStruct t1)
   | type_eq_array: forall b1 b2 b1a b2a t1 t2, type_eq T t1 t2 -> nat_eq T b1 b1a -> nat_eq T b2 b2a
               -> type_eq T (TArray b1 b2 t1) (TArray b1a b2a t2)
   | type_eq_ntarray: forall b1 b2 b1a b2a t1 t2, type_eq T t1 t2 -> nat_eq T b1 b1a -> nat_eq T b2 b2a
                 -> type_eq T (TNTArray b1 b2 t1) (TNTArray b1a b2a t2)
   | type_eq_fun: forall xl t1 ts1, type_eq T (TFun xl t1 ts1) (TFun xl t1 ts1).


Lemma subst_bound_var_same: forall l b, (forall x y, In (x,y) l -> x = y) -> subst_bounds_var b l = b.
Proof.
 induction l;intros;simpl in *. easy.
 destruct a.
 specialize (H v v0) as X1.
 assert ((v, v0) = (v, v0) \/ In (v, v0) l). left. easy.
 apply H in H0. subst.
 unfold subst_bound_var. destruct b.
 apply IHl. intros. apply H. right. easy.
 destruct ((v =? v0)%nat) eqn:eq1.
 apply Nat.eqb_eq in eq1. subst.
 apply IHl;intros;try easy. apply H. right. easy.
 apply Nat.eqb_neq in eq1.
 apply IHl. intros. apply H. right. easy.
Qed.

Lemma true_subtract : forall l1 (P:list (var * var) -> Prop) l, P l -> P (subtract_subst_var l l1).
Proof.
 intros. unfold subtract_subst_var in *.
 induction l1;intros;simpl in *.
 easy. apply IHl1.
Qed.

Lemma subst_type_var_same : forall t l, (forall x y, In (x,y) l -> x = y) -> subst_type_var l t = t.
Proof.
 induction t using type_ind';intros; simpl in *; try easy.
 rewrite IHt; try easy.
 repeat rewrite subst_bound_var_same; try easy.
 rewrite IHt; try easy.
 repeat rewrite subst_bound_var_same; try easy.
 rewrite IHt; try easy.
 rewrite IHt.
 apply true_subtract. easy.
 assert ((map [eta subst_type_var (subtract_subst_var l0 xl)] l) = l).
 induction l;simpl in *. easy.
 inv H.
 rewrite IHl. apply H4.
 rewrite H3.
 apply true_subtract. easy. easy.
 rewrite H1. easy.
Qed.

Lemma combine_eq: forall (l:list var) x y, In (x,y) (combine l l) -> x = y.
Proof.
 induction l;intros;simpl in *.
 easy. destruct H. inv H. easy.
 apply IHl. easy.
Qed.

Lemma type_eq_refl (T:theta) : forall t, type_eq T t t.
Proof.
 intros.
 induction t using type_ind';intros; simpl in *; try easy.
 constructor.
 constructor;try easy.
 constructor.
 constructor;auto with ty.
 constructor;auto with ty.
 constructor; try easy.
(*
 rewrite subst_type_var_same.
 apply combine_eq. easy.
 induction l;intros; simpl in *. constructor.
 inv H. constructor.
 rewrite subst_type_var_same.
 apply combine_eq. easy.
 apply IHl. easy.
*)
Qed.

Lemma type_eq_sym (T:theta) : forall t1 t2, type_eq T t1 t2 -> type_eq T t2 t1.
Proof.
 intros. induction H;intros; simpl in *.
 constructor; easy.
 constructor; easy.
 constructor; easy.
 constructor; auto with ty.
 constructor; auto with ty.
 constructor.
(* easy.*)
Qed.

Lemma type_eq_trans (T:theta) : forall t1 t2 t3, type_eq T t1 t2 -> type_eq T t2 t3 -> type_eq T t1 t3.
Proof.
 intros. generalize dependent t3. induction H;intros; simpl in *; try easy.
 inv H0. constructor. apply IHtype_eq; try easy.
 inv H2. constructor. apply IHtype_eq; auto.
 specialize (nat_eq_trans T b1 b1a b1a0 H0 H8) as X1; easy.
 specialize (nat_eq_trans T b2 b2a b2a0 H1 H9) as X1; easy.
 inv H2. constructor. apply IHtype_eq; auto.
 specialize (nat_eq_trans T b1 b1a b1a0 H0 H8) as X1; easy.
 specialize (nat_eq_trans T b2 b2a b2a0 H1 H9) as X1; easy.
Qed.

Lemma nat_leq_q_eq: forall Q Q' a b, Theta.Equal Q Q' ->
      nat_leq Q a b -> nat_leq Q' a b.
Proof.
  intros. induction H0;try easy.
  constructor. easy. constructor. easy.
  constructor; try easy.
  eapply Theta.mapsto_equal. apply H0. easy.
  apply nat_leq_var_1 with (n := n); try easy.
  eapply Theta.mapsto_equal. apply H0. easy.
  apply nat_leq_var_2 with (n := n); try easy.
  eapply Theta.mapsto_equal. apply H0. easy.
  apply nat_leq_var_3 with (y := y) (n := n); try easy.
  eapply Theta.mapsto_equal. apply H0. easy.
  apply nat_leq_var_4 with (y := y) (n := n); try easy.
  eapply Theta.mapsto_equal. apply H0. easy.
Qed.

Lemma nat_leq_q_conv: forall Q a b x v, 0 <= v ->
      nat_leq (Theta.add x GeZero Q) a b -> nat_leq (Theta.add x (NumEq (Num v)) Q) a b.
Proof.
  intros. induction H0;try easy.
  constructor. easy. constructor. easy.
  destruct (Nat.eq_dec x0 x); subst.
  apply nat_leq_var_2 with (n := v); try easy.
  apply Theta.add_1. easy. constructor. lia.
  apply Theta.add_3 in H0; try lia.
  constructor; try easy.
  apply Theta.add_2; try lia. easy.
  destruct (Nat.eq_dec x0 x); subst.
  apply Theta.mapsto_add1 in H0. inv H0.
  apply Theta.add_3 in H0; try lia.
  apply nat_leq_var_1 with (n := n); try easy.
  apply Theta.add_2. lia. easy.
  destruct (Nat.eq_dec x0 x); subst.
  apply Theta.mapsto_add1 in H0. inv H0.
  apply Theta.add_3 in H0; try lia.
  apply nat_leq_var_2 with (n := n); try easy.
  apply Theta.add_2. lia. easy.
  destruct (Nat.eq_dec x0 x); subst.
  apply Theta.mapsto_add1 in H0. inv H0.
  apply Theta.add_3 in H0; try lia.
  apply nat_leq_var_3 with (y := y) (n := n); try easy.
  apply Theta.add_2. lia. easy.
  destruct (Nat.eq_dec x0 x); subst.
  apply Theta.mapsto_add1 in H0. inv H0.
  apply Theta.add_3 in H0; try lia.
  apply nat_leq_var_4 with (y := y) (n := n); try easy.
  apply Theta.add_2. lia. easy.
Qed.

Lemma type_eq_q_eq: forall Q Q' t t', Theta.Equal Q Q' ->
     type_eq Q t t' -> type_eq Q' t t'.
Proof.
  intros. induction H0; intros;simpl in *. constructor.
  constructor. easy. constructor. constructor; try easy.
  unfold nat_eq in *. destruct H1.
  split. eapply nat_leq_q_eq; eauto.
  eapply nat_leq_q_eq; eauto. 
  unfold nat_eq in *. destruct H2.
  split. eapply nat_leq_q_eq; eauto.
  eapply nat_leq_q_eq; eauto.
  constructor; try easy. 
  unfold nat_eq in *. destruct H1.
  split. eapply nat_leq_q_eq; eauto.
  eapply nat_leq_q_eq; eauto. 
  unfold nat_eq in *. destruct H2.
  split. eapply nat_leq_q_eq; eauto.
  eapply nat_leq_q_eq; eauto.
  constructor.
Qed.

Lemma type_eq_q_conv: forall Q t t' x v, 0 <= v ->
     type_eq (Theta.add x GeZero Q) t t' -> type_eq (Theta.add x (NumEq (Num v)) Q) t t'.
Proof.
  intros. induction H0; intros;simpl in *. constructor.
  constructor. easy. constructor. constructor; try easy.
  unfold nat_eq in *. destruct H1.
  split. eapply nat_leq_q_conv; eauto.
  eapply nat_leq_q_conv; eauto. 
  unfold nat_eq in *. destruct H2.
  split. eapply nat_leq_q_conv; eauto.
  eapply nat_leq_q_conv; eauto.
  constructor; try easy. 
  unfold nat_eq in *. destruct H1.
  split. eapply nat_leq_q_conv; eauto.
  eapply nat_leq_q_conv; eauto. 
  unfold nat_eq in *. destruct H2.
  split. eapply nat_leq_q_conv; eauto.
  eapply nat_leq_q_conv; eauto.
  constructor.
Qed.


Lemma nat_leq_q_add: forall Q t t' x v, ~ Theta.In x Q ->
    nat_leq Q t t' -> nat_leq (Theta.add x v Q) t t'.
Proof.
  intros. induction H0;simpl in *; try easy.
  constructor. lia. constructor. lia.
  constructor. destruct (Nat.eq_dec x0 x); subst.
  assert (Theta.In x Q). exists GeZero. easy. easy.
  apply Theta.add_2. lia. easy. lia.
  apply nat_leq_var_1 with (n := n); try lia.
  destruct (Nat.eq_dec x0 x); subst. assert (Theta.In x Q). exists (NumEq (Num n)).
  easy. easy. apply Theta.add_2. lia. easy. auto.
  apply nat_leq_var_2 with (n := n); try lia.
  destruct (Nat.eq_dec x0 x); subst. assert (Theta.In x Q). exists (NumEq (Num n)).
  easy. easy. apply Theta.add_2. lia. easy. auto.
  apply nat_leq_var_3 with (y := y) (n := n); try lia.
  destruct (Nat.eq_dec x0 x); subst. assert (Theta.In x Q). exists (NumEq (Var y n)).
  easy. easy. apply Theta.add_2. lia. easy. auto.
  apply nat_leq_var_4 with (y := y) (n := n); try lia.
  destruct (Nat.eq_dec x0 x); subst. assert (Theta.In x Q). exists (NumEq (Var y n)).
  easy. easy. apply Theta.add_2. lia. easy. auto.
Qed.


Lemma type_eq_q_add: forall Q t t' x v, ~ Theta.In x Q ->
    type_eq Q t t' -> type_eq (Theta.add x v Q) t t'.
Proof.
  intros. induction H0; simpl in *; try easy.
  constructor. constructor; try easy.
  constructor. constructor; try easy.
  split. apply nat_leq_q_add. easy. destruct H1; easy.
  apply nat_leq_q_add. easy. destruct H1; easy.
  split. apply nat_leq_q_add. easy. destruct H2; easy.
  apply nat_leq_q_add. easy. destruct H2; easy.
  constructor; try easy.
  split. apply nat_leq_q_add. easy. destruct H1; easy.
  apply nat_leq_q_add. easy. destruct H1; easy.
  split. apply nat_leq_q_add. easy. destruct H2; easy.
  apply nat_leq_q_add. easy. destruct H2; easy.
  constructor.
Qed.


(*
Definition union := list (list var).

Fixpoint union_find (env:union) (x:var) :=
    match env with [] => None
             | (xl::xll) => if find (fun y =>  Nat.eqb x y) xl then Some xl else union_find xll x
    end.

Fixpoint union_remove_find (env:union) (x:var) : option (list var * union) :=
    match env with [] => None
             | (xl::xll) => if find (fun y =>  Nat.eqb x y) xl then Some (xl,xll)
            else match union_remove_find xll x with None => None
                | Some (yl,yll) => Some (yl,xl::yll)
                 end
    end.

Fixpoint par_add (env:union) (x:var) (yl:list var) :=
    match env with [] => [(x::yl)]
                | (xl::xll) => if find (fun z =>  Nat.eqb x z) xl then (xl ++ yl)::xll else xl::(par_add xll x yl)
    end.

Definition union_add (env:union) (x y:var) :=
    match union_remove_find env y with None => par_add env x [y]
          | Some (xl,xll) => par_add xll x xl
    end.

Definition union_same (env:union) (x y:var) :=
   match union_find env x with None => False
                 | Some xl => if find (fun z => Nat.eqb y z) xl then True else False
    end.
*)
(*
Inductive ptr_mode_same (U:union) : ptrMode -> ptrMode -> Prop :=
  | ptr_mode_num : forall t l, ptr_mode_same U (Some (t,NumPtr l)) (Some (t,NumPtr l))
  | ptr_mode_var : forall t l h, union_same U l h -> ptr_mode_same U (Some (t,VarPtr l)) (Some (t,VarPtr h)).
*)

(*
Inductive subtypeRef (D : structdef) (U:union) (Q:theta) : type -> type -> Prop :=
  | SubTyReflNat :  subtypeRef D U Q TNat TNat
  | SubTypeReflPtr : forall pm pm' m t t', ptr_mode_same U pm pm'
       -> subtypeRef D U Q t t' -> subtypeRef D U Q (TPtr m pm t) (TPtr m pm' t').
 *)

Section Subtype. 

  Inductive subtype_core (Q:theta) : type -> type -> Prop :=
  | SubTyRefl : forall t, subtype_core Q t t
  | SubTyBot : forall m l h t,
      word_type t -> nat_leq Q (Num 0) l -> nat_leq Q h (Num 1) ->
      subtype_core Q (TPtr m t) (TPtr m (TArray l h t))
  | SubTyOne : forall m l h t,
      word_type t -> nat_leq Q l (Num 0) -> nat_leq Q (Num 1) h ->
      subtype_core Q (TPtr m (TArray l h t)) (TPtr m t)
  | SubTyOneNT : forall m l h t,
      word_type t -> nat_leq Q l (Num 0) -> nat_leq Q (Num 1) h ->
      subtype_core Q (TPtr m (TNTArray l h t)) (TPtr m t)
  | SubTySubsume : forall l h l' h' t m,
      nat_leq Q l l' -> nat_leq Q h' h ->
      subtype_core Q (TPtr m (TArray l h t)) (TPtr m (TArray l' h' t))
  | SubTyNtArray : forall l h l' h' t m,
      nat_leq Q l l' -> nat_leq Q h' h ->
      subtype_core Q (TPtr m (TNTArray l h t)) (TPtr m (TArray l' h' t))
  | SubTyNtSubsume : forall l h l' h' t m,
      nat_leq Q l l' -> nat_leq Q h' h ->
      subtype_core Q (TPtr m (TNTArray l h t)) (TPtr m (TNTArray l' h' t)).
  Hint Constructors subtype_core : ty.

  Lemma subtype_core_word_type : forall Q t1 t2,
      @subtype_core Q t1 t2 -> word_type t1 -> word_type t2.
  Proof.
    intros. inv H0. inv H. easy.
    inv H; try easy.
  Qed.

  Lemma subtype_core_word_type_1 : forall Q t1 t2,
      @subtype_core Q t1 t2 -> word_type t2 -> word_type t1.
  Proof.
    intros. inv H0. inv H. easy.
    inv H; try easy.
  Qed.
 
  Lemma subtype_core_trans : forall Q t t1 t',
      @subtype_core Q t t1 -> @subtype_core Q t1 t' -> @subtype_core Q t t'.
  Proof with (eauto with ty; try easy). 
    intros. inv H; inv H0...
  Qed.


  Inductive subtype (Q:theta) : type -> type -> Prop :=
  | SubCore : forall t t', @subtype_core Q t t' -> subtype Q t t'
  | SubTypeFunChecked : forall t t' tl tl' xl,
      word_type t ->
      Forall word_type tl ->
      @subtype empty_theta t t' ->
      Forall2 (@subtype empty_theta) tl' tl ->
      subtype Q (TPtr Checked (TFun xl t tl)) (TPtr Checked (TFun xl t' tl'))
  | SubTypeFunTainted : forall t t' tl tl' xl,
      word_type t -> 
      Forall word_type tl ->
      @subtype empty_theta t t' ->
      Forall2 (@subtype empty_theta) tl' tl ->
      subtype Q (TPtr Tainted (TFun xl t tl)) (TPtr Tainted (TFun xl t' tl')).

  Hint Constructors subtype : ty.

  Lemma subtype_core_type_1 : forall Q t1 t2, @subtype_core Q t1 t2 -> word_type t2 -> word_type t1.
  Proof.
    intros. inv H0. inv H. easy.
    inv H; try easy.
  Qed.

  Lemma subtype_word_type : forall Q t1 t2,
      @subtype Q t1 t2 -> word_type t1 -> word_type t2.
  Proof.
    intros. induction H; try easy.
    apply subtype_core_word_type with (Q:= Q) (t1 := t); auto.
  Qed.

  Lemma subtype_word_type_1 : forall Q t1 t2,
      @subtype Q t1 t2 -> word_type t2 -> word_type t1.
  Proof with (auto with subtype).
    intros. induction H; try easy.
    apply subtype_core_word_type_1 with (Q:=Q) (t2 := t'); auto.
  Qed.

  Lemma subtype_word_type_list : forall Q t1 t2,
      Forall2 (@subtype Q) t1 t2 -> Forall word_type t1 -> Forall word_type t2.
  Proof.
    intros. induction H. constructor.
    constructor. inv H0.
    eapply subtype_word_type. apply H. easy.
    apply IHForall2. inv H0. easy.
  Qed.

  Definition is_fun_ptr (t:type) :=
    match t with TPtr m (TFun xl t l) => True | _ => False end.

  Definition is_fun_ty (t:type) :=
    match t with (TFun xl t l) => True | _ => False end.

(*
  Definition word_type_b (t:type) := match t with TNat => true | TPtr _ _ => true | _ => false end.

  Fixpoint word_type_sub (t:type) :=
   match t with TNat => true
              | TPtr m ta => match ta with TNat => true
                                        | TPtr a b => true
                                        | TStruct T => true
                                        | (TArray b1 b2 t) => word_type_b t
                                        | (TNTArray b1 b2 t) => word_type_b t
                                        | (TFun xl t l) => (word_type_sub t && (forallb (fun a => word_type_sub a) l))
                              end
              | _ => false
  end.
*)

  Inductive Forall3 {A B C: Type} (R : A -> B -> C -> Prop): list A -> list B -> list C -> Prop :=
  | Forall3_nil : Forall3 R [] [] []
  | Forall3_cons : forall x y z l l' l'',
      R x y z -> Forall3 R l l' l'' -> Forall3 R (x::l) (y::l') (z::l'').

  Inductive subtype_order : theta -> type -> type -> type -> Prop :=
    subtype_order_1: forall Q t1 t2 t3,
        word_type t1 -> @subtype_core Q t1 t2 -> @subtype_core Q t2 t3 -> subtype_order Q t1 t2 t3

  | subtype_order_4: forall Q m t1 tl1 t2 tl2 t3 tl3 xl,
      word_type_sub t1 -> word_type_sub t2 -> word_type_sub t3 ->
      Forall word_type_sub tl1 -> Forall word_type_sub tl2 -> Forall word_type_sub tl3 -> 
      subtype_order empty_theta t1 t2 t3 -> Forall3 (subtype_order empty_theta) tl3 tl2 tl1 ->
      subtype_order Q (TPtr m (TFun xl t1 tl1)) (TPtr m (TFun xl t2 tl2)) (TPtr m (TFun xl t3 tl3)).


  Definition subtype_type_ind3
    : forall P : theta -> type -> type -> type -> Prop,
      (forall Q t1 t2 t3, 
          word_type t1 -> @subtype_core Q t1 t2 -> @subtype_core Q t2 t3 -> P Q t1 t2 t3) ->
      (forall Q m t1 tl1 t2 tl2 t3 tl3 xl,
          word_type_sub t1 -> word_type_sub t2 -> word_type_sub t3 ->
          Forall word_type_sub tl1 -> Forall word_type_sub tl2 -> Forall word_type_sub tl3 -> 
          subtype_order empty_theta t1 t2 t3 -> P empty_theta t1 t2 t3 
          -> Forall3 (subtype_order empty_theta) tl3 tl2 tl1 -> Forall3 (P empty_theta) tl3 tl2 tl1 ->
          P Q (TPtr m (TFun xl t1 tl1)) (TPtr m (TFun xl t2 tl2)) (TPtr m (TFun xl t3 tl3))) ->
      forall Q (t1 t2 t3:type), subtype_order Q t1 t2 t3 -> P Q t1 t2 t3.
  Proof.
    intros P ST1 ST4.
    refine
      (fix F Q t1 t2 t3 (Hw : subtype_order Q t1 t2 t3) {struct Hw} :=
         match Hw with
         | subtype_order_1 Q t1 t2 t3 Hw Hs1 Hs2 => ST1 Q t1 t2 t3 Hw Hs1 Hs2
         | subtype_order_4 Q m t1 tl1 t2 tl2 t3 tl3 xl Hw1 Hw2 Hw3 Hl1 Hl2 Hl3 Hs Hl
           => ST4 Q m t1 tl1 t2 tl2 t3 tl3 xl Hw1 Hw2 Hw3 Hl1 Hl2 Hl3 Hs _ Hl _
         end).
    - exact (F empty_theta t1 t2 t3 Hs).
    - induction Hl; constructor.
      exact (F empty_theta x y z H).
      inv Hl1. inv Hl2. inv Hl3.
      apply IHHl; try easy.
  Qed.

  Lemma subtype_core_fun_1 : forall Q t1 m2 t2 tl2 m3 t3 tl3 xl, 
      @subtype_core Q t1 (TPtr m2 (TFun xl t2 tl2)) ->
      @subtype Q (TPtr m2 (TFun xl t2 tl2)) (TPtr m3 (TFun xl t3 tl3)) ->
      @subtype Q t1 (TPtr m3 (TFun xl t3 tl3)).
  Proof.
    intros. inv H0. constructor.
    apply subtype_core_trans with (t1 := (TPtr m2 (TFun xl t2 tl2))); try easy.
    inv H.
    apply SubTypeFunChecked; try easy. inv H2. inv H2.
    inv H.
    apply SubTypeFunTainted; try easy.
    constructor. inv H2. inv H2.
  Qed.

  Lemma subtype_core_fun_2 : forall Q t1 m2 t2 tl2 m3 t3 tl3 xl, 
      @subtype Q (TPtr m2 (TFun xl t2 tl2)) (TPtr m3 (TFun xl t3 tl3))
      -> @subtype_core Q (TPtr m3 (TFun xl t3 tl3)) t1
      -> @subtype Q (TPtr m2 (TFun xl t2 tl2)) t1.
  Proof.
    intros. inv H. constructor.
    apply subtype_core_trans with (t1 := (TPtr m3 (TFun xl t3 tl3))); try easy.
    inv H0.
    apply SubTypeFunChecked; try easy. inv H2. 
    inv H0.
    apply SubTypeFunTainted; try easy.
    constructor. inv H2.
  Qed.


  Lemma subtype_trans : forall Q t1 t2 t3,
      subtype_order Q t1 t2 t3 ->
      @subtype Q t1 t2 -> @subtype Q t2 t3 -> @subtype Q t1 t3.
  Proof with (eauto with ty; try easy).
    intros. induction H using subtype_type_ind3.
    - constructor.
      apply subtype_core_trans with (t1 := t2); try easy.
    - inv H0. inv H10. easy. inv H1... inv H0...
      apply SubTypeFunChecked; try easy. apply IHsubtype_order; try easy.
      induction H9. constructor.
      inv H4. inv H5. inv H6.
      inv H19. inv H21. constructor.
      apply H0; try easy.
      inv H8. inv H17. inv H16.
      apply IHForall3; try easy. 
      inv H1.
      apply subtype_core_fun_2 with (m3 :=Tainted) (t3:=t2) (tl3:=tl2); try easy.
      apply SubTypeFunTainted; try easy.
      apply SubTypeFunTainted; try easy.
      apply IHsubtype_order; try easy.
      induction H9. constructor.
      inv H4. inv H5. inv H6.
      inv H19. inv H21. constructor.
      apply H0; try easy.
      inv H8. inv H17. inv H16.
      apply IHForall3; try easy. 
  Qed.

  Lemma subtype_refl : forall Q t,
      @subtype Q t t.
  Proof.
    auto with ty.
  Qed.

  Hint Resolve subtype_refl : ty.


  Lemma subtype_core_fun : forall Q xl t tl m ta,
         @subtype_core Q ta (TPtr m (TFun xl t tl)) 
               -> (exists yl tb tlb, ta = TPtr m (TFun yl tb tlb)).
  Proof.
   intros. inv H;simpl in *; try easy.
   exists xl, t, tl. easy.
  Qed.

  Lemma subtype_fun : forall Q xl t tl m ta,
           @subtype Q ta (TPtr m (TFun xl t tl)) 
               -> (exists yl tb tlb, ta = TPtr m (TFun yl tb tlb)).
  Proof.
   intros. inv H; try easy.
   eapply subtype_core_fun. apply H0.
   exists xl,t0,tl0. easy. 
   exists xl,t0,tl0. easy. 
  Qed.

  Lemma subtype_fun_1 : forall Q m yl tb tlb xl t ts, 
           @subtype Q (TPtr m (TFun yl tb tlb)) (TPtr m (TFun xl t ts))
               -> yl = xl /\ @subtype empty_theta tb t /\ Forall2 (@subtype empty_theta) ts tlb.
  Proof.
   intros. inv H; try easy.
   inv H0; try easy. split. easy. split. constructor. constructor. 
   induction ts;intros;simpl in *. constructor.
   constructor. constructor. constructor. easy.
  Qed.

Lemma subtype_nat: forall Q t, subtype Q t TNat -> t = TNat.
Proof.
  intros. inv H. inv H0. easy.
Qed.

Lemma subtype_nat_1: forall Q t, subtype Q TNat t -> t = TNat.
Proof.
  intros. inv H. inv H0. easy.
Qed.

Lemma subtype_core_q_empty: forall Q t t', subtype_core empty_theta t t' -> subtype_core Q t t'.
Proof.
  intros. remember empty_theta as Q'. induction H;intros;simpl in *;subst; try easy.
  constructor. 
  constructor; try easy.
  1-2:apply nat_leq_q_empty; easy.
  constructor; try easy.
  1-2:apply nat_leq_q_empty; easy.
  constructor; try easy.
  1-2:apply nat_leq_q_empty; easy.
  constructor; try easy.
  1-2:apply nat_leq_q_empty; easy.
  constructor; try easy.
  1-2:apply nat_leq_q_empty; easy.
  constructor; try easy.
  1-2:apply nat_leq_q_empty; easy.
Qed.

Lemma subtype_q_empty: forall Q t t', subtype empty_theta t t' -> subtype Q t t'.
Proof.
  intros. remember empty_theta as Q'. induction H;intros;simpl in *;subst.
  constructor. apply subtype_core_q_empty; try easy.
  apply SubTypeFunChecked; try easy.
  apply SubTypeFunTainted; try easy.
Qed.

Lemma subtype_core_q_eq: forall Q Q' t t', Theta.Equal Q Q' ->
      subtype_core Q t t' -> subtype_core Q' t t'.
Proof with (eauto with ty; try easy). 
  intros. induction H0;try easy.
  constructor.
  apply SubTyBot; try easy.
  eapply nat_leq_q_eq; eauto. 
  eapply nat_leq_q_eq; eauto. 
  apply SubTyOne; try easy.
  eapply nat_leq_q_eq; eauto. 
  eapply nat_leq_q_eq; eauto. 
  apply SubTyOneNT; try easy.
  eapply nat_leq_q_eq; eauto. 
  eapply nat_leq_q_eq; eauto. 
  apply SubTySubsume; try easy.
  eapply nat_leq_q_eq; eauto. 
  eapply nat_leq_q_eq; eauto. 
  apply SubTyNtArray; try easy.
  eapply nat_leq_q_eq; eauto. 
  eapply nat_leq_q_eq; eauto. 
  apply SubTyNtSubsume; try easy.
  eapply nat_leq_q_eq; eauto. 
  eapply nat_leq_q_eq; eauto. 
Qed.

Lemma subtype_core_q_conv: forall Q t t' x v, 0 <= v ->
      subtype_core (Theta.add x GeZero Q) t t'
        -> subtype_core (Theta.add x (NumEq (Num v)) Q) t t'.
Proof with (eauto with ty; try easy). 
  intros. induction H0;try easy.
  constructor.
  apply SubTyBot; try easy.
  eapply nat_leq_q_conv; eauto. 
  eapply nat_leq_q_conv; eauto. 
  apply SubTyOne; try easy.
  eapply nat_leq_q_conv; eauto. 
  eapply nat_leq_q_conv; eauto. 
  apply SubTyOneNT; try easy.
  eapply nat_leq_q_conv; eauto. 
  eapply nat_leq_q_conv; eauto. 
  apply SubTySubsume; try easy.
  eapply nat_leq_q_conv; eauto. 
  eapply nat_leq_q_conv; eauto. 
  apply SubTyNtArray; try easy.
  eapply nat_leq_q_conv; eauto. 
  eapply nat_leq_q_conv; eauto. 
  apply SubTyNtSubsume; try easy.
  eapply nat_leq_q_conv; eauto. 
  eapply nat_leq_q_conv; eauto. 
Qed.

Lemma subtype_q_eq: forall Q Q' t t', Theta.Equal Q Q' ->
      subtype Q t t' -> subtype Q' t t'.
Proof.
  intros. induction H0;try easy.
  constructor. eapply subtype_core_q_eq; eauto.
  apply SubTypeFunChecked; try easy.
  apply SubTypeFunTainted; try easy.
Qed.

Lemma subtype_q_conv: forall Q t t' x v, 0 <= v ->
      subtype (Theta.add x GeZero Q) t t' 
      -> subtype (Theta.add x (NumEq (Num v)) Q) t t'.
Proof.
  intros. remember (Theta.add x GeZero Q) as Q'.
  induction H0;try easy; subst.
  constructor. eapply subtype_core_q_conv; eauto.
  apply SubTypeFunChecked; try easy.
  apply SubTypeFunTainted; try easy.
Qed.

Lemma subtype_core_nt: forall Q m l h t t', subtype_core Q t' (TPtr m (TNTArray l h t)) 
      -> (exists l' h', t' = TPtr m (TNTArray l' h' t)).
Proof.
  intros. inv H. exists l,h. easy.
  inv H2. inv H2. exists l0,h0. easy. 
Qed.

Lemma subtype_core_q_add: forall Q t t' x v, ~ Theta.In x Q ->
    subtype_core Q t t' -> subtype_core (Theta.add x v Q) t t'.
Proof.
  intros. induction H0; simpl in *; eauto with ty.
  apply SubTyBot; try easy.
  apply nat_leq_q_add; try easy.
  apply nat_leq_q_add; try easy.
  apply SubTyOne; try easy.
  apply nat_leq_q_add; try easy.
  apply nat_leq_q_add; try easy.
  apply SubTyOneNT; try easy.
  apply nat_leq_q_add; try easy.
  apply nat_leq_q_add; try easy.
  apply SubTySubsume; try easy.
  apply nat_leq_q_add; try easy.
  apply nat_leq_q_add; try easy.
  apply SubTyNtArray; try easy.
  apply nat_leq_q_add; try easy.
  apply nat_leq_q_add; try easy.
  apply SubTyNtSubsume; try easy.
  apply nat_leq_q_add; try easy.
  apply nat_leq_q_add; try easy.
Qed.


Lemma subtype_core_q_add_1: forall Q t t' x v, ~ In x (freeTypeVars t) -> ~ In x (freeTypeVars t) ->
    subtype_core (Theta.add x v Q) t t' -> subtype_core Q t t'.
Proof.
Admitted.

Lemma subtype_q_add: forall Q t t' x v, ~ Theta.In x Q ->
    subtype Q t t' -> subtype (Theta.add x v Q) t t'.
Proof.
  intros. induction H0; simpl in *; eauto with ty.
  constructor. apply subtype_core_q_add; try easy.
Qed.

End Subtype.

#[export] Hint Constructors subtype_core : ty.
#[export] Hint Constructors subtype : ty.
#[export] Hint Resolve subtype_refl : ty.

(* Defining stack. *)
Module Stack := Map.Make Nat_as_OT.

Definition stack := Stack.t (Z * type).

Definition empty_stack := @Stack.empty (Z * type).

Definition arg_stack := Stack.t bound.

Definition empty_arg_stack := @Stack.empty bound.

Section StackWt.
  Variable D : structdef.
  Variable m : mode.
  Definition stack_wt(S:stack) :=
    forall x v t, Stack.MapsTo x (v,t) S -> word_type t /\ type_wf D m t /\ simple_type t.
End StackWt.

Definition theta_wt (Q:theta) (env:env) (S:stack) :=
  (forall x, Theta.In x Q <-> Env.MapsTo x TNat env)
  /\ (forall x n, Theta.MapsTo x GeZero Q ->
                     Stack.MapsTo x (n,TNat) S -> 0 <= n)
  /\ (forall x n, Stack.MapsTo x (n,TNat) S -> Theta.MapsTo x (NumEq (Num n)) Q).

(*
Definition dyn_env := Stack.t type.

Definition empty_dyn_env := @Stack.empty type.


Definition cast_bound (s:stack) (b:bound) : option bound :=
  match b with
  | Num n => Some (Num n)
  | Var x n => (match (Stack.find x s) with Some (v,t) => Some (Num (n+v)) | None => None end)
  | NVar m x n => (match (Stack.find x s) with Some (v,t) => Some (Num (m+v+n)) | None => None end)
  | VVar x y n => (match (Stack.find x s) with
                    Some (v,t) => (match (Stack.find y s) with Some (v',t') => Some (Num (v+v'+n)) | None => None end)
                    | None => None end)
   end.


*)

Inductive expression : Type :=
  | ELit : Z -> type -> expression
  | EVar : var -> expression
  | EStrlen : var -> expression
  | ECall : expression -> list expression -> expression
  | ERet : var -> Z* type -> expression -> expression (* return new value, old value and the type. *)
  | EDynCast : type -> expression -> expression
  | ELet : var -> expression -> expression -> expression
  | EMalloc : mode -> type -> expression
  | ECast : type -> expression -> expression
  | EPlus : expression -> expression -> expression
  | EFieldAddr : expression -> field -> expression
  | EDeref : expression -> expression (*  * e *)
  | EAssign : expression -> expression -> expression (* *e = e *)
  | EIfDef : var -> expression -> expression -> expression (* if * x then e1 else e2. *)
(*
  | EIfPtrEq : expression -> expression -> expression -> expression -> expression (* if e1 = e2 then e3 else e4. *)
  | EIfPtrLt : expression -> expression -> expression -> expression -> expression (* if e1 < e2 then e3 else e4. *)
*)
  | EIf : expression -> expression -> expression -> expression (* if e1 then e2 else e3. *)
  | EUnchecked : list var -> type -> expression -> expression
  | Echecked : list var -> type -> expression -> expression.

Definition funElem : Type := (list (var * type) * type * expression).


Definition FEnv : Type := mode -> Z -> option funElem. (* first Z is a permission and second z is address *)

(* Parameter fenv : FEnv. *)

Definition Ffield : Type := Z -> option Z.

(*
Inductive gen_sub_bound : bn_env -> bound -> bound -> bn_env -> Prop :=
    gen_sub_num : forall env n, gen_sub_bound env (Num n) (Num n) env
  | gen_sub_var_1 : forall env x n m, ~ Env.In x env -> gen_sub_bound env (Var x n) (Num m) (Env.add x (Num (m - n)) env)
  | gen_sub_var_2 : forall env x n m, Env.MapsTo x (Num (m - n)) env -> gen_sub_bound env (Var x n) (Num m) env
  | gen_sub_var_3 : forall env x y n, ~ Env.In x env -> gen_sub_bound env (Var x n) (Var y n) (Env.add x (Var y 0) env)
  | gen_sub_var_4 : forall env x y n, Env.MapsTo x (Var y 0) env -> gen_sub_bound env (Var x n) (Var y n) env.

Inductive gen_sub_type : bn_env -> type -> type -> bn_env -> Prop :=
   gen_sub_nat : forall env, gen_sub_type env TNat TNat env
 | gen_sub_ptr : forall env env' m t t', gen_sub_type env t t' env' -> gen_sub_type env (TPtr m t) (TPtr m t') env'
 | gen_sub_struct : forall env T, gen_sub_type env (TStruct T) (TStruct T) env
 | gen_sub_array : forall env env1 env2 env3 b1 b2 c1 c2 t t', gen_sub_bound env b1 c1 env1 -> gen_sub_bound env1 b2 c2 env2 ->
                       gen_sub_type env2 t t' env3 -> gen_sub_type env (TArray b1 b2 t) (TArray c1 c2 t') env3
 | gen_sub_ntarray : forall env env1 env2 env3 b1 b2 c1 c2 t t', gen_sub_bound env b1 c1 env1 -> gen_sub_bound env1 b2 c2 env2 ->
                       gen_sub_type env2 t t' env3 -> gen_sub_type env (TNTArray b1 b2 t) (TNTArray c1 c2 t') env3
 | gen_sub_fun : forall env env1 env2 env3 b c ts1 ts2 t1 t2, gen_sub_bound env b c env1 ->
              gen_sub_type_list env1 ts1 ts2 env2 -> gen_sub_type env2 t1 t2 env3 -> gen_sub_type env (TFun b t1 ts1) (TFun c t2 ts2) env3

with gen_sub_type_list : bn_env -> list type -> list type -> bn_env -> Prop :=
 | gen_sub_empty: forall env, gen_sub_type_list env [] [] env
 | gen_sub_many : forall env env1 env2 t1 ts1 t2 ts2, gen_sub_type env t1 t2 env1 -> gen_sub_type_list env1 ts1 ts2 env2
                   -> gen_sub_type_list env (t1::ts1) (t2::ts2) env2.

Definition subst_fun_bound (bv:bn_env) (b:bound) :=
  match b with
    Num n => (Num n)
  | Var y n =>
      match Env.find y bv with
        None => Var y n
      | Some b1 =>
          match b1 with
            Num m => Num (m+n)
          | Var x m => Var x (m + n)
          end
      end
  end.

Inductive subst_fun_type : bn_env -> type -> type -> Prop :=
  subst_fun_nat : forall env, subst_fun_type env TNat TNat
| subst_fun_ptr : forall env m t t',
    subst_fun_type env t t' ->
    subst_fun_type env (TPtr m t) (TPtr m t')
| subst_fun_struct : forall env T,
    subst_fun_type env (TStruct T) (TStruct T)
| subst_fun_array : forall env b1 b2 c1 c2 t t',
    subst_fun_bound env b1 = c1 ->
    subst_fun_bound env b2 = c2 ->
    subst_fun_type env t t' ->
    subst_fun_type env (TArray b1 b2 t) (TArray c1 c2 t')
| subst_fun_ntarray : forall env b1 b2 c1 c2 t t',
    subst_fun_bound env b1 = c1 ->
    subst_fun_bound env b2 = c2 ->
    subst_fun_type env t t' ->
    subst_fun_type env (TNTArray b1 b2 t) (TNTArray c1 c2 t')
| subst_fun_fun : forall env b c ts1 ts2 t1 t2, 
    subst_fun_bound env b = c ->
    subst_fun_type_list env ts1 ts2 ->
    subst_fun_type env t1 t2 ->
    subst_fun_type env (TFun b t1 ts1) (TFun c t2 ts2)

with subst_fun_type_list : bn_env -> list type -> list type -> Prop :=
 | subst_fun_empty : forall env, subst_fun_type_list env [] []
| subst_fun_many : forall env t1 ts1 t2 ts2,
    subst_fun_type env t1 t2 ->
    subst_fun_type_list env ts1 ts2 ->
    subst_fun_type_list env (t1::ts1) (t2::ts2).

Definition eq_types (ts1 ts2: list type) :=
  exists env, gen_sub_type_list empty_bn_env ts1 ts2 env /\ subst_fun_type_list env ts1 ts2.
*)
Definition to_tfun (b:bound) (tvl: list (var * type)) (t:type) := TFun (fst (List.split tvl)) t (snd (List.split tvl)).

Inductive gen_arg_env : env -> list (var * type) -> env -> Prop :=
    gen_arg_env_empty : forall env, gen_arg_env env [] env
  | gen_ar_env_many : forall env x t tvl env',
      gen_arg_env env tvl env' -> gen_arg_env env ((x,t)::tvl) (Env.add x t env').

(* Well-formedness definition. *)
Definition is_check_array_ptr (t:type) : Prop :=
  match t with
  | TPtr Checked (TArray l h t') => True
  | TPtr Checked (TNTArray l h t') => True
  | TPtr Tainted (TArray l h t') => True
  | TPtr Tainted (TNTArray l h t') => True
  | _ => False
  end.

Definition is_array_ptr (t:type) : Prop :=
  match t with
  | TPtr _ (TArray l h t') => True
  | TPtr _ (TNTArray l h t') => True
  | _ => False
  end.


Definition simple_option (D : structdef) (a: (Z*type)) :=
  match a with  (v,t) => word_type t /\ type_wf D Checked t /\ simple_type t
  end.


(* Standard substitution.
   In a let, if the bound variable is the same as the one we're substituting,
   then we don't substitute under the lambda. *)
(*
Definition list_diff (l1 l2:list var) :=
   List.filter (fun n => (List.forallb (fun v => negb (Nat.eqb v n)) l2)) l1.

Lemma list_diff_prop l1 l2 n : In n (list_diff l1 l2) <-> In n l1 /\ ~ In n l2.
Proof.
unfold list_diff.
 rewrite filter_In. rewrite forallb_forall.
 split. intros. destruct H. split. easy.
 specialize (H0 n). intros R. apply H0 in R.
 apply negb_true_iff in R.
 apply Nat.eqb_neq in R. easy.
 intros. destruct H. split. easy.
 intros.
 apply negb_true_iff.
 apply Nat.eqb_neq.
 destruct (Nat.eq_dec x n) eqn:eq1. subst. easy. easy.
Qed.. easy.
Qed.
*)

(* Definition free var f *)
Fixpoint freeVars (e : expression) := 
  match e with ELit a t => freeTypeVars t
          | EVar x => [x]
          | EStrlen x => [x]
          | ECall e1 el => freeVars e1 ++ (fold_right (fun b a => freeVars b ++ a) [] el)
          | ERet x (n,t) e => set_diff Nat.eq_dec (freeTypeVars t ++ freeVars e) [x]
          | EDynCast t e => freeTypeVars t ++ freeVars e
          | ELet x e1 e2 => (freeVars e1) ++ set_diff Nat.eq_dec (freeVars e2) [x] 
          | EMalloc m t => freeTypeVars t
          | ECast t e => freeTypeVars t ++ freeVars e
          | EPlus e1 e2 => freeVars e1 ++ freeVars e2
          | EFieldAddr e f => freeVars e
          | EDeref e => freeVars e
          | EAssign e1 e2 => freeVars e1 ++ freeVars e2
          | EIfDef x e1 e2 => [x] ++ freeVars e1 ++ freeVars e2
          | EIf e1 e2 e3 => freeVars e1 ++ freeVars e2 ++ freeVars e3
          | EUnchecked vl t e => freeVars e
          | Echecked vl t e => freeVars e
end.

Definition list_sub (l1 l2:list var) := (forall x, In x l1 -> In x l2).

Definition env_wf (e:expression) (env:env) := (forall x, In x (freeVars e) -> Env.In x env).

(** Values, [v], are expressions [e] which are literals. *)

Inductive value (D : structdef) : expression -> Prop :=
  VLit : forall (n : Z) (t : type),
    word_type t ->
    type_wf D Checked t ->
    simple_type t ->
    value D (ELit n t).

#[export] Hint Constructors value.

(** Note: Literal is a less strong version of value that doesn't
    enforce the syntactic constraints on the literal type. *)

Inductive literal : expression -> Prop :=
  Lit : forall (n : Z) (t : type),
    literal (ELit n t).

#[export] Hint Constructors literal.

(** * Dynamic Semantics *)

(** Heaps, [H], are a list of literals indexed by memory location.
    Memory locations are just natural numbers, and literals are
    numbers paired with their type (same as [ELit] constructor).
    Addresses are offset by 1 -- looking up address 7 will translate
    to index 6 in the list.

    Heaps also have a well-formedness predicate, which says that
    all memory locations must be annotated with a well-formed word
    type.

    Finally, the only operation we can perform on a heap is allocation.
    This operation is defined by the partial function [allocate]. This
    function takes [D] a structdef, [H] a heap, and [w] a (compound) type.
    The function is total assuming usual well-formedness conditions of [D] and
    [w]. It gives back a pair [(base, H')] where [base] is the base pointer for
    the allocated region and [H'] is [H] with the allocation.
*)


Module Heap := Map.Make Z_as_OT.

Definition heap : Type := Heap.t (Z * type).

(** Real Heaps, [R], consist of 2 heaps tha  t represents (checked * tainted)
    heaps
 *)
Definition real_heap : Type := heap * heap.

Section allocation.
  Import ListNotations.
  Import MonadNotation.
  Local Open Scope monad_scope.

  Print replicate.
  Definition Zreplicate (z:Z) (T : type) : (list type) :=
    match z with
    |Z.pos p => (replicate (Pos.to_nat p) T)
    |_ => []
    end.

  (* Changed this, to return the lower bound *)
  Definition allocate_meta (D : structdef) (w : type)
    : option (Z * list type) :=
    match w with
    | TStruct T =>
        fs <- StructDef.find T D ;;
        ret (0, List.map snd (Fields.elements fs))
    | TArray (Num l) (Num h) T =>
        Some (l, Zreplicate (h - l) T)
    | TNTArray (Num l) (Num h) T =>
        Some (l, Zreplicate (h - l + 1) T)
    | _ => Some (0, [w])
    end.


  Definition allocate_meta_no_bounds (D : structdef) (w : type)
    : option (list type) :=
    match (allocate_meta D w) with
    | Some( _ , x) => Some x
    | None => None
    end.

  Lemma allocate_meta_implies_allocate_meta_no_bounds : forall D w ts b,
      allocate_meta D w = Some (b, ts) -> allocate_meta_no_bounds D w = Some ts.
  Proof.
    intros. unfold allocate_meta_no_bounds. rewrite H. reflexivity.
  Qed.

  (* allocate_meta can succeed with bad bounds. allocate itself shouldn't *)
  Definition allocate (D : structdef) (H : heap) (w : type) : option (Z * heap) :=
    let H_size := Z.of_nat(Heap.cardinal H) in
    let base   := H_size + 1 in
    match allocate_meta D w with
    | Some (0, am) =>
        let (_, H') := List.fold_left
                         (fun (acc : Z * heap) (t : type) =>
                            let (sizeAcc, heapAcc) := acc in
                            let sizeAcc' := sizeAcc + 1 in
                            let heapAcc' := Heap.add sizeAcc' (0, t) heapAcc in
                            (sizeAcc', heapAcc'))
                         am
                         (H_size, H)
        in
        ret (base, H')
    | _ => None
    end.

End allocation.

(** Results, [r], are an expression ([RExpr]), null dereference error ([RNull]),
    or array out-of-bounds error ([RBounds]).
 *)

Inductive result : Type :=
  | RExpr : expression -> result
  | RNull : result
  | RBounds : result.

(** Contexts, [E], are expressions with a hole in them. They are used in the standard way,
    for lifting a small-step reduction relation to compound expressions.

    We define two functions on contexts: [in_hole] and [mode_of]. The [in_hole] function takes a context,
    [E] and an expression [e] and produces an expression [e'] which is [E] with its hole filled by [e].
    The [mode_of] function takes a context, [E], and returns [m] (a mode) indicating whether the context has a
    subcontext which is unchecked. *)

Inductive ctxt : Type :=
  | CHole : ctxt
  | CLet : var -> ctxt -> expression -> ctxt
  | CCall : ctxt -> list expression -> ctxt
  | CPlusL : ctxt -> expression -> ctxt
  | CPlusR : Z -> type -> ctxt -> ctxt
  | CFieldAddr : ctxt -> field -> ctxt
  | CDynCast : type -> ctxt -> ctxt
  | CCast : type -> ctxt -> ctxt
  | CDeref : ctxt -> ctxt
  | CAssignL : ctxt -> expression -> ctxt
  | CAssignR : Z -> type -> ctxt -> ctxt
(*
  | CIfEqL : ctxt -> expression -> expression -> expression -> ctxt
  | CIfEqR : expression -> ctxt -> expression -> expression -> ctxt
  | CIfLtL : ctxt -> expression -> expression -> expression -> ctxt
  | CIfLtR : expression -> ctxt -> expression -> expression -> ctxt
*)
  | CIf : ctxt -> expression -> expression -> ctxt
  | CUnchecked : list var -> type -> ctxt -> ctxt
  | Cchecked : list var -> type -> ctxt -> ctxt.

Fixpoint in_hole (e : expression) (E : ctxt) : expression :=
  match E with
  | CHole => e
  | CLet x E' e' => ELet x (in_hole e E') e'
  | CCall E' es => ECall (in_hole e E') es
  | CPlusL E' e' => EPlus (in_hole e E') e'
  | CPlusR n t E' => EPlus (ELit n t) (in_hole e E')
  | CFieldAddr E' f => EFieldAddr (in_hole e E') f
  | CDynCast t E' => EDynCast t (in_hole e E')
  | CCast t E' => ECast t (in_hole e E')
  | CDeref E' => EDeref (in_hole e E')
  | CAssignL E' e' => EAssign (in_hole e E') e'
  | CAssignR n t E' => EAssign (ELit n t) (in_hole e E')
  | CIf E' e1 e2 => EIf (in_hole e E') e1 e2
(*
  | CIfEqL E' e1 e2 e3 => EIfPtrEq (in_hole e E') e1 e2 e3
  | CIfEqR e1 E' e2 e3 => EIfPtrEq e1 (in_hole e E') e2 e3
  | CIfLtL E' e1 e2 e3 => EIfPtrLt (in_hole e E') e1 e2 e3
  | CIfLtR e1 E' e2 e3 => EIfPtrLt e1 (in_hole e E') e2 e3
*)
  | CUnchecked vl t E' => EUnchecked vl t (in_hole e E')
  | Cchecked vl t E' => Echecked vl t (in_hole e E')
  end.

(* the top mode is always checked mode. *)
Fixpoint mode_of' (E : ctxt) (m:mode) : mode :=
  match E with
  | CHole => m
  | CLet _ E' _ => mode_of' E' m
  | CCall E' _ => mode_of' E' m
  | CPlusL E' _ => mode_of' E' m
  | CPlusR _ _ E' => mode_of' E' m
  | CFieldAddr E' _ => mode_of' E' m
  | CDynCast _ E' => mode_of' E' m
  | CCast _ E' => mode_of' E' m
  | CDeref E' => mode_of' E' m
  | CAssignL E' _ => mode_of' E' m
  | CAssignR _ _ E' => mode_of' E' m
  | CIf E' e1 e2 => mode_of' E' m
(*
  | CIfEqL E' e1 e2 e3 => mode_of E'
  | CIfEqR e1 E' e2 e3 => mode_of E'
  | CIfLtL E' e1 e2 e3 => mode_of E'
  | CIfLtR e1 E' e2 e3 => mode_of E'
*)
  | CUnchecked vl t E' => mode_of' E' Unchecked
  | Cchecked vl t E' => mode_of' E' Checked
  end.
Definition mode_of (E: ctxt) := mode_of' E Checked.


Fixpoint compose (E_outer : ctxt) (E_inner : ctxt) : ctxt :=
  match E_outer with
  | CHole => E_inner
  | CLet x E' e' => CLet x (compose E' E_inner) e'
  | CCall E' e' => CCall (compose E' E_inner) e'
  | CPlusL E' e' => CPlusL (compose E' E_inner) e'
  | CPlusR n t E' => CPlusR n t (compose E' E_inner)
  | CFieldAddr E' f => CFieldAddr (compose E' E_inner) f
  | CDynCast t E' => CDynCast t (compose E' E_inner)
  | CCast t E' => CCast t (compose E' E_inner)
  | CDeref E' => CDeref (compose E' E_inner)
  | CAssignL E' e' => CAssignL (compose E' E_inner) e'
  | CAssignR n t E' => CAssignR n t (compose E' E_inner)

  | CIf E' e1 e2 => CIf (compose E' E_inner) e1 e2
(*
  | CIfEqL E' e1 e2 e3 => CIfEqL (compose E' E_inner) e1 e2 e3
  | CIfEqR e1 E' e2 e3 => CIfEqR e1 (compose E' E_inner) e2 e3
  | CIfLtL E' e1 e2 e3 => CIfLtL (compose E' E_inner) e1 e2 e3
  | CIfLtR e1 E' e2 e3 => CIfLtR e1 (compose E' E_inner) e2 e3
*)
  | CUnchecked vl t E' => CUnchecked vl t (compose E' E_inner)
  | Cchecked vl t E' => Cchecked vl t (compose E' E_inner)
  end.

Inductive expr_wf (D : structdef) : mode -> expression -> Prop :=
  | WFELit : forall m n t,
    word_type t ->
    type_wf D m t ->
    simple_type t ->
    expr_wf D m (ELit n t)
  | WFEVar : forall m x,
      expr_wf D m (EVar x)
  | WFEStr : forall m x,
      expr_wf D m (EStrlen x)
  | WFECall : forall m xe el,
      expr_wf D m xe ->
      (forall e, In e el -> (exists n t, e = ELit n t) \/ (exists y, e = EVar y)) ->
      expr_wf D m (ECall xe el)
  | WFRet : forall m x old e, simple_option D (old) -> expr_wf D m e -> expr_wf D m (ERet x old e)
  | WFEDynCast : forall m t e,
     is_array_ptr t -> type_wf D m t -> expr_wf D m e -> expr_wf D m (EDynCast t e)
  | WFELet : forall m x e1 e2,
      expr_wf D m e1 ->
      expr_wf D m e2 ->
      expr_wf D m (ELet x e1 e2)
  | WFEIFDef : forall m x e1 e2,
      expr_wf D m e1 ->
      expr_wf D m e2 ->
      expr_wf D m (EIfDef x e1 e2)
  | WFEIF : forall m e1 e2 e3,
      expr_wf D m e1 ->
      expr_wf D m e2 ->
      expr_wf D m e3 ->
      expr_wf D m (EIf e1 e2 e3)
(*
  | WFEIFEq : forall e1 e2 e3 e4,
      expr_wf D e1 ->
      expr_wf D e2 ->
      expr_wf D e3 ->
      expr_wf D e4 ->
      expr_wf D (EIfPtrLt e1 e2 e3 e4)
  | WFEIFLt : forall e1 e2 e3 e4,
      expr_wf D e1 ->
      expr_wf D e2 ->
      expr_wf D e3 ->
      expr_wf D e4 ->
      expr_wf D (EIfPtrEq e1 e2 e3 e4)
*)
  | WFEMalloc : forall m m' w,
      type_wf D m w -> expr_wf D m' (EMalloc m w)
  | WFECast : forall m t e,
      word_type t ->
      type_wf D m t ->
      expr_wf D m e ->
      expr_wf D m (ECast t e)
  | WFEPlus : forall m e1 e2,
      expr_wf D m e1 ->
      expr_wf D m e2 ->
      expr_wf D m (EPlus e1 e2)
  | WFEFieldAddr : forall m e f,
      expr_wf D m e ->
      expr_wf D m (EFieldAddr e f)
  | WFEDeref : forall m e,
      expr_wf D m e ->
      expr_wf D m (EDeref e)
  | WFEAssign : forall m e1 e2,
      expr_wf D m e1 ->
      expr_wf D m e2 ->
      expr_wf D m (EAssign e1 e2)
  | WFEUnchecked : forall m tvl t e,
      word_type t ->
      type_wf D Unchecked t ->
      expr_wf D Unchecked e ->
      expr_wf D m (EUnchecked tvl t e)
  | WFEchecked : forall m tvl t e,
      word_type t ->
      type_wf D Unchecked t ->
      expr_wf D Checked e ->
      expr_wf D m (Echecked tvl t e).

Lemma hole_is_id : forall e,
    in_hole e CHole = e.
Proof.
  intros.
  reflexivity.
Qed.


Lemma compose_correct : forall E_outer E_inner e0,
    in_hole (in_hole e0 E_inner) E_outer = in_hole e0 (compose E_outer E_inner).
Proof.
  intros.
  induction E_outer; try reflexivity; try (simpl; rewrite IHE_outer; reflexivity).
Qed.

Lemma expr_wf_in_hole : forall E D m m' e, mode_of' E m = m' -> expr_wf D m (in_hole e E) -> expr_wf D m' e.
Proof.
 induction E; intros; unfold mode_of in *; simpl in *; try easy.
 subst. easy.
 inv H0. apply IHE with (m' :=  (mode_of' E m)) in H4; try easy.
 inv H0. apply IHE with (m' :=  (mode_of' E m)) in H4; try easy.
 inv H0. apply IHE with (m' :=  (mode_of' E m)) in H4; try easy.
 inv H0. apply IHE with (m' :=  (mode_of' E m)) in H5; try easy.
 inv H0. apply IHE with (m' :=  (mode_of' E m)) in H3; try easy.
 inv H0. apply IHE with (m' :=  (mode_of' E m)) in H6; try easy.
 inv H0. apply IHE with (m' :=  (mode_of' E m)) in H6; try easy.
 inv H0. apply IHE with (m' :=  (mode_of' E m)) in H3; try easy.
 inv H0. apply IHE with (m' :=  (mode_of' E m)) in H4; try easy.
 inv H0. apply IHE with (m' :=  (mode_of' E m)) in H5; try easy.
 inv H0. apply IHE with (m' :=  (mode_of' E m)) in H5; try easy.
 inv H0. apply IHE with (m' :=  (mode_of' E Unchecked)) in H7; try easy.
 inv H0. apply IHE with (m' :=  (mode_of' E Checked)) in H7; try easy.
Qed.

(*
Lemma compose_unchecked : forall m E_outer E_inner,
    mode_of (compose E_outer E_inner) Checked = mode_of E_inner Checked.
Proof.
  intros.
  induction E_outer; try reflexivity; try (simpl; rewrite IHE_outer; reflexivity); try assumption.
  simpl.
Qed.
*)
(* TODO: say more *)

(*
Fixpoint eval_type_bound (s:stack) (t:type) :=
  match t with
  | TNat => Some TNat
  | TPtr c t =>
      match eval_type_bound s t with
      | None => None
      | Some t' => Some (TPtr c t') end
  | TArray l h t =>
      match eval_type_bound s t with
      | None => None
      | Some t' =>
          match (eval_bound s l,eval_bound s h) with
          | (Some l', Some h') => Some (TArray l' h' t')
          | (_,_) => None end
      end
  | TNTArray l h t =>
      match eval_type_bound s t with
      | None => None
      | Some t' =>
          match (eval_bound s l,eval_bound s h) with
          | (Some l', Some h') => Some (TNTArray l' h' t')
          | (_,_) => None end
      end

  | TStruct T => Some (TStruct T)
  | TFun b [] t ts =>
      match (eval_bound s b,eval_type_bound s t) with
        | (Some b',Some t') =>
            match (fold_right
                     (fun ta r =>
                        match r with
                        | None => None
                        | Some l =>
                            match eval_type_bound s ta with
                            | None => None
                            | Some ta' => Some (ta' :: l)
                            end
                        end)
                     (Some []) ts)
            with
            | None => None
            | Some ts' => Some (TFun b' [] t' ts')
            end
      | _ => None end
   | _ => None
  end.
*)
(*
Definition eval_base (s:stack) (b:ptrMode) : ptrMode :=
   match b with None => None
             | Some (t,NumPtr x) => Some (t, NumPtr x)
             | Some (t,VarPtr x) => match (Stack.find x s) with Some (v,ta) => Some (t,NumPtr v) | _ => None end
   end.
*)

(*
Lemma eval_type_bound_array_ptr : forall s t,
    eval_type_bound s t = None -> (exists  c l h t', t = TPtr c (TArray l h t') \/ t = TPtr c (TNTArray l h t')).
Proof.
 intros. unfold eval_type_bound in H.
 destruct t; inversion H.
 destruct t; inversion H.
 exists m. exists b. exists b0. exists t.
 left. reflexivity.
 exists m. exists b. exists b0. exists t.
 right. reflexivity.
Qed.
*)

Definition NTHit (s : stack) (x : var) : Prop :=
  match Stack.find x s with
  | Some (v,TPtr m (TNTArray l (Num 0) t)) => True
  | _ => False
  end.

Definition add_nt_one (s : stack) (x:var) : stack :=
   match Stack.find x s with | Some (v,TPtr m (TNTArray l (Num h) t))
                         => Stack.add x (v,TPtr m (TNTArray l (Num (h+1)) t)) s
                              (* This following case will never happen since the type in a stack is always evaluated. *)
                             | _ => s
   end.

Definition is_rexpr (r : result) : Prop :=
  match r with
    RExpr x => True
  | _ => False
  end.


Definition sub_bound (b:bound) (n:Z) : (bound) :=
  match b with
    Num m => Num (m - n)
  | Var x m => Var x (m - n)
  end.

Definition sub_type_bound (t:type) (n:Z) : type :=
  match t with
  | TPtr Checked (TArray l h t1) =>
      TPtr Checked (TArray (sub_bound l n) (sub_bound h n) t1)
  | TPtr Checked (TNTArray l h t1) =>
      TPtr Checked (TNTArray (sub_bound l n) (sub_bound h n) t1)
  | _ => t
  end.

Definition malloc_bound (t:type) : Prop :=
   match t with (TArray (Num l) (Num h) t) => (l = 0 /\ h > 0)
              | (TNTArray (Num l) (Num h) t) => (l = 0 /\ h > 0)
              | _ => True
   end.

Definition change_strlen_stack (s:stack) (x : var) (m:mode) (t:type) (l n n' h:Z) :=
     if n' <=? h then s else @Stack.add (Z * type) x (n,TPtr m (TNTArray (Num l) (Num n') t)) s.

Fixpoint gen_stack (vl:list var)  (es:list expression) (e:expression) : option expression :=
  match vl with
    [] => Some e
  | (v::vl') =>
      match es with
        [] => None
      | e1::el =>
          match gen_stack vl' el e with
            None => None
          | Some new_e => Some (ELet v e1 new_e)
          end
      end
  end.


Definition get_high_ptr (t : type) :=
    match t with (TPtr a (TArray l h t')) => Some h
              | (TPtr a (TNTArray l h t')) => Some h
              | _ => None
    end.

Definition get_high (t : type) :=
    match t with ((TArray l h t')) => Some h
              | ((TNTArray l h t')) => Some h
              | _ => None
    end.

Definition get_low_ptr (t : type) :=
    match t with (TPtr a (TArray l h t')) => Some l
              | (TPtr a (TNTArray l h t')) => Some l
              | _ => None
    end.

Definition get_low (t : type) :=
    match t with ((TArray l h t')) => Some l
              | ((TNTArray l h t')) => Some l
              | _ => None
    end.

(* TODO: say more *)
(** The compatible closure of [H; e ~> H'; r], [H; e ->m H'; r].

    We also define a convenience predicate, [reduces H e], which holds
    when there's some [m], [H'], and [r] such that [H; e ->m H'; r]. *)
Definition get_good_dept (e:expression) :=
  match e with
  | ELit v t => Some (Num v)
  | EVar x   => Some (Var x 0)
  | _        => None
  end.

Fixpoint get_dept_map (l:list (var * type)) (es:list expression) :=
  match l with
  | [] => Some []
  | (x,TNat)::xl =>
      match es with
      | e::es' =>
          match get_good_dept e with
          | None => None
          | Some b =>
              match (get_dept_map xl es') with
              | None => None
              | Some xl' => Some ((x,b)::xl')
              end
          end
      | _ => None
      end
  | (x,y)::xl =>
      match es with
      | (e::es') => get_dept_map xl es'
      | _ => None
      end
  end.

Definition subst_bound (b:bound) (x:var) (b1:bound) :=
   match b with Num n => (Num n)
           | Var y n =>
        if Nat.eqb y x then
           match b1 with (Num m) => (Num (n+m))
                         | (Var z m) => (Var z (n+m))
           end
        else Var y n
   end.
Fixpoint subst_type (t:type) (x:var) (b:bound) :=
   match t with TNat => TNat
            | TPtr m t' => TPtr m (subst_type t' x b)
            | TStruct T => TStruct T
            | TArray b1 b2 t => TArray (subst_bound b1 x b) (subst_bound b2 x b) (subst_type t x b)
            | TNTArray b1 b2 t => TNTArray (subst_bound b1 x b) (subst_bound b2 x b) (subst_type t x b)
            | TFun xl t tl => TFun xl t tl
  end.

Definition subst_env (env:env) (x:var) (b:bound) :=
      Env.map (fun t => subst_type t x b) env.

Fixpoint get_var_stack (S:stack) (l:list var) :=
   match l with [] => []
           | (x::xs) => match Stack.find x S with None => get_var_stack S xs
                             | Some v => (x,Num (fst v))::(get_var_stack S xs)
                        end
   end.

Lemma nat_leq_q_subst: forall Q t x y v, Theta.MapsTo y (NumEq (Num v)) Q ->
              nat_leq Q (subst_bound t x (Num v)) (subst_bound t x (Var y 0)).
Proof.
  intros. induction t;simpl in *;subst. constructor. easy.
  destruct (v0 =? x)%nat eqn:eq1.
  apply Nat.eqb_eq in eq1; subst.
  apply nat_leq_var_2 with (n := v); try easy.
  constructor. lia. apply nat_leq_var. lia.
Qed.

Lemma nat_leq_q_subst_1: forall Q t x y v, Theta.MapsTo y (NumEq (Num v)) Q ->
              nat_leq Q (subst_bound t x (Var y 0)) (subst_bound t x (Num v)).
Proof.
  intros. induction t;simpl in *;subst. constructor. easy.
  destruct (v0 =? x)%nat eqn:eq1.
  apply Nat.eqb_eq in eq1; subst.
  apply nat_leq_var_1 with (n := v); try easy.
  constructor. lia. apply nat_leq_var. lia.
Qed.

Lemma nat_eq_q_subst: forall Q t x y v, Theta.MapsTo y (NumEq (Num v)) Q ->
              nat_eq Q (subst_bound t x (Num v)) (subst_bound t x (Var y 0)).
Proof.
  intros. split. apply nat_leq_q_subst.  easy. 
  apply nat_leq_q_subst_1; easy.
Qed. 


Lemma type_eq_q_subst: forall Q t x y v, Theta.MapsTo y (NumEq (Num v)) Q ->
              type_eq Q (subst_type t x (Num v)) (subst_type t x (Var y 0)).
Proof.
  intros. induction t; intros;simpl in *. constructor.
  constructor. easy. constructor. constructor; try easy.
  apply nat_eq_q_subst; easy.
  apply nat_eq_q_subst; easy.
  constructor; try easy.
  apply nat_eq_q_subst; easy.
  apply nat_eq_q_subst; easy.
  constructor.
Qed.

Lemma not_in_subst_bound_same: forall t x v, ~ In x (freeBoundVars t) -> subst_bound t x v = t.
Proof.
  induction t;intros;simpl in *; eauto.
  apply not_or_and in H. destruct H.
  destruct (v =? x)%nat eqn:eq1.
   apply Nat.eqb_eq in eq1. subst. easy. easy.
Qed.

Lemma not_in_subst_same: forall t x v, ~ In x (freeTypeVars t) -> subst_type t x v = t.
Proof.
  induction t;intros;simpl in *; eauto.
  rewrite IHt. easy. easy.
  setoid_rewrite in_app_iff in H.
  apply not_or_and in H.
  destruct H. 
  setoid_rewrite in_app_iff in H0.
  apply not_or_and in H0. destruct H0.
  rewrite not_in_subst_bound_same; try easy.
  rewrite not_in_subst_bound_same; try easy.
  rewrite IHt; try easy.
  setoid_rewrite in_app_iff in H.
  apply not_or_and in H.
  destruct H. 
  setoid_rewrite in_app_iff in H0.
  apply not_or_and in H0. destruct H0.
  rewrite not_in_subst_bound_same; try easy.
  rewrite not_in_subst_bound_same; try easy.
  rewrite IHt; try easy.
Qed.

Lemma subtype_core_q_subst: forall Q t t' x v, 
              subtype_core (Theta.add x (NumEq (Num v)) Q) t t' ->
              subtype_core Q (subst_type t x (Num v)) (subst_type t' x (Num v)).
Proof.
Admitted.

(* cast bounds. 
Definition  cast_bound (Q:theta) (b:bound) : bound :=
   match b with Num n => (Num n)
             | Var x n => (match (Theta.find x Q) with Some (NumEq (Num v)) => (Num (v + n)) | _ => (Var x n) end)
   end.

Inductive cast_type_bound (s:theta) : type -> type -> Prop :=
   | cast_type_bound_nat : cast_type_bound s (TNat) (TNat)
   | cast_type_bound_ptr : forall c t t', cast_type_bound s t t'
                 -> cast_type_bound s (TPtr c t) (TPtr c t')
   | cast_type_bound_array : forall l l' h h' t t', cast_bound s l = l' -> cast_bound s h = h' ->
                  cast_type_bound s t t' -> cast_type_bound s (TArray l h t) (TArray l' h' t')
   | cast_type_bound_ntarray : forall l l' h h' t t', cast_bound s l = l' -> cast_bound s h = h' ->
                  cast_type_bound s t t' -> cast_type_bound s (TNTArray l h t) (TNTArray l' h' t')
   | cast_type_bound_struct : forall t, cast_type_bound s (TStruct t) (TStruct t)
   | cast_type_bound_fun : forall xl t ts,  cast_type_bound s (TFun xl t ts) (TFun xl t ts).
*)
(*eval bounds *)


Definition eval_bound (s:stack) (b:bound) : option bound :=
   match b with Num n => Some (Num n)
             | Var x n => (match (Stack.find x s) with Some (v,t) => Some (Num (v + n)) | None => None end)
   end.

Inductive eval_type_bound (s:stack) : type -> type -> Prop :=
   | eval_type_bound_nat : eval_type_bound s (TNat) (TNat)
   | eval_type_bound_ptr : forall c t t', eval_type_bound s t t'
                 -> eval_type_bound s (TPtr c t) (TPtr c t')
   | eval_type_bound_array : forall l l' h h' t t', eval_bound s l = Some l' -> eval_bound s h = Some h' ->
                  eval_type_bound s t t' -> eval_type_bound s (TArray l h t) (TArray l' h' t')
   | eval_type_bound_ntarray : forall l l' h h' t t', eval_bound s l = Some l' -> eval_bound s h = Some h' ->
                  eval_type_bound s t t' -> eval_type_bound s (TNTArray l h t) (TNTArray l' h' t')
   | eval_type_bound_struct : forall t, eval_type_bound s (TStruct t) (TStruct t)
   | eval_type_bound_fun : forall xl t ts,  eval_type_bound s (TFun xl t ts) (TFun xl t ts).


Definition is_fun_type (t:type) :=
   match t with TFun yl x xl => True
             | _ => False
   end.

Definition tfun_prop (F: FEnv) (n:Z) (t:type) :=
   match t with TPtr Checked (TFun yl t ts) => F Checked n <> None
              | TPtr m (TFun _  _ _) => F m n <> None
              | _ => True end.

Definition get_xl (tvl: list (var*type)) := (fold_right (fun b a => match (snd b) with TNat => (fst b)::a |_ => a end) [] tvl).

Definition get_fun_type (m:mode) (tvl: list (var*type)) (t:type) :=
  TPtr m (TFun (get_xl tvl) t (snd (List.split tvl))).

Lemma get_fun_type_fun: forall tvl t m,  get_fun_type m tvl t = TPtr m (TFun (get_xl tvl) t (snd (List.split tvl))).
Proof.
  unfold get_fun_type in *.
  induction tvl;intros; simpl in *; try easy.
Qed.

Section EvalArg.
  Variable S : stack. 
  Inductive eval_arg : expression -> type -> expression -> Prop :=
  | eval_lit : forall n t t',
      eval_arg (ELit n t') t (ELit n t)
  | eval_var : forall x n t t',
      Stack.MapsTo x (n,t') S ->
      eval_arg (EVar x) t (ELit n t).

  Inductive eval_vl: list Z -> list (var * type) -> list var -> expression -> type -> expression -> type -> Prop :=
  | eval_vl_empty: forall e t, eval_vl [] [] [] e t (ECast t e) t
  | eval_vl_many_1: forall e es x t tvl xl ea ta ea' ta',
     t <> TNat -> eval_vl es tvl xl ea ta ea' ta' 
           -> eval_vl (e::es) ((x,t)::tvl) xl ea ta (ELet x (ELit e t) ea') ta'
  | eval_vl_many_2: forall e es x tvl xl ea ta ea' ta',
     eval_vl es (map (fun a => (fst a, subst_type (snd a) x (Num e))) tvl) xl ea (subst_type ta x (Num e)) ea' ta' ->
     eval_vl (e::es) ((x,TNat)::tvl) (x::xl) ea ta (ELet x (ELit e TNat) ea') ta'.

  Inductive eval_el : list expression -> list (var * type) -> list var -> expression -> type -> expression -> type -> Prop :=
  | eval_el_empty : forall e t, eval_el [] [] [] e t (ECast t e) t
  | eval_el_many_1 : forall e es x t tvl xl v ea ta ea' ta',
      t <> TNat ->
      eval_arg e t v ->
      eval_el es tvl xl ea ta ea' ta' ->
      eval_el (e::es) ((x,t)::tvl) xl ea ta (ELet x v ea') ta'
  | eval_el_many_2 : forall e es x tvl xl v ea ta ea' ta',
      eval_arg e TNat (ELit v TNat) ->
      eval_el es (map (fun a => (fst a, subst_type (snd a) x (Num v))) tvl)
                 xl ea (subst_type ta x (Num v)) ea' ta' ->
      eval_el (e::es) ((x,TNat)::tvl) (x::xl) ea ta (ELet x (ELit v TNat) ea') ta'.

(*
  Lemma vl_el_same: forall es tvl e ea ta, eval_el es tvl e ea ->
        exists vl ta', eval_vl vl tvl e ta ea ta' /\ (Forall3 (fun a b c => eval_arg a (snd c) (ELit b (snd c))) es vl tvl).
  Proof.
    intros. induction H; simpl in *.
    exists [],ta. split. constructor.
    constructor.
    destruct IHeval_el. destruct H1.
    assert (t = TNat \/ t <> TNat). destruct t; auto; right; easy.
    destruct H2. subst.
    inv H.
    exists (n::x0), (subst_type [(x,Num n)] x1). split.
    apply eval_vl_many_2; try easy.
    constructor. constructor. easy.
    exists (n::x0), (subst_type [(x,Num n)] x1). split.
    apply eval_vl_many_2; try easy.
    constructor. econstructor. apply H2. easy.
    inv H.
    exists (n::x0), x1. split.
    constructor; try easy.
    constructor. constructor. easy.
    exists (n::x0), x1. split.
    constructor; try easy.
    constructor. econstructor. apply H3. easy.
  Qed.
*)
End EvalArg.


Definition is_nor_array_ptr (t:type) : Prop :=
   match t with (TPtr m (TArray x y t')) => True
              | _ => False
   end.

Inductive get_root {D:structdef} : type -> type -> Prop :=
  get_root_word : forall m t, word_type t -> get_root (TPtr m t) t
| get_root_array : forall m l h t, get_root (TPtr m (TArray l h t)) t
| get_root_ntarray : forall m l h t, get_root (TPtr m (TNTArray l h t)) t
| get_root_struct : forall m T f,
    StructDef.MapsTo T f D ->
    Some (TNat) = (Fields.find 0%nat f) ->
    @get_root D (TPtr m (TStruct T)) TNat.

(*
Inductive gen_rets  (AS: list (var*bound)) (S: stack)
  : list (var * type) -> list expression -> expression -> expression -> Prop :=
  gen_rets_empty : forall e, gen_rets AS S [] [] e e
| gen_rets_many : forall x t t' xl e1 v es e2 e',
    gen_rets AS S xl es e2 e' ->
    eval_arg S e1 (subst_type AS t) (ELit v t') ->
    gen_rets AS S ((x,t)::xl) (e1::es) e2 (ERet x (v,t') (Stack.find x S) e').
*)
Require Import Lists.ListSet.


Definition eq_dec_nt (x y : Z * type) : {x = y} + { x <> y}.
Admitted.

Definition scope := set (Z *type)%type.
Definition empty_scope := empty_set (Z * type).

Definition scope_set_add (v:Z) (t:type) (s:scope) :=
     match t with TPtr m (TStruct x) => set_add eq_dec_nt (v,TPtr m (TStruct x)) s
               | _ => s
     end.


Definition nt_array_prop (H:heap) (n:Z) (t:type) :=
  match t with
    TPtr m (TNTArray (Num l) (Num h) t) =>
      exists n' t', (0 <= n' /\ Heap.MapsTo (n+n') (0,t') H
                     /\ (forall i , n <= i < n+n' -> (exists n1, Heap.MapsTo i (n1,t') H /\ n1 <> 0)))
  | _ => True
  end.



(** Typing of literals on Checked heaps *)
Inductive well_typed_lit_checked (D : structdef) (F: FEnv) H
  : scope -> Z -> type -> Prop :=
| TyLitInt_C : forall s n,
    well_typed_lit_checked D F H s n TNat
| TyLitU_C : forall s n w m,
    m <> Checked ->             (* tainted + unchecked *)
    well_typed_lit_checked D F H s n (TPtr m w)
| TyLitZero_C : forall s t,
    well_typed_lit_checked D F H s 0 t
| TyLitFun_C : forall s n xl t ts tvl e ta,
     F Checked n = Some (tvl,ta,e) ->
     @subtype empty_theta (get_fun_type Checked tvl ta) (TPtr Checked (TFun xl t ts)) ->
    well_typed_lit_checked D F H s n (TPtr Checked (TFun xl t ts))
| TyLitRec_C : forall s n w t,
    set_In (n, t) s ->
    @subtype empty_theta t (TPtr Checked w) ->
    well_typed_lit_checked D F H s n (TPtr Checked w)
| TyLitC_C : forall sc n w t b ts,
    simple_type w -> ~ is_fun_type w ->
    @subtype empty_theta (TPtr Checked w) (TPtr Checked t) ->
    Some (b, ts) = allocate_meta D w ->
    nt_array_prop H n (TPtr Checked t) ->
    (forall k,
        b <= k < b + Z.of_nat(List.length ts) ->
        exists n' t',
          Some t' = List.nth_error ts (Z.to_nat (k - b)) /\
            Heap.MapsTo (n + k) (n', t') H /\
            well_typed_lit_checked D F H (scope_set_add n (TPtr Checked w) sc) n' t') ->
    well_typed_lit_checked D F H sc n (TPtr Checked t).

(*
#[export] Hint Constructors well_typed_lit_checked : ty.
*)


Lemma well_typed_lit_c_ind' :
  forall (D : structdef) (F: FEnv) (H : heap) (P : scope -> Z -> type -> Prop),
    (forall (s : scope) (n : Z), P s n TNat) ->
       (forall (s : scope) (n : Z) (w : type) (m : mode), m <> Checked -> P s n (TPtr m w)) ->
       (forall (s : scope) (t : type), P s 0 t) ->
       (forall (s: scope) (n:Z) (xl:list var) (t:type) (ts: list type)
              (tvl:list (var * type)) (e:expression) (ta:type),
                F Checked n = Some (tvl,ta,e) 
               -> subtype empty_theta (get_fun_type Checked tvl ta) (TPtr Checked (TFun xl t ts)) 
               -> P s n (TPtr Checked (TFun xl t ts))) ->
       (forall (s : scope) (n : Z) (w : type) (t : type),
            set_In (n, t) s -> subtype empty_theta t (TPtr Checked w) -> P s n (TPtr Checked w)) ->
       (forall (s : scope) (n : Z) (w : type) (t: type) (b : Z) (ts : list type),
        simple_type w ->  ~ is_fun_type w  ->
        subtype empty_theta (TPtr Checked w) (TPtr Checked t) ->
        Some (b, ts) = allocate_meta D w ->
        nt_array_prop H n (TPtr Checked t) ->
        (forall k : Z,
         b <= k < b + Z.of_nat (length ts) ->
         exists (n' : Z) (t' : type),
           Some t' = nth_error ts (Z.to_nat (k - b)) /\
           Heap.MapsTo (n + k) (n', t') H /\
           well_typed_lit_checked D F H (scope_set_add n (TPtr Checked w) s) n' t' /\
           P (scope_set_add n (TPtr Checked w) s) n' t') ->
           P s n (TPtr Checked t)) 
       -> forall (s : scope) (n : Z) (w : type), well_typed_lit_checked D F H s n w -> P s n w.
Proof.
  intros D F H P.
  intros HTyLitInt
         HTyLitU
         HTyLitZero
         HTyLitFun
         HTyLitRec
         HTyLitC.
  refine (fix F s n w Hwtl :=
            match Hwtl with
            | TyLitInt_C _ _ _ s' n' => HTyLitInt s' n'
            | TyLitU_C _ _ _ s' n' w' m' Hc => HTyLitU s' n' w' m' Hc
            | TyLitZero_C _ _ _ s' t' => HTyLitZero s' t'
            | TyLitFun_C _ _ _ s' n' xl' t' ts' tvl' e' ta' HF HSub => HTyLitFun s' n' xl' t' ts' tvl' e' ta' HF HSub
            | TyLitRec_C _ _ _ s' n' w' t' Hscope Hsub => HTyLitRec s' n' w' t' Hscope Hsub
            | TyLitC_C _ _ _ s' n' w' t' b ts HSim Hf HSub Hnt Hts IH =>
              HTyLitC s' n' w' t' b ts HSim Hf HSub Hnt Hts (fun k Hk =>
                                         match IH k Hk with
                                         | ex_intro _ n' Htmp =>
                                           match Htmp with
                                           | ex_intro _ t' Hn't' =>
                                             match Hn't' with
                                             | conj Ht' Hrest1 =>
                                             match Hrest1 with
                                               | conj Hheap Hwt =>
                                                 ex_intro _ n' (ex_intro _ t'
                     (conj Ht' (conj Hheap (conj Hwt (F (scope_set_add _ (TPtr Checked w') s') n' t' Hwt)))))
                                               end
                                             end
                                           end
                                       end)
            end).
Qed.

(** Typing of literals on Tainted heaps *)
Inductive well_typed_lit_tainted (D : structdef) (F: FEnv) H
  : scope -> Z -> type -> Prop :=
| TyLitInt_T : forall s n,
    well_typed_lit_tainted D F H s n TNat
| TyLitU_T : forall s n w,
    well_typed_lit_tainted D F H s n (TPtr Unchecked w)
| TyLitZero_T : forall s t,
    well_typed_lit_tainted D F H s 0 t
| TyLitFun_T : forall s n xl t ts tvl e ta,
    F Tainted n = Some (tvl,ta,e) ->
     subtype empty_theta (get_fun_type Tainted tvl ta) (TPtr Tainted (TFun xl t ts)) ->
    well_typed_lit_tainted D F H s n (TPtr Tainted (TFun xl t ts))
| TyLitRec_T : forall s n w t,
    set_In (n, t) s ->
    subtype empty_theta t (TPtr Tainted w) ->
    well_typed_lit_tainted D F H s n (TPtr Tainted w)
| TyLitC_T : forall sc n w t b ts,
    simple_type w -> ~ is_fun_type w ->
    subtype empty_theta (TPtr Tainted w) (TPtr Tainted t) ->
    Some (b, ts) = allocate_meta D w ->
    nt_array_prop H n (TPtr Tainted t) ->
    (forall k,
        b <= k < b + Z.of_nat(List.length ts) ->
        exists n' t',
          Some t' = List.nth_error ts (Z.to_nat (k - b)) /\
            Heap.MapsTo (n + k) (n', t') H /\
            well_typed_lit_tainted D F H (scope_set_add n (TPtr Tainted w) sc) n' t') ->
    well_typed_lit_tainted D F H sc n (TPtr Tainted t).


Lemma well_typed_lit_u_ind' :
  forall (D : structdef) (F: FEnv) (H : heap) (P : scope -> Z -> type -> Prop),
    (forall (s : scope) (n : Z), P s n TNat) ->
       (forall (s : scope) (n : Z) (w : type), P s n (TPtr Unchecked w)) ->
       (forall (s : scope) (t : type), P s 0 t) ->
       (forall (s: scope) (n:Z) (xl:list var) (t:type) (ts: list type)
              (tvl:list (var * type)) (e:expression) (ta:type),
                F Tainted n = Some (tvl,ta,e) 
               -> subtype empty_theta (get_fun_type Tainted tvl ta) (TPtr Tainted (TFun xl t ts)) 
               -> P s n (TPtr Tainted (TFun xl t ts))) ->
       (forall (s : scope) (n : Z) (w : type) (t : type),
            set_In (n, t) s -> subtype empty_theta t (TPtr Tainted w) -> P s n (TPtr Tainted w)) ->
       (forall (s : scope) (n : Z) (w : type) (t: type) (b : Z) (ts : list type),
        simple_type w ->  ~ is_fun_type w  ->
        subtype empty_theta (TPtr Tainted w) (TPtr Tainted t) ->
        Some (b, ts) = allocate_meta D w ->
        nt_array_prop H n (TPtr Tainted t) ->
        (forall k : Z,
         b <= k < b + Z.of_nat (length ts) ->
         exists (n' : Z) (t' : type),
           Some t' = nth_error ts (Z.to_nat (k - b)) /\
           Heap.MapsTo (n + k) (n', t') H /\
           well_typed_lit_tainted D F H (scope_set_add n (TPtr Tainted w) s) n' t' /\
           P (scope_set_add n (TPtr Tainted w) s) n' t') ->
           P s n (TPtr Tainted t)) 
       -> forall (s : scope) (n : Z) (w : type), well_typed_lit_tainted D F H s n w -> P s n w.
Proof.
  intros D F H P.
  intros HTyLitInt
         HTyLitU
         HTyLitZero
         HTyLitFun
         HTyLitRec
         HTyLitC.
  refine (fix F s n w Hwtl :=
            match Hwtl with
            | TyLitInt_T _ _ _ s' n' => HTyLitInt s' n'
            | TyLitU_T _ _ _ s' n' w' => HTyLitU s' n' w'
            | TyLitZero_T _ _ _ s' t' => HTyLitZero s' t'
            | TyLitFun_T _ _ _ s' n' xl' t' ts' tvl' e' ta' HF HSub => HTyLitFun s' n' xl' t' ts' tvl' e' ta' HF HSub
            | TyLitRec_T _ _ _ s' n' w' t' Hscope Hsub => HTyLitRec s' n' w' t' Hscope Hsub
            | TyLitC_T _ _ _ s' n' w' t' b ts HSim Hf HSub Hnt Hts IH =>
              HTyLitC s' n' w' t' b ts HSim Hf HSub Hnt Hts (fun k Hk =>
                                         match IH k Hk with
                                         | ex_intro _ n' Htmp =>
                                           match Htmp with
                                           | ex_intro _ t' Hn't' =>
                                             match Hn't' with
                                             | conj Ht' Hrest1 =>
                                             match Hrest1 with
                                               | conj Hheap Hwt =>
                                                 ex_intro _ n' (ex_intro _ t'
                     (conj Ht' (conj Hheap (conj Hwt (F (scope_set_add _ (TPtr Tainted w') s') n' t' Hwt)))))
                                               end
                                             end
                                           end
                                       end)
            end).
Qed.
(*
#[export] Hint Constructors well_typed_lit_tainted : ty.
*)

Definition well_typed_lit D F R Theta n t := forall H1 H2,
  R = (H1, H2) ->
  well_typed_lit_checked D F H1 Theta n t
  \/ well_typed_lit_tainted D F H2 Theta n t.


(** It turns out, the induction principle that Coq generates automatically isn't very useful. *)
(** In particular, the TyLitC case does not have an induction hypothesis.
    So, we prove an alternative induction principle which is almost identical but includes
    an induction hypothesis for the TyLitC case.

    TODO: write blog post about this *)
(* FIXME : REDEFINE ind *)
(*
 *)
(*
Definition add_value (H:heap) (n:Z) (t:type) :=
   match t with TFun xl ta tas => Heap.add n (na,t) H
              | _ => H
   end.
*)
(* Hint Constructors well_typed_lit. *)

(** Memory, [M], is the composition of stack, checked heap and tainted heap *)
Definition mem : Type := stack * real_heap.

(** ** Checked C Semantics *)

Create HintDb sem.

Definition inject_ret (x:var) (v1:Z * type) (e:result) :=
  match e with RExpr ea => RExpr (ERet x v1 ea)
            | a => a
 end.

(** The single-step reduction relation, [H; e ~> H'; r]. *)
Inductive step
  (D : structdef)
  (F: FEnv)
  : mem -> expression -> mem -> result -> Prop :=
| SVar : forall s R x v t,
    (Stack.MapsTo x (v,t) s) ->
    step D F
      (s, R) (EVar x)
      (s, R) (RExpr (ELit v t))
| StrlenChecked : forall s H1 H2 x n n' l h t t1,
    h > 0 -> l <= 0 -> 0 <= n' ->
    (Stack.MapsTo x (n,(TPtr Checked (TNTArray (Num l) (Num h) t))) s) ->
    (forall i ,
        n <= i < n+n' ->
        (exists n1, Heap.MapsTo i (n1,t1) H1 /\ n1 <> 0)) ->
    Heap.MapsTo (n+n') (0,t1) H1 ->
    step D F
      (s, (H1,H2)) (EStrlen x)
      ((change_strlen_stack s x Checked t l n n' h), (H1,H2))
      (RExpr (ELit n' TNat))
| StrlenTainted : forall s H1 H2 x n n' l h t t1,
    h > 0 -> l <= 0 -> 0 <= n' ->
    (Stack.MapsTo x (n,(TPtr Tainted (TNTArray (Num l) (Num h) t))) s) ->
    (forall i ,
        n <= i < n+n' ->
        (exists n1,
            Heap.MapsTo i (n1,t1) H2 /\ n1 <> 0
            /\ well_typed_lit_tainted D F H2 empty_scope n1 t1)) ->
    Heap.MapsTo (n+n') (0,t1) H2 ->
    step D F
      (s, (H1,H2)) (EStrlen x)
      ((change_strlen_stack s x Tainted t l n n' h), (H1,H2))
      (RExpr (ELit n' TNat))
| StrlenUnChecked : forall s H1 H2 x n n' t t1,
    0 <= n' ->
    (Stack.MapsTo x (n,(TPtr Unchecked t)) s) ->
    (forall i ,
        n <= i < n+n' -> (exists n1, Heap.MapsTo i (n1,t1) H2 /\ n1 <> 0)) ->
    Heap.MapsTo (n+n') (0,t1) H2 ->
    step D F
      (s, (H1,H2)) (EStrlen x)
      (s, (H1,H2)) (RExpr (ELit n' TNat))

| StrlenHighOOB : forall s R x n t l h,
    h <= 0 -> 
    (Stack.MapsTo x (n,(TPtr Checked (TNTArray l (Num h) t))) s) ->
    step D F
      (s, R) (EStrlen x) (s, R) RBounds
| StrlenLowOOB : forall s R x n t l h,
    l > 0 -> 
    (Stack.MapsTo x (n,(TPtr Checked (TNTArray (Num l) h t))) s) ->
    step D F
      (s, R) (EStrlen x) (s, R) RBounds
| StrlenNull : forall s R x t n l h,
    n <= 0 ->
    (Stack.MapsTo x (n,(TPtr Checked (TNTArray l h t))) s) ->
    step D F
      (s, R) (EStrlen x)
      (s, R) RNull

| SCallChecked : forall s R x ta ts el t tvl e ea ta' xl,
    F Checked x = Some (tvl,t,e) ->
    @eval_el s el tvl (get_xl tvl) e t ea ta' ->
   (* subtype D empty_theta (TPtr Checked (TFun (Num n) [] ta' ts')) (TPtr Checked (TFun (Num n) [] ta ts)) -> *)
    step D F
      (s, R) (ECall (ELit x (TPtr Checked (TFun xl ta ts))) el)
      (s, R) (RExpr ea)
(*
| SCallCheckedType : forall s R x ta ts ta' ts' el t tvl e ea n,
    n = -1 ->
    F n x = Some (tvl,t,e,Checked) ->
    @eval_el s el tvl t (ECast t e) ea (ts',ta') ->
    ~ subtype D empty_theta (TPtr Checked (TFun (Num n) [] ta' ts')) (TPtr Checked (TFun (Num n) [] ta ts)) ->
    step D F
      (s, R) (ECall (ELit x (TPtr Checked (TFun (Num n) [] ta ts))) el)
      (s, R) RBounds
*)
| SCallNull : forall m s R x ta ts el xl,
    m <> Unchecked ->
    F m x = None ->
    step D F
      (s, R) (ECall (ELit x (TPtr m (TFun xl ta ts))) el)
      (s, R) RNull
| SCallTainted : forall s H1 H2 x ta ts el t tvl e ea ta' xl,
    F Tainted x = Some (tvl,t,e) ->
    @eval_el s el tvl (get_xl tvl) e t ea ta' ->
    well_typed_lit_tainted D F H2 empty_scope x (TPtr Tainted (TFun xl ta ts)) ->
    step D F
      (s, (H1, H2)) (ECall (ELit x (TPtr Tainted (TFun xl ta ts))) el)
      (s, (H1, H2)) (RExpr ea)

| SCallTaintedType : forall s R x ta ts el t tvl e xl,
    F Tainted x = Some (tvl,t,e) ->
    ~ well_typed_lit_tainted D F (snd R) empty_scope x (TPtr Tainted (TFun xl ta ts)) ->
    step D F
      (s, R) (ECall (ELit x (TPtr Tainted (TFun xl ta ts))) el)
      (s, R) RBounds

| SCallUnchecked : forall s R x ta ts el t tvl e ea ta' xl,
    F Unchecked x = Some (tvl,t,e) ->
    @eval_el s el tvl (get_xl tvl) e t ea ta' ->
    step D F
      (s, R) (ECall (ELit x (TPtr Unchecked (TFun xl ta ts))) el)
      (s, R) (RExpr ea)

| SLet : forall s R x n t e t',
    eval_type_bound s t t' ->
    step D F
      (s, R) (ELet x (ELit n t) e)
      (s,  R)
      (RExpr (ERet x (n,t') e))

| SRetSome : forall s R s' R' x nb tb nb' tb' a' ta' e re,
    Stack.MapsTo x (a',ta') s ->
    Stack.MapsTo x (nb',tb') s' ->
    step D F (Stack.add x (nb,tb) s, R) e (s',R') re ->
    step D F
      (s, R) (ERet x (nb,tb) e)
      (Stack.add x (a',ta') s', R') (inject_ret x (nb',tb') re)
| SRetNone : forall s R s' R' x nb tb nb' tb' e re,
    ~ Stack.In x s ->
    Stack.MapsTo x (nb',tb') s' ->
    step D F (Stack.add x (nb,tb) s,R) e (s',R') re ->
    step D F
      (s, R)
      (ERet x (nb,tb) e)
      (Stack.remove x s', R') (inject_ret x (nb',tb') re)
| SRetEnd : forall s R x n t nb tb,
    step D F
      (s, R)
      (ERet x (nb,tb) (ELit n t)) (s,R) (RExpr (ELit n t))
| SPlusChecked : forall s R n1 t1 n2,
    n1 > 0 -> is_check_array_ptr t1 ->
    step D F
      (s, R) (EPlus (ELit n1 t1) (ELit n2 TNat))
      (s, R) (RExpr (ELit (n1 + n2) (sub_type_bound t1 n2)))
| SPlus : forall s R t1 n1 n2,
    ~ is_check_array_ptr t1 ->
    step D F
      (s, R) (EPlus (ELit n1 t1) (ELit n2 TNat))
      (s, R) (RExpr (ELit (n1 + n2) t1))
| SPlusNull : forall s R n1 t n2,
    n1 <= 0 -> is_check_array_ptr t ->
    step D F
      (s, R) (EPlus (ELit n1 t) (ELit n2 (TNat)))
      (s, R) RNull
| SCast : forall s R t n t' t'',
    eval_type_bound s t t'' ->
    step D F
      (s, R) (ECast t (ELit n t'))
      (s, R) (RExpr (ELit n t''))

| SCastNotArray : forall s R x y t l h w n m t',
    eval_type_bound s (TPtr m (TArray x y t)) (TPtr m (TArray (Num l) (Num h) w)) ->
    ~ is_array_ptr (TPtr m t') -> 
    0 <= l -> l < h -> h <= 1 ->
    step D F
      (s, R) (EDynCast (TPtr m (TArray x y t)) (ELit n (TPtr m t')))
      (s, R) (RExpr (ELit n (TPtr m (TArray (Num l) (Num h) w))))

| SCastNotArrayHighOOB1 : forall s R x y t l h w n m t',
    eval_type_bound s (TPtr m (TArray x y t)) (TPtr m (TArray (Num l) (Num h) w)) ->
    ~ is_array_ptr (TPtr m t') -> 
    1 < h ->
     step D F (s, R) (EDynCast (TPtr m (TArray x y t)) (ELit n (TPtr m t'))) (s, R) RBounds
| SCastNotArrayLowOOB1 : forall s R x y t l h w n m t',
    eval_type_bound s (TPtr m (TArray x y t)) (TPtr m (TArray (Num l) (Num h) w)) ->
    ~ is_array_ptr (TPtr m t') -> 
    l < 0 ->
    step D F (s, R) (EDynCast (TPtr m (TArray x y t)) (ELit n (TPtr m t'))) (s, R) RBounds
| SCastNotArrayLowOOB2 : forall s R x y t l h w n m t',
    eval_type_bound s (TPtr m (TArray x y t)) (TPtr m (TArray (Num l) (Num h) w)) ->
    ~ is_array_ptr (TPtr m t') -> 
    h <= l ->
    step D F (s, R) (EDynCast t (ELit n t')) (s, R) RBounds

| SCastArray : forall m s R t n t' l h w l' h' w',
    eval_type_bound s t (TPtr m (TArray (Num l) (Num h) w)) ->
    eval_type_bound s t' (TPtr m (TArray (Num l') (Num h') w')) ->
    l' <= l -> l < h -> h <= h' ->
    step D F
      (s, R) (EDynCast t (ELit n t'))
      (s, R) (RExpr (ELit n (TPtr m (TArray (Num l) (Num h) w))))
| SCastArrayHighOOB1 : forall m s R t n t' l h w l' h' w',
    eval_type_bound s t (TPtr m (TArray (Num l) (Num h) w)) ->
    eval_type_bound s t' (TPtr m (TArray (Num l') (Num h') w')) ->
    h' < h ->
           step D F (s, R) (EDynCast t (ELit n t')) (s, R) RBounds
| SCastArrayLowOOB1 : forall m s R t n t' l h w l' h' w',
    eval_type_bound s t (TPtr m (TArray (Num l) (Num h) w)) ->
    eval_type_bound s t' (TPtr m (TArray (Num l') (Num h') w')) ->
    l < l' ->
    step D F (s, R) (EDynCast t (ELit n t'))  (s, R) RBounds
| SCastArrayLowOOB2 : forall m s R t n t' l h w l' h' w',
    eval_type_bound s t (TPtr m (TArray (Num l) (Num h) w)) ->
    eval_type_bound s t' (TPtr m (TArray (Num l') (Num h') w')) ->
    h <= l ->
    step D F (s, R) (EDynCast t (ELit n t')) (s, R) RBounds
| SCastNTArray : forall m s R t n t' l h w l' h' w',
    eval_type_bound s t (TPtr m (TNTArray (Num l) (Num h) w)) ->
    eval_type_bound s t' (TPtr m (TNTArray (Num l') (Num h') w')) ->
    l' <= l -> l < h -> h <= h' ->
    step D F
      (s, R) (EDynCast t (ELit n t'))
      (s, R) (RExpr (ELit n (TPtr m (TNTArray (Num l) (Num h) w))))
| SCastNTArrayHighOOB1 : forall m s R t n t' l h w l' h' w',
    eval_type_bound s t (TPtr m (TNTArray (Num l) (Num h) w)) ->
    eval_type_bound s t' (TPtr m (TNTArray (Num l') (Num h') w')) ->
    h' < h ->
           step D F (s, R) (EDynCast t (ELit n t')) (s, R) RBounds
| SCastNTArrayLowOOB1 : forall m s R t n t' l h w l' h' w',
    eval_type_bound s t (TPtr m (TNTArray (Num l) (Num h) w)) ->
    eval_type_bound s t' (TPtr m (TNTArray (Num l') (Num h') w')) ->
    l < l' ->
    step D F (s, R) (EDynCast t (ELit n t')) (s, R) RBounds
| SCastNTArrayLowOOB2 : forall m s R t n t' l h w l' h' w',
    eval_type_bound s t (TPtr m (TNTArray (Num l) (Num h) w)) ->
    eval_type_bound s t' (TPtr m (TNTArray (Num l') (Num h') w')) ->
    h <= l ->
    step D F (s, R) (EDynCast t (ELit n t')) (s, R) RBounds

| SCastNTTArray : forall m s R t n t' l h w l' h' w',
    eval_type_bound s t (TPtr m (TArray (Num l) (Num h) w)) ->
    eval_type_bound s t' (TPtr m (TNTArray (Num l') (Num h') w')) ->
    l' <= l -> l < h -> h <= h' ->
    step D F
      (s, R) (EDynCast t (ELit n t'))
      (s, R) (RExpr (ELit n (TPtr m (TArray (Num l) (Num h) w))))
| SCastNTTArrayHighOOB1 : forall m s R t n t' l h w l' h' w',
    eval_type_bound s t (TPtr m (TArray (Num l) (Num h) w)) ->
    eval_type_bound s t' (TPtr m (TNTArray (Num l') (Num h') w')) ->
    h' < h ->
           step D F (s, R) (EDynCast t (ELit n t')) (s, R) RBounds
| SCastNTTArrayLowOOB1 : forall m s R t n t' l h w l' h' w',
    eval_type_bound s t (TPtr m (TArray (Num l) (Num h) w)) ->
    eval_type_bound s t' (TPtr m (TNTArray (Num l') (Num h') w')) ->
    l < l' ->
    step D F (s, R) (EDynCast t (ELit n t')) (s, R) RBounds
| SCastNTTArrayLowOOB2 : forall m s R t n t' l h w l' h' w',
    eval_type_bound s t (TPtr m (TArray (Num l) (Num h) w)) ->
    eval_type_bound s t' (TPtr m (TNTArray (Num l') (Num h') w')) ->
    h <= l ->
    step D F (s, R) (EDynCast t (ELit n t')) (s, R) RBounds

| SDerefChecked : forall s H1 H2 n n1 t1 t t2 tv,
    eval_type_bound s (TPtr Checked t) t2 ->
    Heap.MapsTo n (n1, t1) H1 ->
    (forall l h t',
        t2 = TPtr Checked (TArray (Num l) (Num h) t') -> l <= 0 < h) ->
    (forall l h t',
        t2 = TPtr Checked (TNTArray (Num l) (Num h) t') -> l <= 0 < h) ->
    @get_root D t2 tv ->
    step D F
      (s, (H1,H2)) (EDeref (ELit n (TPtr Checked t)))
      (s, (H1,H2)) (RExpr (ELit n1 tv))
| SDerefTainted : forall s H1 H2 n n1 t1 t t2 tv,
    eval_type_bound s (TPtr Tainted t) t2 ->
    Heap.MapsTo n (n1, t1) H2 ->
    well_typed_lit_tainted D F H2 empty_scope n1 t1 ->
    (forall l h t',
        t2 = TPtr Tainted (TArray (Num l) (Num h) t') -> l <= 0 < h) ->
    (forall l h t',
        t2 = TPtr Tainted (TNTArray (Num l) (Num h) t') -> l <= 0 < h) ->
    @get_root D t2 tv ->
    step D F
      (s, (H1,H2)) (EDeref (ELit n (TPtr Tainted t)))
      (s, (H1,H2)) (RExpr (ELit n1 tv))
| SDerefNone : forall s H1 H2 m n n1 t1 t t2 tv,
    eval_type_bound s (TPtr m t) t2 -> m <> Unchecked ->
    Heap.MapsTo n (n1, t1) H2 ->
    @get_root D t2 tv ->
    step D F
      (s, (H1,H2)) (EDeref (ELit n (TPtr m t))) (s, (H1,H2)) RNull

(* Add two rules for when pm = None. *)

| SDerefUnChecked : forall s H1 H2 m n n1 t1 t t2 tv,
    eval_type_bound s (TPtr m t) t2 ->
    Heap.MapsTo n (n1, t1) H2 ->
    m <> Checked ->
    @get_root D t2 tv ->
    step D F
      (s, (H1,H2)) (EDeref (ELit n (TPtr m t)))
      (s, (H1,H2)) (RExpr (ELit n1 tv))
| SDerefHighOOB : forall s R n t t' h,
    h <= n ->
    eval_type_bound s t t' ->
    get_high_ptr t' = Some (Num h) ->
    step D F (s, R) (EDeref (ELit n t)) (s, R) RBounds
| SDerefLowOOB : forall s R n t t' l,
    l > n ->
    eval_type_bound s t t' ->
    get_low_ptr t' = Some (Num l) ->
    step D F (s, R) (EDeref (ELit n t)) (s, R) RBounds
| SDerefNull : forall s R t n,
    n <= 0 ->
    step D F (s, R) (EDeref (ELit n (TPtr Checked t))) (s, R) RNull
| SAssignChecked : forall s H1 H2 n t na ta tv n1 t1 tv',
    Heap.MapsTo n (na,ta) H1 ->
    eval_type_bound s (TPtr Checked t) tv ->
    (forall l h t',
        tv = TPtr Checked (TArray (Num l) (Num h) t') -> l <= n < h) ->
    (forall l h t',
        tv = TPtr Checked (TNTArray (Num l) (Num h) t') -> l <= n < h) ->
    @get_root D tv tv' ->
    step D F
      (s, (H1,H2))  (EAssign (ELit n (TPtr Checked t)) (ELit n1 t1))
      (s, (Heap.add n (n1, ta) H1, H2)) (RExpr (ELit n1 tv'))
| SAssignTainted : forall s H1 H2 n t na ta tv n1 t1 tv',
    Heap.MapsTo n (na,ta) H2 ->
    well_typed_lit_tainted D F H2 empty_scope na ta ->
    eval_type_bound s (TPtr Tainted t) tv ->
    (forall l h t',
        tv = TPtr Tainted (TArray (Num l) (Num h) t') -> l <= n < h) ->
    (forall l h t',
        tv = TPtr Tainted (TNTArray (Num l) (Num h) t') -> l <= n < h) ->
    @get_root D tv tv' ->
    step D F
      (s, (H1,H2))  (EAssign (ELit n (TPtr Tainted t)) (ELit n1 t1))
      (s, (Heap.add n (n1, ta) H1,H2)) (RExpr (ELit n1 tv'))
(*
  | SAssignNone : forall s H1 H2 m n pm t na ta tv n1 t1 tv',
      Heap.MapsTo n (na,ta) H2 -> m <> Unchecked -> pm = None ->
      eval_type_bound s (TPtr m pm t) tv ->
      @get_root D tv tv' ->
      step D U F
         s (H1,H2)  (EAssign (ELit n (TPtr m pm t)) (ELit n1 t1))
         s (Heap.add n (n1, ta) H1,H2) RNull
 *)
(* Add two rules for RNull / RBound SAssign. *)

| SAssignUnChecked : forall s H1 H2 m n t na ta tv n1 t1 tv',
    Heap.MapsTo n (na,ta) H2 -> m <> Checked ->
    eval_type_bound s (TPtr m t) tv ->
    @get_root D tv tv' ->
    step D F
      (s, (H1,H2))  (EAssign (ELit n (TPtr m t)) (ELit n1 t1))
      (s, (H1,Heap.add n (n1, ta) H2)) (RExpr (ELit n1 tv'))
| SAssignHighOOB : forall s R n t t' n1 t1 h,
     h <= n ->
    eval_type_bound s t t' ->
     get_high_ptr t' = Some (Num h) ->
     step D F
       (s, R) (EAssign (ELit n t) (ELit n1 t1))
       (s, R) RBounds
 | SAssignLowOOB : forall s R n t t' n1 t1 l,
     l > n ->
     eval_type_bound s t t' ->
     get_low_ptr t' = Some (Num l) ->
     step D F
       (s, R) (EAssign (ELit n t) (ELit n1 t1))
       (s, R) RBounds
 | SAssignNull : forall s R t tv m n n1 t',
     n1 <= 0 -> m <> Unchecked ->
     eval_type_bound s t tv ->
     step D F
       (s, R) (EAssign (ELit n1 t) (ELit n t')) (s, R) RNull
| SFieldAddrChecked : forall s R n t (fi : field) n0 t0 T fs i fi ti,
    n > 0 ->
    t = TPtr Checked (TStruct T) ->
    StructDef.MapsTo T fs D ->
    Fields.MapsTo fi ti fs ->
    List.nth_error (Fields.this fs) i = Some (fi, ti) ->
    n0 = n + Z.of_nat(i) ->
    t0 = TPtr Checked ti ->
    word_type ti ->
    step D F
      (s, R) (EFieldAddr (ELit n t) fi)
      (s, R) (RExpr (ELit n0 t0))
(*
  | SFieldAddrCheckedNone : forall s H n t T (fi : field),
      n > 0 ->
      t = TPtr Checked None (TStruct T) ->
      step D U F
         s H (EFieldAddr (ELit n t) fi)
         s H (RNull)
 *)
| SFieldAddrTainted : forall s R n t (fi : field) n0 t0 T fs i fi ti,
    n > 0 -> t = TPtr Tainted (TStruct T) ->
    StructDef.MapsTo T fs D ->
    Fields.MapsTo fi ti fs ->
    List.nth_error (Fields.this fs) i = Some (fi, ti) ->
    n0 = n + Z.of_nat(i) ->
    t0 = TPtr Tainted ti ->
    word_type ti ->
    well_typed_lit_tainted D F (snd R) empty_scope n0 t0 ->
    step D F
      (s, R) (EFieldAddr (ELit n t) fi)
      (s, R) (RExpr (ELit n0 t0))

| SFieldAddrNull : forall s R (fi : field) m n T,
    n <= 0 -> m <> Unchecked  ->
    step D F
      (s, R) (EFieldAddr (ELit n (TPtr m (TStruct T))) fi)
      (s, R) RNull

| SFieldAddr : forall s R n t (fi : field) n0 t0 T fs i fi ti,
    t = TPtr Unchecked (TStruct T) ->
    StructDef.MapsTo T fs D ->
    Fields.MapsTo fi ti fs ->
    List.nth_error (Fields.this fs) i = Some (fi, ti) ->
    n0 = n + Z.of_nat(i) ->
    t0 = TPtr Unchecked ti ->
    word_type ti ->
    step D F
      (s, R) (EFieldAddr (ELit n t) fi)
      (s, R) (RExpr (ELit n0 t0))
| SMallocChecked : forall s H1 H2 w w' H1' n1,
    eval_type_bound s w w' -> malloc_bound w' ->
    allocate D H1 w' = Some (n1, H1') ->
    step D F
      (s, (H1,H2)) (EMalloc Checked w)
      (s, (H1',H2)) (RExpr (ELit n1 (TPtr Checked w')))
| SMallocUnChecked : forall s H1 H2 m w w' H2' n1,
    eval_type_bound s w w' -> malloc_bound w' -> m <> Checked ->
    allocate D H2 w' = Some (n1, H2') ->
    step D F
      (s, (H1,H2)) (EMalloc m w)
      (s, (H1, H2')) (RExpr (ELit n1 (TPtr m w')))
| SMallocHighOOB : forall s R m w t' h l,
    h <= l ->
    eval_type_bound s w t' ->
    get_high t' = Some (Num h) ->
    get_low t' = Some (Num l) ->
    step D F (s, R) (EMalloc m w)  (s, R) RBounds

| SMallocLowOOB : forall s R m w t' l,
    l <> 0 ->
    eval_type_bound s w t' ->
    get_low t' = Some (Num l) ->
    step D F (s, R) (EMalloc m w)  (s, R) RBounds

| SUnchecked : forall s R n vl t t' t'',
    eval_type_bound s t t'' ->
    step D F
      (s, R) (EUnchecked vl t (ELit n t'))
      (s, R) (RExpr (ELit n t''))

| Schecked : forall s R n vl t t' t'',
    eval_type_bound s t t'' ->
    step D F
      (s, R) (Echecked vl t (ELit n t'))
      (s, R) (RExpr (ELit n t''))

| SIfDefTrueNotNTHit : forall s R x n t e1 e2 n1 t1,
    Stack.MapsTo x (n,t) s ->
    step D F (s, R) (EDeref (ELit n t)) (s, R) (RExpr (ELit n1 t1)) ->
    n1 <> 0 -> ~ (NTHit s x) ->
    step D F (s, R) (EIfDef x e1 e2) (s, R) (RExpr e1)
| SIfDefTrueNTHit : forall s R x n t e1 e2 n1 t1,
    Stack.MapsTo x (n,t) s ->
    step D F (s, R) (EDeref (ELit n t)) (s, R) (RExpr (ELit n1 t1)) ->
    n1 <> 0 -> (NTHit s x) ->
    step D F (s, R) (EIfDef x e1 e2) (add_nt_one s x, R) (RExpr e1)
| SIfDefFalse : forall s R x n t e1 e2 t1,
    Stack.MapsTo x (n,t) s ->
    step D F (s, R) (EDeref (ELit n t)) (s, R) (RExpr (ELit 0 t1)) ->
    step D F (s, R) (EIfDef x e1 e2) (s, R) (RExpr e2)
| SIfDefFail : forall s R x n t e1 e2 r,
    Stack.MapsTo x (n,t) s ->
    ~ is_rexpr r
    -> step D F (s, R) (EDeref (ELit n t)) (s, R) r
    -> step D F (s, R) (EIfDef x e1 e2) (s, R) r
| SIfTrue : forall s R n t e1 e2,
    n <> 0 ->
    step D F (s, R) (EIf (ELit n t) e1 e2) (s, R) (RExpr e1)
| SIfFalse : forall s R t e1 e2,
    step D F
      (s, R) (EIf (ELit 0 t) e1 e2)
      (s, R) (RExpr e2).
(*
   | SIfEqTrue : forall s H n t t' e1 e2,
           step D F s H (EIfPtrEq (ELit n t) (ELit n t') e1 e2) s H (RExpr e1)
  | SIfEqFalse : forall s H n n' t t' e1 e2, n <> n' ->
           step D F s H (EIfPtrEq (ELit n t) (ELit n' t') e1 e2) s H (RExpr e2)
  | SIfLtTrue : forall s H n n' t t' e1 e2, n < n' ->
           step D F s H (EIfPtrLt (ELit n t) (ELit n' t') e1 e2) s H (RExpr e1)
  | SIfLtFalse : forall s H n n' t t' e1 e2,  n' <= n ->
           step D F s H (EIfPtrLt (ELit n t) (ELit n' t') e1 e2) s H (RExpr e2).
*)

#[export] Hint Constructors step : sem.

(** ** Reduction *)
Inductive reduce
  (D : structdef)
  (F : FEnv) (cm: mode)
  : mem -> expression -> mode -> mem -> result -> Prop :=
  | RSExp : forall M e m M' e' E,
      step D F M e M' (RExpr e') ->
      m = mode_of' (E) cm ->
      reduce D F cm
        M (in_hole e E)
        m
        M' (RExpr (in_hole e' E))
  | RSHaltNull : forall M e m M' E,
      step D F M e M' RNull ->
      m = mode_of' (E) cm ->
      reduce D F cm
        M (in_hole e E)
        m
        M' RNull
  | RSHaltBounds : forall M e m M' E,
      step D F M e M' RBounds ->
      m = mode_of' (E) cm ->
      reduce D F cm
        M (in_hole e E)
        m
        M' RBounds
  | RUnChecked: forall M l t t' e E,
      eval_type_bound (fst M) t t' ->
      reduce D F cm
        M (in_hole (EUnchecked l t e) E)
        Unchecked
        M (RExpr (in_hole (ELit 0 t') E)). (* rep*)

#[export] Hint Constructors reduce : sem.

Definition reduces (D : structdef) (F:FEnv) (cm: mode) (M : mem) (e : expression) (m:mode): Prop :=
  exists (M' : mem) (r : result), reduce D F cm M e m M' r.

#[export] Hint Unfold reduces : sem.

(* Defining function calls. *)
(** * Static Semantics *)
Definition is_nt_ptr (t : type) : Prop :=
  match t with
  | TPtr m (TNTArray l h t') => True
  | _ => False
  end.

(* equivalence of type based on semantic meaning. *)
(*
Inductive type_eq (S : stack) : type -> type -> Prop :=
| type_eq_refl: forall t , type_eq S t t
| type_eq_left: forall t1 t2, simple_type t1 -> eval_type_bound S t2 = Some t1 -> type_eq S t2 t1
| type_eq_right: forall t1 t2, simple_type t2 -> eval_type_bound S t1 = Some t2 -> type_eq S t1 t2.

(* subtyping relation based on types. *)
Inductive subtype_stack (D: structdef) (Q:theta) (S:stack) : type -> type -> Prop :=
| subtype_same : forall t t',
    subtype D Q t t' -> subtype_stack D Q S t t'
| subtype_left : forall t1 t2 t2',
    simple_type t1 -> eval_type_bound S t2 = Some t2' -> subtype D Q t1 t2' ->
    subtype_stack D Q S t1 t2
| subtype_right : forall t1 t1' t2,
    simple_type t2 -> eval_type_bound S t1 = Some t1' -> subtype D Q t1' t2 ->
    subtype_stack D Q S t1 t2.

(* The join opeartions. *)
Inductive join_type (D : structdef) (Q:theta) (S:stack) : type -> type -> type -> Prop :=
  join_type_front : forall a b, subtype_stack D Q S a b -> join_type D Q S a b b
| join_type_end : forall a b, subtype_stack D Q S b a -> join_type D Q S a b a.
*)
Definition good_lit (H:heap) (n:Z) (t:type):=
  match t with
    TNat => True
  | _ => n <= (Z.of_nat (Heap.cardinal H))
  end.


Inductive is_checked : type -> Prop :=
   is_checked_tnat: is_checked TNat
 | is_checked_tptr: forall t, is_checked (TPtr Checked t).

Inductive is_tainted : type -> Prop :=
   is_tainted_tnat: is_tainted TNat
 | is_tainted_tptr: forall t, is_tainted (TPtr Tainted t).

Definition allQ  (l:list var) (Q:theta):= 
   forall x, In x l -> (exists n, Theta.MapsTo x (NumEq n) Q).

Definition well_bound_vars_type (l:list var) (t:type) :=
   forall x, In x (freeTypeVars t) -> In x l.

Definition eq_subtype (Q:theta) (t1 t3:type) := (exists t2, type_eq Q t1 t2 /\ subtype Q t2 t3).

Axiom eq_subtype_trans: forall Q t1 t2 t3, 
 eq_subtype Q t1 t2 -> eq_subtype Q t2 t3 -> eq_subtype Q t1 t3.

Lemma eq_subtype_q_eq: forall Q Q' t t', Theta.Equal Q Q' -> 
   eq_subtype Q t t' -> eq_subtype Q' t t'.
Proof.
  intros. unfold eq_subtype in *.
  destruct H0. destruct H0.
  exists x. split. eapply type_eq_q_eq; eauto.
  eapply subtype_q_eq;eauto.
Qed.

Lemma eq_subtype_q_conv: forall Q t t' x v, 0 <= v -> 
   eq_subtype (Theta.add x GeZero Q) t t' 
        -> eq_subtype (Theta.add x (NumEq (Num v)) Q) t t'.
Proof.
  intros. unfold eq_subtype in *.
  destruct H0. destruct H0.
  exists x0. split. eapply type_eq_q_conv; eauto.
  eapply subtype_q_conv;eauto.
Qed.


Lemma eq_subtype_subst_1: forall Q t t' x b, ~ Theta.In x Q ->
          eq_subtype (Theta.add x (NumEq b) Q) t t' ->
          eq_subtype Q (subst_type t x b) (subst_type t' x b).
Proof.
Admitted.

Lemma type_eq_simple_same: forall Q t t', simple_type t -> simple_type t' -> 
        type_eq Q t t' -> t = t'.
Proof.
  intros. induction H1; intros;simpl in *; try easy. 
  inv H. inv H0. rewrite IHtype_eq; try easy.
Admitted.

Lemma eq_subtype_simple_same : forall Q t t', simple_type t -> simple_type t' ->
          eq_subtype Q t t' -> subtype Q t t'.
Proof.
  intros. destruct H1. destruct H1. apply type_eq_simple_same in H1; subst. easy. easy.
Admitted.


(* well_typed definition. *)
Inductive well_typed_arg (D: structdef) (F:FEnv) (R : real_heap) (Q: theta)
  (env:env) : mode -> expression -> type -> Prop :=
| ArgLitChecked : forall n t t',
    simple_type t' ->
    well_typed_lit_checked D F (fst R) empty_scope n t' ->
    eq_subtype Q t' t ->
    well_typed_arg D F R Q env Checked (ELit n t') t
| ArgLitUnchecked : forall m n t t',
    ~ is_checked t' ->
    simple_type t' ->
    eq_subtype Q t' t ->
    well_typed_arg D F R Q env m (ELit n t') t
| ArgVar : forall m x t t',
    Env.MapsTo x t' env ->
    eq_subtype Q t' t ->
    well_typed_arg D F R Q env m (EVar x) t.
Inductive well_typed_args {D: structdef} {U:FEnv} {H : real_heap} {Q:theta} :
  env -> mode -> list expression -> list (type) -> list var -> type -> type -> Prop :=
| args_empty : forall env m ta, well_typed_args env m [] [] [] ta ta

| args_many_1 : forall env m e es t vl xl ta ta',
   t <> TNat ->
    well_typed_arg D U H Q env m e t ->
    well_typed_args env m es vl xl ta ta'
    -> well_typed_args env m (e::es) (t::vl) xl ta ta'

| args_many_2 : forall env m e es vl x b xl ta ta',
    get_good_dept e = Some b ->
    well_typed_arg D U H Q env m e TNat ->
    well_typed_args env m es (map (fun a => subst_type a x b) vl) xl (subst_type ta x b) ta'
    -> well_typed_args env m (e::es) (TNat::vl) (x::xl) ta ta'.




Lemma type_eq_is_nat : forall Q t, type_eq Q TNat t -> t = TNat.
Proof.
  intros. inv H. easy.
Qed.


Lemma eq_subtype_nat : forall Q t, eq_subtype Q TNat t -> t = TNat.
Proof.
   intros. inv H. destruct H0. inv H. inv H0. inv H. easy.
Qed.

Lemma eq_subtype_nat_1 : forall Q t, eq_subtype Q t TNat -> t = TNat.
Proof.
   intros. inv H. destruct H0. inv H0. inv H1. inv H. easy.
Qed.

Lemma eq_subtype_ptr : forall Q t m' ta, eq_subtype Q t (TPtr m' ta) -> (exists tb, t = TPtr m' tb).
Proof with (eauto with ty; try easy).
   intros. inv H. destruct H0. inv H0. inv H1; inv H... inv H. inv H2.
   exists (TFun xl t0 tl). easy.
   inv H. inv H2. exists (TFun xl t0 tl). easy.
Qed.


Lemma eq_subtype_nt_ptr : forall Q t t', is_nt_ptr t' -> eq_subtype Q t t' -> is_nt_ptr t.
Proof with (eauto with ty; try easy).
   intros. unfold is_nt_ptr in *. destruct t'... destruct t'... 
   inv H0. destruct H1. inv H1. inv H2; inv H0... inv H3. easy. inv H3. easy.
Qed.

Lemma subtype_nt_ptr_1 : forall Q t t', is_nt_ptr t' -> subtype Q t t' -> subtype_core Q t t'.
Proof with (eauto with ty; try easy).
   intros. unfold is_nt_ptr in *. destruct t'... destruct t'... 
   inv H0. easy.
Qed.

Lemma eq_subtype_fun : forall Q m xl t ts ta,
      eq_subtype Q ta (TPtr m (TFun xl t ts)) ->
       (exists tb tlb, ta = TPtr m (TFun xl tb tlb)
            /\ @subtype empty_theta tb t /\ Forall2 (@subtype empty_theta) ts tlb).
Proof.
  intros. inv H. destruct H0.
  apply subtype_fun in H0 as X1. destruct X1 as [yl [tb [tlb X1]]];subst.
  apply subtype_fun_1 in H0. destruct H0;subst.
  inv H. inv H3.
  exists tb,tlb; easy.
Qed.


Lemma checked_subtype_well_type : forall D F H env t t' n,
simple_type t -> 
simple_type t' -> type_wf D Checked t' ->
@well_typed_lit_checked D F H env n t ->
eq_subtype empty_theta t t' ->
@well_typed_lit_checked D F H env n t'.
Proof.
  intros. induction H3. 
  - apply eq_subtype_nat in H4. subst. constructor.
  - admit.
  - constructor.
Admitted.

Lemma eq_subtype_mode_same :forall Q m t m' t', eq_subtype Q (TPtr m t) (TPtr m' t') -> m = m'.
Proof.
  intros. inv H. inv H0. inv H. inv H1.
  inv H; try easy. easy. easy.
Qed.


(*
Inductive gen_env : env -> list (var * type) -> env -> Prop :=
     | gen_env_empty : forall env, gen_env env [] env
     | gen_env_many : forall x t l env env', gen_env env l env' -> gen_env env ((x,t)::l) (Env.add x t env').


Definition subst_bound_val (x:var) (n:Z) (b:bound) : bound :=
   match b with Num m => Num m
              | Var y m => if (Nat.eqb x y) then Num (n+m) else Var y m
   end.

Fixpoint subst_type_val (x:var) (n:Z) (b:type) : type :=
   match b with TNat => TNat
              | TPtr c t => TPtr c (subst_type_val x n t)
              | TStruct t => TStruct t
              | TArray l h t => TArray (subst_bound_val x n l) (subst_bound_val x n h) (subst_type_val x n t)
              | TNTArray l h t => TNTArray (subst_bound_val x n l) (subst_bound_val x n h) (subst_type_val x n t)
   end.


Definition subst_bound_var (x:var) (n:var) (b:bound) : bound :=
   match b with Num m => Num m
              | Var y m => if (Nat.eqb x y) then (Var n m) else Var y m
   end.

Fixpoint subst_type_var (x:var) (n:var) (b:type) : type :=
   match b with TNat => TNat
              | TPtr c t => TPtr c (subst_type_var x n t)
              | TStruct t => TStruct t
              | TArray l h t => TArray (subst_bound_var x n l) (subst_bound_var x n h) (subst_type_var x n t)
              | TNTArray l h t => TNTArray (subst_bound_var x n l) (subst_bound_var x n h) (subst_type_var x n t)
   end.

Inductive subst_all_arg : var -> expression -> type -> type -> Prop :=
   | subt_arg_lit : forall x n t t', subst_all_arg x (ELit n t) t' (subst_type_val x n t')
   | subt_arg_var : forall x y t', subst_all_arg x (EVar y) t' (subst_type_var x y t').

Inductive subst_all_args : list (var*type) -> list expression -> type -> type -> Prop :=
   | subt_arg_empty : forall t, subst_all_args [] [] t t
   | subt_arg_many_1 : forall x tvl e el t t' t'', subst_all_arg x e t t' ->
                 subst_all_args tvl el t' t'' -> subst_all_args ((x,TNat)::tvl) (e::el) t t''
   | subt_arg_many_2 : forall x tvl e el t t' ta,
         ta <> TNat -> subst_all_args tvl el t t' -> subst_all_args ((x,ta)::tvl) (e::el) t t'.
*)
(*
Inductive to_ext_bound : var -> bound -> bound -> Prop :=
   | to_ext_num : forall x n, to_ext_bound x (Num n) (Num n)
   | to_ext_var_1 : forall x n, to_ext_bound x (Var x n) (ExVar x n)
   | to_ext_var_2 : forall x y n, x <> y -> to_ext_bound x (Var y n) (Var y n)
   | to_ext_exvar : forall x y n, to_ext_bound x (ExVar y n) (ExVar y n).

Inductive to_ext_type : var -> type -> type -> Prop :=
   | to_ext_nat : forall x, to_ext_type x TNat TNat
   | to_ext_ptr : forall x c t t',  to_ext_type x t t' -> to_ext_type x (TPtr c t) (TPtr c t')
   | to_ext_struct : forall x t, to_ext_type x (TStruct t) (TStruct t)
   | to_ext_array : forall x l h t l' h' t', to_ext_bound x l l' -> to_ext_bound x h h' ->
                      to_ext_type x t t' -> to_ext_type x (TArray l h t) (TArray l' h' t')
    | to_ext_ntarray : forall x l h t l' h' t', to_ext_bound x l l' -> to_ext_bound x h h' ->
                      to_ext_type x t t' -> to_ext_type x (TNTArray l h t) (TNTArray l' h' t')
*)

Fixpoint eq_nat (s:stack) (e:expression) :=
  match e with (ELit n TNat) => Some n
             | EVar x => match Stack.find x s with None => None | Some (n,t) => Some n end
             | EPlus e1 e2 =>
               (match eq_nat s e1 with Some n1 =>
                   match eq_nat s e2 with Some n2 => Some (n1 + n2)
                       | _ => None
                   end
                  | _ => None
                end)
              | _ => None
    end.

Definition NTHitVal (t:type) : Prop :=
   match t with | (TPtr m (TNTArray l (Num 0) t)) => True
                | _ => False
   end.

Definition add_nt_one_env (s : env) (x:var) : env :=
   match Env.find x s with | Some (TPtr m (TNTArray l (Num h) t))
                         => Env.add x (TPtr m (TNTArray l (Num (h+1)) t)) s
                              (* This following case will never happen since the type in a stack is always evaluated. *)
                             | _ => s
   end.

(*

Inductive to_ext_bound : var -> bound -> bound -> Prop :=
   | to_ext_num : forall x n, to_ext_bound x (Num n) (Num n)
   | to_ext_var_1 : forall x n, to_ext_bound x (Var x n) (ExVar x n)
   | to_ext_var_2 : forall x y n, x <> y -> to_ext_bound x (Var y n) (Var y n)
   | to_ext_exvar : forall x y n, to_ext_bound x (ExVar y n) (ExVar y n).

Inductive to_ext_type : var -> type -> type -> Prop :=
   | to_ext_nat : forall x, to_ext_type x TNat TNat
   | to_ext_ptr : forall x c t t',  to_ext_type x t t' -> to_ext_type x (TPtr c t) (TPtr c t')
   | to_ext_struct : forall x t, to_ext_type x (TStruct t) (TStruct t)
   | to_ext_array : forall x l h t l' h' t', to_ext_bound x l l' -> to_ext_bound x h h' ->
                      to_ext_type x t t' -> to_ext_type x (TArray l h t) (TArray l' h' t')
    | to_ext_ntarray : forall x l h t l' h' t', to_ext_bound x l l' -> to_ext_bound x h h' ->
                      to_ext_type x t t' -> to_ext_type x (TNTArray l h t) (TNTArray l' h' t')
   | to_ext_ext_1 : forall x t, to_ext_type x (TExt x t) (TExt x t)
   | to_ext_ext_2 : forall x y t t', x <> y -> to_ext_type x t t' -> to_ext_type x (TExt x t) (TExt x t').
*)

(*
Inductive vars_to_ext : list var -> type -> type -> Prop :=
    vars_to_ext_empty : forall t, vars_to_ext [] t t
  | vars_to_ext_many : forall x l t t' t'', to_ext_type x t t'
             -> vars_to_ext l (TExt x t') t'' -> vars_to_ext (x::l) t t''.
*)

(*
Inductive well_bound_args {A:Type}: list (var * type) -> list (var * A) -> type -> Prop :=
    well_bound_args_empty : forall l t, well_bound_vars_type l t -> well_bound_args [] l t
  | well_bound_args_many : forall x t1 tvl l t, well_bound_vars_type l t1
                           -> well_bound_args tvl l t -> well_bound_args ((x,t1)::tvl) l t.

Inductive well_arg_bound_in {A:Type}: list (var * A) -> expression -> Prop :=
   | well_arg_bound_in_lit : forall s v t, well_bound_vars_type s t -> well_arg_bound_in s (ELit v t)
   | well_arg_bound_in_var : forall s x, (exists a, In (x,a) s) -> well_arg_bound_in s (EVar x).

Inductive well_args_bound_in {A:Type}: list (var * A) -> list expression -> Prop :=
   | well_args_bound_empty : forall l, well_args_bound_in l []
   | well_args_bound_many : forall l x xl, well_arg_bound_in l x -> well_args_bound_in l xl -> well_args_bound_in l (x::xl).

Inductive well_expr_bound_in {A:Type}: list (var * A) -> expression -> Prop :=
   | well_expr_bound_in_lit : forall s v t, well_bound_vars_type s t -> well_expr_bound_in s (ELit v t)
   | well_expr_bound_in_var : forall s x, (exists a, In (x,a) s) -> well_expr_bound_in s (EVar x)
   | well_expr_bound_in_str : forall s x,(exists a, In (x,a) s) -> well_expr_bound_in s (EStrlen x)
   | well_expr_bound_in_call : forall s x el, well_args_bound_in s el ->  well_expr_bound_in s (ECall x el)
   | well_expr_bound_in_let : forall s x e1 e2, well_expr_bound_in s e1
           -> well_expr_bound_in s e2 -> well_expr_bound_in s (ELet x e1 e2)
   | well_expr_bound_in_malloc : forall s t, list_type_bound_in s t -> well_expr_bound_in s (EMalloc t)
   | well_expr_bound_in_cast : forall s t e, list_type_bound_in s t ->
                    well_expr_bound_in s e -> well_expr_bound_in s (ECast t e)
   | well_expr_bound_in_dyncast : forall s t e, list_type_bound_in s t ->
                    well_expr_bound_in s e -> well_expr_bound_in s (EDynCast t e)
   | well_expr_bound_in_plus : forall s e1 e2,  well_expr_bound_in s e1 ->
                 well_expr_bound_in s e2 -> well_expr_bound_in s (EPlus e1 e2)
   | well_expr_bound_in_field : forall s e1 f,  well_expr_bound_in s e1 ->
                well_expr_bound_in s (EFieldAddr e1 f)
   | well_expr_bound_in_deref : forall s e,  well_expr_bound_in s e ->
                well_expr_bound_in s (EDeref e)
   | well_expr_bound_in_assign : forall s e1 e2,  well_expr_bound_in s e1 ->
                 well_expr_bound_in s e2 -> well_expr_bound_in s (EAssign e1 e2)
   | well_expr_bound_in_if : forall s x e1 e2, In x s -> well_expr_bound_in s e1 ->
                 well_expr_bound_in s e2 -> well_expr_bound_in s (EIf x e1 e2)
   | well_expr_bound_in_unchecked : forall s e,  well_expr_bound_in s e ->
                well_expr_bound_in s (EUnchecked e).
*)

Fixpoint get_nat_vars (l : list (var * type)) : list var :=
   match l with [] => []
            | (x,TNat)::xl => x::(get_nat_vars xl)
            | (x,t)::xl => (get_nat_vars xl)
   end.

Definition fun_mode_eq (m1 m2 :mode) : Prop :=
   (m2 = Checked /\ m1 = Checked) \/ (m2 = Unchecked /\ (m1 <> Checked)).

Definition mode_leq (m1 m2 :mode) : Prop :=
   (m2 = Checked -> m1 <> Unchecked) /\ (m2 = Unchecked -> (m1 <> Checked)).

(** [mode_comp m1 m2]: variable mode [m1] is compatible in region mode [m2]*)
Inductive mode_comp : mode -> mode -> Prop :=
| MC_Checked : mode_comp Checked Checked
| MC_Unchecked : mode_comp Unchecked Unchecked
| MC_Tainted : forall m, mode_comp Tainted m.


Definition match_mode_ptr (t:type) (m:mode) :Prop :=
    match t with TPtr m1 t => mode_leq m1 m
             | _ => True
    end.

Definition is_off_zero (b:bound) :=
  match b with (Var x n) => (n = 0)
            | _ => True
  end.


(* The CoreChkC Type System. *)
Section Typing. 
  Variable D : structdef.
  Variable F : FEnv.
  Variable H : real_heap.
  Inductive well_typed
    : env -> theta -> mode -> expression -> type -> Prop :=
  | TyLitChecked : forall env Q n t,
      is_checked t ->
      simple_type t ->
      well_typed_lit_checked D F (fst H) empty_scope n t ->
      well_typed env Q Checked (ELit n t) t
  | TyLitTainted : forall env Q m n t,
      ~ is_checked t ->
      simple_type t ->
      well_typed env Q m (ELit n t) t
  | TyVar : forall env Q m x t t',
      Env.MapsTo x t env ->
      subtype_core Q t t' ->
      well_typed env Q m (EVar x) t'

  | TyCall : forall env Q m m' es x xl ts t ta,
      mode_leq m' m ->
      Forall (fun e => env_wf e env) es ->
      well_typed env Q m x (TPtr m' (TFun xl t ts)) ->
      @well_typed_args D F H Q env m es ts xl t ta ->
      well_typed env Q m (ECall x es) ta

  (*
  | TyCallHeap : forall env U Q pm m m' es x tvl t,
      (* get_dept_map tvl es = Some s -> *)
        pm = HeapType ->
        fun_mode_eq m' m ->
        Env.MapsTo x (TPtr m' pm (TFun t tvl)) env ->
        @well_typed_args D U Q H env m es tvl ->
        well_typed env U Q m (ECall x es) t.
   *)

  | TyStrlen : forall env Q x m m' h l t,
      Env.MapsTo x (TPtr m' (TNTArray h l t)) env ->
      mode_leq m' m ->
      well_typed env Q m (EStrlen x) TNat

(*
  | TyLetStrlen : forall env Q m m' x y e l h t ta,
      mode_leq m' m ->
      Env.MapsTo y (TPtr m' (TNTArray l h ta)) env ->
      well_typed (Env.add x TNat (Env.add y (TPtr m' (TNTArray l (Var x 0) ta)) env)) (Theta.add x GeZero Q) m e t ->
      ~ In x (freeTypeVars t) ->
      well_typed env Q m (ELet x (EStrlen y) e) t
*)
  | TyLetNat : forall env Q m x e1 e2 t b,
      well_typed env Q m e1 TNat ->
      well_typed (Env.add x TNat env) (Theta.add x (NumEq b) Q) m e2 t ->
      get_good_dept e1 = Some b ->
      ~ Theta.In x Q ->
      well_typed env Q m (ELet x e1 e2) (subst_type t x b)

  (* | TyLetPtrSame1 : forall env Q m m' x e1 t1 e2 t, *)
  (*     mode_leq m' m -> *)
  (*     well_typed env Q m e1 (TPtr m' t) -> *)
  (*     well_typed (Env.add x t1 env) Q m e2 t -> *)
  (*     ~ In x (get_tvars t) -> *)
  (*     well_typed env Q m (ELet x e1 e2) t *)

  | TyLet : forall env Q m x e1 m' t1 e2 t,
      ~ Theta.In x Q ->
      mode_leq m' m ->
      well_typed env Q m e1 (TPtr m' t1) ->
      well_typed (Env.add x (TPtr m' t1) env) Q m e2 t ->
      well_typed env Q m (ELet x e1 e2) t

  | TyRetTNat : forall env Q m x na e t,
      ~ Theta.In x Q ->
      well_typed (Env.add x TNat env) (Theta.add x (NumEq (Num na)) Q) m e t ->
      well_typed env Q m (ERet x (na,TNat) e) (subst_type t x (Num na))

  | TyRetChecked : forall env Q x na ta e t,
      ~ Theta.In x Q ->
      simple_type (TPtr Checked ta) ->
      well_typed_lit_checked D F (fst H) empty_scope na (TPtr Checked ta) ->
      well_typed (Env.add x (TPtr Checked ta) env) Q Checked e t ->
      well_typed env Q Checked (ERet x (na,TPtr Checked ta) e) t

  | TyRet : forall env Q m m' x na ta e t,
      ~ Theta.In x Q ->
      m' <> Checked ->
      mode_leq m' m ->
      simple_type (TPtr m' ta) ->
      well_typed (Env.add x (TPtr m' ta) env) Q m e t ->
      well_typed env Q m (ERet x (na,TPtr m' ta) e) t

  | TyPlus : forall env Q m e1 e2,
      well_typed env Q m e1 (TNat) ->
      well_typed env Q m e2 (TNat) ->
      well_typed env Q m (EPlus e1 e2) TNat

  | TyFieldAddr : forall env Q m e m' T fs i fi ti,
      mode_leq m' m ->
      well_typed env Q m e (TPtr m' (TStruct T)) ->
      StructDef.MapsTo T fs D ->
      Fields.MapsTo fi ti fs ->
      List.nth_error (Fields.this fs) i = Some (fi, ti) ->
      well_typed env Q m (EFieldAddr e fi) (TPtr m' ti)

  | TyMalloc : forall env Q m m' w,
      mode_leq m' m ->
      ~ is_fun_type w ->
      well_type_bound_in env w ->
      well_typed env Q m (EMalloc m' w) (TPtr m' w)

  | TyUnchecked : forall env Q m vl t t' e,
      list_sub (freeVars e) vl ->
      well_typed env Q Unchecked e t' ->
      eq_subtype Q t' t ->
      Forall (fun x => forall t, Env.MapsTo x t env -> is_tainted t) vl ->
      is_tainted t ->
      well_typed env Q m (EUnchecked vl t e) t

  | Tychecked : forall env Q m vl t t' e,
      list_sub (freeVars e) vl ->
      well_typed env Q Checked e t' ->
      eq_subtype Q t' t ->
      Forall (fun x => forall t, Env.MapsTo x t env -> is_tainted t) vl ->
      is_tainted t ->
      well_typed env Q m (Echecked vl t e) t


  | TyCast1 : forall env Q t e t',
      well_type_bound_in env t ->
      match_mode_ptr t Unchecked ->
      well_typed env Q Unchecked e t' ->
      well_typed env Q Unchecked (ECast t e) t
  | TyCast2 : forall env Q m t e t',
      well_type_bound_in env t ->
      well_typed env Q Checked e t' ->
      eq_subtype Q t' (TPtr m t) ->
      well_typed env Q Checked (ECast (TPtr m t) e) (TPtr m t)

  | TyDynCast1 : forall env Q m e x y u v t t',
      well_type_bound_in env (TPtr m (TArray x y t)) ->
      well_typed env Q Checked e (TPtr m (TArray u v t')) ->
      type_eq Q t t' ->
      mode_leq m Checked ->
      well_typed env Q Checked (EDynCast (TPtr m (TArray x y t)) e) (TPtr m (TArray x y t))
  | TyDynCast2 : forall env Q m e x y t t',
      word_type t' ->
      type_eq Q t t' ->
      well_type_bound_in env (TPtr m (TArray x y t)) ->
      well_typed env Q Checked e (TPtr m t') ->
      mode_leq m Checked ->
      well_typed env Q Checked (EDynCast (TPtr m (TArray x y t)) e) (TPtr m (TArray x y t))
  | TyDynCast3 : forall env Q m e x y u v t t',
      well_type_bound_in env (TPtr m (TNTArray x y t)) ->
      type_eq Q t t' ->
      well_typed env Q Checked e (TPtr m (TNTArray u v t')) ->
      mode_leq m Checked ->
      well_typed env Q Checked (EDynCast (TPtr m (TNTArray x y t)) e) (TPtr m (TNTArray x y t))

  | TyDynCast4 : forall env Q m e x y u v t t',
      well_type_bound_in env (TPtr m (TArray x y t)) ->
      type_eq Q t t' ->
      well_typed env Q Checked e (TPtr m (TNTArray u v t')) ->
      mode_leq m Checked ->
      well_typed env Q Checked (EDynCast (TPtr m (TArray x y t)) e) (TPtr m (TArray x y t))


  | TyDeref : forall env Q m e m' t l h t',
      well_typed env Q m e t ->
      ((word_type t' /\ t = TPtr m' t')
       \/ (t = TPtr m' (TArray l h t') /\ word_type t' /\ type_wf D  m' t')
       \/ (t = TPtr m' (TNTArray l h t') /\ word_type t' /\ type_wf D  m' t')) ->
      mode_leq m' m ->
      well_typed env Q m (EDeref e) t'

  | TyIndex1 : forall env Q m e1 m' l h e2 t,
      word_type t -> type_wf D m' t ->
      well_typed env Q m e1 (TPtr m' (TArray l h t)) ->
      well_typed env Q m e2 (TNat) ->
      mode_leq m' m ->
      well_typed env Q m (EDeref (EPlus e1 e2)) t
  | TyIndex2 : forall env Q m e1 m' l h e2 t,
      word_type t -> type_wf D m' t ->
      well_typed env Q m e1 (TPtr m' (TNTArray l h t)) ->
      well_typed env Q m e2 (TNat) ->
      mode_leq m' m ->
      well_typed env Q m (EDeref (EPlus e1 e2)) t

  | TyAssign1 : forall env Q m e1 e2 m' t t1,
      subtype Q t1 t -> word_type t ->
      well_typed env Q m e1 (TPtr m' t) ->
      well_typed env Q m e2 t1 ->
      mode_leq m' m ->
      well_typed env Q m (EAssign e1 e2) t
(*
  | TyAssignFun : forall env Q m e1 e2 m' b t ts,
      well_typed env Q m e1 (TPtr m' (TFun b [] t ts)) ->
      well_typed env Q m e2 TNat ->
      mode_leq m' m -> is_off_zero b ->
      well_typed env Q m (EAssign e1 e2) TNat
*)
  | TyAssign2 : forall env Q m e1 e2 m' l h t t',
      word_type t -> type_wf D m' t -> subtype Q t' t ->
      well_typed env Q m e1 (TPtr m' (TArray l h t)) ->
      well_typed env Q m e2 t' ->
      mode_leq m' m ->
      well_typed env Q m (EAssign e1 e2) t
  | TyAssign3 : forall env Q m e1 e2 m' l h t t',
      word_type t -> type_wf D m' t ->
      subtype Q t' t  ->
      well_typed env Q m e1 (TPtr m' (TNTArray l h t)) ->
      well_typed env Q m e2 t' ->
      mode_leq m' m ->
      well_typed env Q m (EAssign e1 e2) t

  | TyIndexAssign1 : forall env Q m e1 e2 e3 m' l h t t',
      word_type t' -> type_wf D m' t' ->
      subtype Q t' t ->
      well_typed env Q m e1 (TPtr m' (TArray l h t)) ->
      well_typed env Q m e2 (TNat) ->
      well_typed env Q m e3 t' ->
      mode_leq m' m ->
      well_typed env Q m (EAssign (EPlus e1 e2) e3) t
  | TyIndexAssign2 : forall env Q m e1 e2 e3 m' l h t t',
      word_type t' -> type_wf D m' t' ->
      subtype Q t' t ->
      well_typed env Q m e1 (TPtr m' (TNTArray l h t)) ->
      well_typed env Q m e2 (TNat) ->
      well_typed env Q m e3 t' ->
      mode_leq m' m ->
      well_typed env Q m (EAssign (EPlus e1 e2) e3) t

  | TyIfDef : forall env Q m m' x t t1 e1 e2 t2,
      Env.MapsTo x t env ->
      subtype Q t (TPtr m' t1) ->
      (exists l h t', (word_type t1 /\ t1 = t')
                      \/ (t1 = TArray l h t' /\ word_type t' /\ type_wf D m' t')
                      \/ (t1 = TNTArray l h t' /\ word_type t' /\ type_wf D m' t')) ->
      well_typed env Q m e1 t2 -> well_typed env Q m e2 t2 ->
      mode_leq m' m ->
      well_typed env Q m (EIfDef x e1 e2) t2

  | TyIfDefNT : forall env Q m m' x l t e1 e2 t2,
      Env.MapsTo x (TPtr m' (TNTArray l (Var x 0) t)) env ->
      well_typed (Env.add x (TPtr m' (TNTArray l (Var x 1) t)) env) Q m e1 t2
      -> well_typed env Q m e2 t2 ->
      (m' = Unchecked -> m = Unchecked) ->
      well_typed env Q m (EIfDef x e1 e2) t2


  | TyIf : forall env Q m e1 e2 e3 t2,
      well_typed env Q m e1 TNat ->
      well_typed env Q m e2 t2 ->
      well_typed env Q m e3 t2 ->
      well_typed env Q m (EIf e1 e2 e3) t2.
End Typing.
#[export] Hint Constructors well_typed : ty.

Inductive fun_arg_wf {D : structdef} {m:mode}: list var -> list var -> list (var * type) -> Prop :=
  fun_arg_empty : forall AS, fun_arg_wf [] AS nil
| fun_arg_many_1 : forall xl AS x t tvl, t <> TNat -> fun_arg_wf xl AS tvl ->
                                      word_type t -> type_wf D m t -> well_bound_vars_type AS t
                                      -> fun_arg_wf xl AS ((x,t)::tvl)
| fun_arg_many_2 : forall xl AS x tvl, fun_arg_wf xl (x::AS) tvl -> fun_arg_wf (x::xl) AS ((x,TNat)::tvl).

Definition fun_wf (D : structdef) (F:FEnv) (H:real_heap) :=
    (forall m, F m 0 = None) /\
    (forall env Q f tvl t ta e vl ea m m',
        mode_leq m' m ->
        F m' f = Some (tvl,t,e) ->
        eval_vl vl tvl (get_xl tvl) e t ea ta ->
        @fun_arg_wf D m (get_xl tvl) [] tvl /\ NoDup (fst (List.split tvl)) /\
          word_type t /\
          type_wf D m t /\
          well_bound_vars_type (get_xl tvl) t /\
          expr_wf D m e /\
          @well_typed D (F) H env Q m ea ta).


Definition sub_domain (env: env) (S:stack) := forall x,
    Env.In x env -> Stack.In x S.

Definition same_domain (env: env) (S:stack) := forall x,
    Env.In x env <-> Stack.In x S.

Local Close Scope Z_scope.
Local Open Scope nat_scope.
