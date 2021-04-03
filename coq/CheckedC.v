Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Structures.Monads.

From CHKC Require Import Tactics ListUtil Map.

(** * Document Conventions *)


(** It is common when defining syntax for a language on paper to associate one or manysimple_type
    _metavariables_ with each syntactic class. For example, the metavariables <<x>>, <<y>>,
    and <<z>> are often used to represent the syntactic class of program variables. It is
    understood that wherever these metavariables appear they indicate an implicit universalf
    quantification over all members of the syntactic class they represent. In Coq, however,Rq


    we have no such issue -- all quantification must be made explicit. However, we must still
    grapple with the hardest problem in computer science: naming our quantified variables.
    To ameliorate this problem, we maintain two stylistic invariants.

    - (1) Whenever a new piece of syntax is introduced we we will include, in parentheses,
          its associated metavariable. We will then use this as the naming convention for
          naming universally quantified variables in the future.
    - (2) Whenever syntax, semantics, or proofs appear in the associated paper
          ("Checked C for Safety, Gradually") we take this to be an authoritative source
          for naming. *)

(** * Syntax *)

(** The types [var], [field], and [struct] are the (distinguished) syntactic classes of program variables ([x]), fields ([f]), and structures [T])
    respectively. They are all implemented concretely as natural numbers. Each is a distinguished class of identifier in the syntax of
    the language. *)
Require Export Psatz.
Require Export Bool.
Require Export Arith.
Require Export Psatz.
Require Export Program.
Require Export List.
Require Import ZArith.
Require Import ZArith.BinIntDef.
Require Export Reals.
Export ListNotations.

(*
Notation "¬ b" := (negb b) (at level 10).
Infix  "⊕" := xorb (at level 20).

Lemma xorb_nb_b : forall b, ¬ b ⊕ b = true. Proof. destruct b; easy. Qed.
Lemma xorb_b_nb : forall b, b ⊕ ¬ b = true. Proof. destruct b; easy. Qed.

Lemma xorb_involutive_l : forall b b', b ⊕ (b ⊕ b') = b'. Proof. destruct b, b'; easy. Qed.
Lemma xorb_involutive_r : forall b b', b ⊕ b' ⊕ b' = b. Proof. destruct b, b'; easy. Qed.

Lemma andb_xorb_dist : forall b b1 b2, b && (b1 ⊕ b2) = (b && b1) ⊕ (b && b2).
Proof. destruct b, b1, b2; easy. Qed.

Lemma beq_reflect : forall x y, reflect (x = y) (x =? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry.  apply beq_nat_true_iff.
Qed.

Lemma blt_reflect : forall x y, reflect (x < y) (x <? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry. apply Nat.ltb_lt.
Qed.

Lemma ble_reflect : forall x y, reflect (x <= y) (x <=? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry. apply Nat.leb_le.
Qed.

Hint Resolve blt_reflect ble_reflect beq_reflect : bdestruct.

Ltac bdestruct X :=
  let H := fresh in let e := fresh "e" in
   evar (e: Prop);
   assert (H: reflect e X); subst e;
    [eauto with bdestruct
    | destruct H as [H|H];
       [ | try first [apply not_lt in H | apply not_le in H]]].

Ltac bdestructΩ X := bdestruct X; simpl; try lia.
*)
Require Export BinNums.
Require Import BinPos BinNat.

Local Open Scope Z_scope.


Definition var    := nat.
Definition field  := nat.
Definition struct := nat.
Definition funid := nat.

(* Useful shorthand in case we ever change representation. *)
Definition var_eq_dec := Nat.eq_dec.

(** The Mode ([m]) is

The [mode], indicated by metavariable [m], is either [Checked] or [Unchecked]. *)

Inductive mode : Type :=
  | Checked : mode
  | Unchecked : mode.

(** Types, <<w>>, are either a word type, [TNat, TPtr], a struct type, [TStruct],
    or an array type, [TArray]. Struct types must be annotated with a struct identifier.
    Array types are annotated with their lower-bound, upper-bound, and the (word) type of their elements.

    The metavariable, [w], was chosen to abbreviate "wide" or compound types.

    Notice that struct types can be self-referential. Furthermore, they are the only type
    which may be self-referential.

    Example:

    In

      struct foo {
        self^struct foo
      }

      let my_foo = malloc@struct foo in
      let my_foo_self = &my_foo->self in
      *my_foo_self = my_foo

    the memory location which holds the `self` field of `my_foo` contains a pointer which
    refers back to `my_foo`. Thus, `my_foo` is self-referential. *)

(* a bound is either a value or a expression as the form of var + num. *)
Inductive bound : Set := | Num : Z -> bound | Var : var -> Z -> bound.

Inductive type : Type :=
  | TNat : type
  | TPtr : mode -> type -> type
  | TStruct : struct -> type
  | TArray : bound -> bound -> type -> type
  | TNTArray : bound -> bound -> type -> type.


(** Word types, <<t>>, are either numbers, [WTNat], or pointers, [WTPtr].
    Pointers must be annotated with a [mode] and a (compound) [type]. *)


Inductive word_type : type -> Prop :=
  | WTNat : word_type (TNat)
  | WTPtr : forall m w, word_type (TPtr m w).

Hint Constructors word_type.

(** Fields, [fs], are a vector of fields paired with their (word) type.
    We represent this as a finite list map. The keys are the field identifier, and the
    values are its (word) type.
 *)

Require Import OrderedTypeEx.

Module Fields := FMapList.Make Nat_as_OT.

Definition fields := Fields.t type.

(** Structdefs, [D], are a map of structures to fields.

    Structdefs also have a well-formedness predicate. This says that a structdef
    cannot reference structures that it does not define. *)

Module StructDef := Map.Make Nat_as_OT.

Definition structdef := StructDef.t fields.

(*
Inductive none_bound_only : bound -> Prop :=
    | none_bound_only_1: forall n, none_bound_only (Num n)
    | none_bound_only_2: forall x y, none_bound_only (Var x y None).
*)


Module Env := Map.Make Nat_as_OT.

Definition env := Env.t type.

Definition empty_env := @Env.empty type.

(* well_bound definition might not needed in the type system, since the new expr_wf will guarantee that. *)
Inductive well_bound_in : env -> bound -> Prop :=
   | well_bound_in_num : forall env n, well_bound_in env (Num n)
   | well_bound_in_var : forall env x y, Env.In x env -> well_bound_in env (Var x y).

Inductive well_type_bound_in : env -> type -> Prop :=
   | well_type_bound_in_nat : forall env, well_type_bound_in env TNat
   | well_type_bound_in_ptr : forall m t env, well_type_bound_in env t -> well_type_bound_in env (TPtr m t)
   | well_type_bound_in_struct : forall env T, well_type_bound_in env (TStruct T)
   | well_type_bound_in_array : forall env l h t, well_bound_in env l -> well_bound_in env h -> 
                                      well_type_bound_in env t -> well_type_bound_in env (TArray l h t)
   | well_type_bound_in_ntarray : forall env l h t, well_bound_in env l -> well_bound_in env h -> 
                                      well_type_bound_in env t -> well_type_bound_in env (TNTArray l h t).

Inductive simple_type : type -> Prop := 
  | SPTNat : simple_type TNat
  | SPTPtr : forall m w, simple_type w -> simple_type (TPtr m w)
  | SPTStruct : forall t, simple_type (TStruct t)
  | SPTArray : forall l h t, simple_type t -> simple_type (TArray (Num l) (Num h) t)
  | SPTNTArray : forall l h t, simple_type t -> simple_type (TNTArray (Num l) (Num h) t).

Inductive type_wf (D : structdef) : type -> Prop :=
  | WFTNat : type_wf D (TNat)
  | WFTPtr : forall m w, type_wf D w -> type_wf D (TPtr m w)
  | WFTStruct : forall T,
      (exists (fs : fields), StructDef.MapsTo T fs D) ->
      type_wf D (TStruct T)
  | WFArray : forall l h t,
      word_type t ->
      type_wf D t ->
      type_wf D (TArray l h t)
  | WFNTArry : forall l h t,       
      word_type t ->
      type_wf D t ->
      type_wf D (TNTArray l h t).


Definition fields_wf (D : structdef) (fs : fields) : Prop :=
  forall f t,
    Fields.MapsTo f t fs ->
    word_type t /\ type_wf D t /\ simple_type t.

Definition structdef_wf (D : structdef) : Prop :=
  forall (T : struct) (fs : fields),
    StructDef.MapsTo T fs D ->
    fields_wf D fs.

(* This defines the subtyping relation. *)
Inductive nat_leq : bound -> bound -> Prop :=
  | nat_leq_num : forall l h, l <= h -> nat_leq (Num l) (Num h)
  | nat_leq_var : forall x l h, l <= h -> nat_leq (Var x l) (Var x h).

Lemma nat_leq_trans : forall a b c, nat_leq a b -> nat_leq b c -> nat_leq a c.
Proof.
  intros.
  destruct a. destruct b. destruct c.
  inv H. inv H0.
  apply nat_leq_num. lia.
  inv H0.
  inv H.
  destruct b. inv H.
  destruct c. inv H0.
  inv H. inv H0.
  apply nat_leq_var. lia.
Qed.

Inductive subtype (D : structdef) : type -> type -> Prop :=
  | SubTyRefl : forall t, subtype D t t
  | SubTyBot : forall m l h t, word_type t -> nat_leq (Num 0) l -> nat_leq h (Num 1)
                           -> subtype D (TPtr m t) (TPtr m (TArray l h t))
  | SubTyOne : forall m l h t, word_type t -> nat_leq l (Num 0) -> nat_leq (Num 1) h
                             -> subtype D (TPtr m (TArray l h t)) (TPtr m t)
  | SubTyOneNT : forall m l h t, word_type t -> nat_leq l (Num 0) ->nat_leq (Num 1) h
                             -> subtype D (TPtr m (TNTArray l h t)) (TPtr m t)
  | SubTySubsume : forall l h l' h' t m,
    nat_leq l l' -> nat_leq h' h -> 
    subtype D (TPtr m (TArray l h t)) (TPtr m (TArray l' h' t))
  | SubTyNtArray : forall l h l' h' t m,
    nat_leq l l' -> nat_leq h' h ->
                subtype D (TPtr m (TNTArray l h t)) (TPtr m (TArray l' h' t))
  | SubTyNtSubsume : forall l h l' h' t m,
    nat_leq l l' -> nat_leq h' h -> 
    subtype D (TPtr m (TNTArray l h t)) (TPtr m (TNTArray l' h' t))
  | SubTyStructArrayField_1 : forall (T : struct) (fs : fields) m,
    StructDef.MapsTo T fs D ->
    Some (TNat) = (Fields.find 0%nat fs) ->
    subtype D (TPtr m (TStruct T)) (TPtr m (TNat))
  | SubTyStructArrayField_2 : forall (T : struct) (fs : fields) m l h,
    StructDef.MapsTo T fs D ->
    Some (TNat) = (Fields.find 0%nat fs) -> nat_leq (Num 0) l -> nat_leq h (Num 1) ->
    subtype D (TPtr m (TStruct T)) (TPtr m (TArray l h (TNat))).

Lemma subtype_trans : forall D t t' m w, subtype D t (TPtr m w) -> subtype D (TPtr m w) t' -> subtype D t t'.
Proof.
 intros. inv H; inv H0.
      * eapply SubTyRefl.
      * eapply SubTyBot;eauto.
      * eapply SubTyOne; eauto.
      * eapply SubTyOneNT; eauto.
      * eapply SubTySubsume; eauto.
      * eapply SubTyNtArray; eauto.
      * eapply SubTyNtSubsume; eauto.
      * eapply SubTyStructArrayField_1; eauto.
      * eapply SubTyStructArrayField_2; eauto.
      * eapply SubTyBot; eauto.
      * inv H2.
      * eapply SubTyRefl.
      * eapply SubTyBot;eauto. eapply nat_leq_trans. apply H5. assumption.
         eapply nat_leq_trans. apply H9. assumption.
      * eapply SubTyOne; eauto.
      * eapply SubTySubsume;eauto.
        eapply nat_leq_trans. apply H5. assumption.
        eapply nat_leq_trans. apply H8. assumption.
      * inv H3.
      * inv H3.
      * inv H3.
      * inv H3.
      * inv H3.
      * inv H3.
      * inv H3.
      * eapply SubTyOneNT; eauto.
      * eapply SubTyNtArray; eauto.
        eapply nat_leq_trans. apply H5. assumption.
        eapply nat_leq_trans. apply H8. assumption.
      * inv H3.
      * inv H3.
      * inv H3.
      * inv H3.
      * inv H3.
      * inv H3.
      * inv H3.
      * eapply SubTySubsume; eauto.
      * inv H2.
      * eapply SubTyOne; eauto.
        eapply nat_leq_trans. apply H4. assumption.
        eapply nat_leq_trans. apply H9. assumption.
      * eapply SubTySubsume; eauto.
        eapply nat_leq_trans. apply H4. assumption.
        eapply nat_leq_trans. apply H8. assumption.
      * eapply SubTyNtArray; eauto.
      * inv H2.
      * eapply SubTyOneNT; eauto.
        eapply nat_leq_trans. apply H4. assumption.
        eapply nat_leq_trans. apply H9. assumption.
      * eapply SubTyNtArray; eauto.
        eapply nat_leq_trans. apply H4. assumption.
        eapply nat_leq_trans. apply H8. assumption.
      * eapply SubTyNtSubsume; eauto.
      * inv H2.
      * eapply SubTyOneNT; eauto.
        eapply nat_leq_trans. apply H4. assumption.
        eapply nat_leq_trans. apply H9. assumption.
      * eapply SubTyNtArray; eauto.
        eapply nat_leq_trans. apply H4. assumption.
        eapply nat_leq_trans. apply H8. assumption.
      * eapply SubTyNtSubsume; eauto.
        eapply nat_leq_trans. apply H4. assumption.
        eapply nat_leq_trans. apply H8. assumption.
      * eapply SubTyStructArrayField_1; eauto.
      * eapply SubTyStructArrayField_2; eauto.
      * eapply SubTyStructArrayField_2; eauto.
      * inv H2.
      * eapply SubTyStructArrayField_1; eauto.
      * eapply SubTyStructArrayField_2; eauto.
        eapply nat_leq_trans. apply H6. assumption.
        eapply nat_leq_trans. apply H10. assumption.
Qed.

Inductive expression : Type :=
  | ELit : Z -> type -> expression
  | EVar : var -> expression
  | EStrlen : var -> expression
  | ECall : funid -> list expression -> expression
  | EDynCast : type -> expression -> expression
  | ELet : var -> expression -> expression -> expression
  | EMalloc : type -> expression
  | ECast : type -> expression -> expression
  | EPlus : expression -> expression -> expression
  | EFieldAddr : expression -> field -> expression
  | EDeref : expression -> expression (*  * e *)
  | EAssign : expression -> expression -> expression (* *e = e *)
  | EIf : var -> expression -> expression -> expression (* if * x then e1 else e2. *)
  | EUnchecked : expression -> expression.



Module FEnv := Map.Make Nat_as_OT.

Definition fenv := FEnv.t (list (var * type) * type * expression).

Definition empty_fenv := @Env.empty (list (var * type) * type * expression).



(* Defining stack. *)
Module Stack := Map.Make Nat_as_OT.

Definition stack := Stack.t (Z * type).

Definition empty_stack := @Stack.empty (Z * type).

Definition cast_bound (s:stack) (b:bound) : option bound :=
   match b with Num n => Some (Num n)
             | Var x n => (match (Stack.find x s) with Some (v,t) => Some (Num (n+v)) | None => None end)
   end.

Inductive cast_type_bound (s:stack) : type -> type -> Prop :=
   | cast_type_bound_nat : cast_type_bound s (TNat) (TNat)
   | cast_type_bound_ptr : forall c t t', cast_type_bound s t t'
                 -> cast_type_bound s (TPtr c t) (TPtr c t')
   | cast_type_bound_array : forall l l' h h' t t', cast_bound s l = Some l' -> cast_bound s h = Some h' ->
                  cast_type_bound s t t' -> cast_type_bound s (TArray l h t) (TArray l' h' t')
   | cast_type_bound_ntarray : forall l l' h h' t t', cast_bound s l = Some l' -> cast_bound s h = Some h' ->
                  cast_type_bound s t t' -> cast_type_bound s (TNTArray l h t) (TNTArray l' h' t')
   | cast_type_bound_struct : forall t, cast_type_bound s (TStruct t) (TStruct t).


Inductive well_expr_bound_in : stack -> expression -> Prop :=
   | well_expr_bound_in_lit : forall s v t t', cast_type_bound s t t' 
                                   -> well_expr_bound_in s (ELit v t)
   | well_expr_bound_in_var : forall s x, Stack.In x s -> well_expr_bound_in s (EVar x)
   | well_expr_bound_in_call : forall s x el, 
         (forall e, In e el -> well_expr_bound_in s e) ->  well_expr_bound_in s (ECall x el)
   | well_expr_bound_in_let : forall s x e1 e2, well_expr_bound_in s e1 
           -> well_expr_bound_in s e2 -> well_expr_bound_in s (ELet x e1 e2)
   | well_expr_bound_in_malloc : forall s t t', cast_type_bound s t t'
                     -> well_expr_bound_in s (EMalloc t)
   | well_expr_bound_in_cast : forall s t e t', cast_type_bound s t t' ->
                    well_expr_bound_in s e -> well_expr_bound_in s (ECast t e)
   | well_expr_bound_in_plus : forall s e1 e2,  well_expr_bound_in s e1 ->
                 well_expr_bound_in s e2 -> well_expr_bound_in s (EPlus e1 e2)
   | well_expr_bound_in_field : forall s e1 f,  well_expr_bound_in s e1 ->
                well_expr_bound_in s (EFieldAddr e1 f)
   | well_expr_bound_in_deref : forall s e,  well_expr_bound_in s e ->
                well_expr_bound_in s (EDeref e)
   | well_expr_bound_in_assign : forall s e1 e2,  well_expr_bound_in s e1 ->
                 well_expr_bound_in s e2 -> well_expr_bound_in s (EAssign e1 e2)
   | well_expr_bound_in_if : forall s x e1 e2, Stack.In x s -> 
             well_expr_bound_in s e1 ->
                 well_expr_bound_in s e2 -> well_expr_bound_in s (EIf x e1 e2)
   | well_expr_bound_in_unchecked : forall s e,  well_expr_bound_in s e ->
                well_expr_bound_in s (EUnchecked e).
   

(** Expressions, [e], compose to form programs in Checked C. It is a core, imperative
    calculus of explicit memory management based on C. Literals, [ELit], are annotated
    with their word type. Memory allocation, [EMalloc], is annotated with a type rather
    than a number (as in C). The amount of memory to be allocated can then be computed
    from the type. Unchecked regions, [EUnchecked], are used to delimit code which may
    perform unsafe (as defined by the type system) operations. The rest of the language
    is standard.

    Expressions also have a well-formedness predicate, parameterized by a structdef. This
    says that any (word or compound) types cannot reference structures that are not defined
    by the structdef.

    Finally, we define a function [subst] over expressions which takes a variable, [x], an
    expression, [v], and an expression, [e], and returns [e] with [v] substituted for [x].
    Even though [v] can be an arbitrary expression, it is expected that callers will only
    ever provide a value (defined below). *)

(*
Inductive stack :=
 | Empty : stack
 | Stack : var * (Z * type) -> stack -> stack.

Definition pop (s : stack) :=
  match s with
  | Empty => None
  | Stack v s0 => Some v
  end.

Fixpoint lookup (x : var) (s : stack) :=
  match s with
  | Empty  => None
  | Stack (x0, v) s0 => if (var_eq_dec x x0) then Some v else (lookup x s0)
  end.
*)



Definition is_check_array_ptr (t:type) : Prop :=
  match t with TPtr Checked (TArray l h t') => True
             | TPtr Checked (TNTArray l h t') => True
             | _ => False
  end.

Definition is_array_ptr (t:type) : Prop :=
  match t with TPtr m (TArray l h t') => True
             | TPtr m (TNTArray l h t') => True
             | _ => False
  end.


Inductive expr_wf (D : structdef) (F: fenv) : expression -> Prop :=
  | WFELit : forall n t,
    word_type t ->
    type_wf D t ->
    expr_wf D F (ELit n t)
  | WFEVar : forall x,
      expr_wf D F (EVar x)
  | WFECall : forall x el, 
      FEnv.In x F ->
      (forall e, In e el -> (exists n t, e = ELit n t
                 /\ word_type t /\ type_wf D t) \/ (exists y, e = EVar y)) ->
      expr_wf D F (ECall x el)
  | WFEDynCast : forall t e, 
     is_array_ptr t -> type_wf D t
           -> expr_wf D F e -> expr_wf D F (EDynCast t e)
  | WFELet : forall x e1 e2,
      expr_wf D F e1 ->
      expr_wf D F e2 ->
      expr_wf D F (ELet x e1 e2)
  | WFEIF : forall x e1 e2,
      expr_wf D F e1 ->
      expr_wf D F e2 ->
      expr_wf D F (EIf x e1 e2)
  | WFEMalloc : forall w,
      type_wf D w ->
      expr_wf D F (EMalloc w)
  | WFECast : forall t e,
      word_type t ->
      type_wf D t ->
      expr_wf D F e ->
      expr_wf D F (ECast t e)
  | WFEPlus : forall e1 e2,
      expr_wf D F e1 ->
      expr_wf D F e2 ->
      expr_wf D F (EPlus e1 e2)
  | WFEFieldAddr : forall e f,
      expr_wf D F e ->
      expr_wf D F (EFieldAddr e f)
  | WFEDeref : forall e,
      expr_wf D F e ->
      expr_wf D F (EDeref e)
  | WFEAssign : forall e1 e2,
      expr_wf D F e1 ->
      expr_wf D F e2 ->
      expr_wf D F (EAssign e1 e2)
  | WFEUnchecked : forall e,
      expr_wf D F e ->
      expr_wf D F (EUnchecked e).

(* Standard substitution.
   In a let, if the bound variable is the same as the one we're substituting,
   then we don't substitute under the lambda. *)

Definition var_subst_bound (b:bound) (x:var) (z:var) : bound :=
   match b with Num n => Num n
              | Var x' n => Var (if var_eq_dec x' x then z else x') n
   end.

Fixpoint var_subst_type (t:type) (x:var) (z:var) : type :=
   match t with TNat => TNat
             | TPtr m t' => TPtr m (var_subst_type t' x z)
             | TStruct t' => TStruct t'
             | TArray b1 b2 t' => TArray (var_subst_bound b1 x z) (var_subst_bound b2 x z) (var_subst_type t' x z)
             | TNTArray b1 b2 t' => TNTArray (var_subst_bound b1 x z) (var_subst_bound b2 x z) (var_subst_type t' x z)
   end.
 
Fixpoint var_subst (e : expression) (x : var) (z : var) : expression :=
  match e with
  | ELit n t => ELit n (var_subst_type t x z)
  | EStrlen x' => EStrlen (if var_eq_dec x' x then z else x')
  | EVar y => if var_eq_dec x y then EVar z else e
  | ECall x el => ECall x (map (fun e' => var_subst e' x z) el)
  | ELet x' e1 e2 =>
    if var_eq_dec x x' then ELet x' (var_subst e1 x z) e2 else ELet x' (var_subst e1 x z) (var_subst e2 x z)
  | EIf x' e1 e2 => EIf (if var_eq_dec x' x then z else x') (var_subst e1 x z) (var_subst e2 x z)
  | EMalloc w => EMalloc (var_subst_type w x z)
  | ECast t e' => ECast (var_subst_type t x z) (var_subst e' x z)
  | EDynCast t e' => EDynCast (var_subst_type t x z) (var_subst e' x z)
  | EPlus e1 e2 => EPlus (var_subst e1 x z) (var_subst e2 x z)
  | EFieldAddr e' f => EFieldAddr (var_subst e' x z) f
  | EDeref e' => EDeref (var_subst e' x z)
  | EAssign e1 e2 => EAssign (var_subst e1 x z) (var_subst e2 x z)
  | EUnchecked e' => EUnchecked (var_subst e' x z)
  end.

(** Values, [v], are expressions [e] which are literals. *)

Inductive value (D : structdef) : expression -> Prop :=
  VLit : forall (n : Z) (t : type),
    word_type t ->
    type_wf D t ->
    value D (ELit n t).

Hint Constructors value.

(** Note: Literal is a less strong version of value that doesn't
    enforce the syntactic constraints on the literal type. *)

Inductive literal : expression -> Prop :=
  Lit : forall (n : Z) (t : type),
    literal (ELit n t).

Hint Constructors literal.

(** * Dynamic Semantics *)

(** Heaps, [H], are a list of literals indexed by memory location.
    Memory locations are just natural numbers, and literals are
    numbers paired with their type (same as [ELit] constructor).
    Addresses are offset by 1 -- looking up address 7 will translate
    to index 6 in the list.
lls
    Heaps also have a well-formedness predicate, which says that
    all memory locations must be annotated with a well-formed word
    type.

    Finally, the only operation we can perform on a heap is allocation.
    This operation is defined by the partial function [allocate]. This
    function takes [D] a structdef, [H] a heap, and [w] a (compound) type.
    The function is total assuming usual well-formedness conditions of [D] and
    [w]. It gives back a pair [(base, H')] where [base] is the base pointer for
    the allocated region and [H'] is [H] with the allocation. *)


Module Heap := Map.Make Z_as_OT.

Definition heap : Type := Heap.t (Z * type).

Definition heap_wf (D : structdef) (H : heap) : Prop :=
  forall (addr : Z), 0 < addr <= (Z.of_nat (Heap.cardinal H)) <-> Heap.In addr H.

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

(** Results, [r], are an expression ([RExpr]), null dereference error ([RNull]), or
    array out-of-bounds error ([RBounds]). *)

Inductive result : Set :=
  | RExpr : expression -> result
  | RNull : result
  | RBounds : result.

(** Contexts, [E], are expressions with a hole in them. They are used in the standard way,
    for lifting a small-step reduction relation to compound expressions.

    We define two functions on contexts: [in_hole] and [mode_of]. The [in_hole] function takes a context,
    [E] and an expression [e] and produces an expression [e'] which is [E] with its hole filled by [e].
    The [mode_of] function takes a context, [E], and returns [m] (a mode) indicating whether the context has a
    subcontext which is unchecked. *)

Inductive context : Set :=
  | CHole : context
  | CLet : var -> context -> expression -> context
  | CPlusL : context -> expression -> context
  | CPlusR : Z -> type -> context -> context
  | CFieldAddr : context -> field -> context
  | CDynCast : type -> context -> context
  | CCast : type -> context -> context
  | CDeref : context -> context
  | CAssignL : context -> expression -> context
  | CAssignR : Z -> type -> context -> context
  | CUnchecked : context -> context.

Fixpoint in_hole (e : expression) (E : context) : expression :=
  match E with
  | CHole => e
  | CLet x E' e' => ELet x (in_hole e E') e'
  | CPlusL E' e' => EPlus (in_hole e E') e'
  | CPlusR n t E' => EPlus (ELit n t) (in_hole e E')
  | CFieldAddr E' f => EFieldAddr (in_hole e E') f
  | CDynCast t E' => EDynCast t (in_hole e E')
  | CCast t E' => ECast t (in_hole e E')
  | CDeref E' => EDeref (in_hole e E')
  | CAssignL E' e' => EAssign (in_hole e E') e'
  | CAssignR n t E' => EAssign (ELit n t) (in_hole e E')
  | CUnchecked E' => EUnchecked (in_hole e E')
  end.


Fixpoint mode_of (E : context) : mode :=
  match E with
  | CHole => Checked
  | CLet _ E' _ => mode_of E'
  | CPlusL E' _ => mode_of E'
  | CPlusR _ _ E' => mode_of E'
  | CFieldAddr E' _ => mode_of E'
  | CDynCast _ E' => mode_of E'
  | CCast _ E' => mode_of E'
  | CDeref E' => mode_of E'
  | CAssignL E' _ => mode_of E'
  | CAssignR _ _ E' => mode_of E'
  | CUnchecked E' => Unchecked
  end.

Fixpoint compose (E_outer : context) (E_inner : context) : context :=
  match E_outer with
  | CHole => E_inner
  | CLet x E' e' => CLet x (compose E' E_inner) e'
  | CPlusL E' e' => CPlusL (compose E' E_inner) e'
  | CPlusR n t E' => CPlusR n t (compose E' E_inner)
  | CFieldAddr E' f => CFieldAddr (compose E' E_inner) f
  | CDynCast t E' => CDynCast t (compose E' E_inner)
  | CCast t E' => CCast t (compose E' E_inner)
  | CDeref E' => CDeref (compose E' E_inner)
  | CAssignL E' e' => CAssignL (compose E' E_inner) e'
  | CAssignR n t E' => CAssignR n t (compose E' E_inner)
  | CUnchecked E' => CUnchecked (compose E' E_inner)
  end.

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

Lemma compose_unchecked : forall E_outer E_inner,
    mode_of E_inner = Unchecked ->
    mode_of (compose E_outer E_inner) = Unchecked.
Proof.
  intros.
  induction E_outer; try reflexivity; try (simpl; rewrite IHE_outer; reflexivity); try assumption.
Qed.

(* TODO: say more *)
(** The single-step reduction relation, [H; e ~> H'; r]. *)

Definition eval_bound (s:stack) (b:bound) : option bound :=
   match b with Num n => Some (Num n)
             | Var x n => (match (Stack.find x s) with Some (v,t) => Some (Num (v + n)) | None => None end)
   end.

Definition eval_type_bound (s : stack) (t : type) : option type := 
  match t with | TPtr c (TArray l h t) => 
                   match eval_bound s l with None => None
                                         | Some l' => 
                     match eval_bound s h with None => None
                                      | Some h' => 
                                Some (TPtr c (TArray l' h' t))
                     end
                   end
              | TPtr c (TNTArray l h t) => 
                   match eval_bound s l with None => None
                                         | Some l' => 
                     match eval_bound s h with None => None
                                      | Some h' => 
                                Some (TPtr c (TNTArray l' h' t))
                     end
                   end
              | _ => Some t
  end.


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




(*
Lemma cast_type_bound_array_ptr : forall s t,
    cast_type_bound s t = None -> (exists  c l h t', t = TPtr c (TArray l h t') \/ t = TPtr c (TNTArray l h t')).
Proof.
 intros. unfold cast_type_bound in H.
 destruct t; inversion H.
 destruct t; inversion H.
 exists m. exists b. exists b0. exists t.
 left. reflexivity.
 exists m. exists b. exists b0. exists t.
 right. reflexivity.
Qed.
*)

Lemma eval_is_cast_bound : forall s b, 
       eval_bound s b = None -> cast_bound s b = None.
Proof.
  intros. unfold eval_bound in H.
  unfold cast_bound.
  destruct b. assumption.
  destruct (Stack.find (elt:=Z * type) v s).
  destruct p. inversion H.
  reflexivity.
Qed.

Lemma cast_is_eval_bound : forall s b, 
       cast_bound s b = None -> eval_bound s b = None.
Proof.
  intros. unfold cast_bound in H.
  unfold eval_bound.
  destruct b. inversion H.
  destruct (Stack.find (elt:=Z * type) v s).
  destruct p. inversion H.
  reflexivity.
Qed.

(*
Definition add_type (s: stack) (t : type) (nt : option bound) : type :=
   match nt with Some (Num n) =>
    
      (match t with TNat None => TNat None
             | TNat (Some (Num m)) => TNat (Some (Num (n + m)))
             | TNat (Some (Var x m)) => TNat (Some (Var x (n+m)))
             | _ => t
       end)
             | _ => t
   end.
*)

Definition NTHit (s : stack) (x : var) : Prop :=
   match Stack.find x s with | Some (v, TPtr m (TNTArray l h t)) => (cast_bound s h = Some (Num 0))
                          | _ => False
   end.

Definition add_nt_one (s : stack) (x:var) : stack :=
   match Stack.find x s with | Some (v, TPtr m (TNTArray l (Num h) t)) 
                         => Stack.add x (v, TPtr m (TNTArray l (Num (h+1)) t)) s
                              (* This following case will never happen since the type in a stack is always evaluated. *)
                             | Some (v, TPtr m (TNTArray l (Var y n) t))
                           => Stack.add x (v, TPtr m (TNTArray l (Var y (n+1)) t)) s
                             | _ => s
   end.

Definition is_rexpr (r : result) : Prop :=
   match r with RExpr x => True
              | _ => False
   end.

Definition sub_bound (b:bound) (n:Z) : (bound) :=
  match b with Num m => Num (m - n)
           | Var x m => Var x (m - n)
  end.

Definition sub_type_bound (t:type) (n:Z) : type :=
   match t with TPtr Checked (TArray l h t1) => TPtr Checked (TArray (sub_bound l n) (sub_bound h n) t1)
              | TPtr Checked (TNTArray l h t1) => TPtr Checked (TNTArray (sub_bound l n) (sub_bound h n) t1)
              | _ => t
   end.

Definition malloc_bound (t:type) : Prop :=
   match t with (TArray (Num l) (Num h) t) => (l = 0 /\ h > 0)
              | (TNTArray (Num l) (Num h) t) => (l = 0 /\ h > 0)
              | _ => True
   end.

Definition change_strlen_stack (s:stack) (x : var) (m:mode) (t:type) (l:bound) (n n' h:Z) :=
     if (n' - n) <=? h then s else @Stack.add (Z*type) x (n,TPtr m (TNTArray l (Num (n'-n)) t)) s. 

Fixpoint gen_stack (vl:list var)  (es:list expression) (e:expression) : option expression := 
   match vl with [] => Some e
              | (v::vl') => match es with [] => None | e1::el =>
                                    match gen_stack vl' el e with None => None
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

Inductive eval_e : stack -> expression -> expression -> Prop :=
    eval_var : forall s x v t, Stack.MapsTo x (v,t) s -> eval_e s (EVar x) (ELit v t)
  | eval_lit : forall s v t t', cast_type_bound s t t' -> eval_e s (ELit v t) (ELit v t').

Inductive eval_el : stack -> list (var * type) -> list expression -> list expression -> Prop :=
    eval_el_empty : forall s, eval_el s [] [] []
  | eval_el_many : forall s x t t' tvl e el v vl, eval_e s e (ELit v t') ->
                 eval_el (Stack.add x (v,t') s) tvl el vl -> eval_el s ((x,t)::tvl) (e::el) ((ELit v t')::vl).

Inductive gen_e : list (var * type) -> list expression -> expression -> expression -> Prop :=
    gen_e_empty : forall e, gen_e [] [] e e
   | gen_e_many : forall x t xl v vl e e', gen_e xl vl e e' -> gen_e ((x,t)::xl) (v::vl) e (ELet x v e').

Definition is_nor_array_ptr (t:type) : Prop :=
   match t with (TPtr m (TArray x y t')) => True
              | _ => False
   end.

Inductive get_root : type -> type -> Prop :=
    get_root_word : forall m t, word_type t -> get_root (TPtr m t) t
  | get_root_array : forall m l h t, get_root (TPtr m (TArray l h t)) t
  | get_root_ntarray : forall m l h t, get_root (TPtr m (TNTArray l h t)) t.

Definition fresh_up (n:var) := (n+1)%nat.


Inductive step (D : structdef) (F:fenv) : var -> stack -> heap -> expression -> var -> stack -> heap -> result -> Prop :=
  | SVar : forall cx s H x v t,
      (Stack.find x s) = Some (v, t) ->
      step D F
           cx s H (EVar x)
           cx s H (RExpr (ELit v t))
  | Strlen : forall cx s H x n n' m l h t t1, 
     (Stack.find x s) = Some (n,TPtr m (TNTArray l (Num h) t)) ->
     (forall i , n <= i < n' -> (exists n1 t1, Heap.MapsTo n (n1,t1) H /\ n1 <> 0))
      -> Heap.MapsTo (n+n') (0,t1) H ->
            step D F cx s H (EStrlen x) 
              cx (change_strlen_stack s x m t l n n' h) H (RExpr (ELit n' TNat))
  | SCall : forall cx s H x el vl t tvl e e', 
           eval_el s tvl el vl -> 
           FEnv.MapsTo x (tvl,t,e) F -> gen_e tvl vl e e' ->
          step D F cx s H (ECall x el) cx s H (RExpr e')
  | SPlusChecked : forall cx s H n1 t1 t1' n2,
      n1 > 0 -> is_check_array_ptr t1 -> cast_type_bound s t1 t1' ->
      step D F
         cx s H (EPlus (ELit n1 t1) (ELit n2 TNat))
         cx s H (RExpr (ELit (n1 + n2) (sub_type_bound t1' n2)))
  | SPlus : forall cx s H t1 n1 n2,
       ~ is_check_array_ptr t1 -> 
      step D F
        cx s H (EPlus (ELit n1 t1) (ELit n2 TNat))
        cx s H (RExpr (ELit (n1 + n2) t1))
  | SPlusNull : forall cx s H n1 t n2,
      n1 <= 0 -> is_check_array_ptr t ->
      step D F
        cx s H (EPlus (ELit n1 t) (ELit n2 (TNat)))
        cx s H RNull
  | SCast : forall cx s H t n t',
      step D F
        cx s H (ECast t (ELit n t'))
        cx s H (RExpr (ELit n t))

  | SCastNoArray : forall cx s H t n m t',
     ~ is_array_ptr (TPtr m t') -> is_nor_array_ptr t ->
      step D F
        cx s H (EDynCast t (ELit n (TPtr m t')))
        cx s H (RExpr (ELit n (TPtr m (TArray (Num 0) (Num 1) t'))))

  | SCastArray : forall cx s H t n t' l h w l' h' w',
     eval_type_bound s t = Some (TPtr Checked (TArray (Num l) (Num h) w)) ->
      eval_type_bound s t' = Some (TPtr Checked (TArray (Num l') (Num h') w')) ->
          l' <= l -> l < h -> h <= h' ->
      step D F
        cx s H (EDynCast t (ELit n t'))
        cx s H (RExpr (ELit n t))

  | SCastArrayLowOOB1 : forall cx s H t n t' l h w l' h' w',
     eval_type_bound s t = Some (TPtr Checked (TArray (Num l) (Num h) w)) ->
      eval_type_bound s t' = Some (TPtr Checked (TArray (Num l') (Num h') w')) ->
           l < l' -> 
           step D F
        cx s H (EDynCast t (ELit n t')) cx s H RBounds
  | SCastArrayLowOOB2 : forall cx s H t n t' l h w l' h' w',
     eval_type_bound s t = Some (TPtr Checked (TArray (Num l) (Num h) w)) ->
      eval_type_bound s t' = Some (TPtr Checked (TArray (Num l') (Num h') w')) ->
           h <= l -> 
           step D F
        cx s H (EDynCast t (ELit n t')) cx s H RBounds
  | SCastArrayHighOOB1 : forall cx s H t n t' l h w l' h' w',
     eval_type_bound s t = Some (TPtr Checked (TArray (Num l) (Num h) w)) ->
      eval_type_bound s t' = Some (TPtr Checked (TArray (Num l') (Num h') w')) ->
           h' < h -> 
           step D F
        cx s H (EDynCast t (ELit n t')) cx s H RBounds
  | SCastNTArray : forall cx s H t n t' l h w l' h' w',
     eval_type_bound s t = Some (TPtr Checked (TNTArray (Num l) (Num h) w)) ->
      eval_type_bound s t' = Some (TPtr Checked (TNTArray (Num l') (Num h') w')) ->
          l' <= l -> l < h -> h <= h' ->
      step D F
        cx s H (EDynCast t (ELit n t'))
        cx s H (RExpr (ELit n t))
  | SCastNTArrayLowOOB1 : forall cx s H t n t' l h w l' h' w',
     eval_type_bound s t = Some (TPtr Checked (TNTArray (Num l) (Num h) w)) ->
      eval_type_bound s t' = Some (TPtr Checked (TNTArray (Num l') (Num h') w')) ->
           l < l' -> 
           step D F 
        cx s H (EDynCast t (ELit n t')) cx s H RBounds
  | SCastNTArrayLowOOB2 : forall cx s H t n t' l h w l' h' w',
     eval_type_bound s t = Some (TPtr Checked (TNTArray (Num l) (Num h) w)) ->
      eval_type_bound s t' = Some (TPtr Checked (TNTArray (Num l') (Num h') w')) ->
           h <= l -> 
           step D F
        cx s H (EDynCast t (ELit n t')) cx s H RBounds
  | SCastNTArrayHighOOB1 : forall cx s H t n t' l h w l' h' w',
     eval_type_bound s t = Some (TPtr Checked (TNTArray (Num l) (Num h) w)) ->
      eval_type_bound s t' = Some (TPtr Checked (TNTArray (Num l') (Num h') w')) ->
           h' < h -> 
           step D F
        cx s H (EDynCast t (ELit n t')) cx s H RBounds

  | SDeref : forall cx s H n n1 t1 t t2,
      eval_type_bound s t = Some t2 ->
      Heap.MapsTo n (n1, t1) H ->
      (forall l h t', t2 = TPtr Checked (TArray (Num l) (Num h) t') -> h > 0 /\ l <= 0) ->
      (forall l h t', t2 = TPtr Checked (TNTArray (Num l) (Num h) t') -> h > 0 /\ l <= 0) ->
      step D F
        cx s H (EDeref (ELit n t))
        cx s H (RExpr (ELit n1 t1))
  | SDerefHighOOB : forall cx s H n t t' h,
      h <= 0 ->
      eval_type_bound s t = Some t' ->
      get_high_ptr t' = Some (Num h) ->
      step D F
        cx s H (EDeref (ELit n t))
        cx s H RBounds
  | SDerefLowOOB : forall cx s H n t t' l,
      l > 0 ->
      eval_type_bound s t = Some t' ->
      get_low_ptr t' = Some (Num l) ->
      step D F
        cx s H (EDeref (ELit n t))
        cx s H RBounds
  | SDerefNull : forall cx s H t n,
      n <= 0 -> 
      step D F
        cx s H (EDeref (ELit n (TPtr Checked t)))
        cx s H RNull

  | SAssign : forall cx s H n t tv n1 t1 tv' H',
      Heap.In n H ->
      cast_type_bound s t tv ->
      (forall l h t', tv = TPtr Checked (TArray (Num l) (Num h) t') -> h > 0 /\ l <= 0) -> 
      (forall l h t', tv = TPtr Checked (TNTArray (Num l) (Num h) t') -> h > 0 /\ l <= 0) -> 
      get_root tv tv' ->
      H' = Heap.add n (n1, tv') H ->
      step D F
        cx s H  (EAssign (ELit n t) (ELit n1 t1))
        cx s H' (RExpr (ELit n1 tv'))
  | SAssignHighOOB : forall cx s H n t t' n1 t1 h,
      h <= 0 ->
      eval_type_bound s t = Some t' ->
      get_high_ptr t' = Some (Num h) ->
      step D F
        cx s H (EAssign (ELit n t) (ELit n1 t1))
        cx s H RBounds
  | SAssignLowOOB : forall cx s H n t t' n1 t1 l,
      l > 0 ->
      eval_type_bound s t = Some t' ->
      get_low_ptr t' = Some (Num l) ->
      step D F
        cx s H (EAssign (ELit n t) (ELit n1 t1))
        cx s H RBounds
  | SAssignNull : forall cx s H t tv w n n1 t',
      n1 <= 0 ->
      eval_type_bound s t = Some tv ->
      tv = TPtr Checked w ->
      step D F
        cx s H (EAssign (ELit n1 t) (ELit n t'))
        cx s H RNull

  | SFieldAddrChecked : forall cx s H n t (fi : field) n0 t0 T fs i fi ti,
      n > 0 ->
      t = TPtr Checked (TStruct T) ->
      StructDef.MapsTo T fs D ->
      Fields.MapsTo fi ti fs ->
      List.nth_error (Fields.this fs) i = Some (fi, ti) ->
      n0 = n + Z.of_nat(i) ->
      t0 = TPtr Checked ti ->
      word_type ti ->
      step D F
        cx s H (EFieldAddr (ELit n t) fi)
        cx s H (RExpr (ELit n0 t0))
  | SFieldAddrNull : forall cx s H (fi : field) n T,
      n <= 0 ->
      step D F
        cx s H (EFieldAddr (ELit n (TPtr Checked (TStruct T))) fi)
        cx s H RNull
  | SFieldAddr : forall cx s H n t (fi : field) n0 t0 T fs i fi ti,
      t = TPtr Unchecked (TStruct T) ->
      StructDef.MapsTo T fs D ->
      Fields.MapsTo fi ti fs ->
      List.nth_error (Fields.this fs) i = Some (fi, ti) ->
      n0 = n + Z.of_nat(i) ->
      t0 = TPtr Unchecked ti ->
      word_type ti ->
      step D F
       cx  s H (EFieldAddr (ELit n t) fi)
        cx s H (RExpr (ELit n0 t0))
  | SMalloc : forall cx s H w w' H' n1,
      cast_type_bound s w w' -> malloc_bound w' ->
      allocate D H w' = Some (n1, H') ->
      step D F
        cx s H (EMalloc w)
        cx s H' (RExpr (ELit n1 (TPtr Checked w')))
  | SMallocHighOOB : forall cx s H w t' h,
      h <= 0 ->
      cast_type_bound s w t' ->
      get_high t' = Some (Num h) ->
      step D F
        cx s H (EMalloc w)
        cx s H RBounds
  | SMallocLowOOB : forall cx s H w t' l,
      l <> 0 ->
      cast_type_bound s w t' ->
      get_low t' = Some (Num l) ->
      step D F
        cx s H (EMalloc w)
        cx s H RBounds
  | SLet : forall cx s H x n t e t',
      cast_type_bound s t t' ->
      step D F
        cx s H (ELet x (ELit n t) e)
        (fresh_up cx) (Stack.add cx (n, t') s) H (RExpr (var_subst e x cx))
  | SUnchecked : forall cx s H n t,
      step D F
        cx s H (EUnchecked (ELit n t))
        cx s H (RExpr (ELit n t))
   | SIfTrueNotNTHit : forall cx s H x n t e1 e2 n1 t1, 
           Stack.MapsTo x (n,t) s ->
           step D F cx s H (EDeref (ELit n t)) cx s H (RExpr (ELit n1 t1)) ->
           n1 <> 0 -> ~ (NTHit s x) -> step D F cx s H (EIf x e1 e2) cx s H (RExpr e1)
   | SIfTrueNTHit : forall cx s H x n t e1 e2 n1 t1, 
           Stack.MapsTo x (n,t) s ->
           step D F cx s H (EDeref (ELit n t)) cx s H (RExpr (ELit n1 t1)) ->
           n1 <> 0 -> (NTHit s x) -> step D F cx (add_nt_one s x) H (EIf x e1 e2) cx s H (RExpr e1)
   | SIfFalse : forall cx s H x n t e1 e2 t1, 
           Stack.MapsTo x (n,t) s ->
           step D F cx s H (EDeref (ELit n t)) cx s H (RExpr (ELit 0 t1)) ->
              step D F cx s H (EIf x e1 e2) cx s H (RExpr e2)
   | SIfFail : forall cx s H x n t e1 e2 r,
           Stack.MapsTo x (n,t) s ->
              ~ is_rexpr r 
              -> step D F cx s H (EDeref (ELit n t)) cx s H r -> step D F cx s H (EIf x e1 e2) cx s H r.

Hint Constructors step.

Inductive reduce (D : structdef) (F:fenv) : var -> stack -> heap -> expression -> mode -> var -> stack -> heap -> result -> Prop :=
  | RSExp : forall cx H s e m cx' H' s' e' E,
      step D F cx s H e cx' s' H' (RExpr e') ->
      m = mode_of(E) ->
      reduce D F cx s
        H (in_hole e E)
        m cx' s'
        H' (RExpr (in_hole e' E))
  | RSHaltNull : forall cx H s e m cx' H' s' E,
      step D F cx s H e cx' s' H' RNull ->
      m = mode_of(E) ->
      reduce D F cx s
        H (in_hole e E)
        m cx' s'
        H' RNull
  | RSHaltBounds : forall cx H s e m cx' H' s'  E,
      step D F cx s H e cx' s' H' RBounds ->
      m = mode_of(E) ->
      reduce D F cx s
        H (in_hole e E)
        m cx' s'
        H' RBounds.

Hint Constructors reduce.

Definition reduces (D : structdef) (F:fenv) (cx:var) (s : stack) (H : heap) (e : expression) : Prop :=
  exists (m : mode) (cx':var) (s' : stack) (H' : heap) (r : result), reduce D F cx s H e m cx' s' H' r.

Hint Unfold reduces.


(* Defining function calls. *)


(*
Local Close Scope Z_scope.
Local Open Scope nat_scope.

Definition subst_bound (b:bound) (x y:var) : bound :=
   match b with Num a => Num a
             | Var a b => if a =? x then Var y b else Var a b
   end.

Fixpoint subst_var_type (t:type) (x y:var) : type :=
   match t with TNat => TNat
             | TStruct t' => TStruct t'
             | TPtr m t' => TPtr m (subst_var_type t' x y)
             | TArray a b t' => TArray (subst_bound a x y) (subst_bound b x y) (subst_var_type t' x y)
             | TNTArray a b t' => TArray (subst_bound a x y) (subst_bound b x y) (subst_var_type t' x y)
   end.

Fixpoint subst_var (e:expression) (x y :var) : expression :=
    match e with
        ELit v t => ELit v (subst_var_type t x y)
      | EVar a => if a =? x then EVar y else EVar a
      | EStrlen a => if a =? x then EStrlen y else EStrlen a
      | ELet a e1 e2 => if a =? x then ELet a (subst_var e1 x y) e2 else ELet a (subst_var e1 x y) (subst_var e2 x y)
      | EMalloc t => EMalloc (subst_var_type t x y)
      | ECast t e1 => ECast (subst_var_type t x y) (subst_var e1 x y)
      | EPlus e1 e2 => EPlus (subst_var e1 x y) (subst_var e2 x y)
      | EFieldAddr e f => EFieldAddr (subst_var e x y) f
      | EDeref e1 => EDeref (subst_var e1 x y)
      | EAssign e1 e2 => EAssign (subst_var e1 x y) (subst_var e2 x y)
      | EIf a e1 e2 => if a =? x then EIf y (subst_var e1 x y) (subst_var e2 x y) else EIf a (subst_var e1 x y) (subst_var e2 x y)
      | EUnchecked e => EUnchecked (subst_var e x y)
    end.

Definition gen_var (l:list var) := (list_max l) + 1.

Fixpoint gen_exp (state vl late:list var) (e:expression) :=
    match vl with [] => (late,e)
               | (x::xl) => let new_var := gen_var state in
                             match gen_exp (new_var::state) xl late e
                                with (late',e') => (new_var::late',subst_var e' x new_var)
                             end
    end.

Fixpoint gen_let (xl:list var) (el:list expression) (e:expression) :=
    match xl with [] => Some e
               | (y::yl) => match el with [] => None
                              | (ye::yel) => 
                                 match gen_let yl yel e with None => None
                                     | Some e' => Some (ELet y ye e')
                                 end
                            end
    end.

Definition ECall (F:fenv) (S:list var) (x:var) (el:list expression) := 
      match FEnv.find x F with None => None
                | Some (tl,t,vl,e) => 
                match gen_exp S vl [] e with (late',e') => gen_let late' el e'
                end
       end.



Local Close Scope nat_scope.

Local Open Scope Z_scope.
*)

(** * Static Semantics *)

Require Import Lists.ListSet.

Definition eq_dec_nt (x y : Z * type) : {x = y} + { x <> y}.
repeat decide equality.
Defined. 

Definition scope := set (Z *type)%type. 
Definition empty_scope := empty_set (Z * type).

(*
Definition simp_bound (T:env) (b:bound) : bound :=
   match b with Num n => Num n
              | Var x n => (match Env.find x T with Some (TNat (Some (Num m))) => Num (n + m)
                                                  | Some (TNat (Some (Var y m))) => Var y (n + m)
                                                  | _ => Var x n
                            end)
   end. 

Fixpoint simp_type (T: env) (t:type) : type :=
  match t with TNat None => TNat None
             | TNat (Some b) => TNat (Some (simp_bound T b))
             | TPtr c t' => TPtr c (simp_type T t')
             | TStruct x => TStruct x
             | TArray l h t' => TArray (simp_bound T l) (simp_bound T h) (simp_type T t')
             | TNTArray l h t' => TArray (simp_bound T l) (simp_bound T h) (simp_type T t')
  end.
*)

(* Type check for a literal + simplifying the type. *)
Inductive well_typed_lit (D : structdef) (H : heap) : scope -> Z -> type -> Prop :=
  | TyLitInt : forall s n,
      well_typed_lit D H s n TNat
  | TyLitU : forall s n w,
      well_typed_lit D H s n (TPtr Unchecked w)
  | TyLitZero : forall s t,
      well_typed_lit D H s 0 t
  | TyLitRec : forall s n w,
      set_In (n, (TPtr Checked w)) s ->
      well_typed_lit D H s n (TPtr Checked w)
  | TyLitC : forall sc n w b ts,
      Some (b, ts) = allocate_meta D w ->
      (forall k, b <= k < b + Z.of_nat(List.length ts) ->
                 exists n' t',
                   Some t' = List.nth_error ts (Z.to_nat (k - b)) /\
                   Heap.MapsTo (n + k) (n', t') H /\
                   well_typed_lit D H (set_add eq_dec_nt (n, TPtr Checked w) sc) n' t') ->
      well_typed_lit D H sc n (TPtr Checked w).


Hint Constructors well_typed_lit.

(** It turns out, the induction principle that Coq generates automatically isn't very useful. *)

(** In particular, the TyLitC case does not have an induction hypothesis.
    So, we prove an alternative induction principle which is almost identical but includes
    an induction hypothesis for the TyLitC case.

    TODO: write blog post about this *)

Lemma well_typed_lit_ind' :
  forall (D : structdef) (H : heap) (P : scope -> Z -> type -> Prop),
    (forall (s : scope) (n : Z), P s n TNat) ->
       (forall (s : scope) (n : Z) (w : type), P s n (TPtr Unchecked w)) ->
       (forall (s : scope) (t : type), P s 0 t) ->
       (forall (s : scope) (n : Z) (w : type), set_In (n, (TPtr Checked w)) s -> P s n (TPtr Checked w)) ->
       (forall (s : scope) (n : Z) (w : type) (ts : list type) (b : Z),
        Some (b, ts) = allocate_meta D w ->
        (forall k : Z,
         b <= k < b + Z.of_nat (length ts) ->
         exists (n' : Z) (t' : type),
           Some t' = nth_error ts (Z.to_nat (k - b)) /\
           Heap.MapsTo (n + k) (n', t') H /\
           well_typed_lit D H (set_add eq_dec_nt (n, TPtr Checked w) s) n' t' /\
           P (set_add eq_dec_nt (n, TPtr Checked w) s) n' t') ->
        P s n (TPtr Checked w)) -> forall (s : scope) (n : Z) (w : type), well_typed_lit D H s n w -> P s n w.
Proof.
  intros D H P.
  intros HTyLitInt
         HTyLitU
         HTyLitZero
         HTyLitRec
         HTyLitC.
  refine (fix F s n t Hwtl :=
            match Hwtl with
            | TyLitInt _ _ s' n' => HTyLitInt s' n'
            | TyLitU _ _ s' n' w' => HTyLitU s' n' w'
            | TyLitZero _ _ s' t' => HTyLitZero s' t'
            | TyLitRec _ _ s' n' w'  Hscope => HTyLitRec s' n' w' Hscope
            | TyLitC _ _ s' n' w' b ts Hts IH =>
              HTyLitC s' n' w' ts b Hts (fun k Hk =>
                                         match IH k Hk with
                                         | ex_intro _ n' Htmp =>
                                           match Htmp with
                                           | ex_intro _ t' Hn't' =>
                                             match Hn't' with
                                             | conj Ht' Hrest1 =>
                                               match Hrest1 with
                                               | conj Hheap Hwt =>
                                                 ex_intro _ n' (ex_intro _ t' 
                     (conj Ht' (conj Hheap (conj Hwt (F (set_add eq_dec_nt (_ , TPtr Checked w') s') n' t' Hwt)))))
                                               end
                                             end
                                           end
                                         end)
            end).
Qed.

Inductive well_type_lit_stack (D : structdef) (S:stack) (H : heap) :  scope -> Z -> type -> Prop :=
      | WTStack : forall sc n t t', cast_type_bound S t t' 
             -> well_typed_lit D H sc n t' -> well_type_lit_stack D S H sc n t.

(** Expression Typing *)
(*
Definition add_bound (b1 b2: option bound) : option bound :=
   match b1 with None => None
               | Some (Num n) => (match b2 with None => None
                                              | Some (Num m) => Some (Num (n + m))
                                              | Some (Var x m) => Some (Var x (n + m))
                                  end)
               | Some (Var x n) => (match b2 with None => None
                                                | Some (Num m) => Some (Var x (n + m))
                                                | Some (Var y m) => None
                                     end)
    end.
*)

Definition is_ptr (t : type) : Prop :=
    match t with TPtr m x => True 
              | _ => False
    end.

Definition is_nt_ptr (t : type) : Prop :=
    match t with TPtr m (TNTArray l h t') => True 
              | _ => False
    end.

Inductive ty_syn_eq : type -> type -> Prop :=
    | ty_syn_eq_nat : ty_syn_eq TNat TNat
    | ty_syn_eq_ptr: forall m x y, ty_syn_eq x y -> ty_syn_eq (TPtr m x) (TPtr m y)
    | ty_syn_eq_struct : forall t, ty_syn_eq (TStruct t) (TStruct t)
    | ty_syn_eq_array : forall x y u v t t', ty_syn_eq t t' -> ty_syn_eq (TArray x y t) (TArray u v t')
    | ty_syn_eq_ntarray : forall x y u v t t', ty_syn_eq t t' -> ty_syn_eq (TNTArray x y t) (TNTArray u v t').

Inductive type_eq (S : stack) : type -> type -> Prop := 
     | type_eq_refl: forall t, type_eq S t t
     | type_eq_left: forall t1 t2, simple_type t1 -> cast_type_bound S t2 t1 -> type_eq S t1 t2
     | type_eq_right: forall t1 t2, simple_type t2 -> cast_type_bound S t1 t2 -> type_eq S t1 t2.

Inductive meet_type (D : structdef) (S : stack) : type -> type -> type -> Prop :=
   meet_type_front_1 : forall a b, subtype D a b -> meet_type D S a b a
  | meet_type_front_2 : forall a a' b b', cast_type_bound S a a' ->
               cast_type_bound S b b' -> subtype D a' b' -> meet_type D S a b a
  | meet_type_end_1 : forall a b, subtype D b a -> meet_type D S a b b
  | meet_type_end_2 : forall a a' b b', cast_type_bound S a a' ->
               cast_type_bound S b b' -> subtype D b' a' -> meet_type D S a b b.

Definition is_ok_up (s:stack) (e:expression) : Prop :=
   match e with ELit n t => (exists t', cast_type_bound s t t')
              | EVar x => Stack.In x s
              | _ => False
   end.
                

Inductive up_arg_stack : stack -> var -> expression -> stack -> Prop :=
    up_arg_num : forall s x n t t', cast_type_bound s t t'
                        -> up_arg_stack s x (ELit n t) (Stack.add x (n,t') s)
  | up_arg_var : forall s x y n t, Stack.MapsTo x (n,t) s -> 
                            up_arg_stack s y (EVar x) (Stack.add y (n,t) s)
  | up_arg_other : forall s x e, ~ is_ok_up s e -> up_arg_stack s x e s.

Inductive well_typed_arg (D: structdef) (S:stack) (H:heap) (env:env): 
                 expression -> type -> Prop :=
     | ArgLit : forall n t t' t'',
      well_type_bound_in env t ->
      well_type_lit_stack D S H empty_scope n t ->
      type_eq S t t'' -> subtype D t' t'' ->
      well_typed_arg D S H env (ELit n t) t'
     | ArgVar : forall x t t' t'',
      well_type_bound_in env t ->
      Env.MapsTo x t env ->
      type_eq S t t'' -> subtype D t' t'' ->
      well_typed_arg D S H env (EVar x) t'.

Inductive well_typed_args (D: structdef) (H:heap) : 
              stack -> env -> list expression -> list (var * type) -> Prop :=
     | args_empty : forall S env, well_typed_args D H S env [] []
     | args_many : forall S S' env e es v t vl, 
                 well_type_bound_in env t ->
                   well_typed_arg D S H env e t -> 
                    up_arg_stack S v e S' ->
                    well_typed_args D H S' (Env.add v t env) es vl
                        -> well_typed_args D H S env (e::es) ((v,t)::vl).

Inductive well_typed { D : structdef } {F : fenv} {S : stack} { H : heap }
                        : env -> mode -> expression -> type -> Prop :=
  | TyLit : forall env m n t,
      well_type_bound_in env t ->
      well_type_lit_stack D S H empty_scope n t ->
      well_typed env m (ELit n t) t
  | TyVar : forall env m x t,
      well_type_bound_in env t ->
      Env.MapsTo x t env ->
      well_typed env m (EVar x) t

  (*  t must be a simple type. *)
  | TyCall : forall env m es x tvl t e t' t'', 
        FEnv.MapsTo x (tvl,t,e) F ->
      well_typed_args D H S env es tvl -> 
         type_eq S t' t'' -> subtype D t t'' ->
           well_typed env m (ECall x es) t'

  | TyStrlen : forall env m x h l t, 
      well_type_bound_in env (TPtr m (TNTArray h l t)) ->
      Env.MapsTo x (TPtr m (TNTArray h l t)) env ->
      well_typed env m (EStrlen x) TNat
  | TyLet : forall env m x e1 t1 e2 t,
      well_typed env m e1 t1 ->
      well_typed (Env.add x t1 env) m e2 t ->
      well_typed env m (ELet x e1 e2) t
  | TyPlus : forall env m e1 e2,
      well_typed env m e1 (TNat) ->
      well_typed env m e2 (TNat) ->
      well_typed env m (EPlus e1 e2) TNat
  | TyFieldAddr : forall env m e m' T fs i fi ti,
      well_typed env m e (TPtr m' (TStruct T)) ->
      StructDef.MapsTo T fs D ->
      Fields.MapsTo fi ti fs ->
      List.nth_error (Fields.this fs) i = Some (fi, ti) ->
      well_typed env m (EFieldAddr e fi) (TPtr m' ti)
  | TyMalloc : forall env m w,
      well_type_bound_in env w ->
      well_typed env m (EMalloc w) (TPtr Checked w)
  | TyUnchecked : forall env m e t,
      well_typed env Unchecked e t ->
      well_typed env m (EUnchecked e) t
  | TyCast1 : forall env m t e t',
      well_type_bound_in env t ->
      (m = Checked -> forall w, t <> TPtr Checked w) ->
      well_typed env m e t' ->
      well_typed env m (ECast t e) t
  | TyCast2 : forall env m t e t',
      well_type_bound_in env t ->
      well_typed env m e t' ->
      subtype D t' (TPtr Checked t) ->
      well_typed env m (ECast (TPtr Checked t) e) (TPtr Checked t)

  | TyDynCast1 : forall env m e x y u v t t',
      type_eq S t t' ->
      well_type_bound_in env (TPtr Checked (TArray x y t)) ->
      well_typed env m e (TPtr Checked (TArray u v t')) ->
      well_typed env m (EDynCast (TPtr Checked (TArray x y t)) e) (TPtr Checked (TArray x y t))
  | TyDynCast2 : forall env m e x y t t',
      type_eq S t t' -> ~ is_array_ptr (TPtr Checked t') ->
      well_type_bound_in env (TPtr Checked (TArray x y t)) ->
      well_typed env m e (TPtr Checked t') ->
      well_typed env m (EDynCast (TPtr Checked (TArray x y t)) e) (TPtr Checked (TArray (Num 0) (Num 1) t))
  | TyDynCast3 : forall env m e x y u v t t',
      type_eq S t t' ->
      well_type_bound_in env (TPtr Checked (TNTArray x y t)) ->
      well_typed env m e (TPtr Checked (TNTArray u v t')) ->
      well_typed env m (EDynCast (TPtr Checked (TNTArray x y t)) e) (TPtr Checked (TNTArray x y t))
  | TyDeref : forall env m e m' t l h t' t'',
      well_typed env m e t ->
      subtype D t (TPtr m' t'') ->
      ((word_type t'' /\ t'' = t') \/ (t'' = TArray l h t' /\ word_type t' /\ type_wf D t')
       \/ (t'' = TNTArray l h t' /\ word_type t' /\ type_wf D t')) ->
      (m' = Unchecked -> m = Unchecked) ->
      well_typed env m (EDeref e) t'
  | TyIndex1 : forall env m e1 m' l h t e2 t',
      word_type t' -> type_wf D t' ->
      well_typed env m e1 t ->
      t= (TPtr m' (TArray l h t')) ->
      well_typed env m e2 (TNat) ->
      (m' = Unchecked -> m = Unchecked) ->
      well_typed env m (EDeref (EPlus e1 e2)) t'
  | TyIndex2 : forall env m e1 m' l h t e2 t',
      word_type t' -> type_wf D t' ->
      well_typed env m e1 t ->
      t= (TPtr m' (TNTArray l h t')) ->
      well_typed env m e2 (TNat) ->
      (m' = Unchecked -> m = Unchecked) ->
      well_typed env m (EDeref (EPlus e1 e2)) t'
  | TyAssign1 : forall env m e1 e2 m' t t1 t2,
      subtype D t1 t2 ->
      word_type t -> type_eq S t t2 ->
      well_typed env m e1 (TPtr m' t) ->
      well_typed env m e2 t1 ->
      (m' = Unchecked -> m = Unchecked) ->
      well_typed env m (EAssign e1 e2) t2
  | TyAssign2 : forall env m e1 e2 m' l h t t' t'',
      word_type t -> type_wf D t -> type_eq S t t'' ->
      subtype D t' t'' ->
      well_typed env m e1 (TPtr m' (TArray l h t)) ->
      well_typed env m e2 t' ->
      (m' = Unchecked -> m = Unchecked) ->
      well_typed env m (EAssign e1 e2) t''
  | TyAssign3 : forall env m e1 e2 m' l h t t' t'',
      word_type t -> type_wf D t -> type_eq S t t'' ->
      subtype D t' t'' ->
      well_typed env m e1 (TPtr m' (TNTArray l h t)) ->
      well_typed env m e2 t' ->
      (m' = Unchecked -> m = Unchecked) ->
      well_typed env m (EAssign e1 e2) t''
  | TyIndexAssign1 : forall env m e1 e2 e3 m' l h t t' t'',
      word_type t' -> type_wf D t' ->
      type_eq S t t'' -> subtype D t' t'' ->
      well_typed env m e1 (TPtr m' (TArray l h t)) ->
      well_typed env m e2 (TNat) ->
      well_typed env m e3 t' ->
      (m' = Unchecked -> m = Unchecked) ->
      well_typed env m (EAssign (EPlus e1 e2) e3) t''
  | TyIndexAssign2 : forall env m e1 e2 e3 m' l h t t' t'',
      word_type t' -> type_wf D t' ->
      type_eq S t t'' -> subtype D t' t'' ->
      well_typed env m e1 (TPtr m' (TNTArray l h t)) ->
      well_typed env m e2 (TNat) ->
      well_typed env m e3 t' ->
      (m' = Unchecked -> m = Unchecked) ->
      well_typed env m (EAssign (EPlus e1 e2) e3) t''
  | TyIf : forall env m m' x t t1 e1 e2 t2 t3 t4,
      Env.MapsTo x t env ->
      subtype D t (TPtr m' t1) ->
      (exists l h t', (word_type t1 /\ t1 = t') \/ (t1 = TArray l h t' /\ word_type t' /\ type_wf D t')
       \/ (t1 = TNTArray l h t' /\ word_type t' /\ type_wf D t')) ->
      well_typed env m e1 t2 ->
      well_typed env m e2 t3 ->
      meet_type D S t2 t3 t4 -> 
      (m' = Unchecked -> m = Unchecked) ->
      well_typed env m (EIf x e1 e2) t4.


Lemma subtype_well_type : forall D H env t t' n,
@well_typed_lit D H env n t ->
subtype D t t' ->
@well_typed_lit D H env n t'.
Proof.
(*
  intros. induction H0. 
  - inv H1. eauto.
  - assert (exists t, t' = (TPtr Unchecked t)) by (inv H1; eauto).
    destruct H0. rewrite H0. eauto.
  - eauto.
  - specialize (subtype_trans D t t' Checked w H2 H1) as eq1.

    assert (exists t0, t' = (TPtr Checked t0)) by (inv H1; eauto).
    destruct H3. rewrite H3 in *.
    eapply TyLitRec; eauto.
  - assert (exists t0, t' = (TPtr Checked t0)) by (inv H1; eauto).
    unfold allocate_meta in H0.
    induction w.
    * inv H1.
      ++ eapply TyLitC; eauto. 
      ++ inv H7. inv H9. eapply TyLitC; eauto.
      unfold allocate_meta. eauto.
      intros.
      assert (l - h0 <= 0 \/ l - h0 = 1) by lia.
      destruct H5.
      assert ((Zreplicate (l - h0) TNat) = []).
      unfold Zreplicate. 
      destruct (l - h0). easy.
      specialize (Pos2Z.is_pos p) as eq1. contradiction. easy.
      rewrite H8 in H1. simpl in H1. lia.
      rewrite H5 in *.
      unfold Zreplicate in *. simpl in *.
      assert (k = h0) by lia. subst. simpl.
      inv H0. simpl in *.
      destruct (H2 0). lia.
      destruct H0. 
      destruct H0. destruct H8.
      assert (l = 1) by lia.
      assert (h0 = 0) by lia.
      subst.
      exists x. exists x0.
      split. easy. split. easy.
      inv H0. apply TyLitInt.
    * inv H1. 
      ++ eapply TyLitC; eauto.
      ++ inv H7. inv H9. eapply TyLitC; eauto. 
      unfold allocate_meta. eauto.
      intros.
      assert (l - h0 <= 0 \/ l - h0 = 1) by lia.
      destruct H5.
      assert ((Zreplicate (l - h0) (TPtr m w)) = []).
      unfold Zreplicate. 
      destruct (l - h0). easy.
      specialize (Pos2Z.is_pos p) as eq1. contradiction. easy.
      rewrite H8 in H1. simpl in H1. lia.
      rewrite H5 in *.
      unfold Zreplicate in *. simpl in *.
      assert (k = h0) by lia. subst. simpl.
      inv H0. simpl in *.
      destruct (H2 0). lia.
      destruct H0. 
      destruct H0. destruct H8.
      assert (l = 1) by lia.
      assert (h0 = 0) by lia.
      subst.
      exists x. exists x0.
      split. easy. split. easy.
      inv H0.
      destruct (Z.eq_dec x n).
      subst.
      destruct m.
      eapply TyLitRec.
      apply set_add_intro2. reflexivity.
      apply SubTyOne.
 inv H9. apply TyLitU.
      apply TyLitZero.
      eapply (TyLitRec).

  | TyLitRec : forall s n w t,
      set_In (n, t) s ->
      subtype D t (TPtr Checked w) ->
      well_typed_lit D H s n (TPtr Checked w)


    * admit. (* inv H1. eapply TyLitC; eauto.
     
      eapply TyLitC; eauto.
      unfold allocate_meta; eauto.
      simpl in H0. destruct (StructDef.find (elt:=fields) s D) eqn:Hf.
      + inv H0. rewrite map_length in H2.
        assert (StructDef.MapsTo s f D) by (eapply find_implies_mapsto; eauto).
        assert (f = fs) by (eapply StructDefFacts.MapsTo_fun; eauto). 
        rewrite H1 in *.
        assert (((length (Fields.elements (elt:=type) fs)) >= 1)%nat) by (eapply fields_implies_length; eauto).
        intros. simpl in H5.
        destruct (H2 k). zify. lia.
        exists x. exists TNat.
        assert (k = 0) by (destruct k; inv H5; eauto; exfalso; zify; lia).
        rewrite H9 in *. simpl. split; eauto.
        destruct H7. destruct H7.
        simpl in H7. 
        rewrite <- (element_implies_element s fs D TNat H0 H8) in H7.
        inv H7. destruct H10.
        split. assumption. eauto.
      + inv H0. *)
    * clear IHw. inv H0.
      admit.
    * 
      inv H1. clear H3. 
        + eapply TyLitC; eauto.
        + clear H3.
          eapply TyLitC.


          unfold allocate_meta; eauto.
          intros. 
          assert (Hmin : (h' - l') > 0).
          {
                destruct (h' - l'); zify; (try omega); simpl in *; inv H0;
                exfalso; rewrite Z.add_0_r in *; omega.
          }
          assert (Hpos : exists p, h' - l' = Z.pos p).
          {
           destruct (h' - l'); zify; (try omega).
           exists p; eauto.
          }
          assert ((z0 - z) >= (h' - l')) by omega.
          assert ((length (Zreplicate (z0 - z) w) >= (length (Zreplicate (h' - l') w)))%nat).
          {
            destruct (z0 - z).
            * simpl. destruct (h' - l'); simpl; eauto. exfalso. zify; omega.
            * simpl. rewrite replicate_length. destruct (h' - l');
              simpl; eauto; (try omega). rewrite replicate_length; zify; omega.
            * exfalso; zify; omega.
          }
          destruct (H2 k).
          split. 
            ** omega.
            ** (* relies on the fact that h' - l' must be greater than 0*)
              destruct Hpos as [p Hpos].
              assert (h' > l') by omega.
              assert (psuc : exists n, Pos.to_nat p = S n) by (eapply pos_succ; eauto).
              (*very convoluted*)
              destruct (z0 - z)eqn:Hz.
              ++ exfalso; omega.
              ++ rewrite Hpos in *. simpl in *.
                 rewrite replicate_length in *.
                 assert (Hp : Z.of_nat (Pos.to_nat p) = Z.pos p).
                 {
                  destruct psuc as [n0 psuc]. rewrite psuc.
                  zify; omega.
                 } clear psuc.
                 assert (psuc: exists n, Pos.to_nat p0 = S n) by eapply pos_succ; eauto.
                 assert (Hp0 : Z.of_nat (Pos.to_nat p0) = Z.pos p0).
                 {
                  destruct psuc as [n0 psuc]. rewrite psuc.
                  zify; omega.
                 }
                 rewrite Hp0. rewrite <- Hz. 
                 assert (z + (z0 - z) = z0) by omega.
                 rewrite H5. rewrite Hp in H0.
                 rewrite <- Hpos in H0.
                 assert (l' + (h' - l') = h') by omega.
                 rewrite H6 in H0. omega.
              ++ exfalso; zify; omega.
          ** exists x. exists w.
             split.
             ++ destruct Hpos as [p Hpos]. rewrite Hpos.
                simpl. 
                assert (exists n, Pos.to_nat p = S n) by (eapply pos_succ; eauto).
                destruct H5. rewrite H5. simpl.
                destruct (k - l')eqn:Hk; simpl; eauto.
               -- Search nth_error.
             ++ destruct H4.
                destruct H4 as [? [? ?]].
                assert (x0 = w) by admit. 
                rewrite H7 in *. 
                split; eauto. 
                assert (well_typed_lit D H
               (set_add eq_dec_nt (n, TPtr Checked (TArray l' h' w))
               (set_add eq_dec_nt
               (n, TPtr Checked (TArray z z0 w))
                s)) x w) by (eapply scope_weakening; eauto).
                assert (set_equal (set_add eq_dec_nt (n, TPtr Checked (TArray l' h' w))
          (set_add eq_dec_nt (n, TPtr Checked (TArray z z0 w)) s))
              (set_add eq_dec_nt (n, TPtr Checked (TArray z z0 w))
               (set_add eq_dec_nt
               (n, TPtr Checked (TArray l' h' w))
                s))).
                { eapply set_equal_add_add; eauto. instantiate (1:=s). unfold set_equal.
                  intros; split; intros; assumption. } 
                assert (well_typed_lit D H
               (set_add eq_dec_nt (n, TPtr Checked (TArray z z0 w))
               (set_add eq_dec_nt
               (n, TPtr Checked (TArray l' h' w))
                s)) x w). 
               { eapply scope_replacement; eauto. } *)
              
          
Admitted.

Inductive gen_env (D : structdef) (S : stack) : list (var * type) -> env -> Prop :=
   gen_env_empty : gen_env D S [] empty_env
  | gen_env_many_1 : forall v t tl env, 
         gen_env D S tl env -> gen_env D S ((v,t)::tl) (Env.add v t env)
  | gen_env_many_2 : forall v t t' t'' tl env,
         subtype D t' t -> type_eq S t' t'' -> 
         gen_env D S tl env -> gen_env D S ((v,t)::tl) (Env.add v t'' env).

Inductive dis_vars : list var -> var -> list var -> Prop :=
    dis_right : forall l x, ~ In x l -> dis_vars l x []
  | dis_mid : forall l1 x v l2, ~ In x (l1 ++ (v::l2)) ->
                dis_vars (l1 ++ [x]) v l2 -> dis_vars l1 x (v::l2)
  | dis_left : forall x v l, ~ In x (v::l) -> dis_vars [x] v l -> dis_vars [] x (v::l).

Inductive dis_all : list var -> Prop :=
     dis_all_empty : dis_all []
   | dis_all_many : forall x l, dis_vars [] x l -> dis_all (x::l).

Definition get_vars (l:list (var*type)) := map (fun x => match x with (a,b) => a end) l.

Definition fun_typed (D : structdef) (F:fenv) (S : stack) (H : heap) : Prop :=
  forall x tvl t e,
    FEnv.MapsTo x (tvl,t,e) F ->
    word_type t /\ type_wf D t /\ simple_type t /\
     (forall x t', In (x,t') tvl -> word_type t' /\ type_wf D t') /\ dis_all (get_vars tvl) /\
   (exists m env, gen_env D S tvl env /\ @well_typed D F S H env m e t).
            

Inductive ty_ssa : list var -> expression -> list var -> Prop :=
   | ty_ssa_lit : forall S n t, ty_ssa S (ELit n t) S
   | ty_ssa_var : forall S x, ty_ssa S (EVar x) S
   | ty_ssa_strlen : forall S x, ty_ssa S (EStrlen x) S
   | ty_ssa_let : forall S S' S'' x e1 e2, ~ In x S -> ty_ssa (x::S) e1 S'
                             -> ty_ssa S' e2 S'' -> ty_ssa S (ELet x e1 e2) S''
   | ty_ssa_if : forall S S' S'' x e1 e2, ty_ssa S e1 S' -> ty_ssa S' e2 S'' -> ty_ssa S (EIf x e1 e2) S''
   | ty_ssa_malloc : forall S w, ty_ssa S (EMalloc w) S
   | ty_ssa_cast : forall S S' t e, ty_ssa S e S' -> ty_ssa S (ECast t e) S'
   | ty_ssa_plus : forall S S' S'' e1 e2, ty_ssa S e1 S' -> ty_ssa S' e2 S'' -> ty_ssa S (EPlus e1 e2) S''
   | ty_ssa_fieldaddr : forall S S' e f, ty_ssa S e S' -> ty_ssa S (EFieldAddr e f) S'
   | ty_ssa_deref : forall S S' e, ty_ssa S e S' -> ty_ssa S (EDeref e) S'
   | ty_ssa_assign : forall S S' S'' e1 e2, ty_ssa S e1 S' -> ty_ssa S' e2 S'' -> ty_ssa S (EAssign e1 e2) S''
   | ty_ssa_unchecked : forall S S' e, ty_ssa S e S' -> ty_ssa S (EUnchecked e) S'.

Definition list_subset (l l': list var) := forall x, In x l -> In x l'.

Lemma ty_ssa_grow : forall S e S' , ty_ssa S e S' -> list_subset S S'.
Proof.
 intros. unfold list_subset. intros.
 induction H;eauto.
 apply IHty_ssa2.
 apply IHty_ssa1.
 apply in_cons. assumption.
Qed.

Hint Constructors well_typed.

Hint Constructors ty_ssa.


Lemma ptr_subtype_equiv : forall D m w t,
subtype D w (TPtr m t) ->
exists t', w = (TPtr m t').
Proof.
  intros. remember (TPtr m t) as p. generalize dependent t. induction H.
  - intros. exists t0. rewrite Heqp. reflexivity.
  - intros. inv Heqp. exists t. easy.
  - intros. inv Heqp. exists (TArray l h t0). easy.
  - intros. inv Heqp. exists (TNTArray l h t0). easy.
  - intros. inv Heqp. exists (TArray l h t). easy.
  - intros. inv Heqp. exists (TNTArray l h t). easy.
  - intros. inv Heqp. exists (TNTArray l h t). easy.
  - intros. exists (TStruct T).
    assert (m0 = m). {
      inv Heqp. reflexivity. 
    }
    rewrite H1. reflexivity.
  - intros. inv Heqp. exists (TStruct T).
    reflexivity.
Qed.

(* this might be an issue if we want to make checked pointers
a subtype of unchecked pointers. This will need to
be changed to generalize m*)
Lemma ptr_subtype_equiv' : forall D m w t,
subtype D (TPtr m t) w ->
exists t', w = (TPtr m t').
Proof.
 intros. remember (TPtr m t) as p. generalize dependent t. induction H.
  - intros. exists t0. rewrite Heqp. reflexivity.
  - intros. inv Heqp. exists (TArray l h t0). easy.
  - intros. inv Heqp. exists t. easy.
  - intros. inv Heqp. exists t. easy.
  - intros. exists (TArray l' h' t).
    assert (m0 = m). {
      inv Heqp. reflexivity. 
    }
    rewrite H1. reflexivity.
  - intros. inv Heqp. exists (TArray l' h' t). easy.
  - intros. exists (TNTArray l' h' t).
    assert (m0 = m). {
      inv Heqp. reflexivity. 
    }
    rewrite H1. reflexivity.
  - intros. exists TNat.
    assert (m0 = m). {
      inv Heqp. reflexivity. 
    }
    rewrite H1. reflexivity.
  - intros. exists (TArray l h TNat).
    assert (m0 = m). {
      inv Heqp. reflexivity. 
    }
    rewrite H3. reflexivity.
Qed.

Lemma nat_subtype : forall D t,
subtype D TNat t ->
t = TNat.
Proof.
  intros. remember TNat as t'. induction H; eauto.
  - exfalso. inv Heqt'.
  - exfalso. inv Heqt'.
  - exfalso. inv Heqt'.
  - exfalso. inv Heqt'.
  - exfalso. inv Heqt'.
  - exfalso. inv Heqt'.
  - exfalso. inv Heqt'.
  - exfalso. inv Heqt'.
Qed.

(** ** Metatheory *)

(** *** Automation *)

(* TODO: write a function decompose : expr -> (context * expr) *)


Ltac clean :=
  subst;
  repeat (match goal with
          | [ P : ?T, PQ : ?T -> _ |- _ ] => specialize (PQ P); clear P
          | [ H : ?T = ?T -> _ |- _ ] => specialize (H eq_refl)
          end).

Definition heap_consistent { D : structdef } (H' : heap) (H : heap) : Prop :=
  forall n t,
    @well_typed_lit D H empty_scope n t->
    @well_typed_lit D H' empty_scope n t.

Hint Unfold heap_consistent.


(** *** Lemmas *)

(* ... for Progress *)

Create HintDb Progress.

Lemma step_implies_reduces : forall D F H s e H' s' r,
    @step D F s H e s' H' r ->
    reduces D F s H e.
Proof.
  intros.
  assert (e = in_hole e CHole); try reflexivity.
  rewrite H1.
  destruct r; eauto 20.
Qed.

Hint Resolve step_implies_reduces : Progress.

Lemma reduces_congruence : forall D F H s e0 e,
    (exists E, in_hole e0 E = e) ->
    reduces D F s H e0 ->
    reduces D F s H e.
Proof.
  intros.
  destruct H0 as [ E Hhole ].
  destruct H1 as [ H' [ m' [ s' [r  HRed ]] ] ].
  inv HRed as [ ? e0' ? ? e0'' E' | ? e0' ? ? E' | ? e0' ? ? E' ]; rewrite compose_correct; eauto 20.
Qed.

Hint Resolve reduces_congruence : Progress.

Lemma unchecked_congruence : forall e0 e,
    (exists e1 E, e0 = in_hole e1 E /\ mode_of(E) = Unchecked) ->
    (exists E, in_hole e0 E = e) ->
    exists e' E, e = in_hole e' E /\ mode_of(E) = Unchecked.
Proof.
  intros.
  destruct H as [ e1 [ E1 [ He0 HE1U ] ] ].
  destruct H0 as [ E He ].
  exists e1.
  exists (compose E E1).
  split.
  - subst. rewrite compose_correct. reflexivity.
  - apply compose_unchecked. assumption.
Qed.

Hint Resolve unchecked_congruence : Progress.


Require Import Omega.

Open Scope Z.
Lemma wf_implies_allocate_meta :
  forall (D : structdef) (w : type),
    (forall l h t, w = TArray (Num l) (Num h) t -> l = 0 /\ h > 0) ->
    (forall l h t, w = TArray (Num l) (Num h) t -> l = 0 /\ h > 0) ->
    simple_type w ->
    type_wf D w -> exists b allocs, allocate_meta D w = Some (b, allocs).
Proof.
  intros D w HL1 HL2 HS HT.
  destruct w; simpl in *; eauto.
  - inv HT. destruct H0.
    apply StructDef.find_1 in H.
    rewrite -> H.
    eauto.
  - inv HS. eauto.
  - inv HS. eauto.
Qed.

Lemma wf_implies_allocate :
  forall (D : structdef) (w : type) (H : heap),
    (forall l h t, w = TArray (Num l) (Num h) t -> l = 0 /\ h > 0) ->
    (forall l h t, w = TNTArray (Num l) (Num h) t -> l = 0 /\ h > 0) ->
    simple_type w ->
    type_wf D w -> exists n H', allocate D H w = Some (n, H').
Proof.
  intros D w H HL1 HL2 HS HT.
  eapply wf_implies_allocate_meta in HT; eauto.
  destruct HT as [l [ts HT]]. 
  unfold allocate. unfold allocate_meta in *.
  rewrite HT.
  edestruct (fold_left
               (fun (acc : Z * heap) (t : type) =>
                  let (sizeAcc, heapAcc) := acc in
                  (sizeAcc + 1, Heap.add (sizeAcc + 1) (0, t) heapAcc)) ts
               ((Z.of_nat (Heap.cardinal H)), H)) as (z, h).

  destruct w eqn:Hw; inv HT; simpl in *; eauto.

  - destruct (StructDef.find s D) eqn:HFind; inv H1; eauto.
  - inv HS.
    edestruct HL1; eauto. 
    destruct l. subst; eauto.
    rewrite H0 in H1.
    assert (0 < Z.pos p).
    easy. inversion H1.
    assert (Z.neg p < 0).
    easy. rewrite H0 in H1. inversion H1.
  - inv HS.
    edestruct HL2; eauto. 
    destruct l. subst; eauto.
    rewrite H0 in H1.
    assert (0 < Z.pos p).
    easy. inversion H1.
    assert (Z.neg p < 0).
    easy. rewrite H0 in H1. inversion H1.
Qed.

Lemma not_in_empty : forall x, Env.In x empty_env -> False.
Proof.
 intros.
  unfold empty_env in H.
 specialize (@Env.empty_1 type) as H1.
 unfold Env.In,Env.Raw.PX.In in H.
 destruct H.
 unfold Env.Empty,Env.Raw.Empty in H1.
 inv H.
Qed.

Lemma simple_type_well_bound : forall (env: env) (w:type),
                simple_type w -> well_type_bound_in env w.
Proof.
   intros. induction w.
   apply well_type_bound_in_nat.
   apply well_type_bound_in_ptr.
   apply IHw. inv H. assumption.
   apply well_type_bound_in_struct.
   inv H.
   apply well_type_bound_in_array.
   apply well_bound_in_num.
   apply well_bound_in_num.
   apply IHw. assumption.
   inv H.
   apply well_type_bound_in_ntarray.
   apply well_bound_in_num.
   apply well_bound_in_num.
   apply IHw. assumption.
Qed.

Lemma well_bound_means_no_var :
     forall b, well_bound_in empty_env b -> (exists n, b = (Num n)).
Proof.
 intros. remember empty_env as env.
 induction H. eauto.
 subst. 
 unfold empty_env in H.
 specialize (@Env.empty_1 type) as H1.
 unfold Env.In,Env.Raw.PX.In in H.
 destruct H.
 unfold Env.Empty,Env.Raw.Empty in H1.
 inv H.
Qed.

Lemma empty_means_cast_bound_same :
   forall s b, well_bound_in empty_env b -> cast_bound s b = Some b.
Proof.
 intros. apply well_bound_means_no_var in H.
 unfold cast_bound. destruct b. reflexivity.
 destruct H. inv H.
Qed.

Lemma empty_means_cast_type_bound_same :
   forall s t, well_type_bound_in empty_env t -> cast_type_bound s t t.
Proof.
 intros. 
 remember empty_env as env.
 induction H.
 apply cast_type_bound_nat.
 apply cast_type_bound_ptr.
 apply IHwell_type_bound_in.
 assumption.
 apply cast_type_bound_struct.
 apply cast_type_bound_array.
 subst.
 apply (empty_means_cast_bound_same s) in H.
 assumption.
 subst.
 apply (empty_means_cast_bound_same s) in H0.
 assumption.
 apply IHwell_type_bound_in.
 assumption.
 apply cast_type_bound_ntarray.
 subst.
 apply (empty_means_cast_bound_same s) in H.
 assumption.
 subst.
 apply (empty_means_cast_bound_same s) in H0.
 assumption.
 apply IHwell_type_bound_in.
 assumption.
Qed.

Lemma well_typed_means_simple : forall (w : type), well_type_bound_in empty_env w -> simple_type w.
Proof.
 intros. remember empty_env as env0.
 induction H.
 apply SPTNat.
 apply SPTPtr.
 apply IHwell_type_bound_in.
 subst. easy.
 constructor.
 subst.
 inv H0.
 inv H.
 constructor.
 apply IHwell_type_bound_in.
 easy.
 inv H0. inv H.
 inv H2. inv H0.
 inv H0. inv H.
 constructor.
 apply IHwell_type_bound_in.
 easy.
 inv H0. inv H.
 inv H2. inv H0.
 Qed.

Definition unchecked (m : mode) (e : expression) : Prop :=
  m = Unchecked \/ exists e' E, e = in_hole e' E /\ mode_of(E) = Unchecked.

Hint Unfold unchecked.

Ltac solve_empty_scope :=
  match goal with
  | [ H : set_In _ empty_scope |- _ ] => inversion H
  | _ => idtac "No empty scope found"
  end.


Require Import Coq.FSets.FMapList.
Require Import Coq.FSets.FMapFacts.

Module EnvFacts := WFacts_fun Env.E Env.
Module FieldFacts := WFacts_fun Fields.E Fields.
Module StructDefFacts := WFacts_fun StructDef.E StructDef.
Module HeapFacts := WFacts_fun Heap.E Heap.

(* This really should be part of the library, or at least easily provable... *)
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

(* This should be part of the stupid map library. *)
(* Changed to Z to push final proof DP*)
Lemma heap_add_in_cardinal : forall n v H,
  Heap.In n H -> 
  Heap.cardinal (elt:=Z * type) (Heap.add n v H) =
  Heap.cardinal (elt:=Z * type) H.
Proof.
  intros.
  remember (Heap.cardinal (elt:=Z * type) H) as m.
  destruct m.
  symmetry in Heqm.
  apply HeapProp.cardinal_Empty in Heqm.
Admitted.

Lemma replicate_length : forall (n : nat) (T : type),
(length (replicate n T)) = n.
Proof.
  intros n T. induction n.
    -simpl. reflexivity.
    -simpl. rewrite IHn. reflexivity.
Qed.

Lemma replicate_length_nth {A} : forall (n k : nat) (w x : A),
    nth_error (replicate n w) k = Some x -> (k < n)%nat.
Proof.
  intros n; induction n; intros; simpl in *; auto.
  - inv H.
    destruct k; inv H1.
  - destruct k.
    + lia.
    + simpl in *.
      apply IHn in H.
      lia.
Qed.

(* Progress:
     If [e] is well-formed with respect to [D] and
        [e] has type [t] under heap [H] in mode [m]
     Then
        [e] is a value, [e] reduces, or [e] is stuck in unchecked code *)
Lemma pos_succ : forall x, exists n, (Pos.to_nat x) = S n.
Proof.
   intros x. destruct (Pos.to_nat x) eqn:N.
    +zify. lia.
    +exists n. reflexivity.
Qed.

Ltac remove_options :=
  match goal with
  | [ H: Some ?X = Some ?Y |- _ ] => inversion H; subst X; clear H
  end.

(*No longer provable since we can allocate
bounds that are less than 0 now.
Lemma allocate_bounds : forall D l h t b ts,
Some(b, ts) = allocate_meta D (TArray l h t) ->
l = 0 /\ h > 0.
Proof.
intros.
destruct l.
  +destruct h.
    *simpl in H. inv H.
    *zify. omega.
    *simpl in H. inv H.
  +simpl in H. inv H.
  +simpl in H. inv H.
Qed.
*)

Lemma fields_aux : forall fs,
length (map snd (Fields.elements (elt:=type) fs)) = length (Fields.elements (elt:=type) fs).
Proof.
  intros. eapply map_length.
Qed.

Lemma obvious_list_aux : forall (A : Type) (l : list A),
(length l) = 0%nat -> 
l = nil.
Proof.
  intros. destruct l.
  - reflexivity.
  - inv H.
Qed.

(*These are obvious*)
Lemma fields_implies_length : forall fs t,
Some t = Fields.find (elt:=type) 0%nat fs ->
((length (Fields.elements (elt:=type) fs) > 0))%nat.
Proof.
 intros.
 assert (Fields.find (elt:=type) 0%nat fs = Some t) by easy.
 apply Fields.find_2 in H0.
 apply Fields.elements_1 in H0.
 destruct ((Fields.elements (elt:=type) fs)).
 inv H0. simpl. lia.
Qed.

(*
Lemma element_implies_element : forall T f D x,
(StructDef.MapsTo T f D) ->
Some x = Fields.find (elt:=type) 0%nat f ->
Some x =
match 
  map snd (Fields.elements (elt:=type) f)
  with
  |nil => None
  | z::_ => Some z
  end.
Proof.
Admitted.

Lemma element_implies_element_1 : forall T f D x,
(StructDef.MapsTo T f D) ->
Some x =
match 
  map snd (Fields.elements (elt:=type) f)
  with
  |nil => None
  | z::_ => Some z
  end
->
Some x = Fields.find (elt:=type) 0%nat f.
Proof.
Admitted.
*)

Lemma find_implies_mapsto : forall s D f,
StructDef.find (elt:=fields) s D = Some f ->
StructDef.MapsTo s f D.
Proof.
  intros. 
  eapply StructDef.find_2. assumption.
Qed.


Lemma struct_subtype_non_empty : forall m T fs D,
subtype D (TPtr m (TStruct T)) (TPtr m TNat) ->
(StructDef.MapsTo T fs D) ->
Z.of_nat(length (map snd (Fields.elements (elt:=type) fs))) > 0.
Proof.
  intros. remember (TPtr m (TStruct T)) as p1.
  remember (TPtr m TNat) as p2. induction H.
  - exfalso. rewrite Heqp1 in Heqp2. inv Heqp2.
  - exfalso. inv Heqp2.
  - exfalso. inv Heqp1.
  - exfalso. inv Heqp1.
  - exfalso. inv Heqp2.
  - inv Heqp1.
  - inv Heqp1.
  - inv Heqp1. assert (fs = fs0) by (eapply StructDefFacts.MapsTo_fun; eauto). 
    eapply fields_implies_length in H1. rewrite H2.
    zify. eauto. rewrite map_length. assumption.
  - inv Heqp2. 
Qed.

Lemma struct_subtype_non_empty_1 : forall m T fs D,
subtype D (TPtr m (TStruct T)) (TPtr m (TArray (Num 0) (Num 1) TNat)) ->
(StructDef.MapsTo T fs D) ->
Z.of_nat(length (map snd (Fields.elements (elt:=type) fs))) > 0.
Proof.
  intros. remember (TPtr m (TStruct T)) as p1.
  remember (TPtr m (TArray (Num 0) (Num 1) TNat)) as p2. induction H.
  - exfalso. rewrite Heqp1 in Heqp2. inv Heqp2.
  - exfalso. inv Heqp2. inv Heqp1.
  - exfalso. inv Heqp1.
  - exfalso. inv Heqp1.
  - exfalso. inv Heqp1.
  - inv Heqp1.
  - inv Heqp2. 
  - inv Heqp1. inv Heqp2. 
  - inv Heqp1. inv Heqp2. 
    assert (fs = fs0) by (eapply StructDefFacts.MapsTo_fun; eauto). 
    eapply fields_implies_length in H1. rewrite H4.
    zify. eauto. rewrite map_length. assumption.
Qed.

Lemma struct_subtype_non_empty_2 : forall m T fs D,
subtype D (TPtr m (TStruct T)) (TPtr m (TNTArray (Num 0) (Num 1) TNat)) ->
(StructDef.MapsTo T fs D) ->
Z.of_nat(length (map snd (Fields.elements (elt:=type) fs))) > 0.
Proof.
  intros. remember (TPtr m (TStruct T)) as p1.
  remember (TPtr m (TNTArray (Num 0) (Num 1) TNat)) as p2. induction H.
  - exfalso. rewrite Heqp1 in Heqp2. inv Heqp2.
  - exfalso. inv Heqp2.
  - exfalso. inv Heqp2. inv Heqp1.
  - exfalso. inv Heqp1.
  - exfalso. inv Heqp1.
  - inv Heqp1.
  - inv Heqp1. 
  - inv Heqp2. 
  - inv Heqp1. inv Heqp2. 
Qed.

Definition sub_domain (env: env) (S:stack) := forall x, Env.In x env -> Stack.In x S.

Lemma gen_cast_bound_same :
   forall env s b, well_bound_in env b -> sub_domain env s -> (exists b', cast_bound s b = Some b').
Proof.
  intros. induction b.
  exists (Num z). unfold cast_bound. reflexivity.
  inv H. unfold sub_domain in *.
  apply H0 in H3. 
  unfold cast_bound.
  unfold Stack.In,Stack.Raw.PX.In in *.
  destruct H3. apply Stack.find_1 in H.
  destruct (Stack.find (elt:=Z * type) v s).
  injection H as eq1. destruct p.
  exists (Num (z + z0)). reflexivity.
  inv H.
Qed.

Lemma gen_cast_type_bound_same :
   forall env s t, well_type_bound_in env t -> sub_domain env s -> (exists t', cast_type_bound s t t').
Proof.
  intros. induction t.
  exists TNat. apply cast_type_bound_nat.
  inv H. apply IHt in H3. destruct H3.
  exists (TPtr m x). apply cast_type_bound_ptr. assumption.
  exists (TStruct s0). apply cast_type_bound_struct.
  inv H. apply IHt in H7. destruct H7.
  apply (gen_cast_bound_same env0 s) in H5.
  apply (gen_cast_bound_same env0 s) in H6.
  destruct H5. destruct H6.
  exists (TArray x0 x1 x).
  apply cast_type_bound_array.
  1 - 5: assumption.
  inv H. apply IHt in H7. destruct H7.
  apply (gen_cast_bound_same env0 s) in H5.
  apply (gen_cast_bound_same env0 s) in H6.
  destruct H5. destruct H6.
  exists (TNTArray x0 x1 x).
  apply cast_type_bound_ntarray.
  1 - 5: assumption.
Qed.



Lemma cast_type_bound_same : forall s t t' t'',
              cast_type_bound s t t' -> cast_type_bound s t t'' -> t' = t''.
Proof.
 intros s t.
 induction t.
 intros. inv H0. inv H. reflexivity.
 intros.
 inv H. inv H0.
 assert (t' = t'0).
 apply IHt. assumption. assumption. rewrite H. reflexivity.
 intros. inv H. inv H0. reflexivity.
 intros. inv H. inv H0.
 unfold cast_bound in *.
 destruct b. destruct b0. inv H4. inv H6. inv H3. inv H8.
 assert (t' = t'0).
 apply IHt. assumption. assumption. rewrite H. reflexivity.
 destruct (Stack.find (elt:=Z * type) v s). destruct p.
 inv H4. inv H6. inv H3. inv H8.
 assert (t' = t'0).
 apply IHt. assumption. assumption. rewrite H. reflexivity.
 inv H6. destruct b0. 
 destruct (Stack.find (elt:=Z * type) v s). destruct p.
 inv H4. inv H6. inv H3. inv H8.
 assert (t' = t'0).
 apply IHt. assumption. assumption. rewrite H. reflexivity.
 inv H3.
 destruct (Stack.find (elt:=Z * type) v s). destruct p.
 destruct (Stack.find (elt:=Z * type) v0 s). destruct p.
 inv H4. inv H6. inv H3. inv H8.
 assert (t' = t'0).
 apply IHt. assumption. assumption. rewrite H. reflexivity.
 inv H6. inv H3. 
 intros. inv H. inv H0.
 unfold cast_bound in *.
 destruct b. destruct b0. inv H4. inv H6. inv H3. inv H8.
 assert (t' = t'0).
 apply IHt. assumption. assumption. rewrite H. reflexivity.
 destruct (Stack.find (elt:=Z * type) v s). destruct p.
 inv H4. inv H6. inv H3. inv H8.
 assert (t' = t'0).
 apply IHt. assumption. assumption. rewrite H. reflexivity.
 inv H6. destruct b0. 
 destruct (Stack.find (elt:=Z * type) v s). destruct p.
 inv H4. inv H6. inv H3. inv H8.
 assert (t' = t'0).
 apply IHt. assumption. assumption. rewrite H. reflexivity.
 inv H3.
 destruct (Stack.find (elt:=Z * type) v s). destruct p.
 destruct (Stack.find (elt:=Z * type) v0 s). destruct p.
 inv H4. inv H6. inv H3. inv H8.
 assert (t' = t'0).
 apply IHt. assumption. assumption. rewrite H. reflexivity.
 inv H6. inv H3. 
Qed.

Lemma lit_empty_means_cast_type_bound_same :
  forall D F S H m n t t1, @well_typed D F S H empty_env m (ELit n t) t1 ->  cast_type_bound S t t.
Proof.
 intros. remember empty_env as env.
 remember (ELit n t) as e.
 induction H0.
 subst.
 injection Heqe.
 intros.
 rewrite <- H2.
 apply (empty_means_cast_type_bound_same S) in H0.
 assumption.
 1 - 22 : inv Heqe.
Qed.

Lemma lit_nat_type : forall D F S H env m n t, @well_typed D F S H env m (ELit n t) TNat -> t = TNat.
Proof.
 intros. remember (ELit n t) as e. remember TNat as t1.
 induction H0; subst; inv Heqe.
 reflexivity.
Qed.

Lemma simple_type_means_cast_same: forall s t, simple_type t -> cast_type_bound s t t.
Proof.
  intros. induction H.
  apply cast_type_bound_nat.
  apply cast_type_bound_ptr.
  assumption.
  apply cast_type_bound_struct.
  apply cast_type_bound_array.
  unfold cast_bound. reflexivity.
  unfold cast_bound. reflexivity.
  assumption.
  apply cast_type_bound_ntarray.
  unfold cast_bound. reflexivity.
  unfold cast_bound. reflexivity.
  assumption.
Qed.


Lemma cast_means_simple_type : forall s t t', cast_type_bound s t t' -> simple_type t'.
Proof.
  intros. induction H. 
  apply SPTNat. apply SPTPtr. assumption.
  unfold cast_bound in *.
  destruct l. destruct h.
  injection H as eq1. injection H0 as eq2.
  subst. 
  apply SPTArray. assumption.
  destruct (Stack.find (elt:=Z * type) v s).
  destruct p.
  injection H0 as eq1. injection H as eq2. subst.
  apply SPTArray. assumption.
  inv H0.
  destruct (Stack.find (elt:=Z * type) v s). destruct p.
  destruct h.
  inv H. inv H0.
  apply SPTArray. assumption.
  destruct (Stack.find (elt:=Z * type) v0 s). destruct p.
  inv H. inv H0.
  apply SPTArray. assumption.
  inv H0. inv H.
  unfold cast_bound in *.
  destruct l. destruct h.
  injection H as eq1. injection H0 as eq2.
  subst. 
  apply SPTNTArray. assumption.
  destruct (Stack.find (elt:=Z * type) v s).
  destruct p.
  inv H. inv H0.
  apply SPTNTArray. assumption.
  inv H0.
  destruct (Stack.find (elt:=Z * type) v s). destruct p.
  destruct h.
  inv H. inv H0.
  apply SPTNTArray. assumption.
  destruct (Stack.find (elt:=Z * type) v0 s). destruct p.
  inv H. inv H0.
  apply SPTNTArray. assumption.
  inv H0. inv H.
  apply SPTStruct.
Qed.

Lemma cast_word_type : forall s t t', cast_type_bound s t t' -> word_type t -> word_type t'.
Proof.
 intros. inv H0. inv H. constructor.
 inv H. constructor.
Qed.

Lemma cast_type_wf : forall D s t t', cast_type_bound s t t' -> type_wf D t -> type_wf D t'.
Proof.
 intros. generalize dependent t'. induction t.
 intros. inv H. constructor.
 intros. inv H. constructor. apply IHt. inv H0. assumption.
 assumption.
 intros. inv H. constructor.
 inv H0. destruct H1. exists x. assumption.
 intros. inv H.
 constructor. inv H0. eapply cast_word_type. apply H7. assumption.
 apply IHt. inv H0. assumption. assumption.
 intros. inv H.
 constructor. inv H0. eapply cast_word_type. apply H7. assumption.
 apply IHt. inv H0. assumption. assumption.
Qed.

Lemma always_gen_stack : 
               forall vl es e, length vl = length es -> (exists e', gen_stack vl es e = Some e').
Proof.
  intro vl. 
  induction vl. 
  intros. simpl.
  exists e. easy.
  intros.
  simpl. destruct es. inv H.
  inv H. apply (IHvl es e) in H1.
  destruct H1.
  rewrite H.
  exists (ELet a e0 x).
  reflexivity.
Qed.

Lemma subtype_simple_left : forall D t t', subtype D t t'
                 -> simple_type t' -> simple_type t.
Proof.
  intros. 
  induction H. assumption.
  inv H0. inv H2.
  constructor. inv H4. easy.
  inv H0. inv H1. inv H2.
  constructor. constructor. easy.
  inv H0. inv H1. inv H2.
  constructor. constructor. easy.
  inv H0. inv H3. inv H. inv H1.
  constructor. constructor. easy.
  inv H0. inv H3. inv H. inv H1.
  constructor. constructor. easy.
  inv H0. inv H3. inv H. inv H1.
  constructor. constructor. easy.
  constructor. constructor.
  constructor. constructor.
Qed.

(*
Lemma subtype_simple_right : forall D t t', subtype D t' t
                 -> simple_type t' -> simple_type t.
Proof.
  intros. 
  induction H. assumption.
  constructor. inv H0. apply SPTArray.
  1-6: constructor.
  inv H0. inv H3.
  constructor.
  inv H. inv H1. apply SPTArray. assumption.
  constructor. inv H0. inv H3.
  inv H. inv H1.
  apply SPTNTArray. assumption.
  constructor. 
  apply SPTNat.
Qed.
*)

Lemma eval_simple_type_same : forall s t, simple_type t -> eval_type_bound s t = Some t.
Proof.
  intros. unfold eval_type_bound.
  induction t; try easy.
  destruct t. easy. easy. easy.
  unfold eval_bound.
  inv H. inv H1. easy.
  unfold eval_bound.
  inv H. inv H1. easy.
Qed.

Lemma type_eq_word_type : forall s t t', type_eq s t t' -> word_type t -> word_type t'.
Proof.
  intros. inv H0. inv H. constructor.
  inv H1. constructor.
  inv H1. constructor.
  inv H. constructor.
  inv H1. constructor.
  inv H1. constructor.
Qed.

Lemma meet_type_word_type : forall D s t t1 t2, meet_type D s t t1 t2 -> word_type t -> word_type t1.
Proof.
  intros. inv H0. inv H.
  inv H0. constructor.
  inv H0. inv H2. inv H1. constructor.
  inv H0. constructor.
  inv H0. inv H2. inv H1.
  constructor.
  inv H. inv H0.
  1 - 9: constructor.
  inv H0. inv H2. inv H1.
  constructor.
  inv H1.
  constructor.
  inv H1.
  constructor.
  inv H1.
  constructor.
  inv H1. constructor.
  inv H1. constructor.
  inv H1. constructor.
  inv H1. constructor.
  inv H1. constructor.
  inv H0. 1 - 9 : constructor.
  inv H0.
  apply ptr_subtype_equiv in H2.
  destruct H2. subst.
  inv H1. constructor.
Qed.

Lemma type_eq_simple_same : forall s t t', type_eq s t t' -> simple_type t -> simple_type t' -> t = t'.
Proof.
  intros. induction H.
  easy. 
  apply (simple_type_means_cast_same s t2) in H1.
  apply (cast_type_bound_same s t2 t1) in H1. easy.
  easy.
  apply (simple_type_means_cast_same s t1) in H0.
  apply (cast_type_bound_same s t1 t2) in H0. easy.
  easy.
Qed.

Lemma meet_type_tnat : forall D s t1 t2, meet_type D s TNat t1 t2 -> t1 = TNat.
Proof.
  intros. inv H. inv H0. easy.
  inv H0. inv H2. inv H1. easy.
  inv H0. easy. inv H0. inv H2. inv H1.
  easy.
Qed.

Lemma type_eq_tnat : forall s t, type_eq s TNat t -> t = TNat.
Proof.
  intros. remember TNat as t'. induction H. easy.
  subst. inv H0. easy.
  subst. inv H0. easy.
Qed.

Lemma type_eq_struct : forall s T t, type_eq s (TStruct T) t -> t = TStruct T.
Proof.
  intros. remember (TStruct T) as t'. induction H. easy.
  subst. inv H0. easy.
  subst. inv H0. easy.
Qed.

Lemma sub_domain_grow : forall env S x v t t', sub_domain env S 
                 -> sub_domain (Env.add x t env) (Stack.add x (v,t') S).
Proof.
  intros.
  unfold sub_domain in *.
  intros.
  unfold Env.In,Env.Raw.PX.In in H0.
  destruct H0.
  unfold Stack.In,Stack.Raw.PX.In.
  destruct (Nat.eq_dec x x0).
  subst.
  exists (v,t').
  apply Stack.add_1. easy.
  apply Env.add_3 in H0.
  assert (Env.In x0 env0).
  unfold Env.In,Env.Raw.PX.In.
  exists x1. easy.
  apply H in H1.
  unfold Stack.In,Stack.Raw.PX.In in H1.
  destruct H1.
  exists x2.
  apply Stack.add_2.
  lia. assumption. lia.
Qed.

Lemma typed_args_values :
    forall D H s env es tvl, 
        sub_domain env s ->
        well_typed_args D H s env es tvl -> 
          (exists vl, eval_el s tvl es vl).
Proof.
  intros.
  remember empty_env as env.
  induction H1.
  exists []. apply eval_el_empty.
  inv H2.
  inv H3.
  specialize (sub_domain_grow env0 S v n t t' H0) as eq1.
  apply IHwell_typed_args in eq1.
  destruct eq1.
  exists ((ELit n t')::x).
  apply eval_el_many.
  apply eval_lit. assumption.
  assumption.
  unfold is_ok_up in H2.
  destruct H2.
  apply (gen_cast_type_bound_same env0 S') in H5.
  easy. assumption.
  inv H3.
  specialize (sub_domain_grow env0 S v n t t1 H0) as eq1.
  apply IHwell_typed_args in eq1.
  destruct eq1.
  exists (ELit n t1:: x0).
  apply eval_el_many.
  apply eval_var.
  assumption.
  assumption.
  unfold is_ok_up in H2.
  unfold sub_domain in H0.
  assert (Env.In x env0).
  unfold Env.In,Env.Raw.PX.In.
  exists t0. assumption.
  apply H0 in H3.
  contradiction.
Qed.

Lemma typed_args_empty_values :
    forall D H s es tvl, 
        well_typed_args D H s empty_env es tvl -> 
          (exists vl, eval_el s tvl es vl).
Proof.
  intros.
  eapply typed_args_values.
  assert (sub_domain empty_env s).
  unfold sub_domain.
  intros. inv H1. inv H2.
  apply H1.
  apply H0.
Qed.

Lemma eval_el_gen_e : forall s tvl es e vl, eval_el s tvl es vl -> (exists e', gen_e tvl vl e e').
Proof.
  intros.
  induction H.
  exists e. apply gen_e_empty.
  destruct IHeval_el. 
  exists (ELet x (ELit v t') x0).
  apply gen_e_many.
  assumption.
Qed.

Lemma subtype_word_type : forall D m t1 t2, word_type t1 -> 
        subtype D (TPtr m t1) (TPtr m t2) -> t2 = t1 \/ (exists l h, nat_leq (Num 0) l
                                   /\ nat_leq h (Num 1) /\ t2 = TArray l h t1).
Proof.
  intros. 
  inv H0. left. easy.
  right. exists l. exists h. easy.
  inv H. inv H. inv H. inv H. inv H.
  inv H. inv H.
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

Lemma nth_error_map_snd : forall (l : list (Z*type)) t i,
                nth_error (map snd l) i = Some t -> (exists x, nth_error l i = Some (x,t)).
Proof.
  intros. generalize dependent i.
  induction l.
  intros.
  destruct i eqn:eq1.
  simpl in *. inv H.
  inv H.
  intros.
  destruct i.
  simpl.
  simpl in H.
  destruct a.
  exists z. inv H. easy.
  simpl in H.
  apply IHl in H.
  simpl.
  easy.
Qed.

Check InA.

Check Fields.elements_1.

Lemma progress : forall D F H s m e t,
    structdef_wf D ->
    heap_wf D H ->
    expr_wf D F e ->
    fun_typed D F s H -> 
    @well_typed D F s H empty_env m e t ->
    value D e \/
    reduces D F s H e \/
    unchecked m e.
Proof with eauto 20 with Progress.
  intros D F H st m e t HDwf HHwf Hewf Hfun Hwt.
  remember empty_env as env.
  induction Hwt as [
                     env m n t Wb HTyLit                                      | (* Literals *)
                     env m x t Wb HVarInEnv                                   | (* Variables *)
                      env m es x tvl t e t' t'' HMap HArg HTy HSub            | (* Call *)
                     env m x h l t Wb HVE                                     | (* Strlen *)
                     env m x e1 t1 e2 t HTy1 IH1 HTy2 IH2                     | (* Let-Expr *)
                     env m e1 e2 HTy1 IH1 HTy2 IH2                            | (* Addition *)
                     env m e m' T fs i fi ti HTy IH HWf1 HWf2                 | (* Field Addr *)
                     env m w Wb                                               | (* Malloc *)
                     env m e t HTy IH                                         | (* Unchecked *)
                     env m t e t' Wb HChkPtr HTy IH                           | (* Cast - nat *)
                     env m t e t' Wb HTy IH HSub                              | (* Cast - subtype *)
                     env m e x y u v t t' Teq Wb HTy IH                       | (* DynCast - ptr array *)
                     env m e x y t t' Teq HNot Wb HTy IH                      | (* DynCast - ptr array from ptr *)
                     env m e x y u v t t' Teq Wb HTy IH                       | (* DynCast - ptr nt-array *)
                     env m e m' t l h t' t'' HTy IH HSub HPtrType HMode       | (* Deref *)
                     env m e1 m' l h t e2 t' WT Twf HTy1 IH1 HSubType HTy2 IH2 HMode                | (* Index for array pointers *)
                     env m e1 m' l h t e2 t' WT Twf HTy1 IH1 HSubType HTy2 IH2 HMode                | (* Index for ntarray pointers *)
                     env m e1 e2 m' t t1 t2 HSubType WT HTy HTy1 IH1 HTy2 IH2 HMode                 | (* Assign normal *)
                     env m e1 e2 m' l h t t' t'' WT Twf Teq HSub HTy1 IH1 HTy2 IH2 HMode            | (* Assign array *)
                     env m e1 e2 m' l h t t' t'' WT Twf Teq HSub HTy1 IH1 HTy2 IH2 HMode            | (* Assign nt-array *)

                     env m e1 e2 e3 m' l h t t' t'' WT Twf Teq TSub HTy1 IH1 HTy2 IH2 HTy3 IH3 HMode      |  (* IndAssign for array pointers *)
                     env m e1 e2 e3 m' l h t t' t'' WT Twf Teq TSub HTy1 IH1 HTy2 IH2 HTy3 IH3 HMode      |  (* IndAssign for ntarray pointers *)
                     env m m' x t t1 e1 e2 t2 t3 t4 HEnv HSubType HPtrType HTy1 IH1 HTy2 IH2 HMeet HMode (* If *)
                   ]; clean.

  (* Case: TyLit *)
  - (* Holds trivially, since literals are values *)
    left...
    inv Hewf. apply VLit. assumption. assumption.  
  (* Case: TyVar *)
  - (* Impossible, since environment is empty *)
    inversion HVarInEnv.
  - (* Call Case *)
    right. left.
    specialize (typed_args_empty_values D H st es tvl HArg) as eq1.
    destruct eq1.
    specialize (eval_el_gen_e st tvl es e x0 H0) as eq2.
    destruct eq2.
    eapply step_implies_reduces.
    apply (SCall D F st H x es x0 t tvl e x1).
    assumption.
    assumption.
    assumption.
  -   (* Case: TyStrlen *)
    inv HVE.
  (* Case: TyLet *)
  - (* `ELet x e1 e2` is not a value *)
    right.
    (* Invoke the IH on `e1` *)
    inv Hewf. apply IH1 in H2.
    2: { easy. }
    destruct H2 as [ HVal1 | [ HRed1 | HUnchk1 ] ].
    (* Case: `e1` is a value *)
    + (* We can take a step according to SLet *)
      left.  
      inv HVal1...
      apply (step_implies_reduces D F H st (ELet x (ELit n t0) e2) H (Stack.add x (n, t0) st) (RExpr e2)).
      apply SLet.
      apply (lit_empty_means_cast_type_bound_same D F st) in HTy1.
      assumption.
    (* Case: `e1` reduces *)
    + (* We can take a step by reducing `e1` *)
      left.
      ctx (ELet x e1 e2) (in_hole e1 (CLet x CHole e2))...
    (* Case: `e1` is unchecked *)
    + (* `ELet x e1 e2` must be unchecked, since `e1` is *)
      right.
      ctx (ELet x e1 e2) (in_hole e1 (CLet x CHole e2)).
      destruct HUnchk1...
  (* Case: TyPlus *)
  - (* `EPlus e1 e2` isn't a value *)
    right.
    inv Hewf. apply IH1 in H2. 2:{ easy. }
    (* Invoke the IH on `e1` *)
    destruct H2 as [ HVal1 | [ HRed1 | HUnchk1 ] ].
    (* Case: `e1` is a value *)
    + (* We don't know if we can take a step yet, since `e2` might be unchecked. *)
      inv HVal1 as [ n1 t1 ].
      (* Invoke the IH on `e2` *)
      apply IH2 in H3. 2:{ easy. }
      destruct H3 as [ HVal2 | [ HRed2 | HUnchk2 ] ].
      (* Case: `e2` is a value *)
      * (* We can step according to SPlus *)
        left.
        inv HVal2 as [ n2 t2 ]...
        eapply (step_implies_reduces D F H st (EPlus (ELit n1 t1) (ELit n2 t2)) H st (RExpr (ELit (n1 + n2) t1))).
        apply lit_nat_type in HTy2. subst.
        apply (@SPlus D F st H t1 n1 n2).
        apply lit_nat_type in HTy1. subst.
        unfold is_array_ptr. easy.
      (* Case: `e2` reduces *)
      * (* We can take a step by reducing `e2` *)
        left.
        ctx (EPlus (ELit n1 t1) e2) (in_hole e2 (CPlusR n1 t1 CHole))...
      (* Case: `e2` is unchecked *)
      * (* `EPlus (n1 t1) e2` must be unchecked, since `e2` is *)
        right.
        ctx (EPlus (ELit n1 t1) e2) (in_hole e2 (CPlusR n1 t1 CHole)).
        destruct HUnchk2...
    (* Case: `e1` reduces *)
    + (* We can take a step by reducing `e1` *)
      left.
      ctx (EPlus e1 e2) (in_hole e1 (CPlusL CHole e2))...
    (* Case: `e1` is unchecked *)
    + (* `EPlus e1 e2` must be unchecked, since `e1` is *)
      right.
      ctx (EPlus e1 e2) (in_hole e1 (CPlusL CHole e2)).
      destruct HUnchk1...
  (* Case: TyFieldAddr *)
  - (* `EFieldAddr e fi` isn't a value *)
    right.
    inv Hewf. apply IH in H2. 2: { easy. }
    (* Invoke the IH on `e` *)
    destruct H2 as [ HVal | [ HRed | HUnchk ] ].
    (* Case: `e` is a value *)
    + (* So we can take a step... but how? *)
      left.
      inv HVal.
      inv HTy.
      {
        (* We proceed by case analysis on `m'` -- the mode of the pointer *)
        destruct m'.
        (* Case: m' = Checked *)
        * (* We now proceed by case analysis on 'n > 0' *)
          destruct (Z_gt_dec n 0).
          (* Case: n > 0 *)
          { (* We can step according to SFieldAddrChecked  *)
            assert (HWf3 := HDwf T fs HWf1). (* TODO(ins): turn these into lemmas, and stick into Progress db *)
            assert (HWf4 := HWf3 fi ti HWf2).
            destruct HWf4... }
          (* Case: n <= 0 *)
          { (* We can step according to SFieldAddrNull *)
             subst...   }
        (* Case: m' = Unchecked *)
        * (* We can step according to SFieldAddr *)
          eapply step_implies_reduces; eapply SFieldAddr; eauto.
          { (* LEO: This should probably be abstracted into a lemma *)
            apply HDwf in HWf1.
            apply HWf1 in HWf2.
            destruct HWf2...
          }
      }

        
    (* Case: `e` reduces *)
    + (* We can take a step by reducing `e` *)
      left.
      ctx (EFieldAddr e fi) (in_hole e (CFieldAddr CHole fi))...
    (* Case: `e` is unchecked *)
    + (* `EFieldAddr e fi` must be unchecked, since `e` is *)
      right.
      ctx (EFieldAddr e fi) (in_hole e (CFieldAddr CHole fi)).
      destruct HUnchk...
  (* Case: TyMalloc *)
  - (* `EMalloc w` isn't a value *)
    right.
    (* Allocation always succeeds, according to SMalloc *)
    left.
    inv Hewf.
    specialize (well_typed_means_simple w Wb) as eq1.
    destruct w.
    * assert ((forall (l h : Z) (t : type),
       TNat = TArray (Num l) (Num h) t -> l = 0 /\ h > 0)).
      intros. inv H0.
      assert (((forall (l h : Z) (t : type),
       TNat = TNTArray (Num l) (Num h) t -> l = 0 /\ h > 0))).
      intros. inv H2.
       destruct ((wf_implies_allocate D TNat H H0 H2 eq1 H1)) as [ n [ H' HAlloc]].
       apply (step_implies_reduces D F H st (EMalloc TNat) H' st (RExpr (ELit n (TPtr Checked TNat)))).
       apply SMalloc.
       apply cast_type_bound_nat.
       unfold malloc_bound. reflexivity.
       assumption.
   * assert ((forall (l h : Z) (t : type),
       (TPtr m0 w) = TArray (Num l) (Num h) t -> l = 0 /\ h > 0)).
      intros. inv H0.
      assert (((forall (l h : Z) (t : type),
       (TPtr m0 w) = TNTArray (Num l) (Num h) t -> l = 0 /\ h > 0))).
      intros. inv H2.
       destruct ((wf_implies_allocate D (TPtr m0 w) H H0 H2 eq1 H1)) as [ n [ H' HAlloc]].
       apply (step_implies_reduces D F H st (EMalloc (TPtr m0 w)) H' st (RExpr (ELit n (TPtr Checked (TPtr m0 w))))).
       apply SMalloc.
       apply cast_type_bound_ptr.
       apply (simple_type_means_cast_same).
       inv eq1. assumption.
       unfold malloc_bound. reflexivity.
       assumption.
   * assert ((forall (l h : Z) (t : type),
       (TStruct s) = TArray (Num l) (Num h) t -> l = 0 /\ h > 0)).
      intros. inv H0.
      assert (((forall (l h : Z) (t : type),
       (TStruct s) = TNTArray (Num l) (Num h) t -> l = 0 /\ h > 0))).
      intros. inv H2.
       destruct ((wf_implies_allocate D (TStruct s) H H0 H2 eq1 H1)) as [ n [ H' HAlloc]].
       apply (step_implies_reduces D F H st (EMalloc (TStruct s)) H' st (RExpr (ELit n (TPtr Checked (TStruct s))))).
       apply SMalloc.
       apply cast_type_bound_struct.
       unfold malloc_bound. reflexivity.
       assumption.
   * inv eq1.
     destruct (Z.eq_dec l 0).
     destruct (0 <? h) eqn:eq2.
     apply Z.ltb_lt in eq2.
     assert ((forall (l' h' : Z) (t : type),
       (TArray (Num l) (Num h) w) = TArray (Num l') (Num h') t -> l' = 0 /\ h' > 0)).
      intros. split. injection H0.
      intros. subst. reflexivity.
      injection H0. intros. subst.  lia.
      assert ((forall (l' h' : Z) (t : type),
       (TArray (Num l) (Num h) w) = TNTArray (Num l') (Num h') t -> l' = 0 /\ h' > 0)).
       intros. inv H3.
       assert (simple_type (TArray (Num l) (Num h) w)).
       apply SPTArray. apply H2.
       destruct ((wf_implies_allocate D (TArray (Num l) (Num h) w) H H0 H3 H4 H1)) as [ n [ H' HAlloc]].
       apply (step_implies_reduces D F H st (EMalloc (TArray (Num l) (Num h) w))
                             H' st (RExpr (ELit n (TPtr Checked (TArray (Num l) (Num h) w))))).
       apply SMalloc.
       apply cast_type_bound_array.
       unfold cast_bound. reflexivity.
       unfold cast_bound. reflexivity.
       apply simple_type_means_cast_same. assumption.
       unfold malloc_bound. split. assumption. lia.
       assumption.
       assert (h <= 0).
       specialize (Z.ltb_lt 0 h) as eq3.
       apply not_iff_compat in eq3.
       assert((0 <? h) <> true).
       apply not_true_iff_false. assumption.
       apply eq3 in H0. lia.
       apply (step_implies_reduces D F H st (EMalloc (TArray (Num l) (Num h) w)) H st RBounds).
       apply (SMallocHighOOB D F st H (TArray (Num l) (Num h) w) (TArray (Num l) (Num h) w) h).
       assumption. apply cast_type_bound_array.
       unfold cast_bound. easy.
       unfold cast_bound. easy.
       apply simple_type_means_cast_same. assumption.
       unfold get_high. easy.
       apply (step_implies_reduces D F H st (EMalloc (TArray (Num l) (Num h) w)) H st RBounds).
       apply (SMallocLowOOB D F st H (TArray (Num l) (Num h) w) (TArray (Num l) (Num h) w) l).
       assumption.
       apply cast_type_bound_array.
       unfold cast_bound. easy.
       unfold cast_bound. easy.
       apply simple_type_means_cast_same. assumption.
       unfold get_low. easy.
   * inv eq1.
     destruct (Z.eq_dec l 0).
     destruct (0 <? h) eqn:eq2.
     apply Z.ltb_lt in eq2.
     assert ((forall (l' h' : Z) (t : type),
       (TNTArray (Num l) (Num h) w) = TArray (Num l') (Num h') t -> l' = 0 /\ h' > 0)).
       intros. inv H0.
      assert ((forall (l' h' : Z) (t : type),
       (TNTArray (Num l) (Num h) w) = TNTArray (Num l') (Num h') t -> l' = 0 /\ h' > 0)).
      intros. split. injection H3.
      intros. subst. reflexivity.
      injection H3. intros. subst.  lia.
       assert (simple_type (TNTArray (Num l) (Num h) w)).
       apply SPTNTArray. apply H2.
       destruct ((wf_implies_allocate D (TNTArray (Num l) (Num h) w) H H0 H3 H4 H1)) as [ n [ H' HAlloc]].
       apply (step_implies_reduces D F H st (EMalloc (TNTArray (Num l) (Num h) w))
                             H' st (RExpr (ELit n (TPtr Checked (TNTArray (Num l) (Num h) w))))).
       apply SMalloc.
       apply cast_type_bound_ntarray.
       unfold cast_bound. reflexivity.
       unfold cast_bound. reflexivity.
       apply simple_type_means_cast_same. assumption.
       unfold malloc_bound. split. assumption. lia.
       assumption.
       assert (h <= 0).
       specialize (Z.ltb_lt 0 h) as eq3.
       apply not_iff_compat in eq3.
       assert((0 <? h) <> true).
       apply not_true_iff_false. assumption.
       apply eq3 in H0. lia.
       apply (step_implies_reduces D F H st (EMalloc (TNTArray (Num l) (Num h) w)) H st RBounds).
       apply (SMallocHighOOB D F st H (TNTArray (Num l) (Num h) w) (TNTArray (Num l) (Num h) w) h).
       assumption.
       apply cast_type_bound_ntarray.
       unfold cast_bound. easy.
       unfold cast_bound. easy.
       apply simple_type_means_cast_same. assumption.
       unfold get_high. easy.
       apply (step_implies_reduces D F H st (EMalloc (TNTArray (Num l) (Num h) w)) H st RBounds).
       apply (SMallocLowOOB D F st H (TNTArray (Num l) (Num h) w) (TNTArray (Num l) (Num h) w) l).
       assumption.
       apply cast_type_bound_ntarray.
       unfold cast_bound. easy.
       unfold cast_bound. easy.
       apply simple_type_means_cast_same. assumption.
       unfold get_low. easy. 
  (* Case: TyUnchecked *)
  - (* `EUnchecked e` isn't a value *)
    right.
    inv Hewf. apply IH in H1. 2: { easy. }
    (* Invoke the IH on `e` *)
    destruct H1 as [ HVal | [ HRed | HUnchk ] ].
    (* Case: `e` is a value *)
    + (* We can step according to SUnchecked *)
      left.
      inv HVal...
    (* Case: `e` reduces *)
    + (* We can take a step by reducing `e` *)
      left.
      ctx (EUnchecked e) (in_hole e (CUnchecked CHole))...
    (* Case: `e` is unchecked *)
    + (* `EUnchecked e` is obviously unchecked *)
      right.
      ctx (EUnchecked e) (in_hole e (CUnchecked CHole))...
  (* Case: TyCast *)
  - (* `ECast t e` isn't a value when t is a nat type or is unchecked mode. *)
    right.
    inv Hewf. apply IH in H4. 2: { easy. }
    (* Invoke the IH on `e` *)
    destruct H4 as [ HVal | [ HRed | HUnchk ] ].
    (* Case: `e` is a value *)
    + (* We can step according to SCast *)
      destruct m.
      left.
      inv HVal.
      apply (step_implies_reduces D F H st (ECast t (ELit n t0)) H st (RExpr (ELit n t))).
      apply SCast.
      right. unfold unchecked. left.
      reflexivity.
    (* Case: `e` reduces *)
    + (* `ECast t e` can take a step by reducing `e` *)
      left.
      ctx (ECast t e) (in_hole e (CCast t CHole))...
    (* Case: `e` is unchecked *)
    + (* `ECast t e` must be unchecked, since `e` is *)
      right.
      ctx (ECast t e) (in_hole e (CCast t CHole)).
      destruct HUnchk...
  - (* `ECast t e` isn't a value when t is a nat type or is unchecked mode. *)
    right.
    inv Hewf. apply IH in H4. 2: { easy. }
    (* Invoke the IH on `e` *)
    destruct H4 as [ HVal | [ HRed | HUnchk ] ].
    (* Case: `e` is a value *)
    + (* We can step according to SCast *)
      destruct m.
      left.
      inv HVal.
      apply (step_implies_reduces D F H st (ECast (TPtr Checked t) (ELit n t0)) H st (RExpr (ELit n (TPtr Checked t)))).
      apply SCast.
      right. unfold unchecked. left.
      reflexivity.
    (* Case: `e` reduces *)
    + (* `ECast t e` can take a step by reducing `e` *)
      left.
      ctx (ECast (TPtr Checked t) e) (in_hole e (CCast (TPtr Checked t) CHole))...
    (* Case: `e` is unchecked *)
    + (* `ECast t e` must be unchecked, since `e` is *)
      right.
      ctx (ECast (TPtr Checked t) e) (in_hole e (CCast (TPtr Checked t) CHole)).
      destruct HUnchk...
  - (* `EDynCast t e` isn't a value when t is an array pointer. *)
    right.
    inv Hewf. apply IH in H4. 2 : { easy. }
    (* Invoke the IH on `e` *)
    destruct H4 as [ HVal | [ HRed | HUnchk ] ].
    (* Case: `e` is a value *)
    + (* We can step according to SCast *)
      left.
      inv HVal.
      inv HTy.
      specialize (well_typed_means_simple (TPtr Checked (TArray x y t)) Wb) as eq1.
      inv eq1. inv H5.
      specialize (well_typed_means_simple (TPtr Checked (TArray u v t')) H8) as eq1.
      inv eq1. inv H5.
      destruct (l0 <=? l) eqn:eq1.
      destruct (l <? h) eqn:eq2.
      destruct (h <=? h0) eqn:eq3.
      apply (step_implies_reduces D F H st (EDynCast (TPtr Checked (TArray (Num l) (Num h) t))
           (ELit n (TPtr Checked (TArray (Num l0) (Num h0) t')))) H st (RExpr (ELit n (TPtr Checked (TArray (Num l) (Num h) t))))).
      apply (SCastArray D F st H (TPtr Checked (TArray (Num l) (Num h) t)) n (TPtr Checked (TArray (Num l0) (Num h0) t'))
                  l h t l0 h0 t').
      unfold eval_type_bound,eval_bound. reflexivity.
      unfold eval_type_bound,eval_bound. reflexivity.
      apply Z.leb_le in eq1. assumption.
      apply Z.ltb_lt in eq2. assumption.
      apply Z.leb_le in eq3. assumption.
       assert (h0 < h).
       specialize (Z.leb_le h h0) as eq4.
       apply not_iff_compat in eq4.
       assert((h <=? h0) <> true).
       apply not_true_iff_false. assumption.
       apply eq4 in H4. lia.
      apply (step_implies_reduces D F H st (EDynCast (TPtr Checked (TArray (Num l) (Num h) t))
            (ELit n (TPtr Checked (TArray (Num l0) (Num h0) t')))) H st RBounds).
      apply (SCastArrayHighOOB1 D F st H (TPtr Checked (TArray (Num l) (Num h) t)) n (TPtr Checked (TArray (Num l0) (Num h0) t'))
                  l h t l0 h0 t').
      unfold eval_type_bound,eval_bound. reflexivity.
      unfold eval_type_bound,eval_bound. reflexivity.
      assumption.
       assert (h <= l).
       specialize (Z.ltb_lt l h) as eq4.
       apply not_iff_compat in eq4.
       assert((l <? h) <> true).
       apply not_true_iff_false. assumption.
       apply eq4 in H4. lia.
      apply (step_implies_reduces D F H st (EDynCast (TPtr Checked (TArray (Num l) (Num h) t))
            (ELit n (TPtr Checked (TArray (Num l0) (Num h0) t')))) H st RBounds).
      apply (SCastArrayLowOOB2 D F st H (TPtr Checked (TArray (Num l) (Num h) t)) n (TPtr Checked (TArray (Num l0) (Num h0) t'))
                  l h t l0 h0 t').
      unfold eval_type_bound,eval_bound. reflexivity.
      unfold eval_type_bound,eval_bound. reflexivity.
      assumption.
       assert (l < l0).
       specialize (Z.leb_le l0 l) as eq4.
       apply not_iff_compat in eq4.
       assert((l0 <=? l) <> true).
       apply not_true_iff_false. assumption.
       apply eq4 in H4. lia.
      apply (step_implies_reduces D F H st (EDynCast (TPtr Checked (TArray (Num l) (Num h) t))
            (ELit n (TPtr Checked (TArray (Num l0) (Num h0) t')))) H st RBounds).
      apply (SCastArrayLowOOB1 D F st H (TPtr Checked (TArray (Num l) (Num h) t)) n (TPtr Checked (TArray (Num l0) (Num h0) t'))
                  l h t l0 h0 t').
      unfold eval_type_bound,eval_bound. reflexivity.
      unfold eval_type_bound,eval_bound. reflexivity.
      assumption.
    (* Case: `e` reduces *)
    + (* `ECast t e` can take a step by reducing `e` *)
      left.
      ctx (EDynCast (TPtr Checked (TArray x y t)) e) (in_hole e (CDynCast (TPtr Checked (TArray x y t)) CHole))...
    (* Case: `e` is unchecked *)
    + (* `ECast t e` must be unchecked, since `e` is *)
      right.
      ctx (EDynCast (TPtr Checked (TArray x y t)) e) (in_hole e (CDynCast (TPtr Checked (TArray x y t)) CHole)).
      destruct HUnchk...
  - (* `EDynCast t e` isn't a value when t is an pointer. *)
    right.
    inv Hewf. apply IH in H4. 2 : { easy. }
    (* Invoke the IH on `e` *)
    destruct H4 as [ HVal | [ HRed | HUnchk ] ].
    (* Case: `e` is a value *)
    + (* We can step according to SCast *)
      left.
      inv HVal.
      inv HTy.
      specialize (well_typed_means_simple (TPtr Checked (TArray x y t)) Wb) as eq1.
      inv eq1. inv H5.
      apply (step_implies_reduces D F H st (EDynCast (TPtr Checked (TArray (Num l) (Num h) t))
           (ELit n (TPtr Checked t'))) H st (RExpr (ELit n (TPtr Checked (TArray (Num 0) (Num 1) t'))))).
      apply (SCastNoArray D F st H (TPtr Checked (TArray (Num l) (Num h) t)) n Checked t').
      assumption.
      unfold is_nor_array_ptr. easy.
    (* Case: `e` reduces *)
    + (* `ECast t e` can take a step by reducing `e` *)
      left.
      ctx (EDynCast (TPtr Checked (TArray x y t)) e) (in_hole e (CDynCast (TPtr Checked (TArray x y t)) CHole))...
    (* Case: `e` is unchecked *)
    + (* `ECast t e` must be unchecked, since `e` is *)
      right.
      ctx (EDynCast (TPtr Checked (TArray x y t)) e) (in_hole e (CDynCast (TPtr Checked (TArray x y t)) CHole)).
      destruct HUnchk...
  - (* `ECast t e` isn't a value when t is an nt-array pointer. *)
    right.
    inv Hewf. apply IH in H4. 2 : { easy. }
    (* Invoke the IH on `e` *)
    destruct H4 as [ HVal | [ HRed | HUnchk ] ].
    (* Case: `e` is a value *)
    + (* We can step according to SCast *)
      left.
      inv HVal.
      inv HTy.
      specialize (well_typed_means_simple (TPtr Checked (TNTArray x y t)) Wb) as eq1.
      inv eq1. inv H5.
      specialize (well_typed_means_simple (TPtr Checked (TNTArray u v t')) H8) as eq1.
      inv eq1. inv H5.
      destruct (l0 <=? l) eqn:eq1.
      destruct (l <? h) eqn:eq2.
      destruct (h <=? h0) eqn:eq3.
      apply (step_implies_reduces D F H st (EDynCast (TPtr Checked (TNTArray (Num l) (Num h) t))
           (ELit n (TPtr Checked (TNTArray (Num l0) (Num h0) t')))) H st (RExpr (ELit n (TPtr Checked (TNTArray (Num l) (Num h) t))))).
      apply (SCastNTArray D F st H (TPtr Checked (TNTArray (Num l) (Num h) t)) n (TPtr Checked (TNTArray (Num l0) (Num h0) t'))
                  l h t l0 h0 t').
      unfold eval_type_bound,eval_bound. reflexivity.
      unfold eval_type_bound,eval_bound. reflexivity.
      apply Z.leb_le in eq1. assumption.
      apply Z.ltb_lt in eq2. assumption.
      apply Z.leb_le in eq3. assumption.
       assert (h0 < h).
       specialize (Z.leb_le h h0) as eq4.
       apply not_iff_compat in eq4.
       assert((h <=? h0) <> true).
       apply not_true_iff_false. assumption.
       apply eq4 in H4. lia.
      apply (step_implies_reduces D F H st (EDynCast (TPtr Checked (TNTArray (Num l) (Num h) t))
            (ELit n (TPtr Checked (TNTArray (Num l0) (Num h0) t')))) H st RBounds).
      apply (SCastNTArrayHighOOB1 D F st H (TPtr Checked (TNTArray (Num l) (Num h) t)) n (TPtr Checked (TNTArray (Num l0) (Num h0) t'))
                  l h t l0 h0 t').
      unfold eval_type_bound,eval_bound. reflexivity.
      unfold eval_type_bound,eval_bound. reflexivity.
      assumption.
       assert (h <= l).
       specialize (Z.ltb_lt l h) as eq4.
       apply not_iff_compat in eq4.
       assert((l <? h) <> true).
       apply not_true_iff_false. assumption.
       apply eq4 in H4. lia.
      apply (step_implies_reduces D F H st (EDynCast (TPtr Checked (TNTArray (Num l) (Num h) t))
            (ELit n (TPtr Checked (TNTArray (Num l0) (Num h0) t')))) H st RBounds).
      apply (SCastNTArrayLowOOB2 D F st H (TPtr Checked (TNTArray (Num l) (Num h) t)) n (TPtr Checked (TNTArray (Num l0) (Num h0) t'))
                  l h t l0 h0 t').
      unfold eval_type_bound,eval_bound. reflexivity.
      unfold eval_type_bound,eval_bound. reflexivity.
      assumption.
       assert (l < l0).
       specialize (Z.leb_le l0 l) as eq4.
       apply not_iff_compat in eq4.
       assert((l0 <=? l) <> true).
       apply not_true_iff_false. assumption.
       apply eq4 in H4. lia.
      apply (step_implies_reduces D F H st (EDynCast (TPtr Checked (TNTArray (Num l) (Num h) t))
            (ELit n (TPtr Checked (TNTArray (Num l0) (Num h0) t')))) H st RBounds).
      apply (SCastNTArrayLowOOB1 D F st H (TPtr Checked (TNTArray (Num l) (Num h) t)) n (TPtr Checked (TNTArray (Num l0) (Num h0) t'))
                  l h t l0 h0 t').
      unfold eval_type_bound,eval_bound. reflexivity.
      unfold eval_type_bound,eval_bound. reflexivity.
      assumption.
    (* Case: `e` reduces *)
    + (* `ECast t e` can take a step by reducing `e` *)
      left.
      ctx (EDynCast (TPtr Checked (TNTArray x y t)) e) (in_hole e (CDynCast (TPtr Checked (TNTArray x y t)) CHole))...
    (* Case: `e` is unchecked *)
    + (* `ECast t e` must be unchecked, since `e` is *)
      right.
      ctx (EDynCast (TPtr Checked (TNTArray x y t)) e) (in_hole e (CDynCast (TPtr Checked (TNTArray x y t)) CHole)).
      destruct HUnchk...
  (* Case: TyDeref *)
  - (* `EDeref e` isn't a value *)
    right.

    (* If m' is unchecked, then the typing mode `m` is unchecked *)
    destruct m'; [> | right; eauto 20 with Progress].
    clear HMode.

    (* TODO(ins): find a way to automate everything after case analysis... *)
    inv Hewf. apply IH in H1. 2 : { easy. }
    (* Invoke the IH on `e` *)
    destruct H1 as [ HVal | [ HRed | HUnchk ] ].
    (* Case: `e` is a value *)
     (* We can take a step... but how? *)

     + inv HVal.
      inv HTy.
      (* We proceed by case analysis on `w`, the type of the pointer *)
      destruct HPtrType.
      (* Case: `w` is a word pointer *)
      * (* We now proceed by case analysis on 'n > 0' *)
        destruct (Z_gt_dec n 0) as [ Hn0eq0 | Hn0neq0 ].
        (* Case: n > 0 *)
        { (*Since w is subtype of a ptr it is also a ptr*)
          assert (H3 : exists t1, t = (TPtr Checked t1)).
          { eapply ptr_subtype_equiv. eauto.
          } destruct H3. rewrite H3 in *.
          clear H3.
          (* We now proceed by case analysis on '|- n0 : ptr_C w' *)
          inversion H8.
          inv H4. inv H3. inv H3. 
          (* Case: TyLitZero *)
          {
           (* Impossible, since n > 0 *)
           exfalso. lia.
            (*subst. inv H2. inv H3.*)
          }
          (* Case: TyLitRec *)
          { (* Impossible, since scope is empty *)
            solve_empty_scope. }
          (* Case: TyLitC *)
          { (* We can step according to SDeref *)
            destruct H11 with (k := 0) as [ n' [ t1' [ Ht'tk [ Hheap Hwtn' ] ] ] ].
            inv H2; subst. inv H4; inv HSub; inv H3; inv H4; unfold allocate_meta in *; inv H10; simpl; (try lia).
            inv H16. inv H9. inv H12. inv H13. inv H15.
            assert (1 <= h1 - l1) by lia.
            inv H3.
            rewrite replicate_gt_eq. lia. lia.
            inv H16. inv H9. inv H12. inv H13. inv H15.
            assert (1 <= h1 - l1) by lia.
            inv H3.
            rewrite replicate_gt_eq. lia. lia.
            destruct (StructDef.find T D) eqn:HFind.
            assert (Hmap : StructDef.MapsTo T f D). 
            {
             eapply find_implies_mapsto. assumption.
            }
            assert ( Z.of_nat (length (map snd (Fields.elements (elt:=type) f))) > 0). 
            {
              eapply struct_subtype_non_empty; eauto.
              apply (SubTyStructArrayField_1 D T fs m).
              assumption.
              assumption.
            }
            inv H3; zify; (try lia).
            inv H3.
            inv H16. inv H9. inv H12. inv H13. inv H15.
            assert (1 <= h1 - l1) by lia.
            inv H3.
            rewrite replicate_gt_eq. lia. lia.
            inv H16. inv H9. inv H12. inv H13. inv H15.
            assert (1 <= h1 - l1) by lia.
            inv H3.
            rewrite replicate_gt_eq. lia. lia.

            rewrite Z.add_0_r in Hheap;
            inv Ht'tk.
            left.
            eapply step_implies_reduces.
            eapply SDeref; eauto.
            - destruct H2. inv w0. inv HSub.
              unfold eval_type_bound,eval_bound.
              reflexivity.
              inv H12. inv H13. 
              unfold eval_type_bound,eval_bound. reflexivity.
              inv H12. inv H13.
              unfold eval_type_bound,eval_bound. reflexivity.
              unfold eval_type_bound,eval_bound. reflexivity.
              inv HSub.
              unfold eval_type_bound,eval_bound. reflexivity.
              inv H12. inv H13.
              unfold eval_type_bound,eval_bound. reflexivity.
              inv H12. inv H13.
              unfold eval_type_bound,eval_bound. reflexivity.
            - intros. inv H4. inv HSub.
              destruct H2. inv H2.
              destruct H2. inv H2.
              inv H15. inv H16. split. lia. easy.
              destruct H2. inv H2.
            - intros. inv H4. inv HSub.
              destruct H2. inv H2.
              destruct H2. inv H2.
              destruct H2. inv H2.
              inv H15. inv H16. split. lia. easy.
              inv H15. inv H16. split. lia. easy.
              destruct H2. inv H2.
              destruct H2. inv H2.
          }
        }
        (* Case: n <= 0 *)
        { (* We can step according to SDerefNull *)
          left. eapply step_implies_reduces.
         
          assert (exists w0, t = TPtr Checked w0).
          {
            inv H0. inv HSub.
            exists w. destruct m0.
            reflexivity. inv HSub.
          }
          destruct H3. subst.
          eapply SDerefNull; eauto. 
        }

      (* Case: `w` is an array pointer *)
      * destruct H2.
        destruct H2 as [Ht H2].
        subst.

        assert (HArr : (exists l0 h0, t = (TPtr Checked (TArray l0 h0 t')))
                     \/ (exists l0 h0, t = (TPtr Checked (TNTArray l0 h0 t')))
                        \/ (t = TPtr Checked t')
                           \/ (exists T, (t = TPtr Checked (TStruct T)))).
        {
          inv HSub.
          left. exists l; exists h; reflexivity.
          right. right. left. easy. inv H5.
          inv H5.
          left. exists l0; exists h0; reflexivity.
          right. left. exists l0; exists h0; reflexivity.
          right. right. right. exists T. easy.
        }

        destruct HArr.
        destruct H3 as [l1 [h1 HArr]].
        subst.
        (* We now perform case analysis on 'n > 0' *)
        destruct (Z_gt_dec n 0) as [ Hn0eq0 | Hn0neq0 ].
        (* Case: n > 0 *)
        { (* We now proceed by case analysis on '|- n0 : ptr_C (array n t)' *)
          inv H8. inv H3. inv H9.
          match goal with
          | [ H : well_typed_lit _ _ _ _ _ |- _ ] => inv H
          end.
          (* Case: TyLitZero *)
          { (* Impossible, since n0 <> 0 *)
            exfalso. inv Hn0eq0.
          } 
          (* Case: TyLitRec *)
          { (* Impossible, since scope is empty *)
            solve_empty_scope.
          } 
          (* Case: TyLitC *)
          { (* We proceed by case analysis on 'h > 0' -- the size of the array *)
            destruct H2 as [Hyp2 Hyp3]; subst.
            apply (well_typed_means_simple (TPtr Checked (TArray l1 h1 t'))) in H6.
            inv H6. inv H3. inv H8. inv H11.
            (* should this also be on ' h > 0' instead? DP*)
            destruct (Z_gt_dec h0 0) as [ Hneq0 | Hnneq0 ].
            (* Case: h > 0 *)
            { left. (* We can step according to SDeref *)
              (* LEO: This looks exactly like the previous one. Abstract ? *)
              inv H5.
              specialize (simple_type_means_cast_same st t' H4) as eq1.
              apply (cast_type_bound_same st t' t' t'0) in eq1. subst.
              destruct (Z_gt_dec l0 0).

              (* if l > 0 we have a bounds error*)
              {
                eapply step_implies_reduces. 
                apply (SDerefLowOOB D F st H n (TPtr Checked (TArray (Num l0) (Num h0) t'0))
                           (TPtr Checked (TArray (Num l0) (Num h0) t'0)) l0). eapply g.
                unfold eval_type_bound. eauto.
                unfold get_low_ptr. easy.
              }
              
              (* if l <= 0 we can step according to SDeref. *)

              assert (Hhl : h0 - l0 > 0). {
                destruct h0. inv Hneq0. lia. inv Hneq0.
              }
              destruct (h0 - l0) as [| p | ?] eqn:Hp; zify; [lia | |lia].
              simpl in *.
              rewrite replicate_length in *.
              assert (HL: l0 + Z.of_nat (Pos.to_nat p) = h0) by (zify; lia).
              rewrite HL in *; try lia.

              destruct H10 with (k := 0) as [ n' [ t'' [ Ht'tk [ Hheap Hwtn' ] ] ] ].
              { (split;  lia). }

              rewrite Z.add_0_r in Hheap.
              simpl in *.

              assert (Hp': Z.of_nat (Pos.to_nat p) = Z.pos p) by lia.
              rewrite Hp' in *; clear Hp'.
              assert (Hp': Pos.to_nat p = Z.to_nat (Z.pos p)) by (simpl; reflexivity).
              rewrite Hp' in *; clear Hp'. 

              assert (t'0 = t'').
              {
                eapply replicate_nth; eauto.
              }
              subst t''.
              eapply step_implies_reduces.
              apply (SDeref D F st H n n' t'0 (TPtr Checked (TArray (Num l0) (Num h0) t'0))
                          (TPtr Checked (TArray (Num l0) (Num h0) t'0))); eauto.
              - intros l' h' t'' HT.
                injection HT; intros ? ? ?; subst h0 l0 t'0.
                split; zify; lia.
              - intros. inv H2.
              - assumption.
            }
            (* Case: h <= 0 *)
            { (* We can step according to SDerefOOB *)
              subst. left. eapply step_implies_reduces. 
              eapply (SDerefHighOOB D F st H n (TPtr Checked (TArray (Num l0) (Num h0) t'))
                           (TPtr Checked (TArray (Num l0) (Num h0) t')) h0). eauto.
              unfold eval_type_bound; eauto. unfold get_high_ptr. reflexivity.
            } 
          }
        } 
        (* Case: n <= 0 *)
        { (* We can step according to SDerefNull *)
          subst... }

        (* when subtype is nt-array ptr. *)
        destruct H3.
        destruct H3 as [l1 [h1 HArr]].
        subst.
        (* We now perform case analysis on 'n > 0' *)
        destruct (Z_gt_dec n 0) as [ Hn0eq0 | Hn0neq0 ].
        (* Case: n > 0 *)
        { (* We now proceed by case analysis on '|- n0 : ptr_C (array n t)' *)
          inv H8. inv H3. inv H9.
          match goal with
          | [ H : well_typed_lit _ _ _ _ _ |- _ ] => inv H
          end.
          (* Case: TyLitZero *)
          { (* Impossible, since n0 <> 0 *)
            exfalso. inv Hn0eq0.
          } 
          (* Case: TyLitRec *)
          { (* Impossible, since scope is empty *)
            solve_empty_scope.
          } 
          (* Case: TyLitC *)
          { (* We proceed by case analysis on 'h > 0' -- the size of the array *)
            destruct H2 as [Hyp2 Hyp3]; subst.
            apply (well_typed_means_simple (TPtr Checked (TNTArray l1 h1 t'))) in H6.
            inv H6. inv H3. inv H8. inv H11.
            (* should this also be on ' h > 0' instead? DP*)
            destruct (Z_gt_dec h0 0) as [ Hneq0 | Hnneq0 ].
            (* Case: h > 0 *)
            { left. (* We can step according to SDeref *)
              (* LEO: This looks exactly like the previous one. Abstract ? *)
              inv H5.
              specialize (simple_type_means_cast_same st t' H4) as eq1.
              apply (cast_type_bound_same st t' t' t'0) in eq1. subst.
              destruct (Z_gt_dec l0 0).

              (* if l > 0 we have a bounds error*)
              {
                eapply step_implies_reduces. 
                apply (SDerefLowOOB D F st H n (TPtr Checked (TNTArray (Num l0) (Num h0) t'0))
                           (TPtr Checked (TNTArray (Num l0) (Num h0) t'0)) l0). eapply g.
                unfold eval_type_bound. eauto.
                unfold get_low_ptr. easy.
              }
              
              (* if l <= 0 we can step according to SDeref. *)

              assert (Hhl : h0 - l0 + 1 > 0). {
                destruct h0. inv Hneq0. lia. inv Hneq0.
              }
              destruct (h0 - l0 + 1) as [| p | ?] eqn:Hp; zify; [lia | |lia].
              simpl in *.
              rewrite replicate_length in *.
              assert (HL: l0 + Z.of_nat (Pos.to_nat p) = h0 + 1) by (zify; lia).
              rewrite HL in *; try lia.

              destruct H10 with (k := 0) as [ n' [ t'' [ Ht'tk [ Hheap Hwtn' ] ] ] ].
              { (split;  lia). }

              rewrite Z.add_0_r in Hheap.
              simpl in *.

              assert (Hp': Z.of_nat (Pos.to_nat p) = Z.pos p) by lia.
              rewrite Hp' in *; clear Hp'.
              assert (Hp': Pos.to_nat p = Z.to_nat (Z.pos p)) by (simpl; reflexivity).
              rewrite Hp' in *; clear Hp'. 

              assert (t'0 = t'').
              {
                eapply replicate_nth; eauto.
              }
              subst t''.
              eapply step_implies_reduces.
              apply (SDeref D F st H n n' t'0 (TPtr Checked (TNTArray (Num l0) (Num h0) t'0))
                          (TPtr Checked (TNTArray (Num l0) (Num h0) t'0))); eauto.
              - intros. inv H2.
              - intros l' h' t'' HT.
                injection HT; intros ? ? ?; subst h0 l0 t'0.
                split; zify; lia.
              - assumption.
            }
            (* Case: h <= 0 *)
            { (* We can step according to SDerefOOB *)
              subst. left. eapply step_implies_reduces. 
              eapply (SDerefHighOOB D F st H n (TPtr Checked (TNTArray (Num l0) (Num h0) t'))
                           (TPtr Checked (TNTArray (Num l0) (Num h0) t')) h0). eauto.
              unfold eval_type_bound; eauto. unfold get_high_ptr. reflexivity.
            } 
          }
        } 
        (* Case: n <= 0 *)
        { (* We can step according to SDerefNull *)
          subst... }

        destruct H3.
        destruct H2 as [Ht H2].
        subst.

        destruct (Z_gt_dec n 0) as [ Hn0eq0 | Hn0neq0 ].
        (* Case: n > 0 *)
        { (*Since w is subtype of a ptr it is also a ptr*)
          (* We now proceed by case analysis on '|- n0 : ptr_C w' *)
          inversion H8.
          inv H4. inv H3. inv H3. 
          (* Case: TyLitZero *)
          {
           (* Impossible, since n > 0 *)
           exfalso. lia.
            (*subst. inv H2. inv H3.*)
          }
          (* Case: TyLitRec *)
          { (* Impossible, since scope is empty *)
            solve_empty_scope. }
          (* Case: TyLitC *)
          { (* We can step according to SDeref *)
            destruct H11 with (k := 0) as [ n' [ t1' [ Ht'tk [ Hheap Hwtn' ] ] ] ].
            inv H3. specialize (cast_word_type st t' w H5 Ht) as eq1.
            unfold allocate_meta in *. destruct w.
            inv H10. simpl. lia. inv H10. simpl. lia.
            inv eq1. inv eq1. inv eq1.

            rewrite Z.add_0_r in Hheap;
            inv Ht'tk.
            left.
            eapply step_implies_reduces.
            eapply SDeref; eauto.
            - unfold eval_type_bound,eval_bound.
              destruct t'.
              reflexivity. reflexivity.
              inv Ht. inv Ht. inv Ht.
            - intros. inv H4. inv Ht.
            - intros. inv H4. inv Ht.
          }
        }
        (* Case: n <= 0 *)
        { (* We can step according to SDerefNull *)
          left. eapply step_implies_reduces.
         
          eapply SDerefNull; eauto. 
        }

       (* when subtype is a TStruct pointer. *)
        destruct H3.
        destruct H2 as [Ht H2].
        subst.
        inv HSub. inv Ht.        

        destruct (Z_gt_dec n 0) as [ Hn0eq0 | Hn0neq0 ].
        (* Case: n > 0 *)
        { (*Since w is subtype of a ptr it is also a ptr*)
          (* We now proceed by case analysis on '|- n0 : ptr_C w' *)
          inversion H8.
          inv H4. inv H3. inv H3. 
          (* Case: TyLitZero *)
          {
           (* Impossible, since n > 0 *)
           exfalso. lia.
            (*subst. inv H2. inv H3.*)
          }
          (* Case: TyLitRec *)
          { (* Impossible, since scope is empty *)
            solve_empty_scope. }
          (* Case: TyLitC *)
          { (* We can step according to SDeref *)
            destruct H15 with (k := 0) as [ n' [ t1' [ Ht'tk [ Hheap Hwtn' ] ] ] ].
            inv H3.
            unfold allocate_meta in *. inv H5. inv H12. inv H13.
            destruct (StructDef.find x D) eqn:HFind.
            assert (Hmap : StructDef.MapsTo x f D). 
            {
             eapply find_implies_mapsto. assumption.
            }
            assert ( Z.of_nat (length (map snd (Fields.elements (elt:=type) f))) > 0). 
            {
              eapply struct_subtype_non_empty; eauto.
              apply (SubTyStructArrayField_1 D x fs m).
              assumption.
              assumption.
            }
            inv H14; zify; try lia.
            inv H14.

            rewrite Z.add_0_r in Hheap;
            inv Ht'tk.
            left.
            eapply step_implies_reduces.
            eapply SDeref; eauto.
            - unfold eval_type_bound,eval_bound. reflexivity.
            - intros. inv H4.
            - intros. inv H4.
          }
        }
        (* Case: n <= 0 *)
        { (* We can step according to SDerefNull *)
          left. eapply step_implies_reduces.
         
          eapply SDerefNull; eauto. 
        }

        (* when t'' is a TNTArray. *)
        destruct H2 as [Ht H2]. subst.
        assert (HArr : (exists l0 h0, t = (TPtr Checked (TNTArray l0 h0 t')))).
        {
          inv HSub.
          exists l; exists h; easy.
          inv H5. inv H5.
          exists l0; exists h0; reflexivity.
        }

        destruct HArr as [l1 [h1 HArr]].
        rewrite HArr in *. clear HArr.
        (* We now perform case analysis on 'n > 0' *)
        destruct (Z_gt_dec n 0) as [ Hn0eq0 | Hn0neq0 ].
        (* Case: n > 0 *)
        { (* We now proceed by case analysis on '|- n0 : ptr_C (array n t)' *)
          inv H8. inv H3. inv H9.
          match goal with
          | [ H : well_typed_lit _ _ _ _ _ |- _ ] => inv H
          end.
          (* Case: TyLitZero *)
          { (* Impossible, since n0 <> 0 *)
            exfalso. inv Hn0eq0.
          } 
          (* Case: TyLitRec *)
          { (* Impossible, since scope is empty *)
            solve_empty_scope.
          } 
          (* Case: TyLitC *)
          { (* We proceed by case analysis on 'h > 0' -- the size of the array *)
            destruct H2 as [Hyp2 Hyp3]; subst.
            apply (well_typed_means_simple (TPtr Checked (TNTArray l1 h1 t'))) in H6.
            inv H6. inv H3.
            (* should this also be on ' h > 0' instead? DP*)
            destruct (Z_gt_dec h0 0) as [ Hneq0 | Hnneq0 ].
            (* Case: h > 0 *)
            { left. (* We can step according to SDeref *)
              (* LEO: This looks exactly like the previous one. Abstract ? *)
              destruct (Z_gt_dec l0 0).

              (* if l > 0 we have a bounds error*)
              {
                eapply step_implies_reduces. 
                eapply (SDerefLowOOB D F st H n (TPtr Checked (TNTArray (Num l0) (Num h0) t'))
                           (TPtr Checked (TNTArray (Num l0) (Num h0) t')) l0). eapply g.
                unfold eval_type_bound. eauto.
                unfold get_low_ptr.
                reflexivity.
              }
              
              (* if l <= 0 we can step according to SDeref. *)
              inv H8. inv H11. inv H5.
              assert (Hhl : (h0 - l0 + 1) > 0). {
                destruct h0. inv Hneq0. lia. inv Hneq0.
              }

              destruct (h0 - l0 + 1) as [| p | ?] eqn:Hp; zify; [lia | |lia].
              simpl in *.
              rewrite replicate_length in *.
              assert (HL: l0 + Z.of_nat (Pos.to_nat p) = h0+1) by (zify; lia).
              rewrite HL in *; try lia.

              destruct H10 with (k := 0) as [ n' [ t'' [ Ht'tk [ Hheap Hwtn' ] ] ] ].
              { (split;  lia). }

              rewrite Z.add_0_r in Hheap.
              simpl in *.

              assert (Hp': Z.of_nat (Pos.to_nat p) = Z.pos p) by lia.
              rewrite Hp' in *; clear Hp'.
              assert (Hp': Pos.to_nat p = Z.to_nat (Z.pos p)) by (simpl; reflexivity).
              rewrite Hp' in *; clear Hp'. 

              assert (t'0 = t'').
              {
                eapply replicate_nth; eauto.
              }
              subst t''.
              apply (simple_type_means_cast_same st) in H4.
              apply (cast_type_bound_same st t' t' t'0) in H4. rewrite H4 in *.
              eapply step_implies_reduces.
              apply (SDeref D F st H n n' t'0 (TPtr Checked (TNTArray (Num l0) (Num h0) t'0))
                          (TPtr Checked (TNTArray (Num l0) (Num h0) t'0))); eauto.
              - intros. inv H2.
              - intros l' h' t'' HT.
                injection HT. intros. subst.
                split; zify; lia.
              - assumption.
            }
            (* Case: h <= 0 *)
            { (* We can step according to SDerefOOB *)
              subst. left. eapply step_implies_reduces. 
              eapply (SDerefHighOOB D F st H n (TPtr Checked (TNTArray (Num l0) (Num h0) t'))
                           (TPtr Checked (TNTArray (Num l0) (Num h0) t')) h0). eauto.
              unfold eval_type_bound; eauto. unfold get_high_ptr. reflexivity.
            } 
          }
        } 
        (* Case: n <= 0 *)
        { (* We can step according to SDerefNull *)
          subst... }

     + left. ctx (EDeref e) (in_hole e (CDeref CHole))...
     + right.
       ctx (EDeref e) (in_hole e (CDeref CHole)).
       destruct HUnchk...
  - (* Index for array type. *)
    right.
    destruct m'; [> | right; eauto 20 with Progress].
    clear HMode.
    (* Leo: This is becoming hacky *)
    inv Hewf. inv H1.
    (*
    assert (exists l0 h0, t = (TPtr Checked (TArray l0 h0 t'))).
    {
      inv HSubType. exists l; exists h; eauto.
      exists l0; exists h0; eauto.
    }
    destruct H0 as [l0 [h0 H0]].
    rewrite H0 in *.
    clear HSubType H0 l h.
    remember l0 as l. remember h0 as h.
    clear Heql Heqh l0 h0 t.
    remember t' as t. clear Heqt t'.
    *)
    specialize (IH1 H3 eq_refl).
    specialize (IH2 H4 eq_refl).
    destruct IH1 as [ HVal1 | [ HRed1 | HUnchk1 ] ]; eauto.
    + inv HVal1 as [ n1 t1 ].
      destruct IH2 as [ HVal2 | [ HRed2 | HUnchk2 ] ]; eauto.
      * left.
        inv HVal2.
        ctx (EDeref (EPlus (ELit n1 t1) (ELit n t))) (in_hole (EPlus (ELit n1 t1) (ELit n t)) (CDeref CHole)).
        inv HTy1.
        specialize (well_typed_means_simple (TPtr Checked (TArray l h t')) H10) as eq1.
        inv eq1. inv H7.
        exists Checked.
        exists st.
        exists H.
        { destruct (Z_gt_dec n1 0).
          - (* n1 > 0 *)
            exists (RExpr (EDeref (ELit (n1 + n) (TPtr Checked (TArray (Num (l0 - n)) (Num (h0 - n)) t'))))).
            ctx (EDeref (ELit (n1 + n) (TPtr Checked (TArray (Num (l0 - n)) (Num (h0 - n)) t'))))
                (in_hole (ELit (n1 + n) (TPtr Checked (TArray (Num (l0 - n)) (Num (h0 - n)) t'))) (CDeref CHole)).
            rewrite HCtx.
            rewrite HCtx0.
            inv HTy2.
            eapply RSExp; eauto.
            assert ((TPtr Checked (TArray (Num (l0 - n)) (Num (h0 - n)) t')) 
             = sub_type_bound (TPtr Checked (TArray (Num l0) (Num h0) t')) n).
            unfold sub_type_bound,sub_bound. reflexivity.
            rewrite H6.
            apply SPlusChecked. assumption.
            unfold is_array_ptr. easy.
            apply cast_type_bound_ptr.
            apply cast_type_bound_array.
            unfold cast_bound. reflexivity.
            unfold cast_bound. reflexivity.
            apply simple_type_means_cast_same. assumption.
          - (* n1 <= 0 *)
            exists RNull.
            subst. 
            rewrite HCtx. 
            inv HTy2.
            eapply RSHaltNull; eauto.
            apply SPlusNull. lia.
            unfold is_array_ptr. easy.
        }
      * left.
        ctx (EDeref (EPlus (ELit n1 t1) e2)) (in_hole e2 (CDeref (CPlusR n1 t1 CHole)))...
      * right.
        ctx (EDeref (EPlus (ELit n1 t1) e2)) (in_hole e2 (CDeref (CPlusR n1 t1 CHole))).
        destruct HUnchk2...
    + left.
      ctx (EDeref (EPlus e1 e2)) (in_hole e1 (CDeref (CPlusL CHole e2)))...
    + right.
      ctx (EDeref (EPlus e1 e2)) (in_hole e1 (CDeref (CPlusL CHole e2))).
      destruct HUnchk1...

  - (* Index for ntarray type. *)
    right.
    destruct m'; [> | right; eauto 20 with Progress].
    clear HMode.
    (* Leo: This is becoming hacky *)
    inv Hewf.
    inv H1.
    (*
    assert (exists l0 h0, t = (TPtr Checked (TArray l0 h0 t'))).
    {
      inv HSubType. exists l; exists h; eauto.
      exists l0; exists h0; eauto.
    }
    destruct H0 as [l0 [h0 H0]].
    rewrite H0 in *.
    clear HSubType H0 l h.
    remember l0 as l. remember h0 as h.
    clear Heql Heqh l0 h0 t.
    remember t' as t. clear Heqt t'.
    *)
    specialize (IH1 H3 eq_refl).
    specialize (IH2 H4 eq_refl).
    destruct IH1 as [ HVal1 | [ HRed1 | HUnchk1 ] ]; eauto.
    + inv HVal1 as [ n1 t1 ].
      destruct IH2 as [ HVal2 | [ HRed2 | HUnchk2 ] ]; eauto.
      * left.
        inv HVal2.
        ctx (EDeref (EPlus (ELit n1 t1) (ELit n t))) (in_hole (EPlus (ELit n1 t1) (ELit n t)) (CDeref CHole)).
        inv HTy1.
        specialize (well_typed_means_simple (TPtr Checked (TNTArray l h t')) H10) as eq1.
        inv eq1. inv H7.
        exists Checked.
        exists st.
        exists H.
        { destruct (Z_gt_dec n1 0).
          - (* n1 > 0 *)
            exists (RExpr (EDeref (ELit (n1 + n) (TPtr Checked (TNTArray (Num (l0 - n)) (Num (h0 - n)) t'))))).
            ctx (EDeref (ELit (n1 + n) (TPtr Checked (TNTArray (Num (l0 - n)) (Num (h0 - n)) t'))))
                (in_hole (ELit (n1 + n) (TPtr Checked (TNTArray (Num (l0 - n)) (Num (h0 - n)) t'))) (CDeref CHole)).
            rewrite HCtx.
            rewrite HCtx0.
            inv HTy2.
            eapply RSExp; eauto.
            assert ((TPtr Checked (TNTArray (Num (l0 - n)) (Num (h0 - n)) t')) 
             = sub_type_bound (TPtr Checked (TNTArray (Num l0) (Num h0) t')) n).
            unfold sub_type_bound,sub_bound. reflexivity.
            rewrite H6.
            apply SPlusChecked. assumption.
            unfold is_array_ptr. easy.
            apply cast_type_bound_ptr.
            apply cast_type_bound_ntarray.
            unfold cast_bound. reflexivity.
            unfold cast_bound. reflexivity.
            apply simple_type_means_cast_same. assumption.
          - (* n1 <= 0 *)
            exists RNull.
            subst. 
            rewrite HCtx. 
            inv HTy2.
            eapply RSHaltNull; eauto.
            apply SPlusNull. lia.
            unfold is_array_ptr. easy.
        }
      * left.
        ctx (EDeref (EPlus (ELit n1 t1) e2)) (in_hole e2 (CDeref (CPlusR n1 t1 CHole)))...
      * right.
        ctx (EDeref (EPlus (ELit n1 t1) e2)) (in_hole e2 (CDeref (CPlusR n1 t1 CHole))).
        destruct HUnchk2...
    + left.
      ctx (EDeref (EPlus e1 e2)) (in_hole e1 (CDeref (CPlusL CHole e2)))...
    + right.
      ctx (EDeref (EPlus e1 e2)) (in_hole e1 (CDeref (CPlusL CHole e2))).
      destruct HUnchk1...

  - (* Assign1 rule. This isn't a value, so it must reduce *)
    right.

    (* If m' is unchecked, then we are typing mode is unchecked *)
    destruct m'; [> | right; eauto 20 with Progress].
    clear HMode.

    (* Invoke IH on e1 *)
    inv Hewf. apply IH1 in H2. 2 : { easy. }
    destruct H2 as [ HVal1 | [ HRed1 | [| HUnchk1 ] ] ]; idtac...
    + (* Case: e1 is a value *)
      inv HVal1 as [ n1' t1' WTt1' Ht1' ].
      (* Invoke IH on e2 *)
      apply IH2 in H3. 2 : { easy. }
      inv H3 as [ HVal2 | [ HRed2 | [| HUnchk2 ] ] ]; idtac...
      * (* Case: e2 is a value, so we can take a step *)
        inv HVal2 as [n2' t2' Wtt2' Ht2' ].
        {
            inv HTy1; eauto.
            inv H6.
            match goal with
            | [ H : well_typed_lit _ _ _ _ _ |- _ ] => inv H
            end... 
            + exfalso; inv H0; inv HSubType.
            + exfalso; inv H0; inv HSubType.
            + left.
              eapply step_implies_reduces.
              eapply SAssignNull; eauto. lia.
              apply (well_typed_means_simple) in H4.
              apply eval_simple_type_same. assumption.
            + solve_empty_scope.
            + left. unfold allocate_meta in H2.
              destruct w; inv H2; simpl in *. inv H0. inv H2.
              ++   destruct (H3 0) as [x [xT [HNth [HMap HWT]]]]; simpl in*;
                try (zify; lia);
                try rewrite Z.add_0_r in *;
                eauto; 
              try (eapply step_implies_reduces;
                   eapply SAssign; eauto);
              try (eexists; eauto);
              intros; try congruence...
              constructor. constructor. inv H0. inv H0. inv H0. inv H0.
              apply get_root_word. constructor.
              ++ inv H0. inv H2.
                 destruct (H3 0) as [x [xT [HNth [HMap HWT]]]]; simpl in*;
                try (zify; lia);
                try rewrite Z.add_0_r in *;
                eauto; 
              try (eapply step_implies_reduces;
                   eapply SAssign; eauto);
              try (eexists; eauto);
              intros; try congruence...
              constructor. constructor. apply H5. inv H0. inv H0. inv H0. inv H0.
              apply get_root_word. constructor.
              ++ destruct (StructDef.find (elt:=fields) s D)eqn:Hmap; inv H5.
                 inv H0. inv H2. inv WT.
              ++ inv H0.  inv H2. inv WT.
              ++ inv H0.  inv H2. inv WT.
         }
      * unfold reduces in HRed2. destruct HRed2 as [ H' [ ? [ ? [ r HRed2 ] ] ] ].
        inv HRed2; ctx (EAssign (ELit n1' t1') (in_hole e E)) (in_hole e (CAssignR n1' t1' E))...
      * destruct HUnchk2 as [ e' [ E [ ] ] ]; subst.
        ctx (EAssign (ELit n1' t1') (in_hole e' E)) (in_hole e' (CAssignR n1' t1' E))...
    + (* Case: e1 reduces *)
      destruct HRed1 as [ H' [ ? [? [ r HRed1 ] ] ] ].
      inv HRed1; ctx (EAssign (in_hole e E) e2) (in_hole e (CAssignL E e2))...
    + destruct HUnchk1 as [ e' [ E [ ] ] ]; subst.
      ctx (EAssign (in_hole e' E) e2) (in_hole e' (CAssignL E e2))...
  - (* Assign2 rule for array. *)
    right.

    (* If m' is unchecked, then we are typing mode is unchecked *)
    destruct m'; [> | right; eauto 20 with Progress].
    clear HMode.

    (* Invoke IH on e1 *)
    inv Hewf. apply IH1 in H2. 2 : { easy. }
    destruct H2 as [ HVal1 | [ HRed1 | [| HUnchk1 ] ] ]; idtac...
    + (* Case: e1 is a value *)
      inv HVal1 as [ n1' t1' WTt1' Ht1' ].
      (* Invoke IH on e2 *)
      apply IH2 in H3. 2 : { easy. }
      inv H3 as [ HVal2 | [ HRed2 | [| HUnchk2 ] ] ]; idtac...
      * (* Case: e2 is a value, so we can take a step *)
        inv HVal2 as [n2' t2' Wtt2' Ht2' ].
        {
            inv HTy1; eauto.
            inv H6.
            match goal with
            | [ H : well_typed_lit _ _ _ _ _ |- _ ] => inv H
            end...
            + exfalso; inv H0.
            + exfalso; inv H0.
            + left.
              specialize (well_typed_means_simple (TPtr Checked (TArray l h t)) H4) as eq1.
              inv eq1. inv H2.

              destruct (Z_gt_dec h0 0).
              * (* h > 0 - Assign  *)
                destruct (Z_gt_dec l0 0).
                { (* l > 0 *)
                eapply step_implies_reduces.
                eapply SAssignLowOOB; eauto... inv HTy2.
                unfold eval_type_bound,eval_bound. reflexivity.
                unfold get_low_ptr. easy.
                }
                { (* l <= 0 *)
                  eapply step_implies_reduces.
                  eapply SAssignNull; eauto. lia.
                  unfold eval_type_bound,eval_bound. eauto. 
                }
              * (* h <= 0 *)
                eapply step_implies_reduces.
                eapply SAssignHighOOB; eauto... 
                unfold eval_type_bound, eval_bound. reflexivity.
                unfold get_high_ptr. easy.
            + solve_empty_scope.
            + left.
              specialize (well_typed_means_simple (TPtr Checked (TArray l h t)) H4) as eq1.
              inv eq1. inv H5.

              destruct (Z_gt_dec n1' 0).
                ++ destruct (Z_gt_dec h0 0).
                    * (* h > 0 - Assign  *)
                      destruct (Z_gt_dec l0 0).
                      { (* l > 0 *)
                      eapply step_implies_reduces.
                      eapply SAssignLowOOB; eauto... 
                      unfold eval_type_bound, eval_bound. reflexivity.
                      unfold get_low_ptr. easy. }
                      { (* l <= 0 *)
                        inv H0. inv H5.
                        eapply step_implies_reduces.
                        eapply (SAssign); eauto.
                        apply (simple_type_means_cast_same st) in H6.
                        apply (cast_type_bound_same st t t t'0) in H6.
                        inv H8. inv H10.
                        destruct (H3 0). unfold allocate_meta in H2.
                        inv H2. 
                        assert (Hmin : h0 - l0 > 0) by lia.
                        assert (Hpos : exists p, h0 - l0 = Z.pos p).
                        {
                          destruct (h0 - l0); inv Hmin.
                          exists p; eauto.
                        }
                        destruct Hpos as [p Hpos].
                        rewrite Hpos. simpl.
                        rewrite replicate_length.
                        zify; lia.
                        rewrite Z.add_0_r in H0.
                        destruct H0 as [? [? [? ?]]].
                        assert (Heap.find n1' H = Some (x, x0)) by (eapply Heap.find_1; assumption).
                        eapply HeapProp.F.in_find_iff. 
                        rewrite H6. easy. assumption.
                        constructor. constructor. apply H8. apply H10. apply H11.
                        intros l1 h1 t1 Heq; inv Heq; zify.
                        inv H8. inv H10. lia.
                        intros. inv H0.
                        apply get_root_array.
                      }
                    * (* h <= 0 *)
                      eapply step_implies_reduces.
                      eapply SAssignHighOOB; eauto...
                      unfold eval_type_bound,eval_bound. reflexivity. 
                      unfold get_high_ptr. easy.
              ++ destruct (Z_gt_dec h0 0).
                 * (* h > 0 - Assign  *)
                   destruct (Z_gt_dec l0 0).
                   { (* l > 0 *)
                   eapply step_implies_reduces.
                   eapply SAssignLowOOB; eauto...
                   unfold eval_type_bound,eval_bound. reflexivity. 
                   unfold get_low_ptr. easy. }
                   { (* l <= 0 *)
                     eapply step_implies_reduces.   
                     eapply SAssignNull; eauto.
                     unfold eval_type_bound,eval_bound. eauto.
                   }
                 * (* h <= 0 *)
                   eapply step_implies_reduces.
                   eapply SAssignHighOOB; eauto... inv HTy2.
                   unfold eval_type_bound,eval_bound. reflexivity.
                   unfold get_high_ptr. easy.
         }
      * unfold reduces in HRed2. destruct HRed2 as [ H' [ ? [ ? [ r HRed2 ] ] ] ].
        inv HRed2; ctx (EAssign (ELit n1' t1') (in_hole e E)) (in_hole e (CAssignR n1' t1' E))...
      * destruct HUnchk2 as [ e' [ E [ ] ] ]; subst.
        ctx (EAssign (ELit n1' t1') (in_hole e' E)) (in_hole e' (CAssignR n1' t1' E))...
    + (* Case: e1 reduces *)
      destruct HRed1 as [ H' [ ? [? [ r HRed1 ] ] ] ].
      inv HRed1; ctx (EAssign (in_hole e E) e2) (in_hole e (CAssignL E e2))...
    + destruct HUnchk1 as [ e' [ E [ ] ] ]; subst.
      ctx (EAssign (in_hole e' E) e2) (in_hole e' (CAssignL E e2))...

  - (* Assign3 rule for nt-array. *)
    right.

    (* If m' is unchecked, then we are typing mode is unchecked *)
    destruct m'; [> | right; eauto 20 with Progress].
    clear HMode.

    (* Invoke IH on e1 *)
    inv Hewf. apply IH1 in H2. 2 : { easy. }
    destruct H2 as [ HVal1 | [ HRed1 | [| HUnchk1 ] ] ]; idtac...
    + (* Case: e1 is a value *)
      inv HVal1 as [ n1' t1' WTt1' Ht1' ].
      (* Invoke IH on e2 *)
      apply IH2 in H3. 2 : { easy. }
      inv H3 as [ HVal2 | [ HRed2 | [| HUnchk2 ] ] ]; idtac...
      * (* Case: e2 is a value, so we can take a step *)
        inv HVal2 as [n2' t2' Wtt2' Ht2' ].
        {
            inv HTy1; eauto.
            inv H6.
            match goal with
            | [ H : well_typed_lit _ _ _ _ _ |- _ ] => inv H
            end...
            + exfalso; inv H0.
            + exfalso; inv H0.
            + left.
              specialize (well_typed_means_simple (TPtr Checked (TNTArray l h t)) H4) as eq1.
              inv eq1. inv H2.

              destruct (Z_gt_dec h0 0).
              * (* h > 0 - Assign  *)
                destruct (Z_gt_dec l0 0).
                { (* l > 0 *)
                eapply step_implies_reduces.
                eapply SAssignLowOOB; eauto...
                unfold eval_type_bound,eval_bound. reflexivity. 
                unfold get_low_ptr. easy. }
                { (* l <= 0 *)
                  eapply step_implies_reduces.
                  eapply SAssignNull; eauto. lia.
                  unfold eval_type_bound,eval_bound. eauto. 
                }
              * (* h <= 0 *)
                eapply step_implies_reduces.
                eapply SAssignHighOOB; eauto...                
                unfold eval_type_bound,eval_bound. reflexivity. 
                unfold get_high_ptr. easy. 
            + solve_empty_scope.
            + left.
              specialize (well_typed_means_simple (TPtr Checked (TNTArray l h t)) H4) as eq1.
              inv eq1. inv H5.

              destruct (Z_gt_dec n1' 0).
                ++ destruct (Z_gt_dec h0 0).
                    * (* h > 0 - Assign  *)
                      destruct (Z_gt_dec l0 0).
                      { (* l > 0 *)
                      eapply step_implies_reduces.
                      eapply SAssignLowOOB; eauto...                
                      unfold eval_type_bound,eval_bound. reflexivity. 
                      unfold get_low_ptr. easy. }
                      { (* l <= 0 *)
                        inv H0. inv H5.
                        eapply step_implies_reduces.
                        eapply SAssign; eauto.
                        apply (simple_type_means_cast_same st) in H6.
                        apply (cast_type_bound_same st t t t'0) in H6.
                        inv H8. inv H10.
                        destruct (H3 0). unfold allocate_meta in H2.
                        inv H2. 
                        assert (Hmin : h0 - l0 + 1 > 0) by lia.
                        assert (Hpos : exists p, h0 - l0 + 1 = Z.pos p).
                        {
                          destruct (h0 - l0 + 1); inv Hmin.
                          exists p; eauto.
                        }
                        destruct Hpos as [p Hpos].
                        rewrite Hpos. simpl.
                        rewrite replicate_length.
                        zify; lia.
                        rewrite Z.add_0_r in H0.
                        destruct H0 as [? [? [? ?]]].
                        assert (Heap.find n1' H = Some (x, x0)) by (eapply Heap.find_1; assumption).
                        eapply HeapProp.F.in_find_iff. 
                        rewrite H6. easy. assumption.
                        constructor. constructor. apply H8. apply H10. apply H11.
                        intros l1 h1 t1 Heq; inv Heq; zify; lia.
                        intros l1 h1 t1 Heq; inv Heq; zify.
                        inv H8. inv H10. lia.
                        apply get_root_ntarray.
                      }
                    * (* h <= 0 *)
                      eapply step_implies_reduces.
                      eapply SAssignHighOOB; eauto...
                      unfold eval_type_bound,eval_bound. reflexivity.
                      unfold get_high_ptr. easy.
              ++ destruct (Z_gt_dec h0 0).
                 * (* h > 0 - Assign  *)
                   destruct (Z_gt_dec l0 0).
                   { (* l > 0 *)
                   eapply step_implies_reduces.
                   eapply SAssignLowOOB; eauto...
                   unfold eval_type_bound,eval_bound. reflexivity.
                   unfold get_low_ptr. easy.
                   }
                   { (* l <= 0 *)
                     eapply step_implies_reduces.   
                     eapply SAssignNull; eauto.
                     unfold eval_type_bound,eval_bound. eauto.
                   }
                 * (* h <= 0 *)
                   eapply step_implies_reduces.
                   eapply SAssignHighOOB; eauto...
                   unfold eval_type_bound,eval_bound. reflexivity.
                   unfold get_high_ptr. easy.
         }
      * unfold reduces in HRed2. destruct HRed2 as [ H' [ ? [ ? [ r HRed2 ] ] ] ].
        inv HRed2; ctx (EAssign (ELit n1' t1') (in_hole e E)) (in_hole e (CAssignR n1' t1' E))...
      * destruct HUnchk2 as [ e' [ E [ ] ] ]; subst.
        ctx (EAssign (ELit n1' t1') (in_hole e' E)) (in_hole e' (CAssignR n1' t1' E))...
    + (* Case: e1 reduces *)
      destruct HRed1 as [ H' [ ? [? [ r HRed1 ] ] ] ].
      inv HRed1; ctx (EAssign (in_hole e E) e2) (in_hole e (CAssignL E e2))...
    + destruct HUnchk1 as [ e' [ E [ ] ] ]; subst.
      ctx (EAssign (in_hole e' E) e2) (in_hole e' (CAssignL E e2))...

  (* T-IndAssign for array pointer. *)
  - (* This isn't a value, so it must reduce *)
    right.

    (* If m' is unchecked, then we are typing mode is unchecked *)
    destruct m'; [> | right; eauto 20 with Progress].
    clear HMode.
    inv Hewf. inv H2.
    (*
    assert (exists l0 h0, t = (TPtr Checked (TArray l0 h0 t'))).
    {
      inv HSubType. exists l; exists h; eauto.
      exists l0; exists h0; eauto.
    }
    destruct H0 as [l0 [h0 H0]].
    rewrite H0 in *.
    clear HSubType H0 l h.
    remember l0 as l. remember h0 as h.
    clear Heql Heqh l0 h0 t.
    remember t' as t. clear Heqt t'.
    *)
    (* Invoke IH on e1 *)
    apply IH1 in H4. 2 : { easy. }
    destruct H4 as [ HVal1 | [ HRed1 | [| HUnchk1 ] ] ]; idtac...
    + (* Case: e1 is a value *)
      inv HVal1.
      (* Invoke IH on e2 *)
      apply IH2 in H5. 2 : { easy. }
      destruct H5 as [ HVal2 | [ HRed2 | [| HUnchk2 ] ] ]; idtac...
      * inv HVal2.
        ctx (EAssign (EPlus (ELit n t0) (ELit n0 t1)) e3) 
                  (in_hole (EPlus (ELit n t0) (ELit n0 t1)) (CAssignL CHole e3)).
        inv HTy1.
        inv HTy2.
        specialize (well_typed_means_simple (TPtr Checked (TArray l h t)) H9) as eq1.
        inv eq1. inv H6.
        {
          inv H11. inv H13. inv H5. inv H8. inv H15. inv H13. inv H16.
          apply IH3 in H3. 2 : { easy. }
          inv H6; inv H11; (eauto 20 with Progress); 
            try solve_empty_scope.
          - destruct H3 as [ HVal3 | [ HRed3 | [| HUnchk3]]]; idtac...
            + inv HVal3.
              inv HTy3.
              left; eauto...
              destruct (Z_gt_dec n 0); subst; rewrite HCtx; do 4 eexists.
              * eapply RSHaltNull... eapply SPlusNull. lia.
                unfold is_array_ptr. easy.
              * eapply RSHaltNull... eapply SPlusNull. lia.
                unfold is_array_ptr. easy.
            + destruct HRed3 as [H' [? [r HRed3]]].
              rewrite HCtx; left; do 4 eexists.
              eapply RSHaltNull... eapply SPlusNull. lia. 
                unfold is_array_ptr. easy.
            + destruct HUnchk3 as [ e' [ E [ He2 HEUnchk ]]]; subst.
              rewrite HCtx; left; do 4 eexists.
              eapply RSHaltNull... eapply SPlusNull. lia.
                unfold is_array_ptr. easy.
          - destruct H3 as [ HVal3 | [ HRed3 | [| HUnchk3]]]; idtac...
            + inv HVal3.
              inv HTy3.
              destruct (Z_gt_dec n 0); rewrite HCtx; left; do 4 eexists.
              * eapply RSHaltNull... eapply SPlusNull. lia.
                unfold is_array_ptr. easy.
              * eapply RSHaltNull... eapply SPlusNull. lia.
                unfold is_array_ptr. easy.
            + destruct HRed3 as [H' [? [r HRed3]]].
              rewrite HCtx; left; do 4 eexists.
              eapply RSHaltNull... eapply SPlusNull. lia.
                unfold is_array_ptr. easy.
            + destruct HUnchk3 as [ e' [ E [ He2 HEUnchk ]]]; subst.
              rewrite HCtx; left; do 4 eexists.
              eapply RSHaltNull... eapply SPlusNull. lia.
                unfold is_array_ptr. easy.
          - destruct (Z_gt_dec n 0); rewrite HCtx; left; do 4 eexists.
              * eapply RSExp. eapply SPlusChecked. lia.
                unfold is_array_ptr. easy.
                apply empty_means_cast_type_bound_same. assumption.
                eauto.
              * eapply RSHaltNull. eapply SPlusNull. lia.
                unfold is_array_ptr. easy. eauto.
          -  destruct (Z_gt_dec n 0); rewrite HCtx; left; do 4 eexists.
              * eapply RSExp. eapply SPlusChecked. lia.
                unfold is_array_ptr. easy. 
                apply empty_means_cast_type_bound_same. assumption.
                eauto.
              * eapply RSHaltNull. eapply SPlusNull. lia.
                unfold is_array_ptr. easy. eauto.
        }
      * destruct HRed2 as [ H' [ ? [? [ r HRed2 ] ] ] ].
        inv HRed2; ctx (EAssign (EPlus (ELit n t0) (in_hole e E)) e3) (in_hole e (CAssignL (CPlusR n t0 E) e3))...
      * destruct HUnchk2 as [ e' [ E [ He2 HEUnchk ] ] ]; subst.
        ctx (EAssign (EPlus (ELit n t0) (in_hole e' E)) e3) (in_hole e' (CAssignL (CPlusR n t0 E) e3))...
    + destruct HRed1 as [ H' [? [ ? [ r HRed1 ] ] ] ].
      inv HRed1; ctx (EAssign (EPlus (in_hole e E) e2) e3) (in_hole e (CAssignL (CPlusL E e2) e3))...
    + destruct HUnchk1 as [ e' [ E [ He1 HEUnchk ] ] ]; subst.
      ctx (EAssign (EPlus (in_hole e' E) e2) e3) (in_hole e' (CAssignL (CPlusL E e2) e3))...
  (* T-IndAssign for ntarray pointer. *)
  - (* This isn't a value, so it must reduce *)
    right.

    (* If m' is unchecked, then we are typing mode is unchecked *)
    destruct m'; [> | right; eauto 20 with Progress].
    clear HMode.
    inv Hewf. inv H2.
    (*
    assert (exists l0 h0, t = (TPtr Checked (TArray l0 h0 t'))).
    {
      inv HSubType. exists l; exists h; eauto.
      exists l0; exists h0; eauto.
    }
    destruct H0 as [l0 [h0 H0]].
    rewrite H0 in *.
    clear HSubType H0 l h.
    remember l0 as l. remember h0 as h.
    clear Heql Heqh l0 h0 t.
    remember t' as t. clear Heqt t'.
    *)
    (* Invoke IH on e1 *)
    apply IH1 in H4. 2 : { easy. }
    destruct H4 as [ HVal1 | [ HRed1 | [| HUnchk1 ] ] ]; idtac...
    + (* Case: e1 is a value *)
      inv HVal1.
      (* Invoke IH on e2 *)
      apply IH2 in H5. 2 : { easy. }
      destruct H5 as [ HVal2 | [ HRed2 | [| HUnchk2 ] ] ]; idtac...
      * inv HVal2.
        ctx (EAssign (EPlus (ELit n t0) (ELit n0 t1)) e3) 
                  (in_hole (EPlus (ELit n t0) (ELit n0 t1)) (CAssignL CHole e3)).
        inv HTy1.
        inv HTy2.
        specialize (well_typed_means_simple (TPtr Checked (TNTArray l h t)) H9) as eq1.
        inv eq1. inv H6.
        {
          inv H11. inv H13. inv H5. inv H8. inv H15. inv H13. inv H16.
          apply IH3 in H3. 2 : { easy. }
          inv H6; inv H11; (eauto 20 with Progress); 
            try solve_empty_scope.
          - destruct H3 as [ HVal3 | [ HRed3 | [| HUnchk3]]]; idtac...
            + inv HVal3.
              inv HTy3.
              left; eauto...
              destruct (Z_gt_dec n 0); subst; rewrite HCtx; do 4 eexists.
              * eapply RSHaltNull... eapply SPlusNull. lia.
                unfold is_array_ptr. easy.
              * eapply RSHaltNull... eapply SPlusNull. lia.
                unfold is_array_ptr. easy.
            + destruct HRed3 as [H' [? [r HRed3]]].
              rewrite HCtx; left; do 4 eexists.
              eapply RSHaltNull... eapply SPlusNull. lia. 
                unfold is_array_ptr. easy.
            + destruct HUnchk3 as [ e' [ E [ He2 HEUnchk ]]]; subst.
              rewrite HCtx; left; do 4 eexists.
              eapply RSHaltNull... eapply SPlusNull. lia.
                unfold is_array_ptr. easy.
          - destruct H3 as [ HVal3 | [ HRed3 | [| HUnchk3]]]; idtac...
            + inv HVal3.
              inv HTy3.
              destruct (Z_gt_dec n 0); rewrite HCtx; left; do 4 eexists.
              * eapply RSHaltNull... eapply SPlusNull. lia.
                unfold is_array_ptr. easy.
              * eapply RSHaltNull... eapply SPlusNull. lia.
                unfold is_array_ptr. easy.
            + destruct HRed3 as [H' [? [r HRed3]]].
              rewrite HCtx; left; do 4 eexists.
              eapply RSHaltNull... eapply SPlusNull. lia.
                unfold is_array_ptr. easy.
            + destruct HUnchk3 as [ e' [ E [ He2 HEUnchk ]]]; subst.
              rewrite HCtx; left; do 4 eexists.
              eapply RSHaltNull... eapply SPlusNull. lia.
                unfold is_array_ptr. easy.
          - destruct (Z_gt_dec n 0); rewrite HCtx; left; do 4 eexists.
              * eapply RSExp. eapply SPlusChecked. lia.
                unfold is_array_ptr. easy.
                apply empty_means_cast_type_bound_same. assumption.
                eauto.
              * eapply RSHaltNull. eapply SPlusNull. lia.
                unfold is_array_ptr. easy. eauto.
          -  destruct (Z_gt_dec n 0); rewrite HCtx; left; do 4 eexists.
              * eapply RSExp. eapply SPlusChecked. lia.
                unfold is_array_ptr. easy. 
                apply empty_means_cast_type_bound_same. assumption.
                eauto.
              * eapply RSHaltNull. eapply SPlusNull. lia.
                unfold is_array_ptr. easy. eauto.
        }
      * destruct HRed2 as [ H' [ ? [? [ r HRed2 ] ] ] ].
        inv HRed2; ctx (EAssign (EPlus (ELit n t0) (in_hole e E)) e3) (in_hole e (CAssignL (CPlusR n t0 E) e3))...
      * destruct HUnchk2 as [ e' [ E [ He2 HEUnchk ] ] ]; subst.
        ctx (EAssign (EPlus (ELit n t0) (in_hole e' E)) e3) (in_hole e' (CAssignL (CPlusR n t0 E) e3))...
    + destruct HRed1 as [ H' [? [ ? [ r HRed1 ] ] ] ].
      inv HRed1; ctx (EAssign (EPlus (in_hole e E) e2) e3) (in_hole e (CAssignL (CPlusL E e2) e3))...
    + destruct HUnchk1 as [ e' [ E [ He1 HEUnchk ] ] ]; subst.
      ctx (EAssign (EPlus (in_hole e' E) e2) e3) (in_hole e' (CAssignL (CPlusL E e2) e3))...
  (* Istatement. It is impossible due to empty env. *)
   - inversion HEnv.
Qed.


(* ... for Preservation *)
Lemma weakening_bound : forall env x b t',
     well_bound_in env b -> well_bound_in (Env.add x t' env) b.
Proof.
  intros. induction H.
  apply well_bound_in_num.
  apply well_bound_in_var.
  unfold Env.In in *.
  unfold Env.Raw.PX.In in *.
  assert (x = x0 \/ x <> x0).
  lia.
  destruct H0.
  exists t'.
  apply Env.add_1. assumption.
  destruct H.
  exists x1.
  apply Env.add_2. assumption.
  assumption.
Qed.

Lemma weakening_type_bound : forall env x t t', 
         well_type_bound_in env t -> well_type_bound_in (Env.add x t' env) t.
Proof.
  intros.
  induction H.
  apply well_type_bound_in_nat.
  apply well_type_bound_in_ptr.
  assumption.
  apply well_type_bound_in_struct.
  apply well_type_bound_in_array.
  apply weakening_bound. assumption.
  apply weakening_bound. assumption.
  assumption.
  apply well_type_bound_in_ntarray.
  apply weakening_bound. assumption.
  apply weakening_bound. assumption.
  assumption.
Qed.


Lemma weakening : forall D F S H env m n t,
    @well_typed D F S H env m (ELit n t) t ->
    forall x t', @well_typed D F S H (Env.add x t' env) m (ELit n t) t.
Proof.
  intros D F S H env m e t HWT.
  inv HWT.
  inv H6; eauto.
  intros. apply TyLit.
  apply weakening_type_bound. assumption.
  apply (@WTStack D S H empty_scope e t t').
  assumption.
  apply H1.
Qed.

Lemma env_maps_add :
  forall env x (t1 t2 : type),
    Env.MapsTo x t1 (Env.add x t2 env) ->
    t1 = t2.
Proof.
  intros env x t1 t2 H.
  assert (Env.E.eq x x); try reflexivity.
  apply Env.add_1 with (elt := type) (m := env) (e := t2) in H0.
  remember (Env.add x t2 env) as env'.
  apply Env.find_1 in H.
  apply Env.find_1 in H0.
  rewrite H in H0.
  inv H0.
  reflexivity.
Qed.


(* This theorem will be useful for substitution.

   In particular, we can automate a lot of reasoning about environments by:
   (1) proving that equivalent environments preserve typing (this lemma)
   (2) registering environment equivalence in the Setoid framework (this makes proofs in (3) easier)
   (3) proving a number of lemmas about which environments are equivalent (such as shadowing above)
   (4) registering these lemmas in the proof automation (e.g. Hint Resolve env_shadow)

   Then when we have a typing context that looks like:

   H : (Env.add x0 t0 (Env.add x0 t1 env)) |- e : t
   ================================================
   (Env.add x0 t0 env) |- e : t

   we can solve it simply by eauto.

   during proof search, eauto should invoke equiv_env_wt which will leave a goal of
   (Env.add x0 t0 (Env.add x0 t1 env)) == (Env.add x0 t0) and then subsequently apply the
   shadowing lemma.
 *)

Lemma env_find_add1 : forall x (t : type) env,
    Env.find x (Env.add x t env) = Some t.
Proof.
  intros.
  apply Env.find_1.
  apply Env.add_1.
  reflexivity.
Qed.

Lemma env_find1 : forall x env,
    Env.find x env = None -> (forall (t : type), ~ Env.MapsTo x t env).
Proof.
  intros.
  unfold not.
  intros.
  apply Env.find_1 in H0.
  rewrite -> H0 in H.
  inv H.
Qed.

Lemma env_find2 : forall x env,
    (forall (t : type), ~ Env.MapsTo x t env) -> Env.find x env = None.
Proof.
  intros.
  destruct (Env.find (elt := type) x env0) eqn:Hd.
  - exfalso. eapply H.
    apply Env.find_2 in Hd.
    apply Hd.
  - reflexivity.
Qed.

Lemma env_find_add2 : forall x y (t : type) env,
    x <> y ->
    Env.find x (Env.add y t env) = Env.find x env.
Proof.
  intros.
  destruct (Env.find (elt:=type) x env0) eqn:H1.
  apply Env.find_1.
  apply Env.add_2.
  auto.
  apply Env.find_2.
  assumption.
  apply env_find2.
  unfold not.
  intros.
  eapply Env.add_3 in H0.
  apply Env.find_1 in H0.
  rewrite -> H1 in H0.
  inversion H0.
  auto.
Qed.

Lemma equiv_env_add : forall x t env1 env2,
    Env.Equal (elt:=type) env1 env2 ->
    Env.Equal (elt:=type) (Env.add x t env1) (Env.add x t env2).
Proof.
  intros.
  unfold Env.Equal.
  intros.
  destruct (Env.E.eq_dec x y).
  rewrite e.
  rewrite env_find_add1.
  rewrite env_find_add1.
  auto.
  auto.
  auto.
  rewrite env_find_add2.
  rewrite env_find_add2.
  unfold Env.Equal in H.
  apply H.
  auto.
  auto.
Qed.
(* LEO: All of these proofs are horribly brittle :) *)

Lemma equiv_env_well_bound : forall b env1 env2,
    Env.Equal env1 env2 -> well_bound_in env1 b -> well_bound_in env2 b.
Proof.
  intros. induction H0;eauto.
  apply well_bound_in_num.
  apply well_bound_in_var.
  unfold Env.In in *. unfold Env.Raw.PX.In in *.
  destruct H0.
  specialize (@Env.mapsto_equal type x x0 env0 env2 H0 H) as eq1.
  eauto.
Qed.

Lemma equiv_env_well_bound_type : forall t env1 env2,
    Env.Equal env1 env2 -> well_type_bound_in env1 t -> well_type_bound_in env2 t.
Proof.
  intros. induction H0;eauto.
  apply well_type_bound_in_nat.
  apply well_type_bound_in_ptr.
  apply IHwell_type_bound_in.
  assumption.
  apply well_type_bound_in_struct.
  apply well_type_bound_in_array.
  apply (equiv_env_well_bound l env0 env2). 1 - 2: assumption.
  apply (equiv_env_well_bound h env0 env2). 1 - 2: assumption.
  apply IHwell_type_bound_in. assumption.
  apply well_type_bound_in_ntarray.
  apply (equiv_env_well_bound l env0 env2). 1 - 2: assumption.
  apply (equiv_env_well_bound h env0 env2). 1 - 2: assumption.
  apply IHwell_type_bound_in. assumption.
Qed.

Lemma equiv_env_warg: forall D H S env1 env2 e t,
    Env.Equal env1 env2 -> 
     well_typed_arg D H S env1 e t -> 
     well_typed_arg D H S env2 e t.
Proof.
  intros. generalize dependent env2.
  induction H1; eauto 20.
  intros. eapply ArgLit.
  eapply equiv_env_well_bound_type. apply H4. assumption.
  apply H1. apply H2. apply H3.
  intros. eapply ArgVar.
  eapply equiv_env_well_bound_type. apply H4. apply H0.
  unfold Env.Equal in H4.
  apply Env.find_2. rewrite <- H4.
  apply Env.find_1 in H1.
  apply H1.
  apply H2. assumption.
Qed.

Lemma equiv_env_wargs: forall D H S env1 env2 es tvl,
    Env.Equal env1 env2 -> 
     well_typed_args D H S env1 es tvl -> 
     well_typed_args D H S env2 es tvl.
Proof.
  intros. generalize dependent env2.
  induction H1; eauto 20.
  intros. apply args_empty.
  intros. eapply args_many.
  eapply equiv_env_well_bound_type. apply H4. assumption.
  eapply equiv_env_warg. apply H4. assumption.
  apply H2. apply IHwell_typed_args.
  apply equiv_env_add. assumption.
Qed.

Lemma equiv_env_wt : forall D F S H env1 env2 m e t,
    Env.Equal env1 env2 ->
    @well_typed D F S H env1 m e t ->
    @well_typed D F S H env2 m e t.
Proof.
  intros.
  generalize dependent env2.
  induction H1; eauto 20.
  - intros. apply TyLit.
    apply (equiv_env_well_bound_type t env0 env2). 1 - 3 : assumption.
  - intros.
    apply TyVar.
    apply (equiv_env_well_bound_type t env0 env2). 1 - 2 : assumption.
    unfold Env.Equal in H2.
    apply Env.find_2.
    rewrite <- H2.
    apply Env.find_1.
    assumption.
  - intros. 
    eapply TyCall.
    apply H0.
    eapply equiv_env_wargs. apply H4.
    assumption.
    apply H2. assumption.
  - intros. 
    apply (TyStrlen env2 m x h l t).
    apply (equiv_env_well_bound_type (TPtr m (TNTArray h l t)) env0).
    assumption. assumption.
    eapply Env.mapsto_equal.
    apply H1. assumption.
  - intros.
    eapply TyLet.
    apply IHwell_typed1.
    assumption.
    apply IHwell_typed2.
    apply equiv_env_add.
    auto.
  - intros.
    eapply TyMalloc.
    apply (equiv_env_well_bound_type w env0 env2). 1 - 2 : assumption.
  - intros.
    eapply TyCast1; eauto.
    apply (equiv_env_well_bound_type t env0 env2). 1 - 2 : assumption.
  - intros.
    eapply TyCast2; eauto.
    apply (equiv_env_well_bound_type t env0 env2). 1 - 2 : assumption.
  - intros.
    eapply TyDynCast1; eauto.
    apply (equiv_env_well_bound_type (TPtr Checked (TArray x y t)) env0 env2). 1 - 2 : assumption.
  - intros.
    eapply TyDynCast2; eauto.
    apply (equiv_env_well_bound_type (TPtr Checked (TArray x y t)) env0 env2). 1 - 2 : assumption.
  - intros.
    eapply TyDynCast3; eauto.
    apply (equiv_env_well_bound_type (TPtr Checked (TNTArray x y t)) env0 env2). 1 - 2 : assumption.
  - intros.
    eapply TyIf; eauto.
    apply Env.find_2.
    apply Env.find_1 in H0.
    unfold Env.Equal in H5.
    rewrite <- H5. assumption.
Qed.

Lemma env_shadow : forall env x (t1 t2 : type),
    Env.Equal (Env.add x t2 (Env.add x t1 env)) (Env.add x t2 env).
Proof.
  intros env x t1 t2 y.
  destruct (Nat.eq_dec x y) eqn:Eq; subst; eauto.
  - do 2 rewrite env_find_add1; auto.
  - repeat (rewrite env_find_add2; eauto).
Qed.

Lemma env_shadow_eq : forall env0 env1 x (t1 t2 : type),
    Env.Equal env0 (Env.add x t2 env1) ->
    Env.Equal (Env.add x t1 env0) (Env.add x t1 env1).
Proof.
  intros env0 env1 x t1 t2 H y.
  destruct (Nat.eq_dec x y) eqn:Eq; subst; eauto.
  - repeat (rewrite env_find_add1; eauto).
  - rewrite env_find_add2; eauto.
    specialize (H y).
    rewrite env_find_add2 in H; eauto.
    rewrite env_find_add2; eauto.
Qed.

Lemma env_neq_commute : forall x1 x2 (t1 t2 : type) env,
    ~ Env.E.eq x1 x2 ->
    Env.Equal (Env.add x1 t1 (Env.add x2 t2 env)) (Env.add x2 t2 (Env.add x1 t1 env)).
Proof.
  intros x1 x2 t1 t2 env Eq x.
  destruct (Nat.eq_dec x x1) eqn:Eq1; destruct (Nat.eq_dec x x2) eqn:Eq2; subst; eauto;
  repeat (try rewrite env_find_add1; auto; try rewrite env_find_add2; auto).    
Qed.

Lemma env_neq_commute_eq : forall x1 x2 (t1 t2 : type) env env',
    ~ Env.E.eq x1 x2 -> Env.Equal env' (Env.add x2 t2 env) ->
    Env.Equal (Env.add x1 t1 env') (Env.add x2 t2 (Env.add x1 t1 env)).
Proof.
  intros x1 x2 t1 t2 env env' NEq Eq x.
  destruct (Nat.eq_dec x x1) eqn:Eq1; destruct (Nat.eq_dec x x2) eqn:Eq2; subst; eauto.
  - unfold Env.E.eq in *; exfalso; eapply NEq; eauto.
  - repeat (try rewrite env_find_add1 in *; auto; try rewrite env_find_add2 in *; auto).
  - specialize (Eq x2); repeat (try rewrite env_find_add1 in *; auto; try rewrite env_find_add2 in *; auto).
  - specialize (Eq x); repeat (try rewrite env_find_add1 in *; auto; try rewrite env_find_add2 in *; auto).
Qed.

Create HintDb Preservation.

(*
Lemma substitution :
  forall D H env m x v e t1 t2,
  @well_typed D H env m (ELit v t1) t1 ->
  @well_typed D H (Env.add x t1 env) m e t2 ->
  @well_typed D H env m (subst x (ELit v t1) e) t2.
Proof.
  intros D H env m x v e t1 t2 HWTv HWTe.
  generalize dependent v.
  remember (Env.add x t1 env) as env'.
  assert (Eq: Env.Equal env' (Env.add x t1 env))
    by (subst; apply EnvFacts.Equal_refl).
  clear Heqenv'.
  generalize dependent env.
  induction HWTe; subst; simpl; eauto 20.
  - intros. apply TyLit.
  - intros. destruct (var_eq_dec x x0); subst.
    + eapply Env.mapsto_equal in Eq; eauto.
      apply env_maps_add in Eq; subst. assumption.
    + apply TyVar.
      eapply Env.mapsto_equal in Eq; eauto.
      apply Env.add_3 in Eq. assumption. assumption.
  - intros. destruct (var_eq_dec x x0); subst.
    + eapply TyLet.
      * apply IHHWTe1; eauto.
      * eapply equiv_env_wt; eauto.
        eapply env_shadow_eq; eauto.
    + eapply TyLet.
      * apply IHHWTe1; eauto. 
      * {
          apply IHHWTe2; eauto.
          - apply env_neq_commute_eq; eauto.
          - inv HWTv. eapply TyLit; eauto.
        } 
  - intros. subst. apply TyUnchecked. apply IHHWTe; eauto.
    inv HWTv.
   (* inv Hvalue as [n' t'].
    destruct m. *)
      *
        apply TyLit.
        assumption.
Qed.
    

Hint Resolve substitution : Preservation.
*)

Lemma heapWArg :
  forall D S H H' env e t,
    well_typed_arg D S H env e t ->
    @heap_consistent D H' H ->
    well_typed_arg D S H' env e t.
Proof.
  intros D S H H' env es tvl WT HC.
  induction WT; intros; eauto.
  eapply ArgLit.
  assumption.
  unfold heap_consistent in HC.
  inv H1. econstructor. apply H4.
  apply HC. assumption.
  apply H2. assumption.
  eapply ArgVar.
  apply H0. apply H1. apply H2. assumption.
Qed.

Lemma heapWArgs :
  forall D S H H' env es tvl,
    well_typed_args D H S env es tvl ->
    @heap_consistent D H' H ->
    well_typed_args D H' S env es tvl.
Proof.
  intros D S H H' env es tvl WT HC.
  induction WT; intros; eauto.
  apply args_empty.
  eapply args_many.
  assumption. eapply heapWArg.
  apply H1. assumption.
  apply H2. assumption.
Qed.  

Lemma heapWF :
  forall D F S H H' env m e t,
    @well_typed D F S H env m e t ->
    @heap_consistent D H' H ->
    @well_typed D F S H' env m e t.
Proof.
  intros D F S H H' env m e t WT HC.
  induction WT; intros; eauto.
  apply TyLit.
  assumption.
  unfold heap_consistent in HC.
  inv H1. econstructor. apply H2.
  apply HC. assumption.
  eapply TyCall.
  apply H0.
  eapply heapWArgs.
  apply H1. assumption. apply H2. apply H3.
Qed.  

Hint Resolve heapWF : Preservation.

(*
Lemma wf_empty_scope : forall D H, scope_wf D H empty_scope.
Proof.
  intros D H x T Contra.
  inversion Contra.
Qed.

Hint Resolve wf_empty_scope.
Hint Resolve wf_empty_scope : Preservation.
 *)
(* Automate this*)
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

Require Import Coq.Program.Equality.
  
Lemma heap_wf_maps_nonzero : forall D H n v, heap_wf D H -> Heap.MapsTo n v H -> n <> 0.
Proof.
  intros D H n v Hwf HMap.
  destruct (Hwf n) as [ _ HIn ]. 
  destruct n; eauto.
    -exfalso. destruct HIn; try eexists; eauto; 
     inversion H0.
    -zify. lia.
    -zify. lia.
Qed.

(*
Lemma scope_wf_heap_weakening :
  forall s D H x v,
    ~ Heap.In x H ->
    scope_wf D H s -> scope_wf D (Heap.add x v H) s.
Proof.
  intros s D H x v HNotIn HSwf.
  intros x' t' HS.
  destruct (HSwf x' t') as [x0 [HA Hx0]]; eauto.
  exists x0.
  split; auto.
  intros k Hk.
  destruct (Hx0 k Hk) as [n' [T [HT HM]]].
  exists n'. exists T.
  split; auto.
  apply Heap.add_2; eauto.
  intro Contra; subst.
  apply HNotIn.
  eexists; eauto.
Qed.

Hint Resolve scope_wf_heap_weakening.
*)
Lemma cardinal_not_in :
  forall D H, heap_wf D H -> ~ Heap.In (Z.of_nat(Heap.cardinal H) + 1) H.
Proof.
  intros D H Hwf Contra.
  destruct (Hwf (Z.of_nat(Heap.cardinal H) + 1)) as [H1 H2].
  specialize (H2 Contra).
  lia.
Qed.


Lemma well_typed_preserved : forall D H t, heap_wf D H ->
  @heap_consistent D (Heap.add (Z.of_nat(Heap.cardinal H) + 1) (0, t) H) H.
Proof.
  intros D H t0 Hwf n t HT.
  induction HT using well_typed_lit_ind'; pose proof (cardinal_not_in D H Hwf); eauto.
  eapply TyLitC; eauto.
  intros k HK.  
  destruct (H1 k HK) as [n' [t' [HNth [HMap HWT]]]].
  exists n'. exists t'.
  repeat split; eauto.
  + apply Heap.add_2; eauto.
    destruct (Hwf (n+k)) as [ _ HIn ].
    destruct HIn; try eexists; eauto.
    lia.
  + inv HWT; eauto.
Qed.


  
Lemma heap_add_preserves_wf : forall D H n v, heap_wf D H ->
  heap_wf D (Heap.add (Z.of_nat(Heap.cardinal H) + 1) (n, v) H).
Proof.
  intros D H n v Hwf.
  split; intros; simpl; eauto.
  * rewrite cardinal_plus_one in H0.
    - assert (Hyp: 0 < addr <= Z.of_nat(Heap.cardinal H) \/ addr = Z.of_nat(Heap.cardinal H) + 1). {zify. lia. } 
      inv Hyp.
      + destruct (Hwf addr) as [ HIn _ ].
        specialize (HIn H1).
        inv HIn. exists x.
        apply Heap.add_2; eauto.
        lia.
      + eexists; eapply Heap.add_1; eauto.
    - intros Contra.
      destruct (Hwf (Z.of_nat(Heap.cardinal H) + 1)) as [? ?].
      specialize (H2 Contra).
      lia.
  * apply HeapFacts.add_in_iff in H0.
    inv H0.
    - rewrite cardinal_plus_one; try (zify; lia).
      intro Contra.
      destruct (Hwf (Z.of_nat(Heap.cardinal H) + 1)) as [? ?].
      specialize (H1 Contra).
      lia.
    - rewrite cardinal_plus_one.
      + destruct (Hwf addr) as [_ H2]; specialize (H2 H1); zify; lia.
      + intro Contra.
        destruct (Hwf (Z.of_nat(Heap.cardinal H) + 1)) as [H2 H3].
        specialize (H3 Contra).
        lia.
Qed.

Lemma backwards_consistency :
  forall D H' H v,
    @heap_consistent D H' (Heap.add (Z.of_nat(Heap.cardinal H) + 1) v H) ->
    heap_wf D H ->
    @heap_consistent D H' H.
Proof.
  intros D H' H v HC Hwf.
  intros n t HWT.
  eapply HC; eauto.
  induction HWT using well_typed_lit_ind'; pose proof (cardinal_not_in D H Hwf); eauto.
  eapply TyLitC; eauto.
  intros k HK.
  destruct (H1 k HK) as [n' [t' [HN [HM HW]]]].
  exists n'. exists t'.
  repeat split; eauto.
  - apply Heap.add_2; eauto.
    intro Contra.
    destruct (Hwf (n + k)) as [ _ Hyp ].
    destruct Hyp; [eexists; eauto | lia].
  - inv HW; eauto.
Qed.
      
Lemma fold_preserves_consistency : forall l D H ptr, heap_wf D H ->
  let (_, H') :=
      fold_left
        (fun (acc : Z * heap) (t : type) =>
           let (sizeAcc, heapAcc) := acc in
           (sizeAcc + 1, Heap.add (sizeAcc + 1) (0, t) heapAcc))
        l
        (Z.of_nat(Heap.cardinal H), H) in
  Some ((Z.of_nat(Heap.cardinal H) + 1), H') = Some (ptr, H') ->
  @heap_consistent D H' H.
Proof.
  intro l; induction l; intros; simpl; eauto.
  assert (Hwf : heap_wf D (Heap.add (Z.of_nat(Heap.cardinal H) + 1) (0, a) H))
    by (apply heap_add_preserves_wf; auto).
  specialize (IHl D (Heap.add (Z.of_nat(Heap.cardinal H) + 1) (0, a) H) (ptr + 1) Hwf).
  remember (Heap.add (Z.of_nat(Heap.cardinal H) + 1) (0, a) H) as H1.

  
  Set Printing All.
  remember ((fun (acc : prod Z heap) (t : type) =>
             match acc return (prod Z heap) with
             | pair sizeAcc heapAcc =>
                 @pair Z (Heap.t (prod Z type)) (sizeAcc + 1)
                   (@Heap.add (prod Z type) (sizeAcc + 1) 
                      (@pair Z type 0 t) heapAcc)
             end)) as fold_fun.
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


  
(* This could probably be merged with the previous one *)
Lemma fold_summary : forall l D H ptr,
  heap_wf D H ->
  let (_, H') :=
      fold_left
        (fun (acc : Z * heap) (t : type) =>
           let (sizeAcc, heapAcc) := acc in
           (sizeAcc + 1, Heap.add (sizeAcc + 1) (0, t) heapAcc))
        l
        (Z.of_nat(Heap.cardinal  H), H) in
  Some (Z.of_nat(Heap.cardinal  H)+ 1, H') = Some (ptr, H') ->
  heap_wf D H' /\
  ptr = Z.of_nat(Heap.cardinal  H) + 1 /\
  (Heap.cardinal  H') = ((Heap.cardinal H) + length l)%nat /\
  (forall (k : nat) v,
      (0 <= k < (length l))%nat -> nth_error l k = Some v ->
               Heap.MapsTo (Z.of_nat(Heap.cardinal  H) + 1 + Z.of_nat(k)) (0,v) H') /\
  forall x v, Heap.MapsTo x v H -> Heap.MapsTo x v H'.                                               
Proof.
  intro l; induction l; simpl; intros D H ptr Hwf.
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

    assert (Hwf' : heap_wf D (Heap.add (Z.of_nat(Heap.cardinal H) + 1) (0, a) H))
      by (apply heap_add_preserves_wf; eauto).
    specialize (IHl D (Heap.add (Z.of_nat(Heap.cardinal H) + 1) (0, a) H) (ptr + 1) Hwf').

    
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

Print length_nth.

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

Lemma alloc_correct : forall w D F S env H ptr H',
    simple_type w ->
    allocate D H w = Some (ptr, H') ->
    structdef_wf D ->
    heap_wf D H ->
    @heap_consistent D H' H /\
    @well_typed D F S H' env Checked (ELit ptr (TPtr Checked w)) (TPtr Checked w) /\
    heap_wf D H'.
Proof.
  intros w D F S env H ptr H' Wb Alloc HSd HWf.
  unfold allocate in *.
  unfold allocate_meta in *.
  unfold bind in *; simpl in *.
  destruct w; simpl in *; eauto; inv Alloc; simpl in *; eauto.
  - split; [| split].
    * apply well_typed_preserved; eauto.
    * apply TyLit; eauto.
      apply well_type_bound_in_ptr. apply well_type_bound_in_nat.
      eapply WTStack. apply cast_type_bound_ptr. apply cast_type_bound_nat.
      eapply TyLitC; simpl; eauto.
      intros k HK.
      simpl in HK.
      assert (k = 0) by lia; subst; clear HK.
      exists 0. exists TNat.
      repeat split; eauto.
      apply Heap.add_1; eauto. lia.
    * apply heap_add_preserves_wf; auto.
  - split; [ | split].
    * apply well_typed_preserved; eauto.
    * apply TyLit; eauto.
      apply (simple_type_well_bound env) in Wb.
      apply well_type_bound_in_ptr. assumption.
      eapply WTStack. apply cast_type_bound_ptr.
      apply (simple_type_means_cast_same). assumption.
      eapply TyLitC; simpl; eauto.
      intros k HK.
      simpl in HK.
      assert (k = 0) by lia; subst; clear HK.
      exists 0. exists (TPtr m w).
      repeat split; eauto.
      apply Heap.add_1; eauto. lia.
    * apply heap_add_preserves_wf; auto.
  - split.

    *unfold allocate in H1.
      unfold allocate_meta_no_bounds, allocate_meta in H1.
      destruct (StructDef.find s D) eqn:Find; simpl in *; try congruence.

      remember (Fields.elements f) as l.

      pose proof (fold_preserves_consistency (map snd l) D H ptr HWf).
      
      remember (fold_left
            (fun (acc : Z * heap) (t : type) =>
             let (sizeAcc, heapAcc) := acc in (sizeAcc + 1, Heap.add (sizeAcc + 1) (0, t) heapAcc))
            (map snd l) (Z.of_nat(Heap.cardinal H), H)) as p.
      
      destruct p.
      clear Heqp.      
      inv H1.
      eauto.
    
    * unfold allocate_meta_no_bounds, allocate_meta in H1.

      simpl in *.
      destruct (StructDef.find s D) eqn:Find; try congruence.

      pose proof (fold_summary (map snd (Fields.elements f)) D H ptr HWf) as Hyp.

      remember
        (fold_left
           (fun (acc : Z * heap) (t : type) =>
            let (sizeAcc, heapAcc) := acc in
            (sizeAcc + 1, Heap.add (sizeAcc + 1) (0, t) heapAcc))
           (map snd (Fields.elements (elt:=type) f))
           (Z.of_nat(Heap.cardinal H), H)) as p.
      destruct p as [z h].
      clear Heqp.
      inv H1.

      destruct Hyp as [H'wf  [Card1 [Card2 [HF HM]]]]; eauto.

      split; auto.
      constructor.
      apply (simple_type_well_bound env) in Wb.
      apply well_type_bound_in_ptr. assumption.
      eapply WTStack. apply cast_type_bound_ptr.
      apply cast_type_bound_struct.
      eapply TyLitC; simpl in *; eauto; [ rewrite Find | ]; eauto.
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
      rewrite Z.sub_0_r in *.
      destruct (Zlength_nth (map snd (Fields.elements f)) k HK) as [x Hnth].
      assert (HK': (0 <= (Z.to_nat k) < (length (map snd (Fields.elements (elt:=type) f))))%nat). {
        destruct k.
          +zify. simpl. lia.
          +simpl. zify. lia.
          +exfalso. inv HK. apply H0. simpl. reflexivity. }
      specialize (HF (Z.to_nat k) x HK' Hnth).
      assert (K0 : k = Z.of_nat (Z.to_nat k)). {
      destruct k.
        +simpl. reflexivity.
        +simpl. zify. reflexivity.
        +inv HK. exfalso. apply H0. simpl. reflexivity. }
      rewrite <- K0 in HF.
      pose proof (HeapFacts.MapsTo_fun HM' HF) as Eq.
      inv Eq.
      repeat (split; eauto).
  - split.
    * destruct b. destruct b0.

      remember (Zreplicate (z0 - z) w) as l.
      pose proof (fold_preserves_consistency l D H ptr HWf) as H0.

      remember (fold_left
         (fun (acc : Z * heap) (t : type) =>
          let (sizeAcc, heapAcc) := acc in
          (sizeAcc + 1, Heap.add (sizeAcc + 1) (0, t) heapAcc))
         l
         (Z.of_nat (Heap.cardinal (elt:=Z * type) H), H)) as p.
      
      destruct p as (n1, h). (*n0 already used???*)
      clear Heqp.
      destruct z; inv H1.
      apply H0; eauto.
      inv Wb. inv Wb.
    * destruct b. destruct b0.

      remember (Zreplicate (z0 - z) w) as l.

      pose proof (fold_summary l D H ptr HWf) as Hyp.
      remember
        (fold_left
          (fun (acc : Z * heap) (t : type) =>
           let (sizeAcc, heapAcc) := acc in
           (sizeAcc + 1, Heap.add (sizeAcc + 1) (0, t) heapAcc)) l
          (Z.of_nat (Heap.cardinal (elt:=Z * type) H), H)) as p.
      destruct p.
      clear Heqp.
      inv H1.

      destruct z; inv H2; eauto.
      destruct Hyp as [H'wf  [Card1 [Card2 [HF HM]]]]; eauto.

      
      split; auto.
      constructor.
      apply (simple_type_well_bound env) in Wb.
      apply well_type_bound_in_ptr. assumption.
      eapply WTStack. apply cast_type_bound_ptr.
      apply (simple_type_means_cast_same). assumption.
      eapply TyLitC; simpl in *; eauto.
      intros k HK.
      simpl in *.
      pose proof (H'wf (Z.of_nat(Heap.cardinal H) + 1 + k)) as Hyp.
      rewrite Z.sub_0_r in *.

      remember (Heap.cardinal H ) as c.
      remember (Heap.cardinal H') as c'.
      
      assert (HOrd : 0 < Z.of_nat c + 1 + k <= Z.of_nat c')
        by (zify; lia).
      
      destruct Hyp as [HIn Useless].
      destruct (HIn HOrd) as [[n' t'] HM'].

      destruct HK as [HP1 HP2].

      destruct z0 as [ | p | ?]; simpl in *; [ lia | | lia].
      rewrite replicate_length in *.

      destruct (length_nth (replicate (Pos.to_nat p) w) (Z.to_nat k)) as [t Hnth].
      { rewrite replicate_length ; zify; split; try lia. }
       (* (*This should go through with omega but it doesn't*)
        assert (Hk : Z.of_nat (Z.to_nat k) = k). {
        destruct k; simpl.
          + reflexivity.
          + zify. omega.
          + exfalso. zify. apply HP1. simpl. reflexivity. }
        rewrite Hk. assumption.
      } *)

      rewrite Z.sub_0_r in *.
      
      rewrite Hnth.
      remember Hnth as Hyp; clear HeqHyp.
      apply replicate_nth in Hnth. rewrite Hnth in *; clear Hnth.
        
      exists n'; exists t.
      split; [ reflexivity | ].

      specialize (HF (Z.to_nat k) t).
      assert (HF1 : (0 <= Z.to_nat k < Pos.to_nat p)%nat). {
        split; zify; (try lia).
        (* destruct k; simpl; zify; lia.*)
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
      inv Wb. inv Wb.
  - split.
    * destruct b. destruct b0.

      remember (Zreplicate (z0 - z + 1) w) as l.
      pose proof (fold_preserves_consistency l D H ptr HWf) as H0.

      remember (fold_left
         (fun (acc : Z * heap) (t : type) =>
          let (sizeAcc, heapAcc) := acc in
          (sizeAcc + 1, Heap.add (sizeAcc + 1) (0, t) heapAcc))
         l
         (Z.of_nat (Heap.cardinal (elt:=Z * type) H), H)) as p.
      
      destruct p as (n1, h). (*n0 already used???*)
      clear Heqp.
      destruct z; inv H1.
      apply H0; eauto.
      inv Wb. inv Wb.
    * destruct b. destruct b0.

      remember (Zreplicate (z0 - z + 1) w) as l.

      pose proof (fold_summary l D H ptr HWf) as Hyp.
      remember
        (fold_left
          (fun (acc : Z * heap) (t : type) =>
           let (sizeAcc, heapAcc) := acc in
           (sizeAcc + 1, Heap.add (sizeAcc + 1) (0, t) heapAcc)) l
          (Z.of_nat (Heap.cardinal (elt:=Z * type) H), H)) as p.
      destruct p.
      clear Heqp.
      inv H1.

      destruct z; inv H2; eauto.
      destruct Hyp as [H'wf  [Card1 [Card2 [HF HM]]]]; eauto.

      
      split; auto.
      constructor.
      apply (simple_type_well_bound env) in Wb.
      apply well_type_bound_in_ptr. assumption.
      eapply WTStack. apply cast_type_bound_ptr.
      apply (simple_type_means_cast_same). assumption.
      eapply TyLitC; simpl in *; eauto.
      intros k HK.
      simpl in *.
      pose proof (H'wf (Z.of_nat(Heap.cardinal H) + 1 + k)) as Hyp.
      rewrite Z.sub_0_r in *.

      remember (Heap.cardinal H ) as c.
      remember (Heap.cardinal H') as c'.
      
      assert (HOrd : 0 < Z.of_nat c + 1 + k <= Z.of_nat c')
        by (zify; lia).
      
      destruct Hyp as [HIn Useless].
      destruct (HIn HOrd) as [[n' t'] HM'].

      destruct HK as [HP1 HP2].

      destruct (z0+1) as [ | p | ?]; simpl in *; [ lia | | lia].
      rewrite replicate_length in *.

      destruct (length_nth (replicate (Pos.to_nat p) w) (Z.to_nat k)) as [t Hnth].
      { rewrite replicate_length ; zify; split; try lia. }
       (* (*This should go through with omega but it doesn't*)
        assert (Hk : Z.of_nat (Z.to_nat k) = k). {
        destruct k; simpl.
          + reflexivity.
          + zify. omega.
          + exfalso. zify. apply HP1. simpl. reflexivity. }
        rewrite Hk. assumption.
      } *)

      rewrite Z.sub_0_r in *.
      
      rewrite Hnth.
      remember Hnth as Hyp; clear HeqHyp.
      apply replicate_nth in Hnth. rewrite Hnth in *; clear Hnth.
        
      exists n'; exists t.
      split; [ reflexivity | ].

      specialize (HF (Z.to_nat k) t).
      assert (HF1 : (0 <= Z.to_nat k < Pos.to_nat p)%nat). {
        split; zify; (try lia).
        (* destruct k; simpl; zify; lia.*)
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
      inv Wb. inv Wb.
Qed.

Definition heap_wt (D : structdef) (H:heap) := forall x n t, Heap.MapsTo x (n,t) H
            -> word_type t /\ type_wf D t /\ simple_type t.

Definition stack_wt (D : structdef) (S:stack) := forall x n t, Stack.MapsTo x (n,t) S
            -> word_type t /\ type_wf D t /\ simple_type t.

Definition env_wt (D : structdef) (env:env) := forall x t, Env.MapsTo x t env
            -> word_type t /\ type_wf D t. 

Lemma subtype_word_type_1 : forall D t t', subtype D t t' -> word_type t -> word_type t'.
Proof.
  intros.
  inv H. assumption.
  1-8:constructor.
Qed.

Lemma get_root_word_type : forall m t t', get_root (TPtr m t) t' -> word_type t -> word_type t'.
Proof.
  intros.
  inv H. assumption. inv H0. inv H0.
Qed.

Lemma get_root_type_wf : forall D m t t', get_root (TPtr m t) t' -> type_wf D t -> type_wf D t'.
Proof.
  intros.
  inv H. assumption. inv H0. assumption.
  inv H0. assumption.
Qed.

Lemma get_root_simple_type : forall m t t', get_root (TPtr m t) t' -> simple_type t -> simple_type t'.
Proof.
  intros.
  inv H. assumption. inv H0. assumption.
  inv H0. assumption.
Qed.

Lemma subtype_type_wf : forall D t t', subtype D t t' -> type_wf D t -> type_wf D t'.
Proof.
  intros.
  inv H. assumption.
  inv H0. constructor.
  constructor. assumption. assumption.
  inv H0.
  constructor.
  inv H4.
  assumption.
  constructor.
  inv H0.
  inv H4. assumption.
  inv H0. inv H3. constructor. constructor. assumption. assumption.
  inv H0. inv H3. constructor. constructor. assumption. assumption.
  inv H0. inv H3. constructor. constructor. assumption. assumption.
  constructor. constructor.
  constructor. constructor.
  constructor. constructor.
Qed.

Lemma subtype_type_wf_1 : forall D t t', subtype D t t' -> type_wf D t' -> type_wf D t.
Proof.
  intros.
  inv H. assumption.
  inv H0. inv H4. constructor. assumption.
  inv H0.
  constructor. constructor.
  assumption. assumption.
  inv H0.
  constructor. constructor.
  assumption. assumption.
  inv H0. inv H3.
  constructor. constructor.
  1-2:assumption.
  inv H0. inv H3.
  constructor. constructor.
  assumption. assumption.
  inv H0. inv H3.
  constructor. constructor.
  assumption. assumption.
  constructor. constructor.
  exists fs. assumption.
  constructor. constructor.
  exists fs. assumption.
Qed.

Lemma type_eq_word_type_1 :  forall S t t', type_eq S t t' -> word_type t' -> word_type t.
Proof.
  intros.
  inv H. assumption.
  inv H0. inv H2. constructor.
  inv H2. constructor.
  inv H0. inv H2. constructor.
  inv H2. constructor.
Qed.

Lemma cast_word_type_1 : forall s t t', cast_type_bound s t t' -> word_type t' -> word_type t.
Proof.
  intros.
  induction H0. inv H. constructor.
  inv H. constructor.
Qed.


Lemma cast_type_wf_1 : forall D s t t', cast_type_bound s t t' -> type_wf D t' -> type_wf D t.
Proof.
 intros. generalize dependent t. induction t'.
 intros. inv H. constructor.
 intros. inv H. constructor. apply IHt'. inv H0. assumption.
 assumption.
 intros. inv H. constructor.
 inv H0. destruct H1. exists x. assumption.
 intros. inv H.
 constructor. inv H0. eapply cast_word_type_1. apply H7. assumption.
 apply IHt'. inv H0. assumption. assumption.
 intros. inv H.
 constructor. inv H0. eapply cast_word_type_1. apply H7. assumption.
 apply IHt'. inv H0. assumption. assumption.
Qed.

Lemma type_eq_type_wf : forall D S t t', type_eq S t t' -> type_wf D t' -> type_wf D t.
Proof.
  intros.
  inv H0.
  inv H. constructor.
  inv H1. constructor.
  inv H1. constructor.
  inv H. constructor. assumption.
  inv H2.
  constructor.
  eapply cast_type_wf.
  apply H5. assumption.
  inv H2.
  constructor.
  eapply cast_type_wf_1.
  apply H4.
  assumption.
  inv H.
  constructor.
  easy.
  inv H2.
  constructor.
  easy.
  inv H2.
  constructor.
  easy.
  inv H.
  constructor. easy. easy.
  inv H3.
  constructor.
  eapply cast_word_type. apply H9. assumption. 
  eapply cast_type_wf. apply H9. assumption.
  inv H3.
  constructor.
  eapply cast_word_type_1. apply H9. assumption. 
  eapply cast_type_wf_1. apply H9. assumption.
  inv H.
  constructor. assumption. assumption.
  inv H3. constructor.
  eapply cast_word_type. apply H9. assumption. 
  eapply cast_type_wf. apply H9. assumption.
  inv H3. constructor.
  eapply cast_word_type_1. apply H9. assumption. 
  eapply cast_type_wf_1. apply H9. assumption.
Qed.

Lemma type_eq_type_wf_1 : forall D S t t', type_eq S t t' -> type_wf D t -> type_wf D t'.
Proof.
  intros.
  inv H0.
  inv H. constructor.
  inv H1. constructor.
  inv H1. constructor.
  inv H. constructor. assumption.
  inv H2.
  constructor.
  eapply cast_type_wf_1.
  apply H4. assumption.
  inv H2.
  constructor.
  eapply cast_type_wf.
  apply H5.
  assumption.
  inv H.
  constructor.
  easy.
  inv H2.
  constructor.
  easy.
  inv H2.
  constructor.
  easy.
  inv H.
  constructor. easy. easy.
  inv H3.
  constructor.
  eapply cast_word_type_1. apply H9. assumption. 
  eapply cast_type_wf_1. apply H9. assumption.
  inv H3.
  constructor.
  eapply cast_word_type. apply H9. assumption. 
  eapply cast_type_wf. apply H9. assumption.
  inv H.
  constructor. assumption. assumption.
  inv H3. constructor.
  eapply cast_word_type_1. apply H9. assumption. 
  eapply cast_type_wf_1. apply H9. assumption.
  inv H3. constructor.
  eapply cast_word_type. apply H9. assumption. 
  eapply cast_type_wf. apply H9. assumption.
Qed.

Lemma meet_type_word_type_1 : forall D s t t1 t2, meet_type D s t t1 t2 -> word_type t -> word_type t2.
Proof.
  intros. inv H0. inv H.
  inv H0. constructor.
  inv H0. inv H2. inv H1. constructor.
  inv H0. constructor.
  inv H0. inv H2. inv H1.
  constructor.
  inv H. inv H0.
  1 - 9: constructor.
  inv H0. inv H2. inv H1.
  constructor.
  inv H1.
  constructor.
  inv H1.
  constructor.
  inv H1.
  constructor.
  inv H1. constructor.
  inv H1. constructor.
  inv H1. constructor.
  inv H1. constructor.
  inv H1. constructor.
  inv H0. 1 - 9 : constructor.
  inv H0.
  apply ptr_subtype_equiv in H2.
  destruct H2. subst.
  inv H1. constructor.
Qed.

Lemma meet_type_type_wf : forall D s t t1 t2, meet_type D s t t1 t2 
                                -> type_wf D t -> type_wf D t1 -> type_wf D t2.
Proof.
  intros. inv H. assumption.
  assumption.
  assumption.
  assumption.
Qed.

Lemma well_typed_word_type_wf :
   forall D F S H env m e t,
          structdef_wf D ->
          expr_wf D F e -> 
         env_wt D env ->
         fun_typed D F S H ->
         @well_typed D F S H env m e t  -> word_type t /\ type_wf D t.
Proof.
  intros.
  induction H4; eauto.
  inv H1. easy.
  apply H3 in H4.
  destruct H4. destruct H8.
  split.
  apply subtype_word_type_1 in H7. eapply type_eq_word_type_1.
  apply H6. assumption. assumption.
  apply subtype_type_wf in H7.
  eapply type_eq_type_wf. apply H6.
  assumption. assumption.
  split. constructor. constructor.
  inv H1.
  specialize (IHwell_typed1 H6 H2) as eq1.
  assert (env_wt D (Env.add x t1 env0)).
  unfold env_wt in *.
  intros.
  destruct (Nat.eq_dec x0 x).
  subst.
  apply Env.mapsto_add1 in H1.
  subst. assumption.
  apply Env.add_3 in H1.
  specialize (H2 x0 t0 H1) as eq2.
  easy. lia.
  specialize (IHwell_typed2 H8 H1) as eq2. easy.
  split. constructor. constructor.
  inv H1.
  split. constructor. constructor.
  unfold structdef_wf in H0.
  apply H0 in H5.
  unfold fields_wf in H5.
  apply H5 in H6.
  easy.
  inv H1.
  split. constructor. constructor. easy.
  apply IHwell_typed.
  inv H1. assumption. assumption.
  inv H1. easy.
  inv H1.
  easy.
  inv H1.
  split. easy. easy.
  inv H1.
  split. easy.
  constructor. constructor.
  inv H11. inv H8.
  easy.
  inv H11. inv H8. easy.
  inv H1. easy.
  inv H1.
  specialize (IHwell_typed H9 H2).
  destruct H6.
  destruct IHwell_typed.
  destruct H1. subst.
  split. easy.
  assert (type_wf D (TPtr m' t')).
  eapply subtype_type_wf. apply H5.
  assumption. inv H10. assumption.
  destruct H1.
  destruct H1. subst.
  easy.
  destruct H1. subst.
  easy.
  split.
  eapply type_eq_word_type. apply H6.
  assumption.
  inv H1.
  specialize (IHwell_typed1 H10 H2) as eq1.
  destruct eq1. inv H8.
  eapply type_eq_type_wf_1.
  apply H6. assumption. 
  split.
  eapply type_eq_word_type. apply H6.
  assumption.
  inv H1.
  specialize (IHwell_typed1 H11 H2) as eq1.
  destruct eq1. inv H9. inv H13.
  eapply type_eq_type_wf_1.
  apply H6. assumption. 
  split.
  eapply type_eq_word_type. apply H6.
  assumption.
  inv H1.
  specialize (IHwell_typed1 H11 H2) as eq1.
  destruct eq1. inv H9. inv H13.
  eapply type_eq_type_wf_1.
  apply H6. assumption. 
  split. 
  eapply subtype_word_type_1.
  apply H7. assumption.
  eapply subtype_type_wf.
  apply H7. assumption.
  split. 
  eapply subtype_word_type_1.
  apply H7. assumption.
  eapply subtype_type_wf.
  apply H7. assumption.
  inv H1.
  specialize (IHwell_typed1 H11 H2) as eq1.
  specialize (IHwell_typed2 H13 H2) as eq2.
  destruct eq1. destruct eq2.
  split.
  eapply meet_type_word_type_1. apply H7.
  assumption.
  eapply meet_type_type_wf.
  apply H7.
  assumption. assumption.
Qed.

Lemma in_map_snd : forall (l : list (Fields.key*type)) t,
                In t (map snd l) -> (exists x, In (x,t) l).
Proof.
  intros.
  induction l. inv H.
  simpl in *.
  destruct H.
  destruct a. exists k. simpl in H. subst. left. easy.
  apply IHl in H.
  destruct H.
  exists x. right. easy.
Qed.

Axiom field_eq : Equivalence (Fields.eq_key_elt (elt:=type)).

Lemma replicate_in : forall n (w t:type), In t (replicate n w) -> t = w.
Proof.
 induction n.
 simpl. intros. inv H.
 simpl. intros. destruct H. easy.
 apply IHn in H. easy.
Qed.

Lemma allocate_meta_wt : forall D w n tl, 
          structdef_wf D -> type_wf D w -> simple_type w 
            -> allocate_meta D w = Some (n, tl) ->
                      (forall t, In t tl -> word_type t /\ type_wf D t /\ simple_type t).
Proof.
   intros. unfold allocate_meta in H2.
   destruct w. inv H2.
   inv H3.
   split. easy. split. easy. easy.
   inv H2.
   inv H2. inv H3.
   split. easy. split. constructor. inv H0. easy. easy.
   inv H2.
   destruct ((StructDef.find (elt:=fields) s D)) eqn:eq1.
   inv H2.
   apply in_map_snd in H3.
   destruct H3.
   apply (@In_InA (Fields.key*type) (Fields.eq_key_elt (elt:=type))) in H2.
   apply Fields.elements_2 in H2.
   unfold structdef_wf in H.
   apply StructDef.find_2 in eq1.
   apply H in eq1.
   apply eq1 in H2. easy.
   apply field_eq.
   inv H2. inv H1.
   inv H2.
   unfold Zreplicate in H3.
   destruct (h - n). inv H3.
   apply replicate_in in H3.
   subst.
   inv H0. easy.
   inv H3.
   inv H1.
   inv H2.
   unfold Zreplicate in H3.
   destruct (h - n + 1). inv H3.
   apply replicate_in in H3.
   subst.
   inv H0. easy.
   inv H3.
Qed.

Lemma heap_add_preserves_wt : forall D H n v, heap_wt D H ->
  word_type v -> type_wf D v -> simple_type v ->
  heap_wt D (Heap.add (Z.of_nat(Heap.cardinal H) + 1) (n, v) H).
Proof.
  intros D H n v WT Twf ST Hwf.
  unfold heap_wt in *.
  intros.
  destruct (Z.eq_dec x (Z.of_nat (Heap.cardinal (elt:=Z * type) H) + 1)).
  subst.
  apply Heap.mapsto_add1 in H0. inv H0.
  easy.
  apply Heap.add_3 in H0. apply WT in H0.
  easy. lia.
Qed.


Lemma allocate_wt_aux : forall l D H ptr, 
   heap_wf D H -> 
   heap_wt D H ->
   (forall t, In t l -> word_type t /\ type_wf D t /\ simple_type t) ->
  let (_, H') :=
      fold_left
        (fun (acc : Z * heap) (t : type) =>
           let (sizeAcc, heapAcc) := acc in
           (sizeAcc + 1, Heap.add (sizeAcc + 1) (0, t) heapAcc))
        l
        (Z.of_nat(Heap.cardinal H), H) in
  Some ((Z.of_nat(Heap.cardinal H) + 1), H') = Some (ptr, H') ->
  heap_wt D H'.
Proof.
  intro l; induction l; intros; simpl; eauto.
  assert (Hwt : heap_wt D (Heap.add (Z.of_nat(Heap.cardinal H) + 1) (0, a) H)).
  specialize (H2 a). assert (a = a \/ In a l). left. easy.
  apply H2 in H3.
  apply heap_add_preserves_wt. assumption. 1-3:easy.
  assert (Hwf : heap_wf D (Heap.add (Z.of_nat(Heap.cardinal H) + 1) (0, a) H))
     by (apply heap_add_preserves_wf; eauto).
  assert ((forall t : type,
       In t l -> word_type t /\ type_wf D t /\ simple_type t)).
  intros. simpl in H2.
  assert (a = t \/ In t l). right. assumption. apply H2 in H4. easy.
  specialize (IHl D (Heap.add (Z.of_nat(Heap.cardinal H) + 1) (0, a) H) (ptr + 1) Hwf Hwt H3).
  remember (Heap.add (Z.of_nat(Heap.cardinal H) + 1) (0, a) H) as H5.

  Set Printing All.
  remember ((fun (acc : prod Z heap) (t : type) =>
             match acc return (prod Z heap) with
             | pair sizeAcc heapAcc =>
                 @pair Z (Heap.t (prod Z type)) (sizeAcc + 1)
                   (@Heap.add (prod Z type) (sizeAcc + 1) 
                      (@pair Z type 0 t) heapAcc)
             end)) as fold_fun.
  Unset Printing All.
  clear Heqfold_fun. 

  assert (Z.of_nat(Heap.cardinal H5) = (Z.of_nat(Heap.cardinal H) + 1)).
  {
    subst; apply cardinal_plus_one; eauto.
    intro Contra. 
    destruct (H0 (Z.of_nat(Heap.cardinal H) + 1)) as [H7 H8].
    specialize (H8 Contra).
    lia.
  } 
  rewrite H4 in IHl.

  assert (HEq:
      (  fold_left fold_fun l
            (@pair Z heap (Z.of_nat(Heap.cardinal H) + 1) H5) ) =
      (    @fold_left (prod Z heap) type fold_fun l
                      (@pair Z (Heap.t (prod Z type)) (Z.of_nat(Heap.cardinal H) + 1) H5))
    ). {zify. eauto. }


  rewrite HEq in IHl.


  match goal with
  | |- (match ?X with _ => _ end) => destruct X
  end.
  intro Hyp.
  inv Hyp.
   
  assert (Z.of_nat(Heap.cardinal H) + 1 + 1 = Z.of_nat((Heap.cardinal H + 1)) + 1) by (zify; lia).
  rewrite H5 in IHl.

  specialize (IHl eq_refl).
  assumption.
Qed.

Lemma allocate_wt : forall D H w n H',    
         heap_wf D H -> 
         heap_wt D H -> 
          structdef_wf D -> type_wf D w -> simple_type w ->
                 allocate D H w = Some (n, H') -> heap_wt D H'.
Proof.
 intros. unfold allocate in H5.
 destruct (allocate_meta D w) eqn:eq1.
 destruct p.
 specialize (allocate_meta_wt D w z l H2 H3 H4 eq1) as eq2.
 destruct z.
 clear eq1.
 Check allocate_wt_aux.
 
 pose proof (allocate_wt_aux l D H n H0 H1 eq2).

 remember (fold_left
         (fun (acc : Z * heap) (t : type) =>
          let (sizeAcc, heapAcc) := acc in
          (sizeAcc + 1, Heap.add (sizeAcc + 1) (0, t) heapAcc)) l
         (Z.of_nat (Heap.cardinal (elt:=Z * type) H), H)) as p.
      
 destruct p.
 clear Heqp.      
 inv H5.
 eauto. inv H5. inv H5. inv H5.
Qed.

Lemma heapWT : forall D F S S' H H' env m e t r,
     heap_wf D H -> 
     structdef_wf D ->
     expr_wf D F e -> 
     env_wt D env ->
     fun_typed D F S H ->
    @well_typed D F S H env m e t ->
     heap_wt D H -> step D F S H e S' H' r -> heap_wt D H'.
Proof.
  intros D F S S' H H' env m e t r Hwf Wsd Wexp Wenv Wfun WT Hwt HS.
  induction HS; eauto.
  unfold heap_wt in *.
  subst.
  intros.
  destruct (Z.eq_dec x n).
  subst.
  apply Heap.mapsto_add1 in H5.
  inv H5.
  inv WT.
  inv Wexp.
  specialize (well_typed_word_type_wf D F s H env m 
               (ELit n t0) (TPtr m' t2) Wsd H11 Wenv Wfun H10) as eq1.
  inv H10. 
  inv H1.
  assert (word_type t').
  eapply cast_word_type. apply H14. assumption.
  assert (type_wf D t').
  eapply cast_type_wf.
  apply H14.
  destruct eq1. inv H6. assumption.
  assert (simple_type t').
  apply cast_means_simple_type in H14. assumption.
  split. eapply get_root_word_type. apply H4. assumption.
  split. eapply get_root_type_wf. apply H4. assumption.
  eapply get_root_simple_type. apply H4. assumption.
  inv Wexp.
  specialize (well_typed_word_type_wf D F s H env m 
               (ELit n t0) (TPtr m' (TArray l h t2)) Wsd H12 Wenv Wfun H11) as eq1.
  inv H11. 
  inv H1. inv H15.
  assert (word_type t'1).
  eapply cast_word_type. apply H21. assumption.
  assert (type_wf D t'1).
  eapply cast_type_wf.
  apply H21.
  destruct eq1. inv H6. inv H17. assumption.
  assert (simple_type t'1).
  apply cast_means_simple_type in H21. assumption.
  split. inv H4. inv H23. assumption.
  split. inv H4. inv H23. assumption.
  inv H4. inv H23. assumption.
  inv Wexp.
  specialize (well_typed_word_type_wf D F s H env m 
               (ELit n t0) (TPtr m' (TNTArray l h t2)) Wsd H12 Wenv Wfun H11) as eq1.
  inv H11. 
  inv H1. inv H15.
  assert (word_type t'1).
  eapply cast_word_type. apply H21. assumption.
  assert (type_wf D t'1).
  eapply cast_type_wf.
  apply H21.
  destruct eq1. inv H6. inv H17. assumption.
  assert (simple_type t'1).
  apply cast_means_simple_type in H21. assumption.
  split. inv H4. inv H23. assumption.
  split. inv H4. inv H23. assumption.
  inv H4. inv H23. assumption.
  apply Heap.add_3 in H5.
  apply Hwt in H5. easy. lia.
  inv Wexp.
  assert (type_wf D w'). 
  eapply cast_type_wf. apply H0. assumption.
  assert (simple_type w').
  eapply cast_means_simple_type. apply H0. 
  apply (allocate_wt D H w' n1 H' Hwf Hwt Wsd H3 H5 H2).
Qed.  

Hint Resolve heapWT : Preservation.

Lemma values_are_nf : forall D F H s e,
    value D e ->
    ~ exists H' s' m r, @reduce D F s H e m H' s' r.
Proof.
  intros D F H s e Hv contra.
  inv Hv.
  destruct contra as [H' [ m [ s' [ r contra ] ] ] ].
  inv contra; destruct E; inversion H4; simpl in *; subst; try congruence.
Qed.

Lemma lit_are_nf : forall D F H s n t,
    ~ exists H'  s' m r, @reduce D F s H (ELit n t) m s' H' r.
Proof.
  intros D F s H n t contra.
  destruct contra as [H' [ s' [ m [ r contra ] ] ] ].
  inv contra; destruct E; inversion H2; simpl in *; subst; try congruence.
Qed.

(*
This theorem is incorrect!!. 

Lemma var_is_nf : forall D s H x,
    ~ exists H' s' m r, @reduce D s H (EVar x) m s' H' r.
Proof.
  intros.
  intros contra.
  destruct contra as [H' [ m [s' [ r contra ] ] ] ].
  inv contra; destruct E; inversion H1; simpl in *; subst; inv H2.
Admitted.
*)

Ltac maps_to_fun :=
  match goal with
  | [ H1 : Heap.MapsTo ?X (?V1, ?T1) ?H 
    , H2 : Heap.MapsTo ?X (?V2, ?T2) ?H
      |- _ ] =>
    let H := fresh "Eq" in     
    assert (H : (V1,T1) = (V2, T2)) by (eapply HeapFacts.MapsTo_fun; eauto);
    inv H
  | _ => idtac
  end.

Ltac solve_map :=
  match goal with
  | [ |- Heap.MapsTo ?x ?T (Heap.add ?x ?T _) ] => apply Heap.add_1; auto
  | _ => idtac
  end.


(*
Lemma HeapUpd:
  Suppose H(i) = n^T and G |- n'^T' : T' under heap H.
  If H' = H[i |--> k^T] and G |- k^T : T under H' then G |- n'^T' under heap H'
  (In short: H' |- H)
Proof.
  The proof is by induction on G |- n'^T' : T' under H.
  Case T-Int and T-VConst apply as before
  Case T-PtrC
    G |- n'^(ptr^c W) under H
    where
      types(D,W) = T0,...,T(j-1)
      G,n'^(ptr^c W) |-m H(n'+x) : Tx for 0 <= x < j under H
    We want to prove
      G,n'^(ptr^c W) |-m H'(n'+x) : Tx for 0 <= x < j under H'
    Two cases
      n'+x == i: So H'(i) = k^T and we are given G |- k^T under H'. Follows by weakening
      n'+x != i. So H'(i) = H(i) and the result follows by induction.
 *)

Definition set_equal (s1 s2 : scope) :=
  forall x, set_In x s1 <-> set_In x s2.

Lemma set_equal_add (s1 s2 : scope) (v : Z * type) :
  set_equal s1 s2 -> 
  set_equal (set_add eq_dec_nt v s1) (set_add eq_dec_nt v s2).
Proof.  
  intros Eq x.
  split; intros.
  - destruct (eq_dec_nt x v).
    + subst; apply set_add_intro2; auto.
    + apply set_add_intro1; auto.
      apply set_add_elim2 in H; eauto.
      apply Eq; auto.
  - destruct (eq_dec_nt x v).
    + subst; apply set_add_intro2; auto.
    + apply set_add_intro1; auto.
      apply set_add_elim2 in H; eauto.
      apply Eq; auto.
Qed.      

Lemma scope_replacement :
  forall D H s n t,
    @well_typed_lit D H s n t ->
  (forall s', 
    set_equal s s' ->
    @well_typed_lit D H s' n t).
Proof.
  intros D H ss n t HWT.
  induction HWT using well_typed_lit_ind'; eauto.
  - (* Replacement, TyRec *)
    intros s' HEq.
    econstructor; eauto; eapply HEq; eauto.
  - (* Replacement, TyLitC *)
    intros s' Heq.
    eapply TyLitC; eauto.
    intros k Hk.
    destruct (H1 k Hk) as [n' [t' [HNth [HMap [HWt1 HRepl]]]]].
    exists n'. exists t'.
    repeat (split; eauto).
    eapply HRepl; eauto.
    apply set_equal_add; auto.
Qed.

Lemma set_equal_add_add (s1 s2 : scope) (v1 v2 : Z * type) :
  set_equal s1 s2 -> 
  set_equal (set_add eq_dec_nt v1 (set_add eq_dec_nt v2 s1))
            (set_add eq_dec_nt v2 (set_add eq_dec_nt v1 s1)).
Proof.  
  intros Eq x.
  split; intros;
    destruct (eq_dec_nt x v1); destruct (eq_dec_nt x v2); subst;
      try solve [apply set_add_intro2; auto];
      try solve [apply set_add_intro1; auto;
                 apply set_add_intro2; auto];
    (do 2 (apply set_add_intro1; auto);
     do 2 (apply set_add_elim2 in H; auto)).
Qed.

Lemma set_equal_refl (s : scope) : set_equal s s.
  intros x; split; auto.
Qed.

Lemma scope_weakening :
  forall D H s n t,
    @well_typed_lit D H s n t ->
  forall x,
    @well_typed_lit D H (set_add eq_dec_nt x s) n t.
Proof.
  intros D H ss n t HWT.
  induction HWT using well_typed_lit_ind'; eauto.
  - (* Weakening, TyRec *)
    intros x.
    econstructor.
    apply set_add_intro1; eauto.
  - (* Weakening, TyLitC *)
    intros x.
    eapply TyLitC; eauto.
    intros k Hk.
    destruct (H1 k Hk) as [n' [t' [HNth [HMap [HWt1 HWeak]]]]].
    exists n'. exists t'.
    repeat (split; eauto).
    eapply scope_replacement; [eapply HWeak; eauto |].
    eapply set_equal_add_add; eauto.
    eapply set_equal_refl; eauto.
Qed.

Lemma set_equal_add_cons :
  forall x y s,
      set_equal (x :: set_add eq_dec_nt y s)
                (set_add eq_dec_nt y (x :: s)).
Proof.
  intros x y s z; split; intros H;
  destruct (eq_dec_nt z y); destruct (eq_dec_nt z x);
    subst; try congruence.
  - apply set_add_intro2; auto.
  - apply set_add_intro2; auto.
  - apply set_add_intro1; left; auto.
  - inv H; try congruence.
    apply set_add_elim in H0.
    inv H0; try congruence.
    apply set_add_intro1; auto.
    right; auto.
  - left; auto. 
  - right; apply set_add_intro2; auto.
  - left; auto.
  - apply set_add_elim in H.
    inv H; try congruence.
    inv H0; try congruence.
    right; apply set_add_intro1; auto.
Qed.

Lemma scope_weakening_cons :
  forall D H n t s,
    @well_typed_lit D H s n t ->
  forall x, @well_typed_lit D H (x :: s) n t.
Proof.
  intros D H n t s HWT.
  induction HWT using well_typed_lit_ind'; eauto; intros x.
  - econstructor.
    right; eauto.
  - eapply TyLitC; eauto.
    intros k Hk.
    destruct (H1 k Hk) as [n' [t' [HNth [HMap [HWt1 HWeak]]]]].
    exists n'. exists t'.
    repeat (split; eauto).
    eapply scope_replacement; [eapply (HWeak x); eauto |].
    apply set_equal_add_cons.
Qed.

Corollary scope_weakening' :
  forall D H n t,
    @well_typed_lit D H empty_scope n t ->
  forall s, @well_typed_lit D H s n t.
Proof.  
  intros D H n t HWT s.
  induction s; auto.
  apply scope_weakening_cons; auto.
Qed.  
  
  (*
Lemma scope_wf_heap_consistent_weakening :
  forall s D H x v T v',
    Heap.MapsTo x (v,T) H ->
    scope_wf D H s -> scope_wf D (Heap.add x (v',T) H) s.
Proof.
  intros s D H x v T v' HMap HSwf.
  intros x' t' HS.
  destruct (HSwf x' t'); eauto.
  destruct (Nat.eq_dec x x').
  - subst; maps_to_fun.
    exists v'.
    eapply Heap.add_1; eauto.
  - exists x0.
    eapply Heap.add_2; eauto.
Qed.

Hint Resolve scope_wf_heap_consistent_weakening.
 *)
     
Lemma HeapUpd : forall D i n T H k,
  Heap.MapsTo i (n,T) H ->
  @well_typed_lit D (Heap.add i (k,T) H) empty_scope k T ->
  @heap_consistent D (Heap.add i (k,T) H) H.
Proof.
  intros D i n T H k HMap Hwtk n' t' HWT.
  induction HWT using well_typed_lit_ind'; eauto.
  (* T-PtrC *)
  eapply TyLitC; eauto.
  intros x Hx.
  destruct (H1 x Hx) as [n' [t' [HNth [HMap' [HWt1 HWt2]]]]].
  destruct (Z.eq_dec (n0+x) i).
  - exists k. exists t'.
    subst. maps_to_fun.
    repeat (split; eauto).
    + apply Heap.add_1; eauto.
    + apply scope_weakening; eauto.
  - exists n'. exists t'.
    repeat (split; eauto).
      + apply Heap.add_2; eauto.
      + eapply HWt2.
        eapply scope_weakening; eauto.
Qed.

Hint Constructors value.

Lemma types_are_not_infinite :
  forall w, TPtr Checked w = w -> False.
Proof.
  induction w; intros; try congruence.
Qed.

(* Custom remove to avoid NoDup? *)
Fixpoint set_remove_all v (x : scope) := 
    match x with
    | nil => empty_scope
    | v' :: vs => if eq_dec_nt v v' then
                    set_remove_all v vs
                  else
                    v' :: set_remove_all v vs
    end.

Lemma set_remove_all_intro : forall a b l,
    set_In a l -> a <> b -> set_In a (set_remove_all b l).
Proof.
  intros a b l.
  induction l; intros; simpl.
  - inv H.
  - destruct (eq_dec_nt b a0).
    + subst.
      inv H; try congruence.
      eapply IHl; eauto.
    + destruct (eq_dec_nt a a0).
      * subst; left; auto.
      * inv H; try congruence.
        simpl.
        right.
        eauto.
Qed.

Lemma set_remove_all_elim1:
  forall a b l, set_In a (set_remove_all b l) -> a <> b.
Proof.  
  intros; induction l.
  - inv H.
  - intro Contra; subst.
    simpl in H.
    destruct (eq_dec_nt b a0).
    + subst.
      apply IHl; eauto.
    + simpl in *.
      inv H; try congruence.
      eapply IHl; eauto.
Qed.

Lemma set_remove_all_elim2:
  forall a b l, set_In a (set_remove_all b l) -> set_In a l.
Proof.
  intros; induction l.
  - inv H.
  - simpl in H.
    destruct (eq_dec_nt b a0).
    + subst.
      right; apply IHl; eauto.
    + simpl in *.
      inv H.
      * left; auto.
      * right; eapply IHl; eauto.
Qed.
  
Lemma set_equal_add_remove (s : scope) (v1 v2 : Z * type) :
  v1 <> v2 ->
  set_equal (set_add eq_dec_nt v1 (set_remove_all v2 s))
            (set_remove_all v2 (set_add eq_dec_nt v1 s)).
Proof.
  intros H x.
  split; intro In.
  * destruct (eq_dec_nt x v1); destruct (eq_dec_nt x v2); try congruence; subst;
      unfold not in *.
    - apply set_remove_all_intro; eauto.
      apply set_add_intro2; auto.
    - apply set_add_elim in In; destruct In; try congruence.
      eapply set_remove_all_elim1 in H0.
      congruence.
    - apply set_remove_all_intro; eauto.
      apply set_add_elim in In; destruct In; try congruence.
      apply set_remove_all_elim2 in H0.
      apply set_add_intro1; auto.
  * destruct (eq_dec_nt x v1); destruct (eq_dec_nt x v2); try congruence; subst.
    - apply set_add_intro2; auto.
    - apply set_remove_all_elim1 in In.
      try congruence.
    - apply set_remove_all_elim2 in In.
      apply set_add_elim in In.
      inv In; try congruence.
      apply set_add_intro1; auto.
      apply set_remove_all_intro; eauto.
Qed.      

Definition type_eq_dec (t1 t2 : type): {t1 = t2} + {~ t1 = t2}.
  repeat decide equality.
Defined.

Lemma set_remove_add :
  forall x s, set_equal (set_remove_all x (set_add eq_dec_nt x s)) (set_remove_all x s).
Proof.
  intros x s y; split; intros H; destruct (eq_dec_nt x y); subst; eauto.
  - apply set_remove_all_elim1 in H; congruence.
  - apply set_remove_all_elim2 in H.
    apply set_add_elim in H.
    inv H; try congruence.
    apply set_remove_all_intro; auto.
  - apply set_remove_all_elim1 in H; congruence.
  - apply set_remove_all_intro; auto.
    apply set_remove_all_elim2 in H.
    apply set_add_intro1; auto.
Qed.

Lemma set_equal_symmetry : forall (s1 s2 : scope),
    set_equal s1 s2 -> set_equal s2 s1.
Proof.  
  intros s1 s2 Eq x; split; intro H;
  apply Eq; auto.
Qed.  
  
Lemma scope_swap :
  forall D H x y s N T,
    @well_typed_lit D H (set_remove_all x (set_add eq_dec_nt y s)) N T ->
    @well_typed_lit D H (set_add eq_dec_nt y (set_remove_all x s)) N T.
Proof.
  intros D H x y s N T HWT.
  destruct (eq_dec_nt x y).
  - subst.
    pose proof (set_remove_add y s).
    apply scope_replacement with (s' := set_remove_all y s) in HWT; auto.
    apply scope_weakening; auto.
  - assert (Neq: y <> x) by auto.
    pose proof (set_equal_add_remove s y x Neq) as Hyp.
    eapply scope_replacement.
    + eapply HWT.
    + apply set_equal_symmetry.
      auto.
Qed.




Lemma scope_strengthening :
  forall D H n tn s,
    @well_typed_lit D H s n tn ->
    heap_wf D H ->
    forall m tm,
      @well_typed_lit D H empty_scope m tm ->
      @well_typed_lit D H (set_remove_all (m, tm) s) n tn.
Proof.
  intros D H n' t s HWT.
  remember HWT as Backup; clear HeqBackup.
  induction HWT using well_typed_lit_ind';
  (* intros HHwf m HMap HSetIn HWT; eauto. *)
    intros HHwf m tm Hwt; eauto.
  - destruct (Z.eq_dec n m).
    + subst.
      destruct (type_eq_dec tm (TPtr Checked w)).
      * subst. 
        apply scope_weakening'; eauto.
      * econstructor; eauto.
        apply set_remove_all_intro; eauto.
        intro Contra; inv Contra. eauto.
    + econstructor.
      apply set_remove_all_intro; eauto.
      congruence.
  - eapply TyLitC; eauto.
    intros k Hk.
    destruct (H1 k Hk) as [N [T [HNth [HMap' [Hwt' IH]]]]].

    exists N; exists T; eauto.
    repeat (split; eauto).

    specialize (IH Hwt' HHwf m tm Hwt).
    apply scope_swap; auto.
Qed.


Lemma preservation_fieldaddr : forall (D : structdef) H n T (fs : fields),
  @well_typed_lit D H empty_scope n (TPtr Checked (TStruct T)) ->
  forall i fi ti,
  n <> 0 ->
  StructDef.MapsTo T fs D ->
  Fields.MapsTo fi ti fs ->
  nth_error (Fields.this fs) i = Some (fi, ti) ->
  heap_wf D H ->
  structdef_wf D ->
  fields_wf D fs ->
  word_type ti ->
  @well_typed_lit D H empty_scope (n + (Z.of_nat i)) (TPtr Checked ti).
Proof.
  intros D H n T fs HWT.
  inversion HWT;
  intros i fi ti Hn HS HF Hnth Hhwf HDwf Hfwf Hwt; eauto.
  - exfalso ; eauto.
  - destruct (H4  (Z.of_nat i)) as [N' [T' [HNth [HMap HWT']]]]; subst.
    + inv H1.
      simpl in H2.
      destruct (StructDef.find T D) eqn:Find; try congruence.
      inv H2.
      rewrite map_length.
      apply StructDef.find_2 in Find.
      assert (f = fs).
      { eapply StructDefFacts.MapsTo_fun; eauto. }
      subst.
      apply nth_length in Hnth.
      rewrite <- Fields.cardinal_1.
      eauto.
    + inv H1.
      simpl in *.
      destruct (@StructDef.find _ T D) eqn:Find; try congruence.
      inv H2.

      apply StructDef.find_2 in Find.
      assert (f = fs).
      { eapply StructDefFacts.MapsTo_fun; eauto. }
      subst.

      eapply map_nth_error with (f := snd) in Hnth.
      assert (Hyp: Fields.this fs = Fields.elements fs) by auto.
      rewrite Hyp in Hnth.

      (* I hate these types... *)
      assert (
          Hnth' : @eq (option type)
                      (@nth_error type
              (@map (prod Fields.key type) type (@snd Fields.key type)
                 (@Fields.elements type fs)) i)
           (@Some type (@snd nat type (@pair Fields.key type fi ti)))
        ) by auto.
      assert (Hi : (Z.to_nat (Z.of_nat i)) = i). {
        destruct i.
          +simpl. reflexivity.
          +simpl. zify. lia. }
      simpl in *.
      rewrite Z.sub_0_r in *. rewrite Hi in HNth.
      rewrite <- HNth in Hnth'.
      inv Hnth'.
      inv Hwt.
      * eapply TyLitC; simpl in *; eauto.
        intros k Hk; simpl in *.
        assert (k = 0) by lia; subst.
        exists N'. exists TNat.
        repeat (split; eauto).
        rewrite Z.add_0_r; eauto.
      * unfold fields_wf in Hfwf.
        apply Hfwf in HF. destruct HF. destruct H1.
        eapply TyLitC; simpl in *; eauto.
        intros k Hk; simpl in *.
        assert (k = 0) by lia; subst.
        exists N'. exists (TPtr m w).
        repeat (split; eauto).
        rewrite Z.add_0_r; eauto.

        assert (HEmpty : empty_scope = set_remove_all (n, TPtr Checked (TStruct T))
                                             ((n, TPtr Checked (TStruct T)) :: nil)).
        { unfold set_remove_all.
          destruct (eq_dec_nt (n, TPtr Checked (TStruct T)) (n, TPtr Checked (TStruct T))); auto.
          congruence.
        }

        eapply scope_strengthening in HWT'; eauto.
        rewrite <- HEmpty in HWT'.
        apply scope_weakening_cons.
        auto.

Qed.

(*

Def: H' |- H iff for all i
  H(i) = n^T such that . |- n^T : T under H implies
  H'(i) = n'^T such that . |- n'^T : T under H'.

Lemma PtrUpdA:
  Suppose H(i) = n^T and G |- n'^T' : T' under heap H.
  Then H' = H[i |--> k^T] implies that G,k^T |- n'^T' under heap H'
    when T = ptr^c W (i.e., it's a checked pointer type)
Proof
  Proof by induction on G |- n'^T' : T' under heap H.
  Case T-Int: Then T'=int and G,k^T |- n'^int under heap H' by T-Int
  Case T-VConst: Then G,k^T |- n'^T' under heap H' by T-VConst as well (since n'^T' \in G)
  Case T-PtrC: Three cases:
    n'^T' = k^T. Follows from T-VConst
    Otherwise
      T' = ptr^c W'
      types(D,W') = T0,...,T(j-1)
      G,n'^(ptr^c W') |-m H(n'+x) : Tx for 0 <= x < j under H
    We want to show
      G,n'^(ptr^c W'),k^T |-m H(n'+x) : Tx for 0 <= x < j under H'
    When n'+x != i then the result follows from T-Int, T-VConst, or T-PtrC and induction.
    When n'+x = i it follows by H-Visited, since H'(i) = k^T and k^T \in G,k^T
      (and H(i) = n^T --- that is the old and new value had the same annotation)
*)

Lemma PtrUpdA :
  forall D H s n' T',
    @well_typed_lit D H s n' T' ->
    forall i k m w,
      Heap.MapsTo i (m,TPtr Checked w) H ->
      @well_typed_lit D (Heap.add i (k,TPtr Checked w) H) (set_add eq_dec_nt (k,TPtr Checked w) s) n' T'.
Proof.
  intros D H s n' T' HWT'.
  remember HWT' as Backup; clear HeqBackup.
  induction HWT' using well_typed_lit_ind'; eauto;
    intros i k m T HMap.
  - econstructor.
    apply set_add_intro; eauto.
  - eapply TyLitC; eauto.
    intros x Hx.
    destruct (H1 x Hx) as [N' [T' [HNth [HMap' [HWT'' IH]]]]].
    destruct (Z.eq_dec (n + x) i).
    + subst.
      maps_to_fun.
      exists k; exists (TPtr Checked T); eauto.
      repeat (split; eauto).
      * apply Heap.add_1; eauto.
      * eapply TyLitRec; auto.
        apply set_add_intro1;
        apply set_add_intro2; auto. 
    + exists N'; exists T'; eauto.
      repeat (split; eauto).
      * apply Heap.add_2; auto.
      * eapply scope_replacement; eauto.
        eapply set_equal_add_add; eauto.
        eapply set_equal_refl.
Qed.
        (*
Lemma A: If G |- n^T : T where T = Ptr^c W such that W is an array
or word type, then G |- H(n) : T' where types(D,W) = T',...
Proof by induction on G |- n^T.
We have G,n^T |- H(n) : T' by inversion on H-PtrC. Consider the
derivation of this, and let k^T' = H(n).
  H-Int: Then G |- k^Int : Int as well
  H-Visited: There are two cases:
   k^T' \in G: In that case G |- k^T' : T' by H-Visited
   k^T' = n^T: In this case we can simply reuse the derivation we were
   given, i.e., G |- n^T : T.
 H-PtrC: Holds by induction.



Corollary PtrUpd:
  Suppose H(i) = n^T and G |- n'^T : T under heap H.
  Then H' = H[i |--> n'^T] implies that G |- n'^T under heap H'
Proof.
  If T is not a checked pointer it follows directly (same logic is PtrUpdA)
  Else by inversion we have
      T = ptr^c W 
      types(D,W) = T0,...,T(j-1)
      G,n'^(ptr^c W) |-m H(n'+k) : Tk for 0 <= k < j under H
    We want to prove
      G,n'^(ptr^c W) |-m H'(n'+k) : Tk for 0 <= k < j under H'
    Two cases
      n'+k == i. Then H'(i) = n'^T. The result follows from T-VConst.
      n'+k != i. Then H'(n'+k) = H(n'+k) = n''^Tk.
        By Lemma A we have G |-m H(n'+k) : Tk for 0 <= k < j under H
        By PtrUpdA we have G, n'^(ptr^c W) |-m H'(n'+k) : Tk for 0 <= k < j under H'

 *)

Inductive stack_wf D H : env -> stack -> Prop :=
  | WFS_Stack : forall env s,
     (forall x t,
         Env.MapsTo x t env ->
         exists v t' t'',
           cast_type_bound s t t' /\
           subtype D t'' t' /\
            Stack.MapsTo x (v, t'') s /\
            simple_type t'' /\
            @well_typed_lit D H empty_scope v t'')
   /\ (forall x v t,
             Stack.MapsTo x (v, t) s -> simple_type t ->
                   @well_typed_lit D H empty_scope v t    
          -> exists t' t'',
                @Env.MapsTo type x t' env /\ cast_type_bound s t' t''
                   /\ subtype D t t'')
 ->
     stack_wf D H env s.


Lemma PtrUpd : forall i n T H D n',
    heap_wf D H ->
    simple_type T ->
    Heap.MapsTo i (n, T) H ->
    @well_typed_lit D H empty_scope n' T ->
    @well_typed_lit D (Heap.add i (n',T) H) empty_scope n' T.
Proof.
  intros i n T H D n' Hwf HSimple HMap HWT.
  remember HWT as Backup; clear HeqBackup.
  inv HWT; eauto.
  eapply TyLitC; eauto.
  intros x Hx.
  destruct (H1 x Hx) as [x' [Tx [HNth [HMap' HWt1]]]].

  destruct (Z.eq_dec (n'+x) i).
  - subst.
    maps_to_fun.
    exists n'. exists (TPtr Checked w).
    repeat (split; eauto).
    + solve_map.
    + eapply TyLitRec; eauto.
      apply set_add_intro2; auto. 
  - exists x'. exists Tx.
    repeat (split; eauto).
    + eapply Heap.add_2; eauto.
    + eapply PtrUpdA; eauto.

      assert (HEmpty : empty_scope = set_remove_all (n', TPtr Checked w)
                                                    ((n', TPtr Checked w) :: nil)).
      {
        unfold set_remove_all.
        destruct (eq_dec_nt (n', TPtr Checked w) (n', TPtr Checked w)); auto.
        congruence.
      } 

      rewrite HEmpty.
      eapply scope_strengthening; eauto.
Qed.

Lemma well_typed_heap_in : forall n D H w,
  heap_wf D H ->
  Heap.In n H ->
  word_type w ->
  @well_typed_lit D H empty_scope n (TPtr Checked w) ->
  exists x, Heap.MapsTo n (x, w) H.
Proof.
  intros n D H w Hwf HIn Hwt HWT.
  inv HWT.
  - destruct (Hwf 0) as [_ Contra].
    apply Contra in HIn.
    lia.
  - inv H3. 
  - inv Hwt; simpl in *; inv H1.
    + destruct (H4 0) as [n' [t' [HNth [HMap HWT]]]]; auto.
      *simpl. lia.
      *
      rewrite Z.add_0_r in HMap.
      inv HNth.
      exists n'; eauto.
    + destruct (H4 0) as [n' [t' [HNth [HMap HWT]]]]; auto.
      *simpl. lia.
      *rewrite Z.add_0_r in HMap.
       inv HNth.
       exists n'; eauto.
Qed.

Lemma well_typed_heap_in_array : forall n D H l h w,
  heap_wf D H ->
  Heap.In n H ->
  h > 0 ->
  l <= 0 ->
  @well_typed_lit D H empty_scope n (TPtr Checked (TArray (Num l) (Num h) w)) ->
  exists x, Heap.MapsTo n (x, w) H.
Proof.
  intros n D H l h w Hwf HIn Hl Hh HWT.
  inv HWT.
  - destruct (Hwf 0) as [_ Contra].
    apply Contra in HIn.
    lia.
  - inv H3.
  - inv H1.
    destruct l.
    + destruct (H4 0) as [n' [t' [HNth [HMap HWT]]]]; auto.
      * simpl. destruct h; inv Hl. simpl.
        assert (Hyp : exists s, Pos.to_nat(p) = S s).
        { apply pos_succ. }
        inv Hyp.
        rewrite replicate_length.
        simpl. lia.
      * rewrite Z.sub_0_r in *.
        inv HNth.
        exists n'; eauto.
        assert (H3 : t' = w). {
          destruct h; inv Hl. inv H1. 
          assert (HP: exists s, Pos.to_nat(p) = S s) by apply pos_succ.
          inv HP.
          rewrite H0 in H2. simpl in H2. inv H2. reflexivity.
        }
        rewrite <- H3. rewrite Z.add_0_r in *. assumption.
    + zify; lia.
    + assert (H1: (h - (Z.neg p)) > 0) by (zify; lia).
      assert (H2: exists n, (h - (Z.neg p)) = Z.pos n). {
        destruct (h - (Z.neg p)); inv H1. exists p0. reflexivity.
      }
      destruct H2 as [pos Hpos].
      assert (Hpos': exists n, Pos.to_nat pos = S n) by apply pos_succ.
      destruct Hpos' as [N HN].
      destruct (H4 0) as [n' [t' [HNth [HMap HWT]]]]; auto.
      rewrite Hpos. simpl. rewrite HN.
      rewrite replicate_length.
      simpl. split.
        * zify. lia.
        * rewrite Z.pos_sub_gt. 
          { zify. lia. }
          { zify. lia. }
        * rewrite Z.add_0_r in HMap.
          rewrite Hpos in HNth. simpl in HNth.
          rewrite HN in HNth. 
          assert (w = t').
              {
                eapply replicate_nth; eauto.
              }
              subst w.
          exists n'. assumption.
Qed.

Lemma add_one_not_change :
   forall x0 s,
      (forall x v t, Stack.MapsTo x (v,t) (add_nt_one s x0) -> simple_type t)
     -> (forall x v t, Stack.MapsTo x (v,t) s -> simple_type t).
Proof.
  intros.
  destruct (var_eq_dec x x0). subst.
  destruct t. apply SPTNat.
  destruct t. apply SPTPtr. apply SPTNat.
  apply (H x0 v (TPtr m (TPtr m0 t))).
  unfold add_nt_one.
  specialize (@Stack.find_1 (Z * type)s x0 (v,TPtr m (TPtr m0 t)) H0) as eq1.
  destruct (Stack.find (elt:=Z * type) x0 s). destruct p.
  inv eq1. assumption. inv eq1.
  apply SPTPtr. apply SPTStruct.
  apply (H x0 v (TPtr m (TArray b b0 t))).
  unfold add_nt_one.
  specialize (@Stack.find_1 (Z * type)s x0 (v, TPtr m (TArray b b0 t)) H0) as eq1.
  destruct (Stack.find (elt:=Z * type) x0 s). destruct p.
  inv eq1. assumption. inv eq1.
  destruct b0.
  assert (Stack.MapsTo x0
        (v, TPtr m (TNTArray b (Num (z + 1)) t))
        (add_nt_one s x0)).
  unfold add_nt_one.
  specialize (@Stack.find_1 (Z * type)s x0 (v, TPtr m (TNTArray b (Num z) t)) H0) as eq1.
  destruct (Stack.find (elt:=Z * type) x0 s).
  inv eq1.
  apply Stack.add_1. reflexivity. inv eq1.
  apply H in H1.
  inv H1. inv H3.
  apply SPTPtr. apply SPTNTArray. assumption.
  assert (Stack.MapsTo x0
        (v, TPtr m (TNTArray b (Var v0 (z + 1)) t))
        (add_nt_one s x0)).
  unfold add_nt_one.
  specialize (@Stack.find_1 (Z * type)s x0 (v, TPtr m (TNTArray b (Var v0 z) t)) H0) as eq1.
  destruct (Stack.find (elt:=Z * type) x0 s).
  inv eq1.
  apply Stack.add_1. reflexivity. inv eq1.
  apply H in H1.
  inv H1. inv H3.
  apply SPTStruct.
  apply (H x0 v (TArray b b0 t)).
  unfold add_nt_one.
  specialize (@Stack.find_1 (Z * type)s x0 (v, TArray b b0 t) H0) as eq1.
  destruct (Stack.find (elt:=Z * type) x0 s).
  inv eq1. assumption. inv eq1.
  apply (H x0 v (TNTArray b b0 t)).
  unfold add_nt_one.
  specialize (@Stack.find_1 (Z * type)s x0 (v, TNTArray b b0 t) H0) as eq1.
  destruct (Stack.find (elt:=Z * type) x0 s).
  inv eq1. assumption. inv eq1.
  apply (H x v t).
  unfold add_nt_one.
  destruct (Stack.find (elt:=Z * type) x0 s). destruct p.
  destruct t0.
  assumption.
  destruct t0. 1 - 4 : assumption.
  destruct b0.
  apply Stack.add_2. lia. assumption.
  apply Stack.add_2. lia. assumption.
  1 - 4 : assumption.
Qed.

(*
Lemma simple_type_step : forall D H s e s' H' r, (forall x v t, Stack.MapsTo x (v,t) s -> simple_type t)
                                    -> step D s H e s' H' r -> (forall x v t, Stack.MapsTo x (v,t) s' -> simple_type t).
Proof.
  intros. induction H1; eauto.
  destruct (var_eq_dec x x0).
  rewrite e0 in H2.
  apply Stack.mapsto_add1 in H2.
  injection H2. intros.
  subst.
  apply cast_means_simple_type in H1. assumption.
  apply Stack.add_3 in H2.
  apply (H0 x v). assumption. lia.
  specialize (add_one_not_change x0 s H0 x v t) as eq1.
  apply eq1. assumption.
Qed.
*)

Lemma well_bound_grow_env :
    forall env x v b, well_bound_in env b -> well_bound_in (Env.add x v env) b.
Proof.
   intros. induction b.
   apply well_bound_in_num.
   apply well_bound_in_var.
   inv H. inv H2.
   destruct (var_eq_dec x v0).
   unfold Env.In,Env.Raw.PX.In.
   exists v. apply Env.add_1. assumption.
   unfold Env.In,Env.Raw.PX.In.
   exists x0.
   apply Env.add_2. assumption. assumption.
Qed.

Lemma well_type_bound_grow_env :
    forall env x v t, well_type_bound_in env t -> well_type_bound_in (Env.add x v env) t.
Proof.
   intros. induction t.
   apply well_type_bound_in_nat.
   apply well_type_bound_in_ptr.
   apply IHt. inv H. assumption.
   apply well_type_bound_in_struct.
   apply well_type_bound_in_array.
   apply well_bound_grow_env. inv H. assumption.
   apply well_bound_grow_env. inv H. assumption.
   inv H. apply IHt. assumption.
   apply well_type_bound_in_ntarray.
   apply well_bound_grow_env. inv H. assumption.
   apply well_bound_grow_env. inv H. assumption.
   inv H. apply IHt. assumption.
Qed.

Lemma cast_bound_well_type : forall D F S H m env v t t', cast_type_bound S t t'
                 -> @well_typed D F S H env m (ELit v t) t -> @well_typed D F S H env m (ELit v t') t'.
Proof.
  intros. inv H1. apply TyLit.
  apply cast_means_simple_type in H0.
  apply (simple_type_well_bound env0) in H0.
  assumption. remember empty_scope as scope.
  eapply WTStack. apply (simple_type_means_cast_same).
  apply cast_means_simple_type in H0. assumption.
  inv H8.
  apply (cast_type_bound_same S t t' t'0) in H0.
  subst. apply cast_means_simple_type in H1.
  remember empty_scope as sc.
  induction H2 using well_typed_lit_ind'.
  apply TyLitInt.
  apply TyLitU.
  apply TyLitZero.
  subst. inv H0.
  eapply TyLitC;eauto.
    intros k Hk.
    destruct (H2 k Hk) as [N [T [HNth [HMap' [Hwt' IH]]]]].
    exists N. exists T.
    easy.
  assumption.
Qed.

  (*
  Lemma mt : forall D H env,
      stack_wf D H env Empty.
  Proof.
    intros D H env. constructor.
    intros x t v m H1 H2.
    induction x; simpl in H2; inv H2.
  Qed.

  
  Lemma add_stack : forall s x t1 D H n t0 env,
      stack_wf D H env s ->
       @well_typed D H env Checked (ELit n t0) t1 ->
  stack_wf D H (Env.add x t1 env) (Stack (ELit n t0) s).
  Proof.
    intros s x t1 D H n t0 env' Hswf Hwt.
    apply WFS_Stack. intros x0 t v m H1 H2.
    inv Hswf. *)

   
Inductive env_consistent : env -> env -> Prop :=
  |Env_refl : forall e,
      env_consistent e e
  |Env_add : forall e x t,
      ~ Env.In x e ->
      env_consistent (Env.add x t e) e.

Definition ty_ssa_stack (S:stack) (e:expression) 
            := exists l, (forall x,  Stack.In x S -> In x l) /\ (exists l', ty_ssa l e l').

(* Defining stack. *)
Lemma ty_ssa_preserve' : forall D F S H S' H' e e', 
           ty_ssa_stack S e
          -> step D F S H e S' H' (RExpr e') -> ty_ssa_stack S' e'.
Proof.
 unfold ty_ssa_stack in *.
 intros.
 induction e;eauto; destruct H0;destruct H0.
 - inv H1. 
 - inv H1.
   exists x. split. easy.
   exists x.
   apply ty_ssa_lit.
 - inv H1. unfold change_strlen_stack.
   destruct (n' - n <=? h) eqn:eq1.
   exists x.
   intros. split. apply H0.
   exists x. apply ty_ssa_lit.
   exists x. split. 
   intros.
   apply H0.
   unfold Stack.In,Stack.Raw.PX.In in *.
   destruct H.
   destruct (Nat.eq_dec x0 v). subst.
   exists ((n, TPtr m (TNTArray l (Num h) t))).
   apply Stack.find_2. assumption.
   apply Stack.add_3 in H. exists x1. assumption. lia.
   exists x. apply ty_ssa_lit.
 - admit.
 - admit.
 - admit. 

(*inv H1. inv H2.
   exists (v::x).
   split.
   intros.  
   destruct (Nat.eq_dec x1 v).
   subst. apply in_eq.
   apply in_cons. apply H0.
   unfold Stack.In,Stack.Raw.PX.In in *.
   destruct H1.
   apply Stack.add_3 in H1.
   exists x2. assumption. lia.
   inv H. exists x0. inv H7. assumption.
   - inv H1. exists x.
     split.  easy. exists x. easy.
   - inv H1. exists x.
     split.  easy. exists x. easy.
     exists x.
     split.  easy. exists x. easy.
     exists x.
     split.  easy. exists x. easy.
     exists x.
     split.  easy. exists x. easy.
   - inv H1. exists x.
     split.  easy. exists x. easy.
     exists x.
     split.  easy. exists x. easy.
   - inv H1. exists x.
     split.  easy. exists x. easy.
     exists x.
     split.  easy. exists x. easy.
   - inv H1. exists x.
     split.  easy. exists x. easy.
   - inv H1. exists x.
     split.  easy. exists x. easy.
   - inv H1. 
     exists x. split.  easy.
     destruct H2. inv H. exists S'0. easy.
     exists x. split. intros.
     apply H0.
     unfold Stack.In, Stack.Raw.PX.In in *.
     destruct H.
     destruct (Nat.eq_dec x0 v).
     subst.
     unfold add_nt_one.
     specialize (@Stack.find_1 (Z * type) S' v x1 H) as eq1.
     destruct (Stack.find (elt:=Z * type) v S').
     inv eq1.
     destruct x1. destruct t0.
     exists (z, TNat). easy.
     destruct t0. exists (z, TPtr m TNat). easy.
     exists (z, TPtr m (TPtr m0 t0)). easy.
     exists (z, TPtr m (TStruct s)). easy.
     exists (z, TPtr m (TArray b b0 t0)). easy.
     destruct b0.
     exists (z, TPtr m (TNTArray b (Num (z0 + 1)) t0)).
     apply Stack.add_1. easy.
     exists ((z, TPtr m (TNTArray b (Var v0 (z0 + 1)) t0))).
     apply Stack.add_1. easy.
     exists ((z, TStruct s)). easy.
     exists (z, TArray b b0 t0). easy.
     exists (z, TNTArray b b0 t0). easy.
     exists x1. easy.
     exists x1.
     unfold add_nt_one.
     destruct (Stack.find (elt:=Z * type) v S').
     destruct p. destruct t0.
     assumption.
     destruct t0. assumption. assumption.
     assumption. assumption.
     destruct b0.
     apply Stack.add_2. lia. assumption.
     apply Stack.add_2. lia. assumption.
     assumption. assumption. assumption. assumption.
     destruct H2. inv H.
     exists S'0. assumption.
     destruct H2. inv H.
     exists S'0. split.
     intros.
     apply ty_ssa_grow in H6.
     apply H0 in H.
     unfold list_subset in H6.
     apply H6. assumption.
     exists x0. assumption.
     unfold is_rexpr in H13. contradiction.
   - inv H1. exists x.
     split.  easy. exists x. easy.
*)
Admitted.

Definition stack_grow (D: structdef) (S S' : stack) :=
     (forall x v t, Stack.MapsTo x (v,t) S
              -> (exists t', (subtype D t' t) /\ Stack.MapsTo x (v,t') S')).


Lemma stack_grow_prop : forall D F S H S' H' e e', 
           ty_ssa_stack S e
          -> step D F S H e S' H' (RExpr e') -> stack_grow D S S'.
Proof.
(*
 intros.
 specialize (ty_ssa_preserve' D S H S' H' e e' H0 H1) as eq1.
 remember (RExpr e') as e1.
 unfold stack_grow. intros.
 induction H1.
 exists t. split. constructor. easy.
 unfold change_strlen_stack in *.
 destruct ( n' - n <=? h) eqn:eq2.
 exists t. split. constructor. easy.
 assert (~ (n' - n <= h)).
 specialize (Z.leb_le (n' - n) h) as eq3.
 apply not_true_iff_false in eq2.
 intros R.
 apply eq3 in R. rewrite R in eq2. contradiction.
 assert (h < n' - n) by lia.
 destruct (Nat.eq_dec x x0).
 subst.
 apply Stack.find_1 in H2. rewrite H1 in H2. inv H2.
 exists (TPtr m (TNTArray l (Num (n' - v)) t0)).
 split. 
 apply SubTyNtSubsume.
 destruct l.
 constructor. lia. constructor. lia.
 constructor. lia.
 apply Stack.add_1. lia.
 exists t.
 split. constructor.
 apply Stack.add_2. lia. assumption.
 1 - 36 : exists t; split; try constructor; try easy.
 unfold ty_ssa_stack in H0.
 destruct H0. destruct H0.
 destruct H3.
 inv H3.
 destruct (Nat.eq_dec x x0).
 subst.
 assert (In x0 x1).
 apply H0.
 unfold Stack.In,Stack.Raw.PX.In.
 exists (v,t). assumption.
 contradiction.
 exists t. split. constructor.
 apply Stack.add_2. lia. assumption.
 1 - 5 : exists t; split; try constructor; try easy.
*)
Admitted.

(*

Lemma stack_grow_diff_var_1 : forall D S x v, stack_grow D S (Stack.add x v S)
                     -> ~ Stack.MapsTo x v S -> ~ Stack.In x S.
Proof.
  intros. unfold stack_grow in H.
  destruct v.
  specialize (H x z t) as eq1.
  intros R.
  unfold Stack.In,Stack.Raw.PX.In in R.
  destruct R.
  destruct x0.
  destruct (eq_dec_nt (z0, t0) (z, t)).
  inv e. contradiction.
  apply H in H1.
  destruct H1. destruct H1.
  apply Stack.mapsto_add1 in H2. inv H2. contradiction.
Qed.

Require Import Coq.Logic.Classical.

Lemma stack_grow_diff_var : forall S x v, stack_grow S (Stack.add x v S)
                               -> Stack.MapsTo x v S \/ ~ Stack.In x S.
Proof.
  intros.
  specialize (stack_grow_diff_var_1 S x v H) as eq1.
  Check classic.
  destruct (classic (Stack.MapsTo x v S)).
  left. assumption.
  apply eq1 in H0. right. assumption.
Qed.
*)

Lemma stack_grow_cast_same : forall D S S' b b', stack_grow D S S' ->
              cast_bound S b = Some b' -> cast_bound S' b = Some b'.
Proof.
  intros. unfold cast_bound in *.
  destruct b. assumption.
  destruct (Stack.find (elt:=Z * type) v S) eqn:eq1. destruct p.
  unfold stack_grow in H.
  apply Stack.find_2 in eq1. apply H in eq1.
  destruct eq1. destruct H1.
  apply Stack.find_1 in H2.
  destruct (Stack.find (elt:=Z * type) v S') eqn:eq2. destruct p.
  inv H2. assumption. inv H2. inv H0.
Qed.

Lemma stack_grow_cast_type_same : forall D S S' t t', stack_grow D S S' ->
              cast_type_bound S t t' -> cast_type_bound S' t t'.
Proof.
  intros.
  induction H0. apply cast_type_bound_nat.
  apply cast_type_bound_ptr. apply IHcast_type_bound.
  apply cast_type_bound_array.
  apply (stack_grow_cast_same D S). assumption.
  assumption.
  apply (stack_grow_cast_same D S). assumption.
  assumption.
  assumption.
  apply cast_type_bound_ntarray.
  apply (stack_grow_cast_same D S). assumption.
  assumption.
  apply (stack_grow_cast_same D S). assumption.
  assumption.
  assumption.
  apply cast_type_bound_struct.
Qed.

Lemma cast_type_well_typed_lit :
    forall D s H v t t', cast_type_bound s t t' -> 
      well_type_lit_stack D s H empty_scope v t -> 
       well_type_lit_stack D s H empty_scope v t'.
Proof. 
 intros. 
 inv H1.
 apply (cast_type_bound_same s t t' t'0) in H0.
 subst. eapply WTStack. apply (simple_type_means_cast_same).
 apply (cast_means_simple_type) in H2. assumption.
 assumption. assumption.
Qed.

Lemma stack_grow_well_typed_lit :
    forall D s s' H v t,
     stack_grow D s s' -> 
      well_type_lit_stack D s H empty_scope v t -> 
       well_type_lit_stack D s' H empty_scope v t.
Proof. 
 intros D s s' H v t Hgrow HWT.
 inv HWT.
 eapply WTStack.
 apply (stack_grow_cast_type_same D s).
 assumption. apply H0.
 assumption.
Qed.

Lemma stack_grow_type_eq :
   forall D s s' t t', stack_grow D s s' -> 
         type_eq s t t' -> type_eq s' t t'.
Proof.
 intros.
 induction H0.
 constructor.
 apply type_eq_left. apply H0.
 apply (stack_grow_cast_type_same D s). assumption. assumption.
 apply type_eq_right. apply H0.
 apply (stack_grow_cast_type_same D s). assumption. assumption.
Qed.

Lemma stack_grow_meet_type :
  forall D s s' t t1 t2, stack_grow D s s' 
         -> meet_type D s t t1 t2 -> meet_type D s' t t1 t2.    
Proof.
  intros. 
  induction H0; eauto.
  apply meet_type_front_1. assumption.
  eapply meet_type_front_2.
  apply (stack_grow_cast_type_same D s s').
  assumption. apply H0.
  apply (stack_grow_cast_type_same D s s').
  assumption. apply H1.
  apply H2.
  apply meet_type_end_1. assumption.
  eapply meet_type_end_2.
  apply (stack_grow_cast_type_same D s s').
  assumption. apply H0.
  apply (stack_grow_cast_type_same D s s').
  assumption. apply H1.
  apply H2.
Qed.

Lemma stack_grow_well_typed :
    forall D F s s' H env m e t,
     stack_grow D s s' -> 
      @well_typed D F s H env m e t -> 
       @well_typed D F s' H env m e t.
Proof. 
 intros D F s s' H env m e t Hgrow Hwf.
 induction Hwf;eauto.
 constructor. assumption.
 apply (stack_grow_well_typed_lit D s s').
 assumption. assumption.
 eapply TyCall. apply H0.
(*
 eapply TyCast2. 
 apply (stack_grow_type_eq D s s') in H0.
 apply H0. assumption.
 assumption.
 apply IHHwf.
 eapply TyCast3. 
 apply (stack_grow_type_eq D s s') in H0.
 apply H0. assumption.
 assumption.
 apply IHHwf.
 eapply TyCast4. 
 apply (stack_grow_type_eq D s s') in H0.
 apply H0. assumption.
 assumption.
 apply IHHwf.
 eapply TyAssign1.
 apply H0. assumption.
 apply (stack_grow_type_eq D s s'). assumption.
 assumption. apply IHHwf1.
 apply IHHwf2.
 assumption.
 eapply TyAssign2.
 apply H0. assumption. 
 apply (stack_grow_type_eq D s s'); assumption.
 apply IHHwf1.
 apply IHHwf2.
 assumption.
 eapply TyAssign3.
 apply H0. assumption. 
 apply (stack_grow_type_eq D s s'); assumption.
 apply IHHwf1.
 apply IHHwf2.
 assumption.
 eapply TyIndexAssign1. assumption. assumption.
 apply IHHwf1.
 apply (stack_grow_type_eq D s s'); assumption.
 apply IHHwf2. apply IHHwf3. assumption.
 eapply TyIndexAssign2. assumption. assumption.
 apply IHHwf1.
 apply (stack_grow_type_eq D s s'); assumption.
 apply IHHwf2. apply IHHwf3. assumption.
 eapply TyIf.
 apply H0. apply H1. easy.
 apply IHHwf1. apply IHHwf2.
 apply (stack_grow_meet_type D s s'); assumption.
 assumption.
*)
Admitted.

Definition stack_simple (S:stack) := forall x v t, Stack.MapsTo x (v,t) S -> simple_type t.

Lemma stack_simple_aux : forall S x, stack_simple (add_nt_one S x) -> stack_simple S.
Proof.
  unfold stack_simple in *.
  unfold add_nt_one.
  intros. 
  destruct (Stack.find (elt:=Z * type) x S) eqn:eq1.
  destruct p. destruct t0.
  apply (H x0 v t). assumption.
  destruct t0.
  apply (H x0 v t). assumption.
  apply (H x0 v t). assumption.
  apply (H x0 v t). assumption.
  apply (H x0 v t). assumption.
  destruct b0.
  destruct (Nat.eq_dec x0 x).
  specialize (H x z (TPtr m (TNTArray b (Num (z0 + 1)) t0))).
  assert (Stack.MapsTo x
      (z, TPtr m (TNTArray b (Num (z0 + 1)) t0))
      (Stack.add x
         (z, TPtr m (TNTArray b (Num (z0 + 1)) t0)) S)).
  apply Stack.add_1. reflexivity.
  apply H in H1.
  apply Stack.find_2 in eq1.
  subst.
  apply (Stack.mapsto_always_same (Z * type) x (z, TPtr m (TNTArray b (Num z0) t0)) (v, t)) in eq1.
  inv eq1.
  inv H1. inv H3.
  apply SPTPtr.
  apply SPTNTArray. assumption. assumption.
  specialize (H x0 v t).
  assert (Stack.MapsTo x0 (v, t)
      (Stack.add x
         (z, TPtr m (TNTArray b (Num (z0 + 1)) t0)) S)).
  apply Stack.add_2. lia. assumption.
  apply H in H1.
  assumption.
  destruct (Nat.eq_dec x0 x).
  specialize (H x z (TPtr m (TNTArray b (Var v0 (z0 + 1)) t0))).
  assert (Stack.MapsTo x
      (z, TPtr m (TNTArray b (Var v0 (z0 + 1)) t0))
      (Stack.add x
         (z, TPtr m (TNTArray b (Var v0 (z0 + 1)) t0)) S)).
  apply Stack.add_1. reflexivity.
  apply H in H1. inv H1. inv H3.
  specialize (H x0 v t).
  assert (Stack.MapsTo x0 (v, t)
      (Stack.add x
         (z, TPtr m (TNTArray b (Var v0 (z0 + 1)) t0)) S)).
  apply Stack.add_2.
  lia. assumption.
  apply H in H1. assumption.
  apply (H x0 v t). assumption.
  apply (H x0 v t). assumption.
  apply (H x0 v t). assumption.
  apply (H x0 v t). assumption.
Qed.

Lemma stack_simple_prop : forall D F S H S' H' e e',
         stack_simple S ->
            step D F S H e S' H' (RExpr e') -> stack_simple S'.
Proof.
  intros.
  induction H1;eauto.
  unfold stack_simple in *.
  intros.
  unfold change_strlen_stack in *.
  destruct (n' - n <=? h).
  apply (H0 x0 v t0). assumption.
  apply Stack.find_2 in H1.
  apply H0 in H1.
  destruct (Nat.eq_dec x0 x).
  subst.
  apply Stack.mapsto_add1 in H4.
  inv H4.
  inv H1. inv H5.
  apply SPTPtr. apply SPTNTArray. assumption.
  apply Stack.add_3 in H4.
  apply H0 in H4. assumption. lia.
  apply (cast_means_simple_type) in H1.
  unfold stack_simple in *.
  intros.
  destruct (Nat.eq_dec x0 x).
  subst. 
  apply Stack.mapsto_add1 in H2. inv H2.
  assumption.
  apply Stack.add_3 in H2.
  apply H0 in H2. assumption. lia.
  eapply stack_simple_aux. apply H0.
Qed.

Lemma subtype_simple : forall D t t', subtype D t t'
                 -> simple_type t' -> simple_type t.
Proof.
  intros. 
  induction H. assumption.
  inv H0. inv H4.
  constructor. assumption.
  inv H1. inv H2. constructor. constructor. inv H0. assumption.
  inv H1. inv H2. constructor. constructor. inv H0. assumption.
  inv H0. inv H3. inv H. inv H1. constructor. apply SPTArray. assumption.
  inv H0. inv H3. inv H. inv H1. constructor. apply SPTNTArray. assumption.
  inv H0. inv H3. inv H. inv H1. constructor. apply SPTNTArray. assumption.
  constructor. constructor.
  constructor. constructor.
Qed.


Lemma new_sub : forall D F s H env v t t' x,
      stack_grow D s (Stack.add x (v,t') s) ->
      stack_simple (Stack.add x (v,t') s) ->
      stack_wf D H env s ->
      cast_type_bound s t t' ->
      @well_typed D F s H env Checked (ELit v t) t ->
      stack_wf D H (Env.add x t env) (Stack.add x (v, t') s).
  Proof.
(*
  intros.
  apply WFS_Stack. split.
  - intros.
    inv H4. inv H12.
    specialize (cast_type_bound_same s t t' t'0 H3 H4) as eq1.
    subst.
    destruct (Nat.eq_dec x x0).
    subst.
    apply Env.mapsto_add1 in H5.
    subst.
    apply (stack_grow_cast_type_same D s (Stack.add x0 (v, t'0) s) t t'0) in H4.
    exists v. exists t'0. exists t'0.
    split. assumption.
    split. constructor.
    split.
    apply Stack.add_1. reflexivity.
    split. apply (cast_means_simple_type) in H3. assumption.
    assumption. assumption.
    inv H2. destruct H7.
    apply Env.add_3 in H5.
    specialize (H2 x0 t0 H5).
    destruct H2. destruct H2. destruct H2.
    destruct H2. destruct H8. destruct H9.
    destruct H12.
    exists x1. exists x2. exists x3.
    split. apply (stack_grow_cast_type_same D s (Stack.add x (v, t'0) s)).
    assumption. assumption.
    split. assumption.
    split.
    apply Stack.add_2. lia. assumption.
    split. 
    apply (cast_means_simple_type) in H2.
    eapply subtype_simple. apply H8.
    assumption.
    assumption.
    lia.
  - intros.
    inv H2.
    destruct H8.
    destruct (Nat.eq_dec x0 x).
    subst.
    apply Stack.mapsto_add1 in H5.
    inv H5.
    exists t. exists t'.
    split. apply Env.add_1. reflexivity.
    split. apply (stack_grow_cast_type_same D s (Stack.add x (v, t') s)).
    assumption. assumption. constructor.
    destruct (H8 x0 v0 t0).
    apply Stack.add_3 in H5. assumption.
    lia.
    assumption.
    assumption.
    destruct H9.
    exists x1. exists x2.
    destruct H9. destruct H10.
    split.
    apply Env.add_2. lia.
    assumption.
    split. apply (stack_grow_cast_type_same D s (Stack.add x (v, t') s)).
    assumption. assumption.
    assumption.
*)
Admitted.


Lemma env_sym : forall env env', @Env.Equal type env env' -> @Env.Equal type env' env.
Proof.
 intros. unfold Env.Equal in *.
 intros.  rewrite H. reflexivity.
Qed.

Lemma well_typed_grow : forall D F S H env m e t x t',
    ~ Env.In x env ->
    @well_typed D F S H env m e t ->
    @well_typed D F S H (Env.add x t' env) m e t.
Proof.
  intros.
  induction H1; eauto 20.
  apply weakening.
  eauto.
  apply TyVar. apply weakening_type_bound. assumption.
  destruct (Nat.eq_dec x0 x).
  subst.
  unfold Env.In,Env.Raw.PX.In in H0.
  destruct H0.
  exists t. assumption.
  apply Env.add_2. lia. assumption.
  eapply TyCall. apply H1.
(*

  eapply TyStrlen.
  apply weakening_type_bound.
  apply H1.
  destruct (Nat.eq_dec x0 x).
  subst.
  unfold Env.In,Env.Raw.PX.In in H0.
  destruct H0.
  exists (TPtr m (TNTArray h l t)). assumption.
  apply Env.add_2. lia. assumption.
  eapply TyLet.
  apply IHwell_typed1. assumption.
  destruct (Nat.eq_dec x0 x).
  subst.
  eapply equiv_env_wt.
  assert (Env.Equal (Env.add x t1 (Env.add x t' env0)) (Env.add x t1 env0)).
  apply env_shadow. apply env_sym in H1. apply H1.
  assumption.
  eapply equiv_env_wt.
  assert (Env.Equal (Env.add x t' (Env.add x0 t1 env0)) (Env.add x0 t1 (Env.add x t' env0))).
  apply env_neq_commute.
  unfold Env.E.eq. lia. apply H1.
  apply IHwell_typed2.
  unfold Env.In,Env.Raw.PX.In in *.
  intros R. destruct R.
  apply Env.add_3 in H1.
  destruct H0.
  exists x1. assumption.
  lia.
  eapply TyMalloc.
  apply weakening_type_bound. assumption.
  eapply TyCast1; eauto.
  apply weakening_type_bound. assumption.
  eapply TyCast2; eauto.
  apply weakening_type_bound. assumption.
  eapply TyCast3; eauto.
  apply weakening_type_bound. assumption.
  eapply TyCast4; eauto.
  apply weakening_type_bound. assumption.
  eapply TyIf; eauto.
  destruct (Nat.eq_dec x x0).
  subst.
  unfold Env.In,Env.Raw.PX.In in *.
  destruct H0.
  exists t.
  assumption.
  apply Env.add_2.
  lia.
  assumption.
*)
Admitted.


Lemma well_bound_in_subst : forall env x t1 t2 b,
                          well_bound_in (Env.add x t1 env) b
                                -> well_bound_in (Env.add x t2 env) b.
Proof.
 intros. remember (Env.add x t1 env0) as env1.
 remember (Env.add x t2 env0) as env2.
 induction H;subst;eauto.
 apply well_bound_in_num.
 apply well_bound_in_var.
 unfold Env.In,Env.Raw.PX.In in *.
 destruct (Nat.eq_dec x x0).
 subst.
 exists t2.
 apply Env.add_1. reflexivity.
 destruct H.
 apply Env.add_3 in H.
 exists x1.
 apply Env.add_2. lia.
 assumption. lia.
Qed.

Definition ty_ssa_env (S:env) (e:expression) 
            := exists l, (forall x,  Env.In x S -> In x l) /\ (exists l', ty_ssa l e l').

Lemma well_type_bound_in_subst : forall env x t1 t2 t,
                          well_type_bound_in (Env.add x t1 env) t
                                -> well_type_bound_in (Env.add x t2 env) t.
Proof.
  intros. remember (Env.add x t1 env0) as env1.
  remember (Env.add x t2 env0) as env2.
  induction H;subst;eauto.
  apply well_type_bound_in_nat.
  apply well_type_bound_in_ptr.
  apply IHwell_type_bound_in. reflexivity.
  apply well_type_bound_in_struct.
  apply well_type_bound_in_array.
  eapply well_bound_in_subst. apply H.
  eapply well_bound_in_subst. apply H0.
  apply IHwell_type_bound_in. reflexivity.
  apply well_type_bound_in_ntarray.
  eapply well_bound_in_subst. apply H.
  eapply well_bound_in_subst. apply H0.
  apply IHwell_type_bound_in. reflexivity.
Qed.

Lemma ty_ssa_env_let_r : forall s x e e1 t,
         ty_ssa_env s (ELet x e e1) -> ty_ssa_env (Env.add x t s) e1.
Proof.
  intros. unfold ty_ssa_env in *.
  destruct H. destruct H.
  destruct H0.
  inv H0.
  exists S'.
  specialize (ty_ssa_grow (x::x0) e S' H7) as eq1.
  unfold list_subset in eq1.
  split. intros.
  destruct (Nat.eq_dec x2 x).
  subst.
  assert (In x (x::x0)) by apply in_eq.
  apply eq1 in H1. assumption.
  unfold Env.In,Env.Raw.PX.In in H0.
  destruct H0.
  apply Env.add_3 in H0.
  assert (Env.In x2 s).
  unfold Env.In,Env.Raw.PX.In. exists x3. assumption.
  apply H in H1.
  assert (In x2 (x::x0)). apply in_cons. assumption.
  apply eq1 in H2. assumption. lia.
  exists x1. assumption.
Qed.

Lemma ty_ssa_env_eq : forall s1 s2 e,
        Env.Equal s1 s2 -> ty_ssa_env s1 e -> ty_ssa_env s2 e.
Proof.
  intros. 
  unfold ty_ssa_env in *.
  destruct H0.
  unfold Env.Equal in H.
  exists x.
  split. intros.
  unfold Env.In,Env.Raw.PX.In in H1.
  destruct H1.
  apply Env.find_1 in H1.
  rewrite <- H in H1.
  apply Env.find_2 in H1.
  destruct H0. apply H0.
  unfold Env.In,Env.Raw.PX.In.
  exists x1. assumption.
  destruct H0.
  destruct H1.
  exists x0. assumption.
Qed.

Definition env_match D S (env env' : env) : Prop :=
   (forall x t, (Env.MapsTo x t env -> (Env.MapsTo x t env'
                   \/ (exists t' t'', cast_type_bound S t t' /\ subtype D t'' t' /\ Env.MapsTo x t'' env'))))
   /\ (forall x, Env.In x env' -> Env.In x env).

Lemma env_match_refl : forall D S env, env_match D S env env.
Proof.
  intros. unfold env_match.
  intros. split. intros. left. assumption.
  intros. assumption.
Qed.

Lemma env_match_ty_ssa : forall D S env1 env2 e,
        env_match D S env1 env2 -> ty_ssa_env env1 e -> ty_ssa_env env2 e.
Proof.
  intros. 
  unfold ty_ssa_env in *.
  unfold env_match in H.
  destruct H0. destruct H0.
  destruct H1.
  destruct H.
  assert (forall x0 : Env.key, Env.In (elt:=type) x0 env2 -> In x0 x).
  intros.
  apply H0.
  apply H2. assumption.
  exists x.
  split.
  easy.
  exists x0. assumption.
Qed.

Lemma env_match_grow : forall D S env env' x t, env_match D S env env' -> 
               env_match D S (Env.add x t env) (Env.add x t env').
Proof.
  unfold env_match in *.
  split. intros.
  destruct (Nat.eq_dec x0 x).
  subst.
  apply Env.mapsto_add1 in H0.
  subst.
  left. apply Env.add_1. reflexivity.
  apply Env.add_3 in H0.
  apply H in H0.
  destruct H0.
  left. apply Env.add_2.
  lia. assumption.
  destruct H0.
  destruct H0.
  right.
  exists x1. exists x2.
  split. destruct H0. eauto.
  split. destruct H0. destruct H1. assumption.
  apply Env.add_2. lia.
  destruct H0. destruct H1.
  assumption. lia.
  intros.
  destruct H.
  unfold Env.In,Env.Raw.PX.In in *.
  destruct (Nat.eq_dec x0 x).
  subst.
  exists t. apply Env.add_1. reflexivity.
  destruct H0.
  apply Env.add_3 in H0.
  specialize (H1 x0) as eq1.
  assert ((exists e : type, Env.Raw.PX.MapsTo x0 e (Env.this env'))).
  exists x1. assumption.
  apply eq1 in H2.
  destruct H2.
  exists x2.
  apply Env.add_2.
  lia. assumption. lia.
Qed.

Lemma env_match_grow_1 : forall D S env env' x t t' t'', env_match D S env env' -> 
              cast_type_bound S t t' -> subtype D t'' t' ->
               env_match D S (Env.add x t env) (Env.add x t'' env').
Proof.
  unfold env_match in *.
  split. intros.
  destruct (Nat.eq_dec x0 x).
  subst.
  apply Env.mapsto_add1 in H2.
  subst.
  right.
  exists t'. exists t''.
  split. assumption.
  split. assumption.
  apply Env.add_1. reflexivity.
  apply Env.add_3 in H2.
  destruct H.
  apply H in H2.
  destruct H2.
  left. apply Env.add_2. lia. assumption.
  destruct H2. destruct H2. destruct H2. destruct H4.
  right.
  exists x1. exists x2.
  split. assumption. split. assumption. 
  apply Env.add_2. lia. assumption. lia.
  intros.
  destruct H.
  unfold Env.In,Env.Raw.PX.In in *.
  destruct (Nat.eq_dec x0 x).
  subst.
  exists t. apply Env.add_1. reflexivity.
  destruct H2.
  apply Env.add_3 in H2.
  specialize (H3 x0) as eq1.
  assert ((exists e : type, Env.Raw.PX.MapsTo x0 e (Env.this env'))).
  exists x1. assumption.
  apply eq1 in H4.
  destruct H4.
  exists x2.
  apply Env.add_2.
  lia. assumption. lia.
Qed.

Lemma well_bound_match : forall D S env env' b, 
    env_match D S env env' ->
    well_bound_in env b -> well_bound_in env' b.
Proof.
  intros. induction H0.
  apply well_bound_in_num.
  apply well_bound_in_var.
  unfold env_match in *.
  destruct H.
  unfold Env.In,Env.Raw.PX.In in *.
  destruct H0.
  apply H in H0.
  destruct H0.
  exists x0. assumption.
  destruct H0. destruct H0.
  destruct H0. destruct H2.
  exists x2. assumption.
Qed.

(*
Lemma subtype_ntarray : forall D t m h l t', 
   subtype D t (TPtr m (TNTArray h l t')) -> (exists h1 l1, t = (TPtr m (TNTArray h1 l1 t'))).
Proof.
 intros. inv H.
 exists h. exists l. easy.
 exists l0. exists h0. easy.
Qed.

Lemma subtype_array : forall D t m h l t', 
   subtype D t (TPtr m (TArray h l t')) -> (exists h1 l1, t = (TPtr m (TArray h1 l1 t'))).
Proof.
 intros. inv H.
 exists h. exists l. easy.
 exists l0. exists h0. easy.
Qed.

Lemma subtype_ptr : forall D t m t', subtype D t (TPtr m t') -> (exists t'', t = TPtr m t'').
Proof.
  intros.
  inv H. exists t'. easy.
  exists (TArray l h t0). easy.
  exists (TNTArray l h t0). easy.
  exists (TStruct T). easy.
Qed.
*)

Lemma well_type_bound_match : forall D S env env' t,
     env_match D S env env' ->
    well_type_bound_in env t -> well_type_bound_in env' t.
Proof.
 intros.
 induction H0;eauto.
 apply well_type_bound_in_nat.
 apply well_type_bound_in_ptr.
 apply IHwell_type_bound_in.
 assumption.
 apply well_type_bound_in_struct.
 apply well_type_bound_in_array.
 apply (well_bound_match D S env0). assumption.
 assumption.
 apply (well_bound_match D S env0). assumption.
 assumption.
 apply IHwell_type_bound_in. assumption.
 apply well_type_bound_in_ntarray.
 apply (well_bound_match D S env0). assumption.
 assumption.
 apply (well_bound_match D S env0). assumption.
 assumption.
 apply IHwell_type_bound_in. assumption.
Qed.

Lemma well_typed_match : forall D F S H env env' m e t,
    (env_match D S env env') -> 
     @well_typed D F S H env m e t ->
     ( @well_typed D F S H env' m e t \/ (exists t' t'' , cast_type_bound S t t'
          /\ subtype D t'' t' /\ @well_typed D F S H env' m e t'')).
Proof.
  intros.
(*
  generalize dependent env'.
  induction H1;eauto.
  intros.
  - left. apply TyLit.
  apply (well_type_bound_match D S env0). assumption. assumption.
  assumption.
  - intros.
  unfold env_match in H2.
  destruct H2.
  apply H2 in H1.
  destruct H1.
  left. apply TyVar.
  apply (well_type_bound_match D S env0).
  unfold env_match. eauto.
  assumption.
  assumption.
  right.
  destruct H1. destruct H1.
  exists x0. exists x1.
  destruct H1. destruct H4.
  split. assumption. split. assumption.
  apply TyVar.
  apply cast_means_simple_type in H1.
  apply subtype_simple in H4.
  apply simple_type_well_bound. assumption.
  assumption. assumption.
  - admit.
  - intros. 
  assert (eq1 := H2).
  unfold env_match in H2.
  destruct H2.
  apply H2 in H1.
  destruct H1.
  left.
  eapply TyStrlen.
  apply (well_type_bound_match D S env0).
  assumption.
  apply H0.
  apply H1.
  destruct H1. destruct H1. destruct H1. destruct H4.
  left.
  specialize (cast_means_simple_type S (TPtr m (TNTArray h l t)) x0 H1) as eq2.
  inv H1. inv H9.
(*
  specialize (subtype_ntarray D x1 m l' h' t'0 H4) as eq3.
  destruct eq3.  destruct H1. subst.
  apply subtype_simple_left in H4.
  eapply TyStrlen.
  apply (simple_type_well_bound env') in H4.
  apply H4.
  apply H5. assumption.
*) admit.
  - intros.
  assert (eq1 := H0).
  apply IHwell_typed1 in H0.
  destruct H0.
  assert (env_match D S (Env.add x t1 env0) (Env.add x t1 env')).
  apply env_match_grow. assumption.
  apply IHwell_typed2 in H1.
  destruct H1.
  left. eapply TyLet.
  apply H0. apply H1.
  destruct H1. destruct H1. destruct H1.
  destruct H2.
  right. 
  exists x0. exists x1.
  split. assumption. split. assumption.
  eapply TyLet.
  apply H0.
  apply H3.
  destruct H0. destruct H0. destruct H0.
  destruct H1.
  assert (env_match D S (Env.add x t1 env0) (Env.add x x1 env')).
  eapply env_match_grow_1. apply eq1.
  apply H0. apply H1.
  apply IHwell_typed2 in H3.
  destruct H3.
  left. eapply TyLet.
  apply H2.
  apply H3.
  destruct H3. destruct H3. destruct H3. destruct H4.
  right. exists x2. exists x3.
  split. assumption. split. assumption.
  eapply TyLet.
  apply H2.
  assumption.
  - intros.
  assert (eq1:= H0).
  apply IHwell_typed1 in H0.
  apply IHwell_typed2 in eq1.
  destruct H0.
  destruct eq1.
  left. apply TyPlus. assumption. assumption.
  destruct H1. destruct H1. destruct H1. destruct H2.
  inv H1. inv H2.
  left. apply TyPlus. assumption. assumption.
  destruct H0. destruct H0. destruct H0. destruct H1.
  destruct eq1. 
  inv H0. inv H1.
  left. apply TyPlus. assumption. assumption.
  destruct H3. destruct H3. destruct H3. destruct H4.
  inv H0. inv H1. inv H3. inv H4.
  left. apply TyPlus. assumption. assumption.
  - intros. 
  apply IHwell_typed in H4.
  destruct H4.
  left. eapply TyFieldAddr.
  apply H4. apply H0. apply H2.
  apply H3.
  destruct H4. destruct H4. destruct H4. destruct H5.
  inv H4. inv H10. inv H5.
  left. eapply TyFieldAddr.
  apply H6. apply H0. apply H2.
  apply H3.
  - intros.
  left.
  apply TyMalloc.
  eapply well_type_bound_match. apply H1.
  assumption.
  - intros. 
  apply IHwell_typed in H0.
  destruct H0.
  left. apply TyUnchecked.
  assumption.
  destruct H0. destruct H0. destruct H0.
  destruct H2.
  right.
  exists x. exists x0.
  split. assumption. split. assumption.
  apply TyUnchecked.
  assumption.
  - intros.
  assert (eq1 := H3).
  apply IHwell_typed in H3.
  destruct H3.
  left. eapply TyCast1.
  eapply well_type_bound_match. apply eq1.
  apply H0.
  assumption.
  apply H3.
  destruct H3. destruct H3. destruct H3.
  destruct H4.
  left.
  eapply TyCast1.
  eapply well_type_bound_match. apply eq1.
  assumption.
  assumption.
  apply H5.
  - intros.
  assert (eq1 := H3).
  apply IHwell_typed in H3.
  destruct H3.
  left.
  eapply TyCast2. apply H0.
  eapply well_type_bound_match. apply eq1.
  assumption.
  apply H3.
  destruct H3. destruct H3. destruct H3.
  destruct H4.
  specialize (cast_means_simple_type S (TPtr Checked (TArray u v t')) x0 H3) as eq2.
  inv H3.
  inv H9.
  specialize (subtype_array D x1 Checked l' h' t'1 H4) as eq3.
  destruct eq3. destruct H3. subst.
  apply subtype_simple_left in H4.
  left.
  eapply TyCast2.
  assert (type_eq S t t'1).
  inv H0.
  apply type_eq_right.
  apply (cast_means_simple_type S t'). assumption. assumption.
  apply (cast_type_bound_same S t' t t'1) in H12.
  subst. apply type_eq_refl. assumption.
  specialize (simple_type_means_cast_same S t' H3) as eq3.
  apply (cast_type_bound_same S t' t' t'1) in H12.
  subst.
  apply type_eq_right.
  assumption. assumption. assumption.
  apply H3.
  eapply well_type_bound_match.
  apply eq1. assumption. apply H5.
  assumption.
  - intros.
  assert (eq1 := H3).
  apply IHwell_typed in H3.
  destruct H3.
  left.
  eapply TyCast3. apply H0.
  eapply well_type_bound_match. apply eq1.
  assumption.
  apply H3.
  destruct H3. destruct H3. destruct H3.
  destruct H4.
  specialize (cast_means_simple_type S (TPtr Checked (TNTArray u v t')) x0 H3) as eq2.
  inv H3.
  inv H9.
  specialize (subtype_ntarray D x1 Checked l' h' t'1 H4) as eq3.
  destruct eq3. destruct H3. subst.
  apply subtype_simple_left in H4.
  left.
  eapply TyCast3.
  assert (type_eq S t t'1).
  inv H0.
  apply type_eq_right.
  apply (cast_means_simple_type S t'). assumption. assumption.
  apply (cast_type_bound_same S t' t t'1) in H12.
  subst. apply type_eq_refl. assumption.
  specialize (simple_type_means_cast_same S t' H3) as eq3.
  apply (cast_type_bound_same S t' t' t'1) in H12.
  subst.
  apply type_eq_right.
  assumption. assumption. assumption.
  apply H3.
  eapply well_type_bound_match.
  apply eq1. assumption. apply H5.
  assumption.
  - intros.
  assert (eq1 := H3).
  apply IHwell_typed in H3.
  destruct H3.
  left.
  eapply TyCast4. apply H0.
  eapply well_type_bound_match. apply eq1.
  assumption.
  apply H3.
  destruct H3. destruct H3. destruct H3.
  destruct H4.
  specialize (cast_means_simple_type S (TPtr Checked (TNTArray u v t')) x0 H3) as eq2.
  inv H3.
  inv H9.
  specialize (subtype_ntarray D x1 Checked l' h' t'1 H4) as eq3.
  destruct eq3. destruct H3. subst.
  apply subtype_simple_left in H4.
  left.
  eapply TyCast4.
  assert (type_eq S t t'1).
  inv H0.
  apply type_eq_right.
  apply (cast_means_simple_type S t'). assumption. assumption.
  apply (cast_type_bound_same S t' t t'1) in H12.
  subst. apply type_eq_refl. assumption.
  specialize (simple_type_means_cast_same S t' H3) as eq3.
  apply (cast_type_bound_same S t' t' t'1) in H12.
  subst.
  apply type_eq_right.
  assumption. assumption. assumption.
  apply H3.
  eapply well_type_bound_match.
  apply eq1. assumption. apply H5.
  assumption.
  - intros. 
  assert (eq1 := H4).
  apply IHwell_typed in H4.
  destruct H4.
  left. eapply TyDeref.
  apply H4.
  apply H0.
  eauto.
  apply H3.
  destruct H4. destruct H4. destruct H4.
  destruct H5.
  destruct H2. destruct H2.
  inv H0. inv H4. inv H5.
  right. exists t'0. exists t'0.
  split. assumption.
  split. constructor.
  eapply TyDeref.
  apply H6.
  apply SubTyRefl.
  left. split. eapply cast_word_type.
  apply H9. apply H2. reflexivity. assumption.
  inv H9. inv H2. inv H9. inv H2.
  inv H9.
  left. 
  eapply TyDeref.
  apply H6.
  eapply SubTyStructArrayField.
  apply H8. assumption.
  left. easy. assumption.
  inv H2. inv H2.
  inv H4. inv H9. inv H5.
  left. eapply TyDeref.
  apply H6.
  eapply SubTyStructArrayField.
  apply H11. assumption.
  left. easy. assumption.
  destruct H2. destruct H2. destruct H7.
  inv H0.
  inv H4. inv H10.
  inv H5.
  right. exists t'1. exists t'1.
  split. assumption. split. constructor.
  eapply TyDeref. apply H6.
  apply SubTyRefl.
  right. left.
  split. reflexivity.
  split. eapply cast_word_type.
  apply H13. assumption.
  eapply cast_type_wf. apply H13. assumption.
  assumption.
  right. exists t'1. exists t'1.
  split. assumption. split. constructor.
  eapply TyDeref. apply H6.
  apply SubTyRefl.
  right. left.
  split. reflexivity.
  split. eapply cast_word_type.
  apply H13. assumption.
  eapply cast_type_wf. apply H13. assumption.
  assumption.
  inv H4.
  inv H11. inv H5. inv H10.
  right. 
  exists t'1. exists t'1.
  split. assumption. split. constructor.
  eapply TyDeref. apply H6.
  apply SubTyRefl.
  right. left.
  split. reflexivity.
  split. eapply cast_word_type.
  apply H16. assumption.
  eapply cast_type_wf. apply H16. assumption.
  assumption.
  inv H10.
  right. 
  exists t'1. exists t'1.
  split. assumption. split. constructor.
  eapply TyDeref. apply H6.
  apply SubTyRefl.
  right. left.
  split. reflexivity.
  split. eapply cast_word_type.
  apply H16. assumption.
  eapply cast_type_wf. apply H16. assumption.
  assumption. inv H10. inv H10.
  destruct H2. destruct H7. subst.
  inv H0.
  inv H4. inv H10.
  inv H5.
  right. exists t'1. exists t'1.
  split. assumption. split. constructor.
  eapply TyDeref. apply H6.
  apply SubTyRefl.
  right. right.
  split. reflexivity.
  split. eapply cast_word_type.
  apply H13. assumption.
  eapply cast_type_wf. apply H13. assumption.
  assumption.
  right. exists t'1. exists t'1.
  split. assumption. split. constructor.
  eapply TyDeref. apply H6.
  apply SubTyRefl.
  right. right.
  split. reflexivity.
  split. eapply cast_word_type.
  apply H13. assumption.
  eapply cast_type_wf. apply H13. assumption.
  assumption.
  inv H4.
  inv H10. inv H5.
  right. 
  exists t'1. exists t'1.
  split. assumption. split. constructor.
  eapply TyDeref. apply H6.
  apply SubTyRefl.
  right. right.
  split. reflexivity.
  split. eapply cast_word_type.
  apply H15. assumption.
  eapply cast_type_wf. apply H15. assumption.
  assumption.
  right. 
  exists t'1. exists t'1.
  split. assumption. split. constructor.
  eapply TyDeref. apply H6.
  apply SubTyRefl.
  right. right.
  split. reflexivity.
  split. eapply cast_word_type.
  apply H15. assumption.
  eapply cast_type_wf. apply H15. assumption.
  assumption.
  - intros.
  assert (eq1 := H4).
  assert (eq2 := H4).
  apply IHwell_typed1 in H4.
  apply IHwell_typed2 in eq1.
  destruct H4.
  destruct eq1.
  left. eapply TyIndex1.
  assumption. assumption.
  apply H4. apply H2.
  apply H5. assumption.
  destruct H5. destruct H5.
  destruct H5. destruct H6.
  inv H5. inv H6.
  left. eapply TyIndex1.
  assumption. assumption.
  apply H4. reflexivity.
  assumption. assumption.
  destruct H4. destruct H4. destruct H4.
  destruct H5. subst.
  inv H4. inv H9.
  specialize (cast_means_simple_type S t' t'1 H12) as eqa.
  inv H5.
  destruct eq1.
  right. exists t'1. exists t'1.
  split. assumption. split. constructor.
  eapply TyIndex1.
  eapply cast_word_type. apply H12. assumption.
  eapply cast_type_wf. apply H12. assumption.
  apply H6. reflexivity. apply H2. assumption.
  destruct H2. destruct H2. 
  destruct H2. destruct H4.
  inv H2. inv H4.
  right. exists t'1. exists t'1.
  split. assumption. split. constructor.
  eapply TyIndex1.
  eapply cast_word_type. apply H12. assumption.
  eapply cast_type_wf. apply H12. assumption.
  apply H6. reflexivity. apply H5. assumption.
  destruct eq1.
  right. exists t'1. exists t'1.
  split. assumption. split. constructor.
  eapply TyIndex1.
  eapply cast_word_type. apply H12. assumption.
  eapply cast_type_wf. apply H12. assumption.
  apply H6. reflexivity. apply H2. assumption.
  destruct H2. destruct H2. 
  destruct H2. destruct H4.
  inv H2. inv H4.
  right. exists t'1. exists t'1.
  split. assumption. split. constructor.
  eapply TyIndex1.
  eapply cast_word_type. apply H12. assumption.
  eapply cast_type_wf. apply H12. assumption.
  apply H6. reflexivity. apply H5. assumption.
  - intros.
  assert (eq1 := H4).
  assert (eq2 := H4).
  apply IHwell_typed1 in H4.
  apply IHwell_typed2 in eq1.
  destruct H4.
  destruct eq1.
  left. eapply TyIndex2.
  assumption. assumption.
  apply H4. apply H2.
  apply H5. assumption.
  destruct H5. destruct H5.
  destruct H5. destruct H6.
  inv H5. inv H6.
  left. eapply TyIndex2.
  assumption. assumption.
  apply H4. reflexivity.
  assumption. assumption.
  destruct H4. destruct H4. destruct H4.
  destruct H5. subst.
  inv H4. inv H9.
  specialize (cast_means_simple_type S t' t'1 H12) as eqa.
  inv H5.
  destruct eq1.
  right. exists t'1. exists t'1.
  split. assumption. split. constructor.
  eapply TyIndex2.
  eapply cast_word_type. apply H12. assumption.
  eapply cast_type_wf. apply H12. assumption.
  apply H6. reflexivity. apply H2. assumption.
  destruct H2. destruct H2. 
  destruct H2. destruct H4.
  inv H2. inv H4.
  right. exists t'1. exists t'1.
  split. assumption. split. constructor.
  eapply TyIndex2.
  eapply cast_word_type. apply H12. assumption.
  eapply cast_type_wf. apply H12. assumption.
  apply H6. reflexivity. apply H5. assumption.
  destruct eq1.
  right. exists t'1. exists t'1.
  split. assumption. split. constructor.
  eapply TyIndex2.
  eapply cast_word_type. apply H12. assumption.
  eapply cast_type_wf. apply H12. assumption.
  apply H6. reflexivity. apply H2. assumption.
  destruct H2. destruct H2. 
  destruct H2. destruct H4.
  inv H2. inv H4.
  right. exists t'1. exists t'1.
  split. assumption. split. constructor.
  eapply TyIndex2.
  eapply cast_word_type. apply H12. assumption.
  eapply cast_type_wf. apply H12. assumption.
  apply H6. reflexivity. apply H5. assumption.
  - intros. 
  assert (eq1 := H4).
  assert (eq2 := H4).
  apply IHwell_typed1 in H4.
  apply IHwell_typed2 in eq1.
  destruct H4. destruct eq1.
  left. 
  eapply TyAssign1.
  apply H0.
  apply H1.
  apply H2.
  assumption. assumption. assumption.
  destruct H5. destruct H5.
  destruct H5. destruct H6.
  inv H1. apply type_eq_tnat in H2. subst.
  inv H5. inv H6.
  left. eapply TyAssign1.
  apply H0. constructor. constructor.
  assumption. assumption. assumption.
  assert (eq3 := H2).
  inv H2. inv H5.
  inv H6.
  admit.
  inv H0.
  subst.
  right. 
  exists (TPtr m0 t').
  exists (TPtr m0 x).
  split. constructor. assumption.
  split. apply H6.
  inv H0.
  assert (
  eapply TyAssign1.
  apply H0. constructor.
  apply type_eq_right.
  constructor. apply (cast_means_simple_type S w).
  assumption. constructor.
  assumption.
  assumption.
  assumption.
  assumption.
  constructor.
  apply H3. apply H4.
  apply H0. apply H1.
  assumption.
  destruct H4. destruct H4.
  destruct H4. destruct H5.


  intros.
  assert (eq1 := H5).
  apply IHwell_typed1 in H5.
  apply IHwell_typed2 in eq1.
  destruct H5.
  destruct eq1.
  left. eapply TyIf. admit.
  apply H1. eauto.
  apply H5. apply H6. apply H3.
  assumption.
  destruct H6. destruct H6. destruct H6.
  destruct H7.
*)
Admitted.


Lemma well_typed_subtype : forall D F S H env m e t x t1 t2 t3,
    @well_typed D F S H (Env.add x t1 env) m e t ->
     cast_type_bound S t1 t2 ->
     subtype D t3 t2 ->
    (exists env', env_match D S env env' /\
    (@well_typed D F S H (Env.add x t3 env') m e t \/ 
       (exists t' t'' , cast_type_bound S t t'
          /\ subtype D t'' t' /\ @well_typed D F S H (Env.add x t3 env') m e t''))).
Proof.

Admitted.

(* ty_ssa properties. *)
Lemma ty_ssa_stack_small_let : forall s e x e1,
         ty_ssa_stack s (ELet x e e1) -> ty_ssa_stack s e.
Proof.
  intros. unfold ty_ssa_stack in *.
  destruct H. destruct H.
  destruct H0.
  inv H0.
  exists ((x :: x0)).
  split. intros.
  apply H in H0.
  apply in_cons. assumption.
  exists S'. assumption.
Qed.

Lemma ty_ssa_stack_small_plus_l : forall s e e1,
         ty_ssa_stack s (EPlus e e1) -> ty_ssa_stack s e.
Proof.
  intros. unfold ty_ssa_stack in *.
  destruct H. destruct H.
  destruct H0.
  inv H0.
  exists x.
  split. intros.
  apply H in H0. assumption.
  exists S'. assumption.
Qed.

Lemma ty_ssa_stack_small_plus_r : forall s v t e,
         ty_ssa_stack s (EPlus (ELit v t) e) -> ty_ssa_stack s e.
Proof.
  intros. unfold ty_ssa_stack in *.
  destruct H. destruct H.
  destruct H0.
  inv H0. inv H4.
  exists S'. eauto.
Qed.

Lemma ty_ssa_stack_small_efield : forall s e f,
         ty_ssa_stack s (EFieldAddr e f) -> ty_ssa_stack s e.
Proof.
  intros. unfold ty_ssa_stack in *.
  destruct H. destruct H.
  destruct H0.
  exists x.
  split. intros.
  apply H in H1. assumption.
  exists x0. inv H0. assumption.
Qed.

Lemma ty_ssa_stack_small_cast : forall s t e,
         ty_ssa_stack s (ECast t e) -> ty_ssa_stack s e.
Proof.
  intros. unfold ty_ssa_stack in *.
  destruct H. destruct H.
  destruct H0.
  exists x.
  split. intros.
  apply H in H1. assumption.
  exists x0. inv H0. assumption.
Qed.

Lemma ty_ssa_stack_small_deref : forall s e,
         ty_ssa_stack s (EDeref e) -> ty_ssa_stack s e.
Proof.
  intros. unfold ty_ssa_stack in *.
  destruct H. destruct H.
  destruct H0.
  exists x.
  split. intros.
  apply H in H1. assumption.
  exists x0. inv H0. assumption.
Qed.

Lemma ty_ssa_stack_small_assign_l : forall s e e1,
         ty_ssa_stack s (EAssign e e1) -> ty_ssa_stack s e.
Proof.
  intros. unfold ty_ssa_stack in *.
  destruct H. destruct H.
  destruct H0.
  exists x.
  split. intros.
  apply H in H1. assumption.
  inv H0.
  exists S'. assumption.
Qed.

Lemma ty_ssa_stack_small_assign_r : forall s v t e,
         ty_ssa_stack s (EAssign (ELit v t) e) -> ty_ssa_stack s e.
Proof.
  intros. unfold ty_ssa_stack in *.
  destruct H. destruct H.
  destruct H0. inv H0. inv H4.
  exists S'.
  split. intros. apply H.
  assumption.
  exists x0. assumption.
Qed.

Lemma ty_ssa_stack_small_unchecked : forall s e,
         ty_ssa_stack s (EUnchecked e) -> ty_ssa_stack s e.
Proof.
  intros. unfold ty_ssa_stack in *.
  destruct H. destruct H.
  destruct H0.
  exists x.
  split. intros.
  apply H in H1. assumption.
  exists x0. inv H0. assumption.
Qed.

Lemma ty_ssa_stack_in_hole : forall s e E,
         ty_ssa_stack s (in_hole e E) -> ty_ssa_stack s e.
Proof.
(*
  intros.
  induction E;simpl in *.
  assumption.
  apply ty_ssa_stack_small_let in H.
  apply IHE in H. assumption.
  apply ty_ssa_stack_small_plus_l in H.
  eauto.
  apply ty_ssa_stack_small_plus_r in H.
  eauto.
  apply ty_ssa_stack_small_efield in H.
  eauto.
  apply ty_ssa_stack_small_cast in H.
  eauto.
  apply ty_ssa_stack_small_deref in H.
  eauto.
  apply ty_ssa_stack_small_assign_l in H.
  eauto.
  apply ty_ssa_stack_small_assign_r in H.
  eauto.
  apply ty_ssa_stack_small_unchecked in H.
  eauto.
*)
Admitted.

Lemma preservation : forall D F S H env e t S' H' e',
    @structdef_wf D ->
    heap_wf D H ->
    heap_wt D H ->
    expr_wf D F e ->
    ty_ssa_stack S e ->
    (forall x v t, Heap.MapsTo x (v,t) H -> simple_type t) ->
    stack_simple S ->
    sub_domain env S ->
    stack_wf D H env S ->
    @well_typed D F S H env Checked e t ->
    @reduce D F S H e Checked S' H' (RExpr e') ->
    exists env',
      env_consistent env' env /\ sub_domain env' S' /\ stack_wf D H env' S' /\
      @heap_consistent D H' H 
   /\ (@well_typed D F S' H' env' Checked e' t
       \/ (exists t' t'', cast_type_bound S' t t' 
        /\ subtype D t'' t' /\ @well_typed D F S' H' env' Checked e' t'')).
Proof with eauto 20 with Preservation.
  intros D F s H env e t s' H' e' HDwf HHwf HHWt HEwf HSSA HSimple SSimple HSubDom HSwf Hwt.
  generalize dependent H'. generalize dependent e'.
  remember Checked as m.
  induction Hwt as [
                     env m n t Wb HTyLit                                      | (* Literals *)
                     env m x t Wb HVarInEnv                                   | (* Variables *)
                      env m es x tvl t e t' t'' HMap HArg HTy HSub            | (* Call *)
                     env m x h l t Wb HVE                                     | (* Strlen *)
                     env m x e1 t1 e2 t HTy1 IH1 HTy2 IH2                     | (* Let-Expr *)
                     env m e1 e2 HTy1 IH1 HTy2 IH2                            | (* Addition *)
                     env m e m' T fs i fi ti HTy IH HWf1 HWf2                 | (* Field Addr *)
                     env m w Wb                                               | (* Malloc *)
                     env m e t HTy IH                                         | (* Unchecked *)
                     env m t e t' Wb HChkPtr HTy IH                           | (* Cast - nat *)
                     env m t e t' Wb HTy IH HSub                              | (* Cast - subtype *)
                     env m e x y u v t t' Teq Wb HTy IH                       | (* DynCast - ptr array *)
                     env m e x y t t' Teq HNot Wb HTy IH                      | (* DynCast - ptr array from ptr *)
                     env m e x y u v t t' Teq Wb HTy IH                       | (* DynCast - ptr nt-array *)
                     env m e m' t l h t' t'' HTy IH HSub HPtrType HMode       | (* Deref *)
                     env m e1 m' l h t e2 t' WT Twf HTy1 IH1 HSubType HTy2 IH2 HMode                | (* Index for array pointers *)
                     env m e1 m' l h t e2 t' WT Twf HTy1 IH1 HSubType HTy2 IH2 HMode                | (* Index for ntarray pointers *)
                     env m e1 e2 m' t t1 t2 HSubType WT HTy HTy1 IH1 HTy2 IH2 HMode                 | (* Assign normal *)
                     env m e1 e2 m' l h t t' t'' WT Twf Teq HSub HTy1 IH1 HTy2 IH2 HMode            | (* Assign array *)
                     env m e1 e2 m' l h t t' t'' WT Twf Teq HSub HTy1 IH1 HTy2 IH2 HMode            | (* Assign nt-array *)

                     env m e1 e2 e3 m' l h t t' t'' WT Twf Teq TSub HTy1 IH1 HTy2 IH2 HTy3 IH3 HMode      |  (* IndAssign for array pointers *)
                     env m e1 e2 e3 m' l h t t' t'' WT Twf Teq TSub HTy1 IH1 HTy2 IH2 HTy3 IH3 HMode      |  (* IndAssign for ntarray pointers *)
                     env m m' x t t1 e1 e2 t2 t3 t4 HEnv HSubType HPtrType HTy1 IH1 HTy2 IH2 HMeet HMode (* If *)
                   ]; intros e' H' Hreduces; subst.
  (* T-Lit, impossible because values do not step *)
  - exfalso. eapply lit_are_nf...
  (* T-Var *)
  - inv Hreduces.
    destruct E; inversion H1; simpl in *; subst. inv H5. exists env.
    split. econstructor.
    split. assumption.
    split. assumption.
    split. unfold heap_consistent. eauto.
    right. inv HSwf. destruct H.
    specialize (gen_cast_type_bound_same env s' t Wb HSubDom) as eq1.
    destruct eq1.
    specialize (H x t HVarInEnv) as eq2.
    destruct eq2. destruct H3. destruct H3. destruct H3.
    destruct H4. destruct H5. destruct H6. 
    apply Stack.find_2 in H10.
    specialize (Stack.mapsto_always_same (Z*type) x (x1, x3) (v, t0) s' H5 H10) as eq1.
    injection eq1. intros. subst.
    exists x2. exists t0.
    split. easy. split. easy.
    apply TyLit.
    apply (simple_type_well_bound env). assumption.
    apply (WTStack D s' H' empty_scope v t0 t0).
    apply simple_type_means_cast_same.
    assumption.
    assumption.
  (*T-Call*)
  - admit.
  (*T-Strlen*)
  - admit.
  (* T-Let *)
  - inv Hreduces.
    destruct E; inversion H1; simpl in *; subst.
    + clear H0. clear H9. rename e'0 into e'.
      specialize (stack_grow_prop D F s H s' H' (ELet x e1 e2) e' HSSA H5) as eq1.
      specialize (stack_simple_prop D F s H s' H' (ELet x e1 e2) e' SSimple H5) as eq2.
      inv H5. exists (Env.add x t0 env). inv HEwf.
      assert (Ht : t0 = t1). {
        inv HTy1. reflexivity.
      } rewrite Ht in *. clear Ht.
      split. econstructor.
      inv HSSA.
      destruct H. destruct H0.
      inv H0.
      unfold sub_domain in HSubDom.
      intros R. apply HSubDom in R.
      apply H in R. contradiction.
      split. unfold sub_domain in *.
      intros. 
      destruct (Nat.eq_dec x0 x). subst.
      unfold Stack.In,Stack.Raw.PX.In.
      exists (n, t').
      apply Stack.add_1. reflexivity.
      assert (Stack.In (elt:=Z * type) x0 s -> Stack.In (elt:=Z * type) x0 (Stack.add x (n, t') s)).
      intros. 
      unfold Stack.In,Stack.Raw.PX.In in *.
      destruct H0. exists x1.
      apply Stack.add_2. lia. assumption.
      apply H0. apply HSubDom.
      unfold Env.In,Env.Raw.PX.In in *.
      destruct H.
      apply Env.add_3 in H.
      exists x1. assumption. lia.
      split. apply (new_sub D F).
      assumption. assumption.
      assumption. assumption.
      assumption.
      split. unfold heap_consistent. eauto.
      left. apply (stack_grow_well_typed D F s).
      assumption.
      assumption.
    + clear H1.
      assert (~ Stack.In x s) as eqa.
      inv HSSA. destruct H0. destruct H1.
      inv H1.
      intros R. apply H0 in R. contradiction.
      apply ty_ssa_stack_small_let in HSSA.
      specialize (ty_ssa_stack_in_hole s e E HSSA) as eq3.
      specialize (stack_grow_prop D F s H s' H' e e'0 eq3 H5) as eq1.
      edestruct IH1...
      inv HEwf;eauto.
      exists x0. destruct H0 as [He [Hdom [Hs' [Hh Hwt]]]]. split. eauto. split.
      eauto. split. eauto. split. eauto.
      destruct Hwt.
      left. econstructor. apply H0.
      inv He. apply (stack_grow_well_typed D F s).
      assumption. 
      apply (heapWF D F s H).
      assumption. assumption.
      destruct (Nat.eq_dec x  x1).
      subst.
      eapply equiv_env_wt.
      assert (Env.Equal (Env.add x1 t1 (Env.add x1 t0 env)) (Env.add x1 t1 env)).
      apply env_shadow. apply env_sym in H2.
      apply H2.
      apply (stack_grow_well_typed D F s s') in HTy2.
      apply (heapWF D F s' H). assumption.
      assumption. assumption.
      apply (equiv_env_wt D F s' H' 
               (Env.add x1 t0 (Env.add x t1 env)) (Env.add x t1 (Env.add x1 t0 env))).
      apply env_neq_commute_eq.
      unfold Env.E.eq. lia. easy.
      apply well_typed_grow.
      intros R. 
      unfold Env.In,Env.Raw.PX.In in *.
      destruct R.
      apply Env.add_3 in H2.
      destruct H1.
      exists x0. assumption. assumption.
      apply (stack_grow_well_typed D F s s') in HTy2.
      apply (heapWF D F s' H). assumption.
      assumption. assumption.
      destruct H0.
      destruct H0.
      destruct H0. destruct H1.
      assert (@well_typed D F s' H' (Env.add x t1 env) Checked e2 t).
      apply (stack_grow_well_typed D F s s') in HTy2.
      apply (heapWF D F s' H). assumption. assumption. assumption.
      specialize (@well_typed_subtype D F s' H' env
                    Checked e2 t x t1 x1 x2 H3 H0 H1) as eqb.
      destruct eqb. left. econstructor.
      apply H2. inv He. 
      apply well_typed_grow.
      destruct (Nat.eq_dec x  x3).
      subst.
      eapply equiv_env_wt.
      assert (Env.Equal (Env.add x3 x2 (Env.add x3 t0 env)) (Env.add x3 x2 env)).
      apply env_shadow. apply env_sym in H7.
      apply H7. assumption.
      apply (equiv_env_wt D s' H' 
               (Env.add x3 t0 (Env.add x x2 env)) (Env.add x x2 (Env.add x3 t0 env))).
      apply env_neq_commute_eq.
      unfold Env.E.eq. lia. easy.
      apply well_typed_grow.
      intros R. 
      unfold Env.In,Env.Raw.PX.In in *.
      destruct R.
      apply Env.add_3 in H7.
      destruct H6.
      exists x0. assumption. assumption. assumption.
      destruct H4.
      destruct H4.
      destruct H4.
      destruct H6.
      right. exists x3. exists x4.
      split. eauto. split. eauto.
      econstructor. apply H2.
      inv He. assumption.
      destruct (Nat.eq_dec x  x5).
      subst.
      eapply equiv_env_wt.
      assert (Env.Equal (Env.add x5 x2 (Env.add x5 t0 env)) (Env.add x5 x2 env)).
      apply env_shadow. apply env_sym in H10.
      apply H10. assumption.
      apply (equiv_env_wt D s' H' 
               (Env.add x5 t0 (Env.add x x2 env)) (Env.add x x2 (Env.add x5 t0 env))).
      apply env_neq_commute_eq.
      unfold Env.E.eq. lia. easy.
      apply well_typed_grow.
      intros R. 
      unfold Env.In,Env.Raw.PX.In in *.
      destruct R.
      apply Env.add_3 in H10.
      destruct H8.
      exists x0. assumption. assumption. assumption.
  (* T-FieldAddr *)
  - inv Hreduces.
    destruct E; inversion H2; simpl in *; subst. exists env. 
    + clear H0. clear H10. inv H6.
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

        (* assert (i = i0).
        { edestruct H; eauto. destruct H0. eapply H0. apply HWf2. apply H9. } *)
        subst.
        assert (ti = ti0).
        { apply Fields.find_1 in HWf2.
          apply Fields.find_1 in H9.
          rewrite HWf2 in H9.
          inv H9.
          reflexivity. }
        subst.
        rename fs0 into fs.
        clear i.
        rename i0 into i. 
        rename ti0 into ti. 

        (* The fact that n^(ptr C struct T) is well-typed is all we need *)
        split; eauto.
        inv HHwf.
        constructor. eapply preservation_fieldaddr; eauto. omega.
      * inv HTy.
        (* Gotta prove some equalities *)
        assert (fs = fs0).
        { apply StructDef.find_1 in HWf1.
          apply StructDef.find_1 in H7.
          rewrite HWf1 in H7.
          inv H7.
          reflexivity. }
        subst. 
        assert (fields_wf D fs0) by eauto.
        assert (ti = ti0).
        { eauto using FieldFacts.MapsTo_fun. }
        clear i.
        rename fs0 into fs.
        rename i0 into i.
        subst; rename ti0 into ti.
        (* Since it is an unchecked pointer, well-typedness is easy *)
        idtac...
    + clear H2. rename e0 into e1_redex. rename e'0 into e1_redex'.
      edestruct IH; eauto.
      inv HHwf; eauto.
  (* T-Plus *)
  - inv Hreduces.
    destruct E; inversion H1; simpl in *; subst.
    + clear H0. clear H7. rename e'0 into e'. inv H4.
      * inversion HTy1.
      * inv HTy1...
    + clear H1. rename e into e1_redex. rename e'0 into e1_redex'. edestruct IH1; idtac...
      inv HHwf; eauto.
    + clear H1. rename e into e2_redex. rename e'0 into e2_redex'. edestruct IH2; idtac...
      inv HHwf; eauto.
  (* T-Malloc *)
  - inv Hreduces.
    destruct E; inversion H2; simpl in *; subst.
    clear H0. clear H8.
    inv H5.
    split; eapply alloc_correct; eauto.
  (* T-Unchecked *)
  - inv Hreduces.
    destruct E; inversion H1; simpl in *; subst.
    + clear H0. clear H7. inv H4. inv HTy...
    + inversion H7; inversion H0.
  (* T-Cast *)
  - inv Hreduces.
    destruct E; inversion H1; simpl in *; subst.
    + clear H0. clear H7. inv H4. inv HTy.
      inv HHwf.
      inv H1.
      * idtac...
      * destruct m.
        { specialize (HChkPtr eq_refl w). exfalso. apply HChkPtr. reflexivity. }
        { idtac... }
    + clear H1. rename e0 into e1_redex. rename e'0 into e1_redex'. edestruct IH; idtac...
      inv HHwf; eauto.
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

(* ... for Blame *)

Create HintDb Blame.

Print heap_add_in_cardinal.

Lemma heap_wf_step : forall D H e H' e',
    @structdef_wf D ->
    heap_wf D H ->
    @step D H e H' (RExpr e') ->
    heap_wf D H'.
Proof.
  intros D H e H' e' HD HHwf HS.
  induction HS; eauto.
  - assert (Heap.cardinal H' = Heap.cardinal H).
      { rewrite H2. apply heap_add_in_cardinal. auto. }
    intro addr; split; intro Hyp.
    + rewrite H2.
      rewrite H3 in Hyp.
      destruct (HHwf addr) as [HAddr HIn].
      destruct (HAddr Hyp) as [v Hx].
      destruct (Z.eq_dec addr n).
      * subst.
        exists (n1, t1); auto.
        eapply Heap.add_1; eauto.
      * exists v.
        eapply Heap.add_2; eauto.
    + rewrite H2 in Hyp.
      destruct Hyp as [v Hv].
      destruct (Z.eq_dec addr n).
      * subst.
        rewrite H3.
        apply HHwf; auto.
      * rewrite H3.
        apply HHwf.
        exists v.
        apply Heap.add_3 in Hv; auto.
  - apply alloc_correct in H0; eauto.
    apply Env.empty.
Qed.

Lemma expr_wf_subst :
  forall D n t x e,
    expr_wf D (ELit n t) ->
    expr_wf D e ->
    expr_wf D (subst x (ELit n t) e).
Proof.
  intros D n t x e Hwf H.
  inv Hwf.
  induction H; simpl; eauto;
    repeat (constructor; eauto).
  - destruct (var_eq_dec x x0); repeat (constructor; eauto).
  - destruct (var_eq_dec x x0); repeat (constructor; eauto).
Qed.

Lemma expr_wf_step : forall D H e H' e',
    @expr_wf D e ->
    @step D H e H' (RExpr e') ->
    @expr_wf D e'.
Proof.
  intros D H e H' e' Hwf HS.
  inv HS; inv Hwf; eauto; try solve [repeat (constructor; eauto)].
  - inv H1; constructor; eauto.
  - apply expr_wf_subst; eauto.
Qed.

Lemma expr_wf_reduce : forall D H m e H' e',
    @expr_wf D e ->
    @reduce D H e m H' (RExpr e') ->
    @expr_wf D e'.
Proof.
  intros D H m e H' e' Hwf HR.
  inv HR; auto.
  induction E; subst; simpl in *; eauto;
  try solve [inv Hwf; constructor; eauto].
  - eapply expr_wf_step in H2; eauto.
Qed.  

Definition normal { D : structdef } (H : heap) (e : expression) : Prop :=
  ~ exists m' H' r, @reduce D H e m' H' r.

Definition stuck { D : structdef } (H : heap) (r : result) : Prop :=
  match r with
  | RBounds => True
  | RNull => True
  | RExpr e => @normal D H e /\ ~ value D e
  end.

Inductive eval { D : structdef } : heap -> expression -> mode -> heap -> result -> Prop :=
  | eval_refl   : forall H e m, eval H e m H (RExpr e)
  | eval_transC : forall H H' H'' e e' r,
      @reduce D H e Checked H' (RExpr e') ->
      eval H' e' Checked H'' r ->
      eval H e Checked H'' r
  | eval_transU : forall H H' H'' m' e e' r,
      @reduce D H e Unchecked H' (RExpr e') ->
      eval H' e' m' H'' r ->
      eval H e Unchecked H'' r.

Lemma wt_dec : forall D H env m e t, { @well_typed D H env m e t } + { ~ @well_typed D H env m e t }.
  (* This is a biggy *)
Admitted.

Theorem blame : forall D H e t m H' r,
    @structdef_wf D ->
    heap_wf D H ->
    @expr_wf D e ->
    @well_typed D H empty_env Checked e t ->
    @eval D H e m H' r ->
    @stuck D H' r ->
    m = Unchecked \/ (exists E e0, r = RExpr (in_hole e0 E) /\ mode_of E = Unchecked).
Proof.
  intros D H e t m H' r HDwf HHwf Hewf Hwt Heval Hstuck.
  destruct r.
  - pose proof (wt_dec D H' empty_env Checked e0 t).
    destruct H0.
    (* e0 is well typed *)
    + remember (RExpr e0) as r.
      induction Heval; subst.
      * inv Heqr.
        assert (value D e0 \/ reduces D H e0 \/ unchecked Checked e0).
        { apply progress with (t := t); eauto. }
        destruct H0.
        unfold stuck in Hstuck.
        destruct Hstuck.
        exfalso. apply H2. assumption.
        destruct H0.
        unfold stuck in Hstuck.
        destruct Hstuck.
        unfold normal in H1.
        unfold reduces in H0.
        exfalso. apply H1.
        assumption.
        unfold  in H0.
        destruct H0.
        inversion H0.
        right. destruct H0. destruct H0. destruct H0.
        exists x0.
        exists x.
        split.
        rewrite H0. reflexivity.
        assumption.
      * apply IHHeval.
        inv H0. eapply heap_wf_step; eauto.
        eapply expr_wf_reduce; eauto.
        assert (@heap_consistent D H' H /\ @well_typed D H' empty_env Checked e' t).
        { apply preservation with (e := e); assumption. }
        destruct H1.
        assumption.
        reflexivity.
        assumption.
        assumption.
      * left. reflexivity.
    (* e0 is not well typed *)
    + remember (RExpr e0) as r.
      induction Heval; subst.
      * inv Heqr.
        exfalso.
        apply n.
        assumption.
      * apply IHHeval.
        inv H0. eapply heap_wf_step; eauto.
        eapply expr_wf_reduce; eauto.
        assert (@heap_consistent D H' H /\ @well_typed D H' empty_env Checked e' t).
        { apply preservation with (e := e); assumption. }
        destruct H1.
        assumption.
        reflexivity.
        assumption.
        assumption.
      * left. reflexivity.
  - left.
    clear Hstuck.
    remember RNull as r.
    induction Heval; subst.
    + inversion Heqr.
    + apply IHHeval; try reflexivity.
      inv H0.
      eapply heap_wf_step; eauto.
      eapply expr_wf_reduce; eauto.
      assert (@heap_consistent D H' H /\ @well_typed D H' empty_env Checked e' t).
      { apply preservation with (e := e); eauto. }
      destruct H1.
      apply H2.
    + reflexivity.
  - left.
    clear Hstuck.
    remember RBounds as r.
    induction Heval; subst.
    + inversion Heqr.
    + apply IHHeval; try reflexivity.
      inv H0.
      eapply heap_wf_step; eauto.
      eapply expr_wf_reduce; eauto.
      assert (@heap_consistent D H' H /\ @well_typed D H' empty_env Checked e' t).
      { apply preservation with (e := e); eauto. }
      destruct H1.
      apply H2.
    + reflexivity.
Qed. 
