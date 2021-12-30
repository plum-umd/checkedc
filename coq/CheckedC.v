Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Structures.Monads.

From CHKC Require Import Tactics ListUtil Map.
Require Import Coq.FSets.FMapFacts.
(** * Document Conventions *)

(* 
(** It is common when defining syntax for a language on paper to associate one or manysimple_type *)
(*     _metavariables_ with each syntactic class. For example, the metavariables <<x>>, <<y>>,
    and <<z>> are often used to represent the syntactic class of program variables. It is *)
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

Definition type_eq_dec (t1 t2 : type): {t1 = t2} + {~ t1 = t2}.
  repeat decide equality.
Defined.

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
Module EnvFacts := FMapFacts.Facts (Env).
Definition env := Env.t type.

Definition empty_env := @Env.empty type.

Definition venv := Env.t var.

Definition empty_venv := @Env.empty var.

(* well_bound definition might not needed in the type system, since the new expr_wf will guarantee that. *)
Inductive well_bound_in : env -> bound -> Prop :=
   | well_bound_in_num : forall env n, well_bound_in env (Num n)
   | well_bound_in_var : forall env x y, Env.MapsTo x TNat env -> well_bound_in env (Var x y).

Inductive well_type_bound_in : env -> type -> Prop :=
   | well_type_bound_in_nat : forall env, well_type_bound_in env TNat
   | well_type_bound_in_ptr : forall m t env, well_type_bound_in env t -> well_type_bound_in env (TPtr m t)
   | well_type_bound_in_struct : forall env T, well_type_bound_in env (TStruct T)
   | well_type_bound_in_array : forall env l h t, well_bound_in env l -> well_bound_in env h -> 
                                      well_type_bound_in env t -> well_type_bound_in env (TArray l h t)
   | well_type_bound_in_ntarray : forall env l h t, well_bound_in env l -> well_bound_in env h -> 
                                      well_type_bound_in env t -> well_type_bound_in env (TNTArray l h t).

(* Definition of simple type meaning that no bound variables. *)
Inductive simple_type : type -> Prop := 
  | SPTNat : simple_type TNat
  | SPTPtr : forall m w, simple_type w -> simple_type (TPtr m w)
  | SPTStruct : forall t, simple_type (TStruct t)
  | SPTArray : forall l h t, simple_type t -> simple_type (TArray (Num l) (Num h) t)
  | SPTNTArray : forall l h t, simple_type t -> simple_type (TNTArray (Num l) (Num h) t).

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
    word_type t /\ type_wf D t /\ simple_type t.

Definition structdef_wf (D : structdef) : Prop :=
  forall (T : struct) (fs : fields),
    StructDef.MapsTo T fs D ->
    fields_wf D fs.


Inductive theta_elem : Type := TopElem | GeZero.

Module Theta := Map.Make Nat_as_OT.

Definition theta := Theta.t theta_elem.

Definition empty_theta := @Theta.empty theta_elem.

(* This defines the subtyping relation. *)
Inductive nat_leq (T:theta) : bound -> bound -> Prop :=
  | nat_leq_num : forall l h, l <= h -> nat_leq T (Num l) (Num h)
  | nat_leq_var : forall x l h, l <= h -> nat_leq T (Var x l) (Var x h)
  | nat_leq_num_var : forall x l h, Theta.MapsTo x GeZero T -> l <= h -> nat_leq T (Num l) (Var x h).

Lemma nat_leq_trans : forall T a b c,  nat_leq T a b -> nat_leq T b c -> nat_leq T a c.
Proof.
  intros.
  destruct a. destruct b. destruct c.
  inv H. inv H0.
  apply nat_leq_num. lia.
  inv H. inv H0. apply nat_leq_num_var; try easy. lia.
  destruct c. inv H0.
  inv H. inv H0.
  constructor. easy. lia.
  inv H. inv H0.
  constructor. lia.
Qed.


Inductive subtype (D : structdef) (Q:theta) : type -> type -> Prop :=
  | SubTyRefl : forall t, subtype D Q t t
  | SubTyBot : forall m l h t, word_type t -> nat_leq Q (Num 0) l -> nat_leq Q h (Num 1)
                           -> subtype D Q (TPtr m t) (TPtr m (TArray l h t))
  | SubTyOne : forall m l h t, word_type t -> nat_leq Q l (Num 0) -> nat_leq Q (Num 1) h
                             -> subtype D Q (TPtr m (TArray l h t)) (TPtr m t)
  | SubTyOneNT : forall m l h t, word_type t -> nat_leq Q l (Num 0) ->nat_leq Q (Num 1) h
                             -> subtype D Q (TPtr m (TNTArray l h t)) (TPtr m t)
  | SubTySubsume : forall l h l' h' t m,
    nat_leq Q l l' -> nat_leq Q h' h -> 
    subtype D Q (TPtr m (TArray l h t)) (TPtr m (TArray l' h' t))
  | SubTyNtArray : forall l h l' h' t m,
    nat_leq Q l l' -> nat_leq Q h' h ->
                subtype D Q (TPtr m (TNTArray l h t)) (TPtr m (TArray l' h' t))
  | SubTyNtSubsume : forall l h l' h' t m,
    nat_leq Q l l' -> nat_leq Q h' h -> 
    subtype D Q (TPtr m (TNTArray l h t)) (TPtr m (TNTArray l' h' t))
  | SubTyStructArrayField_1 : forall (T : struct) (fs : fields) m,
    StructDef.MapsTo T fs D ->
    Some (TNat) = (Fields.find 0%nat fs) ->
    subtype D Q (TPtr m (TStruct T)) (TPtr m (TNat))
  | SubTyStructArrayField_2 : forall (T : struct) (fs : fields) m l h,
    StructDef.MapsTo T fs D ->
    Some (TNat) = (Fields.find 0%nat fs) -> nat_leq Q (Num 0) l -> nat_leq Q h (Num 1) ->
    subtype D Q (TPtr m (TStruct T)) (TPtr m (TArray l h (TNat))).

(* Subtyping transitivity. *)
Lemma subtype_trans : forall D Q t t' m w, subtype D Q t (TPtr m w) -> subtype D Q (TPtr m w) t' -> subtype D Q t t'.
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



(* Defining stack. *)
Module Stack := Map.Make Nat_as_OT.

Definition stack := Stack.t (Z * type).

Definition empty_stack := @Stack.empty (Z * type).

Definition arg_stack := Stack.t bound.

Definition empty_arg_stack := @Stack.empty bound.

(*
Definition dyn_env := Stack.t type.

Definition empty_dyn_env := @Stack.empty type.
*)

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


Inductive expression : Type :=
  | ELit : Z -> type -> expression
  | EVar : var -> expression
  | EStrlen : var -> expression
  | ECall : funid -> list expression -> expression
  | ERet : var -> Z* type -> option (Z * type) -> expression -> expression (* return new value, old value and the type. *)
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

Parameter fenv : env -> funid -> option (list (var * type) * type * expression * mode).

Definition FEnv : Type := env -> funid -> option (list (var * type) * type * expression * mode).

Inductive gen_arg_env : env -> list (var * type) -> env -> Prop :=
    gen_arg_env_empty : forall env, gen_arg_env env [] env
  | gen_ar_env_many : forall env x t tvl env', gen_arg_env env tvl env' -> gen_arg_env env ((x,t)::tvl) (Env.add x t env').

(* Well-formedness definition. *)
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


Definition simple_option (D : structdef) (a:option (Z*type)) :=
  match a with None => True
         | Some (v,t) => word_type t /\ type_wf D t /\ simple_type t
  end.

Inductive expr_wf (D : structdef) (F:FEnv) : expression -> Prop :=
  | WFELit : forall n t,
    word_type t ->
    type_wf D t ->
    simple_type t ->
    expr_wf D F (ELit n t)
  | WFEVar : forall x,
      expr_wf D F (EVar x)
  | WFEStr : forall x,
      expr_wf D F (EStrlen x)
  | WFECall : forall x el, 
      (forall env v, fenv env x = Some v) ->
      (forall e, In e el -> (exists n t, e = ELit n t
                 /\ word_type t /\ type_wf D t /\ simple_type t) \/ (exists y, e = EVar y)) ->
      expr_wf D F (ECall x el)
  | WFRet : forall x old a e, simple_option D (Some old) -> simple_option D a -> expr_wf D F e -> expr_wf D F (ERet x old a e)
  | WFEDynCast : forall t e, 
     is_array_ptr t -> type_wf D t -> expr_wf D F e -> expr_wf D F (EDynCast t e)
  | WFELet : forall x e1 e2,
      expr_wf D F e1 ->
      expr_wf D F e2 ->
      expr_wf D F (ELet x e1 e2)
  | WFEIF : forall x e1 e2,
      expr_wf D F e1 ->
      expr_wf D F e2 ->
      expr_wf D F (EIf x e1 e2)
  | WFEMalloc : forall w,
      type_wf D w -> expr_wf D F (EMalloc w)
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
 

(** Values, [v], are expressions [e] which are literals. *)

Inductive value (D : structdef) : expression -> Prop :=
  VLit : forall (n : Z) (t : type),
    word_type t ->
    type_wf D t ->
    simple_type t ->
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

Inductive context : Type :=
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
  | CRet : var -> (Z*type) -> option (Z * type) -> context -> context
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
  | CRet x old a E' => ERet x old a (in_hole e E')
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
  | CRet x old a E' => mode_of E'
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
  | CRet x old a E' => CRet x old a (compose E' E_inner)
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


Definition NTHit (s : stack) (x : var) : Prop :=
   match Stack.find x s with | Some (v,TPtr m (TNTArray l (Num 0) t)) => True
                          | _ => False
   end.

Definition add_nt_one (s : stack) (x:var) : stack :=
   match Stack.find x s with | Some (v,TPtr m (TNTArray l (Num h) t)) 
                         => Stack.add x (v,TPtr m (TNTArray l (Num (h+1)) t)) s
                              (* This following case will never happen since the type in a stack is always evaluated. *)
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
     if n' <=? h then s else @Stack.add (Z * type) x (n,TPtr m (TNTArray l (Num n') t)) s. 

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
Definition get_good_dept (e:expression) :=
  match e with ELit v t => Some (Num v)
             | EVar x => Some (Var x 0)
             | _ => None
  end.

Fixpoint get_dept_map (l:list (var * type)) (es:list expression) :=
   match l with [] => Some []
       | (x,TNat)::xl => (match es with e::es' => match get_good_dept e with None => None 
                                                        | Some b => match (get_dept_map xl es') with None => None
                                                                           | Some xl' => Some ((x,b)::xl')
                                                                    end
                                                  end
                                      | _ => None
                          end)
       | (x,y)::xl => match es with (e::es') => get_dept_map xl es' 
                                 | _ => None
                      end
    end.

Definition subst_bound (b:bound) (x:var) (b1:bound) := 
   match b with Num n => (Num n)
           | Var y n => 
        if var_eq_dec y x then
           match b1 with (Num m) => (Num (n+m))
                         | (Var z m) => (Var z (n+m))
           end
        else Var y n
   end.

Fixpoint subst_bounds (b:bound) (s: list (var*bound)) :=
  match s with [] => b
            | (x,b1)::xs => subst_bounds (subst_bound b x b1) xs
  end.

Fixpoint subst_type (s: list (var*bound)) (t:type) :=
   match t with TNat => TNat
            | TPtr m t' => TPtr m (subst_type s t')
            | TStruct T => TStruct T
            | TArray b1 b2 t => TArray (subst_bounds b1 s) (subst_bounds b2 s) (subst_type s t)
            | TNTArray b1 b2 t => TNTArray (subst_bounds b1 s) (subst_bounds b2 s) (subst_type s t)
  end.

Inductive eval_arg : stack -> expression -> type -> expression -> Prop :=
    eval_lit : forall arg_s n t t' t'', cast_type_bound arg_s t t'' -> eval_arg arg_s (ELit n t') t (ELit n t'')
  | eval_var : forall arg_s x n t t' t'', Stack.MapsTo x (n,t') arg_s
            -> cast_type_bound arg_s t t'' -> eval_arg arg_s (EVar x) t (ELit n t'').

Inductive eval_el (AS: list (var*bound)) : stack -> list (var * type) -> list expression -> stack -> Prop :=
    eval_el_empty : forall s, eval_el AS s [] [] s
  | eval_el_many_2 : forall s s' e x n t t' tvl es, eval_arg s e (subst_type AS t) (ELit n t') ->
              eval_el AS s tvl es s' -> 
              eval_el AS s ((x,t)::tvl) (e::es) (Stack.add x (n,t') s').


Definition is_nor_array_ptr (t:type) : Prop :=
   match t with (TPtr m (TArray x y t')) => True
              | _ => False
   end.

Inductive get_root {D:structdef} : type -> type -> Prop :=
    get_root_word : forall m t, word_type t -> get_root (TPtr m t) t
  | get_root_array : forall m l h t, get_root (TPtr m (TArray l h t)) t
  | get_root_ntarray : forall m l h t, get_root (TPtr m (TNTArray l h t)) t
  | get_root_struct : forall m T f, StructDef.MapsTo T f D ->
    Some (TNat) = (Fields.find 0%nat f) -> @get_root D (TPtr m (TStruct T)) TNat.

Inductive gen_rets  (AS: list (var*bound)) (S: stack) : list (var * type) -> list expression -> expression -> expression -> Prop :=
   gen_rets_empty : forall e, gen_rets AS S [] [] e e
  | gen_rets_many : forall x t t' xl e1 v es e2 e',  gen_rets AS S xl es e2 e' ->
          eval_arg S e1 (subst_type AS t) (ELit v t') ->
          gen_rets AS S ((x,t)::xl) (e1::es) e2 (ERet x (v,t') (Stack.find x S) e').

(* Checked C semantics. *)
Inductive step (D : structdef) (F:funid -> option (list (var * type) * type * expression * mode)) : stack -> heap 
                     -> expression -> stack -> heap -> result -> Prop :=
  | SVar : forall s H x v t,
      (Stack.MapsTo x (v,t) s) ->
      step D F s H (EVar x) s H (RExpr (ELit v t))
  | Strlen : forall s H x n n' m l h t t1, 
     (Stack.MapsTo x (n,(TPtr m (TNTArray l (Num h) t))) s) ->
     (forall i , n <= i < n+n'+1 -> (exists n1 t1, Heap.MapsTo n (n1,t1) H /\ n1 <> 0))
      -> Heap.MapsTo (n+n'+1) (0,t1) H ->
            step D F s H (EStrlen x) (change_strlen_stack s x m t l n n' h) H (RExpr (ELit n' TNat))
  | SCall : forall AS s s' H x el t tvl e e' m, 
           F x = Some (tvl,t,e,m) ->
           get_dept_map tvl el = Some AS ->
           eval_el AS s tvl el s' -> 
           gen_rets AS s tvl el e e' ->
          step D F s H (ECall x el) s' H (RExpr (ECast (subst_type AS t) e'))
  | SLet : forall s H x n t e t',
      cast_type_bound s t t' ->
      step D F s H (ELet x (ELit n t) e) (Stack.add x (n,t') s) H 
                     (RExpr (ERet x (n,t') (Stack.find x s) e))

  | SRetSome : forall s H x a ta ntb n t, 
          step D F s H (ERet x ntb (Some (a,ta)) (ELit n t))
                  (Stack.add x (a,ta) s) H (RExpr (ELit n t))
  | SRetNone : forall s H x ntb n t, 
          step D F s H (ERet x ntb None (ELit n t))
                  (Stack.remove x s) H (RExpr (ELit n t))
  | SPlusChecked : forall s H n1 t1 n2,
      n1 > 0 -> is_check_array_ptr t1 -> 
      step D F
         s H (EPlus (ELit n1 t1) (ELit n2 TNat))
         s H (RExpr (ELit (n1 + n2) (sub_type_bound t1 n2)))
  | SPlus : forall s H t1 n1 n2,
       ~ is_check_array_ptr t1 -> 
      step D F
         s H (EPlus (ELit n1 t1) (ELit n2 TNat))
         s H (RExpr (ELit (n1 + n2) t1))
  | SPlusNull : forall s H n1 t n2,
      n1 <= 0 -> is_check_array_ptr t ->
      step D F s H (EPlus (ELit n1 t) (ELit n2 (TNat))) s H RNull
  | SCast : forall s H t n t' t'',
      cast_type_bound s t t'' ->
      step D F
         s H (ECast t (ELit n t'))
         s H (RExpr (ELit n t''))

  | SCastNoArray : forall s H x y t n m t' t'',
     ~ is_array_ptr (TPtr m t') -> cast_type_bound s t t'' ->
      step D F
        s H (EDynCast (TPtr m (TArray x y t)) (ELit n (TPtr m t')))
        s H (RExpr (ELit n (TPtr m (TArray (Num 0) (Num 1) t''))))

  | SCastArray : forall s H t n t' l h w l' h' w',
     cast_type_bound s t (TPtr Checked (TArray (Num l) (Num h) w)) ->
      eval_type_bound s t' = Some (TPtr Checked (TArray (Num l') (Num h') w')) ->
          l' <= l -> l < h -> h <= h' ->
      step D F
         s H (EDynCast t (ELit n t'))
         s H (RExpr (ELit n (TPtr Checked (TArray (Num l) (Num h) w))))

  | SCastArrayLowOOB1 : forall s H t n t' l h w l' h' w',
     eval_type_bound s t = Some (TPtr Checked (TArray (Num l) (Num h) w)) ->
      eval_type_bound s t' = Some (TPtr Checked (TArray (Num l') (Num h') w')) ->
           l < l' -> 
           step D F s H (EDynCast t (ELit n t'))  s H RBounds
  | SCastArrayLowOOB2 : forall s H t n t' l h w l' h' w',
     eval_type_bound s t = Some (TPtr Checked (TArray (Num l) (Num h) w)) ->
      eval_type_bound s t' = Some (TPtr Checked (TArray (Num l') (Num h') w')) ->
           h <= l -> 
           step D F s H (EDynCast t (ELit n t')) s H RBounds
  | SCastArrayHighOOB1 : forall s H t n t' l h w l' h' w',
     eval_type_bound s t = Some (TPtr Checked (TArray (Num l) (Num h) w)) ->
      eval_type_bound s t' = Some (TPtr Checked (TArray (Num l') (Num h') w')) ->
           h' < h -> 
           step D F s H (EDynCast t (ELit n t')) s H RBounds
  | SCastNTArray : forall s H t n t' l h w l' h' w',
     cast_type_bound s t (TPtr Checked (TNTArray (Num l) (Num h) w)) ->
      eval_type_bound s t' = Some (TPtr Checked (TNTArray (Num l') (Num h') w')) ->
          l' <= l -> l < h -> h <= h' ->
      step D F s H (EDynCast t (ELit n t')) s H (RExpr (ELit n (TPtr Checked (TNTArray (Num l) (Num h) w)) ))
  | SCastNTArrayLowOOB1 : forall s H t n t' l h w l' h' w',
     eval_type_bound s t = Some (TPtr Checked (TNTArray (Num l) (Num h) w)) ->
      eval_type_bound s t' = Some (TPtr Checked (TNTArray (Num l') (Num h') w')) ->
           l < l' -> 
           step D F s H (EDynCast t (ELit n t')) s H RBounds
  | SCastNTArrayLowOOB2 : forall s H t n t' l h w l' h' w',
     eval_type_bound s t = Some (TPtr Checked (TNTArray (Num l) (Num h) w)) ->
      eval_type_bound s t' = Some (TPtr Checked (TNTArray (Num l') (Num h') w')) ->
           h <= l -> 
           step D F s H (EDynCast t (ELit n t')) s H RBounds
  | SCastNTArrayHighOOB1 : forall s H t n t' l h w l' h' w',
     eval_type_bound s t = Some (TPtr Checked (TNTArray (Num l) (Num h) w)) ->
      eval_type_bound s t' = Some (TPtr Checked (TNTArray (Num l') (Num h') w')) ->
           h' < h -> 
           step D F s H (EDynCast t (ELit n t')) s H RBounds

  | SDeref : forall s H n n1 t1 t t2 tv,
      cast_type_bound s t t2 ->
      Heap.MapsTo n (n1, t1) H ->
      (forall l h t', t2 = TPtr Checked (TArray (Num l) (Num h) t') -> h > 0 /\ l <= 0) ->
      (forall l h t', t2 = TPtr Checked (TNTArray (Num l) (Num h) t') -> h >= 0 /\ l <= 0) ->
      @get_root D t2 tv ->
      step D F s H (EDeref (ELit n t)) s H (RExpr (ELit n1 tv))
  | SDerefHighOOB : forall s H n t t' h,
      h <= 0 ->
      eval_type_bound s t = Some t' ->
      get_high_ptr t' = Some (Num h) ->
      step D F s H (EDeref (ELit n t)) s H RBounds
  | SDerefLowOOB : forall s H n t t' l,
      l > 0 ->
      eval_type_bound s t = Some t' ->
      get_low_ptr t' = Some (Num l) ->
      step D F s H (EDeref (ELit n t)) s H RBounds
  | SDerefNull : forall s H t n,
      n <= 0 -> 
      step D F s H (EDeref (ELit n (TPtr Checked t))) s H RNull

  | SAssign : forall s H n t tv n1 t1 tv' H',
      Heap.In n H ->
      cast_type_bound s t tv ->
      (forall l h t', tv = TPtr Checked (TArray (Num l) (Num h) t') -> h > 0 /\ l <= 0) -> 
      (forall l h t', tv = TPtr Checked (TNTArray (Num l) (Num h) t') -> h > 0 /\ l <= 0) -> 
      @get_root D tv tv' ->
      H' = Heap.add n (n1, tv') H ->
      step D F
         s H  (EAssign (ELit n t) (ELit n1 t1))
         s H' (RExpr (ELit n1 tv'))
  | SAssignHighOOB : forall s H n t t' n1 t1 h,
      h <= 0 ->
      eval_type_bound s t = Some t' ->
      get_high_ptr t' = Some (Num h) ->
      step D F
        s H (EAssign (ELit n t) (ELit n1 t1))
        s H RBounds
  | SAssignLowOOB : forall s H n t t' n1 t1 l,
      l > 0 ->
      eval_type_bound s t = Some t' ->
      get_low_ptr t' = Some (Num l) ->
      step D F
         s H (EAssign (ELit n t) (ELit n1 t1))
         s H RBounds
  | SAssignNull : forall s H t tv w n n1 t',
      n1 <= 0 ->
      eval_type_bound s t = Some tv ->
      tv = TPtr Checked w ->
      step D F
         s H (EAssign (ELit n1 t) (ELit n t')) s H RNull

  | SFieldAddrChecked : forall s H n t (fi : field) n0 t0 T fs i fi ti,
      n > 0 ->
      t = TPtr Checked (TStruct T) ->
      StructDef.MapsTo T fs D ->
      Fields.MapsTo fi ti fs ->
      List.nth_error (Fields.this fs) i = Some (fi, ti) ->
      n0 = n + Z.of_nat(i) ->
      t0 = TPtr Checked ti ->
      word_type ti ->
      step D F
         s H (EFieldAddr (ELit n t) fi)
         s H (RExpr (ELit n0 t0))
  | SFieldAddrNull : forall s H (fi : field) n T,
      n <= 0 ->
      step D F
         s H (EFieldAddr (ELit n (TPtr Checked (TStruct T))) fi)
         s H RNull
  | SFieldAddr : forall s H n t (fi : field) n0 t0 T fs i fi ti,
      t = TPtr Unchecked (TStruct T) ->
      StructDef.MapsTo T fs D ->
      Fields.MapsTo fi ti fs ->
      List.nth_error (Fields.this fs) i = Some (fi, ti) ->
      n0 = n + Z.of_nat(i) ->
      t0 = TPtr Unchecked ti ->
      word_type ti ->
      step D F
        s H (EFieldAddr (ELit n t) fi)
        s H (RExpr (ELit n0 t0))
  | SMalloc : forall s H w w' H' n1,
      cast_type_bound s w w' -> malloc_bound w' ->
      allocate D H w' = Some (n1, H') ->
      step D F
         s H (EMalloc w)
         s H' (RExpr (ELit n1 (TPtr Checked w')))
  | SMallocHighOOB : forall s H w t' h,
      h <= 0 ->
      eval_type_bound s w = Some t' ->
      get_high t' = Some (Num h) ->
      step D F s H (EMalloc w)  s H RBounds
  | SMallocLowOOB : forall s H w t' l,
      l <> 0 ->
      eval_type_bound s w = Some t' ->
      get_low t' = Some (Num l) ->
      step D F s H (EMalloc w)  s H RBounds

  | SUnchecked : forall s H n t,
      step D F s H (EUnchecked (ELit n t)) s H (RExpr (ELit n t))
   | SIfTrueNotNTHit : forall s H x n t e1 e2 n1 t1, 
           Stack.MapsTo x (n,t) s ->
           step D F s H (EDeref (ELit n t)) s H (RExpr (ELit n1 t1)) ->
           n1 <> 0 -> ~ (NTHit s x) -> step D F s H (EIf x e1 e2) s H (RExpr e1)
   | SIfTrueNTHit : forall s H x n t e1 e2 n1 t1, 
           Stack.MapsTo x (n,t) s ->
           step D F s H (EDeref (ELit n t)) s H (RExpr (ELit n1 t1)) ->
           n1 <> 0 -> (NTHit s x) -> step D F s H (EIf x e1 e2) (add_nt_one s x) H (RExpr e1)
   | SIfFalse : forall s H x n t e1 e2 t1, 
           Stack.MapsTo x (n,t) s ->
           step D F s H (EDeref (ELit n t)) s H (RExpr (ELit 0 t1)) ->
              step D F s H (EIf x e1 e2) s H (RExpr e2)
   | SIfFail : forall s H x n t e1 e2 r,
           Stack.MapsTo x (n,t) s ->
              ~ is_rexpr r 
              -> step D F s H (EDeref (ELit n t)) s H r
                 -> step D F s H (EIf x e1 e2) s H r.

Hint Constructors step.

Inductive reduce (D : structdef) (F:funid -> option (list (var * type) * type * expression * mode)) : stack -> heap -> expression
                              -> mode -> stack -> heap -> result -> Prop :=
  | RSExp : forall H s e m H' s' e' E,
      step D F s H e s' H' (RExpr e') ->
      m = mode_of(E) ->
      reduce D F s
        H (in_hole e E)
        m  s'
        H' (RExpr (in_hole e' E))
  | RSHaltNull : forall H s e m H' s' E,
      step D F s H e s' H' RNull ->
      m = mode_of(E) ->
      reduce D F s
        H (in_hole e E)
        m s'
        H' RNull
  | RSHaltBounds : forall H s e m H' s'  E,
      step D F s H e s' H' RBounds ->
      m = mode_of(E) ->
      reduce D F s
        H (in_hole e E)
        m s'
        H' RBounds.

Hint Constructors reduce.

Definition reduces (D : structdef) (F:funid -> option (list (var * type) * type * expression * mode)) 
    (s : stack) (H : heap) (e : expression) : Prop :=
  exists (m : mode) (s' : stack) (H' : heap) (r : result), reduce D F s H e m s' H' r.

Hint Unfold reduces.


(* Defining function calls. *)

(** * Static Semantics *)

Require Import Lists.ListSet.

Definition eq_dec_nt (x y : Z * type) : {x = y} + { x <> y}.
repeat decide equality.
Defined. 

Definition scope := set (Z *type)%type. 
Definition empty_scope := empty_set (Z * type).


(* Type check for a literal + simplifying the type. *)
Inductive well_typed_lit (D : structdef) (Q:theta) (H : heap) : scope -> Z -> type -> Prop :=
  | TyLitInt : forall s n,
      well_typed_lit D Q H s n TNat
  | TyLitU : forall s n w,
      well_typed_lit D Q H s n (TPtr Unchecked w)
  | TyLitZero : forall s t,
      well_typed_lit D Q H s 0 t
  | TyLitRec : forall s n w t,
      set_In (n, t) s ->
      subtype D Q t (TPtr Checked w) ->
      well_typed_lit D Q H s n (TPtr Checked w)
  | TyLitC : forall sc n w t b ts,
      simple_type w ->
      subtype D Q (TPtr Checked w) (TPtr Checked t) ->
      Some (b, ts) = allocate_meta D w ->
      (forall k, b <= k < b + Z.of_nat(List.length ts) ->
                 exists n' t',
                   Some t' = List.nth_error ts (Z.to_nat (k - b)) /\
                   Heap.MapsTo (n + k) (n', t') H /\
                   well_typed_lit D Q H (set_add eq_dec_nt (n, TPtr Checked w) sc) n' t') ->
      well_typed_lit D Q H sc n (TPtr Checked t).


Hint Constructors well_typed_lit.

(** It turns out, the induction principle that Coq generates automatically isn't very useful. *)

(** In particular, the TyLitC case does not have an induction hypothesis.
    So, we prove an alternative induction principle which is almost identical but includes
    an induction hypothesis for the TyLitC case.

    TODO: write blog post about this *)

Lemma well_typed_lit_ind' :
  forall (D : structdef) (Q:theta) (H : heap) (P : scope -> Z -> type -> Prop),
    (forall (s : scope) (n : Z), P s n TNat) ->
       (forall (s : scope) (n : Z) (w : type), P s n (TPtr Unchecked w)) ->
       (forall (s : scope) (t : type), P s 0 t) ->
       (forall (s : scope) (n : Z) (w : type) (t : type), set_In (n, t) s -> subtype D Q t (TPtr Checked w) -> P s n (TPtr Checked w)) ->
       (forall (s : scope) (n : Z) (w : type) (t: type) (ts : list type) (b : Z),
        simple_type w ->
        subtype D Q (TPtr Checked w) (TPtr Checked t) ->
        Some (b, ts) = allocate_meta D w ->
        (forall k : Z,
         b <= k < b + Z.of_nat (length ts) ->
         exists (n' : Z) (t' : type),
           Some t' = nth_error ts (Z.to_nat (k - b)) /\
           Heap.MapsTo (n + k) (n', t') H /\
           well_typed_lit D Q H (set_add eq_dec_nt (n, TPtr Checked w) s) n' t' /\
           P (set_add eq_dec_nt (n, TPtr Checked w) s) n' t') ->
        P s n (TPtr Checked t)) -> forall (s : scope) (n : Z) (w : type), well_typed_lit D Q H s n w -> P s n w.
Proof.
  intros D Q H P.
  intros HTyLitInt
         HTyLitU
         HTyLitZero
         HTyLitRec
         HTyLitC.
  refine (fix F s n t Hwtl :=
            match Hwtl with
            | TyLitInt _ _ _ s' n' => HTyLitInt s' n'
            | TyLitU _ _ _ s' n' w' => HTyLitU s' n' w'
            | TyLitZero _ _ _ s' t' => HTyLitZero s' t'
            | TyLitRec _ _ _ s' n' w' t' Hscope Hsub => HTyLitRec s' n' w' t' Hscope Hsub
            | TyLitC _ _ _ s' n' w' t' b ts HSim Hsub Hts IH =>
              HTyLitC s' n' w' t' ts b HSim Hsub Hts (fun k Hk =>
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

Definition heap_well_typed (D:structdef) (Q:theta) (H:heap) (n:Z) (t:type) :=
      simple_type t -> well_typed_lit D Q H empty_scope n t.

Inductive heap_wt_arg (D:structdef) (Q:theta) (H:heap) : expression -> Prop :=
     | HtArgLit : forall n t, heap_well_typed D Q H n t -> heap_wt_arg D Q H (ELit n t)
     | HtArgVar : forall x, heap_wt_arg D Q H (EVar x).

Inductive heap_wt_args (D:structdef) (Q:theta) (H:heap) : list expression -> Prop :=
    heap_wt_empty : heap_wt_args D Q H ([])
  | heap_wt_many : forall e el, heap_wt_arg D Q H e -> heap_wt_args D Q H el -> heap_wt_args D Q H (e::el).

Inductive heap_wt (D:structdef) (Q:theta) (H:heap) : expression -> Prop :=
   | HtLit : forall n t, heap_well_typed D Q H n t -> heap_wt D Q H (ELit n t)
   | HtVar : forall x, heap_wt D Q H (EVar x)
   | HtStrlen : forall x, heap_wt D Q H (EStrlen x)
   | HtCall : forall f el, heap_wt_args D Q H el -> heap_wt D Q H (ECall f el)
   | HtRet : forall x old a e, heap_wt D Q H e -> heap_wt D Q H (ERet x old a e)
   | HtDynCast : forall t e, heap_wt D Q H e -> heap_wt D Q H (EDynCast t e)
   | HtLet : forall x e1 e2, heap_wt D Q H e1 -> heap_wt D Q H e2 -> heap_wt D Q H (ELet x e1 e2)
   | HtMalloc : forall t, heap_wt D Q H (EMalloc t)
   | HtCast : forall t e, heap_wt D Q H e -> heap_wt D Q H (ECast t e)
   | HtPlus : forall e1 e2, heap_wt D Q H e1 -> heap_wt D Q H e2 -> heap_wt D Q H (EPlus e1 e2)
   | HtFieldAddr : forall e f, heap_wt D Q H e -> heap_wt D Q H (EFieldAddr e f)
   | HtDeref : forall e, heap_wt D Q H e -> heap_wt D Q H (EDeref e)
   | HtAssign : forall e1 e2, heap_wt D Q H e1 -> heap_wt D Q H e2 -> heap_wt D Q H (EAssign e1 e2)
   | HtIf : forall x e1 e2, heap_wt D Q H e1 -> heap_wt D Q H e2 -> heap_wt D Q H (EIf x e1 e2)
   | HtUnChecked : forall e, heap_wt D Q H e -> heap_wt D Q H (EUnchecked e).


Definition is_ptr (t : type) : Prop :=
    match t with TPtr m x => True 
              | _ => False
    end.

Definition is_nt_ptr (t : type) : Prop :=
    match t with TPtr m (TNTArray l h t') => True 
              | _ => False
    end.

(* equivalence of type based on semantic meaning. *)
Inductive type_eq (S : stack) : type -> type -> Prop := 
     | type_eq_refl: forall t , type_eq S t t
     | type_eq_left: forall t1 t2, simple_type t1 -> cast_type_bound S t2 t1 -> type_eq S t2 t1
     | type_eq_right: forall t1 t2, simple_type t2 -> cast_type_bound S t1 t2 -> type_eq S t1 t2.

(* subtyping relation based on types. *)
Inductive subtype_stack (D: structdef) (Q:theta) (S:stack) : type -> type -> Prop :=
     | subtype_same : forall t t', subtype D Q t t' -> subtype_stack D Q S t t'
     | subtype_left : forall t1 t2 t2', simple_type t1 -> cast_type_bound S t2 t2'
            -> subtype D Q t1 t2' -> subtype_stack D Q S t1 t2
     | subtype_right : forall t1 t1' t2, simple_type t2 -> cast_type_bound S t1 t1'
            -> subtype D Q t1' t2 -> subtype_stack D Q S t1 t2.

(* The join opeartions. *)
Inductive join_type (D : structdef) (Q:theta) (S:stack) : type -> type -> type -> Prop :=
   join_type_front : forall a b, subtype_stack D Q S a b -> join_type D Q S a b b
  | join_type_end : forall a b, subtype_stack D Q S b a -> join_type D Q S a b a.

Definition good_lit (H:heap) (n:Z) (t:type):=
      match t with TNat => True
               | _ => n <= (Z.of_nat (Heap.cardinal H))
      end.


Inductive well_bound_vars {A:Type}: list (var * A) -> bound -> Prop :=
  | well_bound_vars_num : forall l n, well_bound_vars l (Num n)
  | well_bound_vars_var : forall l y n, (exists a, In (y,a) l) -> well_bound_vars l (Var y n).

Inductive well_bound_vars_type {A:Type}: list (var * A) -> type -> Prop :=
  | well_bound_vars_nat : forall l, well_bound_vars_type l (TNat)
  | well_bound_vars_ptr : forall l c t, well_bound_vars_type l t -> well_bound_vars_type l (TPtr c t)
  | well_bound_vars_struct : forall l t, well_bound_vars_type l (TStruct t)
  | well_bound_vars_array : forall l b1 b2 t, well_bound_vars l b1 -> well_bound_vars l b2
                        -> well_bound_vars_type l t -> well_bound_vars_type l (TArray b1 b2 t)
  | well_bound_vars_ntarray : forall l b1 b2 t, well_bound_vars l b1 -> well_bound_vars l b2
                        -> well_bound_vars_type l t -> well_bound_vars_type l (TNTArray b1 b2 t).


Inductive well_typed_arg (D: structdef) (Q:theta) (H : heap) (env:env): 
                 expression -> type -> Prop :=
     | ArgLit : forall n t t',
      simple_type t ->
      @well_typed_lit D Q H empty_scope n t' ->
      subtype D Q t' t ->
      well_typed_arg D Q H env (ELit n t') t
     | ArgVar : forall x t t',
      Env.MapsTo x t' env -> 
      well_type_bound_in env t ->
      subtype D Q t' t ->
      well_typed_arg D Q H env (EVar x) t.

Inductive well_typed_args {D: structdef} {Q:theta} {H : heap}: 
                   env -> list (var * bound) -> list expression -> list (var * type) -> Prop :=
     | args_empty : forall env s, well_typed_args env s [] []
     | args_many : forall env s e es v t vl, 
                 well_typed_arg D Q H env e (subst_type s t) ->
                        well_typed_args env s es vl
                        -> well_typed_args env s (e::es) ((v,t)::vl).

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
Definition get_tvar_bound (b:bound) : list var :=
     match b with Num n => [] | Var x n => [x]  end.

Fixpoint get_tvars (t:type) : (list var) :=
   match t with TNat => []
             | TPtr c t => get_tvars t
             | TStruct t => []
             | TArray l h t => get_tvar_bound l ++ get_tvar_bound h ++ get_tvars t
             | TNTArray l h t => get_tvar_bound l ++ get_tvar_bound h ++ get_tvars t
   end.

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


(* The CoreChkC Type System. *)
Inductive well_typed { D : structdef } {F : FEnv} {S:stack} {H:heap}
        : env -> theta -> mode -> expression -> type -> Prop :=
  | TyLit : forall env Q m n t,
      @well_typed_lit D Q H empty_scope n t ->
      well_typed env Q m (ELit n t) t
  | TyVar : forall env Q m x t,
      Env.MapsTo x t env ->
      well_typed env Q m (EVar x) t

  | TyCall : forall env Q s m m' es x tvl e t, 
        F env x = Some (tvl,t,e,m') ->
        get_dept_map tvl es = Some s ->
        (m' = Unchecked -> m = Unchecked) ->
        @well_typed_args D Q H env s es tvl ->
           well_typed env Q m (ECall x es) (subst_type s t)

  | TyStrlen : forall env Q m x h l t, 
      Env.MapsTo x (TPtr m (TNTArray h l t)) env ->
      well_typed env Q m (EStrlen x) TNat

  | TyLetStrlen : forall env Q m x y e l h t, 
      ~ Env.In x env ->
      Env.MapsTo y (TPtr m (TNTArray l h t)) env ->
      well_typed (Env.add x TNat (Env.add y (TPtr m (TNTArray l (Var x 0) t)) env)) (Theta.add x GeZero Q) m e t ->
      ~ In x (get_tvars t) ->
      well_typed env Q m (ELet x (EStrlen y) e) t

  | TyLetNat : forall env Q m x e1 e2 t b,
      ~ Env.In x env ->
      well_typed env Q m e1 TNat ->
      well_typed (Env.add x TNat env) Q m e2 t ->
      In x (get_tvars t) -> get_good_dept e1 = Some b ->
      well_typed env Q m (ELet x e1 e2) (subst_type [(x,b)] t)

  | TyLet : forall env Q m x e1 t1 e2 t,
      ~ Env.In x env ->
      well_typed env Q m e1 t1 ->
      well_typed (Env.add x t1 env) Q m e2 t ->
      ~ In x (get_tvars t) ->
      well_typed env Q m (ELet x e1 e2) t

  | TyRetTNat : forall env Q m x na a e t,
      Env.In x env ->
      In x (get_tvars t) ->
      well_typed env Q m e t ->
      well_typed env Q m (ERet x (na,TNat) a e) (subst_type [(x,(Num na))] t)

  | TyRet : forall env Q m x na ta a e t,
      Env.In x env ->
      well_typed env Q m e t ->
      ~ In x (get_tvars t) ->
      well_typed env Q m (ERet x (na,ta) a e) t

  | TyPlus : forall env Q m e1 e2,
      well_typed env Q m e1 (TNat) ->
      well_typed env Q m e2 (TNat) ->
      well_typed env Q m (EPlus e1 e2) TNat
  | TyFieldAddr : forall env Q m e m' T fs i fi ti,
      well_typed env Q m e (TPtr m' (TStruct T)) ->
      StructDef.MapsTo T fs D ->
      Fields.MapsTo fi ti fs ->
      List.nth_error (Fields.this fs) i = Some (fi, ti) ->
      well_typed env Q m (EFieldAddr e fi) (TPtr m' ti)
  | TyMalloc : forall env Q m w,
      well_type_bound_in env w ->
      well_typed env Q m (EMalloc w) (TPtr Checked w)
  | TyUnchecked : forall env Q m e t,
      well_typed env Q Unchecked e t ->
      well_typed env Q m (EUnchecked e) t
  | TyCast1 : forall env Q m t e t',
      well_type_bound_in env t ->
      (m = Checked -> forall w, t <> TPtr Checked w) ->
      well_typed env Q m e t' ->
      well_typed env Q m (ECast t e) t
  | TyCast2 : forall env Q m t e t',
      well_type_bound_in env t ->
      well_typed env Q m e t' -> 
      subtype_stack D Q S t' (TPtr Checked t) ->
      well_typed env Q m (ECast (TPtr Checked t) e) (TPtr Checked t)

  | TyDynCast1 : forall env Q m e x y u v t t',
      well_type_bound_in env (TPtr Checked (TArray x y t)) ->
      well_typed env Q m e (TPtr Checked (TArray u v t')) ->
      type_eq S t t' ->
      well_typed env Q m (EDynCast (TPtr Checked (TArray x y t)) e) (TPtr Checked (TArray x y t))
  | TyDynCast2 : forall env Q m e x y t t',
      ~ is_array_ptr (TPtr Checked t') ->
      type_eq S t t' ->
      well_type_bound_in env (TPtr Checked (TArray x y t)) ->
      well_typed env Q m e (TPtr Checked t') ->
      well_typed env Q m (EDynCast (TPtr Checked (TArray x y t)) e) (TPtr Checked (TArray (Num 0) (Num 1) t))
  | TyDynCast3 : forall env Q m e x y u v t t',
      well_type_bound_in env (TPtr Checked (TNTArray x y t)) ->
      type_eq S t t' ->
      well_typed env Q m e (TPtr Checked (TNTArray u v t')) ->
      well_typed env Q m (EDynCast (TPtr Checked (TNTArray x y t)) e) (TPtr Checked (TNTArray x y t))
  | TyDeref : forall env Q m e m' t l h t' t'',
      well_typed env Q m e t ->
      subtype D Q t (TPtr m' t'') ->
      ((word_type t'' /\ t'' = t') 
       \/ (t'' = TArray l h t' /\ word_type t' /\ type_wf D t')
       \/ (t'' = TNTArray l h t' /\ word_type t' /\ type_wf D t')) ->
      (m' = Unchecked -> m = Unchecked) ->
      well_typed env Q m (EDeref e) t'
  | TyIndex1 : forall env Q m e1 m' l h e2 t,
      word_type t -> type_wf D t ->
      well_typed env Q m e1 (TPtr m' (TArray l h t)) -> 
      well_typed env Q m e2 (TNat) ->
      (m' = Unchecked -> m = Unchecked) ->
      well_typed env Q m (EDeref (EPlus e1 e2)) t
  | TyIndex2 : forall env Q m e1 m' l h e2 t,
      word_type t -> type_wf D t ->
      well_typed env Q m e1 (TPtr m' (TNTArray l h t)) ->
      well_typed env Q m e2 (TNat) ->
      (m' = Unchecked -> m = Unchecked) ->
      well_typed env Q m (EDeref (EPlus e1 e2)) t
  | TyAssign1 : forall env Q m e1 e2 m' t t1,
      subtype_stack D Q S t1 t -> word_type t ->
      well_typed env Q m e1 (TPtr m' t) ->
      well_typed env Q m e2 t1 ->
      (m' = Unchecked -> m = Unchecked) ->
      well_typed env Q m (EAssign e1 e2) t
  | TyAssign2 : forall env Q m e1 e2 m' l h t t',
      word_type t -> type_wf D t -> subtype_stack D Q S t' t ->
      well_typed env Q m e1 (TPtr m' (TArray l h t)) ->
      well_typed env Q m e2 t' ->
      (m' = Unchecked -> m = Unchecked) ->
      well_typed env Q m (EAssign e1 e2) t
  | TyAssign3 : forall env Q m e1 e2 m' l h t t',
      word_type t -> type_wf D t -> 
     subtype_stack D Q S t' t ->
      well_typed env Q m e1 (TPtr m' (TNTArray l h t)) ->
      well_typed env Q m e2 t' ->
      (m' = Unchecked -> m = Unchecked) ->
      well_typed env Q m (EAssign e1 e2) t
  | TyIndexAssign1 : forall env Q m e1 e2 e3 m' l h t t',
      word_type t' -> type_wf D t' -> 
      subtype_stack D Q S t' t ->
      well_typed env Q m e1 (TPtr m' (TArray l h t)) ->
      well_typed env Q m e2 (TNat) ->
      well_typed env Q m e3 t' ->
      (m' = Unchecked -> m = Unchecked) ->
      well_typed env Q m (EAssign (EPlus e1 e2) e3) t
  | TyIndexAssign2 : forall env Q m e1 e2 e3 m' l h t t',
      word_type t' -> type_wf D t' -> 
      subtype_stack D Q S t' t ->
      well_typed env Q m e1 (TPtr m' (TNTArray l h t)) ->
      well_typed env Q m e2 (TNat) ->
      well_typed env Q m e3 t' ->
      (m' = Unchecked -> m = Unchecked) ->
      well_typed env Q m (EAssign (EPlus e1 e2) e3) t
  | TyIf : forall env Q m m' x t t1 e1 e2 t2 t3 t4,
      Env.MapsTo x t env ->
      subtype D Q t (TPtr m' t1) ->
      (exists l h t', (word_type t1 /\ t1 = t')
         \/ (t1 = TArray l h t' /\ word_type t' /\ type_wf D t')
       \/ (t1 = TNTArray l h t' /\ word_type t' /\ type_wf D t')) ->
      well_typed env Q m e1 t2 -> well_typed env Q m e2 t3 ->
      join_type D Q S t2 t3 t4 -> 
      (m' = Unchecked -> m = Unchecked) ->
      well_typed env Q m (EIf x e1 e2) t4
  | TyIfNT : forall env Q m m' x l t e1 e2 t2 t3 t4,
      Env.MapsTo x (TPtr m' (TNTArray l (Num 0) t)) env ->
      well_typed (Env.add x (TPtr m' (TNTArray l (Num 1) t)) env) Q m e1 t2 -> well_typed env Q m e2 t3 ->
      join_type D Q S t2 t3 t4 -> 
      (m' = Unchecked -> m = Unchecked) ->
      well_typed env Q m (EIf x e1 e2) t4.


Definition fun_wf (D : structdef) (F:FEnv) (S:stack) (H:heap) :=
     forall env env' f tvl t e m, F env f = Some (tvl,t,e,m) -> 
          gen_arg_env env tvl env' ->
          (forall x t', In (x,t') tvl -> word_type t' /\ type_wf D t' /\ well_bound_vars_type tvl t') /\
          (forall a, In a tvl -> ~ Env.In (fst a) env) /\
          (forall n n' a b, n <> n' -> nth_error tvl n = Some a -> nth_error tvl n' = Some b -> fst a <> fst b) /\
          word_type t /\ type_wf D t /\ well_bound_vars_type tvl t /\ expr_wf D fenv e
          /\ @well_typed D F S H env' empty_theta m e t.


Definition sub_domain (env: env) (S:stack) := forall x, Env.In x env -> Stack.In x S.


Local Close Scope Z_scope.

Local Open Scope nat_scope.

Hint Constructors well_typed.

(*Hint Constructors ty_ssa.*)


Lemma ptr_subtype_equiv : forall D Q m w t,
subtype D Q w (TPtr m t) ->
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
Lemma ptr_subtype_equiv' : forall D Q m w t,
subtype D Q (TPtr m t) w ->
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

Lemma nat_subtype : forall D Q t,
subtype D Q TNat t ->
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

Definition heap_consistent { D : structdef } {Q:theta} (H' : heap) (H : heap) : Prop :=
  forall n t,
    @well_typed_lit D Q H empty_scope n t->
    @well_typed_lit D Q H' empty_scope n t.

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
  destruct H1 as [H' [ m' [ s' [r  HRed ]] ] ].
  inv HRed.
  rewrite compose_correct; eauto 20.
  rewrite compose_correct; eauto 20.
  rewrite compose_correct; eauto 20.
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


Open Scope Z.
Lemma wf_implies_allocate_meta :
  forall (D : structdef) (w : type),
    (forall l h t, w = TArray (Num l) (Num h) t -> l = 0 /\ h > 0) ->
    (forall l h t, w = TNTArray (Num l) (Num h) t -> l = 0 /\ h > 0) ->
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

Lemma find_implies_mapsto : forall s D f,
StructDef.find (elt:=fields) s D = Some f ->
StructDef.MapsTo s f D.
Proof.
  intros. 
  eapply StructDef.find_2. assumption.
Qed.


Lemma struct_subtype_non_empty : forall m T fs D Q,
subtype D Q (TPtr m (TStruct T)) (TPtr m TNat) ->
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

Lemma struct_subtype_non_empty_1 : forall m T fs D Q,
subtype D Q (TPtr m (TStruct T)) (TPtr m (TArray (Num 0) (Num 1) TNat)) ->
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

Lemma struct_subtype_non_empty_2 : forall m T fs D Q,
subtype D Q (TPtr m (TStruct T)) (TPtr m (TNTArray (Num 0) (Num 1) TNat)) ->
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

(*
Definition env_denv_prop (env: env) (S:stack) (denv:dyn_env) :=
    forall x t t', Env.MapsTo x t env -> cast_type_bound S t t' -> Stack.MapsTo x t' denv.
*)
Lemma gen_cast_bound_same :
   forall env s b, well_bound_in env b -> sub_domain env s -> (exists b', cast_bound s b = Some b').
Proof.
  intros. induction b.
  exists (Num z). unfold cast_bound. reflexivity.
  inv H. unfold sub_domain in *.
  assert (Env.In v env0).
  unfold Env.In,Env.Raw.PX.In.
  exists TNat. easy.
  apply H0 in H. 
  unfold cast_bound.
  unfold Stack.In,Stack.Raw.PX.In in *.
  destruct H. apply Stack.find_1 in H.
  destruct (Stack.find v s).
  injection H as eq1. destruct p.
  exists (Num (z + z0)). reflexivity.
  inv H.
Qed.

Lemma gen_cast_type_bound_same :
   forall env s t, well_type_bound_in env t -> sub_domain env s
           -> (exists t', cast_type_bound s t t').
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
 destruct (Stack.find (elt:=Z * type) v s).
 destruct p.
 inv H4. inv H6. inv H3. inv H8.
 assert (t' = t'0).
 apply IHt. assumption. assumption. rewrite H. reflexivity.
 inv H6.
 destruct (Stack.find (elt:=Z * type) v s). destruct b0.
 destruct p.
 inv H4. inv H6. inv H3. inv H8.
 assert (t' = t'0).
 apply IHt. assumption. assumption. rewrite H. reflexivity.
 destruct (Stack.find (elt:=Z * type) v0 s). destruct p. destruct p0.
 inv H4. inv H6. inv H3. inv H8.
 assert (t' = t'0).
 apply IHt. assumption. assumption. rewrite H. reflexivity.
 inv H6. inv H3. 
 intros. inv H. inv H0.
 unfold cast_bound in *.
 destruct b. destruct b0. inv H4. inv H6. inv H3. inv H8.
 assert (t' = t'0).
 apply IHt. assumption. assumption. rewrite H. reflexivity.
 destruct (Stack.find (elt:=Z * type) v s).
 destruct p.
 inv H4. inv H6. inv H3. inv H8.
 assert (t' = t'0).
 apply IHt. assumption. assumption. rewrite H. reflexivity.
 inv H6.
 destruct (Stack.find (elt:=Z * type) v s). destruct b0.
 destruct p.
 inv H4. inv H6. inv H3. inv H8.
 assert (t' = t'0).
 apply IHt. assumption. assumption. rewrite H. reflexivity.
 destruct (Stack.find (elt:=Z * type) v0 s). destruct p. destruct p0.
 inv H4. inv H6. inv H3. inv H8.
 assert (t' = t'0).
 apply IHt. assumption. assumption. rewrite H. reflexivity.
 inv H6. inv H3. 
Qed.

Lemma simple_type_means_cast_same : forall t s, simple_type t -> cast_type_bound s t t.
Proof.
  induction t;intros; simpl; try constructor.
  inv H. apply IHt. easy.
  inv H. easy. inv H. easy. apply IHt. inv H. easy.
  inv H. easy. inv H. easy. apply IHt. inv H. easy.
Qed. 

Lemma simple_type_means_eval_same : forall t s, simple_type t -> eval_type_bound s t = Some t.
Proof.
  induction t;intros; simpl; try constructor.
  destruct t; try easy.
  inv H. inv H1.
  unfold eval_bound. easy.
  inv H. inv H1.
  unfold eval_bound. easy.
Qed. 

Lemma cast_type_eq : forall s t t1 t', 
        cast_type_bound s t t' -> type_eq s t t1 -> cast_type_bound s t1 t'.
Proof.
 intros. inv H0. easy.
 assert (t' = t1).
 eapply cast_type_bound_same. apply H. easy. subst.
 apply simple_type_means_cast_same. easy.
 assert (t1 = t').
 specialize (simple_type_means_cast_same t1 s H1) as eq1.
 eapply cast_type_bound_same. apply H2. easy. subst.
 apply simple_type_means_cast_same. easy.
Qed.

Lemma sub_domain_grow : forall env S x v t, sub_domain env S 
                 -> sub_domain (Env.add x t env) (Stack.add x v S).
Proof.
  intros.
  unfold sub_domain in *.
  intros.
  unfold Env.In,Env.Raw.PX.In in H0.
  destruct H0.
  unfold Stack.In,Stack.Raw.PX.In.
  destruct (Nat.eq_dec x x0).
  subst.
  exists v.
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

(* Some lemmas related to cast/well_bound_in *)
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
 apply EnvFacts.empty_mapsto_iff in H. inv H.
Qed.



Lemma well_typed_means_simple : forall (w : type),
          well_type_bound_in empty_env w -> simple_type w.
Proof.
 intros. remember empty_env as env0.
 induction H.
 apply SPTNat.
 apply SPTPtr.
 apply IHwell_type_bound_in.
 subst. easy.
 constructor.
 subst. inv H0.
 apply well_bound_means_no_var in H; try easy.
 destruct H. subst.
 constructor. apply IHwell_type_bound_in. easy. easy.
 subst. inv H0.
 apply well_bound_means_no_var in H; try easy.
 destruct H. subst.
 constructor. apply IHwell_type_bound_in. easy. easy.
Qed.


Lemma empty_env_means_cast_bound_same :
   forall s b, well_bound_in empty_env b  -> cast_bound s b = Some b.
Proof.
  intros. unfold cast_bound. inv H.
  easy. apply EnvFacts.empty_mapsto_iff in H0. inv H0.
Qed.


Lemma empty_env_means_cast_type_bound_same :
   forall s t, well_type_bound_in empty_env t -> cast_type_bound s t t.
Proof.
 intros. 
 remember empty_env as env.
 induction H. constructor.
 constructor. apply IHwell_type_bound_in. easy.
 constructor.
 constructor. subst.
 apply empty_env_means_cast_bound_same. easy.
 subst.
 apply empty_env_means_cast_bound_same. easy.
 apply IHwell_type_bound_in; easy.
 constructor. subst.
 apply empty_env_means_cast_bound_same. easy.
 subst.
 apply empty_env_means_cast_bound_same. easy.
 apply IHwell_type_bound_in; easy.
Qed.

(*
Lemma lit_empty_means_cast_type_bound_same :
  forall D F Q S H m n t t1, @well_typed D F S H empty_env Q m (ELit n t) t1 ->  cast_type_bound S t t.
Proof.
 intros. remember empty_env as env.
 inv H0.
 apply simple_type_means_cast_same.
 easy.
Qed.
*)

Lemma lit_nat_type : forall D F H Q S env m n t, 
       @well_typed D F S H env Q m (ELit n t) TNat -> t = TNat.
Proof.
 intros. remember (ELit n t) as e. remember TNat as t1.
 induction H0; subst; inv Heqe.
 reflexivity.
Qed.


(* Progress proof for args. *)
Lemma well_typed_args_same_length : forall D Q H env s es tvl,
    @well_typed_args D Q H env s es tvl -> length es = length tvl.
Proof.
  intros. induction H0. easy.
  simpl. rewrite IHwell_typed_args. easy.
Qed.

Definition bound_in_stack (S: stack) (b:bound) :=
       match b with Num n => True
                | Var x n => Stack.In x S
       end.

Inductive stack_bound_in : stack -> type -> Prop :=
   | stack_bound_in_nat : forall env, stack_bound_in env TNat
   | stack_bound_in_ptr : forall m t env, stack_bound_in env t -> stack_bound_in env (TPtr m t)
   | stack_bound_in_struct : forall env T, stack_bound_in env (TStruct T)
   | stack_bound_in_array : forall env l h t, bound_in_stack env l -> bound_in_stack env h -> 
                                      stack_bound_in env t -> stack_bound_in env (TArray l h t)
   | stack_bound_in_ntarray : forall env l h t, bound_in_stack env l -> bound_in_stack env h -> 
                                      stack_bound_in env t -> stack_bound_in env (TNTArray l h t).

Fixpoint bounds_in_stack (S:stack) (l : list (var * bound)) :=
   match l with [] => True
            | (x,v)::xl => (bound_in_stack S v /\ bounds_in_stack S xl)
   end.

Lemma stack_in_cast_bound : forall s t, bound_in_stack s t
              -> (exists t', cast_bound s t = Some t').
Proof.
  intros. unfold bound_in_stack in H.
  destruct t. exists (Num z). easy.
  unfold Stack.In,Stack.Raw.PX.In in H.
  destruct H. destruct x.
  exists (Num (z+z0)).
  unfold cast_bound.
  apply Stack.find_1 in H. rewrite H. easy.
Qed.

Lemma stack_in_cast_type : forall s t, stack_bound_in s t
              -> (exists t', cast_type_bound s t t').
Proof.
  intros. induction H.
  exists TNat. constructor.
  destruct IHstack_bound_in.
  exists (TPtr m x). constructor. easy.
  exists (TStruct T). constructor.
  destruct IHstack_bound_in.
  apply stack_in_cast_bound in H0.
  apply stack_in_cast_bound in H.
  destruct H. destruct H0.
  exists (TArray x0 x1 x).
  constructor. 1-3: easy.
  destruct IHstack_bound_in.
  apply stack_in_cast_bound in H0.
  apply stack_in_cast_bound in H.
  destruct H. destruct H0.
  exists (TNTArray x0 x1 x).
  constructor. 1-3: easy.
Qed.

Lemma well_bound_stack_bound_in : forall env S t,
  well_bound_in env t -> sub_domain env S -> bound_in_stack S t.
Proof.
  intros. induction H.
  constructor.
  unfold bound_in_stack.
  unfold sub_domain in H0.
  unfold Env.In,Env.Raw.PX.In in H0.
  specialize (H0 x).
  apply H0. exists TNat. easy.
Qed.

Lemma well_type_stack_bound_in : forall env S t,
  well_type_bound_in env t -> sub_domain env S -> stack_bound_in S t.
Proof.
  intros. induction H.
  constructor. constructor. apply IHwell_type_bound_in. easy.
  constructor. constructor.
  apply (well_bound_stack_bound_in env0); try easy.
  apply (well_bound_stack_bound_in env0); try easy.
  apply IHwell_type_bound_in. easy.
  constructor.
  apply (well_bound_stack_bound_in env0); try easy.
  apply (well_bound_stack_bound_in env0); try easy.
  apply IHwell_type_bound_in. easy.
Qed.

Lemma stack_bound_in_bounds : forall AS S b, bounds_in_stack S AS ->
    bound_in_stack S b -> bound_in_stack S (subst_bounds b AS).
Proof.
  induction AS; intros; simpl. easy.
  destruct a.
  apply IHAS. simpl in H. destruct H. easy.
  simpl in H. destruct H.
  unfold subst_bound. destruct b. easy.
  destruct (var_eq_dec v0 v).
  destruct b0. constructor.
  unfold bound_in_stack.
  inv H. unfold Stack.In,Stack.Raw.PX.In.
  exists x. easy.
  easy.
Qed.

Lemma stack_bound_in_subst_type : forall S AS t, bounds_in_stack S AS -> 
         stack_bound_in S t -> stack_bound_in S (subst_type AS t).
Proof.
  intros. induction H0; simpl.
  constructor. constructor. apply IHstack_bound_in. easy. constructor.
  constructor.
  apply stack_bound_in_bounds; try easy.
  apply stack_bound_in_bounds; try easy.
  apply IHstack_bound_in. easy.
  constructor.
  apply stack_bound_in_bounds; try easy.
  apply stack_bound_in_bounds; try easy.
  apply IHstack_bound_in. easy.
Qed.

Lemma eval_arg_exists : forall S env e t,
         well_type_bound_in env t -> sub_domain env S ->
         ((exists n t, e = ELit n t) \/ (exists y, e = EVar y /\ Env.In y env))
          -> (exists n' t', eval_arg S e t (ELit n' t')).
Proof.
 intros. destruct H1. destruct H1. destruct H1. subst.
 assert (exists t', cast_type_bound S t t').
 apply stack_in_cast_type.
 apply (well_type_stack_bound_in env0); try easy.
 destruct H1.
 exists x. exists x1. constructor. easy.
 destruct H1. destruct H1. subst.
 assert (exists t', cast_type_bound S t t').
 apply stack_in_cast_type.
 apply (well_type_stack_bound_in env0); try easy.
 destruct H1.
 unfold sub_domain in H0. apply H0 in H2.
 destruct H2. destruct x1.
 exists z. exists x0.
 apply eval_var with (t' := t0).
 easy. easy. 
Qed.

Lemma typed_args_values :
    forall tvl es D Q S H env AS, 
        sub_domain env S ->
        bounds_in_stack S AS ->
        @well_typed_args D Q H env AS es tvl ->
          (exists S', @eval_el AS S tvl es S').
Proof.
  intros. induction H2.
  exists S. constructor. 
  specialize (IHwell_typed_args H0 H1).
  destruct IHwell_typed_args.
  specialize (eval_arg_exists S env0 e (subst_type s t)) as X1.
  inv H2.
  apply simple_type_well_bound with (env := env0) in H5.
  specialize (X1 H5 H0).
  assert ((exists (n0 : Z) (t : type), ELit n t' = ELit n0 t) \/
     (exists y : var,
        ELit n t' = EVar y /\ Env.In (elt:=type) y env0)).
  left. exists n. exists t'. easy.
  apply X1 in H2. destruct H2. destruct H2.
  exists ((Stack.add v (x0,x1) x)).
  apply eval_el_many_2; try easy.
  assert ((exists (n : Z) (t : type), EVar x0 = ELit n t) \/
     (exists y : var,
        EVar x0 = EVar y /\ Env.In (elt:=type) y env0)).
  right.
  exists x0. split. easy. exists t'. easy.
  specialize (X1 H6 H0 H2).
  inv H2. destruct H8. destruct H2. inv H2.
  destruct H8. destruct H2. inv H2.
  destruct X1. destruct H2.
  exists ((Stack.add v (x0,x2) x)).
  apply eval_el_many_2; try easy.
Qed.

Inductive well_arg_env_in : env -> expression -> Prop :=
   | well_arg_env_lit : forall s v t, well_arg_env_in s (ELit v t)
   | well_arg_env_var : forall s x, Env.In x s -> well_arg_env_in s (EVar x).

Inductive well_args_env_in : env -> list expression -> Prop :=
   | well_args_empty : forall s, well_args_env_in s []
   | well_args_many : forall s e es, well_arg_env_in s e -> well_args_env_in s es -> well_args_env_in s (e::es).

Lemma well_type_args_trans : forall D Q H env AS es tvl, @well_typed_args D Q H env AS es tvl -> well_args_env_in env es.
Proof.
  intros. induction H0. constructor.
  constructor.
  inv H0. constructor.
  constructor.
  exists t'. easy. easy.
Qed.

Definition bounds_in_stack_inv (l : list (var * bound)) (S:stack) := forall x y n, In (x,Var y n) l -> Stack.In y S.

Lemma get_dept_map_bounds_in_stack_inv : forall tvl es env S AS, well_args_env_in env es
             -> sub_domain env S -> get_dept_map tvl es = Some AS -> bounds_in_stack_inv AS S.
Proof.
  induction tvl. intros. simpl in *. inv H1. unfold bounds_in_stack. easy.
  intros.
  simpl in *. destruct a. destruct t.
  destruct es. inv H1.
  inv H. inv H5.
  unfold get_good_dept in *.
  destruct (get_dept_map tvl es) eqn:eq1. inv H1.
  specialize (IHtvl es env0 S l H6 H0 eq1).
  unfold bounds_in_stack_inv in *.
  intros. simpl in H. destruct H. inv H. apply IHtvl with (x := x) (y := y) (n:=n). easy.
  inv H1.
  unfold get_good_dept in *.
  destruct (get_dept_map tvl es) eqn:eq1. inv H1.
  specialize (IHtvl es env0 S l H6 H0 eq1).
  unfold bounds_in_stack_inv in *.
  intros. simpl in H1. destruct H1. inv H1.
  unfold sub_domain in H0.
  apply H0. easy.
  apply IHtvl with (x := x0) (y := y) (n:=n). easy.
  inv H1.
  destruct es. inv H1.
  inv H.
  apply IHtvl with (es := es) (env:=env0); try easy.
  destruct es. inv H1.
  inv H.
  apply IHtvl with (es := es) (env:=env0); try easy.
  destruct es. inv H1.
  inv H.
  apply IHtvl with (es := es) (env:=env0); try easy.
  destruct es. inv H1.
  inv H.
  apply IHtvl with (es := es) (env:=env0); try easy.
Qed.

Lemma bound_in_stack_correct : forall S AS, bounds_in_stack_inv AS S -> bounds_in_stack S AS.
Proof.
  intros. induction AS. simpl in *. easy.
  simpl in *. destruct a eqn:eq1.
  split.
  unfold bounds_in_stack_inv in H.
  destruct b. unfold bound_in_stack. easy.
  unfold bound_in_stack. apply H with (x := v) (n := z).
  simpl. left. easy.
  apply IHAS.
  unfold bounds_in_stack_inv in *.
  intros.
  apply H with (x := x) (n:=n). simpl. right. easy.
Qed.

Lemma get_dept_map_bounds_in_stack : forall tvl es env S AS, well_args_env_in env es
             -> sub_domain env S -> get_dept_map tvl es = Some AS -> bounds_in_stack S AS.
Proof.
  intros.
  apply bound_in_stack_correct.
  apply get_dept_map_bounds_in_stack_inv with (tvl := tvl) (env := env0) (es := es); try easy.
Qed.

(*
Definition sub_stack_nat (arg_env: arg_stack) (S:stack) (arg_s:stack) :=
       (forall x v, (Stack.MapsTo x (NumVal v) arg_env -> Stack.MapsTo x (v,TNat) arg_s)) /\
       (forall x v t v', (Stack.MapsTo x (VarVal v) arg_env -> Stack.MapsTo v (v',t) S -> Stack.MapsTo x (v',TNat) arg_s)).

Lemma subtype_stack_nat : forall D S t, subtype_stack D S TNat t -> t = TNat.
Proof.
  intros. inv H. inv H0. easy. inv H2. inv H1. easy. inv H1. inv H2. easy.
Qed.

Definition sub_list_arg_s (l : list var) (arg_s:stack) := forall x, In x l -> Stack.In x arg_s.

Lemma well_bound_vars_cast : forall b l s, sub_list_arg_s l s -> no_ebound b
          -> well_bound_vars l b -> (exists b', cast_bound s b = Some (Num b')).
Proof.
 intros. induction b; simpl.
 exists z. easy.
 destruct (Stack.find (elt:=Z * type) v s) eqn:eq1.
 destruct p.
 exists ((z + z0)). easy.
 unfold sub_list_arg_s in *.
 inv H1. apply H in H4.
 unfold Stack.In,Stack.Raw.PX.In in *.
 destruct H4. apply Stack.find_1 in H1.
 rewrite H1 in eq1. inv eq1.
 inv H0.
Qed.

Lemma well_type_bound_vars_cast : forall t l s, sub_list_arg_s l s -> well_bound_vars_type l t ->
               no_etype t -> (exists t', cast_type_bound s t t' /\ simple_type t').
Proof.
  induction t; intros; simpl.
  exists TNat. split. constructor. constructor.
  inv H0. apply IHt with (s := s) in H4. destruct H4.
  exists (TPtr m x). split.  constructor. easy. constructor. easy. easy. inv H1. easy.
  exists (TStruct s). constructor. constructor. constructor.
  inv H0. inv H1.
  apply IHt with (s := s) in H8; try easy. destruct H8.
  apply well_bound_vars_cast with (s := s) in H6; try easy.
  apply well_bound_vars_cast with (s := s) in H7; try easy.
  destruct H6. destruct H7.
  exists (TArray (Num x0) (Num x1) x). split. constructor. easy. easy. easy.
  constructor. easy.
  inv H0. inv H1.
  apply IHt with (s := s) in H8; try easy. destruct H8.
  apply well_bound_vars_cast with (s := s) in H6; try easy.
  apply well_bound_vars_cast with (s := s) in H7; try easy.
  destruct H6. destruct H7.
  exists (TNTArray (Num x0) (Num x1) x). split. constructor. easy. easy. easy.
  constructor. easy.
  inv H1.
Qed.





Lemma subtype_no_etype : forall t D t', subtype D t t' -> no_etype t -> no_etype t'.
Proof.
  intros. induction H; try easy.
  inv H0. constructor. constructor. easy.
  inv H1. constructor. inv H2. constructor.
  inv H0. inv H4. constructor. easy.
  inv H0. inv H4. constructor. easy.
  inv H0. constructor. inv H3. constructor. easy.
  inv H. constructor. constructor.
  inv H1. constructor. constructor.
  inv H0. constructor. inv H3. constructor. easy.
  inv H. constructor. constructor.
  inv H1. constructor. constructor.
  inv H0. constructor. inv H3. constructor. easy.
  inv H. constructor. constructor.
  inv H1. constructor. constructor.
  constructor. constructor.
  constructor. constructor. constructor.
  inv H2. constructor. inv H3. constructor.
Qed.

Lemma cast_bound_no_ebound : forall s b b', cast_bound s b = Some b' -> no_ebound b' -> no_ebound b.
Proof.
  intros. induction b; simpl. easy. easy.
  inv H. inv H0.
Qed.

Lemma cast_type_no_etype : forall s t t', cast_type_bound s t t' -> no_etype t' -> no_etype t.
Proof.
  intros. induction H;simpl. easy.
  inv H0. constructor. apply IHcast_type_bound. easy.
  inv H0. constructor. apply IHcast_type_bound. easy.
  apply cast_bound_no_ebound with (s := s) (b' := l'); try easy.
  apply cast_bound_no_ebound with (s := s) (b' := h'); try easy.
  inv H0. constructor. apply IHcast_type_bound. easy.
  apply cast_bound_no_ebound with (s := s) (b' := l'); try easy.
  apply cast_bound_no_ebound with (s := s) (b' := h'); try easy.
  easy. inv H0.
Qed.

Lemma subtype_no_etype_r : forall t D t', subtype D t t' -> no_etype t' -> no_etype t.
Proof.
  intros. induction H; try easy.
  inv H0. inv H4. constructor. easy.
  inv H1. constructor. inv H2. constructor. inv H0. easy.
  constructor. constructor.
  inv H0. constructor. constructor. easy.
  inv H1. constructor. inv H2. constructor.
  inv H0. inv H3. constructor. constructor. easy.
  inv H. constructor. constructor. inv H1. constructor. constructor.
  inv H0. inv H3. constructor. constructor. easy.
  inv H. constructor. constructor. inv H1. constructor. constructor.
  inv H0. inv H3. constructor. constructor. easy.
  inv H. constructor. constructor. inv H1. constructor. constructor.
  constructor. constructor.
  constructor. constructor.
Qed.

Lemma cast_bound_no_ebound_r : forall s b b', cast_bound s b = Some b' -> no_ebound b -> no_ebound b'.
Proof.
  intros. induction b; simpl. inv H. constructor. inv H. 
  destruct (Stack.find (elt:=Z * type) v s) eqn:eq1. destruct p. inv H2. constructor. inv H2.
  inv H0.
Qed.

Lemma cast_type_no_etype_r : forall s t t', cast_type_bound s t t' -> no_etype t -> no_etype t'.
Proof.
  intros. induction H;simpl. easy.
  inv H0. constructor. apply IHcast_type_bound. easy.
  inv H0. constructor. apply IHcast_type_bound. easy.
  apply cast_bound_no_ebound_r with (s := s) (b := l); try easy.
  apply cast_bound_no_ebound_r with (s := s) (b := h); try easy.
  inv H0. constructor. apply IHcast_type_bound. easy.
  apply cast_bound_no_ebound_r with (s := s) (b := l); try easy.
  apply cast_bound_no_ebound_r with (s := s) (b := h); try easy.
  easy. inv H0.
Qed.

Lemma subtype_stack_no_etype : forall t D s t', subtype_stack D s t t' -> no_etype t -> no_etype t'.
Proof.
  intros. inv H.
  apply subtype_no_etype with (t := t) (D:=D). easy. easy.
  specialize (subtype_no_etype t D t2' H3 H0) as eq1.
  apply cast_type_no_etype with (s := s) (t' := t2'); try easy.
  specialize (cast_type_no_etype_r s t t1' H2 H0) as eq1. 
  specialize (subtype_no_etype t1' D t' H3 eq1) as eq2.
  easy.
Qed.

Definition bound_env (e:env) := forall x t, Env.MapsTo x t e -> ext_type_in [] t.

Lemma no_ebound_ext_bound : forall b, no_ebound b -> ext_bound_in [] b.
Proof.
  intros. induction b. constructor. constructor. inv H.
Qed.

Lemma no_ebound_ext_bound_anti : forall b, ext_bound_in [] b -> no_ebound b.
Proof.
  intros. induction b. constructor. constructor. inv H. simpl in H2. inv H2.
Qed.

Lemma no_etype_ext_type : forall t, no_etype t -> ext_type_in [] t.
Proof.
  intros. induction H; try constructor. easy.
  apply no_ebound_ext_bound. easy.
  apply no_ebound_ext_bound. easy.
  easy.
  apply no_ebound_ext_bound. easy.
  apply no_ebound_ext_bound. easy.
  easy.
Qed.

Lemma gen_env_ext_type : forall tvl D env env', gen_env env tvl env' ->
        (forall x t', In (x,t') tvl -> word_type t' /\ type_wf D t' /\ no_etype t') -> bound_env env -> bound_env env'.
Proof.
  induction tvl; intros; simpl.
  inv H. easy.
  unfold bound_env in *. intros.
  inv H.
  assert ((forall (x : var) (t' : type),
         In (x, t') tvl ->
         word_type t' /\ type_wf D t' /\ no_etype t')).
  intros.
  specialize (H0 x1 t').
  assert (In (x1, t') ((x0, t0) :: tvl)).
  simpl. right. easy. apply H0 in H3. easy.
  specialize (IHtvl D env0 env'0 H7 H H1).
  destruct (Nat.eq_dec x x0). subst.
  apply Env.mapsto_add1 in H2. subst.
  apply no_etype_ext_type.
  specialize (H0 x0 t0).
  assert (In (x0, t0) ((x0, t0) :: tvl)). simpl. left. easy.
  apply H0 in H2. easy.
  apply Env.add_3 in H2. apply IHtvl with (x := x). easy. lia.
Qed.

Lemma vars_to_ext_bound : forall t t' l, (forall x, In x (get_tvars t) -> In x l)
              -> vars_to_ext l t t' -> ext_type_in [] t'.
Proof.
  induction t; intros; simpl.
  inv H0. constructor.
  inv H2. inv H1. constructor. constructor.
  inv H3.
Admitted.

Lemma to_ext_ext_type : forall t x t', to_ext_type x t t' -> ext_type_in [] t -> ext_type_in [x] t'.
Proof.
  induction t; intros;simpl. inv H. constructor.
  inv H. inv H0. constructor. apply IHt. easy. easy.
  inv H. constructor.
  inv H.
Admitted.

Lemma simple_type_ext_type : forall t, simple_type t -> ext_type_in [] t.
Proof.
  intros. induction H. constructor. constructor. apply IHsimple_type.
  constructor. constructor. constructor. constructor. easy.
  constructor.  constructor.  constructor. easy.
Qed.

Lemma ext_type_well_bound : forall e D F st env m t, expr_wf D F e -> fun_wf D F -> structdef_wf D ->
          bound_env env -> @well_typed D F st env m e t -> ext_type_in [] t.
Proof.
  intros. induction H3; simpl.
  inv H. apply no_etype_ext_type. easy.
  inv H. unfold bound_env in H2. apply H2 with (x := x). easy.
  apply vars_to_ext_bound with (t := t) (l := get_tvars t).
  intros. easy. easy. constructor.
  constructor.
  apply to_ext_ext_type with (t := t). easy.
  apply IHwell_typed2. inv H. easy.
  unfold bound_env in *. intros.
  destruct (Nat.eq_dec x0 x). subst.
  apply Env.mapsto_add1 in H5. subst. constructor.
  apply Env.add_3 in H5. apply H2 with (x := x0). easy. lia.
  inv H.
  apply IHwell_typed2. easy.
  unfold bound_env in *. intros.
  destruct (Nat.eq_dec x0 x). subst.
  apply Env.mapsto_add1 in H. subst. apply IHwell_typed1. easy. easy.
  apply Env.add_3 in H. apply H2 with (x := x0). easy. lia.
  inv H.
  apply IHwell_typed; try easy.
  constructor.
  unfold structdef_wf in H1.
  specialize (H1 T fs). apply H1 in H4. unfold fields_wf in H4.
  apply H4 in H5. destruct H5 as [X1 [X2 X3]].
  constructor.
  apply simple_type_ext_type. easy. inv H.
  constructor. apply no_etype_ext_type. easy.
  apply IHwell_typed.  inv H. easy. easy.
  inv H. apply no_etype_ext_type. easy.
  inv H. apply no_etype_ext_type. easy.
  inv H. apply no_etype_ext_type. easy.
  inv H. apply no_etype_ext_type. inv H11. inv H7. constructor. constructor. easy.
  constructor. constructor.
  inv H. apply no_etype_ext_type. inv H10. inv H6. constructor. constructor. easy.
  easy. easy.
  inv H.
  apply IHwell_typed in H8.
Admitted.


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


*)

Lemma replicate_gt_eq : forall x t, 0 < x -> Z.of_nat (length (Zreplicate (x) t)) = x.
Proof.
  intros.
  unfold Zreplicate.
  destruct x eqn:eq1. lia.
  simpl. 
  rewrite replicate_length. lia.
  lia.
Qed.

Lemma gen_rets_exist: forall tvl (S S':stack) AS es e, length es = length tvl ->
         eval_el AS S tvl es S' -> (exists e', gen_rets AS S tvl es e e').
Proof.
  induction tvl. intros.
  simpl in *.
  destruct es. exists e.
  constructor. simpl in *. inv H.
  intros.
  destruct es. inv H. inv H0.
  assert (length es = length tvl). inv H. easy.
  apply IHtvl with (AS:= AS) (S := S) (S' := s') (e := e) in H0; try easy.
  destruct H0. 
  exists (ERet x (n,t') (Stack.find x S) x0).
  constructor. easy. easy.
Qed.

Lemma subtype_well_type : forall D Q H env t t' n,
simple_type t' -> type_wf D t' ->
@well_typed_lit D Q H env n t ->
subtype D Q t t' ->
@well_typed_lit D Q H env n t'.
Proof.
  intros. induction H2. 
  - inv H3. eauto.
  - assert (exists t, t' = (TPtr Unchecked t)) by (inv H3; eauto).
    destruct H2. rewrite H2. eauto.
  - eauto.
  - specialize (subtype_trans D Q t t' Checked w) as eq1.

    assert (exists t0, t' = (TPtr Checked t0)) by (inv H3; eauto).
    destruct H5. rewrite H5 in *.
    eapply TyLitRec; eauto.
  - assert (exists t0, t' = (TPtr Checked t0)) by (inv H3; eauto).
    destruct H7. subst.
    assert (subtype D Q (TPtr Checked w) (TPtr Checked x)).
    apply subtype_trans with (m := Checked) (w := t); try easy.
    eapply TyLitC;eauto.
Qed.


(* The Type Progress Theorem *)
Lemma progress : forall D s H m e t,
    structdef_wf D ->
    heap_wf D H ->
    heap_wt D empty_theta H e -> 
    expr_wf D fenv e ->
    fun_wf D fenv s H ->
    @well_typed D fenv s H empty_env empty_theta m e t ->
    value D e \/
    reduces D (fenv empty_env) s H e \/
    unchecked m e.
Proof with eauto 20 with Progress.
  intros D st H m e t HDwf HHwf HHwt Hewf Hfun Hwt.
  remember empty_env as env.
  induction Hwt as [
                     env Q m n t HTyLit                                         | (* Literals *)
                     env Q m x t Wb                                             | (* Variables *)
                     env Q AS m m' es x tvl e t HMap HGen HMode HArg            | (* Call *)
                     env Q m x h l t Wb                                         | (* Strlen *)
                     env Q m x y e l h t Alpha Wb HTy IH Hx                     | (* LetStrlen *)
                     env Q m x e1 e2 t b Alpha HTy1 IH1 HTy2 IH2 Hx Hdept       | (* Let-Nat-Expr *)
                     env Q m x e1 t1 e2 t Alpha HTy1 IH1 HTy2 IH2 Hx            | (* Let-Expr *)
                     env Q m x na a e t HIn Hx HTy1 IH1                         | (* RetNat *)
                     env Q m x na ta a e t HIn HTy1 IH1 Hx                      | (* Ret *)
                     env Q m e1 e2 HTy1 IH1 HTy2 IH2                            | (* Addition *)
                     env Q m e m' T fs i fi ti HTy IH HWf1 HWf2                 | (* Field Addr *)
                     env Q m w Wb                                               | (* Malloc *)
                     env Q m e t HTy IH                                         | (* Unchecked *)
                     env Q m t e t' Wb HChkPtr HTy IH                           | (* Cast - nat *)
                     env Q m t e t' Wb HTy IH HSub                              | (* Cast - subtype *)
                     env Q m e x y u v t t' Wb HTy IH Teq                       | (* DynCast - ptr array *)
                     env Q m e x y t t' HNot Teq Wb HTy IH                      | (* DynCast - ptr array from ptr *)
                     env Q m e x y u v t t' Wb Teq HTy IH                       | (* DynCast - ptr nt-array *)
                     env Q m e m' t l h t' t'' HTy IH HSub HPtrType HMode       | (* Deref *)
                     env Q m e1 m' l h e2 t WT Twf HTy1 IH1 HTy2 IH2 HMode                      | (* Index for array pointers *)
                     env Q m e1 m' l h e2 t WT Twf HTy1 IH1 HTy2 IH2 HMode                      | (* Index for ntarray pointers *)
                     env Q m e1 e2 m' t t1 HSub WT HTy1 IH1 HTy2 IH2 HMode                      | (* Assign normal *)
                     env Q m e1 e2 m' l h t t' WT Twf HSub HTy1 IH1 HTy2 IH2 HMode              | (* Assign array *)
                     env Q m e1 e2 m' l h t t' WT Twf HSub HTy1 IH1 HTy2 IH2 HMode              | (* Assign nt-array *)

                     env Q m e1 e2 e3 m' l h t t' WT Twf TSub HTy1 IH1 HTy2 IH2 HTy3 IH3 HMode      |  (* IndAssign for array pointers *)
                     env Q m e1 e2 e3 m' l h t t' WT Twf TSub HTy1 IH1 HTy2 IH2 HTy3 IH3 HMode      |  (* IndAssign for ntarray pointers *)
                     env Q m m' x t t1 e1 e2 t2 t3 t4 HEnv TSub HPtr HTy1 IH1 HTy2 IH2 HJoin HMode  | (* If *)
                     env Q m m' x l t e1 e2 t2 t3 t4 HEnv HTy1 IH1 HTy2 IH2 HJoin HMode (* IfNT *)
                   ]; clean.
  (* Case: TyLit *)
  - (* Holds trivially, since literals are values *)
    left...
    inv Hewf. apply VLit. 1-3:assumption.
  (* Case: TyVar *)
  - (* Impossible, since environment is empty *)
    inversion Wb.
  - (* Call Case *)
    right. left. inv Hewf.
    specialize (well_typed_args_same_length D Q H empty_env AS es tvl HArg) as X1.
    assert (sub_domain empty_env st).
    unfold sub_domain. intros.
    unfold Env.In, Env.Raw.PX.In in *.
    destruct H0.
    apply EnvFacts.empty_mapsto_iff in H0. inv H0.
    specialize (typed_args_values tvl es D Q st H empty_env AS H0) as X3.
    assert (bounds_in_stack st AS).
    apply get_dept_map_bounds_in_stack with (tvl := tvl) (es := es) (env := empty_env); try easy.
    apply (well_type_args_trans D Q H empty_env AS es tvl); try easy.
    specialize (X3 H1 HArg). destruct X3.
    specialize (gen_rets_exist tvl st x0 AS es e X1 H4) as X2.
    destruct X2.
    eapply step_implies_reduces.
    Check SCall.
    apply (SCall D (fenv empty_env) AS st x0 H x es t tvl e x1 m'); try easy.
  -   (* Case: TyStrlen *)
    apply EnvFacts.empty_mapsto_iff in Wb. inv Wb.
  -   (* Case: TyLetStrlen *)
    apply EnvFacts.empty_mapsto_iff in Wb. inv Wb.
  (* Case: TyLetNat *)
  - (* `ELet x e1 e2` is not a value *)
    right.
    (* Invoke the IH on `e1` *)
    inv Hewf. inv HHwt.
    rename H3 into Y1.
    rename H4 into Y2.
    apply (IH1 Y1) in H2.
    2: { easy. }
    destruct H2 as [ HVal1 | [ HRed1 | HUnchk1 ] ].
    (* Case: `e1` is a value *)
    + (* We can take a step according to SLet *)
      left.  
      inv HVal1...
      apply (step_implies_reduces D (fenv empty_env) H st 
              (ELet x (ELit n t0) e2) H (Stack.add x (n, t0) st) (RExpr(ERet x (n,t0) (Stack.find x st) e2))).
      apply SLet.
      apply simple_type_means_cast_same. easy.
    (* Case: `e1` reduces *)
    + (* We can take a step by reducing `e1` *)
      left.
      ctx (ELet x e1 e2) (in_hole e1 (CLet x CHole e2))...
    (* Case: `e1` is unchecked *)
    + (* `ELet x e1 e2` must be unchecked, since `e1` is *)
      right.
      ctx (ELet x e1 e2) (in_hole e1 (CLet x CHole e2)).
      destruct HUnchk1...
  (* Case: TyLet *)
  - (* `ELet x e1 e2` is not a value *)
    right.
    (* Invoke the IH on `e1` *)
    inv Hewf.
    inv HHwt.
    rename H3 into Y1.
    rename H4 into Y2.
    apply (IH1 Y1) in H2.
    2: { easy. }
    destruct H2 as [ HVal1 | [ HRed1 | HUnchk1 ] ].
    (* Case: `e1` is a value *)
    + (* We can take a step according to SLet *)
      left.  
      inv HVal1...
      apply (step_implies_reduces D (fenv empty_env) H st 
              (ELet x (ELit n t0) e2) H (Stack.add x (n, t0) st) (RExpr(ERet x (n,t0) (Stack.find x st) e2))).
      apply SLet.
      apply simple_type_means_cast_same.
      easy.
    (* Case: `e1` reduces *)
    + (* We can take a step by reducing `e1` *)
      left.
      ctx (ELet x e1 e2) (in_hole e1 (CLet x CHole e2))...
    (* Case: `e1` is unchecked *)
    + (* `ELet x e1 e2` must be unchecked, since `e1` is *)
      right.
      ctx (ELet x e1 e2) (in_hole e1 (CLet x CHole e2)).
      destruct HUnchk1...
  (* Case: TyRet *)
  - (* `ELet x e1 e2` is not a value *)
    unfold Env.In,Env.Raw.PX.In in HIn.
    destruct HIn.
    apply EnvFacts.empty_mapsto_iff in H0. inv H0.
  - (* `ELet x e1 e2` is not a value *)
    unfold Env.In,Env.Raw.PX.In in HIn.
    destruct HIn.
    apply EnvFacts.empty_mapsto_iff in H0. inv H0.
  (* Case: TyPlus *)
  - (* `EPlus e1 e2` isn't a value *)
    right.
    inv Hewf. inv HHwt.
    rename H4 into Y1.
    rename H5 into Y2.
    apply (IH1 Y1) in H2. 2:{ easy. }
    (* Invoke the IH on `e1` *)
    destruct H2 as [ HVal1 | [ HRed1 | HUnchk1 ] ].
    (* Case: `e1` is a value *)
    + (* We don't know if we can take a step yet, since `e2` might be unchecked. *)
      inv HVal1 as [ n1 t1 ].
      (* Invoke the IH on `e2` *)
      apply (IH2 Y2) in H3. 2:{ easy. }
      destruct H3 as [ HVal2 | [ HRed2 | HUnchk2 ] ].
      (* Case: `e2` is a value *)
      * (* We can step according to SPlus *)
        left.
        inv HVal2 as [ n2 t2 ]...
        eapply (step_implies_reduces D (fenv empty_env) H st (EPlus (ELit n1 t1) (ELit n2 t2)) H st (RExpr (ELit (n1 + n2) t1))).
        apply lit_nat_type in HTy2. subst.
        apply (@SPlus D (fenv empty_env) st H t1 n1 n2).
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
    inv Hewf. inv HHwt.
    rename H3 into Y1. apply (IH Y1) in H2. 2: { easy. }
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
       apply (step_implies_reduces D (fenv empty_env) H st (EMalloc TNat) H' st (RExpr (ELit n (TPtr Checked TNat)))).
       apply SMalloc. constructor.
       easy. easy.
   * assert ((forall (l h : Z) (t : type),
       (TPtr m0 w) = TArray (Num l) (Num h) t -> l = 0 /\ h > 0)).
      intros. inv H0.
      assert (((forall (l h : Z) (t : type),
       (TPtr m0 w) = TNTArray (Num l) (Num h) t -> l = 0 /\ h > 0))).
      intros. inv H2.
       destruct ((wf_implies_allocate D (TPtr m0 w) H H0 H2 eq1 H1)) as [ n [ H' HAlloc]].
       apply (step_implies_reduces D (fenv empty_env) H st (EMalloc (TPtr m0 w)) H' st (RExpr (ELit n (TPtr Checked (TPtr m0 w))))).
       apply SMalloc.
       apply simple_type_means_cast_same. easy.
       unfold malloc_bound. easy.
       easy.
   * assert ((forall (l h : Z) (t : type),
       (TStruct s) = TArray (Num l) (Num h) t -> l = 0 /\ h > 0)).
      intros. inv H0.
      assert (((forall (l h : Z) (t : type),
       (TStruct s) = TNTArray (Num l) (Num h) t -> l = 0 /\ h > 0))).
      intros. inv H2.
       destruct ((wf_implies_allocate D (TStruct s) H H0 H2 eq1 H1)) as [ n [ H' HAlloc]].
       apply (step_implies_reduces D (fenv empty_env) H st (EMalloc (TStruct s)) H' st (RExpr (ELit n (TPtr Checked (TStruct s))))).
       apply SMalloc.
       apply (simple_type_means_cast_same). easy. easy.
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
       apply SPTArray. easy.
       destruct ((wf_implies_allocate D (TArray (Num l) (Num h) w) H H0 H3 H4 H1)) as [ n [ H' HAlloc]].
       apply (step_implies_reduces D (fenv empty_env) H st (EMalloc (TArray (Num l) (Num h) w))
                             H' st (RExpr (ELit n (TPtr Checked (TArray (Num l) (Num h) w))))).
       apply SMalloc.
       apply cast_type_bound_array.
       unfold cast_bound. reflexivity.
       unfold cast_bound. reflexivity.
       apply simple_type_means_cast_same. assumption.
       unfold malloc_bound. split. easy. lia. easy.
       assert (h <= 0).
       specialize (Z.ltb_lt 0 h) as eq3.
       apply not_iff_compat in eq3.
       assert((0 <? h) <> true).
       apply not_true_iff_false. assumption.
       apply eq3 in H0. lia.
       apply (step_implies_reduces D (fenv empty_env) H st (EMalloc (TArray (Num l) (Num h) w)) H st RBounds).
       apply (SMallocHighOOB D (fenv empty_env) st H (TArray (Num l) (Num h) w) (TArray (Num l) (Num h) w) h).
       assumption.
       apply simple_type_means_eval_same. constructor. easy.
       easy.
       apply (step_implies_reduces D (fenv empty_env) H st (EMalloc (TArray (Num l) (Num h) w)) H st RBounds).
       apply (SMallocLowOOB D (fenv empty_env) st H (TArray (Num l) (Num h) w) (TArray (Num l) (Num h) w) l).
       assumption.
       apply simple_type_means_eval_same. constructor. easy.
       easy.
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
       apply SPTNTArray. easy.
       destruct ((wf_implies_allocate D (TNTArray (Num l) (Num h) w) H H0 H3 H4 H1)) as [ n [ H' HAlloc]].
       apply (step_implies_reduces D (fenv empty_env) H st (EMalloc (TNTArray (Num l) (Num h) w))
                             H' st (RExpr (ELit n (TPtr Checked (TNTArray (Num l) (Num h) w))))).
       apply SMalloc.
       apply cast_type_bound_ntarray.
       unfold cast_bound. reflexivity.
       unfold cast_bound. reflexivity.
       apply simple_type_means_cast_same. assumption.
       unfold malloc_bound.  split. easy. lia. easy.
       assert (h <= 0).
       specialize (Z.ltb_lt 0 h) as eq3.
       apply not_iff_compat in eq3.
       assert((0 <? h) <> true).
       apply not_true_iff_false. assumption.
       apply eq3 in H0. lia.
       apply (step_implies_reduces D (fenv empty_env) H st (EMalloc (TNTArray (Num l) (Num h) w)) H st RBounds).
       apply (SMallocHighOOB D (fenv empty_env) st H (TNTArray (Num l) (Num h) w) (TNTArray (Num l) (Num h) w) h).
       assumption.
       apply simple_type_means_eval_same. constructor. easy.
       easy.
       apply (step_implies_reduces D (fenv empty_env) H st (EMalloc (TNTArray (Num l) (Num h) w)) H st RBounds).
       apply (SMallocLowOOB D (fenv empty_env) st H (TNTArray (Num l) (Num h) w) (TNTArray (Num l) (Num h) w) l).
       assumption.
       apply simple_type_means_eval_same. constructor. easy.
       easy.
  (* Case: TyUnchecked *)
  - (* `EUnchecked e` isn't a value *)
    right.
    inv Hewf. inv HHwt.
    rename H2 into Y1. apply (IH Y1) in H1.
    2: { easy. }
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
  (* Case: TyCast1 *)
  - (* `ECast t e` isn't a value when t is a nat type or is unchecked mode. *)
    right.
    inv Hewf. inv HHwt. rename H1 into Y1. apply (IH Y1) in H4. 2: { easy. }
    (* Invoke the IH on `e` *)
    destruct H4 as [ HVal | [ HRed | HUnchk ] ].
    (* Case: `e` is a value *)
    + (* We can step according to SCast *)
      destruct m.
      left.
      inv HVal.
      specialize (well_typed_means_simple t Wb) as eq1.
      apply simple_type_means_cast_same with ( s:= st) in eq1.
      apply (step_implies_reduces D (fenv empty_env) H st (ECast t (ELit n t0)) H st (RExpr (ELit n t))).
      apply SCast. easy.
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
  - (* `ECast (TPtr Checked t) e` isn't a value when t is a nat type or is unchecked mode. *)
    right.
    inv Hewf. inv HHwt. rename H1 into Y1. apply (IH Y1) in H4. 2: { easy. }
    (* Invoke the IH on `e` *)
    destruct H4 as [ HVal | [ HRed | HUnchk ] ].
    (* Case: `e` is a value *)
    + (* We can step according to SCast *)
      destruct m.
      left.
      inv HVal.
      apply (step_implies_reduces D (fenv empty_env) H st (ECast (TPtr Checked t) (ELit n t0)) H st (RExpr (ELit n (TPtr Checked t)))).
      apply SCast.
      apply simple_type_means_cast_same. constructor.
      apply well_typed_means_simple; try easy.
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
    inv Hewf.
    inv HHwt. rename H1 into Y1.
    apply (IH Y1) in H4. 2 : { easy. }
    (* Invoke the IH on `e` *)
    destruct H4 as [ HVal | [ HRed | HUnchk ] ].
    (* Case: `e` is a value *)
    + (* We can step according to SCast *)
      left.
      inv HVal.
      inv HTy.
      specialize (well_typed_means_simple (TPtr Checked (TArray x y t)) Wb) as eq2.
      inv eq2. inv H6.
      inv H4. inv H6.
      destruct (Z_le_dec l0 l).
      destruct (Z_lt_dec l h).
      destruct (Z_le_dec h h0).
      apply (step_implies_reduces D (fenv empty_env) H st (EDynCast (TPtr Checked (TArray (Num l) (Num h) t))
           (ELit n (TPtr Checked (TArray (Num l0) (Num h0) t')))) H st (RExpr (ELit n (TPtr Checked (TArray (Num l) (Num h) t))))).
      apply (SCastArray D (fenv empty_env) st H (TPtr Checked (TArray (Num l) (Num h) t)) n (TPtr Checked (TArray (Num l0) (Num h0) t'))
                  l h t l0 h0 t').
      constructor. constructor. easy. easy.
      apply simple_type_means_cast_same with ( s:= st). easy.
      unfold eval_type_bound,eval_bound. reflexivity. easy. easy.  easy.
      apply (step_implies_reduces D (fenv empty_env) H st (EDynCast (TPtr Checked (TArray (Num l) (Num h) t))
            (ELit n (TPtr Checked (TArray (Num l0) (Num h0) t')))) H st RBounds).
      apply (SCastArrayHighOOB1 D (fenv empty_env) st H (TPtr Checked (TArray (Num l) (Num h) t)) n (TPtr Checked (TArray (Num l0) (Num h0) t'))
                  l h t l0 h0 t').
      unfold eval_type_bound,eval_bound. reflexivity.
      unfold eval_type_bound,eval_bound. reflexivity. lia.
      apply (step_implies_reduces D (fenv empty_env) H st (EDynCast (TPtr Checked (TArray (Num l) (Num h) t))
            (ELit n (TPtr Checked (TArray (Num l0) (Num h0) t')))) H st RBounds).
      apply (SCastArrayLowOOB2 D (fenv empty_env) st H (TPtr Checked (TArray (Num l) (Num h) t)) n (TPtr Checked (TArray (Num l0) (Num h0) t'))
                  l h t l0 h0 t').
      unfold eval_type_bound,eval_bound. reflexivity.
      unfold eval_type_bound,eval_bound. reflexivity. lia.
      apply (step_implies_reduces D (fenv empty_env) H st (EDynCast (TPtr Checked (TArray (Num l) (Num h) t))
            (ELit n (TPtr Checked (TArray (Num l0) (Num h0) t')))) H st RBounds).
      apply (SCastArrayLowOOB1 D (fenv empty_env) st H (TPtr Checked (TArray (Num l) (Num h) t)) n (TPtr Checked (TArray (Num l0) (Num h0) t'))
                  l h t l0 h0 t').
      unfold eval_type_bound,eval_bound. reflexivity.
      unfold eval_type_bound,eval_bound. reflexivity. lia.
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
    inv Hewf.
   inv HHwt. rename H1 into Y1.
    apply (IH Y1) in H4. 2 : { easy. }
    (* Invoke the IH on `e` *)
    destruct H4 as [ HVal | [ HRed | HUnchk ] ].
    (* Case: `e` is a value *)
    + (* We can step according to SCast *)
      left.
      inv HVal.
      inv HTy.
      specialize (well_typed_means_simple (TPtr Checked (TArray x y t)) Wb) as eq2.
      inv eq2. inv H6.
      apply (step_implies_reduces D (fenv empty_env) H st (EDynCast (TPtr Checked (TArray (Num l) (Num h) t))
           (ELit n (TPtr Checked t'))) H st (RExpr (ELit n (TPtr Checked (TArray (Num 0) (Num 1) t))))).
      apply (SCastNoArray D (fenv empty_env) st H (Num l) (Num h) t n Checked t'); try easy.
      apply simple_type_means_cast_same with ( s:= st). easy.
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
    inv Hewf. 
    inv HHwt. rename H1 into Y1.
    apply (IH Y1) in H4. 2 : { easy. }
    (* Invoke the IH on `e` *)
    destruct H4 as [ HVal | [ HRed | HUnchk ] ].
    (* Case: `e` is a value *)
    + (* We can step according to SCast *)
      left.
      inv HVal.
      inv HTy.
      specialize (well_typed_means_simple (TPtr Checked (TNTArray x y t)) Wb) as eq2.
      inv eq2. inv H6. inv H4. inv H6.
      destruct (Z_le_dec l0 l).
      destruct (Z_lt_dec l h).
      destruct (Z_le_dec h h0).
      apply (step_implies_reduces D (fenv empty_env) H st (EDynCast (TPtr Checked (TNTArray (Num l) (Num h) t))
           (ELit n (TPtr Checked (TNTArray (Num l0) (Num h0) t')))) H st (RExpr (ELit n (TPtr Checked (TNTArray (Num l) (Num h) t))))).
      apply (SCastNTArray D (fenv empty_env) st H (TPtr Checked (TNTArray (Num l) (Num h) t)) n (TPtr Checked (TNTArray (Num l0) (Num h0) t'))
                  l h t l0 h0 t').
      constructor. constructor. easy. easy.
      apply simple_type_means_cast_same with ( s:= st). easy.
      unfold eval_type_bound,eval_bound. reflexivity. easy. easy.  easy.
      apply (step_implies_reduces D (fenv empty_env) H st (EDynCast (TPtr Checked (TNTArray (Num l) (Num h) t))
            (ELit n (TPtr Checked (TNTArray (Num l0) (Num h0) t')))) H st RBounds).
      apply (SCastNTArrayHighOOB1 D (fenv empty_env) st H (TPtr Checked (TNTArray (Num l) (Num h) t)) n (TPtr Checked (TNTArray (Num l0) (Num h0) t'))
                  l h t l0 h0 t').
      unfold eval_type_bound,eval_bound. reflexivity.
      unfold eval_type_bound,eval_bound. reflexivity. lia.
      apply (step_implies_reduces D (fenv empty_env) H st (EDynCast (TPtr Checked (TNTArray (Num l) (Num h) t))
            (ELit n (TPtr Checked (TNTArray (Num l0) (Num h0) t')))) H st RBounds).
      apply (SCastNTArrayLowOOB2 D (fenv empty_env) st H (TPtr Checked (TNTArray (Num l) (Num h) t)) n (TPtr Checked (TNTArray (Num l0) (Num h0) t'))
                  l h t l0 h0 t').
      unfold eval_type_bound,eval_bound. reflexivity.
      unfold eval_type_bound,eval_bound. reflexivity. lia.
      apply (step_implies_reduces D (fenv empty_env) H st (EDynCast (TPtr Checked (TNTArray (Num l) (Num h) t))
            (ELit n (TPtr Checked (TNTArray (Num l0) (Num h0) t')))) H st RBounds).
      apply (SCastNTArrayLowOOB1 D (fenv empty_env) st H (TPtr Checked (TNTArray (Num l) (Num h) t)) n (TPtr Checked (TNTArray (Num l0) (Num h0) t'))
                  l h t l0 h0 t').
      unfold eval_type_bound,eval_bound. reflexivity.
      unfold eval_type_bound,eval_bound. reflexivity. lia.
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
    inv Hewf.
    inv HHwt.
    rename H2 into Y1.
    apply (IH  Y1) in H1. 2 : { easy. }
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
          assert (H4 : exists t1, t = (TPtr Checked t1)).
          { eapply ptr_subtype_equiv. eauto.
          } destruct H4. rewrite H4 in *.
          clear H4.
          (* We now proceed by case analysis on '|- n0 : ptr_C w' *)
          inv Y1.
          unfold heap_well_typed in H5.
          inv H3.
          assert (HSim := H2).
          apply H5 in H2. clear H5. inv H2.
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
            unfold allocate_meta in *.
            specialize (subtype_trans D Q (TPtr Checked w) (TPtr Checked t') Checked x H6 HSub) as X1.
            inv H4.
            inv X1. inv H7. simpl. lia. 
            inv H10. inv H12.  inv H7. rewrite replicate_gt_eq. lia. lia.
            inv H7. simpl. lia.
            inv H10. inv H12.  inv H7. rewrite replicate_gt_eq. lia. lia.
            inv H7. simpl. lia.
            apply StructDef.find_1 in H4. rewrite H4 in H7. inv H7.
            split. lia.
            assert ( Z.of_nat (length (map snd (Fields.elements (elt:=type) fs))) > 0). 
            {
              eapply struct_subtype_non_empty; eauto.
              apply (SubTyStructArrayField_1 D Q T fs m).
              apply StructDef.find_2. assumption.
              assumption.
              apply StructDef.find_2.  easy.
            } lia.
            inv X1. inv H7. simpl. lia.
            inv H10. inv H12.  inv H7. rewrite replicate_gt_eq. lia. lia.
            inv H7. simpl. lia.
            inv H10. inv H12.  inv H7. rewrite replicate_gt_eq. lia. lia.
            inv H7. simpl. lia.
            rewrite Z.add_0_r in Hheap;
            inv Ht'tk.
            left.
            assert (exists tv, @get_root D (TPtr Checked x) tv).
            inv HSub.
            exists t'. constructor. easy.
            exists x. constructor. easy.
            exists t'. apply get_root_array.
            exists t'. apply get_root_ntarray.
            inv H4. inv H4. inv H4.
            exists TNat. apply get_root_struct with (f := fs); try easy.
            inv H4.
            destruct H7. destruct H2.  
            eapply step_implies_reduces.
            eapply SDeref; eauto.
            - apply simple_type_means_cast_same. easy.
            - intros. inv H7. inv H4. inv HSub.
              inv H14. inv H15. split. lia. easy.
              inv HSub. inv H14. inv H15. lia.
            - intros. inv H7. inv H4. inv HSub.
              inv H14. inv H15. split. lia. easy.
              inv HSub. inv H14. inv H15. lia.
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
          destruct H4. subst.
          eapply SDerefNull; eauto. 
        }

      (* Case: `w` is an array pointer *)
      * destruct H3.
        destruct H3 as [Ht H3].
        subst.

        assert (HArr : (exists l0 h0, t = (TPtr Checked (TArray l0 h0 t')))
                     \/ (exists l0 h0, t = (TPtr Checked (TNTArray l0 h0 t')))
                        \/ (t = TPtr Checked t')
                           \/ (exists T, (t = TPtr Checked (TStruct T)))).
        {
          inv HSub.
          left. exists l; exists h; reflexivity.
          right. right. left. easy. inv H6.
          inv H6.
          left. exists l0; exists h0; reflexivity.
          right. left. exists l0; exists h0; reflexivity.
          right. right. right. exists T. easy.
        }

        destruct HArr.
        destruct H4 as [l1 [h1 HArr]].
        subst.
        (* We now perform case analysis on 'n > 0' *)
        destruct (Z_gt_dec n 0) as [ Hn0eq0 | Hn0neq0 ].
        (* Case: n > 0 *)
        { (* We now proceed by case analysis on '|- n0 : ptr_C (array n t)' *)
          inv Y1.
          assert (simple_type ((TPtr Checked (TArray l1 h1 t')))) as Y1.
          easy.
          specialize (H5 Y1).
          match goal with
          | [ H : well_typed_lit _ _ _ _ _ _ |- _ ] => inv H
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
            destruct H3 as [Hyp2 Hyp3]; subst.
            inv Y1. inv H4.
            (* should this also be on ' h > 0' instead? DP*)
            destruct (Z_gt_dec h0 0) as [ Hneq0 | Hnneq0 ].
            (* Case: h > 0 *)
            { left. (* We can step according to SDeref *)
              (* LEO: This looks exactly like the previous one. Abstract ? *)
              inv H7. inv H8.
              specialize (simple_type_means_cast_same t' st H5) as eq1.
              destruct (Z_gt_dec l0 0).

              (* if l > 0 we have a bounds error*)
              {
                eapply step_implies_reduces. 
                apply (SDerefLowOOB D (fenv empty_env) st H n (TPtr Checked (TArray (Num l0) (Num h0) t'))
                           (TPtr Checked (TArray (Num l0) (Num h0) t')) l0). easy.
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

              destruct H12 with (k := 0) as [ n' [ t'' [ Ht'tk [ Hheap Hwtn' ] ] ] ].
              { (split;  lia). }

              rewrite Z.add_0_r in Hheap.
              simpl in *.

              assert (Hp': Z.of_nat (Pos.to_nat p) = Z.pos p) by lia.
              rewrite Hp' in *; clear Hp'.
              assert (Hp': Pos.to_nat p = Z.to_nat (Z.pos p)) by (simpl; reflexivity).
              rewrite Hp' in *; clear Hp'. 

              assert (t' = t'').
              {
                eapply replicate_nth; eauto.
              }
              subst t''.
              eapply step_implies_reduces.
              apply (SDeref D (fenv empty_env) st H n n' t' (TPtr Checked (TArray (Num l0) (Num h0) t'))
                          (TPtr Checked (TArray (Num l0) (Num h0) t'))); eauto.
              apply simple_type_means_cast_same. constructor. constructor.  easy.
              intros l' h' t'' HT.
              inv HT.
              split; zify; lia.
              intros. inv H3.
              apply get_root_array.

              inv H15. inv H16.

              destruct (Z_gt_dec l0 0).

              (* if l > 0 we have a bounds error*)
              {
                eapply step_implies_reduces. 
                apply (SDerefLowOOB D (fenv empty_env) st H n (TPtr Checked (TArray (Num l0) (Num h0) t'))
                           (TPtr Checked (TArray (Num l0) (Num h0) t')) l0). easy.
                unfold eval_type_bound. eauto.
                unfold get_low_ptr. easy.
              }

              assert (l0 = 0) by lia.
              assert (h0 = 1) by lia.
              subst.

              (* if l <= 0 we can step according to SDeref. *)
              inv H13. inv H8.
              specialize (H12 0). simpl in *.
              assert (0 <= 0 < 1) by lia.
              apply H12 in H3. destruct H3 as [n' [t' [X1 [X2 X3]]]].
              inv X1.
              eapply step_implies_reduces.
              apply (SDeref D (fenv empty_env) st H n n' TNat (TPtr Checked (TArray (Num 0) (Num 1) TNat))
                          (TPtr Checked (TArray (Num 0) (Num 1) TNat))); eauto.
              apply simple_type_means_cast_same. constructor. constructor.  easy.
              rewrite Z.add_0_r in X2. easy.
              intros. inv H3. lia.
              intros. inv H3.
              apply get_root_array.

              inv H8.
              specialize (H12 0). simpl in *.
              assert (0 <= 0 < 1) by lia.
              apply H12 in H3. destruct H3 as [n' [t' [X1 [X2 X3]]]].
              inv X1.
              eapply step_implies_reduces.
              apply (SDeref D (fenv empty_env) st H n n' (TPtr m0 w) (TPtr Checked (TArray (Num 0) (Num 1) (TPtr m0 w)))
                          (TPtr Checked (TArray (Num 0) (Num 1) (TPtr m0 w)))); eauto.
              apply simple_type_means_cast_same. constructor. constructor.  easy.
              rewrite Z.add_0_r in X2. easy.
              intros. inv H3. lia.
              intros. inv H3.
              apply get_root_array.
              inv H11. inv H11.
              inv H11. inv H15.

              destruct (Z_gt_dec l0 0).

              (* if l > 0 we have a bounds error*)
              {
                eapply step_implies_reduces. 
                apply (SDerefLowOOB D (fenv empty_env) st H n (TPtr Checked (TArray (Num l0) (Num h0) t'))
                           (TPtr Checked (TArray (Num l0) (Num h0) t')) l0). lia.
                unfold eval_type_bound. eauto.
                unfold get_low_ptr. easy.
              }

              (* if l <= 0 we can step according to SDeref. *)
              inv H8.
              assert (l2 <= 0) by lia.
              rewrite replicate_gt_eq in *.

              assert (Hhl : h2 - l2 > 0). {
                destruct h0. inv Hneq0. lia. inv Hneq0.
              }

              destruct H12 with (k := 0) as [ n' [ t'' [ Ht'tk [ Hheap Hwtn' ] ] ] ].
              lia.
              rewrite Z.add_0_r in Hheap.
              simpl in *.
              unfold Zreplicate in Ht'tk.

              destruct (h2 - l2) as [| p | ?] eqn:Hp; zify; [lia | |lia].
              simpl in *.

              assert (Hp': Pos.to_nat p = Z.to_nat (Z.pos p)) by (simpl; reflexivity).
              rewrite Hp' in *; clear Hp'. 

              assert (t' = t'').
              {
                eapply replicate_nth; eauto.
              }
              subst t''.
              eapply step_implies_reduces.
              apply (SDeref D (fenv empty_env) st H n n' t' (TPtr Checked (TArray (Num l0) (Num h0) t'))
                          (TPtr Checked (TArray (Num l0) (Num h0) t'))); eauto.
              apply simple_type_means_cast_same. constructor. constructor.  easy.
              intros l' h' t'' HT.
              inv HT.
              split; zify; lia.
              intros. inv H8.
              apply get_root_array.
              lia.
              inv H6.
              
              inv H11. inv H15. 
              destruct (Z_gt_dec l0 0).

              (* if l > 0 we have a bounds error*)
              {
                eapply step_implies_reduces. 
                apply (SDerefLowOOB D (fenv empty_env) st H n (TPtr Checked (TArray (Num l0) (Num h0) t'))
                           (TPtr Checked (TArray (Num l0) (Num h0) t')) l0). lia.
                unfold eval_type_bound. eauto.
                unfold get_low_ptr. easy.
              }

              (* if l <= 0 we can step according to SDeref. *)
              inv H8.
              assert (l2 <= 0) by lia.
              rewrite replicate_gt_eq in *.

              assert (Hhl : h2 - l2 > 0). {
                destruct h0. inv Hneq0. lia. inv Hneq0.
              }

              destruct H12 with (k := 0) as [ n' [ t'' [ Ht'tk [ Hheap Hwtn' ] ] ] ].
              lia.
              rewrite Z.add_0_r in Hheap.
              simpl in *.
              unfold Zreplicate in Ht'tk.

              destruct (h2 - l2 + 1) as [| p | ?] eqn:Hp; zify; [lia | |lia].
              simpl in *.

              assert (Hp': Pos.to_nat p = Z.to_nat (Z.pos p)) by (simpl; reflexivity).
              rewrite Hp' in *; clear Hp'. 

              assert (t' = t'').
              {
                eapply replicate_nth; eauto.
              }
              subst t''.
              eapply step_implies_reduces.
              apply (SDeref D (fenv empty_env) st H n n' t' (TPtr Checked (TArray (Num l0) (Num h0) t'))
                          (TPtr Checked (TArray (Num l0) (Num h0) t'))); eauto.
              apply simple_type_means_cast_same. constructor. constructor.  easy.
              intros l' h' t'' HT.
              inv HT.
              split; zify; lia.
              intros. inv H8.
              apply get_root_array.
              lia.
              inv H6.
              
              inv H16. inv H17.
              destruct (Z_gt_dec l0 0).

              (* if l > 0 we have a bounds error*)
              {
                eapply step_implies_reduces. 
                apply (SDerefLowOOB D (fenv empty_env) st H n (TPtr Checked (TArray (Num l0) (Num h0) TNat))
                           (TPtr Checked (TArray (Num l0) (Num h0) TNat)) l0). easy.
                unfold eval_type_bound. eauto.
                unfold get_low_ptr. easy.
              }

              assert (l0 = 0) by lia.
              assert (h0 = 1) by lia.
              subst.

              destruct H12 with (k := 0) as [ n' [ t1' [ Ht'tk [ Hheap Hwtn' ] ] ] ].
              unfold allocate_meta in *. inv H8. 
              destruct (StructDef.find T D) eqn:HFind.
               assert (Hmap : StructDef.MapsTo T f D). 
               {
                 eapply find_implies_mapsto. assumption.
                }
               assert ( Z.of_nat (length (map snd (Fields.elements (elt:=type) f))) > 0). 
              {
                 eapply struct_subtype_non_empty; eauto.
                 apply (SubTyStructArrayField_1 D Q T fs m).
                 assumption.
                 assumption.
              }
              inv H4; zify; try lia.
              inv H4.

              rewrite Z.add_0_r in Hheap;
              inv Ht'tk.
              eapply step_implies_reduces.
              eapply SDeref; eauto.
              - apply simple_type_means_cast_same. easy.
              - intros. inv H3. lia.
              - intros. inv H3.
              - apply get_root_array.

            }
            (* Case: h <= 0 *)
            { (* We can step according to SDerefOOB *)
              subst. left. eapply step_implies_reduces. 
              eapply (SDerefHighOOB D (fenv empty_env) st H n (TPtr Checked (TArray (Num l0) (Num h0) t'))
                           (TPtr Checked (TArray (Num l0) (Num h0) t')) h0). eauto.
              unfold eval_type_bound; eauto. unfold get_high_ptr. reflexivity.
            }
          }
        } 
        (* Case: n <= 0 *)
        { (* We can step according to SDerefNull *)
          subst... }

        (* when subtype is nt-array ptr. *)
        destruct H4.
        destruct H4 as [l1 [h1 HArr]].
        subst.
        (* We now perform case analysis on 'n > 0' *)
        destruct (Z_gt_dec n 0) as [ Hn0eq0 | Hn0neq0 ].
        (* Case: n > 0 *)
        { (* We now proceed by case analysis on '|- n0 : ptr_C (array n t)' *)
          inv Y1.
          assert (simple_type ((TPtr Checked (TNTArray l1 h1 t')))) as Y1.
          easy.
          specialize (H5 Y1).
          match goal with
          | [ H : well_typed_lit _ _ _ _ _ _ |- _ ] => inv H
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
            destruct H3 as [Hyp2 Hyp3]; subst.
            inv Y1. inv H4. 
            (* should this also be on ' h > 0' instead? DP*)
            destruct (Z_gt_dec h0 0) as [ Hneq0 | Hnneq0 ].
            (* Case: h > 0 *)
            { left. (* We can step according to SDeref *)
              (* LEO: This looks exactly like the previous one. Abstract ? *)
              inv H7. inv H8.
              specialize (simple_type_means_cast_same t' st H5) as eq1.
              destruct (Z_gt_dec l0 0).

              (* if l > 0 we have a bounds error*)
              {
                eapply step_implies_reduces. 
                apply (SDerefLowOOB D (fenv empty_env) st H n (TPtr Checked (TNTArray (Num l0) (Num h0) t'))
                           (TPtr Checked (TNTArray (Num l0) (Num h0) t')) l0). easy.
                unfold eval_type_bound. eauto.
                unfold get_low_ptr. easy.
              }
              
              (* if l <= 0 we can step according to SDeref. *)

              assert (Hhl : h0 - l0 +1 > 0). {
                destruct h0. inv Hneq0. lia. inv Hneq0.
              }
              destruct (h0 - l0 +1) as [| p | ?] eqn:Hp; zify; [lia | |lia].
              simpl in *.
              rewrite replicate_length in *.

              destruct H12 with (k := 0) as [ n' [ t'' [ Ht'tk [ Hheap Hwtn' ] ] ] ].
              { (split;  lia). }

              rewrite Z.add_0_r in Hheap.
              simpl in *.

              assert (Hp': Z.of_nat (Pos.to_nat p) = Z.pos p) by lia.
              rewrite Hp' in *; clear Hp'.
              assert (Hp': Pos.to_nat p = Z.to_nat (Z.pos p)) by (simpl; reflexivity).
              rewrite Hp' in *; clear Hp'. 

              assert (t' = t'').
              {
                eapply replicate_nth; eauto.
              }
              subst t''.
              eapply step_implies_reduces.
              apply (SDeref D (fenv empty_env) st H n n' t' (TPtr Checked (TNTArray (Num l0) (Num h0) t'))
                          (TPtr Checked (TNTArray (Num l0) (Num h0) t'))); eauto.
              apply simple_type_means_cast_same. constructor. constructor.  easy.
              intros l' h' t'' HT. inv HT.
              intros.
              inv H3.
              split; zify; lia.
              apply get_root_ntarray.
              inv H11. inv H11.

              inv H11. inv H15.

              destruct (Z_gt_dec l0 0).

              (* if l > 0 we have a bounds error*)
              {
                eapply step_implies_reduces. 
                apply (SDerefLowOOB D (fenv empty_env) st H n (TPtr Checked (TNTArray (Num l0) (Num h0) t'))
                           (TPtr Checked (TNTArray (Num l0) (Num h0) t')) l0). easy.
                unfold eval_type_bound. eauto.
                unfold get_low_ptr. easy.
              }

              (* if l <= 0 we can step according to SDeref. *)
              inv H8.
              assert (l2 <= 0) by lia.
              rewrite replicate_gt_eq in *.

              assert (Hhl : h2 - l2 + 1 > 0). {
                destruct h0. inv Hneq0. lia. inv Hneq0.
              }

              destruct H12 with (k := 0) as [ n' [ t'' [ Ht'tk [ Hheap Hwtn' ] ] ] ].
              lia.
              rewrite Z.add_0_r in Hheap.
              simpl in *.
              unfold Zreplicate in Ht'tk.

              destruct (h2 - l2 + 1) as [| p | ?] eqn:Hp; zify; [lia | |lia].
              simpl in *.

              assert (Hp': Pos.to_nat p = Z.to_nat (Z.pos p)) by (simpl; reflexivity).
              rewrite Hp' in *; clear Hp'. 

              assert (t' = t'').
              {
                eapply replicate_nth; eauto.
              }
              subst t''.
              eapply step_implies_reduces.
              apply (SDeref D (fenv empty_env) st H n n' t' (TPtr Checked (TNTArray (Num l0) (Num h0) t'))
                          (TPtr Checked (TNTArray (Num l0) (Num h0) t'))); eauto.
              apply simple_type_means_cast_same. constructor. constructor.  easy.
              intros l' h' t'' HT. inv HT.
              intros. inv H8.
              split; zify; lia.
              apply get_root_ntarray.
              lia.
              inv H6.
            }
            (* Case: h <= 0 *)
            { (* We can step according to SDerefOOB *)
              subst. left. eapply step_implies_reduces. 
              eapply (SDerefHighOOB D (fenv empty_env) st H n (TPtr Checked (TNTArray (Num l0) (Num h0) t'))
                           (TPtr Checked (TNTArray (Num l0) (Num h0) t')) h0). eauto.
              unfold eval_type_bound; eauto. unfold get_high_ptr. reflexivity.
            }

          }
        } 
        (* Case: n <= 0 *)
        { (* We can step according to SDerefNull *)
          subst... }

        destruct H4.
        destruct H3 as [Ht H3].
        subst.

        destruct (Z_gt_dec n 0) as [ Hn0eq0 | Hn0neq0 ].
        (* Case: n > 0 *)
        { (*Since w is subtype of a ptr it is also a ptr*)
          (* We now proceed by case analysis on '|- n0 : ptr_C w' *)
          inv Y1.
          unfold heap_well_typed in H5.
          assert (simple_type (TPtr Checked t')).
          easy.
          assert (Hsim := H4). 
          apply H5 in H4. clear H5. inv H4.
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
            inv H7. 

            destruct H12 with (k := 0) as [ n' [ t1' [ Ht'tk [ Hheap Hwtn' ] ] ] ].
            unfold allocate_meta in *. destruct t'.
            inv H8. simpl. lia. inv H8. simpl. lia.
            inv Ht. inv Ht. inv Ht.

            rewrite Z.add_0_r in Hheap;
            inv Ht'tk.
            left.
            eapply step_implies_reduces.
            eapply SDeref; eauto.
            apply simple_type_means_cast_same. constructor. inv Hsim. easy.
            intros. inv H4. inv Ht.
            intros. inv H4. inv Ht.
            constructor. easy.

            inv H13. inv H14.

            destruct (Z_gt_dec h1 0).

            (* if l > 0 we have a bounds error*)
            {
                left.
                eapply step_implies_reduces. 
                apply (SDerefLowOOB D (fenv empty_env) st H n (TPtr Checked (TArray (Num h1) (Num l0) w))
                           (TPtr Checked (TArray (Num h1) (Num l0) w)) h1). easy.
                unfold eval_type_bound. eauto.
                unfold get_low_ptr. easy.
            }

            destruct (Z_ge_dec 0 l0).

            (* if h <= 0 we have a bounds error*)
            {
                left.
                eapply step_implies_reduces. 
                apply (SDerefHighOOB D (fenv empty_env) st H n (TPtr Checked (TArray (Num h1) (Num l0) w))
                           (TPtr Checked (TArray (Num h1) (Num l0) w)) l0). easy.
                unfold eval_type_bound. eauto.
                unfold get_high_ptr. easy.
            }

            assert (h1 = 0) by lia.
            assert (l0 = 1) by lia. subst.
              (* if l <= 0 we can step according to SDeref. *)
              inv H11. inv H8.
              left.
              specialize (H12 0). simpl in *.
              assert (0 <= 0 < 1) by lia.
              apply H12 in H4. destruct H4 as [n' [t' [X1 [X2 X3]]]].
              inv X1.
              eapply step_implies_reduces.
              apply (SDeref D (fenv empty_env) st H n n' TNat (TPtr Checked (TArray (Num 0) (Num 1) TNat))
                          (TPtr Checked (TArray (Num 0) (Num 1) TNat))); eauto.
              apply simple_type_means_cast_same. constructor. constructor.  easy.
              rewrite Z.add_0_r in X2. easy.
              intros. inv H4. lia.
              intros. inv H4.
              apply get_root_array.

              inv H8. left.
              specialize (H12 0). simpl in *.
              assert (0 <= 0 < 1) by lia.
              apply H12 in H4. destruct H4 as [n' [t' [X1 [X2 X3]]]].
              inv X1.
              eapply step_implies_reduces.
              apply (SDeref D (fenv empty_env) st H n n' (TPtr m0 w0) (TPtr Checked (TArray (Num 0) (Num 1) (TPtr m0 w0)))
                          (TPtr Checked (TArray (Num 0) (Num 1) (TPtr m0 w0)))); eauto.
              apply simple_type_means_cast_same. constructor. constructor.  easy.
              rewrite Z.add_0_r in X2. easy.
              intros. inv H4. lia.
              intros. inv H4.
              apply get_root_array.
              inv Hsim. inv H10.
              inv H6. 
              inv H13. inv H14.

              inv H8. left.
              assert (Hhl : (h1 - l1) > 0) by lia.

              destruct (h1 - l1) as [| p | ?] eqn:Hp; zify; [lia | |lia].
              simpl in *.
              rewrite replicate_length in *.
              assert (HL: l1 + Z.of_nat (Pos.to_nat p) = h1) by (zify; lia).
              rewrite HL in *; try lia.

              destruct H12 with (k := 0) as [ n' [ t'' [ Ht'tk [ Hheap Hwtn' ] ] ] ].
              { (split;  lia). }

              rewrite Z.add_0_r in Hheap.
              simpl in *.

              assert (Hp': Z.of_nat (Pos.to_nat p) = Z.pos p) by lia.
              rewrite Hp' in *; clear Hp'.
              assert (Hp': Pos.to_nat p = Z.to_nat (Z.pos p)) by (simpl; reflexivity).
              rewrite Hp' in *; clear Hp'. 

              assert (t' = t'').
              {
                eapply replicate_nth; eauto.
              }
              subst t''.
              apply (simple_type_means_cast_same) with (s := st) in H5 as eq1.
              eapply step_implies_reduces.
              apply (SDeref D (fenv empty_env) st H n n' t' (TPtr Checked t') (TPtr Checked t')); eauto.
              apply simple_type_means_cast_same. constructor. inv H2. easy.
              intros. inv H4. inv H11.
              intros. inv H4. inv H11.
              apply get_root_word. easy.

              inv H13. inv H14.
              inv H8. left.
              assert (Hhl : (h1 - l1 + 1) > 0) by lia.

              destruct (h1 - l1  + 1) as [| p | ?] eqn:Hp; zify; [lia | |lia].
              simpl in *.
              rewrite replicate_length in *.
              assert (HL: l1 + Z.of_nat (Pos.to_nat p) = h1+1) by (zify; lia).
              rewrite HL in *; try lia.

              destruct H12 with (k := 0) as [ n' [ t'' [ Ht'tk [ Hheap Hwtn' ] ] ] ].
              { (split;  lia). }

              rewrite Z.add_0_r in Hheap.
              simpl in *.

              assert (Hp': Z.of_nat (Pos.to_nat p) = Z.pos p) by lia.
              rewrite Hp' in *; clear Hp'.
              assert (Hp': Pos.to_nat p = Z.to_nat (Z.pos p)) by (simpl; reflexivity).
              rewrite Hp' in *; clear Hp'. 

              assert (t' = t'').
              {
                eapply replicate_nth; eauto.
              }
              subst t''.

              eapply step_implies_reduces.
              apply (SDeref D (fenv empty_env) st H n n' t' (TPtr Checked t') (TPtr Checked t')); eauto.
              apply simple_type_means_cast_same. constructor. inv H2. easy.
              intros. inv H4. inv H11.
              intros. inv H4. inv H11.
              apply get_root_word. easy.
              inv H6.

              inv H11. inv H13. inv H2. inv H10.
              specialize (simple_type_means_cast_same t st H7) as eq1.
              destruct (Z_gt_dec h1 0).

              (* if l > 0 we have a bounds error*)
              { left.
                eapply step_implies_reduces. 
                apply (SDerefLowOOB D (fenv empty_env) st H n (TPtr Checked (TArray (Num h1) (Num l0) t))
                           (TPtr Checked (TArray (Num h1) (Num l0) t)) h1). easy.
                unfold eval_type_bound. eauto.
                unfold get_low_ptr. easy.
              }
              
            destruct (Z_ge_dec 0 l0).

            (* if h <= 0 we have a bounds error*)
            {
                left.
                eapply step_implies_reduces. 
                apply (SDerefHighOOB D (fenv empty_env) st H n (TPtr Checked (TArray (Num h1) (Num l0) t))
                           (TPtr Checked (TArray (Num h1) (Num l0) t)) l0). easy.
                unfold eval_type_bound. eauto.
                unfold get_high_ptr. easy.
            }
              (* if l <= 0 we can step according to SDeref. *)

              inv H8.
              assert (Hhl : h2 - l1 > 0) by lia.
              destruct (h2 - l1) as [| p | ?] eqn:Hp; zify; [lia | |lia].
              simpl in *.
              rewrite replicate_length in *.

              destruct H12 with (k := 0) as [ n' [ t'' [ Ht'tk [ Hheap Hwtn' ] ] ] ].
              { (split;  lia). }

              rewrite Z.add_0_r in Hheap.
              simpl in *.

              assert (Hp': Z.of_nat (Pos.to_nat p) = Z.pos p) by lia.
              rewrite Hp' in *; clear Hp'.
              assert (Hp': Pos.to_nat p = Z.to_nat (Z.pos p)) by (simpl; reflexivity).
              rewrite Hp' in *; clear Hp'. 

              assert (t = t'').
              {
                eapply replicate_nth; eauto.
              }
              subst t''. left.
              eapply step_implies_reduces.
              apply (SDeref D (fenv empty_env) st H n n' t (TPtr Checked (TArray (Num h1) (Num l0) t))
                          (TPtr Checked (TArray (Num h1) (Num l0) t))); eauto.
              apply simple_type_means_cast_same. constructor. constructor.  easy.
              intros l' h' t'' HT. inv HT. split; zify; lia.
              intros.
              inv H2.
              apply get_root_array.
              inv H6. inv H6.
              inv H6. inv Hsim. inv H10.
              inv H11. inv H13. inv H2. inv H10.
              specialize (simple_type_means_cast_same t st H7) as eq1.
              destruct (Z_gt_dec h1 0).

              (* if l > 0 we have a bounds error*)
              { left.
                eapply step_implies_reduces. 
                apply (SDerefLowOOB D (fenv empty_env) st H n (TPtr Checked (TArray (Num h1) (Num l0) t))
                           (TPtr Checked (TArray (Num h1) (Num l0) t)) h1). easy.
                unfold eval_type_bound. eauto.
                unfold get_low_ptr. easy.
              }

              (* if h <= 0 we have a bounds error*)
              destruct (Z_ge_dec 0 l0).
              { left.
                eapply step_implies_reduces. 
                apply (SDerefHighOOB D (fenv empty_env) st H n (TPtr Checked (TArray (Num h1) (Num l0) t))
                           (TPtr Checked (TArray (Num h1) (Num l0) t)) l0). easy.
                unfold eval_type_bound. eauto.
                unfold get_high_ptr. easy.
              }
              
              (* if l <= 0 we can step according to SDeref. *)
              inv H8.

              assert (Hhl : h2 - l1 +1 > 0) by lia.
              destruct (h2 - l1 +1) as [| p | ?] eqn:Hp; zify; [lia | |lia].
              simpl in *.
              rewrite replicate_length in *.
              destruct H12 with (k := 0) as [ n' [ t'' [ Ht'tk [ Hheap Hwtn' ] ] ] ].
              { (split;  lia). }

              rewrite Z.add_0_r in Hheap.
              simpl in *.

              assert (Hp': Z.of_nat (Pos.to_nat p) = Z.pos p) by lia.
              rewrite Hp' in *; clear Hp'.
              assert (Hp': Pos.to_nat p = Z.to_nat (Z.pos p)) by (simpl; reflexivity).
              rewrite Hp' in *; clear Hp'. 

              assert (t = t'').
              {
                eapply replicate_nth; eauto.
              }
              subst t''. left.
              eapply step_implies_reduces.
              apply (SDeref D (fenv empty_env) st H n n' t (TPtr Checked (TArray (Num h1) (Num l0) t))
                          (TPtr Checked (TArray (Num h1) (Num l0) t))); eauto.
              apply simple_type_means_cast_same. constructor. constructor.  easy.
              intros l' h' t'' HT. inv HT.
              split; zify; lia.
              intros.
              inv H2.
              apply get_root_array.
              inv H6. inv H6.
              inv H6. inv Hsim. inv H10.

              inv H11. inv H13. inv H2. inv H10.
              specialize (simple_type_means_cast_same t st H7) as eq1.
              destruct (Z_gt_dec h1 0).

              (* if l > 0 we have a bounds error*)
              { left.
                eapply step_implies_reduces. 
                apply (SDerefLowOOB D (fenv empty_env) st H n (TPtr Checked (TNTArray (Num h1) (Num l0) t))
                           (TPtr Checked (TNTArray (Num h1) (Num l0) t)) h1). easy.
                unfold eval_type_bound. eauto.
                unfold get_low_ptr. easy.
              }

              (* if h <= 0 we have a bounds error*)
              destruct (Z_ge_dec 0 l0).
              { left.
                eapply step_implies_reduces. 
                apply (SDerefHighOOB D (fenv empty_env) st H n (TPtr Checked (TNTArray (Num h1) (Num l0) t))
                           (TPtr Checked (TNTArray (Num h1) (Num l0) t)) l0). easy.
                unfold eval_type_bound. eauto.
                unfold get_high_ptr. easy.
              }
              
              (* if l <= 0 we can step according to SDeref. *)
              inv H8.

              assert (Hhl : h2 - l1 +1 > 0) by lia.
              destruct (h2 - l1 +1) as [| p | ?] eqn:Hp; zify; [lia | |lia].
              simpl in *.
              rewrite replicate_length in *.
              destruct H12 with (k := 0) as [ n' [ t'' [ Ht'tk [ Hheap Hwtn' ] ] ] ].
              { (split;  lia). }

              rewrite Z.add_0_r in Hheap.
              simpl in *.

              assert (Hp': Z.of_nat (Pos.to_nat p) = Z.pos p) by lia.
              rewrite Hp' in *; clear Hp'.
              assert (Hp': Pos.to_nat p = Z.to_nat (Z.pos p)) by (simpl; reflexivity).
              rewrite Hp' in *; clear Hp'. 

              assert (t = t'').
              {
                eapply replicate_nth; eauto.
              }
              subst t''. left.
              eapply step_implies_reduces.
              apply (SDeref D (fenv empty_env) st H n n' t (TPtr Checked (TNTArray (Num h1) (Num l0) t))
                          (TPtr Checked (TNTArray (Num h1) (Num l0) t))); eauto.
              apply simple_type_means_cast_same. constructor. constructor.  easy.
              intros l' h' t'' HT. inv HT.
              intros.
              inv H2.
              split; zify; lia.
              apply get_root_ntarray.
              inv H6. inv H6.
              inv H6. inv Hsim. inv H10.


              destruct H12 with (k := 0) as [ n' [ t1' [ Ht'tk [ Hheap Hwtn' ] ] ] ].
              unfold allocate_meta in *. inv H8. 
              destruct (StructDef.find T D) eqn:HFind.
               assert (Hmap : StructDef.MapsTo T f D). 
               {
                 eapply find_implies_mapsto. assumption.
                }
               assert ( Z.of_nat (length (map snd (Fields.elements (elt:=type) f))) > 0). 
              {
                 eapply struct_subtype_non_empty; eauto.
                 apply (SubTyStructArrayField_1 D Q T fs m).
                 assumption.
                 assumption.
              }
              inv H5; zify; try lia.
              inv H5.

              rewrite Z.add_0_r in Hheap;
              inv Ht'tk. left.
              eapply step_implies_reduces.
              eapply SDeref; eauto.
              apply simple_type_means_cast_same. easy.
              intros. inv H4.
              intros. inv H4.
              apply get_root_word. easy.

              inv H14. inv H15.
              destruct (Z_gt_dec h1 0).

              (* if l > 0 we have a bounds error*)
              { left.
                eapply step_implies_reduces. 
                apply (SDerefLowOOB D (fenv empty_env) st H n (TPtr Checked (TArray (Num h1) (Num l0) TNat))
                           (TPtr Checked (TArray (Num h1) (Num l0) TNat)) h1). easy.
                unfold eval_type_bound. eauto.
                unfold get_low_ptr. easy.
              }

              (* if h <= 0 we have a bounds error*)
              destruct (Z_ge_dec 0 l0).
              { left.
                eapply step_implies_reduces. 
                apply (SDerefHighOOB D (fenv empty_env) st H n (TPtr Checked (TArray (Num h1) (Num l0) TNat))
                           (TPtr Checked (TArray (Num h1) (Num l0) TNat)) l0). easy.
                unfold eval_type_bound. eauto.
                unfold get_high_ptr. easy.
              }

              assert (h1 = 0) by lia.
              assert (l0 = 1) by lia.
              subst.

              destruct H12 with (k := 0) as [ n' [ t1' [ Ht'tk [ Hheap Hwtn' ] ] ] ].
              unfold allocate_meta in *. inv H8. 
              destruct (StructDef.find T D) eqn:HFind.
               assert (Hmap : StructDef.MapsTo T f D). 
               {
                 eapply find_implies_mapsto. assumption.
                }
               assert ( Z.of_nat (length (map snd (Fields.elements (elt:=type) f))) > 0). 
              {
                 eapply struct_subtype_non_empty; eauto.
                 apply (SubTyStructArrayField_1 D Q T fs m).
                 assumption.
                 assumption.
              }
              inv H7; zify; try lia.
              inv H7. left.

              rewrite Z.add_0_r in Hheap;
              inv Ht'tk.
              eapply step_implies_reduces.
              eapply SDeref; eauto.
              apply simple_type_means_cast_same. easy.
              intros. inv H4. lia.
              intros. inv H4.
              apply get_root_array.
              inv Hsim. inv H10.
          }
        }
        (* Case: n <= 0 *)
        { (* We can step according to SDerefNull *)
          left. eapply step_implies_reduces.
         
          eapply SDerefNull; eauto. 
        }

       (* when subtype is a TStruct pointer. *)
        destruct H4.
        destruct H3 as [Ht H3].
        subst.
        inv HSub. inv Ht.        

        destruct (Z_gt_dec n 0) as [ Hn0eq0 | Hn0neq0 ].
        (* Case: n > 0 *)
        { (*Since w is subtype of a ptr it is also a ptr*)
          (* We now proceed by case analysis on '|- n0 : ptr_C w' *)
          inv Y1.
          unfold heap_well_typed in H5.
          assert (simple_type (TPtr Checked (TStruct x))).
          constructor. constructor.
          assert (Hsim := H4). 
          apply H5 in H4. clear H5. inv H4.
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
            inv H7. 
            destruct H16 with (k := 0) as [ n' [ t1' [ Ht'tk [ Hheap Hwtn' ] ] ] ].
            unfold allocate_meta in *. inv H8. 
            destruct (StructDef.find x D) eqn:HFind.
            assert (Hmap : StructDef.MapsTo x f D). 
            {
             eapply find_implies_mapsto. assumption.
            }
            assert ( Z.of_nat (length (map snd (Fields.elements (elt:=type) f))) > 0). 
            {
              eapply struct_subtype_non_empty; eauto.
              apply (SubTyStructArrayField_1 D Q x fs m).
              assumption.
              assumption.
            }
            inv H5; zify; try lia.
            inv H5.

            unfold allocate_meta in *. inv H8.
            destruct (StructDef.find x D) eqn:HFind.
            assert (Hmap : StructDef.MapsTo x f D). 
            {
             eapply find_implies_mapsto. assumption.
            }
            assert ( Z.of_nat (length (map snd (Fields.elements (elt:=type) f))) > 0). 
            {
              eapply struct_subtype_non_empty; eauto.
              apply (SubTyStructArrayField_1 D Q x fs m).
              assumption.
              assumption.
            }

            rewrite Z.add_0_r in Hheap;
            inv Ht'tk. inv H5.
            left.
            eapply step_implies_reduces.
            eapply SDeref; eauto.
            apply simple_type_means_cast_same. easy.
            intros. inv H5.
            intros. inv H5.
            apply get_root_struct with (f0 := f); try easy. 
            apply StructDef.find_1 in H10.
            rewrite H10 in *. inv HFind. easy. inv H5. inv H15. inv H15.
          }
        }
        (* Case: n <= 0 *)
        { (* We can step according to SDerefNull *)
          left. eapply step_implies_reduces.
         
          eapply SDerefNull; eauto. 
        }

        (* when t'' is a TNTArray. *)
        destruct H3 as [Ht H3]. subst.
        assert (HArr : (exists l0 h0, t = (TPtr Checked (TNTArray l0 h0 t')))).
        {
          inv HSub.
          exists l; exists h; easy.
          inv H6. inv H6.
          exists l0; exists h0; reflexivity.
        }

        destruct HArr as [l1 [h1 HArr]].
        rewrite HArr in *. clear HArr.
        (* We now perform case analysis on 'n > 0' *)
        destruct (Z_gt_dec n 0) as [ Hn0eq0 | Hn0neq0 ].
        (* Case: n > 0 *)
        { (* We now proceed by case analysis on '|- n0 : ptr_C (array n t)' *)
          inv Y1.
          assert (simple_type ((TPtr Checked (TNTArray l1 h1 t')))) as Y1.
          easy.
          specialize (H5 Y1).
          match goal with
          | [ H : well_typed_lit _ _ _ _ _ _ |- _ ] => inv H
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
            destruct H3 as [Hyp2 Hyp3]; subst.
            inv Y1. inv H4.
            (* should this also be on ' h > 0' instead? DP*)
            destruct (Z_gt_dec h0 0) as [ Hneq0 | Hnneq0 ].
            (* Case: h > 0 *)
            { left. (* We can step according to SDeref *)
              (* LEO: This looks exactly like the previous one. Abstract ? *)
              destruct (Z_gt_dec l0 0).

              (* if l > 0 we have a bounds error*)
              {
                eapply step_implies_reduces. 
                eapply (SDerefLowOOB D (fenv empty_env) st H n (TPtr Checked (TNTArray (Num l0) (Num h0) t'))
                           (TPtr Checked (TNTArray (Num l0) (Num h0) t')) l0). easy.
                unfold eval_type_bound. eauto.
                unfold get_low_ptr.
                reflexivity.
              }
              
              (* if l <= 0 we can step according to SDeref. *)
              inv H7. inv H8.
              assert (Hhl : (h0 - l0 + 1) > 0). {
                destruct h0. inv Hneq0. lia. inv Hneq0.
              }

              destruct (h0 - l0 + 1) as [| p | ?] eqn:Hp; zify; [lia | |lia].
              simpl in *.
              rewrite replicate_length in *.
              assert (HL: l0 + Z.of_nat (Pos.to_nat p) = h0+1) by (zify; lia).
              rewrite HL in *; try lia.

              destruct H12 with (k := 0) as [ n' [ t'' [ Ht'tk [ Hheap Hwtn' ] ] ] ].
              { (split;  lia). }

              rewrite Z.add_0_r in Hheap.
              simpl in *.

              assert (Hp': Z.of_nat (Pos.to_nat p) = Z.pos p) by lia.
              rewrite Hp' in *; clear Hp'.
              assert (Hp': Pos.to_nat p = Z.to_nat (Z.pos p)) by (simpl; reflexivity).
              rewrite Hp' in *; clear Hp'. 

              assert (t' = t'').
              {
                eapply replicate_nth; eauto.
              }
              subst t''.
              apply (simple_type_means_cast_same) with (s := st) in H5 as eq1.
              eapply step_implies_reduces.
              apply (SDeref D (fenv empty_env) st H n n' t' (TPtr Checked (TNTArray (Num l0) (Num h0) t'))
                          (TPtr Checked (TNTArray (Num l0) (Num h0) t'))); eauto.
              apply simple_type_means_cast_same. constructor. constructor. easy. 
              intros. inv H3.
              intros l' h' t'' HT.
              injection HT. intros. subst.
              split; zify; lia.
              apply get_root_ntarray.
              inv H11. inv H11.

              inv H11. inv H15. inv H8.
              assert (Hhl : (h2 - l2 + 1) > 0). {
                destruct h0. inv Hneq0. lia. inv Hneq0.
              }

              destruct (h2 - l2 + 1) as [| p | ?] eqn:Hp; zify; [lia | |lia].
              simpl in *.
              rewrite replicate_length in *.

              destruct H12 with (k := 0) as [ n' [ t'' [ Ht'tk [ Hheap Hwtn' ] ] ] ].
              { (split;  lia). }

              rewrite Z.add_0_r in Hheap.
              simpl in *.

              assert (Hp': Z.of_nat (Pos.to_nat p) = Z.pos p) by lia.
              rewrite Hp' in *; clear Hp'.
              assert (Hp': Pos.to_nat p = Z.to_nat (Z.pos p)) by (simpl; reflexivity).
              rewrite Hp' in *; clear Hp'. 

              assert (t' = t'').
              {
                eapply replicate_nth; eauto.
              }
              subst t''.
              apply (simple_type_means_cast_same) with (s := st) in H5 as eq1.
              eapply step_implies_reduces.
              apply (SDeref D (fenv empty_env) st H n n' t' (TPtr Checked (TNTArray (Num l0) (Num h0) t'))
                          (TPtr Checked (TNTArray (Num l0) (Num h0) t'))); eauto.
              apply simple_type_means_cast_same. constructor. constructor. easy. 
              intros. inv H3.
              intros l' h' t'' HT.
              injection HT. intros. subst.
              split; zify; lia.
              apply get_root_ntarray.
              inv H6.
            }
            (* Case: h <= 0 *)
            { (* We can step according to SDerefOOB *)
              subst. left. eapply step_implies_reduces. 
              eapply (SDerefHighOOB D (fenv empty_env) st H n (TPtr Checked (TNTArray (Num l0) (Num h0) t'))
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
    inv HHwt.
    inv H1.
    rename H5 into Y1. rename H6 into Y2.
    specialize (IH1 Y1 H3 eq_refl).
    specialize (IH2 Y2 H4 eq_refl).
    destruct IH1 as [ HVal1 | [ HRed1 | HUnchk1 ] ]; eauto.
    + inv HVal1 as [ n1 t1 ].
      destruct IH2 as [ HVal2 | [ HRed2 | HUnchk2 ] ]; eauto.
      * left.
        inv HVal2.
        ctx (EDeref (EPlus (ELit n1 t1) (ELit n t0))) (in_hole (EPlus (ELit n1 t1) (ELit n t0)) (CDeref CHole)).
        inv HTy1.
        inv H2. inv H9.
        exists Checked.
        exists st.
        exists H.
        { destruct (Z_gt_dec n1 0).
          - (* n1 > 0 *)
            exists (RExpr (EDeref (ELit (n1 + n) (TPtr Checked (TArray (Num (l0 - n)) (Num (h0 - n)) t))))).
            ctx (EDeref (ELit (n1 + n) (TPtr Checked (TArray (Num (l0 - n)) (Num (h0 - n)) t))))
                (in_hole (ELit (n1 + n) (TPtr Checked (TArray (Num (l0 - n)) (Num (h0 - n)) t))) (CDeref CHole)).
            rewrite HCtx.
            rewrite HCtx0.
            inv HTy2.
            eapply RSExp; eauto.
            assert ((TPtr Checked (TArray (Num (l0 - n)) (Num (h0 - n)) t)) 
             = sub_type_bound (TPtr Checked (TArray (Num l0) (Num h0) t)) n).
            unfold sub_type_bound,sub_bound. reflexivity.
            rewrite H2.
            apply SPlusChecked. assumption.
            unfold is_array_ptr. easy.
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
    inv HHwt.
    inv H1.
    rename H5 into Y1. rename H6 into Y2.
    specialize (IH1 Y1 H3 eq_refl).
    specialize (IH2 Y2 H4 eq_refl).
    destruct IH1 as [ HVal1 | [ HRed1 | HUnchk1 ] ]; eauto.
    + inv HVal1 as [ n1 t1 ].
      destruct IH2 as [ HVal2 | [ HRed2 | HUnchk2 ] ]; eauto.
      * left.
        inv HVal2.
        ctx (EDeref (EPlus (ELit n1 t1) (ELit n t0))) (in_hole (EPlus (ELit n1 t1) (ELit n t0)) (CDeref CHole)).
        inv HTy1.
        inv H2. inv H9.
        exists Checked.
        exists st.
        exists H.
        { destruct (Z_gt_dec n1 0).
          - (* n1 > 0 *)
            exists (RExpr (EDeref (ELit (n1 + n) (TPtr Checked (TNTArray (Num (l0 - n)) (Num (h0 - n)) t))))).
            ctx (EDeref (ELit (n1 + n) (TPtr Checked (TNTArray (Num (l0 - n)) (Num (h0 - n)) t))))
                (in_hole (ELit (n1 + n) (TPtr Checked (TNTArray (Num (l0 - n)) (Num (h0 - n)) t))) (CDeref CHole)).
            rewrite HCtx.
            rewrite HCtx0.
            inv HTy2.
            eapply RSExp; eauto.
            assert ((TPtr Checked (TNTArray (Num (l0 - n)) (Num (h0 - n)) t)) 
             = sub_type_bound (TPtr Checked (TNTArray (Num l0) (Num h0) t)) n).
            unfold sub_type_bound,sub_bound. reflexivity.
            rewrite H2.
            apply SPlusChecked. assumption.
            unfold is_array_ptr. easy.
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
Admitted.
(*
  - (* Assign1 rule. This isn't a value, so it must reduce *)
    right.

    (* If m' is unchecked, then we are typing mode is unchecked *)
    destruct m'; [> | right; eauto 20 with Progress].
    clear HMode.

    (* Invoke IH on e1 *)
    inv Hewf.
    inv HHwt. rename H4 into Y1. rename H5 into Y2.
    apply (IH1 Y1) in H2. 2 : { easy. }
    destruct H2 as [ HVal1 | [ HRed1 | [| HUnchk1 ] ] ]; idtac...
    + (* Case: e1 is a value *)
      inv HVal1 as [ n1' t1' WTt1' Ht1' ].
      (* Invoke IH on e2 *)
      apply (IH2 Y2) in H3. 2 : { easy. }
      inv H3 as [ HVal2 | [ HRed2 | [| HUnchk2 ] ] ]; idtac...
      * (* Case: e2 is a value, so we can take a step *)
        inv HVal2 as [n2' t2' Wtt2' Ht2' ].
        {
            inv HTy1; eauto.
            inv Y1. 
            assert (Hsim := H0).
            apply H3 in H0. clear H3.
            match goal with
            | [ H : well_typed_lit _ _ _ _ _ _ |- _ ] => inv H
            end... 
            + left.
              eapply step_implies_reduces.
              eapply SAssignNull; eauto. lia.
              apply simple_type_means_eval_same. assumption.
            + solve_empty_scope.
            + left. unfold allocate_meta in H3.
              destruct t; inv H3; simpl in *. 
              ++   destruct (H6 0) as [x [xT [HNth [HMap HWT]]]]; simpl in*;
                try (zify; lia);
                try rewrite Z.add_0_r in *;
                eauto; 
              try (eapply step_implies_reduces;
                   eapply SAssign; eauto);
              try (eexists; eauto);
              intros; try congruence...
              constructor. constructor. inv H2. inv H2. inv H2. inv H2.
              apply get_root_word. constructor.
              ++ destruct (H6 0) as [x [xT [HNth [HMap HWT]]]]; simpl in*;
                try (zify; lia);
                try rewrite Z.add_0_r in *;
                eauto; 
              try (eapply step_implies_reduces;
                   eapply SAssign; eauto);
              try (eexists; eauto);
              intros; try congruence...
              apply simple_type_means_cast_same. easy. inv H2. inv H2. inv H2. inv H2. 
              apply get_root_word. constructor.
              ++ destruct (StructDef.find (elt:=fields) s D)eqn:Hmap.
                 inv H4. inv WT. inv H4.
              ++ inv WT.
              ++ inv WT.
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
    inv Hewf.
    inv HHwt. rename H4 into Y1. rename H5 into Y2.
    apply (IH1 Y1) in H2. 2 : { easy. }
    destruct H2 as [ HVal1 | [ HRed1 | [| HUnchk1 ] ] ]; idtac...
    + (* Case: e1 is a value *)
      inv HVal1 as [ n1' t1' WTt1' Ht1' ].
      (* Invoke IH on e2 *)
      apply (IH2 Y2) in H3. 2 : { easy. }
      inv H3 as [ HVal2 | [ HRed2 | [| HUnchk2 ] ] ]; idtac...
      * (* Case: e2 is a value, so we can take a step *)
        inv HVal2 as [n2' t2' Wtt2' Ht2' ].
        {
            inv HTy1; eauto.
            inv Y1. 
            assert (Hsim := H0).
            apply H3 in H0. clear H3.
            match goal with
            | [ H : well_typed_lit _ _ _ _ _ _ |- _ ] => inv H
            end...
            + left.
              inv Hsim. inv H3.

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
              inv Hsim. inv H4.

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
                        eapply step_implies_reduces.
                        eapply (SAssign); eauto.
                        apply (simple_type_means_cast_same t st) in H5.
                        destruct (H6 0). unfold allocate_meta in H3.
                        inv H3. 
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
                        rewrite Z.add_0_r in H2.
                        destruct H2 as [? [? [? ?]]].
                        assert (Heap.find n1' H = Some (x, x0)) by (eapply Heap.find_1; assumption).
                        eapply HeapProp.F.in_find_iff. 
                        rewrite H8. easy.
                        constructor. constructor. easy. easy. 
                        apply (simple_type_means_cast_same t st) in H5. apply H5.
                        intros l1 h1 t1 Heq; inv Heq; zify.
                        lia.
                        intros. inv H2.
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
    inv Hewf.
    inv HHwt. rename H4 into Y1. rename H5 into Y2.
    apply (IH1 Y1) in H2. 2 : { easy. }
    destruct H2 as [ HVal1 | [ HRed1 | [| HUnchk1 ] ] ]; idtac...
    + (* Case: e1 is a value *)
      inv HVal1 as [ n1' t1' WTt1' Ht1' ].
      (* Invoke IH on e2 *)
      apply (IH2 Y2) in H3. 2 : { easy. }
      inv H3 as [ HVal2 | [ HRed2 | [| HUnchk2 ] ] ]; idtac...
      * (* Case: e2 is a value, so we can take a step *)
        inv HVal2 as [n2' t2' Wtt2' Ht2' ].
        {
            inv HTy1; eauto.
            inv Y1.
            assert (Hsim := H0).
            apply (H3) in H0. clear H3.
            match goal with
            | [ H : well_typed_lit _ _ _ _ _ _ |- _ ] => inv H
            end...
            + left.
              inv Hsim. inv H3.

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
              inv Hsim. inv H4.

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
                        eapply step_implies_reduces.
                        eapply SAssign; eauto.
                        apply (simple_type_means_cast_same t st) in H5.
                        destruct (H6 0). unfold allocate_meta in H3.
                        inv H3. 
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
                        rewrite Z.add_0_r in H2.
                        destruct H2 as [? [? [? ?]]].
                        assert (Heap.find n1' H = Some (x, x0)) by (eapply Heap.find_1; assumption).
                        eapply HeapProp.F.in_find_iff. 
                        rewrite H8. easy.
                        constructor. constructor. easy. easy. 
                        apply (simple_type_means_cast_same t st) in H5. apply H5. 
                        intros l1 h1 t1 Heq; inv Heq; zify; lia.
                        intros l1 h1 t1 Heq; inv Heq; zify; lia. 
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
    inv Hewf.
    inv H2.
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
    inv HHwt. inv H2. rename H6 into Y1. rename H7 into Y2. rename H8 into Y3. 
    apply (IH1 Y2) in H4. 2 : { easy. }
    destruct H4 as [ HVal1 | [ HRed1 | [| HUnchk1 ] ] ]; idtac...
    + (* Case: e1 is a value *)
      inv HVal1.
      (* Invoke IH on e2 *)
      apply (IH2 Y3) in H5. 2 : { easy. }
      destruct H5 as [ HVal2 | [ HRed2 | [| HUnchk2 ] ] ]; idtac...
      * inv HVal2.
        ctx (EAssign (EPlus (ELit n t0) (ELit n0 t1)) e3) 
                  (in_hole (EPlus (ELit n t0) (ELit n0 t1)) (CAssignL CHole e3)).
        inv HTy1.
        inv HTy2.
        inv Y2.
        assert (Hsim := H2).
        apply H8 in H2. clear H8.
        inv Hsim. inv H8.
        inv Y3.
        assert (simple_type TNat). constructor.
        apply H8 in H7. clear H8.
        {
          apply (IH3 Y1) in H3. 2 : { easy. }
          inv H2; inv H7; (eauto 20 with Progress); 
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
                eauto.
              * eapply RSHaltNull. eapply SPlusNull. lia.
                unfold is_array_ptr. easy. eauto.
          -  destruct (Z_gt_dec n 0); rewrite HCtx; left; do 4 eexists.
              * eapply RSExp. eapply SPlusChecked. lia.
                unfold is_array_ptr. easy. 
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
    inv HHwt. inv H2. rename H6 into Y1. rename H7 into Y2. rename H8 into Y3. 
    apply (IH1 Y2) in H4. 2 : { easy. }
    destruct H4 as [ HVal1 | [ HRed1 | [| HUnchk1 ] ] ]; idtac...
    + (* Case: e1 is a value *)
      inv HVal1.
      (* Invoke IH on e2 *)
      apply (IH2 Y3) in H5. 2 : { easy. }
      destruct H5 as [ HVal2 | [ HRed2 | [| HUnchk2 ] ] ]; idtac...
      * inv HVal2.
        ctx (EAssign (EPlus (ELit n t0) (ELit n0 t1)) e3) 
                  (in_hole (EPlus (ELit n t0) (ELit n0 t1)) (CAssignL CHole e3)).
        inv HTy1.
        inv HTy2.
        inv Y2.
        assert (Hsim := H2).
        apply H8 in H2. clear H8.
        inv Hsim. inv H8.
        inv Y3.
        assert (simple_type TNat). constructor.
        apply H8 in H7. clear H8.
        {
          apply (IH3 Y1) in H3. 2 : { easy. }
          inv H2; inv H7; (eauto 20 with Progress); 
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
                eauto.
              * eapply RSHaltNull. eapply SPlusNull. lia.
                unfold is_array_ptr. easy. eauto.
          -  destruct (Z_gt_dec n 0); rewrite HCtx; left; do 4 eexists.
              * eapply RSExp. eapply SPlusChecked. lia.
                unfold is_array_ptr. easy. 
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
   - inversion HEnv.
Qed.
*)
(* Define the property of a stack. *)
Definition stack_wt D (S:stack) := 
    forall x v t, Stack.MapsTo x (v,t) S -> word_type t /\ type_wf D t /\ simple_type t.

Definition env_wt D (env : env) :=
    forall x t, Env.MapsTo x t env -> word_type t /\ type_wf D t /\ well_type_bound_in env t.

(*
Lemma stack_simple_aux : forall D S x, stack_wf D (add_nt_one S x) -> stack_wf D S.
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
  apply H with (x:= x0) (v:=v).  easy.
  apply H with (x:= x0) (v:=v).  easy.
  apply H with (x:= x0) (v:=v).  easy.
  apply H with (x:= x0) (v:=v).  easy.
  apply H with (x:= x0) (v:=v).  easy.
Qed.
*)

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

Lemma stack_simple_eval_arg : forall s e n t t',
              eval_arg s e t (ELit n t') -> simple_type t'.
Proof.
  intros. inv H.
  apply cast_means_simple_type with (s := s) (t := t). easy.
  apply cast_means_simple_type with (s := s) (t := t). easy.
Qed.

Lemma subst_type_word_type : forall AS t, word_type t -> word_type (subst_type AS t).
Proof.
 intros. induction t. simpl. easy.
 simpl. constructor. simpl. easy.
 inv H.
 inv H.
Qed.

Lemma subst_type_type_wf : forall D AS t, type_wf D t -> type_wf D (subst_type AS t).
Proof.
 intros. induction t. simpl. easy.
 simpl. constructor. apply IHt. inv H. easy.
 simpl.  easy.
 simpl. constructor. inv H. apply subst_type_word_type. easy.
 apply IHt. inv H. easy.
 simpl. constructor. inv H. apply subst_type_word_type. easy.
 apply IHt. inv H. easy.
Qed.

Lemma stack_simple_eval_el : forall D AS s tvl el s',
              stack_wt D s -> (forall x t, In (x,t) tvl -> word_type t /\ type_wf D t) ->
               eval_el AS s tvl el s' -> stack_wt D s'.
Proof.
  intros. induction H1. easy.
  apply stack_simple_eval_arg in H1 as eq1.
  assert (stack_wt D s').
  apply IHeval_el; try easy.
  intros.
  specialize (H0 x0 t0).
  apply H0. simpl. right. easy.
  unfold stack_wt.
  intros.
  destruct (Nat.eq_dec x0 x).
  subst.
  apply Stack.mapsto_add1 in H4. inv H4.
  inv H1.
  specialize (H0 x t).
  assert (In (x, t) ((x, t) :: tvl)). simpl.  left. easy.
  apply H0 in H1.
  split.
  apply cast_word_type with (s := s) (t := subst_type AS t). easy.
  apply subst_type_word_type. easy.
  split.
  apply cast_type_wf with (s := s) (t := subst_type AS t). easy.
  apply subst_type_type_wf. easy. easy.
  specialize (H0 x t).
  assert (In (x, t) ((x, t) :: tvl)). simpl.  left. easy.
  apply H0 in H1.
  split.
  apply cast_word_type with (s := s) (t := subst_type AS t). easy.
  apply subst_type_word_type. easy.
  split.
  apply cast_type_wf with (s := s) (t := subst_type AS t). easy.
  apply subst_type_type_wf. easy. easy.
  apply Stack.add_3 in H4.
  apply H3 in H4. easy. lia.
Qed.

Lemma gen_arg_env_good : forall tvl enva, exists env, gen_arg_env enva tvl env.
Proof.
 intros.
 induction tvl. exists enva. subst. constructor.
 destruct IHtvl.
 destruct a.
 exists (Env.add v t x).
 constructor. easy.
Qed.

Lemma sub_domain_grows : forall tvl es env env' s s' AS,
      gen_arg_env env tvl env' -> eval_el AS s tvl es s'
    -> sub_domain env s -> sub_domain env' s'.
Proof.
  induction tvl. intros.
  inv H. inv H0. easy.
  intros. inv H. inv H0.
  apply sub_domain_grow.
  apply IHtvl with (es := es0) (s := s) (env0 := env0) (AS := AS); try easy.
Qed.


Lemma stack_simple_prop : forall D env S H S' H' e e',
         sub_domain env S ->
         fun_wf D fenv S' H' -> expr_wf D fenv e -> stack_wt D S ->
            step D (fenv env) S H e S' H' (RExpr e') -> stack_wt D S'.
Proof.
  intros.
  induction H4; try easy.
  unfold stack_wt in *.
  intros.
  unfold change_strlen_stack in *.
  destruct (n' <=? h).
  apply (H3 x0 v t0). assumption.
  destruct (Nat.eq_dec x x0). subst.
  apply Stack.mapsto_add1 in H7. inv H7.
  apply H3 in H4. inv H4. constructor.
  inv H7. constructor.
  inv H8. inv H4. split.
  constructor. inv H10. constructor. easy. easy.
  inv H9. inv H8. constructor. constructor. easy.
  apply Stack.add_3 in H7.
  apply H3 in H7. easy. easy.
  apply stack_simple_eval_el with (D := D) in H6. easy. easy.
  intros.
  unfold fun_wf in *.
  specialize (gen_arg_env_good tvl env0) as X1.
  destruct X1.
  specialize (H1 env0 x1 x tvl t e m H4 H9).
  specialize (sub_domain_grows tvl el env0 x1 s s' AS H9 H6 H0) as eq1.
  destruct H1.
  destruct (H1 x0 t0 H8). easy.
  unfold stack_wt. intros.
  destruct (Nat.eq_dec x x0). subst.
  apply Stack.mapsto_add1 in H5. inv H5.
  inv H2. inv H7.
  split.
  apply cast_word_type with (s := s) (t := t); try easy.
  split.
  apply cast_type_wf with (s := s) (t := t); try easy.
  apply cast_means_simple_type with (s := s) (t := t). easy.
  apply Stack.add_3 in H5.
  apply H3 in H5. easy. easy.
  inv H2. unfold simple_option in *.
  unfold stack_wt in *. intros.
  destruct (Nat.eq_dec x x0). subst.
  apply Stack.mapsto_add1 in H2. inv H2. easy.
  apply Stack.add_3 in H2.
  apply H3 in H2. easy. easy.
  unfold stack_wt in *.
  intros.
  apply Stack.remove_3 in H4.
  apply H3 in H4. easy.
  unfold stack_wt.
  intros. unfold add_nt_one in *.
  destruct (Stack.find (elt:=Z * type) x s) eqn:eq1. destruct p.
  destruct t2. inv H2.
  apply H3 in H8. easy.
  destruct t2.
  apply H3 in H8. easy.
  apply H3 in H8. easy.
  apply H3 in H8. easy.
  apply H3 in H8. easy.
  destruct b0.
  apply Stack.find_2 in eq1.
  destruct (Nat.eq_dec x x0). subst.
  apply Stack.mapsto_add1 in H8. inv H8.
  apply H3 in eq1.
  destruct eq1 as [X1 [X2 X3]].
  split. constructor.
  split. constructor. inv X2. inv H9. constructor. easy. easy.
  constructor. inv X3. inv H9. constructor. easy.
  apply Stack.add_3 in H8.
  apply H3 in H8. easy. easy.
  apply H3 in H8. easy.
  apply H3 in H8. easy.
  apply H3 in H8. easy.
  apply H3 in H8. easy.
  apply H3 in H8. easy.
Qed.

Lemma subtype_type_wf : forall D Q t t', subtype D Q t t' -> type_wf D t -> type_wf D t'.
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

(*
Lemma simple_type_var_fresh : forall x t, simple_type t -> var_fresh_type x t.
Proof.
  intros. 
  induction t.
  constructor.
  constructor.
  apply IHt. inv H. assumption.
  constructor.
  inv H. constructor. constructor. constructor.
  apply IHt. assumption.
  inv H. constructor. constructor. constructor.
  apply IHt. assumption.
Qed.

Lemma step_exp_fresh : forall D F cx S H e cx' S' H' e',
        stack_simple S ->
        step D F cx S H e cx' S' H' (RExpr e') -> var_fresh cx e -> var_fresh cx' e'.
Proof.
intros.
remember (RExpr e') as ea.
induction H1; eauto.
inv Heqea.
constructor.
apply Stack.find_2 in H1.
apply H0 in H1.
apply simple_type_var_fresh. assumption.
inv Heqea. constructor. constructor.
inv Heqea.
Qed.
*)

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


(* ... for Preservation *)
(*
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
*)

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
  specialize (@Env.mapsto_equal type x TNat env0 env2 H0 H) as eq1.
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

Lemma equiv_env_warg: forall D Q H env1 env2 e t,
    Env.Equal env1 env2 -> 
     well_typed_arg D Q H env1 e t -> 
     well_typed_arg D Q H env2 e t.
Proof.
  intros. generalize dependent env2.
  induction H1; eauto 20.
  intros. eapply ArgLit. easy. easy. easy.
  intros. apply ArgVar with (t' := t').
  apply Env.mapsto_equal with (s1 := env1); try easy.
  eapply equiv_env_well_bound_type. apply H3. apply H1. easy.
Qed.


Lemma equiv_env_wargs: forall D Q H AS env1 env2 es tvl,
    Env.Equal env1 env2 -> 
     @well_typed_args D Q H env1 AS es tvl -> 
     @well_typed_args D Q H env2 AS es tvl.
Proof.
  intros. generalize dependent env2.
  induction H1; eauto 20.
  intros. apply args_empty.
  intros. eapply args_many.
  eapply equiv_env_warg. apply H2. assumption.
  apply IHwell_typed_args. easy.
Qed.

(*
Lemma equiv_env_wt : forall D F S H Q env1 env2 m e t,
    Env.Equal env1 env2 ->
    @well_typed D F S H env1 Q m e t ->
    @well_typed D F S H env2 Q m e t.
Proof.
  intros.
  generalize dependent env2.
  induction H1; eauto 20.
  - intros.
    apply TyVar.
    apply Env.mapsto_equal with (s1 := env0); try easy.
  - intros. 
    eapply TyCall.
    apply H0. easy.
    eapply equiv_env_wargs. apply H3.
    assumption.
  - intros. 
    apply (TyStrlen env2 Q m x h l t).
    apply Env.mapsto_equal with (s1 := env0); try easy.
  - intros.
    apply (TyLetStrlen env2 Q m x y e l h t).
    apply Env.mapsto_equal with (s1 := env0); try easy.
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
*)
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

Definition heap_wt_all (D : structdef) (H:heap) := forall x n t, Heap.MapsTo x (n,t) H
            -> word_type t /\ type_wf D t /\ simple_type t.

Definition stack_consistent_grow (S S' : stack) (env : env) := 
       forall x v t, Env.In x env -> sub_domain env S -> Stack.MapsTo x (v,t) S -> Stack.MapsTo x (v,t) S'.

Definition stack_wf D Q H env s :=
    (forall x t,
         Env.MapsTo x t env ->
         exists v t' t'',
           cast_type_bound s t t' /\
           subtype D Q t'' t' /\
            Stack.MapsTo x (v, t'') s /\
            @well_typed_lit D Q H empty_scope v t'').

(*
Inductive stack_wf D Q H : env -> stack -> Prop :=
  | WFS_Stack : forall env s,
     (forall x t,
         Env.MapsTo x t env ->
         exists v t' t'',
           cast_type_bound s t t' /\
           subtype D Q t'' t' /\
            Stack.MapsTo x (v, t'') s /\
            @well_typed_lit D H empty_scope v t'')
   /\ (forall x v t,
             Stack.MapsTo x (v, t) s -> 
                   @well_typed_lit D H empty_scope v t    
          -> exists t' t'',
                @Env.MapsTo type x t' env /\ cast_type_bound s t' t''
                   /\ subtype D Q t t'')
 ->
     stack_wf D Q H env s.
*)
Lemma values_are_nf : forall D F H s e,
    value D e ->
    ~ exists  m s' H' r, @reduce D F s H e m s' H' r.
Proof.
  intros D F H s e Hv contra.
  inv Hv.
  destruct contra as [m [ s' [ H' [ r contra ] ] ] ].
  inv contra; destruct E; inversion H4; simpl in *; subst; try congruence.
  inv H5. inv H5. inv H5.
Qed.

Lemma lit_are_nf : forall D F H s n t,
    ~ exists H'  s' m r, @reduce D F s H (ELit n t) m s' H' r.
Proof.
  intros D F s H n t contra.
  destruct contra as [H' [ s' [ m [ r contra ] ] ] ].
  inv contra; destruct E; inversion H2; simpl in *; subst; try congruence.
Qed.

(*
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


(* allocation preservation. *)
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

Lemma subtype_well_type : forall D H env t t' n,
@well_typed_lit D H env n t ->
subtype D t t' ->
@well_typed_lit D H env n t'.
Proof.
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

    * inv H1. eapply TyLitC; eauto.
     
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
      + inv H0. 
    * clear IHw. inv H0.
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
               { eapply scope_replacement; eauto. } 
Qed.

(* If a term is typed checked, then its returned expression has a word type. *)
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

   
Inductive env_consistent : env -> env -> Prop :=
  |Env_refl : forall e,
      env_consistent e e
  |Env_add : forall e x t,
      ~ Env.In x e ->
      env_consistent (Env.add x t e) e.

Definition ty_ssa_stack (S:stack) (e:expression) 
            := exists l, (forall x,  Stack.In x S -> In x l) /\ (exists l', ty_ssa l e l').

Definition stack_grow (D: structdef) (S S' : stack) :=
     (forall x v t, Stack.MapsTo x (v,t) S
              -> (exists t', (subtype D t' t) /\ Stack.MapsTo x (v,t') S')).


Lemma stack_grow_prop : forall D F S H S' H' e e', 
           ty_ssa_stack S e
          -> step D F S H e S' H' (RExpr e') -> stack_grow D S S'.
Proof.
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
Qed.

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
Qed.


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
  - auto.
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
  specialize (subtype_ntarray D x1 m l' h' t'0 H4) as eq3.
  destruct eq3.  destruct H1. subst.
  apply subtype_simple_left in H4.
  eapply TyStrlen.
  apply (simple_type_well_bound env') in H4.
  apply H4.
  apply H5. assumption.
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
  left. eapply TyIf.
  apply H1. eauto.
  apply H5. apply H6. apply H3.
  assumption.
  destruct H6. destruct H6. destruct H6.
  destruct H7.
Qed.


Lemma well_typed_subtype : forall D F S H env m e t x t1 t2 t3,
    @well_typed D F S H (Env.add x t1 env) m e t ->
     cast_type_bound S t1 t2 ->
     subtype D t3 t2 ->
    (exists env', env_match D S env env' /\
    (@well_typed D F S H (Env.add x t3 env') m e t \/ 
       (exists t' t'' , cast_type_bound S t t'
          /\ subtype D t'' t' /\ @well_typed D F S H (Env.add x t3 env') m e t''))).
Proof.
  intros.
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
  left. eapply TyIf.
  apply H1. eauto.
  apply H5. apply H6. apply H3.
  assumption.
  destruct H6. destruct H6. destruct H6.
  destruct H7.
Qed.

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
*)

Lemma subtype_ptr : forall D Q m t t', subtype D Q (TPtr m t) t' -> exists ta, t' = TPtr m ta.
Proof.
  intros. inv H. exists t. easy.
  exists (TArray l h t). easy.
  exists t0. easy.
  exists t0. easy.
  exists (TArray l' h' t0). easy.
  exists (TArray l' h' t0). easy.
  exists (TNTArray l' h' t0). easy.
  exists TNat. easy.
  exists (TArray l h TNat). easy.
Qed.

Lemma cast_ptr_left : forall s t1 m t2, cast_type_bound s t1 (TPtr m t2) -> exists ta, t1 = (TPtr m ta).
Proof.
  intros. inv H. exists t. easy.
Qed.

Lemma gen_arg_env_has_old : forall tvl env env0, gen_arg_env env tvl env0
          -> (forall x, Env.In x env -> Env.In x env0).
Proof.
  induction tvl.
  intros;simpl.
  inv H. easy.
  intros;simpl. inv H.
  apply IHtvl with (x := x) in H5.
  destruct H5.
  destruct (Nat.eq_dec x x0).
  subst.
  exists t.
  apply Env.add_1. easy.
  exists x1.
  apply Env.add_2. lia.
  easy.
  easy.
Qed.

Lemma gen_arg_env_has_all : forall tvl env env0, gen_arg_env env tvl env0
          -> (forall x t, Env.MapsTo x t env0 -> Env.MapsTo x t env \/ In (x,t) tvl).
Proof.
  intros. induction H. left. easy.
  destruct (Nat.eq_dec x x0). subst.
  apply Env.mapsto_add1 in H0. subst.
  right. simpl. left. easy.
  apply Env.add_3 in H0.
  apply IHgen_arg_env in H0. destruct H0. left. easy.
  right. simpl. right. easy. lia.
Qed.

Lemma stack_consist_trans : forall S S' env tvl es AS,
    sub_domain env S ->
    (forall a, In a tvl -> ~ Env.In (fst a) env) ->
    length tvl = length es ->
    eval_el AS S tvl es S' -> stack_consistent_grow S S' env.
Proof.
  intros. induction H2.
  unfold stack_consistent_grow.
  intros. easy.
  unfold stack_consistent_grow.
  intros.
  assert ((forall a : Env.key * type,
             In a tvl -> ~ Env.In (elt:=type) (fst a) env0)).
  intros.
  apply H0. simpl. right. easy.
  assert (length tvl = length es). simpl in *.
  inv H1. easy.
  specialize (IHeval_el H5 H7 H8).
  unfold stack_consistent_grow in *.
  specialize (IHeval_el x0 v t0 H4 H5 H6).
  destruct (Nat.eq_dec x0 x). subst.
  assert (In (x,t) ((x, t) :: tvl)). simpl. left. easy.
  apply H0 in H9.
  simpl in *. contradiction.
  apply Stack.add_2. lia. easy.
Qed.

Lemma well_typed_arg_same_length : forall D Q H env AS es tvl,
         @well_typed_args D Q H env AS es tvl -> length es = length tvl.
Proof.
  intros. induction H0. easy.
  simpl. rewrite IHwell_typed_args. easy.
Qed.

Lemma gen_arg_env_grow_1 : forall tvl env env', gen_arg_env env tvl env' -> 
      (forall a, In a tvl -> ~ Env.In (fst a) env) ->
      (forall x t, Env.MapsTo x t env -> Env.MapsTo x t env').
Proof.
  induction tvl; intros;simpl.
  inv H. easy.
  inv H.
  specialize (IHtvl env0 env'0 H6).
  assert ((forall a : var * type,
         In a tvl -> ~ Env.In (elt:=type) (fst a) env0)).
  intros.
  apply H0. simpl. right. easy.
  specialize (IHtvl H).
  apply IHtvl in H1 as eq1.
  destruct (Nat.eq_dec x x0).
  subst.
  specialize (H0 (x0,t0)).
  assert (In (x0, t0) ((x0, t0) :: tvl)).
  simpl. left. easy.
  apply H0 in H2.
  simpl in *.
  assert (Env.In (elt:=type) x0 env0).
  exists t. easy. contradiction.
  apply Env.add_2. lia.
  easy.
Qed.

Lemma gen_arg_env_grow_2 : forall tvl env env', gen_arg_env env tvl env' -> 
      (forall a, In a tvl -> ~ Env.In (fst a) env) ->
      (forall x t, Env.MapsTo x t env' -> Env.MapsTo x t env \/ In (x,t) tvl).
Proof.
  induction tvl; intros;simpl.
  inv H. left. easy.
  inv H.
  destruct (Nat.eq_dec x x0). subst.
  apply Env.mapsto_add1 in H1. subst.
  right. left. easy.
  apply Env.add_3 in H1; try lia.
  assert ((forall a : var * type,
         In a tvl -> ~ Env.In (elt:=type) (fst a) env0)).
  intros.
  apply H0. simpl. right. easy.
  specialize (IHtvl env0 env'0 H6 H x t H1).
  destruct IHtvl. left. easy.
  right. right. easy.
Qed.

Lemma stack_grow_cast_same : forall env S S' b b', well_bound_in env b ->
        sub_domain env S -> stack_consistent_grow S S' env ->
              cast_bound S b = Some b' -> cast_bound S' b = Some b'.
Proof.
  intros. unfold cast_bound in *.
  destruct b. assumption.
  destruct (Stack.find (elt:=Z * type) v S) eqn:eq1. destruct p.
  unfold stack_consistent_grow in *.
  apply Stack.find_2 in eq1. inv H.
  apply H1 in eq1; try easy.
  destruct (Stack.find (elt:=Z * type) v S') eqn:eq2.
  destruct p.
  apply Stack.find_2 in eq2.
  apply (@Stack.mapsto_always_same (Z * type) v (z0,t)) in eq2; try easy.
  inv eq2. easy.
  apply Stack.find_1 in eq1.
  rewrite eq1 in eq2. easy.
  exists TNat. easy. inv H2.
Qed.

Lemma stack_grow_cast_type_same : forall env S S' t t', well_type_bound_in env t ->
        sub_domain env S -> stack_consistent_grow S S' env ->
              cast_type_bound S t t' -> cast_type_bound S' t t'.
Proof.
  intros.
  induction H2. constructor.
  constructor.
  apply IHcast_type_bound. inv H. easy.
  inv H.
  constructor.
  apply (stack_grow_cast_same env0 S); try easy.
  apply (stack_grow_cast_same env0 S); try easy.
  apply IHcast_type_bound. easy.
  inv H.
  constructor.
  apply (stack_grow_cast_same env0 S); try easy.
  apply (stack_grow_cast_same env0 S); try easy.
  apply IHcast_type_bound. easy.
  apply cast_type_bound_struct.
Qed.

Lemma nth_error_empty_none {A:Type}: forall n, @nth_error A [] n = None.
Proof.
  induction n; intros;simpl.
  easy. easy.
Qed.

Lemma cast_subtype_same : forall t1 D Q S t1' t2 t2', subtype D Q t1 t2 -> 
    cast_type_bound S t1 t1' -> cast_type_bound S t2 t2' ->
    (forall x n ta, Theta.MapsTo x GeZero Q -> Stack.MapsTo x (n,ta) S -> 0 <= n) ->
    subtype D Q t1' t2'.
Proof.
  induction t1; intros;simpl.
  inv H0. inv H. inv H1. constructor.
  inv H0.
  inv H. inv H1.
  specialize (cast_type_bound_same S t1 t' t'0 H6 H4) as eq3. subst.
  constructor. inv H5. inv H8.
  inv H1. inv H8. unfold cast_bound in *. inv H7. inv H10.
  specialize (cast_type_bound_same S t1 t' t'1 H6 H11) as eq3. subst.
  apply SubTyBot.
  apply cast_word_type in H6; try easy. constructor. easy. constructor. easy.
  inv H8. inv H1. inv H9. unfold cast_bound in *.
  destruct (Stack.find (elt:=Z * type) x S) eqn:eq1. destruct p. inv H8. inv H11.
  specialize (cast_type_bound_same S t1 t' t'1 H6 H12) as eq3. subst.
  apply SubTyBot.
  apply cast_word_type in H6; try easy. constructor.
  apply Stack.find_2 in eq1.
  apply H2 in eq1; try easy. lia. constructor. easy.
  inv H8.
Admitted.

Definition bound_eval (S:stack) (b:bound) :=
  match b with Num n => Some n
           | Var x n => match Stack.find x S with Some (m,t) => Some (m + n)
                                               | None => None
                        end
  end.


Lemma well_bound_var_in_as : forall AS x z env, 
     ~ Env.In x env ->
      well_bound_in env (subst_bounds (Var x z) AS) ->
     (exists b, In (x,b) AS).
Proof.
  induction AS; intros; simpl in *.
  inv H0. assert (Env.In x env0).
  exists TNat. easy. contradiction.
  destruct a.
  destruct (var_eq_dec x v). subst.
  exists b. left. easy.
  specialize (IHAS x z env0 H H0). destruct IHAS. 
  exists x0. right. easy.
Qed.


Lemma cast_bound_in_env_same : forall AS S env0 v z, 
    sub_domain env0 S ->
            (forall a, In a AS -> ~ Env.In (fst a) env0) -> Env.In v env0 ->
              cast_bound S (subst_bounds (Var v z) AS) = cast_bound S (Var v z).
Proof.
  induction AS; intros;simpl.
  unfold sub_domain in *.
  specialize (H v H1). destruct H.
  apply Stack.find_1 in H. rewrite H. easy.
  destruct a.
  destruct (var_eq_dec v k). subst.
  assert (In (k,b) ((k, b) :: AS)).
  simpl. left. easy.
  apply H0 in H2. simpl in *. contradiction.
  assert ((forall a : Env.key * bound,
        In a AS -> ~ Env.In (elt:=type) (fst a) env0)).
  intros. apply H0. simpl. right. easy.
  rewrite IHAS with (env0 := env0); try easy.
Qed.

Lemma nth_no_appear {A B:Type} : forall x v AS,
     (forall n n' (a b: A * B), n <> n' -> nth_error ((x,v)::AS) n = Some a -> nth_error ((x,v)::AS) n' = Some b -> fst a <> fst b) ->
     (forall y w, In (y,w) AS -> x <> y).
Proof.
  intros.
  apply In_nth_error in H0. destruct H0.
  specialize (H Nat.zero (S x0) (x,v) (y,w)).
  assert (Nat.zero <> S x0).
  intros R. easy.
  apply H in H1; try easy.
Qed.

Lemma subst_type_no_effect: forall AS v z,
     (forall a, In a AS -> fst a <> v) -> subst_bounds (Var v z) AS = Var v z.
Proof.
  induction AS;intros;simpl.
  easy.
  destruct a.
  specialize (H (v0,b)) as eq1.
  assert (In (v0, b) ((v0, b) :: AS)). simpl. left. easy.
  apply eq1 in H0.
  destruct (var_eq_dec v v0). subst. easy.
  assert (forall a : var * bound, In a (AS) -> fst a <> v).
  intros. apply H. simpl. right. easy.
  apply IHAS with (z := z) in H1. easy.
Qed.

Lemma subst_bounds_only_one: forall AS env v b z, In (v,b) AS -> 
    (forall a, In a AS -> ~ Env.In (fst a) env) ->
     (forall x b, In (x,b) AS -> (match b with Num v => True | Var y v => @Env.In (type) y env end)) ->
    (forall n n' a b, n <> n' -> nth_error AS n = Some a -> nth_error AS n' = Some b -> fst a <> fst b) ->
       subst_bounds (Var v z) AS = subst_bound (Var v z) v b.
Proof.
  induction AS;intros.
  easy. simpl.
  destruct a. simpl in H. destruct H. inv H.
  destruct (var_eq_dec v v).
  destruct b.
   assert (forall AS z, subst_bounds (Num z) AS = Num z).
   {
    intros. induction AS0. simpl. easy.
    simpl. destruct a. easy.
   }
  rewrite H. easy.
  assert (forall a, In a ((v, Var v0 z0) :: AS) -> fst a <> v0).
  {
    intros. simpl in *. intros R. destruct H. destruct a. inv H.
    simpl in *.
    specialize (H0 (k,Var k z0)).
    specialize (H1 k (Var k z0)).
    assert ((k, Var k z0) = (k, Var k z0) \/ In (k, Var k z0) AS).
    left. easy. apply H0 in H as eq1. apply H1 in H. simpl in *. contradiction.
    specialize (H0 a).
    assert ((v, Var v0 z0) = a \/ In a AS). right. easy.
    apply H0 in H3.
    specialize (H1 v (Var v0 z0)).
    assert ((v, Var v0 z0) = (v, Var v0 z0) \/ In (v, Var v0 z0) AS). left. easy.
    apply H1 in H4. destruct a. simpl in *. subst. contradiction.
  }
  rewrite subst_type_no_effect; try easy.
  intros. apply H. simpl. right. easy. easy.
  destruct (var_eq_dec v k). subst.
  specialize (nth_no_appear k b0 AS H2) as eq1.
  apply eq1 in H. easy.
  specialize (IHAS env0 v b z H).
  assert ((forall a : Env.key * bound,
        In a AS -> ~ Env.In (elt:=type) (fst a) env0)).
  intros. apply H0. simpl. right. easy.
  assert ((forall (x : Env.key) (b : bound),
        In (x, b) AS ->
        match b with
        | Num _ => True
        | Var y _ => Env.In (elt:=type) y env0
        end)).
  intros. apply (H1 x). simpl. right. easy. 
  assert ((forall (n n' : nat) (a b : Env.key * bound),
        n <> n' ->
        nth_error AS n = Some a ->
        nth_error AS n' = Some b -> fst a <> fst b)).
  intros.
  specialize (H2 (S n0) (S n')).
  simpl in *.
  apply H2. lia. easy. easy.
  specialize (IHAS H3 H4 H5).
  rewrite IHAS.
  unfold subst_bound.
  easy.
Qed.


Lemma cast_as_same_bound : forall b S S' env AS b',
    sub_domain env S -> stack_consistent_grow S S' env ->
    well_bound_in env (subst_bounds b AS) ->
    (forall a, In a AS -> ~ Env.In (fst a) env) ->
     (forall x b, In (x,b) AS -> (match b with Num v => True | Var y v => Env.In y env end)) ->
     (forall a, In a AS -> Stack.In (fst a) S') ->
     (forall x b na ta, In (x,b) AS -> Stack.MapsTo x (na,ta) S' -> bound_eval S b = Some na) ->
    (forall n n' a b, n <> n' -> nth_error AS n = Some a -> nth_error AS n' = Some b -> fst a <> fst b) ->
      cast_bound S (subst_bounds b AS) = Some b' -> cast_bound S' b = Some b'.
Proof.
  intros. simpl in *. destruct b.
   assert (forall AS, subst_bounds (Num z) AS = Num z).
   {
    intros. induction AS0. simpl. easy.
    simpl. destruct a. easy.
   }
   rewrite H8 in H7. easy.
   specialize (Classical_Prop.classic (Env.In v env0)) as eq1.
   destruct eq1.
   rewrite cast_bound_in_env_same with (env0 := env0) in H7.
   unfold stack_consistent_grow in *.
   rewrite <- H7.
   unfold cast_bound.
   destruct (Stack.find (elt:=Z * type) v S) eqn:eq1. destruct p.
   apply Stack.find_2 in eq1.
   apply H0 in eq1; try easy.
   apply Stack.find_1 in eq1. rewrite eq1. easy.
   unfold sub_domain in *.
   apply H in H8.
   destruct H8. apply Stack.find_1 in H8. rewrite eq1 in H8. easy.
   easy. easy. easy.
   specialize (well_bound_var_in_as AS v z env0 H8 H1) as eq1.
   destruct eq1.
   rewrite <- H7.
   apply H4 in H9 as eq2.
   destruct eq2. simpl in *. destruct x0.
   apply H5 with (b := x) in H10 as eq3; try easy.
   unfold bound_eval in eq3.
   apply Stack.find_1 in H10.
   rewrite H10.
   rewrite subst_bounds_only_one with (env := env0) (b := x); try easy.
   unfold subst_bound.
   destruct (var_eq_dec v v).
   destruct x. inv eq3. easy.
   unfold cast_bound.
   destruct (Stack.find (elt:=Z * type) v0 S) eqn:eq1. destruct p. inv eq3.
   assert ((z + (z2 + z1)) = (z + z1 + z2)) by lia.
   rewrite H11. easy. inv eq3. easy.
Qed.

Lemma cast_as_same : forall t S S' env AS t',
    sub_domain env S -> stack_consistent_grow S S' env ->
     well_type_bound_in env (subst_type AS t) -> 
    (forall a, In a AS -> ~ Env.In (fst a) env) ->
     (forall x b, In (x,b) AS -> (match b with Num v => True | Var y v => Env.In y env end)) ->
     (forall a, In a AS -> Stack.In (fst a) S') ->
     (forall x b na ta, In (x,b) AS -> Stack.MapsTo x (na,ta) S' -> bound_eval S b = Some na) ->
    (forall n n' a b, n <> n' -> nth_error AS n = Some a -> nth_error AS n' = Some b -> fst a <> fst b) ->
     cast_type_bound S (subst_type AS t) t' ->
     cast_type_bound S' t t'.
Proof.
   induction t; intros; simpl.
   assert (forall AS, subst_type AS TNat = TNat).
   {
    intros. induction AS0. simpl. easy.
    simpl. easy.
   }
   rewrite H8 in H7. inv H7. constructor.
   simpl in *. 
   inv H7. constructor. apply IHt with (S := S) (env := env0) (AS := AS); try easy.
   inv H1. easy.
   assert (forall AS, subst_type AS (TStruct s)  = (TStruct s) ).
   {
    intros. induction AS0. simpl. easy.
    simpl. easy.
   }
   rewrite H8 in H7. inv H7. constructor.
   simpl in *. inv H1. inv H7.
   constructor.
   rewrite cast_as_same_bound with (S := S) (env := env0) (AS := AS) (b' := l'); try easy.
   rewrite cast_as_same_bound with (S := S) (env := env0) (AS := AS) (b' := h'); try easy.
   apply IHt with (S := S) (AS := AS) (env := env0); try easy.
   simpl in *. inv H1. inv H7.
   constructor.
   rewrite cast_as_same_bound with (S := S) (env := env0) (AS := AS) (b' := l'); try easy.
   rewrite cast_as_same_bound with (S := S) (env := env0) (AS := AS) (b' := h'); try easy.
   apply IHt with (S := S) (AS := AS) (env := env0); try easy.
Qed.


Lemma stack_wf_out : forall tvl es D Q H env AS S S',
     sub_domain env S -> stack_wt D S -> stack_wf D Q H env S ->
     env_wt D env ->
     (forall a, In a tvl -> ~ Env.In (fst a) env) ->
     (forall x n t ta, Env.MapsTo x t env -> Stack.MapsTo x (n,ta) S ->
           (exists t', cast_type_bound S t t' /\ subtype D Q ta t')) ->
     (forall x n ta, Theta.MapsTo x GeZero Q -> Stack.MapsTo x (n,ta) S -> 0 <= n) ->
     (forall n n' a b, n <> n' -> nth_error tvl n = Some a -> nth_error tvl n' = Some b -> fst a <> fst b) ->
     (forall e, In e es -> (exists n t, e = ELit n t
                 /\ word_type t /\ type_wf D t /\ simple_type t) \/ (exists y, e = EVar y)) ->
     @well_typed_args D Q H env AS es tvl ->
     eval_el AS S tvl es S' ->
       (forall x t, In (x,t) tvl ->
         exists v t',
           cast_type_bound S (subst_type AS t) t' /\
            Stack.MapsTo x (v,t') S' /\
            @well_typed_lit D Q H empty_scope v t').
Proof.
  intros.
  induction H10. inv H9. intros.
  inv H11.
  intros. inv H9.
  assert ((forall a : Env.key * type,
             In a tvl ->
             ~ Env.In (elt:=type) (fst a) env0)).
  intros. apply H4. simpl. right. easy.
  assert ((forall (n n' : nat) (a b : Env.key * type),
             n <> n' ->
             nth_error tvl n = Some a ->
             nth_error tvl n' = Some b -> fst a <> fst b)).
  intros.
  specialize (H7 (S n0) (S n') a b).
  simpl in H7. apply H7; try easy. lia.
  assert ((forall e : expression,
             In e es ->
             (exists (n : Z) (t : type),
                e = ELit n t /\ word_type t /\ type_wf D t /\ simple_type t) \/
             (exists y : var, e = EVar y))).
  intros. apply H8. simpl. right. easy.
  specialize (IHeval_el H0 H1 H2 H9 H5 H6 H13 H14 H21). clear H13. clear H14.
  simpl in H11. destruct H11. inv H11.
  inv H18. inv H10.
  exists n.
  apply simple_type_means_cast_same with (s := s) in H11 as eq1.
  exists (subst_type AS t).
  split. easy. 
  split.
  apply (cast_type_bound_same s (subst_type AS t) (subst_type AS t) t' eq1) in H19.
  rewrite H19. apply Stack.add_1. easy.
  apply subtype_well_type with (t := t'0); try easy.
  assert (In (ELit n t'0) (ELit n t'0 :: es)). simpl. left. easy.
  apply H8 in H10. destruct H10. destruct H10 as [na [ta [X1 [X2 [X3 X4]]]]].
  inv X1. apply subtype_type_wf in H14. easy. easy. destruct H10. inv H10.
  inv H10.
  assert (well_type_bound_in env0 t'0).
  apply H3 with (x := x0); easy.
  specialize (gen_cast_type_bound_same env0 s t'0 H10 H0) as eq1.
  destruct eq1.
  apply cast_means_simple_type in H15 as eq1.
  apply cast_means_simple_type in H22 as eq2.
  specialize (H5 x0 n t'0 t'1 H11 H20) as eq3.
  destruct eq3. destruct H16.
  specialize (cast_type_bound_same s t'0 x1 x2 H15 H16) as eq3. subst.
  unfold stack_wt in H1.
  specialize (cast_subtype_same t'0 D Q s x2 (subst_type AS t) t' H14 H15 H22 H6) as eq3.
  assert (word_type x2).
  apply cast_word_type in H15; try easy.
  specialize (H3 x0 t'0 H11). easy.
  inv H18. inv eq3. inv H17. inv H22. inv H15.
  exists n. exists TNat.
  split. easy.
  split. apply Stack.add_1. easy.  apply TyLitInt.
  specialize (subtype_trans D Q t'1 t' m w H17 eq3) as eq4.
  exists n. exists t'. split. easy.
  split. apply Stack.add_1. easy.
  unfold stack_wf in *.
  specialize (H2 x0 t'0 H11).
  destruct H2 as [v [ta [tb [X1 [X2 [X3 X4]]]]]].
  apply Stack.mapsto_always_same with (v1 := (n, t'1)) in X3 as eq6; try easy. inv eq6.
  apply H1 in X3. destruct X3 as [X3a [X3b X3c]].
  apply subtype_well_type with (t := tb); try easy.
  apply subtype_type_wf with (Q := Q) (t' := t')  in X3b. easy. easy.
  simpl in *.
  specialize (IHeval_el H11).
  destruct IHeval_el as [v [ta [X1 [X2 X3]]]].
  exists v. exists ta.
  split. easy. split.
  apply nth_no_appear with (y := x) (w := t) in H7.
  apply Stack.add_2. easy. easy.
  easy. easy.
Qed.


Lemma stack_wf_core : forall D Q H env S, stack_wf D Q H env S ->
    (forall x n t ta, Env.MapsTo x t env -> Stack.MapsTo x (n,ta) S ->
           (exists t', cast_type_bound S t t' /\ subtype D Q ta t')).
Proof.
  intros.
  unfold stack_wf in *.
  specialize (H0 x t H1).
  destruct H0 as [v [t' [t'' [X1 [X2 [X3 X4]]]]]].
  exists t'. split. easy.
  apply Stack.mapsto_always_same with (v1 := (v,t'')) in H2; try easy. inv H2.
  easy.
Qed.

Lemma well_type_args_well_bound : forall D Q H env AS es tvl,
   @well_typed_args D Q H env AS es tvl -> 
   (forall x t, In (x,t) tvl -> well_type_bound_in env (subst_type AS t)).
Proof.
  intros. induction H0.
  simpl in *. easy. simpl in *.
  destruct H1.
  inv H1. inv H0.
  apply simple_type_well_bound with (env := env0) in H1. easy.
  easy.
  apply IHwell_typed_args. easy.
Qed.

Lemma as_well_bound : forall AS D Q H env tvl es,
   @well_typed_args D Q H env AS es tvl -> 
     get_dept_map tvl es = Some AS -> 
    (forall x b, In (x,b) AS -> (match b with Num v => True | Var y v => Env.In y env end)).
Proof.
Admitted.

Lemma as_not_in_env : forall AS tvl es env,
     get_dept_map tvl es = Some AS -> length tvl = length es -> 
    (forall a, In a tvl -> ~ @Env.In type (fst a) env) -> (forall a, In a AS -> ~ @Env.In type (fst a) env).
Proof.
Admitted.

Lemma as_stack_in : forall AS tvl es S S',
     get_dept_map tvl es = Some AS -> eval_el AS S tvl es S' ->
    (forall a, In a AS -> Stack.In (fst a) S').
Proof.
Admitted.

Lemma as_stack_in_2 : forall AS tvl es S S',
     get_dept_map tvl es = Some AS -> eval_el AS S tvl es S' ->
    (forall a, In a AS -> Stack.In (fst a) S') -> 
(forall x b na ta, In (x,b) AS -> Stack.MapsTo x (na,ta) S' -> bound_eval S b = Some na).
Proof.
Admitted.

Lemma as_diff : forall AS tvl es,
     get_dept_map tvl es = Some AS -> length tvl = length es ->
   (forall n n' a b, n <> n' -> nth_error tvl n = Some a -> nth_error tvl n' = Some b -> fst a <> fst b) ->
   (forall n n' a b, n <> n' -> nth_error AS n = Some a -> nth_error AS n' = Some b -> fst a <> fst b).
Proof.
Admitted.


Definition theta_wt (Q:theta) (env:env) (S:stack) :=
     (forall x, Theta.In x Q -> Env.In x env)
  /\ (forall x n ta, Theta.MapsTo x GeZero Q -> Stack.MapsTo x (n,ta) S -> 0 <= n).



Lemma stack_wf_trans :
   forall D Q H env env' S S' AS tvl es,
   stack_wt D S -> sub_domain env S -> stack_wf D Q H env S -> env_wt D env ->
     (forall a, In a tvl -> ~ Env.In (fst a) env) ->
     (forall n n' a b, n <> n' -> nth_error tvl n = Some a -> nth_error tvl n' = Some b -> fst a <> fst b) ->
     (forall x t, Env.MapsTo x t env' -> Env.MapsTo x t env \/ In (x,t) tvl) ->
     (forall x n ta, Theta.MapsTo x GeZero Q -> Stack.MapsTo x (n,ta) S -> 0 <= n) ->
     (forall e, In e es -> (exists n t, e = ELit n t
                 /\ word_type t /\ type_wf D t /\ simple_type t) \/ (exists y, e = EVar y)) ->
     @well_typed_args D Q H env AS es tvl ->
     get_dept_map tvl es = Some AS ->
     eval_el AS S tvl es S' -> stack_wf D Q H env' S'.
Proof.
  intros.
  assert (length tvl = length es) as eq1.
  rewrite (well_typed_args_same_length D Q H env0 AS es tvl); try easy.
  specialize (stack_consist_trans S S' env0 tvl es AS H1 H4 eq1 H11) as eq2.
  specialize (stack_wf_core D Q H env0 S H2) as eq3.
  specialize (stack_wf_out tvl es D Q H env0 AS S S' H1 H0 H2 H3 H4 eq3 H7 H5 H8 H9 H11) as eq4.
  unfold stack_wf in *.
  intros.
  apply H6 in H12.
  destruct H12. apply H2 in H12 as eq5. destruct eq5 as [v [ta [tb [X1 [X2 [X3 X4]]]]]].
  exists v. exists ta. exists tb.
  split. apply stack_grow_cast_type_same with (env := env0) (S := S); try easy.
  unfold env_wt in *.
  apply H3 in H12. easy. split. easy. split.
  unfold stack_consistent_grow in *.
  apply eq2; try easy. exists t. easy. easy.
  apply eq4 in H12 as eq5.
  destruct eq5 as [v [ta [X1 [X2 X3]]]].
  exists v. exists ta. exists ta.
  split.
  apply cast_as_same with (S := S) (AS := AS) (env := env0); try easy.
  apply (well_type_args_well_bound D Q H env0 AS es tvl) with (x := x); try easy.
  intros.
  apply (as_not_in_env AS tvl es env0); try easy.
  intros.
  apply (as_well_bound AS D Q H env0 tvl es) with (x := x0); try easy.
  intros. 
  apply (as_stack_in AS tvl es S S'); try easy.
  intros.
  apply (as_stack_in_2 AS tvl es S S') with (x := x0) (ta := ta0); try easy.
  apply (as_stack_in AS tvl es S S'); try easy.
  intros. 
  apply (as_diff AS tvl es) with (n := n) (n' := n'); try easy.
  split. constructor. split. easy. easy.
Qed.

(*
Lemma stack_wf_trans: forall tvl D Q H AS es env s env' s',
     sub_domain env s -> eval_el AS s tvl es s' ->
     (forall x t, Env.MapsTo x t env -> well_type_bound_in env t) ->
     (forall x t, Env.MapsTo x t env -> Env.MapsTo x t env') -> 
     (forall x t, Env.MapsTo x t env' -> Env.MapsTo x t env \/ In (x,t) tvl) ->
     (forall x t, In (x,t) tvl -> well_type_bound_in env (subst_type AS t)) ->
     (forall a, In a tvl -> ~ Env.In (fst a) env) ->
    (forall n n' a b, n <> n' -> nth_error tvl n = Some a -> nth_error tvl n' = Some b -> fst a <> fst b) ->
     @well_typed_args D Q H env AS es tvl ->
     stack_wf D Q H env s -> stack_wf D Q H env' s'.
Proof.
  intros. 
  unfold stack_wf in *.
  intros.
  apply H4 in H10. destruct H10.
  apply H9 in H10 as eq1.
  destruct eq1 as [v [t' [t'' [X1 [X2 [X3 X4]]]]]].
  specialize (well_typed_arg_same_length D Q H env0 AS es tvl H8) as eq1.
  symmetry in eq1.
  specialize (stack_consist_trans s s' env0 tvl es AS H0 H6 eq1 H1) as eq2.
  apply stack_grow_cast_type_same with (env := env0) (S' := s') in X1 ; try easy.
  unfold stack_consistent_grow in *.
  specialize (eq2 x v t'').
  assert (Env.In x env0).
  exists t. easy.
  specialize (eq2 H11 H0 X3).
  exists v. exists t'. exists t''. easy.
  apply (H2 x). easy.
Admitted.
*)

Lemma theta_grow_type : forall D F S H env Q m e t,
  @well_typed D F S H env empty_theta m e t
   -> @well_typed D F S H env Q m e t.
Proof.
  intros. remember empty_theta as Q'. induction H0;subst;eauto.
  constructor.
Admitted.

Check List.find.

Definition tmem (l : list var) (x:var) := 
   match find (fun y => Nat.eqb x y) l with Some x => true | _ => false end.

Definition gen_rets_type (S:stack) (x:var) (ta:type) (e:expression) (t:type) :=
   match ta with TNat => 
     match e with ELit v t' => if tmem (get_tvars t) x then Some (subst_type [(x,Num v)] t) else Some t
                | EVar y => match Stack.find y S with None => None
                                  | Some (v,t') => 
                                 if tmem (get_tvars t) x then Some (subst_type [(x,Num v)] t) else Some t
                            end
                | _ => None
     end
             | _ => Some t
   end.

Inductive gen_rets_types (S:stack) : list (var * type) -> (list expression) -> type -> type -> Prop :=
   | rets_type_empty : forall t, gen_rets_types S [] [] t t
   | rets_type_many : forall x ta tvl e es t t' t'', gen_rets_types S tvl es t t' -> 
                gen_rets_type S x ta e t' = Some t'' ->
                gen_rets_types S ((x,ta)::tvl) (e::es) t t''.

Lemma tmem_in : forall l x, tmem l x = true <-> In x l.
Proof.
  intros. split. unfold tmem. intros.
  destruct (find (fun y : nat => (x =? y)%nat) l) eqn:eq1.
  apply find_some in eq1. destruct eq1.
  apply Nat.eqb_eq in H1. subst. easy.
  apply find_none with (x := x) in eq1.
  apply Nat.eqb_neq in eq1. easy. easy.
  intros. unfold tmem.
  destruct (find (fun y : nat => (x =? y)%nat) l) eqn:eq1.
  apply find_some in eq1. destruct eq1.
  apply Nat.eqb_eq in H1. subst. easy.
  apply find_none with (x := x) in eq1.
  apply Nat.eqb_neq in eq1. easy. easy.
Qed.

Lemma well_typed_type_nat : forall D F S H env Q m e t, 
         @well_typed D F S H env Q m e t -> expr_wf D F e -> (forall x, In x (get_tvars t) -> Env.MapsTo x TNat env).
Proof.
Admitted.

Lemma expr_wf_gen_rets : forall tvl es D F S AS e e',
     stack_wt D S -> 
     expr_wf D F e -> gen_rets AS S tvl es e e' ->
    (forall x t', In (x,t') tvl -> word_type t' /\ type_wf D t') ->
     expr_wf D F e'.
Proof.
  intros. induction H1. easy.
  specialize (H2 x t) as eq1.
  assert (In (x, t) ((x, t) :: xl)). simpl in *. left. easy.
  apply eq1 in H4. destruct H4.
  constructor.
  inv H3.
  unfold simple_option. split.
  apply cast_word_type in H10; try easy.
  apply subst_type_word_type. easy.
  split.
  apply cast_type_wf with (D:= D) in H10; try easy.
  apply subst_type_type_wf. easy.
  apply cast_means_simple_type in H10. easy.
  unfold simple_option.
  assert (In (x, t) ((x, t) :: xl)). simpl in *. left. easy.
  apply eq1 in H3. destruct H3.
  split.
  apply cast_word_type in H12; try easy.
  apply subst_type_word_type. easy.
  split.
  apply cast_type_wf with (D:= D) in H12; try easy.
  apply subst_type_type_wf. easy.
  apply cast_means_simple_type in H12. easy.
  unfold simple_option.
  destruct (Stack.find (elt:=Z * type) x S) eqn:eq2.
  destruct p. unfold stack_wt in *.
  apply Stack.find_2 in eq2.
  apply H in eq2. easy. easy.
  apply IHgen_rets; try easy. intros.
  specialize (H2 x0 t'0).
  assert (In (x0, t'0) ((x, t) :: xl)). simpl. right. easy.
  apply H2 in H7. easy.
Qed.

Lemma well_typed_gen_rets : forall tvl es D F S S' H AS env Q m e t e' t',
       expr_wf D F e' ->
       @well_typed D F S' H env Q m e t -> 
       gen_rets AS S tvl es e e' ->
       gen_rets_types S tvl es t t' ->
       (forall x t, In (x,t) tvl -> Env.MapsTo x t env) ->
       @well_typed D F S' H env Q m e' t'.
Proof.
  intros. generalize dependent t'.
  induction H2; intros. inv H3. easy.
  inv H5.
  apply IHgen_rets in H13 ; try easy.
  unfold gen_rets_type in *.
  assert (t0 = TNat \/ t0 <> TNat).
  destruct t0. left. easy. 1-4:right; easy.
  destruct H5. subst.
   assert (forall AS, subst_type AS TNat = TNat).
   {
    intros. induction AS0. simpl. easy.
    simpl. easy.
   }
  rewrite H5 in H3. inv H3. inv H10.
  destruct (tmem (get_tvars t'1) x) eqn:eq1.
  apply tmem_in in eq1. inv H14.
  apply TyRetTNat.
  specialize (H4 x TNat). simpl in *. exists TNat. apply H4. left. easy. easy. easy.
  assert (~ In x (get_tvars t'1)).
  intros R. apply tmem_in in R.
  rewrite eq1 in R. easy.
  inv H14. apply TyRet.
  specialize (H4 x TNat). simpl in *. exists TNat. apply H4. left. easy. easy. easy.
  inv H12.
  apply Stack.find_1 in H11. rewrite H11 in *.
  destruct (tmem (get_tvars t'1) x) eqn:eq1.
  apply tmem_in in eq1. inv H14.
  apply TyRetTNat.
  specialize (H4 x TNat). simpl in *. exists TNat. apply H4. left. easy. easy. easy.
  assert (~ In x (get_tvars t'1)).
  intros R. apply tmem_in in R.
  rewrite eq1 in R. easy.
  inv H14. apply TyRet.
  specialize (H4 x TNat). simpl in *. exists TNat. apply H4. left. easy. easy. easy.
  assert (match t0 with
      | TNat =>
          match e1 with
          | ELit v _ =>
              if tmem (get_tvars t'1) x
              then Some (subst_type [(x, Num v)] t'1)
              else Some t'1
          | EVar y =>
              match Stack.find (elt:=Z * type) y S with
              | Some (v, _) =>
                  if tmem (get_tvars t'1) x
                  then Some (subst_type [(x, Num v)] t'1)
                  else Some t'1
              | None => None
              end
          | _ => None
          end
      | _ => Some t'1
      end = Some t'1).
  destruct t0; try easy. rewrite H6 in *. clear H6.
  inv H14.
  inv H0.
  specialize (well_typed_type_nat D F S' H env0 Q m e' t'0 H13 H12) as eq1.
  apply TyRet.
  specialize (H4 x t0) as eq2.
  simpl in *. exists t0. apply eq2; try easy. left. easy.
  easy.
  intros R.
  apply eq1 in R.
  specialize (H4 x t0) as eq2.
  simpl in *. 
  assert ((x, t0) = (x, t0) \/ In (x, t0) xl). left. easy.
  apply eq2 in H0.
  apply Env.mapsto_always_same with (v1 := TNat) in H0; try easy.
  rewrite <- H0 in *. contradiction.
  inv H0. easy.
  intros. apply H4. simpl. right. easy.
Qed.

Lemma gen_arg_env_same : forall env tvl enva, gen_arg_env env tvl enva
      -> (forall n n' a b, n <> n' -> nth_error tvl n = Some a -> nth_error tvl n' = Some b -> fst a <> fst b)
       -> (forall x t, In (x,t) tvl -> Env.MapsTo x t enva).
Proof.
 intros. induction H.
 simpl in *. easy.
 specialize (nth_no_appear x0 t0 tvl H0) as eq1.
 simpl in *. destruct H1. inv H1.
 apply Env.add_1. easy.
 apply Env.add_2.
 apply eq1 in H1. easy.
 apply IHgen_arg_env; try easy.
 intros.
 specialize (H0 (S n) (S n') a b).
 apply H0. lia. simpl. easy. easy.
Qed.

Lemma get_dept_in_as : forall tvl es AS, 
   get_dept_map tvl es = Some AS -> (forall x, In (x,TNat) tvl -> (exists v, In (x,v) AS)).
Proof.
  induction tvl; intros;simpl in *. easy.
  destruct H0. subst.
  destruct es. inv H.
  destruct (get_good_dept e) eqn:eq1.
  destruct (get_dept_map tvl es) eqn:eq2. inv H.
  exists b. simpl. left. easy.
  inv H. inv H.
  destruct a. destruct t. destruct es. inv H.
  destruct (get_good_dept e) eqn:eq1.
  destruct (get_dept_map tvl es) eqn:eq2. inv H.
  specialize (IHtvl es l eq2 x H0).
  destruct IHtvl. exists x0. simpl. right. easy.
  inv H. inv H. destruct es. inv H.
  specialize (IHtvl es AS H x H0). destruct IHtvl. exists x0. easy.
  destruct es. inv H.
  specialize (IHtvl es AS H x H0). destruct IHtvl. exists x0. easy.
  destruct es. inv H.
  specialize (IHtvl es AS H x H0). destruct IHtvl. exists x0. easy.
  destruct es. inv H.
  specialize (IHtvl es AS H x H0). destruct IHtvl. exists x0. easy.
Qed.


Lemma gen_rets_as_cast_same:
   forall tvl D Q H env es AS S t t', get_dept_map tvl es = Some AS ->
   stack_wf D Q H env S ->
   gen_rets_types S tvl es t t' -> 
   well_bound_vars_type tvl t ->
   @well_typed_args D Q H env AS es tvl ->
   cast_type_bound S (subst_type AS t) t'.
Proof.
Admitted.

Lemma gen_rets_type_exists:
   forall tvl D Q H env es AS S t, 
   sub_domain env S -> 
   get_dept_map tvl es = Some AS ->
   @well_typed_args D Q H env AS es tvl ->
   (exists t', gen_rets_types S tvl es t t').
Proof.
Admitted.


Lemma call_t_in_env : forall tvl D Q H env es AS t,
   well_bound_vars_type tvl t ->
   get_dept_map tvl es = Some AS ->
   @well_typed_args D Q H env AS es tvl ->
   well_type_bound_in env (subst_type AS t).
Proof.
Admitted.

Lemma stack_grow_well_typed:
   forall D F S S' H env Q m e t,
     stack_consistent_grow S S' env -> @well_typed D F S H env Q m e t
     -> @well_typed D F S' H env Q m e t.
Proof.
Admitted.

Lemma well_bound_grow_env :
    forall env enva b, (forall x t, Env.MapsTo x t env -> Env.MapsTo x t enva) -> 
     well_bound_in env b -> well_bound_in enva b.
Proof.
   intros. induction b.
   apply well_bound_in_num.
   apply well_bound_in_var. inv H0.
   apply H. easy.
Qed.

Lemma well_type_bound_grow_env :
        forall env enva t, (forall x t, Env.MapsTo x t env -> Env.MapsTo x t enva) -> 
         well_type_bound_in env t -> well_type_bound_in enva t.
Proof.
   intros. induction t.
   apply well_type_bound_in_nat.
   apply well_type_bound_in_ptr.
   apply IHt. inv H0. assumption.
   apply well_type_bound_in_struct.
   apply well_type_bound_in_array.
   apply well_bound_grow_env with (env := env0); try easy. inv H0. assumption.
   apply well_bound_grow_env with (env := env0); try easy. inv H0. assumption.
   inv H0. apply IHt. assumption.
   apply well_type_bound_in_ntarray.
   apply well_bound_grow_env with (env := env0); try easy. inv H0. assumption.
   apply well_bound_grow_env with (env := env0); try easy. inv H0. assumption.
   inv H0. apply IHt. assumption.
Qed.

(* Type Preservation Theorem. *)
Lemma preservation : forall D S H env Q e t S' H' e',
    @structdef_wf D ->
    heap_wf D H ->
    heap_wt_all D H ->
    fun_wf D fenv S' H' ->
    expr_wf D fenv e ->
    stack_wt D S ->
    env_wt D env ->
    theta_wt Q env S ->
    sub_domain env S ->
    stack_wf D Q H env S ->
    @well_typed D fenv S H env Q Checked e t ->
    @reduce D (fenv env) S H e Checked S' H' (RExpr e') ->
    exists env' Q',
      sub_domain env' S' /\ stack_wf D Q' H env' S' /\
      @heap_consistent D Q H' H 
   /\ (@well_typed D fenv S' H' env' Q' Checked e' t
       \/ (exists t' t'', cast_type_bound S' t t' 
        /\ subtype D Q' t'' t' /\ @well_typed D fenv S' H' env' Q' Checked e' t'')).
Proof with eauto 20 with Preservation.
  intros D s H env Q e t s' H' e' HDwf HHwf HHWt HFun HEwf Hswt Henvt HQt HSubDom HSwf Hwt.
  generalize dependent H'. generalize dependent s'.  generalize dependent e'.
  remember Checked as m.
  induction Hwt as [
                     env Q m n t HTyLit                                         | (* Literals *)
                     env Q m x t Wb                                             | (* Variables *)
                     env Q AS m m' es x tvl e t HMap HGen HMode HArg            | (* Call *)
                     env Q m x h l t Wb                                         | (* Strlen *)
                     env Q m x y e l h t Alpha Wb HTy IH Hx                     | (* LetStrlen *)
                     env Q m x e1 e2 t b Alpha HTy1 IH1 HTy2 IH2 Hx Hdept       | (* Let-Nat-Expr *)
                     env Q m x e1 t1 e2 t Alpha HTy1 IH1 HTy2 IH2 Hx            | (* Let-Expr *)
                     env Q m x na a e t HIn Hx HTy1 IH1                         | (* RetNat *)
                     env Q m x na ta a e t HIn HTy1 IH1 Hx                      | (* Ret *)
                     env Q m e1 e2 HTy1 IH1 HTy2 IH2                            | (* Addition *)
                     env Q m e m' T fs i fi ti HTy IH HWf1 HWf2                 | (* Field Addr *)
                     env Q m w Wb                                               | (* Malloc *)
                     env Q m e t HTy IH                                         | (* Unchecked *)
                     env Q m t e t' Wb HChkPtr HTy IH                           | (* Cast - nat *)
                     env Q m t e t' Wb HTy IH HSub                              | (* Cast - subtype *)
                     env Q m e x y u v t t' Wb HTy IH Teq                       | (* DynCast - ptr array *)
                     env Q m e x y t t' HNot Teq Wb HTy IH                      | (* DynCast - ptr array from ptr *)
                     env Q m e x y u v t t' Wb Teq HTy IH                       | (* DynCast - ptr nt-array *)
                     env Q m e m' t l h t' t'' HTy IH HSub HPtrType HMode       | (* Deref *)
                     env Q m e1 m' l h e2 t WT Twf HTy1 IH1 HTy2 IH2 HMode                      | (* Index for array pointers *)
                     env Q m e1 m' l h e2 t WT Twf HTy1 IH1 HTy2 IH2 HMode                      | (* Index for ntarray pointers *)
                     env Q m e1 e2 m' t t1 HSub WT HTy1 IH1 HTy2 IH2 HMode                      | (* Assign normal *)
                     env Q m e1 e2 m' l h t t' WT Twf HSub HTy1 IH1 HTy2 IH2 HMode              | (* Assign array *)
                     env Q m e1 e2 m' l h t t' WT Twf HSub HTy1 IH1 HTy2 IH2 HMode              | (* Assign nt-array *)

                     env Q m e1 e2 e3 m' l h t t' WT Twf TSub HTy1 IH1 HTy2 IH2 HTy3 IH3 HMode      |  (* IndAssign for array pointers *)
                     env Q m e1 e2 e3 m' l h t t' WT Twf TSub HTy1 IH1 HTy2 IH2 HTy3 IH3 HMode      |  (* IndAssign for ntarray pointers *)
                     env Q m m' x t t1 e1 e2 t2 t3 t4 HEnv TSub HPtr HTy1 IH1 HTy2 IH2 HJoin HMode  | (* If *)
                     env Q m m' x l t e1 e2 t2 t3 t4 HEnv HTy1 IH1 HTy2 IH2 HJoin HMode (* IfNT *)
                   ]; intros e' s' H' HFun Hreduces; subst.
  (* T-Lit, impossible because values do not step *)
  - exfalso. eapply lit_are_nf...
  (* T-Var *)
  - inv Hreduces.
    destruct E; inversion H1; simpl in *; subst. inv H5. exists env. exists Q.
    split. easy.
    split. assumption.
    split. unfold heap_consistent. eauto.
    right. unfold stack_wf in HSwf.
    specialize (HSwf x t Wb) as eq2.
    destruct eq2 as [ vx [ t' [t'' [X1 [X2 [X3 X4]]]]]].
    specialize (Stack.mapsto_always_same (Z*type) x (vx, t'') (v, t0) s' X3 H10) as eq1.
    inv eq1.
    exists t'. exists t0.
    split. easy. split. easy.
    apply TyLit. easy.
  (*T-Call*)
  - inv Hreduces.
    destruct E; inversion H1; simpl in *; subst. inv H5.
    rewrite H6 in HMap. inv HMap.
    rewrite H10 in HGen. inv HGen.
    specialize (gen_arg_env_good tvl env) as X1.
    destruct X1 as [enva X1].
    specialize (sub_domain_grows tvl es env enva s s' AS X1 H13 HSubDom) as X2.
    exists enva. exists Q.
    split. easy.
    split. 
    apply (stack_wf_trans D Q H' env enva s s' AS tvl es); try easy.
    unfold fun_wf in *.
    destruct (HFun env enva x tvl t e m' H6 X1) as [Y1 [Y2 Y3]]. easy.
    destruct (HFun env enva x tvl t e m' H6 X1) as [Y1 [Y2 Y3]]. easy.
    intros.
    specialize (gen_arg_env_has_all tvl env enva X1 x0 t0 H) as eq1. easy.
    unfold theta_wt in *. destruct HQt. easy.
    inv HEwf. easy.
    split. easy.
    destruct (HFun env enva x tvl t e m' H6 X1) as [Y1 [Y2 [Y3 [Y4 [Y5 [Y6 [Y7 Y8]]]]]]].
    left. destruct m'. 2: { assert (Unchecked = Unchecked) by easy. apply HMode in H. easy. } 
    specialize (gen_rets_type_exists tvl D Q H' env es AS s t HSubDom H10 HArg) as eq1.
    destruct eq1.
    specialize (gen_rets_as_cast_same tvl D Q H' env es AS s t x0 H10 HSwf H Y6 HArg) as eq1.
    apply theta_grow_type with (Q := Q) in Y8.
    assert (forall x t', In (x,t') tvl -> word_type t' /\ type_wf D t').
    intros. apply Y1 in H1. easy.
    specialize (expr_wf_gen_rets tvl es D fenv s AS e e' Hswt Y7 H14 H1) as eq2.
    specialize (gen_arg_env_same env tvl enva X1 Y3) as eq3.
    specialize (well_typed_gen_rets tvl es D (fenv) s s' H' AS enva
               Q Checked e t e' x0 eq2 Y8 H14 H eq3) as eq4.
    specialize (call_t_in_env tvl D Q H' env es AS t Y6 H10 HArg) as eq5.
    assert (length tvl = length es) as eq6.
    rewrite (well_typed_args_same_length D Q H' env AS es tvl); try easy.
    specialize (stack_consist_trans s s' env tvl es AS HSubDom Y2 eq6 H13) as eq7.
    inv Y4.
    apply TyCast1 with (t' := x0); try easy.
   assert (forall AS, subst_type AS TNat = TNat).
   {
    intros. induction AS0. simpl. easy.
    simpl. easy.
   }
   rewrite H2. constructor.
   destruct m. simpl. 
   apply TyCast2 with (t' := x0); try easy.
   apply well_type_bound_grow_env with (env := env).
   apply gen_arg_env_grow_1 with (tvl := tvl); try easy.
   inv eq5. easy.
   simpl in eq1.
   apply subtype_left with (t2' := x0).
   apply cast_means_simple_type in eq1. easy.
   apply stack_grow_cast_type_same with (env := env) (S := s); try easy.
   constructor.
    apply TyCast1 with (t' := x0); try easy.
   simpl in *.
   apply well_type_bound_grow_env with (env := env).
   apply gen_arg_env_grow_1 with (tvl := tvl); try easy.
   easy.
  (*T-Strlen*)
  - inv Hreduces.
    destruct E; inversion H1; simpl in *; subst. inv H5. exists env. exists Q.
    split.
    unfold change_strlen_stack.
    unfold sub_domain in *.
    intros. destruct (n' <=? h0).
    apply HSubDom. easy.
    destruct (Nat.eq_dec x0 x). subst.
    exists (n, TPtr m (TNTArray l0 (Num n') t0)).
    apply Stack.add_1. easy.
    apply HSubDom in H.
    destruct H.
    exists x1.
    apply Stack.add_2. lia. easy.
    split.
    inv HSwf.
    destruct H.
    constructor. split. intros.
    unfold change_strlen_stack.
    destruct (n' <=? h0).
    apply H in H2. eauto.
    destruct (Nat.eq_dec x x0). subst.
    apply H in H2 as eq1.
    destruct eq1 as [v [ta [tb [X1 [X2 [X3 [X4 X5]]]]]]].
    specialize (Stack.mapsto_always_same (Z*type) x0 (n, TPtr m (TNTArray l0 (Num h0) t0))
                 (v, tb) s H4 X3) as eq1. inv eq1.
    specialize (subtype_ptr D Q m (TNTArray l0 (Num h0) t0) ta X2) as eq1.
    destruct eq1. subst.
    specialize (cast_ptr_left s t2 m x X1) as eq1.
    destruct eq1. subst.

    exists n. exists (TPtr m (TNTArray l0 (Num n') t0)). exists (TPtr m (TNTArray l0 (Num n') t0)).
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

(* The Blame Theorem. *)
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

