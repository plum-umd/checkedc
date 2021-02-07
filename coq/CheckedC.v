Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Structures.Monads.

From CHKC Require Import Tactics ListUtil Map.

(** * Document Conventions *)


(** It is common when defining syntax for a language on paper to associate one or many
    _metavariables_ with each syntactic class. For example, the metavariables <<x>>, <<y>>,
    and <<z>> are often used to represent the syntactic class of program variables. It is
    understood that wherever these metavariables appear they indicate an implicit universal
    quantification over all members of the syntactic class they represent. In Coq, however,


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

Require Import Arith.
Require Import ZArith.
Require Import ZArith.BinIntDef.

Require Export BinNums.
Require Import BinPos BinNat.

Local Open Scope Z_scope.


Definition var    := nat.
Definition field  := nat.
Definition struct := nat.

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

Inductive bound : Set := | Num : Z -> bound | Var : var -> Z -> option Z -> bound.

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

Inductive simple_type (D : structdef) : type -> Prop := 
  | SPTPtr : forall m w, simple_type D w -> simple_type D (TPtr m w)
  | SPArray : forall l h t, simple_type D (TArray (Num l) (Num h) t)
  | SPNTArray : forall l h t, simple_type D (TNTArray (Num l) (Num h) t).

Inductive none_bound_only : bound -> Prop :=
    | none_bound_only_1: forall n, none_bound_only (Num n)
    | none_bound_only_2: forall x y, none_bound_only (Var x y None).

Inductive type_wf (D : structdef) : type -> Prop :=
  | WFTNat : type_wf D (TNat)
  | WFTPtr : forall m w, type_wf D (TPtr m w)
  | WFTStruct : forall T,
      (exists (fs : fields), StructDef.MapsTo T fs D) ->
      type_wf D (TStruct T)
  | WFArray : forall l h t,
      word_type t ->
      type_wf D t ->
      none_bound_only l ->
      none_bound_only h ->
      type_wf D (TArray l h t)
  | WFNTArry : forall l h t,       
      word_type t ->
      type_wf D t ->
      none_bound_only l ->
      none_bound_only h ->
      type_wf D (TNTArray l h t).

Definition fields_wf (D : structdef) (fs : fields) : Prop :=
  forall f t,
    Fields.MapsTo f t fs ->
    word_type t /\ type_wf D t /\ simple_type D t.

Definition structdef_wf (D : structdef) : Prop :=
  forall (T : struct) (fs : fields),
    StructDef.MapsTo T fs D ->
    fields_wf D fs.
   

(* This defines the subtyping relation. *)
Inductive nat_less : bound -> bound -> Prop :=
  | nat_less_num : forall l h, l <= h -> nat_less (Num l) (Num h)
  | nat_less_var : forall x l h u v, l <= h -> nat_less (Var x l u) (Var x h v).

Inductive subtype (D : structdef) : type -> type -> Prop :=
  | SubTyRefl : forall t, subtype D t t
  | SubTySubsume : forall l h l' h' t m,
    nat_less l l' -> nat_less h' h -> 
    subtype D (TPtr m (TArray l h t)) (TPtr m (TArray l' h' t))
  | SubTyNtSubsume : forall l h l' h' t m,
    nat_less l l' -> nat_less h' h -> 
    subtype D (TPtr m (TNTArray l h t)) (TPtr m (TNTArray l' h' t))
  | SubTyStructArrayField : forall (T : struct) (fs : fields) m,
    StructDef.MapsTo T fs D ->
    Some (TNat) = (Fields.find 0%nat fs) ->
    subtype D (TPtr m (TStruct T)) (TPtr m (TNat)).

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

Inductive expression : Type :=
  | ELit : Z -> type -> expression
  | EVar : var -> expression
  | ELet : var -> expression -> expression -> expression
  | EMalloc : type -> expression
  | ECast : type -> expression -> expression
  | EPlus : expression -> expression -> expression
  | EFieldAddr : expression -> field -> expression
  | EDeref : expression -> expression (*  * e *)
  | EAssign : expression -> expression -> expression (* *e = e *)
  | EIf : var -> expression -> expression -> expression (* if * x then e1 else e2. *)
  | EUnchecked : expression -> expression.

(* Defining stack. *)
Module Stack := Map.Make Nat_as_OT.

Definition stack := Stack.t (Z * type).

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

Inductive expr_wf (D : structdef) : expression -> Prop :=
  | WFELit : forall n t,
    word_type t ->
    type_wf D t ->
    expr_wf D (ELit n t)
  | WFEVar : forall x,
      expr_wf D (EVar x)
  | WFELet : forall x e1 e2,
      expr_wf D e1 ->
      expr_wf D e2 ->
      expr_wf D (ELet x e1 e2)
  | WFEIF : forall x e1 e2,
      expr_wf D e1 ->
      expr_wf D e2 ->
      expr_wf D (EIf x e1 e2)
  | WFEMalloc : forall w,
      type_wf D w ->
      expr_wf D (EMalloc w)
  | WFECast : forall t e,
      word_type t ->
      type_wf D t ->
      expr_wf D e ->
      expr_wf D (ECast t e)
  | WFEPlus : forall e1 e2,
      expr_wf D e1 ->
      expr_wf D e2 ->
      expr_wf D (EPlus e1 e2)
  | WFEFieldAddr : forall e f,
      expr_wf D e ->
      expr_wf D (EFieldAddr e f)
  | WFEDeref : forall e,
      expr_wf D e ->
      expr_wf D (EDeref e)
  | WFEAssign : forall e1 e2,
      expr_wf D e1 ->
      expr_wf D e2 ->
      expr_wf D (EAssign e1 e2)
  | WFEUnchecked : forall e,
      expr_wf D e ->
      expr_wf D (EUnchecked e).

(* Standard substitution.
   In a let, if the bound variable is the same as the one we're substituting,
   then we don't substitute under the lambda. 
 *)
Fixpoint subst (x : var) (v : expression) (e : expression) : expression :=
  match e with
  | ELit _ _ => e
  | EVar y => if var_eq_dec x y then v else e
  | ELet x' e1 e2 =>
    if var_eq_dec x x' then ELet x' (subst x v e1) e2 else ELet x' (subst x v e1) (subst x v e2)
  | EIf x' e1 e2 =>
        EIf x' (subst x v e1) (subst x v e2)
  | EMalloc _ => e
  | ECast t e' => ECast t (subst x v e')
  | EPlus e1 e2 => EPlus (subst x v e1) (subst x v e2)
  | EFieldAddr e' f => EFieldAddr (subst x v e') f
  | EDeref e' => EDeref (subst x v e')
  | EAssign e1 e2 => EAssign (subst x v e1) (subst x v e2)
  | EUnchecked e' => EUnchecked (subst x v e')
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
  | TArray (Var x1 y1 (Some l)) (Var x2 y2 (Some h)) T =>
    Some ((l+y1), Zreplicate ((h + y2) - (l+y1)) T)
  | TNTArray (Num l) (Num h) T =>
    Some (l, Zreplicate (h - l) T)
  | TNTArray (Var x1 y1 (Some l)) (Var x2 y2 (Some h)) T =>
    Some ((l+y1), Zreplicate ((h + y2) - (l+y1)) T)
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
             | Var x n None => (match (Stack.find x s) with Some (v,t) => Some (Num (v + n)) | None => None end)
             | Var x n (Some u) => Some (Num (u + n))
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
                                Some (TPtr c (TArray l' h' t))
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

Definition cast_bound (s:stack) (b:bound) : option bound :=
   match b with Num n => Some (Num n)
             | Var x n None => (match (Stack.find x s) with Some (v,t) => Some (Var x n (Some v)) | None => None end)
             | _ => Some b
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

Lemma eval_is_cast_bound : forall s b, 
       eval_bound s b = None -> cast_bound s b = None.
Proof.
  intros. unfold eval_bound in H.
  unfold cast_bound.
  destruct b. inversion H. inversion H.
  destruct o. inversion H.
  destruct (Stack.find (elt:=Z * type) v s).
  destruct p. inversion H.
  reflexivity.
Qed.

Lemma cast_is_eval_bound : forall s b, 
       cast_bound s b = None -> eval_bound s b = None.
Proof.
  intros. unfold cast_bound in H.
  unfold eval_bound.
  destruct b. inversion H. inversion H.
  destruct o. inversion H.
  destruct (Stack.find (elt:=Z * type) v s).
  destruct p. inversion H.
  reflexivity.
Qed.
*)

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
   match Stack.find x s with | Some (v, TPtr m (TNTArray l h t)) => (eval_bound s h = Some (Num 0))
                          | _ => False
   end.

Definition add_nt_one (s : stack) (x:var) : stack :=
   match Stack.find x s with | Some (v, TPtr m (TNTArray l (Num h) t)) 
                         => Stack.add x (v, TPtr m (TNTArray l (Num (h+1)) t)) s
                             | Some (v, TPtr m (TNTArray l (Var x n u) t))
                           => Stack.add x (v, TPtr m (TNTArray l (Var x (n+1) u) t)) s
                             | _ => s
   end.

Definition is_array_ptr (t:type) : Prop :=
  match t with TPtr Checked (TArray l h t') => True
             | TPtr Checked (TNTArray l h t') => True
             | _ => False
  end.

Definition is_rexpr (r : result) : Prop :=
   match r with RExpr x => True
              | _ => False
   end.

Definition sub_bound (b:bound) (n:Z) : (bound) :=
  match b with Num m => Num (m - n)
           | Var x m z => Var x (m - n) z
  end.

Definition sub_type_bound (t:type) (n:Z) : type :=
   match t with TPtr Checked (TArray l h t1) => TPtr Checked (TArray (sub_bound l n) (sub_bound h n) t1)
              | TPtr Checked (TNTArray l h t1) => TPtr Checked (TNTArray (sub_bound l n) (sub_bound h n) t1)
              | _ => t
   end.

Definition malloc_bound (t:type) : Prop :=
   match t with (TArray (Num l) (Num h) t) => (l = 0 /\ h > 0)
              | (TArray (Var x y (Some l)) (Var x1 y1 (Some h)) t) => ((y+l) = 0 /\ (y1 + h)>0)
              | (TNTArray (Num l) (Num h) t) => (l = 0 /\ h > 0)
              | (TNTArray (Var x y (Some l)) (Var x1 y1 (Some h)) t) => ((y+l) = 0 /\ (y1 + h)>0)
              | _ => True
   end.

Inductive step (D : structdef) : stack -> heap -> expression -> stack -> heap -> result -> Prop :=
  | SVar : forall s H x v t,
      (Stack.find x s) = Some (v, t) ->
      step D
           s H (EVar x)
           s H (RExpr (ELit v t))
  | SPlusChecked : forall s H n1 t1 t1' n2,
      n1 > 0 -> is_array_ptr t1 -> cast_type_bound s t1 t1' ->
      step D
         s H (EPlus (ELit n1 t1) (ELit n2 TNat))
         s H (RExpr (ELit (n1 + n2) (sub_type_bound t1' n2)))
  | SPlus : forall s H t1 n1 n2,
       ~ is_array_ptr t1 -> 
      step D
        s H (EPlus (ELit n1 t1) (ELit n2 TNat))
        s H (RExpr (ELit (n1 + n2) t1))
  | SPlusBounds : forall s H n1 t n2,
      eval_type_bound s t = None ->
      step D
        s H (EPlus (ELit n1 (TPtr Checked t)) (ELit n2 TNat))
        s H RBounds
  | SPlusNull : forall s H n1 t n2,
      n1 <= 0 -> is_array_ptr t ->
      step D
        s H (EPlus (ELit n1 t) (ELit n2 (TNat)))
        s H RNull
  | SCast : forall s H t n t',
      ~ is_array_ptr t ->
      step D
        s H (ECast t (ELit n t'))
        s H (RExpr (ELit n t))
  | SCastArray : forall s H t n t' l h w l' h' w',
     eval_type_bound s t = Some (TPtr Checked (TArray (Num l) (Num h) w)) ->
      eval_type_bound s t' = Some (TPtr Checked (TArray (Num l') (Num h') w')) ->
          l' <= l -> l < h -> h <= h' ->
      step D
        s H (ECast t (ELit n t'))
        s H (RExpr (ELit n t))
  | SCastArrayLowOOB1 : forall s H t n t' l h w l' h' w',
     eval_type_bound s t = Some (TPtr Checked (TArray (Num l) (Num h) w)) ->
      eval_type_bound s t' = Some (TPtr Checked (TArray (Num l') (Num h') w')) ->
           l < l' -> 
           step D
        s H (ECast t (ELit n t')) s H RBounds
  | SCastArrayLowOOB2 : forall s H t n t' l h w l' h' w',
     eval_type_bound s t = Some (TPtr Checked (TArray (Num l) (Num h) w)) ->
      eval_type_bound s t' = Some (TPtr Checked (TArray (Num l') (Num h') w')) ->
           h <= l -> 
           step D
        s H (ECast t (ELit n t')) s H RBounds
  | SCastArrayHighOOB1 : forall s H t n t' l h w l' h' w',
     eval_type_bound s t = Some (TPtr Checked (TArray (Num l) (Num h) w)) ->
      eval_type_bound s t' = Some (TPtr Checked (TArray (Num l') (Num h') w')) ->
           h' < h -> 
           step D
        s H (ECast t (ELit n t')) s H RBounds
  | SCastNTArray : forall s H t n t' l h w l' h' w',
     eval_type_bound s t = Some (TPtr Checked (TNTArray (Num l) (Num h) w)) ->
      eval_type_bound s t' = Some (TPtr Checked (TNTArray (Num l') (Num h') w')) ->
          l' <= l -> l < h -> h <= h' ->
      step D
        s H (ECast t (ELit n t'))
        s H (RExpr (ELit n t))
  | SCastNTArrayLowOOB1 : forall s H t n t' l h w l' h' w',
     eval_type_bound s t = Some (TPtr Checked (TArray (Num l) (Num h) w)) ->
      eval_type_bound s t' = Some (TPtr Checked (TArray (Num l') (Num h') w')) ->
           l < l' -> 
           step D
        s H (ECast t (ELit n t')) s H RBounds
  | SCastNTArrayLowOOB2 : forall s H t n t' l h w l' h' w',
     eval_type_bound s t = Some (TPtr Checked (TArray (Num l) (Num h) w)) ->
      eval_type_bound s t' = Some (TPtr Checked (TArray (Num l') (Num h') w')) ->
           h <= l -> 
           step D
        s H (ECast t (ELit n t')) s H RBounds
  | SCastNTArrayHighOOB1 : forall s H t n t' l h w l' h' w',
     eval_type_bound s t = Some (TPtr Checked (TArray (Num l) (Num h) w)) ->
      eval_type_bound s t' = Some (TPtr Checked (TArray (Num l') (Num h') w')) ->
           h' < h -> 
           step D
        s H (ECast t (ELit n t')) s H RBounds
  | SDeref : forall s H n n1 t1 t t2,
      (expr_wf D (ELit n1 t1)) ->
      eval_type_bound s t = Some t2 ->
      Heap.MapsTo n (n1, t1) H ->
      (forall l h t', t2 = TPtr Checked (TArray (Num l) (Num h) t') -> h > 0 /\ l <= 0) ->
      (forall l h t', t2 = TPtr Checked (TNTArray (Num l) (Num h) t') -> h > 0 /\ l <= 0) ->
      step D
        s H (EDeref (ELit n t))
        s H (RExpr (ELit n1 t1))
  | SDerefHighOOB1 : forall s H n t t' t1 l h,
      h <= 0 ->
      eval_type_bound s t = Some t' ->
      t' = TPtr Checked (TArray (Num l) (Num h) t1) ->
      step D
        s H (EDeref (ELit n t))
        s H RBounds
  | SDerefHighOOB12 : forall s H n t t' t1 l h,
      h <= 0 ->
      eval_type_bound s t = Some t' ->
      t' = TPtr Checked (TNTArray (Num l) (Num h) t1) ->
      step D
        s H (EDeref (ELit n t))
        s H RBounds
  | SDerefLowOOB1 : forall s H n t t' t1 l h,
      l > 0 ->
      eval_type_bound s t = Some t' ->
      t' = TPtr Checked (TArray (Num l) (Num h) t1) ->
      step D
        s H (EDeref (ELit n t))
        s H RBounds
  | SDerefLowOOB2 : forall s H n t t' t1 l h,
      l > 0 ->
      eval_type_bound s t = Some t' ->
      t' = TPtr Checked (TNTArray (Num l) (Num h) t1) ->
      step D
        s H (EDeref (ELit n t))
        s H RBounds
  | SDerefNull : forall s H t t' n w,
      n <= 0 ->
      eval_type_bound s t = Some t' ->
      t' = TPtr Checked w ->
      step D
        s H (EDeref (ELit n t))
        s H RNull
  | SAssign : forall s H n t tv n1 t1 tv' H',
      Heap.In n H ->
      eval_type_bound s t = Some tv ->
      (forall l h t', tv = TPtr Checked (TArray (Num l) (Num h) t') -> h > 0 /\ l <= 0) -> 
      (forall l h t', tv = TPtr Checked (TNTArray (Num l) (Num h) t') -> h > 0 /\ l <= 0) -> 
      cast_type_bound s t1 tv' ->
      H' = Heap.add n (n1, tv') H ->
      step D
        s H  (EAssign (ELit n t) (ELit n1 t1))
        s H' (RExpr (ELit n1 tv'))
  | SAssignHighOOB1 : forall s H n t t' n1 t1 l h,
      h <= 0 ->
      eval_type_bound s t = Some t' ->
      t' = TPtr Checked (TArray (Num l) (Num h) t1) ->
      step D
        s H (EAssign (ELit n t) (ELit n1 t1))
        s H RBounds
  | SAssignHighOOB2 : forall s H n t t' n1 t1 l h,
      h <= 0 ->
      eval_type_bound s t = Some t' ->
      t' = TPtr Checked (TNTArray (Num l) (Num h) t1) ->
      step D
        s H (EAssign (ELit n t) (ELit n1 t1))
        s H RBounds
  | SAssignLowOOB1 : forall s H n t t' n1 t1 l h,
      l > 0 ->
      eval_type_bound s t = Some t' ->
      t' = TPtr Checked (TArray (Num l) (Num h) t1) ->
      step D
        s H (EAssign (ELit n t) (ELit n1 t1))
        s H RBounds
  | SAssignLowOOB2 : forall s H n t t' n1 t1 l h,
      l > 0 ->
      eval_type_bound s t = Some t' ->
      t' = TPtr Checked (TNTArray (Num l) (Num h) t1) ->
      step D
        s H (EAssign (ELit n t) (ELit n1 t1))
        s H RBounds
  | SAssignNull : forall s H t tv w n n1 t',
      n1 <= 0 ->
      eval_type_bound s t = Some tv ->
      tv = TPtr Checked w ->
      step D
        s H (EAssign (ELit n1 t) (ELit n t'))
        s H RNull
  | SFieldAddrChecked : forall s H n t (fi : field) n0 t0 T fs i fi ti,
      n > 0 ->
      t = TPtr Checked (TStruct T) ->
      StructDef.MapsTo T fs D ->
      Fields.MapsTo fi ti fs ->
      List.nth_error (Fields.this fs) i = Some (fi, ti) ->
      n0 = n + Z.of_nat(i) ->
      t0 = TPtr Checked ti ->
      word_type ti ->
      step D
        s H (EFieldAddr (ELit n t) fi)
        s H (RExpr (ELit n0 t0))
  | SFieldAddrNull : forall s H (fi : field) n T,
      n <= 0 ->
      step D
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
      step D
        s H (EFieldAddr (ELit n t) fi)
        s H (RExpr (ELit n0 t0))
  | SMalloc : forall s H w w' H' n1,
      cast_type_bound s w w' -> malloc_bound w' ->
      allocate D H w' = Some (n1, H') ->
      step D
        s H (EMalloc w)
        s H' (RExpr (ELit n1 (TPtr Checked w')))
  | SMallocHighOOB1 : forall s H w t' l h t1,
      h <= 0 ->
      eval_type_bound s w = Some t' ->
      t' = TPtr Checked (TArray (Num l) (Num h) t1) ->
      step D
        s H (EMalloc w)
        s H RBounds
  | SMallocHighOOB2 : forall s H w t' l h t1,
      h <= 0 ->
      eval_type_bound s w = Some t' ->
      t' = TPtr Checked (TNTArray (Num l) (Num h) t1) ->
      step D
        s H (EMalloc w)
        s H RBounds
  | SMallocLowOOB1 : forall s H w t' l h t1,
      l > 0 ->
      eval_type_bound s w = Some t' ->
      t' = TPtr Checked (TArray (Num l) (Num h) t1) ->
      step D
        s H (EMalloc w)
        s H RBounds
  | SMallocLowOOB2 : forall s H w t' l h t1,
      l > 0 ->
      eval_type_bound s w = Some t' ->
      t' = TPtr Checked (TArray (Num l) (Num h) t1) ->
      step D
        s H (EMalloc w)
        s H RBounds
  | SLet : forall s H x n t e t',
      cast_type_bound s t t' ->
      step D
        s H (ELet x (ELit n t) e)
        (Stack.add x (n, t') s) H (RExpr e)
  | SUnchecked : forall s H n t,
      step D
        s H (EUnchecked (ELit n t))
        s H (RExpr (ELit n t))
   | SIfTrueNotNTHit : forall s H x e1 e2 n1 t1, 
           step D s H (EDeref (EVar x)) s H (RExpr (ELit n1 t1)) ->
           n1 <> 0 -> ~ (NTHit s x) -> step D s H (EIf x e1 e2) s H (RExpr e1)
   | SIfTrueNTHit : forall s H x e1 e2 n1 t1, 
           step D s H (EDeref (EVar x)) s H (RExpr (ELit n1 t1)) ->
           n1 <> 0 -> (NTHit s x) -> step D (add_nt_one s x) H (EIf x e1 e2) s H (RExpr e1)
   | SIfFalse : forall s H x e1 e2 t1, 
           step D s H (EDeref (EVar x)) s H (RExpr (ELit 0 t1)) ->
              step D s H (EIf x e1 e2) s H (RExpr e2)
   | SIfFail : forall s H x e1 e2 r, ~ is_rexpr r -> step D s H (EDeref (EVar x)) s H r -> step D s H (EIf x e1 e2) s H r.

Hint Constructors step.

(* TODO: say more *)
(** The compatible closure of [H; e ~> H'; r], [H; e ->m H'; r].

    We also define a convenience predicate, [reduces H e], which holds
    when there's some [m], [H'], and [r] such that [H; e ->m H'; r]. *)

Inductive reduce (D : structdef) : stack -> heap -> expression -> mode -> stack -> heap -> result -> Prop :=
  | RSExp : forall H s e m H' s' e' E,
      step D s H e s' H' (RExpr e') ->
      m = mode_of(E) ->
      reduce D s
        H (in_hole e E)
        m s'
        H' (RExpr (in_hole e' E))
  | RSHaltNull : forall H s e m H' s' E,
      step D s H e s' H' RNull ->
      m = mode_of(E) ->
      reduce D s
        H (in_hole e E)
        m s'
        H' RNull
  | RSHaltBounds : forall H s e m H' s'  E,
      step D s H e s' H' RBounds ->
      m = mode_of(E) ->
      reduce D s
        H (in_hole e E)
        m s'
        H' RBounds.

Hint Constructors reduce.

Definition reduces (D : structdef) (s : stack) (H : heap) (e : expression) : Prop :=
  exists (m : mode) (s' : stack) (H' : heap) (r : result), reduce D s H e m s' H' r.

Hint Unfold reduces.

(** * Static Semantics *)

Require Import Lists.ListSet.

Definition eq_dec_nt (x y : Z * type) : {x = y} + { x <> y}.
repeat decide equality.
Defined. 

Definition scope := set (Z *type)%type. 
Definition empty_scope := empty_set (Z * type).

Module Env := Map.Make Nat_as_OT.

Definition env := Env.t type.

Definition empty_env := @Env.empty type.

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
  | TyLitRec : forall s n w t,
      set_In (n, t) s ->
      subtype D t (TPtr Checked w) ->
      well_typed_lit D H s n (TPtr Checked w)
  | TyLitC : forall s n w b ts,
      Some (b, ts) = allocate_meta D w ->
      (forall k, b <= k < b + Z.of_nat(List.length ts) ->
                 exists n' t',
                   Some t' = List.nth_error ts (Z.to_nat (k - b)) /\
                   Heap.MapsTo (n + k) (n', t') H /\
                   well_typed_lit D H (set_add eq_dec_nt (n, TPtr Checked w) s) n' t') ->
      well_typed_lit D H s n (TPtr Checked w).



Hint Constructors well_typed_lit.

(** It turns out, the induction principle that Coq generates automatically isn't very useful. *)

(** In particular, the TyLitC case does not have an induction hypothesis.
    So, we prove an alternative induction principle which is almost identical but includes
    an induction hypothesis for the TyLitC case.

    TODO: write blog post about this *)

Lemma well_typed_lit_ind' :
  forall (D : structdef) (H : heap) (P : scope -> Z -> type -> Prop),
    (forall (s : scope) (n : Z), P s n (TNat)) ->
       (forall (s : scope) (n : Z) (w : type), P s n (TPtr Unchecked w)) ->
       (forall (s : scope) (t : type), P s 0 t) ->
       (forall (s : scope) (n : Z) (w : type) (t : type), set_In (n, t) s -> subtype D t (TPtr Checked w) -> P s n (TPtr Checked w)) ->
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
            | TyLitRec _ _ s' n' w' t' Hscope Hsub => HTyLitRec s' n' w' t' Hscope Hsub
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
                                                 ex_intro _ n' 
                           (ex_intro _ t' (conj Ht' (conj Hheap (conj Hwt (F (set_add eq_dec_nt (_ , TPtr Checked w') s') n' t' Hwt)))))
                                               end
                                             end
                                           end
                                         end)
            end).
Qed.


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

Inductive well_bound_in : env -> bound -> Prop :=
   | well_bound_in_num : forall env n, well_bound_in env (Num n)
   | well_bound_in_var : forall env x y z, Env.In x env -> well_bound_in env (Var x y z).

Inductive well_type_bound_in : env -> type -> Prop :=
   | well_type_bound_in_nat : forall env, well_type_bound_in env TNat
   | well_type_bound_in_ptr : forall m t env, well_type_bound_in env t -> well_type_bound_in env (TPtr m t)
   | well_type_bound_in_struct : forall env T, well_type_bound_in env (TStruct T)
   | well_type_bound_in_array : forall env l h t, well_bound_in env l -> well_bound_in env h -> 
                                      well_type_bound_in env t -> well_type_bound_in env (TArray l h t)
   | well_type_bound_in_ntarray : forall env l h t, well_bound_in env l -> well_bound_in env h -> 
                                      well_type_bound_in env t -> well_type_bound_in env (TNTArray l h t).

Inductive well_typed { D : structdef } { H : heap } : env -> mode -> expression -> type -> Prop :=
  | TyLit : forall env m n t,
      well_type_bound_in env t ->
      @well_typed_lit D H empty_scope n t ->
      well_typed env m (ELit n t) t
  | TyVar : forall env m x t,
      well_type_bound_in env t ->
      Env.MapsTo x t env ->
      well_typed env m (EVar x) t
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
      well_type_bound_in env ti ->
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
  | TyCast2 : forall env m t e x y u v,
      well_typed env m e (TPtr Checked (TArray u v t)) ->
      well_typed env m (ECast t e) (TPtr Checked (TArray x y t))
  | TyCast3 : forall env m t e x y u v,
      well_typed env m e (TPtr Checked (TNTArray u v t)) ->
      well_typed env m (ECast t e) (TPtr Checked (TNTArray x y t))
  | TyDeref : forall env m e m' t l h t' t'',
      well_typed env m e t ->
      t = (TPtr m' t'') ->
      ((word_type t'' /\ t'' = t') \/ (t'' = TArray l h t' /\ word_type t' /\ type_wf D t')
       \/ (t'' = TNTArray l h t' /\ word_type t' /\ type_wf D t')) ->
      (m' = Unchecked -> m = Unchecked) ->
      well_typed env m (EDeref e) t'
  | TyIndex : forall env m e1 m' l h t e2 t',
      word_type t' -> type_wf D t' ->
      well_typed env m e1 t ->
      t= (TPtr m' (TArray l h t')) ->
      well_typed env m e2 (TNat) ->
      (m' = Unchecked -> m = Unchecked) ->
      well_typed env m (EDeref (EPlus e1 e2)) t'
  | TyAssign : forall env m e1 m' t l h t' t'' e2,
      well_typed env m e1 t ->
      well_typed env m e2 t' ->
      t = (TPtr m' t'') ->
      ((word_type t'' /\ t'' = t') \/ (t'' = TArray l h t' /\ word_type t' /\ type_wf D t')
         \/ (t'' = TNTArray l h t' /\ word_type t' /\ type_wf D t')) ->
      (m' = Unchecked -> m = Unchecked) ->
      well_typed env m (EAssign e1 e2) t'
  | TyIndexAssign : forall env m e1 m' l h t e2 e3 t',
      word_type t' -> type_wf D t' ->
      well_typed env m e1 t ->
      t = (TPtr m' (TArray l h t')) ->
      well_typed env m e2 (TNat) ->
      well_typed env m e3 t' ->
      (m' = Unchecked -> m = Unchecked) ->
      well_typed env m (EAssign (EPlus e1 e2) e3) t'
  | TyIf : forall env m m' x t t1 e1 e2 t2,
      Env.MapsTo x t env ->
      t = (TPtr m' t1) ->
      (exists l h t', (word_type t1 /\ t1 = t') \/ (t1 = TArray l h t' /\ word_type t' /\ type_wf D t')
       \/ (t1 = TNTArray l h t' /\ word_type t' /\ type_wf D t')) ->
      (m' = Unchecked -> m = Unchecked) ->
      well_typed env m e1 t2 ->
      well_typed env m e2 t2 ->
      (m' = Unchecked -> m = Unchecked) ->
      well_typed env m (EIf x e1 e2) t2.

Hint Constructors well_typed.

Lemma ptr_subtype_equiv : forall D m w t,
subtype D w (TPtr m t) ->
exists t', w = (TPtr m t').
Proof.
  intros. remember (TPtr m t) as p. generalize dependent t. induction H.
  - intros. exists t0. rewrite Heqp. reflexivity.
  - intros. exists (TArray l h t).
    assert (m0 = m). {
      inv Heqp. reflexivity. 
    }
    rewrite H1. reflexivity.
  - intros. exists (TNTArray l h t).
    assert (m0 = m). {
      inv Heqp. reflexivity. 
    }
    rewrite H1. reflexivity.
  - intros. exists (TStruct T).
    assert (m0 = m). {
      inv Heqp. reflexivity. 
    }
    rewrite H1. reflexivity.
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
  - intros. exists (TArray l' h' t).
    assert (m0 = m). {
      inv Heqp. reflexivity. 
    }
    rewrite H1. reflexivity.
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
Qed.

Lemma nat_subtype : forall D t,
subtype D TNat t ->
t = TNat.
Proof.
  intros. remember TNat as t'. induction H; eauto.
  - exfalso. inv Heqt'.
  - exfalso. inv Heqt'.
  - exfalso. inv Heqt'.
Qed.

(** ** Metatheory *)

(** *** Automation *)

(* TODO: write a function decompose : expr -> (context * expr) *)


Ltac clean :=
  try (match goal with
       | [ H : expr_wf _ _ |- _ ] => inv H
       | [ H : type_wf _ _ |- _ ] => inv H
       end);
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

Lemma step_implies_reduces : forall D H s e H' s' r,
    @step D s H e s' H' r ->
    reduces D s H e.
Proof.
  intros.
  assert (e = in_hole e CHole); try reflexivity.
  rewrite H1.
  destruct r; eauto 20.
Qed.

Hint Resolve step_implies_reduces : Progress.

Lemma reduces_congruence : forall D H s e0 e,
    (exists E, in_hole e0 E = e) ->
    reduces D s H e0 ->
    reduces D s H e.
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

(*changed THIS!! REMEMBER*)

Open Scope Z.
Lemma wf_implies_allocate_meta :
  forall (D : structdef) (w : type),
    (forall l h t, w = TArray (Num l) (Num h) t -> l = 0 /\ h > 0) ->
    (forall l h t, w = TArray (Num l) (Num h) t -> l = 0 /\ h > 0) ->
    simple_type D w -> 
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
    simple_type D w -> 
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
  omega.
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
    + omega.
    + simpl in *.
      apply IHn in H.
      omega.
Qed.

(* Progress:
     If [e] is well-formed with respect to [D] and
        [e] has type [t] under heap [H] in mode [m]
     Then
        [e] is a value, [e] reduces, or [e] is stuck in unchecked code *)
Lemma pos_succ : forall x, exists n, (Pos.to_nat x) = S n.
Proof.
   intros x. destruct (Pos.to_nat x) eqn:N.
    +zify. omega.
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
Admitted.


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


Lemma find_implies_mapsto : forall s D f,
StructDef.find (elt:=fields) s D = Some f ->
StructDef.MapsTo s f D.
Proof.
  intros. eapply StructDef.find_2. assumption.
Qed.


Lemma struct_subtype_non_empty : forall m T fs D,
subtype D (TPtr m (TStruct T)) (TPtr m TNat) ->
(StructDef.MapsTo T fs D) ->
Z.of_nat(length (map snd (Fields.elements (elt:=type) fs))) > 0.
Proof.
  intros. remember (TPtr m (TStruct T)) as p1.
  remember (TPtr m TNat) as p2. induction H.
  - exfalso. rewrite Heqp1 in Heqp2. inv Heqp2.
  - exfalso. inv Heqp1.
  - exfalso. inv Heqp1.
  - inv Heqp1. inv Heqp2. 
    assert (fs = fs0) by (eapply StructDefFacts.MapsTo_fun; eauto). 
    eapply fields_implies_length in H1. rewrite H2.
    zify. eauto. rewrite map_length. assumption.
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

Lemma lit_empty_means_cast_type_bound_same :
  forall s D H m n t t1, @well_typed D H empty_env m (ELit n t) t1 ->  cast_type_bound s t t.
Proof.
 intros. remember empty_env as env.
 remember (ELit n t) as e.
 induction H0.
 subst.
 injection Heqe.
 intros.
 rewrite <- H2.
 apply (empty_means_cast_type_bound_same s) in H0.
 assumption.
 1 - 14 : inv Heqe.
Qed.


Lemma progress : forall D H s m e t,
    structdef_wf D ->
    heap_wf D H ->
    expr_wf D e ->
    @well_typed D H empty_env m e t ->
    value D e \/
    reduces D s H e \/
    unchecked m e.
Proof with eauto 20 with Progress.
  intros D H st m e t HDwf HHwf Hewf Hwt.
  remember empty_env as env.
  induction Hwt as [
                     env m n t Wb HTyLit                                       | (* Literals *)
                     env m x t Wb HVarInEnv                                    | (* Variables *)
                     env m x e1 t1 e2 t HTy1 IH1 HTy2 IH2                   | (* Let-Expr *)
                     env m e1 e2 HTy1 IH1 HTy2 IH2                          | (* Addition *)
                     env m e m' T fs i fi ti HTy IH HWf1 HWf2               | (* Field Addr *)
                     env m w                                                | (* Malloc *)
                     env m e t HTy IH                                       | (* Unchecked *)
                     env m t e t' HChkPtr HTy IH                            | (* Cast - nat *)
                     env m t e x y u v HTy IH                               | (* Cast - ptr array *)
                     env m t e x y u v HTy IH                               | (* Cast - ptr nt-array *)
                     env m e m' w l h t t' HTy IH HSubType HPtrType HMode   | (* Deref *)
                     env m e1 m' l h t e2 t' WT Twf HTy1 IH1 HSubType HTy2 IH2 HMode     | (* Index *)
                     env m e1 m' w l h t t' e2 HTy1 IH1 HTy2 IH2 HSubType HPtrType HMode | (* Assign *)
                     env m e1 m' l h t e2 e3 t' WT Twf HTy1 IH1 HSubType HTy2 IH2 HTy3 IH3 HMode |  (* IndAssign *)
                     env m m' x t t1 e1 e2 t2 HEnv HSubType HPtrType HTy1 IH1 HTy2 IH2 HMode (* If *)
                   ]; clean.

  (* Case: TyLit *)
  - (* Holds trivially, since literals are values *)
    left...
  (* Case: TyVar *)
  - (* Impossible, since environment is empty *)
    inversion HVarInEnv.
  (* Case: TyLet *)
  - (* `ELet x e1 e2` is not a value *)
    right.
    (* Invoke the IH on `e1` *)
    destruct IH1 as [ HVal1 | [ HRed1 | HUnchk1 ] ].
    (* Case: `e1` is a value *)
    + (* We can take a step according to SLet *)
      left.  
      inv HVal1...
      apply (step_implies_reduces D H st (ELet x (ELit n t0) e2) H (Stack.add x (n, t0) st) (RExpr e2)).
      apply SLet.
      apply (lit_empty_means_cast_type_bound_same st) in HTy1.
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
    (* Invoke the IH on `e1` *)
    destruct IH1 as [ HVal1 | [ HRed1 | HUnchk1 ] ].
    (* Case: `e1` is a value *)
    + (* We don't know if we can take a step yet, since `e2` might be unchecked. *)
      inv HVal1 as [ n1 t1 ].
      (* Invoke the IH on `e2` *)
      destruct IH2 as [ HVal2 | [ HRed2 | HUnchk2 ] ].
      (* Case: `e2` is a value *)
      * (* We can step according to SPlus *)
        left.
        inv HVal2 as [ n2 t2 ]...
        eapply step_implies_reduces; eauto.
        apply SPlus.
        intros l h t Eq; subst.
        inv HTy1.
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
    (* Invoke the IH on `e` *)
    destruct IH as [ HVal | [ HRed | HUnchk ] ].
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
    (* LEO: Where is H1 created from? Match goal style for maintainability *)
    destruct (wf_implies_allocate D w H H0 H2) as [ n [ H' HAlloc]]...
  (* Case: TyUnchecked *)
  - (* `EUnchecked e` isn't a value *)
    right.
    (* Invoke the IH on `e` *)
    destruct IH as [ HVal | [ HRed | HUnchk ] ].
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
  - (* `ECast t e` isn't a value *)
    right.
    (* Invoke the IH on `e` *)
    destruct IH as [ HVal | [ HRed | HUnchk ] ].
    (* Case: `e` is a value *)
    + (* We can step according to SCast *)
      left.
      inv HVal...
    (* Case: `e` reduces *)
    + (* `ECast t e` can take a step by reducing `e` *)
      left.
      ctx (ECast t e) (in_hole e (CCast t CHole))...
    (* Case: `e` is unchecked *)
    + (* `ECast t e` must be unchecked, since `e` is *)
      right.
      ctx (ECast t e) (in_hole e (CCast t CHole)).
      destruct HUnchk...
  (* Case: TyDeref *)
  - (* `EDeref e` isn't a value *)
    right.

    (* If m' is unchecked, then the typing mode `m` is unchecked *)
    destruct m'; [> | right; eauto 20 with Progress].
    clear HMode.

    (* TODO(ins): find a way to automate everything after case analysis... *)

    (* Invoke the IH on `e` *)
    destruct IH as [ HVal | [ HRed | HUnchk ] ].
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
          assert (H3 : exists t1, w = (TPtr Checked t1)).
          { eapply ptr_subtype_equiv. eauto.
          } destruct H3. rewrite H3 in *.
          clear H3.
          (* We now proceed by case analysis on '|- n0 : ptr_C w' *)
          inversion H7.
          (* Case: TyLitZero *)
          {
           (* Impossible, since n > 0 *)
           exfalso. omega.
            (*subst. inv H2. inv H3.*)
          }
          (* Case: TyLitRec *)
          { (* Impossible, since scope is empty *)
            solve_empty_scope. }
          (* Case: TyLitC *)
          { (* We can step according to SDeref *)
            subst.
            destruct H8 with (k := 0) as [ n' [ t1' [ Ht'tk [ Hheap Hwtn' ] ] ] ].
            inv H2; subst; inv H3; unfold allocate_meta in *; destruct x;  inv H4; simpl; (try omega).
            destruct (StructDef.find s D) eqn:HFind.
            assert (Hmap : StructDef.MapsTo s f D). 
            {
             eapply find_implies_mapsto. assumption.
            }
            assert ( Z.of_nat (length (map snd (Fields.elements (elt:=type) f))) > 0). 
            {
              eapply struct_subtype_non_empty; eauto.
            }
            inv H3; zify; (try omega).
            inv H3; inv HSubType.
            inv HSubType. inv HSubType. inv HSubType.
            
            rewrite Z.add_0_r in Hheap;
            inv Ht'tk.
            left.
            eapply step_implies_reduces.
            apply SDeref; eauto.
            - destruct H2; subst.
            inv H2; simpl in *; inv H4; simpl in *; subst; eauto;                
            inv H5; repeat econstructor; eauto.
            destruct x; unfold allocate_meta in H3; inv H3;
            simpl in H4; inv H4; eauto. 
            destruct (StructDef.find (elt:=fields) s D) eqn:HFind.
             * inv H5. simpl in H3. inv HSubType.
               assert (StructDef.MapsTo s f D) by (eapply find_implies_mapsto; eauto).
               assert (f = fs) by (eapply StructDefFacts.MapsTo_fun; eauto).
               rewrite H4 in *.
               assert (Some TNat = match 
                map snd (Fields.elements (elt:=type) fs)
                with
                | nil => None
                | x :: _ => Some x
                end). 
              {
                eapply element_implies_element; eauto.
              } rewrite <- H9 in H3. inv H3. eauto.
            * inv H5.
            * inv HSubType.
            * unfold allocate_meta in H3.
              destruct x;
              inv H3; simpl in H4; inv H4; (try constructor).
              + destruct (StructDef.find (elt:=fields) s D) eqn:HFind.
                {
                  assert (StructDef.MapsTo s f D) by (eapply find_implies_mapsto; eauto).
                  inv H5. simpl in H3. inv HSubType.
                  assert (f = fs) by (eapply StructDefFacts.MapsTo_fun; eauto). 
                  rewrite H4 in *.
                  rewrite <- (element_implies_element s fs D TNat H2 H9) in H3.
                  inv H3. constructor.
                }
                {
                  inv H5.
                }
              + inv HSubType.
            * unfold allocate_meta in H3.
              destruct x;
              inv H3; simpl in H4; inv H4; (try constructor).
              + inv HSubType.
              + inv HSubType.
            * unfold allocate_meta in H3.
              destruct x;
              inv H3; simpl in H4; inv H4; (try constructor).
              + destruct (StructDef.find (elt:=fields) s D) eqn:HFind.
                {
                  assert (StructDef.MapsTo s f D) by (eapply find_implies_mapsto; eauto).
                  inv H5. simpl in H3. inv HSubType.
                }
                {
                  inv H5.
                }
              + inv HSubType.
            - intros.
              destruct H2 as [Hyp1 Hyp2].
              subst.
              inv H3.
              inv Hyp1; inv HSubType.
          }
        }
        (* Case: n <= 0 *)
        { (* We can step according to SDerefNull *)
          left. eapply step_implies_reduces.
          assert (exists w0, w = TPtr Checked w0).
          {
            inv H0. inv HSubType.
            exists w0. destruct m0.
            reflexivity. inv HSubType.
          }
          destruct H3.
          eapply SDerefNull; eauto. 
        }

      (* Case: `w` is an array pointer *)
      * destruct H2 as [Ht H2].
        assert (HArr : exists l0 h0, w = (TPtr Checked (TArray l0 h0 t))).
        {
          rewrite Ht in HSubType. inv HSubType.
          exists l; exists h; reflexivity.
          exists l0; exists h0; reflexivity.
        }
        clear Ht HSubType l h t'.
        destruct HArr as [l [h HArr]].
        rewrite HArr in *. clear HArr.
        (* We now perform case analysis on 'n > 0' *)
        destruct (Z_gt_dec n 0) as [ Hn0eq0 | Hn0neq0 ].
        (* Case: n > 0 *)
        { (* We now proceed by case analysis on '|- n0 : ptr_C (array n t)' *)
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
            (* should this also be on ' h > 0' instead? DP*)
            destruct (Z_gt_dec h 0) as [ Hneq0 | Hnneq0 ].
            (* Case: h > 0 *)
            { left. (* We can step according to SDeref *)
              (* LEO: This looks exactly like the previous one. Abstract ? *)
              subst.
              inv H4.
              destruct (Z_gt_dec l 0).

              (* if l > 0 we have a bounds error*)
              {
                eapply step_implies_reduces. eapply SDerefLowOOB. eapply g. eauto.
              }
              
              (* if l <= 0 we can step according to SDeref. *)

              assert (Hhl : h - l > 0). {
                destruct h. inv Hneq0. omega. inv Hneq0.
              }
              destruct (h - l) as [| p | ?] eqn:Hp; zify; [omega | |omega].
              simpl in *.
              rewrite replicate_length in *.
              assert (HL: l + Z.of_nat (Pos.to_nat p) = h) by (zify; omega).
              rewrite HL in *; try omega.

              destruct H8 with (k := 0) as [ n' [ t' [ Ht'tk [ Hheap Hwtn' ] ] ] ].
              { (split;  omega). }

              rewrite Z.add_0_r in Hheap.
              simpl in *.

              assert (Hp': Z.of_nat (Pos.to_nat p) = Z.pos p) by omega.
              rewrite Hp' in *; clear Hp'.
              assert (Hp': Pos.to_nat p = Z.to_nat (Z.pos p)) by (simpl; reflexivity).
              rewrite Hp' in *; clear Hp'. 

              assert (t = t').
              {
                eapply replicate_nth; eauto.
              }
              subst t'.

              eapply step_implies_reduces.
              apply SDeref; eauto.
              - repeat constructor; eauto.
              - intros l' h' t' HT.
                injection HT; intros ? ? ?; subst h l t.
                split; zify; omega.
            }
            (* Case: h <= 0 *)
            { (* We can step according to SDerefOOB *)
              subst. left. eapply step_implies_reduces. 
              eapply SDerefHighOOB. eauto. eauto.
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
  -
    right.
    destruct m'; [> | right; eauto 20 with Progress].
    clear HMode.
    (* Leo: This is becoming hacky *)
    inv H1.
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
    specialize (IH1 H3 eq_refl).
    specialize (IH2 H4 eq_refl).
    destruct IH1 as [ HVal1 | [ HRed1 | HUnchk1 ] ]; eauto.
    + inv HVal1 as [ n1 t1 ].
      destruct IH2 as [ HVal2 | [ HRed2 | HUnchk2 ] ]; eauto.
      * left.
        inv HVal2.
        ctx (EDeref (EPlus (ELit n1 t1) (ELit n t0))) (in_hole (EPlus (ELit n1 t1) (ELit n t0)) (CDeref CHole)).
        inv HTy1.
        exists Checked.
        exists st.
        exists H.
        { destruct (Z_gt_dec n1 0).
          - (* n1 > 0 *)
            exists (RExpr (EDeref (ELit (n1 + n) (TPtr Checked (TArray (l - n) (h - n) t))))).
            ctx (EDeref (ELit (n1 + n) (TPtr Checked (TArray (l - n) (h - n) t))))
                (in_hole (ELit (n1 + n) (TPtr Checked (TArray (l - n) (h - n) t))) (CDeref CHole)).
            rewrite HCtx.
            rewrite HCtx0.
            inv HTy2.
            eapply RSExp; eauto.
          - (* n1 <= 0 *)
            exists RNull.
            subst. 
            rewrite HCtx. 
            inv HTy2.
            eapply RSHaltNull; eauto.
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
  - (* This isn't a value, so it must reduce *)
    right.

    (* If m' is unchecked, then we are typing mode is unchecked *)
    destruct m'; [> | right; eauto 20 with Progress].
    clear HMode.

    (* Invoke IH on e1 *)
    destruct IH1 as [ HVal1 | [ HRed1 | [| HUnchk1 ] ] ]; idtac...
    + (* Case: e1 is a value *)
      inv HVal1 as [ n1' t1' WTt1' Ht1' ].
      (* Invoke IH on e2 *)
      inv IH2 as [ HVal2 | [ HRed2 | [| HUnchk2 ] ] ]; idtac...
      * (* Case: e2 is a value, so we can take a step *)
        inv HVal2 as [n2' t2' Wtt2' Ht2' ].
        {
          destruct HPtrType as [Hw | Hw]; eauto.
          - inv Hw; subst.
            inv HTy1; eauto.
            match goal with
            | [ H : well_typed_lit _ _ _ _ _ |- _ ] => inv H
            end... 
            + exfalso; inv HSubType.
            + exfalso; inv HSubType.
            + left.
              inv H0.
              * assert (exists t, w = (TPtr Checked t)).
                {
                  inv HSubType. exists TNat; eauto.
                  exists (TStruct T); eauto.
                }
                destruct H0.
                eapply step_implies_reduces.
                eapply SAssignNull; eauto. omega. 
              * assert (exists t, w = (TPtr Checked t)).
                {
                  inv HSubType. exists (TPtr m0 w0); eauto.
                }
                destruct H0.
                eapply step_implies_reduces.
                eapply SAssignNull; eauto. omega. 
            + solve_empty_scope.
            + left. unfold allocate_meta in H1.
              destruct w0; inv H1; simpl in *.
              ++   destruct (H2 0) as [x [xT [HNth [HMap HWT]]]]; simpl in*;
                try (zify; omega);
                try rewrite Z.add_0_r in *;
                eauto; 
              try (eapply step_implies_reduces;
                   eapply SAssign; eauto);
              try (eexists; eauto);
              intros; try congruence...
              ++  destruct (H2 0) as [x [xT [HNth [HMap HWT]]]]; simpl in*;
                try (zify; omega);
                try rewrite Z.add_0_r in *;
                eauto; 
              try (eapply step_implies_reduces;
                   eapply SAssign; eauto);
              try (eexists; eauto);
              intros; try congruence...
              ++ destruct (StructDef.find (elt:=fields) s D)eqn:Hmap; inv H4.
                inv HSubType.
                -- inv H0.
                -- destruct (H2 0) as [x [xT [HNth [HMap HWT]]]]; simpl in*;
                   try (zify; omega);
                   try rewrite Z.add_0_r in *;
                   eauto;
                   try (eapply step_implies_reduces;
                   eapply SAssign; eauto);
                   try (eexists; eauto);
                   intros; try congruence... omega.
                   rewrite map_length. apply find_implies_mapsto in Hmap.
                   assert (f = fs) by (eapply StructDefFacts.MapsTo_fun; eauto). 
                   rewrite H1 in *.
                   assert (((length (Fields.elements (elt:=type) fs)) > 0)%nat) by (eapply fields_implies_length; eauto).
                   zify; omega.
              ++ inv HSubType; inv H0.
          - inv HTy1; eauto.
            match goal with
            | [ H : well_typed_lit _ _ _ _ _ |- _ ] => inv H
            end...
            + exfalso; inv HSubType.
            + exfalso; inv HSubType.
            + left.
              destruct Hw as [? [? ?]]; subst.
              assert (exists l0 h0, w = (TPtr Checked (TArray l0 h0 t))).
              {
                inv HSubType. exists l; exists h; eauto.
                exists l0; exists h0; eauto.
              }
              clear HSubType l h. 
              destruct H0 as [l [h H0]].
              rewrite H0 in *.
              clear H0. 
              destruct (Z_gt_dec h 0).
              * (* h > 0 - Assign  *)
                destruct (Z_gt_dec l 0).
                { (* l > 0 *)
                eapply step_implies_reduces.
                eapply SAssignLowOOB; eauto... inv HTy2. eauto. }
                { (* l <= 0 *)
                  eapply step_implies_reduces.
                  eapply SAssignNull; eauto. omega.
                  
                }
              * (* h <= 0 *)
                eapply step_implies_reduces.
                eapply SAssignHighOOB; eauto... inv HTy2. eauto.
            + solve_empty_scope.
            + left.
              destruct Hw as [? [? ?]]; subst.
              assert (exists l0 h0, w0 = (TArray l0 h0 t)).
              {
                inv HSubType. exists l; exists h; eauto.
                exists l0; exists h0; eauto.
              }
              clear HSubType l h. 
              destruct H2 as [l [h H2]].
              rewrite H2 in *.
              clear H2.
              destruct (Z_gt_dec n1' 0).
                ++ destruct (Z_gt_dec h 0).
                    * (* h > 0 - Assign  *)
                      destruct (Z_gt_dec l 0).
                      { (* l > 0 *)
                      eapply step_implies_reduces.
                      eapply SAssignLowOOB; eauto... inv HTy2. eauto. }
                      { (* l <= 0 *)
                        eapply step_implies_reduces.
                        eapply SAssign; eauto.
                        destruct (H1 0). unfold allocate_meta in H0.
                        inv H0. 
                        assert (Hmin : h - l > 0) by omega.
                        assert (Hpos : exists p, h - l = Z.pos p).
                        {
                          destruct (h - l); inv Hmin.
                          exists p; eauto.
                        }
                        destruct Hpos as [p Hpos].
                        rewrite Hpos. simpl.
                        rewrite replicate_length.
                        zify; omega.
                        rewrite Z.add_0_r in H2.
                        destruct H2 as [? [? [? ?]]].
                        assert (Heap.find n1' H = Some (x, x0)) by (eapply Heap.find_1; assumption).
                        eapply HeapProp.F.in_find_iff. 
                        rewrite H7. intros Hs. inv Hs.
                        intros l0 h0 t' Heq; inv Heq; zify; omega. 
                      }
                    * (* h <= 0 *)
                      eapply step_implies_reduces.
                      eapply SAssignHighOOB; eauto... inv HTy2. eauto.
              ++ destruct (Z_gt_dec h 0).
                 * (* h > 0 - Assign  *)
                   destruct (Z_gt_dec l 0).
                   { (* l > 0 *)
                   eapply step_implies_reduces.
                   eapply SAssignLowOOB; eauto... inv HTy2. eauto. }
                   { (* l <= 0 *)
                     eapply step_implies_reduces.   
                     eapply SAssignNull; eauto.
                   }
                 * (* h <= 0 *)
                   eapply step_implies_reduces.
                   eapply SAssignHighOOB; eauto... inv HTy2. eauto.
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
  (* T-IndAssign *)
  - (* This isn't a value, so it must reduce *)
    right.

    (* If m' is unchecked, then we are typing mode is unchecked *)
    destruct m'; [> | right; eauto 20 with Progress].
    clear HMode.

    inv H2.
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
    (* Invoke IH on e1 *)
    destruct IH1 as [ HVal1 | [ HRed1 | [| HUnchk1 ] ] ]; idtac...
    + (* Case: e1 is a value *)
      inv HVal1.
      (* Invoke IH on e2 *)
      destruct IH2 as [ HVal2 | [ HRed2 | [| HUnchk2 ] ] ]; idtac...
      * inv HVal2.
        ctx (EAssign (EPlus (ELit n t0) (ELit n0 t1)) e3) (in_hole (EPlus (ELit n t0) (ELit n0 t1)) (CAssignL CHole e3)).
        inv HTy1.
        inv HTy2.
        {
          inv H11; inv H12; (eauto 20 with Progress); 
            try solve_empty_scope.
          - destruct IH3 as [ HVal3 | [ HRed3 | [| HUnchk3]]]; idtac...
            + inv HVal3.
              inv HTy3.
              left; eauto...
              destruct (Z_gt_dec n 0); subst; rewrite HCtx; do 4 eexists.
              * eapply RSHaltNull... eapply SPlusNull. omega.
              * eapply RSHaltNull... eapply SPlusNull. omega.
            + destruct HRed3 as [H' [? [r HRed3]]].
              rewrite HCtx; left; do 4 eexists.
              eapply RSHaltNull... eapply SPlusNull. omega. 
            + destruct HUnchk3 as [ e' [ E [ He2 HEUnchk ]]]; subst.
              rewrite HCtx; left; do 4 eexists.
              * eapply RSHaltNull... eapply SPlusNull. omega.
          - destruct IH3 as [ HVal3 | [ HRed3 | [| HUnchk3]]]; idtac...
            + inv HVal3.
              inv HTy3.
              destruct (Z_gt_dec n 0); rewrite HCtx; left; do 4 eexists.
              * eapply RSHaltNull... eapply SPlusNull. omega.
              * eapply RSHaltNull... eapply SPlusNull. omega.
            + destruct HRed3 as [H' [? [r HRed3]]].
              rewrite HCtx; left; do 4 eexists.
              * eapply RSHaltNull... eapply SPlusNull. omega.
            + destruct HUnchk3 as [ e' [ E [ He2 HEUnchk ]]]; subst.
              rewrite HCtx; left; do 4 eexists.
              * eapply RSHaltNull... eapply SPlusNull. omega.
          - destruct (Z_gt_dec n 0); rewrite HCtx; left; do 4 eexists.
              * eapply RSExp. eapply SPlusChecked. omega. eauto.
              * eapply RSHaltNull. eapply SPlusNull. omega. eauto.
          -  destruct (Z_gt_dec n 0); rewrite HCtx; left; do 4 eexists.
              * eapply RSExp. eapply SPlusChecked. omega. eauto.
              * eapply RSHaltNull. eapply SPlusNull. omega. eauto.
        }
      * destruct HRed2 as [ H' [ ? [? [ r HRed2 ] ] ] ].
        inv HRed2; ctx (EAssign (EPlus (ELit n t0) (in_hole e E)) e3) (in_hole e (CAssignL (CPlusR n t0 E) e3))...
      * destruct HUnchk2 as [ e' [ E [ He2 HEUnchk ] ] ]; subst.
        ctx (EAssign (EPlus (ELit n t0) (in_hole e' E)) e3) (in_hole e' (CAssignL (CPlusR n t0 E) e3))...
    + destruct HRed1 as [ H' [? [ ? [ r HRed1 ] ] ] ].
      inv HRed1; ctx (EAssign (EPlus (in_hole e E) e2) e3) (in_hole e (CAssignL (CPlusL E e2) e3))...
    + destruct HUnchk1 as [ e' [ E [ He1 HEUnchk ] ] ]; subst.
      ctx (EAssign (EPlus (in_hole e' E) e2) e3) (in_hole e' (CAssignL (CPlusL E e2) e3))...
Qed.


(* ... for Preservation *)

Lemma weakening : forall D H env m n t,
    @well_typed D H env m (ELit n t) t ->
    forall x t', @well_typed D H (Env.add x t' env) m (ELit n t) t.
Proof.
  intros D H env m e t HWT.
  inv HWT; clear H3.
  inv H5; eauto.
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

Lemma equiv_env_wt : forall D H env1 env2 m e t,
    Env.Equal env1 env2 ->
    @well_typed D H env1 m e t ->
    @well_typed D H env2 m e t.
Proof.
  intros.
  generalize dependent env2.
  induction H1; eauto 20.
  - intros.
    apply TyVar.
    unfold Env.Equal in H1.
    apply Env.find_2.
    rewrite <- H1.
    apply Env.find_1.
    assumption.
  - intros.
    eapply TyLet.
    apply IHwell_typed1.
    assumption.
    apply IHwell_typed2.
    apply equiv_env_add.
    auto.
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

Lemma heapWF :
  forall D H H' env m e t,
    @well_typed D H env m e t ->
    @heap_consistent D H' H ->
    @well_typed D H' env m e t.
Proof.
  intros D H H' env m e t WT HC.
  generalize dependent H'.
  induction WT; intros; eauto.
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
  - omega.
  - destruct k; simpl.
    + exists a; eauto.
    + assert (H: 0 <= Z.of_nat(k) < Z.of_nat(S k)). {split.
      *omega. 
      *zify. omega. }
     destruct H. assert (H2: Z.of_nat(k) < Z.of_nat (length l)). {zify. omega. }
     assert (H3: 0 <= Z.of_nat(k) < Z.of_nat (length l)). {split; assumption. }
     apply (IHl k H3).
Qed.      

Lemma nth_length : forall {A} (l : list A) (k : nat) n,
    nth_error l k = Some n -> 0 <= Z.of_nat(k) < Z.of_nat(length l).
Proof.
  intros A l; induction l; intros k n Hyp; simpl in *.
  - apply nth_error_In in Hyp; inv Hyp.
  - destruct k; simpl in *.
    +zify. omega.
    + edestruct IHl; eauto. zify.
      omega.
Qed.

Require Import Coq.Program.Equality.
  
Lemma heap_wf_maps_nonzero : forall D H n v, heap_wf D H -> Heap.MapsTo n v H -> n <> 0.
Proof.
  intros D H n v Hwf HMap.
  destruct (Hwf n) as [ _ HIn ]. 
  destruct n; eauto.
    -exfalso. destruct HIn; try eexists; eauto; 
     inversion H0.
    -zify. omega.
    -zify. omega.
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
  intros D H Hwf Contra.
  destruct (Hwf (Z.of_nat(Heap.cardinal H) + 1)) as [H1 H2].
  specialize (H2 Contra).
  omega.
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
    omega.
  + inv HWT; eauto.
Qed.


  
Lemma heap_add_preserves_wf : forall D H n v, heap_wf D H ->
  heap_wf D (Heap.add (Z.of_nat(Heap.cardinal H) + 1) (n, v) H).
Proof.
  intros D H n v Hwf.
  split; intros; simpl; eauto.
  * rewrite cardinal_plus_one in H0.
    - assert (Hyp: 0 < addr <= Z.of_nat(Heap.cardinal H) \/ addr = Z.of_nat(Heap.cardinal H) + 1). {zify. omega. } 
      inv Hyp.
      + destruct (Hwf addr) as [ HIn _ ].
        specialize (HIn H1).
        inv HIn. exists x.
        apply Heap.add_2; eauto.
        omega.
      + eexists; eapply Heap.add_1; eauto.
    - intros Contra.
      destruct (Hwf (Z.of_nat(Heap.cardinal H) + 1)) as [? ?].
      specialize (H2 Contra).
      omega.
  * apply HeapFacts.add_in_iff in H0.
    inv H0.
    - rewrite cardinal_plus_one; try (zify; omega).
      intro Contra.
      destruct (Hwf (Z.of_nat(Heap.cardinal H) + 1)) as [? ?].
      specialize (H1 Contra).
      omega.
    - rewrite cardinal_plus_one.
      + destruct (Hwf addr) as [_ H2]; specialize (H2 H1); zify; omega.
      + intro Contra.
        destruct (Hwf (Z.of_nat(Heap.cardinal H) + 1)) as [H2 H3].
        specialize (H3 Contra).
        omega.
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
    destruct Hyp; [eexists; eauto | omega].
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
    omega.
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
   
  assert (Z.of_nat(Heap.cardinal H) + 1 + 1 = Z.of_nat((Heap.cardinal H + 1)) + 1) by (zify; omega).
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
      omega.
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

  assert (Z.of_nat(Heap.cardinal H) + 1 + 1 = ((Z.of_nat(Heap.cardinal H)) + 1) + 1) by omega.
  (*rewrite H1 in IHl.*)
  destruct (IHl eq_refl) as [hwf [Card [Card' [HField HMap]]]].

  repeat (split; eauto).
  + omega.
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
      zify. omega. }
      rewrite HS.
      apply HField; eauto.
      omega.
  + intros x v HM.
    eapply HMap.
    apply Heap.add_2; eauto.
    intro Contra.
    destruct (Hwf x) as [_ Contra'].
    destruct Contra'; [eexists; eauto | ].
    omega.
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

Lemma alloc_correct : forall w D env H ptr H',
    allocate D H w = Some (ptr, H') ->
    structdef_wf D ->
    heap_wf D H ->
    @heap_consistent D H' H /\
    @well_typed D H' env Checked (ELit ptr (TPtr Checked w)) (TPtr Checked w) /\
    heap_wf D H'.
Proof.
  intros w D env H ptr H' Alloc HSd HWf.
  unfold allocate in *.
  unfold allocate_meta in *.
  unfold bind in *; simpl in *.
  destruct w; simpl in *; eauto; inv Alloc; simpl in *; eauto.
  - split; [| split].
    * apply well_typed_preserved; eauto.
    * apply TyLit; eauto.
      eapply TyLitC; simpl; eauto.
      intros k HK.
      simpl in HK.
      assert (k = 0) by omega; subst; clear HK.
      exists 0. exists TNat.
      repeat split; eauto.
      apply Heap.add_1; eauto. omega.
    * apply heap_add_preserves_wf; auto.
  - split; [ | split].
    * apply well_typed_preserved; eauto.
    * apply TyLit; eauto.
      eapply TyLitC; simpl; eauto.
      intros k HK.
      simpl in HK.
      assert (k = 0) by omega; subst; clear HK.
      exists 0. exists (TPtr m w).
      repeat split; eauto.
      apply Heap.add_1; eauto. omega.
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
      eapply TyLitC; simpl in *; eauto; [ rewrite Find | ]; eauto.

      intros k HK.
      apply StructDef.find_2 in Find.
      remember Find as Fwf; clear HeqFwf.
      apply HSd in Fwf.

      assert (HOrd: 0 < Z.of_nat(Heap.cardinal H) + 1 + k <= Z.of_nat(Heap.cardinal H')) by omega.
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
          +zify. simpl. assumption.
          +simpl. zify. omega.
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
    * unfold allocate in H1.
      unfold allocate_meta_no_bounds, allocate_meta in H1.
      simpl in H1.

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
    * unfold allocate in H1.
      unfold allocate_meta_no_bounds, allocate_meta in H1.
      simpl in *.

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
      eapply TyLitC; simpl in *; eauto.
      intros k HK.
      simpl in *.
      pose proof (H'wf (Z.of_nat(Heap.cardinal H) + 1 + k)) as Hyp.
      rewrite Z.sub_0_r in *.

      remember (Heap.cardinal H ) as c.
      remember (Heap.cardinal H') as c'.
      
      assert (HOrd : 0 < Z.of_nat c + 1 + k <= Z.of_nat c')
        by (zify; omega).
      
      destruct Hyp as [HIn Useless].
      destruct (HIn HOrd) as [[n' t'] HM'].

      destruct HK as [HP1 HP2].

      destruct z0 as [ | p | ?]; simpl in *; [ omega | | omega].
      rewrite replicate_length in *.

      destruct (length_nth (replicate (Pos.to_nat p) w) (Z.to_nat k)) as [t Hnth].
      { rewrite replicate_length ; zify; split; try omega. 
        (*This should go through with omega but it doesn't*)
        assert (Hk : Z.of_nat (Z.to_nat k) = k). {
        destruct k; simpl.
          + reflexivity.
          + zify. omega.
          + exfalso. zify. apply HP1. simpl. reflexivity. }
        rewrite Hk. assumption.
      }

      rewrite Z.sub_0_r in *.
      
      rewrite Hnth.
      remember Hnth as Hyp; clear HeqHyp.
      apply replicate_nth in Hnth. rewrite Hnth in *; clear Hnth.
        
      exists n'; exists t.
      split; [ reflexivity | ].

      specialize (HF (Z.to_nat k) t).
      assert (HF1 : (0 <= Z.to_nat k < Pos.to_nat p)%nat). {
        split; zify; (try omega). destruct k; simpl; zify; omega.
      }

      specialize (HF HF1 Hyp).

      assert (HId: Z.of_nat (Z.to_nat k) = k). {
        destruct k; simpl.
          + reflexivity.
          + zify. omega.
          + exfalso. zify. omega. }
      rewrite HId in HF.
      
      pose proof (HeapFacts.MapsTo_fun HM' HF) as Eq.
      inv Eq.
      split; auto.
Qed.

Lemma values_are_nf : forall D H s e,
    value D e ->
    ~ exists H' s' m r, @reduce D s H e m H' s' r.
Proof.
  intros D H s e Hv contra.
  inv Hv.
  destruct contra as [H' [ m [ s' [ r contra ] ] ] ].
  inv contra; destruct E; inversion H4; simpl in *; subst; try congruence.
Qed.

Lemma lit_are_nf : forall D H s n t,
    ~ exists H'  s' m r, @reduce D s H (ELit n t) m s' H' r.
Proof.
  intros D s H n t contra.
  destruct contra as [H' [ s' [ m [ r contra ] ] ] ].
  inv contra; destruct E; inversion H2; simpl in *; subst; try congruence.
Qed.

Lemma var_is_nf : forall D s H x,
    ~ exists H' s' m r, @reduce D s H (EVar x) m s' H' r.
Proof.
  intros.
  intros contra.
  destruct contra as [H' [ m [s' [ r contra ] ] ] ].
  inv contra; destruct E; inversion H1; simpl in *; subst; inv H2.
Admitted.


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
    apply set_add_intro1; eauto. assumption.
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
    right; eauto. assumption.
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
  - assert (subtype D t t').
    {
      inv H1; inv H2.
      * eapply SubTyRefl.
      * eapply SubTySubsume; eauto.
      * eapply SubTyStructArrayField; eauto.
      * eapply SubTySubsume; eauto.
      * eapply SubTySubsume; eauto; omega.
      * eapply SubTyStructArrayField; eauto.
    }
    assert (exists t0, t' = (TPtr Checked t0)) by (inv H1; eauto).
    destruct H4. rewrite H4 in *.
    eapply TyLitRec; eauto.
  - assert (exists t0, t' = (TPtr Checked t0)) by (inv H1; eauto).
    unfold allocate_meta in H0.
    induction w.
    * inv H1. eapply TyLitC; eauto.
    * inv H1. eapply TyLitC; eauto.
    * inv H1. eapply TyLitC; eauto.
      eapply TyLitC; eauto.
      unfold allocate_meta; eauto.
      simpl in H0. destruct (StructDef.find (elt:=fields) s0 D) eqn:Hf.
      + inv H0. rewrite map_length in H2.
        assert (StructDef.MapsTo s0 f D) by (eapply find_implies_mapsto; eauto).
        assert (f = fs) by (eapply StructDefFacts.MapsTo_fun; eauto). 
        rewrite H1 in *.
        assert (((length (Fields.elements (elt:=type) fs)) >= 1)%nat) by (eapply fields_implies_length; eauto).
        intros. simpl in H5.
        destruct (H2 k). zify. omega.
        exists x. exists TNat.
        assert (k = 0) by (destruct k; inv H5; eauto; exfalso; zify; omega).
        rewrite H9 in *. simpl. split; eauto.
        destruct H7. destruct H7.
        simpl in H7. 
        rewrite <- (element_implies_element s0 fs D TNat H0 H8) in H7.
        inv H7. destruct H10.
        split. assumption. eauto.
      + inv H0.
    * clear IHw. inv H0.
      inv H1. clear H3. 
        + eapply TyLitC; eauto.
          unfold allocate_meta; eauto.
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
   (*             -- Search nth_error.
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
      destruct (type_eq_dec tm t).
      * subst. 
        apply scope_weakening'; eauto.
        eapply subtype_well_type; eauto.
      * econstructor; eauto.
        apply set_remove_all_intro; eauto.
        intro Contra; inv Contra. eauto.
    + econstructor.
      apply set_remove_all_intro; eauto.
      congruence. assumption.
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
  - inv H1.
  - destruct (H4  (Z.of_nat i)) as [N' [T' [HNth [HMap HWT']]]]; subst.
    + simpl in H1.
      destruct (StructDef.find T D) eqn:Find; try congruence.
      inv H1.
      rewrite map_length.
      apply StructDef.find_2 in Find.
      assert (f = fs).
      { eapply StructDefFacts.MapsTo_fun; eauto. }
      subst.
      apply nth_length in Hnth.
      rewrite <- Fields.cardinal_1.
      eauto.
    + simpl in *.
      destruct (@StructDef.find _ T D) eqn:Find; try congruence.
      inv H1.

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
          +simpl. zify. omega. }
      simpl in *.
      rewrite Z.sub_0_r in *. rewrite Hi in HNth.
      rewrite <- HNth in Hnth'.
      inv Hnth'.
      inv Hwt.
      * eapply TyLitC; simpl in *; eauto.
        intros k Hk; simpl in *.
        assert (k = 0) by omega; subst.
        exists N'. exists TNat.
        repeat (split; eauto).
        rewrite Z.add_0_r; eauto.
      * eapply TyLitC; simpl in *; eauto.
        intros k Hk; simpl in *.
        assert (k = 0) by omega; subst.
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
    apply set_add_intro; eauto. assumption.
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
        apply set_add_intro2; auto. eapply SubTyRefl.
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
    Heap.MapsTo i (n, T) H ->
    @well_typed_lit D H empty_scope n' T ->
    @well_typed_lit D (Heap.add i (n',T) H) empty_scope n' T.
Proof.
  intros i n T H D n' Hwf HMap HWT.
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
      apply set_add_intro2; auto. eapply SubTyRefl.
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
    omega.
  - inv H1.
  - inv Hwt; simpl in *; inv H1.
    + destruct (H4 0) as [n' [t' [HNth [HMap HWT]]]]; auto.
      *simpl. omega.
      *
      rewrite Z.add_0_r in HMap.
      inv HNth.
      exists n'; eauto.
    + destruct (H4 0) as [n' [t' [HNth [HMap HWT]]]]; auto.
      *simpl. omega.
      *rewrite Z.add_0_r in HMap.
       inv HNth.
       exists n'; eauto.
Qed.

Lemma well_typed_heap_in_array : forall n D H l h w,
  heap_wf D H ->
  Heap.In n H ->
  h > 0 ->
  l <= 0 ->
  @well_typed_lit D H empty_scope n (TPtr Checked (TArray l h w)) ->
  exists x, Heap.MapsTo n (x, w) H.
Proof.
  intros n D H l h w Hwf HIn Hl Hh HWT.
  inv HWT.
  - destruct (Hwf 0) as [_ Contra].
    apply Contra in HIn.
    omega.
  - inv H1.
  - inv H1.
    destruct l.
    + destruct (H4 0) as [n' [t' [HNth [HMap HWT]]]]; auto.
      * simpl. destruct h; inv Hl. simpl.
        assert (Hyp : exists s, Pos.to_nat(p) = S s).
        { apply pos_succ. }
        inv Hyp.
        rewrite replicate_length.
        simpl. omega.
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
    + zify; omega.
    + assert (H1: (h - (Z.neg p)) > 0) by (zify; omega).
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
        * zify. omega.
        * rewrite Z.pos_sub_gt. 
          { zify. omega. }
          { zify. omega. }
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

  Inductive stack_wf D H : env -> stack -> Prop :=
  | WFS_Stack : forall env s,
     (forall x t m,
         Env.MapsTo x t env <->
         exists v, lookup x s = Some ( v, t) /\
         @well_typed D H env m (ELit v t) t) ->
     stack_wf D H env s.


  Lemma in_stack : forall s x x0 v v0,
  x <> x0  ->
  lookup x0 (Stack (x, v) s) = Some v0 ->
  lookup x0 s = Some v0.
  Proof.
    intros s x x0 v v0 He Hlook. simpl in Hlook.
    destruct (var_eq_dec x0 x). rewrite e in He.
    exfalso. apply He. reflexivity. assumption.
  Qed.

 Lemma in_stack2 : forall s x x0 v v0,
  x <> x0  ->
  lookup x0 s = Some v0 ->
  lookup x0 (Stack (x, v) s) = Some v0.
  Proof.
    intros s x x0 v v0 He Hlook. simpl.
    destruct (var_eq_dec x0 x).
    rewrite e in He.
    exfalso. apply He. reflexivity. assumption.
  Qed.

  
  Lemma new_sub : forall D H env s v t1 x,
      stack_wf D H env s ->
      @well_typed D H env Checked (ELit v t1) t1 ->
      stack_wf D H (Env.add x t1 env) (Stack (x, (v, t1)) s).
  Proof.
    intros D H env s v t1 x Hwf Hwt.
    eapply WFS_Stack. intros x0 t m0. split. 
    + intros Hmap. destruct (var_eq_dec x x0).
      * simpl. rewrite e in *. exists v.
        apply env_maps_add in Hmap. rewrite Hmap in *.
        split.
        - destruct (var_eq_dec x0 x0). reflexivity.
          exfalso. apply n. reflexivity.
        - inv Hwt. eapply TyLit. assumption.
      * apply (Env.add_3 n) in Hmap. 
        inv Hwf. destruct (H0 x0 t m0) as [Hl Hr].
        apply Hl in Hmap. destruct Hmap as [v0 [Hlookup Hwt2]].
        exists v0. split. apply (in_stack2 s x x0 (v, t1) (v0, t) n Hlookup).
        inv Hwt2. apply TyLit. assumption.
    + intros H1. destruct H1 as [v0 [Hlookup Hwt2]].
      inv Hwf. simpl in Hlookup.
      destruct (var_eq_dec x0 x).
      * rewrite e. inv Hlookup.
        apply Env.add_1. reflexivity. 
      * assert (Hwt3 : @well_typed D H env m0 (ELit v0 t) t). 
        { inv Hwt2. apply TyLit. assumption. }
        assert (Hmap : Env.MapsTo x0 t env). {
          eapply H0. exists v0. split; (try  assumption); apply Hwt3.
        }
        apply not_eq_sym in n.
        apply Env.add_2; assumption. 
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
      env_consistent (Env.add x t e) e.


  Lemma consistent_typing : forall env env' x t1 e t D H H',
      env_consistent env' env ->
      @heap_consistent D H H' ->
      Env.find x env = None ->
      @well_typed D H (Env.add x t1 env) Checked e t ->
      @well_typed D H' env' Checked e t.
  Proof.
    intros env env' x t' e t D H H' Henv Hheap Hfind Hwt.
    
             
Lemma preservation : forall D s H env e t s' H' e',
    @structdef_wf D ->
    heap_wf D H ->
    expr_wf D e ->
    stack_wf D H env s ->
    @well_typed D H env Checked e t ->
    @reduce D s H e Checked s' H' (RExpr e') ->
    exists env',
      env_consistent env' env /\ stack_wf D H env' s' /\
      @heap_consistent D H' H /\ @well_typed D H' env' Checked e' t.
Proof with eauto 20 with Preservation.
  intros D s H env e t s' H' e' HDwf HHwf HEwf HSwf Hwt.
  generalize dependent H'. generalize dependent e'.
  remember Checked as m.
  induction Hwt as [
                    env m n t HTyLit                                      | (* Literals *)
                    env m x t HVarInEnv                                   | (* Variables *)
                    env m x e1 t1 e2 t HTy1 IH1 HTy2 IH2                  | (* Let-Expr *)
                    env m e m' T fs i fi ti HTy IH HWf1 HWf2              | (* Field Addr *)
                    env m e1 e2 HTy1 IH1 HTy2 IH2                         | (* Addition *)
                    env m w                                               | (* Malloc *)
                    env m e t HTy IH                                      | (* Unchecked *)
                    env m t e t' HChkPtr HTy IH                           | (* Cast *)
                    env m e m' w l h t t' HTy IH HSubType HPtrType HMode  | (* Deref *)
                    env m e1 m' l h t e2 t' WT Twf HTy1 IH1 HSubType HTy2 IH2 HMode | (* Index *)
                    |
                    ]; intros e' H' Hreduces; subst.
  (* T-Lit, impossible because values do not step *)
  - exfalso. eapply lit_are_nf...
  (* T-Var *)
  - exfalso. eapply var_is_nf...
  (* T-Let *)
  - inv Hreduces.
    destruct E; inversion H1; simpl in *; subst.
    + clear H0. clear H9. rename e'0 into e'.
      inv H5. exists (Env.add x t0 env). inv HEwf.
      assert (Ht : t0 = t1). {
        inv HTy1. reflexivity.
      } rewrite Ht in *. clear Ht.
      assert (stack_wf D H' (Env.add x t1 env) (Stack (x, (n, t1)) s)) by
          apply (new_sub D H' env s n t1 x HSwf HTy1).
      split; (try assumption); eauto. econstructor. 
    + clear H1. edestruct IH1... inv HEwf; eauto. (* Uses heap_wf *)
      exists x0. destruct H0 as [He [Hs' [Hh Hwt]]]. split. eauto. split.
      eauto. split. eauto. inv HEwf. econstructor. inv He.
      * econstructor; eauto. apply HTy2.
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
        unfold unchecked in H0.
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
