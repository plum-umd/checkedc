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

Inductive mode : Set :=
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

Inductive type : Set :=
  | TNat : type
  | TPtr : mode -> type -> type
  | TStruct : struct -> type
  | TArray : Z -> Z -> type -> type.

(** Word types, <<t>>, are either numbers, [WTNat], or pointers, [WTPtr].
    Pointers must be annotated with a [mode] and a (compound) [type]. *)

Inductive word_type : type -> Prop :=
  | WTNat : word_type TNat
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

Inductive type_wf (D : structdef) : type -> Prop :=
  | WFTNat : type_wf D TNat
  | WFTPtr : forall m w, type_wf D (TPtr m w)
  | WFTStruct : forall T,
      (exists (fs : fields), StructDef.MapsTo T fs D) ->
      type_wf D (TStruct T)
  | WFArray : forall l h t,
      word_type t ->
      type_wf D t ->
      type_wf D (TArray l h t).

Definition fields_wf (D : structdef) (fs : fields) : Prop :=
  forall f t,
    Fields.MapsTo f t fs ->
    word_type t /\ type_wf D t.

Definition structdef_wf (D : structdef) : Prop :=
  forall (T : struct) (fs : fields),
    StructDef.MapsTo T fs D ->
    fields_wf D fs.

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

Inductive expression : Set :=
  | ELit : nat -> type -> expression
  | EVar : var -> expression
  | ELet : var -> expression -> expression -> expression
  | EMalloc : type -> expression
  | ECast : type -> expression -> expression
(*???? EMinus?*)
  | EPlus : expression -> expression -> expression
  | EFieldAddr : expression -> field -> expression
  | EDeref : expression -> expression
  | EAssign : expression -> expression -> expression
  | EUnchecked : expression -> expression.

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
  VLit : forall (n : nat) (t : type),
    word_type t ->
    type_wf D t ->
    value D (ELit n t).

Hint Constructors value.

(** Note: Literal is a less strong version of value that doesn't
    enforce the syntactic constraints on the literal type. *)

Inductive literal : expression -> Prop :=
  Lit : forall (n : nat) (t : type),
    literal (ELit n t).

Hint Constructors literal.

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
    the allocated region and [H'] is [H] with the allocation. *)


Module Heap := Map.Make Nat_as_OT.

Definition heap : Type := Heap.t (Z * type).

Definition heap_wf (D : structdef) (H : heap) : Prop :=
  forall (addr : Z), 0 < addr <= (Heap.cardinal H) <-> Heap.In addr H.

Section allocation.

Import ListNotations.
Import MonadNotation.
Local Open Scope monad_scope.

(*???should you be able to allocate backwards?*)


Definition to_nat (z:Z) : nat :=
  match z with
    | pos p => Pos.to_nat p
    | _ => O
  end.

Definition allocate_meta (D : structdef) (w : type) : option (list type) :=
  match w with
  | TStruct T =>
    fs <- StructDef.find T D ;;
       ret (List.map snd (Fields.elements fs))
  | TArray 0 0 T => None
  | TArray 0 h T => Some (replicate (to_nat h) T)
  | _ => Some [w]
  end.

Definition allocate (D : structdef) (H : heap) (w : type) : option (nat * heap) :=
  let H_size := Heap.cardinal H in
  let base   := H_size + 1 in
  am <- allocate_meta D w ;;
     let (_, H') := List.fold_left
                  (fun (acc : nat * heap) (t : type) =>
                     let (sizeAcc, heapAcc) := acc in
                     let sizeAcc' := sizeAcc + 1 in
                     let heapAcc' := Heap.add sizeAcc' (0, t) heapAcc in
                     (sizeAcc', heapAcc'))
                  am
                  (H_size, H)
     in
     ret (base, H').

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
  | CPlusR : nat -> type -> context -> context
  | CFieldAddr : context -> field -> context
  | CCast : type -> context -> context
  | CDeref : context -> context
  | CAssignL : context -> expression -> context
  | CAssignR : nat -> type -> context -> context
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

Inductive step (D : structdef) : heap -> expression -> heap -> result -> Prop :=
  | SPlusChecked : forall H n1 h l t n2,
      n1 <> 0 ->
      step D
        H (EPlus (ELit n1 (TPtr Checked (TArray l h t))) (ELit n2 TNat))
        H (RExpr (ELit (n1 + n2) (TPtr Checked (TArray (l - n2) (h - n2) t))))
 | SMinusChecked : forall H n1 h l t n2,
      n1 <> 0 ->
      step D
        H (EPlus (ELit n1 (TPtr Checked (TArray l h t))) (ELit n2 TNat))
        H (RExpr (ELit (n1 - n2) (TPtr Checked (TArray (l + n2) (h + n2) t))))
  | SPlus : forall H n1 t1 n2 t2,
      (forall l h t, t1 <> TPtr Checked (TArray l h t)) -> 
      step D
        H (EPlus (ELit n1 t1) (ELit n2 t2))
        H (RExpr (ELit (n1 + n2) t1))
  | SPlusNull : forall H l h t n2 ,
      step D
        H (EPlus (ELit 0 (TPtr Checked (TArray l h t))) (ELit n2 TNat))
        H RNull
  | SCast : forall H t n t',
      step D
        H (ECast t (ELit n t'))
        H (RExpr (ELit n t))
  | SDeref : forall H n n1 t1 t,
      (expr_wf D (ELit n1 t1)) ->
      Heap.MapsTo n (n1, t1) H ->
      (forall l h t', t = TPtr Checked (TArray l h t') -> h > 0 /\ l <= 0) ->
      step D
        H (EDeref (ELit n t))
        H (RExpr (ELit n1 t1))
  | SDerefOOB : forall H n t t1,
      t = TPtr Checked (TArray 0 0 t1) ->
      step D
        H (EDeref (ELit n t))
        H RBounds
  | SAssign : forall H n t n1 t1 H',
      Heap.In n H ->
      (forall l h t', t = TPtr Checked (TArray l h t') -> h > 0 /\ l <= 0) -> 
      H' = Heap.add n (n1, t1) H ->
      step D
        H  (EAssign (ELit n t) (ELit n1 t1))
        H' (RExpr (ELit n1 t1))
  | SFieldAddrChecked : forall H n t (fi : field) n0 t0 T fs i fi ti,
      n <> 0 ->
      t = TPtr Checked (TStruct T) ->
      StructDef.MapsTo T fs D ->
      Fields.MapsTo fi ti fs ->
      List.nth_error (Fields.this fs) i = Some (fi, ti) ->
      n0 = n + i ->
      t0 = TPtr Checked ti ->
      word_type ti ->
      step D
        H (EFieldAddr (ELit n t) fi)
        H (RExpr (ELit n0 t0))
  | SFieldAddrNull : forall H (fi : field) T,
      step D
        H (EFieldAddr (ELit 0 (TPtr Checked (TStruct T))) fi)
        H RNull
  | SFieldAddr : forall H n t (fi : field) n0 t0 T fs i fi ti,
      t = TPtr Unchecked (TStruct T) ->
      StructDef.MapsTo T fs D ->
      Fields.MapsTo fi ti fs ->
      List.nth_error (Fields.this fs) i = Some (fi, ti) ->
      n0 = n + i ->
      t0 = TPtr Unchecked ti ->
      word_type ti ->
      step D
        H (EFieldAddr (ELit n t) fi)
        H (RExpr (ELit n0 t0))
  | SMalloc : forall H w H' n1,
      allocate D H w = Some (n1, H') ->
      step D
        H (EMalloc w)
        H' (RExpr (ELit n1 (TPtr Checked w)))
  | SLet : forall H x n t e,
      step D
        H (ELet x (ELit n t) e)
        H (RExpr (subst x (ELit n t) e))
  | SUnchecked : forall H n t,
      step D
        H (EUnchecked (ELit n t))
        H (RExpr (ELit n t))
  | SAssignOOB : forall H n t n1 t1,
      t = TPtr Checked (TArray 0 0 t1) ->
      step D
        H (EAssign (ELit n t) (ELit n1 t1))
        H RBounds
  | SDerefNull : forall H t w,
      t = TPtr Checked w ->
      step D
        H (EDeref (ELit 0 t))
        H RNull
  | SAssignNull : forall H t w n t',
      t = TPtr Checked w ->
      step D
        H (EAssign (ELit 0 t) (ELit n t'))
        H RNull.

Hint Constructors step.

(* TODO: say more *)
(** The compatible closure of [H; e ~> H'; r], [H; e ->m H'; r].

    We also define a convenience predicate, [reduces H e], which holds
    when there's some [m], [H'], and [r] such that [H; e ->m H'; r]. *)

Inductive reduce (D : structdef) : heap -> expression -> mode -> heap -> result -> Prop :=
  | RSExp : forall H e m H' e' E,
      step D H e H' (RExpr e') ->
      m = mode_of(E) ->
      reduce D
        H (in_hole e E)
        m
        H' (RExpr (in_hole e' E))
  | RSHaltNull : forall H e m H' E,
      step D H e H' RNull ->
      m = mode_of(E) ->
      reduce D
        H (in_hole e E)
        m
        H' RNull
  | RSHaltBounds : forall H e m H' E,
      step D H e H' RBounds ->
      m = mode_of(E) ->
      reduce D
        H (in_hole e E)
        m
        H' RBounds.

Hint Constructors reduce.

Definition reduces (D : structdef) (H : heap) (e : expression) : Prop :=
  exists (m : mode) (H' : heap) (r : result), reduce D H e m H' r.

Hint Unfold reduces.

(** * Static Semantics *)

Require Import Lists.ListSet.

Definition eq_dec_nt (x y : nat * type) : {x = y} + { x <> y}.
repeat decide equality.
Defined. 

Definition scope := set (nat *type)%type. 
Definition empty_scope := empty_set (nat * type).

Inductive well_typed_lit (D : structdef) (H : heap) : scope -> nat -> type -> Prop :=
  | TyLitInt : forall s n,
      well_typed_lit D H s n TNat
  | TyLitArray : forall s n w,
      well_typed_lit D H s n (TPtr Checked (TArray 0 0 w))
  | TyLitU : forall s n w,
      well_typed_lit D H s n (TPtr Unchecked w)
  | TyLitZero : forall s t,
      well_typed_lit D H s 0 t
  | TyLitRec : forall s n w,
      set_In (n, TPtr Checked w) s ->
      well_typed_lit D H s n (TPtr Checked w)
  | TyLitC : forall s n w ts,
      Some ts = allocate_meta D w ->
      (forall k, 0 <= k < List.length ts ->
                 exists n' t',
                   Some t' = List.nth_error ts k /\
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
  forall (D : structdef) (H : heap) (P : scope -> nat -> type -> Prop),
    (forall (s : scope) (n : nat), P s n TNat) ->
    (forall (s : scope) (n : nat) (w : type), P s n (TPtr Checked (TArray 0 0 w))) ->
       (forall (s : scope) (n : nat) (w : type), P s n (TPtr Unchecked w)) ->
       (forall (s : scope) (t : type), P s 0 t) ->
       (forall (s : scope) (n : nat) (w : type), set_In (n, TPtr Checked w) s -> P s n (TPtr Checked w)) ->
       (forall (s : scope) (n : nat) (w : type) (ts : list type),
        Some ts = allocate_meta D w ->
        (forall k : nat,
         0 <= k < length ts ->
         exists (n' : nat) (t' : type),
           Some t' = nth_error ts k /\
           Heap.MapsTo (n + k) (n', t') H /\
           well_typed_lit D H (set_add eq_dec_nt (n, TPtr Checked w) s) n' t' /\
           P (set_add eq_dec_nt (n, TPtr Checked w) s) n' t') ->
        P s n (TPtr Checked w)) -> forall (s : scope) (n : nat) (w : type), well_typed_lit D H s n w -> P s n w.
Proof.
  intros D H P.
  intros HTyLitInt
         HTyLitArray
         HTyLitU
         HTyLitZero
         HTyLitRec
         HTyLitC.
  refine (fix F s n t Hwtl :=
            match Hwtl with
            | TyLitInt _ _ s' n' => HTyLitInt s' n'
            | TyLitArray _ _ s' n' w' => HTyLitArray s' n' w'
            | TyLitU _ _ s' n' w' => HTyLitU s' n' w'
            | TyLitZero _ _ s' t' => HTyLitZero s' t'
            | TyLitRec _ _ s' n' w' Hscope => HTyLitRec s' n' w' Hscope
            | TyLitC _ _ s' n' w' ts Hts IH =>
              HTyLitC s' n' w' ts Hts (fun k Hk =>
                                         match IH k Hk with
                                         | ex_intro _ n' Htmp =>
                                           match Htmp with
                                           | ex_intro _ t' Hn't' =>
                                             match Hn't' with
                                             | conj Ht' Hrest1 =>
                                               match Hrest1 with
                                               | conj Hheap Hwt =>
                                                 ex_intro _ n' (ex_intro _ t' (conj Ht' (conj Hheap (conj Hwt (F (set_add eq_dec_nt (_ , TPtr Checked w') s') n' t' Hwt)))))
                                               end
                                             end
                                           end
                                         end)
            end).
Qed.

(** Expression Typing *)
Module Env := Map.Make Nat_as_OT.

Definition env := Env.t type.

Definition empty_env := @Env.empty type.

Inductive well_typed { D : structdef } { H : heap } : env -> mode -> expression -> type -> Prop :=
  | TyLit : forall env m n t,
      @well_typed_lit D H empty_scope n t ->
      well_typed env m (ELit n t) t
  | TyVar : forall env m x t,
      Env.MapsTo x t env ->
      well_typed env m (EVar x) t
  | TyLet : forall env m x e1 t1 e2 t,
      well_typed env m e1 t1 ->
      well_typed (Env.add x t1 env) m e2 t ->
      well_typed env m (ELet x e1 e2) t
  | TyFieldAddr : forall env m e m' T fs i fi ti,
      well_typed env m e (TPtr m' (TStruct T)) ->
      StructDef.MapsTo T fs D ->
      Fields.MapsTo fi ti fs ->
      List.nth_error (Fields.this fs) i = Some (fi, ti) ->
      well_typed env m (EFieldAddr e fi) (TPtr m' ti)
  | TyPlus : forall env m e1 e2,
      well_typed env m e1 TNat ->
      well_typed env m e2 TNat ->
      well_typed env m (EPlus e1 e2) TNat
  | TyMalloc : forall env m w,
      (forall l h t, w = TArray l h t -> l <= 0 /\ h > 0) ->
      well_typed env m (EMalloc w) (TPtr Checked w)
  | TyUnchecked : forall env m e t,
      well_typed env Unchecked e t ->
      well_typed env m (EUnchecked e) t
  | TyCast : forall env m t e t',
      (m = Checked -> forall w, t <> TPtr Checked w) ->
      well_typed env m e t' ->
      well_typed env m (ECast t e) t
  | TyDeref : forall env m e m' t l h t',
      well_typed env m e (TPtr m' t) ->
      ((word_type t /\ t = t') \/ (t = TArray l h t' /\ word_type t' /\ type_wf D t')) ->
      (m' = Unchecked -> m = Unchecked) ->
      well_typed env m (EDeref e) t'
  | TyIndex : forall env m e1 m' l h t e2,
      word_type t -> type_wf D t ->
      well_typed env m e1 (TPtr m' (TArray l h t)) ->
      well_typed env m e2 TNat ->
      (m' = Unchecked -> m = Unchecked) ->
      well_typed env m (EDeref (EPlus e1 e2)) t
  | TyAssign : forall env m e1 m' t l h t' e2,
      well_typed env m e1 (TPtr m' t) ->
      well_typed env m e2 t' ->
      ((word_type t /\ t = t') \/ (t = TArray l h t' /\ word_type t' /\ type_wf D t')) ->
      (m' = Unchecked -> m = Unchecked) ->
      well_typed env m (EAssign e1 e2) t'
  | TyIndexAssign : forall env m e1 m' l h t e2 e3,
      word_type t -> type_wf D t ->
      well_typed env m e1 (TPtr m' (TArray l h t)) ->
      well_typed env m e2 TNat ->
      well_typed env m e3 t ->
      (m' = Unchecked -> m = Unchecked) ->
      well_typed env m (EAssign (EPlus e1 e2) e3) t.

Hint Constructors well_typed.

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

Lemma step_implies_reduces : forall D H e H' r,
    @step D H e H' r ->
    reduces D H e.
Proof.
  intros.
  assert (e = in_hole e CHole); try reflexivity.
  rewrite H1.
  destruct r; eauto 20.
Qed.

Hint Resolve step_implies_reduces : Progress.

Lemma reduces_congruence : forall D H e0 e,
    (exists E, in_hole e0 E = e) ->
    reduces D H e0 ->
    reduces D H e.
Proof.
  intros.
  destruct H0 as [ E Hhole ].
  destruct H1 as [ H' [ m' [ r HRed ] ] ].
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

Lemma wf_implies_allocate_meta :
  forall (D : structdef) (w : type),
    (forall l h t, w = TArray l h t -> l <= 0 /\ h > 0) ->
    type_wf D w -> exists allocs, allocate_meta D w = Some allocs.
Proof.
  intros D w HL HT.
  destruct w; simpl in *; eauto.
  - inv HT. destruct H0.
    apply StructDef.find_1 in H.
    rewrite -> H.
    eauto.
  - specialize (HL n n0 w eq_refl).
    destruct HL. destruct n.
      +destruct n0; [omega | eauto].
      +destruct n; [omega | eauto].
Qed.

Lemma wf_implies_allocate :
  forall (D : structdef) (w : type) (H : heap),
    (forall l h t, w = TArray l h t -> l <= 0 /\ h > 0) ->
    type_wf D w -> exists n H', allocate D H w = Some (n, H').
Proof.
  intros D w H HL HT.
  eapply wf_implies_allocate_meta in HT; eauto.
  destruct HT.
  unfold allocate.
  rewrite H0.
  simpl.
  (* TODO(ins): there must be a better way *)
  edestruct (fold_left
               (fun (acc : nat * heap) (t : type) =>
                  let (sizeAcc, heapAcc) := acc in (sizeAcc + 1, Heap.add (sizeAcc + 1) (0, t) heapAcc)) x
               (Heap.cardinal (elt:=nat * type) H, H)).
  eauto.
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
                         Heap.cardinal (Heap.add n v H) = Heap.cardinal H + 1.
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
Lemma heap_add_in_cardinal : forall n v H,
  Heap.In n H -> 
  Heap.cardinal (elt:=nat * type) (Heap.add n v H) =
  Heap.cardinal (elt:=nat * type) H.
Proof.
Admitted.

(* Progress:
     If [e] is well-formed with respect to [D] and
        [e] has type [t] under heap [H] in mode [m]
     Then
        [e] is a value, [e] reduces, or [e] is stuck in unchecked code *)

Lemma progress : forall D H m e t,
    structdef_wf D ->
    heap_wf D H ->
    expr_wf D e ->
    @well_typed D H empty_env m e t ->
    value D e \/
    reduces D H e \/
    unchecked m e.
Proof with eauto 20 with Progress.
  intros D H m e t HDwf HHwf Hewf Hwt.
  remember empty_env as env.
  induction Hwt as [
                     env m n t HTyLit                                       | (* Literals *)
                     env m x t HVarInEnv                                    | (* Variables *)
                     env m x e1 t1 e2 t HTy1 IH1 HTy2 IH2                   | (* Let-Expr *)
                     env m e m' T fs i fi ti HTy IH HWf1 HWf2               | (* Field Addr *)
                     env m e1 e2 HTy1 IH1 HTy2 IH2                          | (* Addition *)
                     env m w                                                | (* Malloc *)
                     env m e t HTy IH                                       | (* Unchecked *)
                     env m t e t' HChkPtr HTy IH                            | (* Cast *)
                     env m e m' w n t HTy IH HPtrType HMode                 | (* Deref *)
                     env m e1 m' n t e2 WT Twf HTy1 IH1 HTy2 IH2 HMode             | (* Index *)
                     env m e1 m' w n t e2 HTy1 IH1 HTy2 IH2 HPtrType HMode  | (* Assign *)
                     env m e1 m' n t e2 e3 WT Twf HTy1 IH1 HTy2 IH2 HTy3 IH3 HMode   (* IndAssign *)
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
    (* Case: `e1` reduces *)
    + (* We can take a step by reducing `e1` *)
      left.
      ctx (ELet x e1 e2) (in_hole e1 (CLet x CHole e2))...
    (* Case: `e1` is unchecked *)
    + (* `ELet x e1 e2` must be unchecked, since `e1` is *)
      right.
      ctx (ELet x e1 e2) (in_hole e1 (CLet x CHole e2)).
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
      (* We proceed by case analysis on `m'` -- the mode of the pointer *)
      destruct m'.
      (* Case: m' = Checked *)
      * (* We now proceed by case analysis on 'n = 0' *)
        destruct (Nat.eq_dec n 0).
        (* Case: n = 0 *)
        { (* We can step according to SFieldAddrNull *)
          subst... }
        (* Case: n <> 0 *)
        { (* We can step according to SFieldAddrChecked *)
          assert (HWf3 := HDwf T fs HWf1). (* TODO(ins): turn these into lemmas, and stick into Progress db *)
          assert (HWf4 := HWf3 fi ti HWf2).
          destruct HWf4... }
      (* Case: m' = Unchecked *)
      * (* We can step according to SFieldAddr *)
        eapply step_implies_reduces; eapply SFieldAddr; eauto.
        { (* LEO: This should probably be abstracted into a lemma *)
          apply HDwf in HWf1.
          apply HWf1 in HWf2.
          destruct HWf2...
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
    + (* We can take a step... but how? *)

      (*inv HVal.
      inv HTy.
      (* We proceed by case analysis on `w`, the type of the pointer *)
      destruct HPtrType.
      (* Case: `w` is a word pointer *)
      * (* We now proceed by case analysis on 'n0 = 0' *)
        destruct (Nat.eq_dec n0 0) as [ Hn0eq0 | Hn0neq0 ].
        (* Case: n0 = 0 *)
        { (* We can step according to SDerefNull *)
          subst... }
        (* Case: n <> 0 *)
        { (* We now proceed by case analysis on '|- n0 : ptr_C w' *)
          inversion H7.
          (* Case: TyLitArray *)
          {
            subst. inv H2. inv H3.
          }
          (* Case: TyLitZero *)
          { (* Impossible, since n0 <> 0 *)
            exfalso. apply Hn0neq0. symmetry. assumption. }
          (* Case: TyLitRec *)
          { (* Impossible, since scope is empty *)
            solve_empty_scope.
          } 
          (* Case: TyLitC *)
          { (* We can step according to SDeref *)
            subst.
            destruct H8 with (k := 0) as [ n' [ t' [ Ht'tk [ Hheap Hwtn' ] ] ] ];
            [ inv H2; subst; inv H3; inv H4; simpl; omega | ].
            rewrite Nat.add_0_r in Hheap;
            inv Ht'tk;
            eapply step_implies_reduces.
            apply SDeref; eauto.
            - destruct H2; subst.
              inv H2; simpl in *; inv H4; simpl in *; subst; eauto;
                inv H5; repeat constructor.
            - intros.
              destruct H2 as [Hyp1 Hyp2].
              subst.
              inv H3.
              inv Hyp1.
          }
        }
      (* Case: `w` is an array pointer *)
      * (* We now perform case analysis on 'n0 = 0' *)
        destruct (Nat.eq_dec n0 0) as [ Hn0eq0 | Hn0neq0 ].
        (* Case: n0 = 0 *)
        { (* We can step according to SDerefNull *)
          subst... }
        (* Case: n0 <> 0 *)
        { (* We now proceed by case analysis on '|- n0 : ptr_C (array n t)' *)
          match goal with
          | [ H : well_typed_lit _ _ _ _ _ |- _ ] => inv H
          end.
          (* Case: TyLitArray *)
          { (* Step according to OOB *)
            eauto...
          }
          (* Case: TyLitZero *)
          { (* Impossible, since n0 <> 0 *)
            exfalso; eauto.
          } 
          (* Case: TyLitRec *)
          { (* Impossible, since scope is empty *)
            solve_empty_scope.
          } 
          (* Case: TyLitC *)
          { (* We proceed by case analysis on 'n = 0' -- the size of the array *)
            destruct H2 as [Hyp1 Hyp2]; subst.
            destruct (Nat.eq_dec n 0) as [ Hneq0 | Hnneq0 ].
            (* Case: n = 0 *)
            { (* We can step according to SDerefOOB *)
              subst... }
            (* Case: n <> 0 *)
            { (* We can step according to SDeref *)
              (* LEO: This looks exactly like the previous one. Abstract ? *)
              subst.
              inv H4.
              destruct n; [omega | ].
              inv H3.
              destruct H8 with (k := 0) as [ n' [ t' [ Ht'tk [ Hheap Hwtn' ] ] ] ].
              { simpl; omega. } 
              rewrite Nat.add_0_r in Hheap.
              inv Ht'tk.
              eapply step_implies_reduces.
              apply SDeref; eauto.
              - destruct Hyp2; repeat constructor; eauto.
              - intros.
                inv H2.
                omega.
        } } }*)
    (* Case: `e` reduces *)
    + (* We can take a step by reducing `e` *)
      left.
      ctx (EDeref e) (in_hole e (CDeref CHole))...
    (* Case: `e` is unchecked *)
    + (* `EDeref e` must be unchecked, since `e` is *)
      right.
      ctx (EDeref e) (in_hole e (CDeref CHole)).
      destruct HUnchk...
  - right.
    destruct m'; [> | right; eauto 20 with Progress].
    clear HMode.
    (* Leo: This is becoming hacky *)
    inv H1.
    specialize (IH1 H3 eq_refl).
    specialize (IH2 H4 eq_refl).
    destruct IH1 as [ HVal1 | [ HRed1 | HUnchk1 ] ]; eauto.
    + inv HVal1 as [ n1 t1 ].
      destruct IH2 as [ HVal2 | [ HRed2 | HUnchk2 ] ]; eauto.
      * left.
        inv HVal2.
        ctx (EDeref (EPlus (ELit n1 t1) (ELit n0 t0))) (in_hole (EPlus (ELit n1 t1) (ELit n0 t0)) (CDeref CHole)).
        inv HTy1.
        exists Checked.
        exists H.
        { destruct (Nat.eq_dec n1 0).
          - (* n1 = 0 - Null *)
            exists RNull.
            subst.
            rewrite HCtx.
            eapply RSHaltNull; eauto.
            inv HTy2.
            eapply SPlusNull.
          - (* n1 <> 0 *)
            exists (RExpr (EDeref (ELit (n1 + n0) (TPtr Checked (TArray (n - n0) t))))).
            ctx (EDeref (ELit (n1 + n0) (TPtr Checked (TArray (n - n0) t))))
                (in_hole (ELit (n1 + n0) (TPtr Checked (TArray (n - n0) t))) (CDeref CHole)).
            rewrite HCtx.
            rewrite HCtx0.
            inv HTy2.
            eapply RSExp; eauto.
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
            + inv H0. 
            + solve_empty_scope.
            + left.
              inv H0; inv H2;
              destruct (H5 0) as [x [xT [HNth [HMap HWT]]]]; simpl in*;
                try omega;
                try rewrite plus_0_r in *;
                eauto; 
              try (eapply step_implies_reduces;
                   eapply SAssign; eauto);
              try (eexists; eauto);
              intros; try congruence...
          - inv HTy1; eauto.
            match goal with
            | [ H : well_typed_lit _ _ _ _ _ |- _ ] => inv H
            end...
            + destruct Hw as [? [? ?]]; subst.
              inv HTy2.
              inv H0.
              left; eauto...
            + solve_empty_scope.
            + left.
              destruct Hw as [? [? ?]]; subst.
              destruct (Nat.eq_dec n 0).
              * (* n = 0 - Null *)
                eapply step_implies_reduces.
                inv HTy2; subst; eapply SAssignOOB; eauto...
              * (* n <> 0 - Assign *)
                eapply step_implies_reduces.
                { eapply SAssign; eauto...
                  - inv H1.
                    destruct (H4 0) as [n' [t' [HNth [HMap HWT]]]]; eauto.
                    + destruct n; [omega |].
                      inv H5; simpl; omega.
                    + inv HNth.
                      rewrite plus_0_r in HMap.
                      destruct n; try omega; simpl in *.
                      inv H1.
                      eexists; eauto.
                  - intros l t' Hyp; inv Hyp.
                    omega.
                } 
        } 
      * unfold reduces in HRed2. destruct HRed2 as [ H' [ ? [ r HRed2 ] ] ].
        inv HRed2; ctx (EAssign (ELit n1' t1') (in_hole e E)) (in_hole e (CAssignR n1' t1' E))...
      * destruct HUnchk2 as [ e' [ E [ ] ] ]; subst.
        ctx (EAssign (ELit n1' t1') (in_hole e' E)) (in_hole e' (CAssignR n1' t1' E))...
    + (* Case: e1 reduces *)
      destruct HRed1 as [ H' [ ? [ r HRed1 ] ] ].
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

    (* Invoke IH on e1 *)
    destruct IH1 as [ HVal1 | [ HRed1 | [| HUnchk1 ] ] ]; idtac...
    + (* Case: e1 is a value *)
      inv HVal1.
      (* Invoke IH on e2 *)
      destruct IH2 as [ HVal2 | [ HRed2 | [| HUnchk2 ] ] ]; idtac...
      * inv HVal2.
        ctx (EAssign (EPlus (ELit n0 t0) (ELit n1 t1)) e3) (in_hole (EPlus (ELit n0 t0) (ELit n1 t1)) (CAssignL CHole e3)).
        inv HTy1.
        inv HTy2.
        {
          inv H11; inv H12; (eauto 20 with Progress); 
            try solve_empty_scope.
          - destruct IH3 as [ HVal3 | [ HRed3 | [| HUnchk3]]]; idtac...
            + inv HVal3.
              inv HTy3.
              left; eauto...
              destruct (Nat.eq_dec n0 0); subst; eauto...
            + destruct HRed3 as [H' [? [r HRed3]]].
              destruct (Nat.eq_dec n0 0); subst; eauto...
            + destruct HUnchk3 as [ e' [ E [ He2 HEUnchk ]]]; subst.
              destruct (Nat.eq_dec n0 0); subst; eauto...
          - destruct IH3 as [ HVal3 | [ HRed3 | [| HUnchk3]]]; idtac...
            + inv HVal3.
              inv HTy3.
              left; eauto...
              destruct (Nat.eq_dec n0 0); subst; eauto...
            + destruct HRed3 as [H' [? [r HRed3]]].
              destruct (Nat.eq_dec n0 0); subst; eauto...
            + destruct HUnchk3 as [ e' [ E [ He2 HEUnchk ]]]; subst.
              destruct (Nat.eq_dec n0 0); subst; eauto...
          - inv H7.
            left.
            destruct (Nat.eq_dec n0 0); subst; eauto...
          - inv H7.
            left.
            destruct (Nat.eq_dec n0 0); subst; eauto...
        }
      * destruct HRed2 as [ H' [ ? [ r HRed2 ] ] ].
        inv HRed2; ctx (EAssign (EPlus (ELit n0 t0) (in_hole e E)) e3) (in_hole e (CAssignL (CPlusR n0 t0 E) e3))...
      * destruct HUnchk2 as [ e' [ E [ He2 HEUnchk ] ] ]; subst.
        ctx (EAssign (EPlus (ELit n0 t0) (in_hole e' E)) e3) (in_hole e' (CAssignL (CPlusR n0 t0 E) e3))...
    + destruct HRed1 as [ H' [ ? [ r HRed1 ] ] ].
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
  - exfalso; eapply NEq; eauto.
  - repeat (try rewrite env_find_add1 in *; auto; try rewrite env_find_add2 in *; auto).
  - specialize (Eq x2); repeat (try rewrite env_find_add1 in *; auto; try rewrite env_find_add2 in *; auto).
  - specialize (Eq x); repeat (try rewrite env_find_add1 in *; auto; try rewrite env_find_add2 in *; auto).
Qed.

Create HintDb Preservation.

Lemma substitution :
  forall D H env m x v e t1 t2,
    literal v ->
  @well_typed D H env m v t1 ->
  @well_typed D H (Env.add x t1 env) m e t2 ->
  @well_typed D H env m (subst x v e) t2.
Proof.
  intros D H env m x v e t1 t2 Hvalue HWTv HWTe.
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
          - inv Hvalue as [n' t'].
            inv HWTv. eapply TyLit; eauto.
        } 
  - intros. subst. apply TyUnchecked. apply IHHWTe; eauto.
    inv Hvalue as [n' t'].
    destruct m.
      * inv HWTv.
        apply TyLit.
        assumption.
      * assumption.
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

Lemma length_nth : forall {A} (l : list A) k,
    0 <= k < length l -> exists n, nth_error l k = Some n.
Proof.
  intros A l; induction l; intros k Hyp; simpl in *.
  - omega.
  - destruct k; simpl.
    + exists a; eauto.
    + destruct (IHl k); [omega | eauto].
Qed.      

Lemma nth_length : forall {A} (l : list A) k n,
    nth_error l k = Some n -> 0 <= k < length l.
Proof.
  intros A l; induction l; intros k n Hyp; simpl in *.
  - apply nth_error_In in Hyp; inv Hyp.
  - destruct k; simpl in *.
    + omega.
    + edestruct IHl; eauto.
      omega.
Qed.

Require Import Coq.Program.Equality.
  
Lemma heap_wf_maps_nonzero : forall D H n v, heap_wf D H -> Heap.MapsTo n v H -> n <> 0.
Proof.
  intros D H n v Hwf HMap.
  destruct (Hwf n) as [ _ HIn ].
  destruct n; eauto; exfalso.
  destruct HIn; try eexists; eauto.
  inversion H0.
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
  forall D H, heap_wf D H -> ~ Heap.In (Heap.cardinal H + 1) H.
  intros D H Hwf Contra.
  destruct (Hwf (Heap.cardinal H + 1)) as [H1 H2].
  specialize (H2 Contra).
  omega.
Qed.

Lemma well_typed_preserved : forall D H t, heap_wf D H ->
  @heap_consistent D (Heap.add (Heap.cardinal (elt:=nat * type) H + 1) (0, t) H) H.
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
  heap_wf D (Heap.add (Heap.cardinal H + 1) (n, v) H).
Proof.
  intros D H n v Hwf.
  split; intros; simpl; eauto.
  * rewrite cardinal_plus_one in H0.
    - assert (Hyp: 0 < addr <= Heap.cardinal H \/ addr = Heap.cardinal H + 1) by omega.
      inv Hyp.
      + destruct (Hwf addr) as [ HIn _ ].
        specialize (HIn H1).
        inv HIn. exists x.
        apply Heap.add_2; eauto.
        omega.
      + eexists; eapply Heap.add_1; eauto.
    - intros Contra.
      destruct (Hwf (Heap.cardinal H + 1)) as [? ?].
      specialize (H2 Contra).
      omega.
  * apply HeapFacts.add_in_iff in H0.
    inv H0.
    - rewrite cardinal_plus_one; try omega.
      intro Contra.
      destruct (Hwf (Heap.cardinal H + 1)) as [? ?].
      specialize (H1 Contra).
      omega.
    - rewrite cardinal_plus_one.
      + destruct (Hwf addr) as [_ H2]; specialize (H2 H1); omega.
      + intro Contra.
        destruct (Hwf (Heap.cardinal H + 1)) as [H2 H3].
        specialize (H3 Contra).
        omega.
Qed.

Lemma backwards_consistency :
  forall D H' H v,
    @heap_consistent D H' (Heap.add (Heap.cardinal H + 1) v H) ->
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
        (fun (acc : nat * heap) (t : type) =>
           let (sizeAcc, heapAcc) := acc in
           (sizeAcc + 1, Heap.add (sizeAcc + 1) (0, t) heapAcc))
        l
        (Heap.cardinal (elt:=nat * type) H, H) in
  Some (Heap.cardinal (elt:=nat * type) H + 1, H') = Some (ptr, H') ->
  @heap_consistent D H' H.
Proof.
  intro l; induction l; intros; simpl; eauto.
  assert (Hwf : heap_wf D (Heap.add (Heap.cardinal H +1) (0, a) H))
    by (apply heap_add_preserves_wf; auto).
  specialize (IHl D (Heap.add (Heap.cardinal H + 1) (0, a) H) (S ptr) Hwf).
  remember (Heap.add (Heap.cardinal H +1) (0, a) H) as H1.

  
  Set Printing All.
  remember ((fun (acc : prod nat heap) (t : type) =>
             match acc return (prod nat heap) with
             | pair sizeAcc heapAcc =>
                 @pair nat (Heap.t (prod nat type)) (Init.Nat.add sizeAcc (S O))
                   (@Heap.add (prod nat type) (Init.Nat.add sizeAcc (S O)) 
                      (@pair nat type O t) heapAcc)
             end)) as fold_fun.
  Unset Printing All.
  clear Heqfold_fun.
  assert (Heap.cardinal H1 = Heap.cardinal H + 1).
  {
    subst; apply cardinal_plus_one; eauto.
    intro Contra.
    destruct (H0 (Heap.cardinal H + 1)) as [H1 H2].
    specialize (H2 Contra).
    omega.
  } 
  rewrite H2 in IHl.

  assert (HEq:
      (  @fold_left (prod nat heap) type fold_fun l
            (@pair nat heap (Init.Nat.add (@Heap.cardinal (prod nat type) H) (S O)) H1) ) =
      (    @fold_left (prod nat heap) type fold_fun l
                      (@pair nat (Heap.t (prod nat type)) (Init.Nat.add (@Heap.cardinal (prod nat type) H) (S O)) H1))
    ) by auto.

  rewrite HEq in IHl.

  Set Printing All.

  remember (
    @fold_left (prod nat heap) type fold_fun l
               (@pair nat (Heap.t (prod nat type)) (Init.Nat.add (@Heap.cardinal (prod nat type) H) (S O)) H1)
    ) as fold_call.

  Unset Printing All.

  destruct fold_call.
  intro Hyp.
  inv Hyp.
  
  assert (Heap.cardinal H + 1 + 1 = S (Heap.cardinal H + 1)) by omega.
  rewrite H1 in IHl.
  specialize (IHl eq_refl).


  eapply backwards_consistency; eauto.
Qed.

  
(* This could probably be merged with the previous one *)
Lemma fold_summary : forall l D H ptr,
  heap_wf D H ->
  let (_, H') :=
      fold_left
        (fun (acc : nat * heap) (t : type) =>
           let (sizeAcc, heapAcc) := acc in
           (sizeAcc + 1, Heap.add (sizeAcc + 1) (0, t) heapAcc))
        l
        (Heap.cardinal (elt:=nat * type) H, H) in
  Some (Heap.cardinal (elt:=nat * type) H + 1, H') = Some (ptr, H') ->
  heap_wf D H' /\
  ptr = Heap.cardinal H + 1 /\
  Heap.cardinal H' = Heap.cardinal H + length l /\
  (forall k v, 0 <= k < length l -> nth_error l k = Some v ->
               Heap.MapsTo (Heap.cardinal H + 1 + k) (0,v) H') /\
  forall x v, Heap.MapsTo x v H -> Heap.MapsTo x v H'.                                               
Proof.
  intro l; induction l; simpl; intros D H ptr Hwf.
  - intros Eq. inv Eq; repeat (split; eauto).
    intros k v Contra _.
    inv Contra.
    inv H1.
  - remember 
      (fun (acc : prod nat heap) (t : type) =>
         match acc return (prod nat heap) with
         | pair sizeAcc heapAcc =>
           @pair nat (Heap.t (prod nat type)) (Init.Nat.add sizeAcc (S O))
                 (@Heap.add (prod nat type) (Init.Nat.add sizeAcc (S O))
                            (@pair nat type O t) heapAcc)
         end) as fold_fun.
    clear Heqfold_fun.

    assert (Hwf' : heap_wf D (Heap.add (Heap.cardinal H + 1) (0, a) H))
      by (apply heap_add_preserves_wf; eauto).
    specialize (IHl D (Heap.add (Heap.cardinal H + 1) (0, a) H) (S ptr) Hwf').

    
    remember (Heap.add (Heap.cardinal H +1) (0, a) H) as H1.

    assert (Heap.cardinal H1 = Heap.cardinal H + 1).
    {
      subst; apply cardinal_plus_one; eauto.
      intro Contra.
      destruct (Hwf (Heap.cardinal H + 1)) as [H1 H2].
      specialize (H2 Contra).
      omega.
    } 
    rewrite H0 in IHl.

    assert (HEq:
        (  @fold_left (prod nat heap) type fold_fun l
              (@pair nat heap (Init.Nat.add (@Heap.cardinal (prod nat type) H) (S O)) H1) ) =
        (    @fold_left (prod nat heap) type fold_fun l
                        (@pair nat (Heap.t (prod nat type)) (Init.Nat.add (@Heap.cardinal (prod nat type) H) (S O)) H1))
      ) by auto.
   
    rewrite HEq in IHl.

  Set Printing All.

  remember (
    @fold_left (prod nat heap) type fold_fun l
               (@pair nat (Heap.t (prod nat type)) (Init.Nat.add (@Heap.cardinal (prod nat type) H) (S O)) H1)
    ) as fold_call.

  Unset Printing All.

  clear Heqfold_call.
  destruct fold_call.
  intro Hyp.
  inv Hyp.

  assert (Heap.cardinal H + 1 + 1 = S (Heap.cardinal H + 1)) by omega.
  rewrite H1 in IHl.
  destruct (IHl eq_refl) as [hwf [Card [Card' [HField HMap]]]].

  repeat (split; eauto).
  + omega.
  + intros k v Hk HF.
    destruct k.
    * simpl in *.
      inv HF.
      specialize (HMap (Heap.cardinal H + 1) (0,v)).
      rewrite Nat.add_0_r.
      eapply HMap.
      apply Heap.add_1; eauto.
    * simpl in *.
      assert (HS: Heap.cardinal H + 1 + S k = S (Heap.cardinal H + 1 + k)) by omega.
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
      apply Heap.add_1; eauto.
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
      apply Heap.add_1; eauto.
    * apply heap_add_preserves_wf; auto.
  - split.
    * unfold allocate in H1.
      unfold allocate_meta in H1.
      simpl in H1.
      destruct (StructDef.find s D) eqn:Find; try congruence.
      remember (Fields.elements f) as l.

      pose proof (fold_preserves_consistency (map snd l) D H ptr HWf).

      remember (fold_left
            (fun (acc : nat * heap) (t : type) =>
             let (sizeAcc, heapAcc) := acc in (sizeAcc + 1, Heap.add (sizeAcc + 1) (0, t) heapAcc))
            (map snd l) (Heap.cardinal (elt:=nat * type) H, H)).
      destruct p.
      clear Heqp.
      inv H1.
      apply H0; eauto.
    * unfold allocate in H1.
      simpl in *.
      destruct (StructDef.find s D) eqn:Find; try congruence.

      pose proof (fold_summary (map snd (Fields.elements f)) D H ptr HWf) as Hyp.
      remember
        (fold_left
           (fun (acc : nat * heap) (t : type) =>
            let (sizeAcc, heapAcc) := acc in
            (sizeAcc + 1, Heap.add (sizeAcc + 1) (0, t) heapAcc))
           (map snd (Fields.elements (elt:=type) f))
           (Heap.cardinal (elt:=nat * type) H, H)) as p.
      destruct p.
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

      assert (HOrd: 0 < Heap.cardinal H + 1 + k <= Heap.cardinal H') by omega.
      pose proof (H'wf (Heap.cardinal H + 1 + k)) as Hyp.
      apply Hyp in HOrd.
      destruct HOrd as [[n' t'] HM'].
      
      exists n'. exists t'.
      destruct (length_nth (map snd (Fields.elements f)) k HK) as [x Hnth].
      specialize (HF k x HK Hnth).
      pose proof (HeapFacts.MapsTo_fun HM' HF) as Eq.
      inv Eq.
      
      repeat (split; eauto).
  - split.
    * unfold allocate in H1.
      unfold allocate_meta in H1.
      simpl in H1.

      remember (replicate n w) as l.

      pose proof (fold_preserves_consistency l D H ptr HWf).

      destruct n; simpl in *; try congruence.

      remember (fold_left
            (fun (acc : nat * heap) (t : type) =>
             let (sizeAcc, heapAcc) := acc in (sizeAcc + 1, Heap.add (sizeAcc + 1) (0, t) heapAcc))
            l (Heap.cardinal (elt:=nat * type) H, H)) as p.
      
      destruct p as (n1, h). (*n0 already used???*)
      clear Heqp.
      inv H1.
      apply H0; eauto.
    * unfold allocate in H1.
      simpl in *.

      remember (replicate n w) as l.
      
      destruct n; simpl in *; try congruence.

      pose proof (fold_summary l D H ptr HWf) as Hyp.
      remember
        (fold_left
           (fun (acc : nat * heap) (t : type) =>
            let (sizeAcc, heapAcc) := acc in
            (sizeAcc + 1, Heap.add (sizeAcc + 1) (0, t) heapAcc))
           l
           (Heap.cardinal (elt:=nat * type) H, H)) as p.
      destruct p.
      clear Heqp.
      inv H1.

      destruct Hyp as [H'wf  [Card1 [Card2 [HF HM]]]]; eauto.

      split; auto.
      constructor.
      eapply TyLitC; simpl in *; eauto.

      intros k HK.
      simpl in *.
      assert (HOrd: 0 < Heap.cardinal H + 1 + k <= Heap.cardinal H') by omega.
      pose proof (H'wf (Heap.cardinal H + 1 + k)) as Hyp.
      destruct k; subst; simpl in *; eauto.
      + exists 0; exists w. split; auto.
      + apply Hyp in HOrd.
        { destruct HOrd as [[n' t'] HM'].
          destruct (length_nth (replicate n w) k) as [x Hnth].
          - rewrite replicate_length in *. omega.
          - exists n'. exists x.
            specialize (HF (S k) w HK).
            split; eauto.
            assert (w = x).
            { eapply replicate_nth; eauto. }
            subst.
            assert (Hyp' : nth_error (x :: replicate n x) (S k) = Some x).
            { simpl; auto. }
            specialize (HF Hyp').
            pose proof (HeapFacts.MapsTo_fun HM' HF) as Eq.
            inv Eq.
            split; auto.
        } 
Qed.

Lemma values_are_nf : forall D H e,
    value D e ->
    ~ exists H' m r, @reduce D H e m H' r.
Proof.
  intros D H e Hv contra.
  inv Hv.
  destruct contra as [H' [ m [ r contra ] ] ].
  inv contra; destruct E; inversion H4; simpl in *; subst; try congruence.
Qed.

Lemma lit_are_nf : forall D H n t,
    ~ exists H' m r, @reduce D H (ELit n t) m H' r.
Proof.
  intros D H n t contra.
  destruct contra as [H' [ m [ r contra ] ] ].
  inv contra; destruct E; inversion H2; simpl in *; subst; try congruence.
Qed.

Lemma var_is_nf : forall D H x,
    ~ exists H' m r, @reduce D H (EVar x) m H' r.
Proof.
  intros.
  intros contra.
  destruct contra as [H' [ m [ r contra ] ] ].
  inv contra; destruct E; inversion H1; simpl in *; subst; inv H2.
Qed.


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

Lemma set_equal_add (s1 s2 : scope) (v : nat * type) :
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
    constructor; apply HEq; auto.
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

Lemma set_equal_add_add (s1 s2 : scope) (v1 v2 : nat * type) :
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
    constructor.
    apply set_add_intro1; auto.
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
  - constructor.
    right; auto.
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
  destruct (Nat.eq_dec (n0+x) i).
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
  
Lemma set_equal_add_remove (s : scope) (v1 v2 : nat * type) :
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
  - destruct (Nat.eq_dec n m).
    + subst.
      destruct (type_eq_dec tm (TPtr Checked w)).
      * subst.
        apply scope_weakening'; auto.
      * constructor.
        apply set_remove_all_intro; auto.
        intro Contra; inv Contra.
        eauto.
    + constructor.
      apply set_remove_all_intro; auto.
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
  @well_typed_lit D H empty_scope (n + i) (TPtr Checked ti).
Proof.
  intros D H n T fs HWT.
  inversion HWT;
  intros i fi ti Hn HS HF Hnth Hhwf HDwf Hfwf Hwt; eauto.
  - exfalso ; eauto.
  - destruct (H4 i) as [N' [T' [HNth [HMap HWT']]]]; subst.
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
      rewrite <- HNth in Hnth'.
      inv Hnth'.
      inv Hwt.
      * eapply TyLitC; simpl in *; eauto.
        intros k Hk; simpl in *.
        assert (k = 0) by omega; subst.
        exists N'. exists TNat.
        repeat (split; eauto).
        rewrite plus_0_r; eauto.
      * eapply TyLitC; simpl in *; eauto.
        intros k Hk; simpl in *.
        assert (k = 0) by omega; subst.
        exists N'. exists (TPtr m w).
        repeat (split; eauto).
        rewrite plus_0_r; eauto.

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
  - constructor.
    apply set_add_intro; auto.
  - eapply TyLitC; eauto.
    intros x Hx.
    destruct (H1 x Hx) as [N' [T' [HNth [HMap' [HWT'' IH]]]]].
    destruct (Nat.eq_dec (n + x) i).
    + subst.
      maps_to_fun.
      exists k; exists (TPtr Checked T); eauto.
      repeat (split; eauto).
      * apply Heap.add_1; auto.
      * apply TyLitRec; auto.
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
  destruct (Nat.eq_dec (n'+x) i).
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
  - inv Hwt.
  - destruct (Hwf 0) as [_ Contra].
    apply Contra in HIn.
    omega.
  - inv H3.
  - inv Hwt; simpl in *; inv H1.
    + destruct (H4 0) as [n' [t' [HNth [HMap HWT]]]]; auto.
      rewrite Nat.add_0_r in *.
      inv HNth.
      exists n'; eauto.
    + destruct (H4 0) as [n' [t' [HNth [HMap HWT]]]]; auto.
      rewrite Nat.add_0_r in *.
      inv HNth.
      exists n'; eauto.
Qed.

Lemma well_typed_heap_in_array : forall n D H l w,
  heap_wf D H ->
  Heap.In n H ->
  l > 0 ->
  @well_typed_lit D H empty_scope n (TPtr Checked (TArray l w)) ->
  exists x, Heap.MapsTo n (x, w) H.
Proof.
  intros n D H l w Hwf HIn Hl HWT.
  inv HWT.
  - inv Hl.
  - destruct (Hwf 0) as [_ Contra].
    apply Contra in HIn.
    omega.
  - inv H3.
  - inv H1.
    destruct l; try omega.
    inv H2.
    destruct (H4 0) as [n' [t' [HNth [HMap HWT]]]]; auto.
    + simpl; omega.
    + rewrite Nat.add_0_r in *.
      inv HNth.
      exists n'; eauto.
Qed.

Lemma preservation : forall D H env e t H' e',
    @structdef_wf D ->
    heap_wf D H ->
    expr_wf D e ->
    @well_typed D H env Checked e t ->
    @reduce D H e Checked H' (RExpr e') ->
    @heap_consistent D H' H /\ @well_typed D H' env Checked e' t.
Proof with eauto 20 with Preservation.
  intros D H env e t H' e' HDwf HEwf HHwf Hwt.
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
                    env m e m' w n t HTy IH HPtrType HMode                | (* Deref *)
                    env m e1 m' n t e2 WT Twf HTy1 IH1 HTy2 IH2 HMode            | (* Index *)
                    |
                    ]; intros e' H' Hreduces; subst.
  (* T-Lit, impossible because values do not step *)
  - exfalso. eapply lit_are_nf...
  (* T-Var *)
  - exfalso. eapply var_is_nf...
  (* T-Let *)
  - inv Hreduces.
    destruct E; inversion H1; simpl in *; subst.
    + clear H0. clear H7. rename e'0 into e'.
      inv H4... (* Uses substitution lemma *)
    + clear H1. edestruct IH1... (* Uses heap_wf *)
      inv HHwf; eauto.
  (* T-FieldAddr *)
  - inv Hreduces.
    destruct E; inversion H2; simpl in *; subst.
    + clear H0. clear H8. inv H5.
      * inv HTy.
        (* Gotta prove some equalities *)
        assert (fs = fs0).
        { apply StructDef.find_1 in HWf1.
          match goal with
          | [ H : StructDef.MapsTo _ _ _ |- _ ] =>
            apply StructDef.find_1 in H; rewrite HWf1 in H; inv H
          end; auto.
        } 
        subst. clear H8.
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
        constructor. eapply preservation_fieldaddr; eauto.
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
    + subst.
      clear IH.
      inv H5.
      split; eauto.
      destruct HPtrType as [[Hw Eq] | Hw]; subst.
      * { inv HTy.
          clear H8.
          clear n.
          clear H0.
          remember H7 as Backup; clear HeqBackup.
          inv H7.
          - inv Hw.
          - exfalso.
            eapply heap_wf_maps_nonzero; eauto.
          - inversion H3.
          - inv Hw; simpl in*; subst; simpl in *.
            + inv H0; simpl in *.
              destruct (H4 0) as [N [T' [HT' [HM' HWT']]]]; [omega | ].
              inv HT'.
              rewrite Nat.add_0_r in HM'.
              assert (Hyp: (N, TNat) = (n1, t1)) by (eapply HeapFacts.MapsTo_fun; eauto).
              inv Hyp; subst; eauto.
            + inv H0; simpl in *.
              destruct (H4 0) as [N [T' [HT' [HM' HWT']]]]; [omega | ].
              inv HT'.
              rewrite Nat.add_0_r in HM'.
              assert (Hyp: (N, TPtr m w) = (n1, t1)) by (eapply HeapFacts.MapsTo_fun; eauto).
              inv Hyp; subst; eauto.
              apply TyLit.

              assert (Hyp: set_remove_all (n0, TPtr Checked (TPtr m w))
                                     ((n0,TPtr Checked (TPtr m w))::nil) = empty_scope).
              { 
                destruct (eq_dec_nt (n0, TPtr Checked (TPtr m w)) (n0, TPtr Checked (TPtr m w))) eqn:EQ; try congruence.
                unfold set_remove_all.
                rewrite EQ.
                auto.
              }

              rewrite <- Hyp.
              apply scope_strengthening; eauto.
        }
      * { inv HTy.
          clear H8.
          clear H0.
          clear H1.
          remember H7 as Backup; clear HeqBackup.
          inv H7.
          - specialize (H11 0 w0 eq_refl); omega.
          - exfalso.
            eapply heap_wf_maps_nonzero; eauto.
          - inversion H2.
          - simpl in H0. subst.
            destruct Hw as [? [? ?]]; subst.
            inv H0; simpl in *.
            destruct n; [ inv H4 | ].
            inv H4; simpl in *.

            destruct (H3 0) as [N [T' [HT' [HM' HWT']]]]; [ simpl; omega | ].
            inv HT'.
            rewrite Nat.add_0_r in HM'.
            maps_to_fun.
            constructor.
            assert (Hyp: set_remove_all (n0, TPtr Checked (TArray (S n) t))
                                        ((n0,TPtr Checked (TArray (S n) t))::nil) = empty_scope).
              { 
                destruct (eq_dec_nt (n0, TPtr Checked (TArray (S n) t))
                                    (n0, TPtr Checked (TArray (S n) t))) eqn:EQ; try congruence.
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
    inv H1.
    inv Hreduces.
    destruct E; inversion H1; simpl in *; subst.
    + clear H0. clear H9.
      inv H6.
    + clear H1.
      destruct E; inversion H2; simpl in *; subst.
      * { (* Plus step *)
          inv H6; split; eauto...
          - inv HTy1.
            eapply TyDeref with (n0 := n - n2); eauto.
            constructor.
            remember H5 as Backup; clear HeqBackup.
            inv H5; eauto; try omega.
            inv H1.
            destruct n; try congruence.
            assert (HLen: length ts = S n).
            { inv H2. simpl. rewrite replicate_length; auto. }
            (* destruct on whether n2 <= length ts or not *)
            destruct (dec_lt n2 (S n)).
            (* Case n2 < S n: in bounds, use hypothesis *)
            + remember (S n - n2) as m.

              eapply TyLitC with (ts := replicate m t) ; eauto.
              * destruct m; try omega; simpl in *; eauto.
              * intros k Hk.
                
                destruct (H7 (n2+k)) as [N [T [HNth [HMap HWT]]]]; try omega.
                { (* Arithmetic for n2 + k *)
                  subst.
                  rewrite HLen.
                  rewrite replicate_length in Hk.
                  omega.
                }
                assert (t = T).
                { inversion H2.
                  rewrite H5 in HNth.
                  replace (t :: replicate n t) with (replicate (S n) t) in HNth by auto.
                  symmetry in HNth.
                  apply replicate_nth in HNth.
                  auto.
                } 
                subst.
                exists N. exists T.
                { repeat (split; eauto).
                  - destruct (length_nth (replicate (S n - n2) T) k Hk).
                    rewrite H1.
                    apply replicate_nth in H1; subst.
                    auto.
                  - rewrite <- plus_assoc; auto.
                  - eapply scope_strengthening in HWT; eauto.
                    assert (HAdd : set_add eq_dec_nt (n1, TPtr Checked (TArray (S n) T)) empty_scope =
                            (n1, TPtr Checked (TArray (S n) T)) :: nil) by auto.
                    rewrite HAdd in HWT.
                    
                    assert (HEmpty : empty_scope = set_remove_all (n1, TPtr Checked (TArray (S n) T))
                                             ((n1, TPtr Checked (TArray (S n) T)) :: nil)).
                    {
                      unfold set_remove_all.
                      destruct (eq_dec_nt (n1, TPtr Checked (TArray (S n) T))
                                          (n1, TPtr Checked (TArray (S n) T))); auto.
                      congruence.
                    }
                    
                    eapply scope_strengthening in HWT; eauto.
                    rewrite <- HEmpty in HWT.
                    apply scope_weakening_cons.
                    auto.
                }
            + assert (S n - n2 = 0) by omega.
              rewrite H1.
              eauto.
          - inv HTy1.
            destruct m'.
            + exfalso; eapply H10; eauto.
            + specialize (HMode eq_refl). inv HMode.
        }
      * specialize (IH1 H3 eq_refl).
        specialize (IH1 (in_hole e'0 E) H').
        destruct IH1 as [HC HWT]; eauto.
        split ; eauto...
      * specialize (IH2 H4 eq_refl (in_hole e'0 E) H').
        destruct IH2 as [HC HWT]; eauto.
        split; eauto...
  (* T-Assign *)
  - inv Hreduces.
    inv HHwf.
    destruct E; inversion H3; simpl in *; subst.
    + clear H9. clear H2.
      inv H6.
      inv Hwt2.
      inv Hwt1.
      destruct H0 as [[HW Eq] | Eq]; subst.
      * { destruct m'; [| specialize (H1 eq_refl); inv H1].
          eapply well_typed_heap_in in H10; eauto.
          destruct H10 as [N HMap].
          split.
          - apply HeapUpd with (n := N); eauto...
            eapply PtrUpd; eauto.
          - constructor.
            eapply PtrUpd; eauto. 
        } 
      * destruct Eq as [? [? ?]]; subst.
        { destruct m'; [| specialize (H1 eq_refl); inv H1].
          eapply (well_typed_heap_in_array n0 D H n) in H10; eauto.
          destruct H10 as [N HMap].
          split.
          - apply HeapUpd with (n := N); eauto...
            eapply PtrUpd; eauto.
          - constructor.
            eapply PtrUpd; eauto.
        } 
    + destruct (IHHwt1 H5 eq_refl (in_hole e'0 E) H') as [HC HWT]; eauto.
      split; eauto...
    + destruct (IHHwt2 H7 eq_refl (in_hole e'0 E) H') as [HC HWT]; eauto.
      split; eauto...
  - inv Hreduces.
    inv HHwf.
    inv H6.
    destruct E; inv H4; subst; simpl in*; subst; eauto.
    + inv H7.
    + destruct E; inversion H5; simpl in *; subst.
      * { (* Plus step *)
          inv H7; split; eauto...
          - inv Hwt1.
            destruct (Nat.eq_dec (n - n2) 0).
            + rewrite e.
              eapply TyAssign; eauto.
            + remember H6 as Backup; clear HeqBackup.
              inv H6; try omega; eauto.
              { inv H7. }
              clear IHHwt1 IHHwt2 IHHwt3 H8.
              destruct n; try omega.
            
              remember (S n - n2) as m.
              eapply TyAssign with (n3 := m); eauto.
              constructor.
              eapply TyLitC with (ts := replicate m t) ; eauto.
              * destruct m; try omega; simpl in *; eauto.
              * intros k Hk.

                assert (HLen: length ts = S n).
                { inv H4. simpl. rewrite replicate_length; auto. }
                
                destruct (H12 (n2+k)) as [N [T [HNth [HMap HWT]]]]; try omega.
                { (* Arithmetic for n2 + k *)
                  subst.
                  rewrite HLen.
                  rewrite replicate_length in Hk.
                  omega.
                }
                assert (t = T).
                { inversion H4.
                  rewrite H5 in HNth.
                  replace (t :: replicate n t) with (replicate (S n) t) in HNth by auto.
                  symmetry in HNth.
                  apply replicate_nth in HNth.
                  auto.
                } 
                subst.
                exists N. exists T.
                { repeat (split; eauto).
                  - destruct (length_nth (replicate (S n - n2) T) k Hk).
                    rewrite H.
                    apply replicate_nth in H; subst.
                    auto.
                  - rewrite <- plus_assoc; auto.
                  - eapply scope_strengthening in HWT; eauto.
                    assert (HAdd : set_add eq_dec_nt (n1, TPtr Checked (TArray (S n) T)) empty_scope =
                            (n1, TPtr Checked (TArray (S n) T)) :: nil) by auto.
                    rewrite HAdd in HWT.
                    
                    assert (HEmpty : empty_scope = set_remove_all (n1, TPtr Checked (TArray (S n) T))
                                             ((n1, TPtr Checked (TArray (S n) T)) :: nil)).
                    {
                      unfold set_remove_all.
                      destruct (eq_dec_nt (n1, TPtr Checked (TArray (S n) T))
                                          (n1, TPtr Checked (TArray (S n) T))); auto.
                      congruence.
                    }
                    
                    eapply scope_strengthening in HWT; eauto.
                    rewrite <- HEmpty in HWT.
                    apply scope_weakening_cons.
                    auto.
                }
          - inv Hwt1.
            destruct m'.
            + exfalso; eapply H14; eauto.
            + specialize (H2 eq_refl). inv H2.
        } 
      * destruct (IHHwt1 H9 eq_refl (in_hole e'0 E) H') as [HC HWT]; eauto.
        split ; eauto...
      * destruct (IHHwt2 H11 eq_refl (in_hole e'0 E) H') as [HC HWT]; eauto.
        split; eauto...
Qed.

(* ... for Blame *)

Create HintDb Blame.

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
      destruct (Nat.eq_dec addr n).
      * subst.
        exists (n1, t1); auto.
        eapply Heap.add_1; eauto.
      * exists v.
        eapply Heap.add_2; eauto.
    + rewrite H2 in Hyp.
      destruct Hyp as [v Hv].
      destruct (Nat.eq_dec addr n).
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