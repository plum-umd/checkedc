Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Structures.Monads.

From CHKC Require Import Tactics ListUtil Map.
Require Import Coq.FSets.FMapFacts.
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
  | TFun : bound -> type -> list type -> type. (* bound refers to the function name. *)

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


Module Env := Map.Make Nat_as_OT.
Module EnvFacts := FMapFacts.Facts (Env).
Definition env := Env.t type.

Definition empty_env := @Env.empty type.

Definition venv := Env.t var.

Definition empty_venv := @Env.empty var.

(* well_bound definition might not needed in the type system, since the new
   [expr_wf] will guarantee that. *)
Definition is_ptr (t : type) : Prop :=
    match t with TPtr m x => True 
              | _ => False
    end.

Inductive well_bound_in : env -> bound -> Prop :=
   | well_bound_in_num : forall env n, well_bound_in env (Num n)
   | well_bound_in_var : forall env x y, Env.MapsTo x TNat env -> well_bound_in env (Var x y).

(*
Definition well_ptr_bound_in (env:env) (p:ptrMode) :=
   match p with None => True
           | Some (t,a) => 
            match a with VarPtr x => Env.MapsTo x TNat env
                      | NumPtr n => True
             end
   end.
*)

Inductive well_type_bound_in : env -> type -> Prop :=
   | well_type_bound_in_nat : forall env, well_type_bound_in env TNat
   | well_type_bound_in_ptr : forall m t env, well_type_bound_in env t -> well_type_bound_in env (TPtr m t)
   | well_type_bound_in_struct : forall env T, well_type_bound_in env (TStruct T)
   | well_type_bound_in_array : forall env l h t, well_bound_in env l -> well_bound_in env h -> 
                                      well_type_bound_in env t -> well_type_bound_in env (TArray l h t)
   | well_type_bound_in_ntarray : forall env l h t, well_bound_in env l -> well_bound_in env h -> 
                                      well_type_bound_in env t -> well_type_bound_in env (TNTArray l h t)
   | well_type_bound_fun : forall env b t ts, well_bound_in env b -> well_type_bound_in env t
                      -> (forall t', In t' ts -> well_type_bound_in env t') -> well_type_bound_in env (TFun b t ts).

(* Definition of simple type meaning that no bound variables. *)
Inductive simple_type : type -> Prop := 
  | SPTNat : simple_type TNat
  | SPTPtr : forall m w, simple_type w -> simple_type (TPtr m w)
  | SPTStruct : forall t, simple_type (TStruct t)
  | SPTArray : forall l h t, simple_type t -> simple_type (TArray (Num l) (Num h) t)
  | SPTNTArray : forall l h t, simple_type t -> simple_type (TNTArray (Num l) (Num h) t)
  | SPTFun: forall l t ts, simple_type t -> (forall t', In t' ts -> simple_type t') -> simple_type (TFun (Num l) t ts).

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

Inductive type_wf (D : structdef) : mode -> type -> Prop :=
  | WFTNat : forall m, type_wf D m (TNat)
  | WFTPtrChecked : forall m w, type_wf D m w -> type_wf D Checked (TPtr m w)
  | WFTPtrUnChecked : forall m m' w, m <> Checked -> m' <> Checked -> type_wf D m w -> type_wf D m (TPtr m' w)
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
  
  | WFTFun : forall m b t ts, word_type t -> type_wf D m t -> 
          (forall t', In t' ts -> word_type t' /\ type_wf D m t') -> type_wf D m (TFun b t ts).

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


Inductive theta_elem : Type := TopElem | GeZero.

Module Theta := Map.Make Nat_as_OT.

Definition theta := Theta.t theta_elem.

Definition empty_theta := @Theta.empty theta_elem.

(* This defines the subtyping relation. *)
Inductive nat_leq (T:theta) : bound -> bound -> Prop :=
| nat_leq_num : forall l h, l <= h -> nat_leq T (Num l) (Num h)
| nat_leq_var : forall x l h, l <= h -> nat_leq T (Var x l) (Var x h)
| nat_leq_num_var : forall x l h,
    Theta.MapsTo x GeZero T -> l <= h -> nat_leq T (Num l) (Var x h).

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
Inductive subtype (D : structdef) (Q:theta) : type -> type -> Prop :=
| SubTypeFun : forall m b t t' tl tl',
    subtype D Q t' t ->
    (forall n ta tb,
        nth_error tl n = Some ta ->
        nth_error tl' n = Some tb ->
        subtype D Q ta tb) ->
    subtype D Q (TPtr m (TFun b t tl)) (TPtr m (TFun b t' tl'))
| SubTyRefl : forall t, subtype D Q t t
| SubTyTainted : forall t t', subtype D Q (TPtr Tainted t) (TPtr Unchecked t')
| SubTyBot : forall m l h t, word_type t -> nat_leq Q (Num 0) l -> nat_leq Q h (Num 1)
                             -> subtype D Q (TPtr m t) (TPtr m (TArray l h t))
| SubTyOne : forall m l h t, word_type t -> nat_leq Q l (Num 0) -> nat_leq Q (Num 1) h
                             -> subtype D Q (TPtr m (TArray l h t)) (TPtr m t)
| SubTyOneNT : forall m l h t, word_type t -> nat_leq Q l (Num 0) -> nat_leq Q (Num 1) h
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

Lemma subtype_trans : forall D Q t t' m w,
    subtype D Q t (TPtr m w) -> subtype D Q (TPtr m w) t' -> subtype D Q t t'.
Admitted.
(*
Proof.
 intros. inv H; inv H0.
 * eapply SubTyRefl.
      * eapply SubTyTaintedNTArray;easy.
      * eapply SubTyTaintedArray;easy.
      * eapply SubTyTaintedStruct;easy.
      * eapply SubTyBot;eauto.
      * eapply SubTyOne; eauto.
      * eapply SubTyOneNT; eauto.
      * eapply SubTySubsume; eauto.
      * eapply SubTyNtArray; eauto.
      * eapply SubTyNtSubsume; eauto.
      * eapply SubTyStructArrayField_1; eauto.
      * eapply SubTyStructArrayField_2; eauto.
      * eapply SubTyTaintedNTArray;eauto.
      * inv H3.
      * inv H3.
      * inv H3.
      * eapply SubTyTaintedArray;easy.
      * inv H3.
      * inv H3.
      * inv H3.
      * eapply SubTyTaintedStruct;easy.
      * eapply SubTyBot; eauto.
      * inv H1.
      * eapply SubTyRefl.
      * eapply SubTyBot;eauto. eapply nat_leq_trans. apply H5. assumption.
         eapply nat_leq_trans. apply H9. assumption.
      * eapply SubTyOne; eauto.
      * eapply SubTySubsume;eauto.
        eapply nat_leq_trans. apply H5. assumption.
        eapply nat_leq_trans. apply H4. assumption.
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
        eapply nat_leq_trans. apply H4. assumption.
      * inv H3.
      * inv H3.
      * inv H3.
      * inv H3.
      * inv H3.
      * inv H3.
      * inv H3.
      * eapply SubTySubsume; eauto.
      * eapply SubTyTaintedArray;easy.
      * inv H2.
      * eapply SubTyOne; eauto.
        eapply nat_leq_trans. apply H4. assumption.
        eapply nat_leq_trans. apply H9. assumption.
      * eapply SubTySubsume; eauto.
        eapply nat_leq_trans. apply H4. assumption.
        eapply nat_leq_trans. apply H8. assumption.
      * eapply SubTyNtArray; eauto.
      * eapply SubTyTaintedNTArray;easy.
      * inv H2.
      * eapply SubTyOneNT; eauto.
        eapply nat_leq_trans. apply H4. assumption.
        eapply nat_leq_trans. apply H9. assumption.
      * eapply SubTyNtArray; eauto.
        eapply nat_leq_trans. apply H4. assumption.
        eapply nat_leq_trans. apply H8. assumption.
      * eapply SubTyNtSubsume; eauto.
      * eapply SubTyTaintedNTArray;easy.
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
      * inv H1.
      * eapply SubTyStructArrayField_1; eauto.
      * eapply SubTyStructArrayField_2; eauto.
        eapply nat_leq_trans. apply H6. assumption.
        eapply nat_leq_trans. apply H10. assumption.
Qed.

*)

(* Defining stack. *)
Module Stack := Map.Make Nat_as_OT.

Definition stack := Stack.t (Z * type).

Definition empty_stack := @Stack.empty (Z * type).

Definition arg_stack := Stack.t bound.

Definition empty_arg_stack := @Stack.empty bound.

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

Inductive eval_type_bound (s:stack) : type -> type -> Prop :=
   | eval_type_bound_nat : eval_type_bound s (TNat) (TNat)
   | eval_type_bound_ptr : forall c t t', eval_type_bound s t t'
                 -> eval_type_bound s (TPtr c t) (TPtr c t')
   | eval_type_bound_array : forall l l' h h' t t', cast_bound s l = Some l' -> cast_bound s h = Some h' ->
                  eval_type_bound s t t' -> eval_type_bound s (TArray l h t) (TArray l' h' t')
   | eval_type_bound_ntarray : forall l l' h h' t t', cast_bound s l = Some l' -> cast_bound s h = Some h' ->
                  eval_type_bound s t t' -> eval_type_bound s (TNTArray l h t) (TNTArray l' h' t')
   | eval_type_bound_struct : forall t, eval_type_bound s (TStruct t) (TStruct t).
*)

Inductive expression : Type :=
  | ELit : Z -> type -> expression
  | EVar : var -> expression
  | EStrlen : var -> expression
  | ECall : expression -> list expression -> expression
  | ERet : var -> Z* type -> option (Z * type) -> expression -> expression (* return new value, old value and the type. *)
  | EDynCast : type -> expression -> expression
  | ELet : var -> expression -> expression -> expression
  | EMalloc : mode -> type -> expression
  | ECast : type -> expression -> expression
  | EPlus : expression -> expression -> expression
  | EFieldAddr : expression -> field -> expression
  | EDeref : expression -> expression (*  * e *)
  | EAssign : expression -> expression -> expression (* *e = e *)
  | EIfDef : var -> expression -> expression -> expression (* if * x then e1 else e2. *)
  | EIfPtrEq : expression -> expression -> expression -> expression -> expression (* if e1 = e2 then e3 else e4. *)
  | EIfPtrLt : expression -> expression -> expression -> expression -> expression (* if e1 < e2 then e3 else e4. *)
  | EIf : expression -> expression -> expression -> expression (* if e1 then e2 else e3. *)
  | EUnchecked : expression -> expression.

Definition funElem : Type := (list (var * type) * type * expression * mode).

Parameter fenv : Z -> option funElem.

Definition FEnv : Type := Z -> option funElem.

Definition Ffield : Type := Z -> option Z.

Inductive gen_arg_env : env -> list (var * type) -> env -> Prop :=
    gen_arg_env_empty : forall env, gen_arg_env env [] env
  | gen_ar_env_many : forall env x t tvl env', gen_arg_env env tvl env' -> gen_arg_env env ((x,t)::tvl) (Env.add x t env').

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


Definition simple_option (D : structdef) (a:option (Z*type)) :=
  match a with None => True
          | Some (v,t) => word_type t /\ type_wf D Checked t /\ simple_type t
  end.

Inductive expr_wf (D : structdef) : expression -> Prop :=
  | WFELit : forall n t,
    word_type t ->
    type_wf D Checked t ->
    simple_type t ->
    expr_wf D (ELit n t)
  | WFEVar : forall x,
      expr_wf D (EVar x)
  | WFEStr : forall x,
      expr_wf D (EStrlen x)
  | WFECall : forall xe el, 
      expr_wf D xe ->
      (forall e, In e el -> (exists n t, e = ELit n t
                 /\ word_type t /\ type_wf D Checked t /\ simple_type t) \/ (exists y, e = EVar y)) ->
      expr_wf D (ECall xe el)
  | WFRet : forall x old a e, simple_option D (Some old) -> simple_option D a -> expr_wf D e -> expr_wf D (ERet x old a e)
  | WFEDynCast : forall t e, 
     is_array_ptr t -> type_wf D Checked t -> expr_wf D e -> expr_wf D (EDynCast t e)
  | WFELet : forall x e1 e2,
      expr_wf D e1 ->
      expr_wf D e2 ->
      expr_wf D (ELet x e1 e2)
  | WFEIFDef : forall x e1 e2,
      expr_wf D e1 ->
      expr_wf D e2 ->
      expr_wf D (EIfDef x e1 e2)
  | WFEIF : forall e1 e2 e3,
      expr_wf D e1 ->
      expr_wf D e2 ->
      expr_wf D e3 ->
      expr_wf D (EIf e1 e2 e3)
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
  | WFEMalloc : forall m w,
      type_wf D m w -> expr_wf D (EMalloc m w)
  | WFECast : forall t e,
      word_type t ->
      type_wf D Checked t ->
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
   then we don't substitute under the lambda. *)
 

(** Values, [v], are expressions [e] which are literals. *)

Inductive value (D : structdef) : expression -> Prop :=
  VLit : forall (n : Z) (t : type),
    word_type t ->
    type_wf D Checked t ->
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

(** Real Heaps, [R], consist of 2 heaps that represents (checked * tainted)
    heaps
 *)
Definition real_heap : Type := heap * heap. 

Definition heap_wf (D : structdef) (R : real_heap) : Prop :=
  (forall (addr : Z),
      0 < addr <= (Z.of_nat (Heap.cardinal (fst R))) <-> Heap.In addr (fst R))
  /\ (forall (addr : Z),
         0 < addr <= (Z.of_nat (Heap.cardinal (snd R))) <-> Heap.In addr (snd R)).

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
    Some (0, Zreplicate (h - l) T)
  | TNTArray (Num l) (Num h) T =>
    Some (0, Zreplicate (h - l + 1) T)
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

Inductive context : Type :=
  | CHole : context
  | CLet : var -> context -> expression -> context
  | CCall : context -> list expression -> context
  | CPlusL : context -> expression -> context
  | CPlusR : Z -> type -> context -> context
  | CFieldAddr : context -> field -> context
  | CDynCast : type -> context -> context
  | CCast : type -> context -> context
  | CDeref : context -> context
  | CAssignL : context -> expression -> context
  | CAssignR : Z -> type -> context -> context
  | CRet : var -> (Z*type) -> option (Z * type) -> context -> context
  | CIfEqL : context -> expression -> expression -> expression -> context
  | CIfEqR : expression -> context -> expression -> expression -> context
  | CIfLtL : context -> expression -> expression -> expression -> context
  | CIfLtR : expression -> context -> expression -> expression -> context
  | CIf : context -> expression -> expression -> context
  | CUnchecked : context -> context.

Fixpoint in_hole (e : expression) (E : context) : expression :=
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
  | CRet x old a E' => ERet x old a (in_hole e E')
  | CIf E' e1 e2 => EIf (in_hole e E') e1 e2
  | CIfEqL E' e1 e2 e3 => EIfPtrEq (in_hole e E') e1 e2 e3
  | CIfEqR e1 E' e2 e3 => EIfPtrEq e1 (in_hole e E') e2 e3
  | CIfLtL E' e1 e2 e3 => EIfPtrLt (in_hole e E') e1 e2 e3
  | CIfLtR e1 E' e2 e3 => EIfPtrLt e1 (in_hole e E') e2 e3
  | CUnchecked E' => EUnchecked (in_hole e E')
  end.


Fixpoint mode_of (E : context) : mode :=
  match E with
  | CHole => Checked
  | CLet _ E' _ => mode_of E'
  | CCall E' _ => mode_of E'
  | CPlusL E' _ => mode_of E'
  | CPlusR _ _ E' => mode_of E'
  | CFieldAddr E' _ => mode_of E'
  | CDynCast _ E' => mode_of E'
  | CCast _ E' => mode_of E'
  | CDeref E' => mode_of E'
  | CAssignL E' _ => mode_of E'
  | CAssignR _ _ E' => mode_of E'
  | CRet x old a E' => mode_of E'
  | CIf E' e1 e2 => mode_of E'
  | CIfEqL E' e1 e2 e3 => mode_of E'
  | CIfEqR e1 E' e2 e3 => mode_of E'
  | CIfLtL E' e1 e2 e3 => mode_of E'
  | CIfLtR e1 E' e2 e3 => mode_of E'
  | CUnchecked E' => Unchecked
  end.

Fixpoint compose (E_outer : context) (E_inner : context) : context :=
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
  | CRet x old a E' => CRet x old a (compose E' E_inner)
  | CIf E' e1 e2 => CIf (compose E' E_inner) e1 e2
  | CIfEqL E' e1 e2 e3 => CIfEqL (compose E' E_inner) e1 e2 e3
  | CIfEqR e1 E' e2 e3 => CIfEqR e1 (compose E' E_inner) e2 e3
  | CIfLtL E' e1 e2 e3 => CIfLtL (compose E' E_inner) e1 e2 e3
  | CIfLtR e1 E' e2 e3 => CIfLtR e1 (compose E' E_inner) e2 e3

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

Definition eval_bound (s:stack) (b:bound) : option bound :=
   match b with Num n => Some (Num n)
             | Var x n => (match (Stack.find x s) with Some (v,t) => Some (Num (v + n)) | None => None end)
   end.

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
  | TFun b t ts =>
      match (eval_bound s b,eval_type_bound s t) with
        | (Some b',Some t') => 
            match (fold_left
                     (fun r => fun ta =>
                        match r with
                        | None => None
                        | Some l =>
                            match eval_type_bound s ta with
                            | None => None
                            | Some ta' => Some (l++[ta'])
                            end
                        end)
                     ts (Some []))
            with
            | None => None
            | Some ts' => Some (TFun b' t' ts')
            end
      | _ => None end
  end. 

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
            | TFun b t tl => TFun (subst_bounds b s) (subst_type s t) (map (fun x => subst_type s x) tl)
  end.

Inductive eval_arg : stack -> expression -> type -> expression -> Prop :=
| eval_lit : forall arg_s n t t' t'',
    eval_type_bound arg_s t = Some t'' ->
    eval_arg arg_s (ELit n t') t (ELit n t'')
| eval_var : forall arg_s x n t t' t'',
    Stack.MapsTo x (n,t') arg_s ->
    eval_type_bound arg_s t = Some t'' ->
    eval_arg arg_s (EVar x) t (ELit n t'').

Inductive eval_el (AS: list (var*bound))
  : stack -> list (var * type) -> list expression -> stack -> Prop :=
| eval_el_empty : forall s, eval_el AS s [] [] s
| eval_el_many_2 : forall s s' e x n t t' tvl es,
    eval_arg s e (subst_type AS t) (ELit n t') ->
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
| get_root_struct : forall m T f,
    StructDef.MapsTo T f D ->
    Some (TNat) = (Fields.find 0%nat f) ->
    @get_root D (TPtr m (TStruct T)) TNat.

Inductive gen_rets  (AS: list (var*bound)) (S: stack)
  : list (var * type) -> list expression -> expression -> expression -> Prop :=
  gen_rets_empty : forall e, gen_rets AS S [] [] e e
| gen_rets_many : forall x t t' xl e1 v es e2 e',
    gen_rets AS S xl es e2 e' ->
    eval_arg S e1 (subst_type AS t) (ELit v t') ->
    gen_rets AS S ((x,t)::xl) (e1::es) e2 (ERet x (v,t') (Stack.find x S) e').

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
   match t with TPtr m (TNTArray (Num l) (Num h) t) =>
    exists n' t', (0 <= n' /\ Heap.MapsTo (n+n') (0,t') H
     /\ (forall i , n <= i < n+n' -> (exists n1, Heap.MapsTo i (n1,t') H /\ n1 <> 0)))
   | _ => True
   end.

Definition tfun_prop (F:Z -> option funElem) (n:Z) (t:type) := 
   match t with TFun (Num n') t ts => ((n = n') /\ F n <> None) | _ => True end.


Inductive well_typed_lit (D : structdef) (F:Z -> option funElem) (Q:theta) (H : heap) : scope -> Z -> type -> Prop :=
  | TyLitInt : forall s n,
      well_typed_lit D F Q H s n TNat
  | TyLitU : forall s n w,
      well_typed_lit D F Q H s n (TPtr Unchecked w)
  | TyLitZero : forall s t,
      well_typed_lit D F Q H s 0 t
  | TyLitFun : forall s n t ts, F n <> None -> well_typed_lit D F Q H s n (TFun (Num n) t ts)
  | TyLitRec : forall s n m w t,
      m <> Unchecked -> set_In (n, t) s -> 
      subtype D Q t (TPtr m w) ->
      well_typed_lit D F Q H s n (TPtr m w)
  | TyLitC : forall sc n m w t b ts,
      simple_type w -> m <> Unchecked ->
      subtype D Q (TPtr m w) (TPtr m t) ->
      Some (b, ts) = allocate_meta D w ->
      nt_array_prop H n (TPtr m t) ->
      (forall k, b <= k < b + Z.of_nat(List.length ts) ->
                 exists n' t',
                   Some t' = List.nth_error ts (Z.to_nat (k - b)) /\
                   Heap.MapsTo (n + k) (n', t') H /\
                   well_typed_lit D F Q H (scope_set_add n (TPtr m w) sc) n' t') ->
      well_typed_lit D F Q H sc n (TPtr m t).

(** It turns out, the induction principle that Coq generates automatically isn't very useful. *)

(** In particular, the TyLitC case does not have an induction hypothesis.
    So, we prove an alternative induction principle which is almost identical but includes
    an induction hypothesis for the TyLitC case.

    TODO: write blog post about this *)
Lemma well_typed_lit_ind' :
  forall (D : structdef) (F: Z -> option funElem) (Q:theta) (H : heap) (P : scope -> Z -> type -> Prop),
    (forall (s : scope) (n : Z), P s n TNat) ->
       (forall (s : scope) (n : Z) (w : type), P s n (TPtr Unchecked w)) ->
       (forall (s : scope) (t : type), P s 0 t) ->
       (forall (s: scope) (n:Z) (t:type) (ts: list type), F n <> None -> P s n (TFun (Num n) t ts)) ->
       (forall (s : scope) (n : Z) (m:mode) (w : type) (t : type),
            m <> Unchecked -> set_In (n, t) s -> subtype D Q t (TPtr m w) -> P s n (TPtr m w)) ->
       (forall (s : scope) (n : Z) (m:mode) (w : type) (t: type) (ts : list type) (b : Z),
        simple_type w ->  m <> Unchecked ->
        subtype D Q (TPtr m w) (TPtr m t) ->
        Some (b, ts) = allocate_meta D w ->
        nt_array_prop H n (TPtr m t) ->
        (forall k : Z,
         b <= k < b + Z.of_nat (length ts) ->
         exists (n' : Z) (t' : type),
           Some t' = nth_error ts (Z.to_nat (k - b)) /\
           Heap.MapsTo (n + k) (n', t') H /\
           well_typed_lit D F Q H (scope_set_add n (TPtr m w) s) n' t' /\
           P (scope_set_add n (TPtr m w) s) n' t') ->
        P s n (TPtr m t)) -> forall (s : scope) (n : Z) (w : type), well_typed_lit D F Q H s n w -> P s n w.
Proof.
  intros D F Q H P.
  intros HTyLitInt
         HTyLitU
         HTyLitZero
         HTyLitFun
         HTyLitRec
         HTyLitC.
  refine (fix F s n t Hwtl :=
            match Hwtl with
            | TyLitInt _ _ _ _ s' n' => HTyLitInt s' n'
            | TyLitU _ _ _ _ s' n' w' => HTyLitU s' n' w'
            | TyLitZero _ _ _ _ s' t' => HTyLitZero s' t'
            | TyLitFun _ _ _ _ s' n' t' ts' HF => HTyLitFun s' n' t' ts' HF
            | TyLitRec _ _ _ _ s' n' m' w' t' HMode Hscope Hsub => HTyLitRec s' n' m' w' t' HMode Hscope Hsub
            | TyLitC _ _ _ _ s' n' m' w' t' b ts HSim HMode Hsub Hts Hnt IH =>
              HTyLitC s' n' m' w' t' ts b HSim HMode Hsub Hts Hnt (fun k Hk =>
                                         match IH k Hk with
                                         | ex_intro _ n' Htmp =>
                                           match Htmp with
                                           | ex_intro _ t' Hn't' =>
                                             match Hn't' with
                                             | conj Ht' Hrest1 =>
                                             match Hrest1 with
                                               | conj Hheap Hwt =>
                                                 ex_intro _ n' (ex_intro _ t' 
                     (conj Ht' (conj Hheap (conj Hwt (F (scope_set_add _ (TPtr m' w') s') n' t' Hwt)))))
                                               end
                                             end
                                           end
                                       end)
            end).
Qed.

Definition add_value (H:heap) (n:Z) (t:type) :=
   match t with TFun (Num na) ta tas => Heap.add n (na,t) H
              | _ => H
   end.


Hint Constructors well_typed_lit.

(** Memory, [M], is the composition of stack, checked heap and tainted heap *)
Definition mem : Type := stack * real_heap.

(** **Checked C semantics** *)
(** The single-step reduction relation, [H; e ~> H'; r]. *)
Inductive step
  (D : structdef) 
  (F:Z -> option (list (var * type) * type * expression * mode))
  : mem -> expression -> mem -> result -> Prop :=
| SVar : forall s R x v t,
    (Stack.MapsTo x (v,t) s) ->
    step D F
      (s, R) (EVar x)
      (s, R) (RExpr (ELit v t))
| StrlenChecked : forall s H1 H2 x n n' l h t t1, 
    h > n -> l <= n -> 0 <= n' ->
    (Stack.MapsTo x (n,(TPtr Checked (TNTArray (Num l) (Num h) t))) s) ->
    (forall i ,
        n <= i < n+n'+1 ->
        (exists n1, Heap.MapsTo i (n1,t1) H1 /\ n1 <> 0)) ->
    Heap.MapsTo (n+n'+1) (0,t1) H1 ->
    step D F
      (s, (H1,H2)) (EStrlen x)
      ((change_strlen_stack s x Checked t l n n' h), (H1,H2))
      (RExpr (ELit n' TNat))
| StrlenTainted : forall s H1 H2 x n n' l h t t1, 
    h > n -> l <= n -> 0 <= n' ->
    (Stack.MapsTo x (n,(TPtr Tainted (TNTArray (Num l) (Num h) t))) s) ->
    (forall i ,
        n <= i < n+n'+1 ->
        (exists n1, Heap.MapsTo i (n1,t1) H2 /\ n1 <> 0 
                    /\ well_typed_lit D F empty_theta H2 empty_scope n1 t1)) ->
    Heap.MapsTo (n+n'+1) (0,t1) H2 ->
    step D F
      (s, (H1,H2)) (EStrlen x)
      ((change_strlen_stack s x Tainted t l n n' h), (H1,H2))
      (RExpr (ELit n' TNat))
| StrlenUnChecked : forall s H1 H2 x n n' t t1, 
    0 <= n' ->
    (Stack.MapsTo x (n,(TPtr Unchecked t)) s) ->
    (forall i ,
        n <= i < n+n'+1 -> (exists n1, Heap.MapsTo i (n1,t1) H2 /\ n1 <> 0)) ->
    Heap.MapsTo (n+n'+1) (0,t1) H2 ->
    step D F
      (s, (H1,H2)) (EStrlen x)
      (s, (H1,H2)) (RExpr (ELit n' TNat))
(*          
  | StrlenNone : forall s H1 H2 x m  n l h t, m <> Unchecked ->
     (Stack.MapsTo x (n,(TPtr m  (TNTArray l h t))) s) ->
            step D U F s (H1,H2) (EStrlen x) s (H1,H2) (RNull).

  | StrlenHighOOB : forall s H x m pm n t l h,
      h <= n -> m <> Unchecked ->
     (Stack.MapsTo x (n,(TPtr m pm (TNTArray l (Num h) t))) s) ->
      step D U F s H (EStrlen x) s H RBounds
  | StrlenLowOOB : forall s H x m pm n t l h,
      l > n -> m <> Unchecked ->
     (Stack.MapsTo x (n,(TPtr m pm (TNTArray (Num l) h t))) s) ->
      step D U F s H (EStrlen x) s H RBounds
 *)  
| StrlenNull : forall s R x t m n l h,
    n <= 0 -> m <> Unchecked ->
    (Stack.MapsTo x (n,(TPtr m (TNTArray l h t))) s) ->
    step D F
      (s, R) (EStrlen x)
      (s, R) RNull
| SCallChecked : forall AS s s' R x ta ts el t tvl e e' n t1, 
    Heap.MapsTo x (n, t1) (fst R) ->
    F n = Some (tvl,t,e,Checked) ->
    get_dept_map tvl el = Some AS ->
    eval_el AS s tvl el s' -> 
    gen_rets AS s tvl el e e' ->
    step D F
      (s, R)  (ECall (ELit x (TPtr Checked (TFun (Num n) ta ts))) el)
      (s', R) (RExpr (ECast (subst_type AS t) e'))
| SCallBound : forall s R x m ta ts el n' n t1, 
    Heap.MapsTo x (n, t1) (fst R) ->
    step D F
      (s, R) (ECall (ELit x (TPtr m (TFun (Num n') ta ts))) el)
      (s, R) RBounds
| SCallNull : forall s R x m ta ts el n' n t1, 
    Heap.MapsTo x (n, t1) (fst R) ->
    F n = None ->
    step D F
      (s, R) (ECall (ELit x (TPtr m (TFun (Num n') ta ts))) el)
      (s, R) RNull

| SCallUnChecked : forall AS s s' R x ta ts el t tvl e e' n n' t1 m m', 
    Heap.MapsTo x (n, t1) (snd R) -> m <> Checked -> m' <> Checked ->
    F n = Some (tvl,t,e,m) ->
    get_dept_map tvl el = Some AS ->
    eval_el AS s tvl el s' -> 
    gen_rets AS s tvl el e e' ->
    step D F
      (s, R) (ECall (ELit x (TPtr m' (TFun (Num n') ta ts))) el)
      (s', R) (RExpr (ECast (subst_type AS t) e'))
| SLet : forall s R x n t e t',
    eval_type_bound s t = Some t' ->
    step D F 
      (s, R) (ELet x (ELit n t) e)
      (Stack.add x (n,t') s,  R)
      (RExpr (ERet x (n,t') (Stack.find x s) e))

| SRetSome : forall s R x a ta ntb n t, 
    step D F
      (s, R) (ERet x ntb (Some (a,ta)) (ELit n t))
      (Stack.add x (a,ta) s, R) (RExpr (ELit n t))
| SRetNone : forall s R x ntb n t, 
    step D F
      (s, R)
      (ERet x ntb None (ELit n t))
      (Stack.remove x s, R) (RExpr (ELit n t))
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
    eval_type_bound s t = Some t'' ->
    step D F
      (s, R) (ECast t (ELit n t'))
      (s, R) (RExpr (ELit n t''))

| SCastNotArray : forall s R x y t n m t' t'',
    ~ is_array_ptr (TPtr m t') -> eval_type_bound s t = Some t'' ->
    step D F
      (s, R) (EDynCast (TPtr m (TArray x y t)) (ELit n (TPtr m t')))
      (s, R) (RExpr (ELit n (TPtr m (TArray (Num n) (Num (n+1)) t''))))

| SCastArray : forall s R t n t' l h w l' h' w',
    eval_type_bound s t = Some (TPtr Checked (TArray (Num l) (Num h) w)) ->
    eval_type_bound s t' = Some (TPtr Checked (TArray (Num l') (Num h') w')) ->
    l' <= l -> l < h -> h <= h' ->
    step D F
      (s, R) (EDynCast t (ELit n t'))
      (s, R) (RExpr (ELit n (TPtr Checked (TArray (Num l) (Num h) w))))
(*
  | SCastArrayLowOOB1 : forall s H t n pm t' l h w l' h' w',
     eval_type_bound s t (TPtr Checked pm (TArray (Num l) (Num h) w)) ->
      eval_type_bound s t' (TPtr Checked pm (TArray (Num l') (Num h') w')) ->
           l < l' -> 
           step D U F s H (EDynCast t (ELit n t'))  s H RBounds
  | SCastArrayLowOOB2 : forall s H t n pm t' l h w l' h' w',
     eval_type_bound s t (TPtr Checked pm (TArray (Num l) (Num h) w)) ->
      eval_type_bound s t' (TPtr Checked pm (TArray (Num l') (Num h') w')) ->
           h <= l -> 
           step D U F s H (EDynCast t (ELit n t')) s H RBounds
  | SCastArrayHighOOB1 : forall s H t n pm t' l h w l' h' w',
     eval_type_bound s t (TPtr Checked pm (TArray (Num l) (Num h) w)) ->
      eval_type_bound s t' (TPtr Checked pm (TArray (Num l') (Num h') w')) ->
           h' < h -> 
           step D U F s H (EDynCast t (ELit n t')) s H RBounds
 *)
| SCastNTArray : forall s R t n t' l h w l' h',
    eval_type_bound s t = Some (TPtr Checked (TNTArray (Num l) (Num h) w)) ->
    l' <= l -> l < h -> h <= h' ->
    step D F
      (s, R) (EDynCast t (ELit n t'))
      (s, R) (RExpr (ELit n (TPtr Checked (TNTArray (Num l) (Num h) w))))
(*
  | SCastNTArrayLowOOB1 : forall s H t n pm t' l h w l' h' w',
     eval_type_bound s t (TPtr Checked pm (TNTArray (Num l) (Num h) w)) ->
      eval_type_bound s t' (TPtr Checked pm (TNTArray (Num l') (Num h') w')) ->
           l < l' -> 
           step D U F s H (EDynCast t (ELit n t')) s H RBounds
  | SCastNTArrayLowOOB2 : forall s H t n pm t' l h w l' h' w',
     eval_type_bound s t (TPtr Checked pm (TNTArray (Num l) (Num h) w)) ->
      eval_type_bound s t' (TPtr Checked pm (TNTArray (Num l') (Num h') w')) ->
           h <= l -> 
           step D U F s H (EDynCast t (ELit n t')) s H RBounds
  | SCastNTArrayHighOOB1 : forall s H t n pm t' l h w l' h' w',
     eval_type_bound s t (TPtr Checked pm (TNTArray (Num l) (Num h) w)) ->
      eval_type_bound s t' (TPtr Checked pm (TNTArray (Num l') (Num h') w')) ->
           h' < h -> 
           step D U F s H (EDynCast t (ELit n t')) s H RBounds
 *)
| SDerefChecked : forall s H1 H2 n n1 t1 t t2 tv,
    eval_type_bound s (TPtr Checked t) = Some t2 ->
    Heap.MapsTo n (n1, t1) H1 ->
    (forall l h t',
        t2 = TPtr Checked (TArray (Num l) (Num h) t') -> l <= n < h) ->
    (forall l h t',
        t2 = TPtr Checked (TNTArray (Num l) (Num h) t') -> l <= n < h) ->
    @get_root D t2 tv ->
    step D F
      (s, (H1,H2)) (EDeref (ELit n (TPtr Checked t)))
      (s, (H1,H2)) (RExpr (ELit n1 tv))
| SDerefTainted : forall s H1 H2 n n1 t1 t t2 tv,
    eval_type_bound s (TPtr Tainted t) = Some t2 ->
    Heap.MapsTo n (n1, t1) H2 ->
    well_typed_lit D F empty_theta H2 empty_scope n1 t1 ->
    (forall l h t',
        t2 = TPtr Tainted (TArray (Num l) (Num h) t') -> l <= n < h) ->
    (forall l h t',
        t2 = TPtr Tainted (TNTArray (Num l) (Num h) t') -> l <= n < h) ->
    @get_root D t2 tv ->
    step D F
      (s, (H1,H2)) (EDeref (ELit n (TPtr Tainted t)))
      (s, (H1,H2)) (RExpr (ELit n1 tv))
(*
  | SDerefNone : forall s H1 H2 m n pm n1 t1 t t2 tv,
      eval_type_bound s (TPtr m pm t) t2 -> m <> Unchecked -> pm = None ->
      Heap.MapsTo n (n1, t1) H2 -> 
      @get_root D t2 tv ->
      step D U F s (H1,H2) (EDeref (ELit n (TPtr m pm t))) s (H1,H2) RNull
 *)
(* Add two rules for when pm = None. *)

| SDerefUnChecked : forall s H1 H2 m n n1 t1 t t2 tv,
    eval_type_bound s (TPtr m t) = Some t2 ->
    Heap.MapsTo n (n1, t1) H2 ->
    m <> Checked ->
    @get_root D t2 tv ->
    step D F
      (s, (H1,H2)) (EDeref (ELit n (TPtr m t)))
      (s, (H1,H2)) (RExpr (ELit n1 tv))
(*
  | SDerefHighOOB : forall s H n t t' h,
      h <= n ->
      eval_type_bound s t t' ->
      get_high_ptr t' = Some (Num h) ->
      step D U F s H (EDeref (ELit n t)) s H RBounds
  | SDerefLowOOB : forall s H n t t' l,
      l > n ->
      eval_type_bound s t t' ->
      get_low_ptr t' = Some (Num l) ->
      step D U F s H (EDeref (ELit n t)) s H RBounds
  | SDerefNull : forall s H pm t n,
      n <= 0 -> pm = None ->
      step D U F s H (EDeref (ELit n (TPtr Checked pm t))) s H RNull
 *)
| SAssignChecked : forall s H1 H2 n t na ta tv n1 t1 tv',
    Heap.MapsTo n (na,ta) H1 ->
    eval_type_bound s (TPtr Checked t) = Some tv ->
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
    well_typed_lit D F empty_theta H2 empty_scope na ta ->
    eval_type_bound s (TPtr Tainted t) = Some tv ->
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
(* Add two rules for when pm = None. *)

| SAssignUnChecked : forall s H1 H2 m n t na ta tv n1 t1 tv',
    Heap.MapsTo n (na,ta) H2 -> m <> Checked ->
    eval_type_bound s (TPtr m t) = Some tv ->
    @get_root D tv tv' ->
    step D F
      (s, (H1,H2))  (EAssign (ELit n (TPtr m t)) (ELit n1 t1))
      (s, (H1,Heap.add n (n1, ta) H2)) (RExpr (ELit n1 tv'))
(*
  | SAssignHighOOB : forall s H n t t' n1 t1 h,
      h <= n ->
      eval_type_bound s t t' ->
      get_high_ptr t' = Some (Num h) ->
      step D U F
        s H (EAssign (ELit n t) (ELit n1 t1))
        s H RBounds
  | SAssignLowOOB : forall s H n t t' n1 t1 l,
      l > n ->
      eval_type_bound s t t' ->
      get_low_ptr t' = Some (Num l) ->
      step D U F
         s H (EAssign (ELit n t) (ELit n1 t1))
         s H RBounds
  | SAssignNull : forall s H t tv w m n n1 t' pm,
      n1 <= 0 -> m <> Unchecked ->
      eval_type_bound s t tv ->
      tv = TPtr m pm w ->
      pm = None ->
      step D U F
         s H (EAssign (ELit n1 t) (ELit n t')) s H RNull
 *)
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
    well_typed_lit D F empty_theta (snd R) empty_scope n0 t0 ->
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
    eval_type_bound s w = Some w' -> malloc_bound w' ->
    allocate D H1 w' = Some (n1, H1') ->
    step D F
      (s, (H1,H2)) (EMalloc Checked w)
      (s, (add_value H1' n1 w',H2)) (RExpr (ELit n1 (TPtr Checked w')))
| SMallocUnChecked : forall s H1 H2 m w w' H2' n1,
    eval_type_bound s w = Some w' -> malloc_bound w' -> m <> Checked ->
    allocate D H2 w' = Some (n1, H2') ->
    step D F
      (s, (H1,H2)) (EMalloc m w)
      (s, (H1,add_value H2' n1 w')) (RExpr (ELit n1 (TPtr m w')))
(*
  | SMallocHighOOB : forall s H m w t' h l,
      h <= l ->
      eval_type_bound s w t' ->
      get_high t' = Some (Num h) ->
      get_low t' = Some (Num l) ->
      step D U F s H (EMalloc m w)  s H RBounds

  | SMallocLowOOB : forall s H m w t' l,
      l <> 0 ->
      eval_type_bound s w t' ->
      get_low t' = Some (Num l) ->
      step D U F s H (EMalloc m w)  s H RBounds
 *)
| SUnchecked : forall s R n,
    step D F
      (s, R) (EUnchecked (ELit n TNat))
      (s, R) (RExpr (ELit n TNat))
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
      (s, R) (RExpr e2)
| SIfEqTrue : forall s R n t t' e1 e2,
    step D F
      (s, R) (EIfPtrEq (ELit n t) (ELit n t') e1 e2)
      (s, R) (RExpr e1)
| SIfEqFalse : forall s R n n' t t' e1 e2,
    n <> n' ->
    step D F
      (s, R) (EIfPtrEq (ELit n t) (ELit n' t') e1 e2)
      (s, R) (RExpr e2)
| SIfLtTrue : forall s R n n' t t' e1 e2, 
    n < n' ->
    step D F
      (s, R) (EIfPtrLt (ELit n t) (ELit n' t') e1 e2)
      (s, R) (RExpr e1)
| SIfLtFalse : forall s R n n' t t' e1 e2,  
    n' <= n ->
    step D F
      (s, R) (EIfPtrLt (ELit n t) (ELit n' t') e1 e2)
      (s, R) (RExpr e2).

Hint Constructors step.

Inductive reduce
  (D : structdef)
  (F:Z -> option (list (var * type) * type * expression * mode))
  : mem -> expression -> mode -> mem -> result -> Prop :=
  | RSExp : forall M e m M' e' E,
      step D F M e M' (RExpr e') ->
      m = mode_of(E) ->
      reduce D F
        M (in_hole e E)
        m
        M' (RExpr (in_hole e' E))
  | RSHaltNull : forall M e m M' E,
      step D F M e M' RNull ->
      m = mode_of(E) ->
      reduce D F 
        M (in_hole e E)
        m 
        M RNull
  | RSHaltBounds : forall M e m M' E,
      step D F M e M' RBounds ->
      m = mode_of(E) ->
      reduce D F 
        M (in_hole e E)
        m
        M' RBounds.

Hint Constructors reduce.

Definition reduces (D : structdef)
  (F:Z -> option (list (var * type) * type * expression * mode)) 
  (M : mem) (e : expression) : Prop :=
  exists (m : mode) (M' : mem) (r : result), reduce D F M e m M' r.

Hint Unfold reduces.


(* Defining function calls. *)

(** * Static Semantics *)


(*
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

*)


Definition is_nt_ptr (t : type) : Prop :=
    match t with TPtr m (TNTArray l h t') => True 
              | _ => False
    end.

(* equivalence of type based on semantic meaning. *)
Inductive type_eq (S : stack) : type -> type -> Prop := 
| type_eq_refl: forall t , type_eq S t t
| type_eq_left: forall t1 t2, simple_type t1 -> eval_type_bound S t2 = Some t1 -> type_eq S t2 t1
| type_eq_right: forall t1 t2, simple_type t2 -> eval_type_bound S t1 = Some t2 -> type_eq S t1 t2.

(* subtyping relation based on types. *)
Inductive subtype_stack (D: structdef) (Q:theta) (S:stack) : type -> type -> Prop :=
| subtype_same : forall t t', subtype D Q t t' -> subtype_stack D Q S t t'
| subtype_left : forall t1 t2 t2', simple_type t1 -> eval_type_bound S t2 = Some t2'
                                   -> subtype D Q t1 t2' -> subtype_stack D Q S t1 t2
| subtype_right : forall t1 t1' t2, simple_type t2 -> eval_type_bound S t1 = Some t1'
                                    -> subtype D Q t1' t2 -> subtype_stack D Q S t1 t2.

(* The join opeartions. *)
Inductive join_type (D : structdef) (Q:theta) (S:stack) : type -> type -> type -> Prop :=
  join_type_front : forall a b, subtype_stack D Q S a b -> join_type D Q S a b b
| join_type_end : forall a b, subtype_stack D Q S b a -> join_type D Q S a b a.

Definition good_lit (H:heap) (n:Z) (t:type):=
  match t with
    TNat => True
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
                        -> well_bound_vars_type l t -> well_bound_vars_type l (TNTArray b1 b2 t)
  | well_bound_vars_tfun : forall l b t ts, well_bound_vars l b -> well_bound_vars_type l t
        -> (forall t', In t' ts -> well_bound_vars_type l t') -> well_bound_vars_type l (TFun b t ts).


Inductive well_typed_arg (D: structdef) (F:Z -> option funElem) (Q:theta) (H : real_heap) (env:env): 
                mode -> expression -> type -> Prop :=
     | ArgLitChecked : forall n t t',
      simple_type t ->
      @well_typed_lit D F Q (fst H) empty_scope n t' ->
      subtype D Q t' t ->
      well_typed_arg D F Q H env Checked (ELit n t') t
     | ArgLitUnChecked : forall n t t',
      simple_type t ->
      well_typed_arg D F Q H env Unchecked (ELit n t') t
     | ArgVar : forall m x t t',
      Env.MapsTo x t' env -> 
      well_type_bound_in env t ->
      subtype D Q t' t ->
      well_typed_arg D F Q H env m (EVar x) t.

Inductive well_typed_args {D: structdef} {U:Z -> option funElem} {Q:theta} {H : real_heap}: 
                   env -> mode -> list expression -> list (type) -> Prop :=
     | args_empty : forall env m, well_typed_args env m [] []

     | args_many : forall env m e es t vl, 
                 well_typed_arg D U Q H env m e t ->
                        well_typed_args env m es vl
                        -> well_typed_args env m (e::es) (t::vl).

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
  match b with
  | Num n => []
  | Var x n => [x]
  end.

Fixpoint get_tvars (t:type) : (list var) :=
   match t with TNat => []
             | TPtr c t => get_tvars t
             | TStruct t => []
             | TArray l h t => get_tvar_bound l ++ get_tvar_bound h ++ get_tvars t
             | TNTArray l h t => get_tvar_bound l ++ get_tvar_bound h ++ get_tvars t
             | TFun b t tl => get_tvar_bound b ++ (get_tvars t)++(fold_left (fun acc t' => acc++(get_tvars t')) tl [])
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

Definition fun_mode_eq (m1 m2 :mode) : Prop :=
   (m2 = Checked /\ m1 = Checked) \/ (m2 = Unchecked /\ (m1 <> Checked)).

Definition mode_leq (m1 m2 :mode) : Prop :=
   (m2 = Checked /\ m1 <> Unchecked) \/ (m2 = Unchecked /\ (m1 <> Checked)).


Definition match_mode_ptr (t:type) (m:mode) :Prop :=
    match t with TPtr m1 t => mode_leq m1 m
             | _ => True
    end.

Definition is_fun_type (t:type) :=
   match t with TFun b x xl => True
             | _ => False
   end.

Definition is_off_zero (b:bound) :=
  match b with (Var x n) => (n = 0)
            | _ => True
  end.



(* The CoreChkC Type System. *)
Inductive well_typed { D : structdef } {F:Z -> option funElem} {S:stack} {H:real_heap}
        : env -> theta -> mode -> expression -> type -> Prop :=
  | TyLitChecked : forall env Q n t,
      @well_typed_lit D F Q (fst H) empty_scope n t ->
      well_typed env Q Checked (ELit n t) t
  | TyLitUnChecked : forall env Q n t,
      well_typed env Q Unchecked (ELit n t) t
  | TyVar : forall env Q m x t,
      Env.MapsTo x t env ->
      well_typed env Q m (EVar x) t

  | TyCall : forall env Q m m' b es x ts t, 
      (* get_dept_map tvl es = Some s -> *)
        fun_mode_eq m' m -> is_off_zero b ->
        well_typed env Q m x (TPtr m' (TFun b t ts)) ->
        @well_typed_args D F Q H env m es ts ->
        well_typed env Q m (ECall x es) t

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

  | TyLetStrlen : forall env Q m m' x y e l h t ta, 
        mode_leq m' m ->
      Env.MapsTo y (TPtr m' (TNTArray l h ta)) env ->
      well_typed (Env.add x TNat (Env.add y (TPtr m' (TNTArray l (Var x 0) ta)) env)) (Theta.add x GeZero Q) m e t ->
      ~ In x (get_tvars t) ->
      well_typed env Q m (ELet x (EStrlen y) e) t

  | TyLetNat : forall env Q m x e1 e2 t b,
      well_typed env Q m e1 TNat ->
      well_typed (Env.add x TNat env) Q m e2 t ->
      In x (get_tvars t) -> get_good_dept e1 = Some b ->
      well_typed env Q m (ELet x e1 e2) (subst_type [(x,b)] t)

  | TyLetPtrSame1 : forall env Q m m' x e1 t1 e2 t,
      well_typed env Q m e1 (TPtr m' t) ->
      well_typed (Env.add x t1 env) Q m e2 t ->
      ~ In x (get_tvars t) ->
        mode_leq m' m ->
      well_typed env Q m (ELet x e1 e2) t

  | TyLet : forall env Q m x e1 t1 e2 t,
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
  | TyPlusIndex : forall env Q m t e1 e2,
      ~ is_fun_type t ->
      well_typed env Q m e1 (TPtr m t) ->
      well_typed env Q m e2 (TNat) ->
      well_typed env Q m (EPlus e1 e2) (TPtr m t)
(*
  | TyFieldAddr : forall env U Q pm m e m' T fs i fi ti,
        mode_leq m' m ->
      well_typed env U Q m e (TPtr m' pm (TStruct T)) ->
      StructDef.MapsTo T fs D ->
      Fields.MapsTo fi ti fs ->
      List.nth_error (Fields.this fs) i = Some (fi, ti) ->
      well_typed env U Q m (EFieldAddr e fi) (TPtr m' pm ti)
*)
  | TyMallocChecked : forall env x m Q w t e2,
      mode_leq m Checked ->
      well_type_bound_in env w ->
      well_typed (Env.add x (TPtr Checked w) env) Q Checked e2 t ->
      well_typed env Q Checked (ELet x (EMalloc m w) e2) t

  | TyUnchecked : forall env Q m e,
      well_typed env Q Unchecked e TNat ->
      well_typed env Q m (EUnchecked e) TNat
  | TyCast1 : forall env Q m t e t',
      well_type_bound_in env t ->
      match_mode_ptr t m ->
      well_typed env Q m e t' ->
      well_typed env Q m (ECast t e) t
  | TyCast2 : forall env Q m m' t e t',
      well_type_bound_in env t ->
      well_typed env Q Checked e t' -> 
      subtype_stack D Q S t' (TPtr m' t) ->
      well_typed env Q Checked (ECast (TPtr m t) e) (TPtr m' t)

  | TyDynCast1 : forall env Q m e x y u v t t',
      well_type_bound_in env (TPtr m (TArray x y t)) ->
      well_typed env Q Checked e (TPtr m (TArray u v t')) ->
      type_eq S t t' ->
      mode_leq m Checked ->
      well_typed env Q Checked (EDynCast (TPtr m (TArray x y t)) e) (TPtr m (TArray x y t))
  | TyDynCast2 : forall env Q m e x y t t',
      ~ is_array_ptr (TPtr Checked t') ->
      type_eq S t t' ->
      well_type_bound_in env (TPtr m (TArray x y t)) ->
      well_typed env Q m e (TPtr Checked t') ->
      mode_leq m Checked ->
      well_typed env Q Checked (EDynCast (TPtr m (TArray x y t)) e) (TPtr m (TArray (Num 0) (Num 1) t))
  | TyDynCast3 : forall env Q m e x y u v t t',
      well_type_bound_in env (TPtr m (TNTArray x y t)) ->
      type_eq S t t' ->
      well_typed env Q Checked e (TPtr m (TNTArray u v t')) ->
      mode_leq m Checked ->
      well_typed env Q Checked (EDynCast (TPtr m (TNTArray x y t)) e) (TPtr m (TNTArray x y t))
  | TyDeref : forall env Q m e m' t l h t' t'',
      well_typed env Q m e t ->
      subtype D Q t (TPtr m' t'') -> 
      ((word_type t'' /\ t'' = t') 
       \/ (t'' = TArray l h t' /\ word_type t' /\ type_wf D  m' t')
       \/ (t'' = TNTArray l h t' /\ word_type t') /\ type_wf D  m' t') ->
      mode_leq m' m ->
      well_typed env Q m (EDeref e) t'
(*
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
*)
  | TyAssign1 : forall env Q m e1 e2 m' t t1,
      subtype_stack D Q S t1 t -> word_type t ->
      well_typed env Q m e1 (TPtr m' t) ->
      well_typed env Q m e2 t1 ->
      mode_leq m' m ->
      well_typed env Q m (EAssign e1 e2) t
  | TyAssignFun : forall env Q m e1 e2 m' b t ts,
      well_typed env Q m e1 (TPtr m' (TFun b t ts)) ->
      well_typed env Q m e2 TNat ->
      mode_leq m' m -> is_off_zero b ->
      well_typed env Q m (EAssign e1 e2) TNat

  | TyAssign2 : forall env Q m e1 e2 m' l h t t',
      word_type t -> type_wf D m' t -> subtype_stack D Q S t' t ->
      well_typed env Q m e1 (TPtr m' (TArray l h t)) ->
      well_typed env Q m e2 t' ->
      mode_leq m' m ->
      well_typed env Q m (EAssign e1 e2) t
  | TyAssign3 : forall env Q m e1 e2 m' l h t t',
      word_type t -> type_wf D m' t -> 
     subtype_stack D Q S t' t  ->
      well_typed env Q m e1 (TPtr m' (TNTArray l h t)) ->
      well_typed env Q m e2 t' ->
      mode_leq m' m ->
      well_typed env Q m (EAssign e1 e2) t

  | TyIndexAssign1 : forall env Q m e1 e2 e3 m' l h t t',
      word_type t' -> type_wf D m' t' -> 
      subtype_stack D Q S t' t ->
      well_typed env Q m e1 (TPtr m' (TArray l h t)) ->
      well_typed env Q m e2 (TNat) ->
      well_typed env Q m e3 t' ->
      mode_leq m' m ->
      well_typed env Q m (EAssign (EPlus e1 e2) e3) t
  | TyIndexAssign2 : forall env Q m e1 e2 e3 m' l h t t',
      word_type t' -> type_wf D m' t' -> 
      subtype_stack D Q S t' t ->
      well_typed env Q m e1 (TPtr m' (TNTArray l h t)) ->
      well_typed env Q m e2 (TNat) ->
      well_typed env Q m e3 t' ->
      mode_leq m' m ->
      well_typed env Q m (EAssign (EPlus e1 e2) e3) t

  | TyIfDef : forall env Q m m' x t t1 e1 e2 t2 t3 t4,
      Env.MapsTo x t env ->
      subtype D Q t (TPtr m' t1) ->
      (exists l h t', (word_type t1 /\ t1 = t')
         \/ (t1 = TArray l h t' /\ word_type t' /\ type_wf D m' t')
       \/ (t1 = TNTArray l h t' /\ word_type t' /\ type_wf D m' t')) ->
      well_typed env Q m e1 t2 -> well_typed env Q m e2 t3 ->
      join_type D Q S t2 t3 t4 -> 
      mode_leq m' m ->
      well_typed env Q m (EIfDef x e1 e2) t4

  | TyIfDefNT : forall env Q m m' x l t e1 e2 t2 t3 t4,
      Env.MapsTo x (TPtr m' (TNTArray l (Var x 0) t)) env ->
      well_typed (Env.add x (TPtr m' (TNTArray l (Var x 1) t)) env) Q m e1 t2 
        -> well_typed env Q m e2 t3 ->
      join_type D Q S t2 t3 t4 -> 
      (m' = Unchecked -> m = Unchecked) ->
      well_typed env Q m (EIfDef x e1 e2) t4


  | TyIf : forall env Q m e1 e2 e3 t2 t3 t4,
      well_typed env Q m e1 TNat ->
      well_typed env Q m e2 t2 ->
      well_typed env Q m e3 t3 ->
      join_type D Q S t2 t3 t4 -> 
      well_typed env Q m (EIf e1 e2 e3) t4. 


Definition fun_wf (D : structdef) (F:Z -> option funElem) (S:stack) (H:real_heap) :=
     forall env env' f tvl t e m, F f = Some (tvl,t,e,m) -> 
          gen_arg_env env tvl env' ->
          (forall x t', In (x,t') tvl -> word_type t' /\ type_wf D m t' /\ well_bound_vars_type tvl t') /\
          (forall n n' a b, n <> n' -> nth_error tvl n = Some a -> nth_error tvl n' = Some b -> fst a <> fst b) /\
          word_type t /\ type_wf D m t /\ well_bound_vars_type tvl t /\ expr_wf D e
          /\ @well_typed D (F) S H env' empty_theta m e t.


Definition sub_domain (env: env) (S:stack) := forall x, Env.In x env -> Stack.In x S.


Local Close Scope Z_scope.

Local Open Scope nat_scope.

Hint Constructors well_typed.

(*Hint Constructors ty_ssa.*)
