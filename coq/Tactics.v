(* Some helpful tactics. *)

(* Adds an equality in the context *)
Ltac ctx e1 e2 :=
  let H := fresh "HCtx" in
  assert (e1 = e2) as H by reflexivity.

(* Standard inversion/subst/clear abbrev. *)
Tactic Notation "inv" hyp(H) := inversion H; subst; clear H.
Tactic Notation "inv" hyp(H) "as" simple_intropattern(p) :=
  inversion H as p; subst; clear H.


(* Reasoning about options *)
Ltac solveOptBoth :=
  match goal with
  | [H : match ?P with | _ => _ end = Some _ |-
       match ?P' with | _ => _ end = Some _] =>
      let H' := fresh H in
      destruct P eqn:H'; inv H; auto;
      let H' := fresh H in
      destruct P' eqn:H'
  end; auto.

Ltac solveOptBothIn H :=
  match type of H with
  | match ?P with | _ => _ end = Some _ =>
      match goal with
      | [H : match P with | _ => _ end = Some _ |-
           match ?P' with | _ => _ end = Some _] =>
          let H' := fresh H in
          destruct P eqn:H'; inv H; auto;
          let H' := fresh H in
          destruct P' eqn:H'
      end; auto
  end.

Ltac solveOptIn H :=
  match type of H with
  | match ?X with |_ => _ end = Some _ =>
      match goal with
      | [H : match X with | _ => _ end = Some _ |- _] =>
          let H' := fresh H in
          destruct X eqn:H'; inv H
      end; auto
  end.

Ltac solveOptTop :=
  match goal with
  | [H : match ?P with | _ => _ end = Some _ |- _] =>
      let H' := fresh H in
      destruct P eqn:H'; inv H
  end; auto.

Ltac solveOptGoal :=
  match goal with
  | |- match ?P' with | _ => _ end = Some _ =>
      let H' := fresh "Hgoal" in
      destruct P' eqn:H'
  end; auto.

Ltac invOpt :=
  match goal with
  | [H : Some _ = Some _ |- _ ] => inv H
  | [H : Some _ = None |- _ ] => inv H
  | [H : None = Some _ |- _ ] => inv H
  | [H : None = None |- _ ] => clear H
  end; auto.


Tactic Notation "solveopt" := solveOptGoal.
Tactic Notation "solveopt" "in" hyp(H) := solveOptIn H.
Tactic Notation "solveopt" "in" "*" := solveOptTop.
Tactic Notation "solveopt2" := solveOptBoth.
Tactic Notation "solveopt2" "with" hyp(H) := solveOptBothIn H.


Ltac focusCut H tac :=
  match type of H with
  | (?P -> _) =>
      match goal with
      | [H : P -> _ |- _] =>
          let Htmp := fresh "Hcut" in
          assert P as Htmp; [tac | specialize (H Htmp)]
      end
  end.

(* Modus Ponens but on the subgoal *)
Tactic Notation "mopo" hyp(H) := focusCut H idtac.
Tactic Notation "mopo" hyp(H) "by" tactic(tac) := focusCut H tac.

