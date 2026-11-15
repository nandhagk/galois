(** * Relational leastness needs sorted comparison views

    A comparison view with an identifier output can satisfy a relational put, because
    [present] does not constrain the output of a put without a result. For example, the rule
    with no query atoms that inserts the nullary relation [1] is closed in a view containing
    only its identifier-output row, and that view is not sorted for the program.
    Builds on: Syntax, Model and Sorts. *)

From Stdlib Require Import List PArith.
From Galois.Egglog Require Import Syntax Model Sorts.

Import List.ListNotations.

Definition leastness_program {V : Type} : program V :=
  Program V [Decl 1%positive [] ORel] [Rule V [] [Put 1%positive [] None]].

Definition leastness_comparison {V : Type} : view (V := V) :=
  {| row := fun f k o => f = 1%positive /\ k = [] /\ o = Some (Id 1%positive);
     same := eq;
     kind := lookup_kind [Decl 1%positive [] ORel] |}.

(** The comparison has the declared relation kind despite its wrongly sorted row. *)
Example leastness_comparison_kind {V : Type} :
  kind (@leastness_comparison V) 1%positive = Some ORel.
Proof.
  reflexivity.
Qed.

(** Relational closure alone does not require the output of the witnessing row to be absent. *)
Example leastness_comparison_closed {V : Type}
    (prim : positive -> list V -> option V) (merge : positive -> V -> V -> V) :
  closed prim merge leastness_program leastness_comparison.
Proof.
  intros r s Hr Hmatch.
  destruct Hr as [<- | []].
  cbn [actions present].
  exists [], (Some (Id 1%positive)).
  split; [constructor |].
  repeat split.
Qed.

(** The comparison omits the relation row that leastness claims it must contain. *)
Example leastness_comparison_missing {V : Type} :
  ~ row (@leastness_comparison V) 1%positive [] None.
Proof.
  intros [_ [_ Hout]].
  discriminate.
Qed.

(** The empty-query rule derives the missing relation row from any seed view. *)
Example leastness_derivation {V : Type} (prim : positive -> list V -> option V)
    (seed : view (V := V)) :
  derives prim leastness_program seed 1%positive [].
Proof.
  eapply derive_rule with (r := Rule V [] [Put 1%positive [] None])
    (s := fun _ => None).
  - now left.
  - constructor.
  - constructor. constructor.
Qed.

(** The comparison fails the sorted-view premise of leastness, because its relation row has
    an identifier output. *)
Example leastness_comparison_unsorted {V : Type} :
  ~ view_sorted (program_sorts (@leastness_program V)) (@leastness_comparison V).
Proof.
  intros Hsorted.
  assert (Hrow : row (@leastness_comparison V) 1%positive [] (Some (Id 1%positive)))
    by (repeat split).
  destruct (Hsorted _ _ _ Hrow) as [kind_out [_ [Hkind Hout]]].
  cbn in Hkind.
  injection Hkind as <-.
  cbn in Hout.
  discriminate Hout.
Qed.
