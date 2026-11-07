(** * Dominance fixtures with multiple entries

    The diamond's initial node immediately dominates its join.
    For example, making the right arm an entry removes that dominance fact.
    Builds on: GraphDomSpec and GraphModelTest. *)

From Stdlib Require Import List PArith.
From Galois.Graph Require Import GraphModel GraphDomSpec.
From Galois.Tests.Graph Require Import GraphModelTest.
Import List.ListNotations.
Open Scope positive_scope.

Example diamond_entry_dominates : dominates diamond 1 4.
Proof.
  intros s es Hin Hpath. vm_compute in Hin. destruct Hin as [<-|Hfalse].
  - now left.
  - contradiction.
Qed.

Example diamond_entry_strict : strictly_dominates diamond 1 4.
Proof.
  split; [exact diamond_entry_dominates|discriminate].
Qed.

Example diamond_entry_immediate : immediately_dominates diamond 1 4.
Proof.
  split; [exact diamond_entry_strict|].
  intros x [Hx Hne].
  assert (Hleft : path diamond 1 [(1, 2); (2, 4)] 4).
  { apply (@path_cons positive edge diamond (1, 2)); [vm_compute; auto|].
    apply (@path_cons positive edge diamond (2, 4)); [vm_compute; auto|constructor]. }
  assert (Hright : path diamond 1 [(1, 3); (3, 4)] 4).
  { apply (@path_cons positive edge diamond (1, 3)); [vm_compute; auto|].
    apply (@path_cons positive edge diamond (3, 4)); [vm_compute; auto|constructor]. }
  pose proof (Hx 1 [(1, 2); (2, 4)] (or_introl eq_refl) Hleft) as Hl.
  pose proof (Hx 1 [(1, 3); (3, 4)] (or_introl eq_refl) Hright) as Hr.
  cbn in Hl, Hr.
  assert (Hcases_left : x = 1 \/ x = 2 \/ x = 4).
  { destruct Hl as [Heq|[e [[Heq|[Heq|Hfalse]] Htarget]]];
      try contradiction; subst; cbn in *; auto. }
  assert (Hcases_right : x = 1 \/ x = 3 \/ x = 4).
  { destruct Hr as [Heq|[e [[Heq|[Heq|Hfalse]] Htarget]]];
      try contradiction; subst; cbn in *; auto. }
  assert (x = 1) by intuition congruence. subst x. apply dominates_refl.
Qed.

Example second_entry_breaks_dominance : ~ dominates two_entry 1 4.
Proof.
  intro Hdom.
  assert (Hpath : path two_entry 3 [(3, 4)] 4).
  { apply (@path_cons positive edge two_entry (3, 4)); [vm_compute; auto|constructor]. }
  destruct (Hdom 3 [(3, 4)] (or_intror (or_introl eq_refl)) Hpath)
    as [Hfalse|[e [Hin Htarget]]].
  - discriminate.
  - destruct Hin as [<-|Hfalse]; [vm_compute in Htarget; discriminate|contradiction].
Qed.

Example two_entry_reflexive : dominates two_entry 3 3.
Proof.
  apply dominates_refl.
Qed.

Example two_entry_arm_dominates : dominates two_entry 1 2.
Proof.
  apply dominates_unique_predecessor.
  - vm_compute. intuition discriminate.
  - intros [s t] Hin Htarget.
    apply filter_In in Hin. destruct Hin as [Hin _].
    vm_compute in Hin, Htarget |- *. intuition congruence.
Qed.

Example two_entry_arm_strict : strictly_dominates two_entry 1 2.
Proof.
  split; [exact two_entry_arm_dominates|discriminate].
Qed.

Example two_entry_arm_immediate : immediately_dominates two_entry 1 2.
Proof.
  split; [exact two_entry_arm_strict|]. intros x [Hx Hne].
  assert (Hpath : path two_entry 1 [(1, 2)] 2).
  { apply (@path_cons positive edge two_entry (1, 2)); [vm_compute; auto|constructor]. }
  destruct (Hx 1 [(1, 2)] (or_introl eq_refl) Hpath) as [Heq|[e [Hin Htarget]]].
  - subst x. apply dominates_refl.
  - destruct Hin as [<-|Hfalse]; [cbn in Htarget; subst x; contradiction|contradiction].
Qed.

Example two_entry_no_strict_entry_dom : ~ strictly_dominates two_entry 1 4.
Proof.
  intros [Hdom _]. exact (second_entry_breaks_dominance Hdom).
Qed.

Example two_entry_no_immediate_entry_dom : ~ immediately_dominates two_entry 1 4.
Proof.
  intros [[Hdom _] _]. exact (second_entry_breaks_dominance Hdom).
Qed.
