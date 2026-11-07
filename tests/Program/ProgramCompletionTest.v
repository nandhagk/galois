(** * Administrative completion clients

    The target splits a visible source transition from its silent completion.
    For example, target state one silently completes at stable state two.
    Builds on: ProgramCompletion. *)

From Stdlib Require Import List Arith Lia.
From Galois.Program Require Import ProgramSemantics ProgramCompletion.
Import List.ListNotations.

Definition source : semantics bool unit :=
  Semantics (fun s => s = false) (fun s l t => s = false /\ l = [tt] /\ t = true).

Definition target : semantics nat unit :=
  Semantics (fun t => t = 0)
    (fun s l t => (s = 0 /\ l = [tt] /\ t = 1) \/ (s = 1 /\ l = [] /\ t = 2)).

Definition source_ends : endings bool :=
  Endings (fun s => s = true) (fun _ => False) (fun _ => False).

Definition target_ends : endings nat :=
  Endings (fun t => t = 2) (fun _ => False) (fun _ => False).

Definition stable (t : nat) := t <> 1.
Definition rank (t : nat) := if Nat.eqb t 1 then 1 else 0.
Definition related (s : bool) (t : nat) := t = if s then 2 else 0.

Example completion_laws :
  Completion.laws source source_ends target target_ends stable rank related.
Proof.
  constructor.
  - intros [] t ->; discriminate.
  - intros [] t k -> Htag; destruct k; cbn in *; intuition congruence.
  - intros t l t' Hunstable [[-> [-> ->]]|[-> [-> ->]]].
    + exfalso; apply Hunstable; discriminate.
    + split; [reflexivity|vm_compute; lia].
  - intros t u v Hunstable [[-> [Hbad _]]|[-> [_ ->]]]
      [[Heq [Hbad' _]]|[Heq [_ ->]]]; congruence.
  - intros t k Hunstable Htag.
    assert (Ht : t = 1).
    { destruct (Nat.eq_dec t 1) as [Heq|Hne]; [exact Heq|].
      exfalso; apply Hunstable; exact Hne. }
    subst t; destruct k; cbn in *; intuition congruence.
  - intros s t l s' Hrel Hstep.
    change (t = if s then 2 else 0) in Hrel.
    change (s = false /\ l = [tt] /\ s' = true) in Hstep.
    destruct Hstep as [Hs [Hl Hs']]; subst s l s'; cbn in Hrel; subst t.
    exists 1, 1, 2; split; [left; repeat split; reflexivity|].
    split.
    + econstructor; [unfold stable; tauto|right; repeat split; reflexivity|constructor].
    + split; [unfold stable; discriminate|reflexivity].
  - intros s t l u Hrel Hstep.
    change (t = if s then 2 else 0) in Hrel; destruct s; cbn in Hrel; subst t.
    + destruct Hstep as [[Hbad _]|[Hbad _]]; discriminate.
    + destruct Hstep as [[_ [-> ->]]|[Hbad _]]; [|discriminate].
      exists true, 1, 2; split; [repeat split; reflexivity|].
      split.
      * econstructor; [unfold stable; tauto|right; repeat split; reflexivity|constructor].
      * split; [unfold stable; discriminate|reflexivity].
Qed.

Example completed_behaviour :
  same_behaviour source source_ends false target target_ends 0.
Proof.
  eapply Completion.behaviour; [exact completion_laws|reflexivity].
Qed.

Example completes_one_step : step target 1 [] 2.
Proof.
  vm_compute; right; repeat split; reflexivity.
Qed.

Example rejects_visible_administration : ~ step target 1 [tt] 2.
Proof.
  vm_compute; intros [[Hbad _]|[_ [Hbad _]]]; discriminate.
Qed.

Example stable_boundary : stable 2.
Proof.
  vm_compute; discriminate.
Qed.

Definition branching : semantics nat unit :=
  Semantics (fun t => t = 0)
    (fun t l u => t = 1 /\ l = [] /\ (u = 0 \/ u = 2)).

Example rejects_nondeterministic_administration :
  ~ (forall t u v, ~ stable t ->
    step branching t [] u -> step branching t [] v -> u = v).
Proof.
  intro Hdet.
  assert (Hunstable : ~ stable 1) by (unfold stable; tauto).
  assert (Hleft : step branching 1 [] 0) by (vm_compute; tauto).
  assert (Hright : step branching 1 [] 2) by (vm_compute; tauto).
  discriminate (Hdet 1 0 2 Hunstable Hleft Hright).
Qed.
