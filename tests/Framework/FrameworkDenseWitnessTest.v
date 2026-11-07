(** * Witness and cover clients

    Boolean facts track whether the unique taken edge occurs in a counter history.
    For example, a busy fact at entry witnesses the edge on every final continuation.
    Builds on: FrameworkDenseWitness and FrameworkDenseForwardTest. *)

From Stdlib Require Import List Bool.
From Galois.Lattice Require Import LatticeCore LatticeSimple.
From Galois.Fixpoint Require Import FixpointSystem.
From Galois.Program Require Import ProgramSemantics ProgramSteps ProgramCfg ProgramLink ProgramRuns.
From Galois.Framework Require Import FrameworkDense FrameworkDenseForward FrameworkDenseAgreement
  FrameworkDenseWitness.
From Galois.Tests.Framework Require Import FrameworkDenseForwardTest.
Import List.ListNotations.

Module CounterWitness.

Definition witness (_ : DenseCounter.state) (es : list unit)
    (_ : DenseCounter.state) (_ : unit) := In tt es.
Definition must_holds (a : bool) (_ : unit) := a = false.
Definition may_holds (a : bool) (_ : unit) := a = true.

Definition must_problem : Dense.t bool unit bool :=
  Dense.of_pure DenseCounter.cfg Forward bool_lattice
    (fun n => if n then None else Some true) (fun _ _ => false).
Definition must_sigma (n : bool) := negb n.

Lemma must_order : DenseWitness.holds_antitone bool_lattice must_holds.
Proof.
  intros [] [] [] Hab Hb; vm_compute in Hab, Hb; congruence.
Qed.

Lemma may_order : DenseWitness.holds_monotone bool_lattice may_holds.
Proof.
  intros [] [] [] Hab Ha; vm_compute in Hab, Ha; congruence.
Qed.

Example wrong_membership_law_negative :
  ~ DenseWitness.holds_antitone bool_lattice may_holds.
Proof.
  intro Hlaw.
  pose proof (Hlaw false true tt eq_refl eq_refl) as Hbad; discriminate Hbad.
Qed.

Lemma must_post :
  post_solution (Dense.lat must_problem) (Dense.system must_problem) must_sigma.
Proof.
  apply (proj2 (Dense.post_solution_iff must_problem must_sigma bool_laws)); split.
  - intros [] a Hin Ha; vm_compute in Hin, Ha; try discriminate.
    inversion Ha; reflexivity.
  - intros [] Hin; reflexivity.
Qed.

Example must_witness_positive : witness DenseCounter.C0 [tt] DenseCounter.C2 tt.
Proof.
  eapply (DenseWitness.forward_witness_sound DenseCounter.m must_problem DenseCounter.lk
    must_holds witness must_sigma).
  - reflexivity.
  - exact bool_laws.
  - exact DenseCounter.link_ok.
  - exact must_order.
  - intros [] Hin.
    + vm_compute in Hin; intuition discriminate.
    + exists true; reflexivity.
  - intros s a u -> Ha Hu.
    change (Some true = Some a) in Ha; inversion Ha; subst a; discriminate Hu.
  - intros [] s0 es a s l s' Hr Hstep Hs0 Hprefix Htaken Hfact [] Hu.
    apply in_or_app; right; vm_compute; tauto.
  - intros s0 es a s l s' Hr Hstep Hs0 Hprefix Hstay Hfact u Hu.
    exact (Hfact u Hu).
  - exact must_post.
  - reflexivity.
  - exact DenseCounter.history.
  - reflexivity.
Qed.

Example may_cover_positive :
  may_holds (DenseCounter.sigma (Link.point DenseCounter.lk DenseCounter.C2)) tt.
Proof.
  eapply (DenseWitness.forward_cover_sound DenseCounter.m DenseCounter.D DenseCounter.lk
    may_holds witness DenseCounter.sigma).
  - reflexivity.
  - exact bool_laws.
  - exact DenseCounter.link_ok.
  - exact may_order.
  - exact DenseCounter.covers.
  - intros s a u Hs Ha Hw; contradiction Hw.
  - intros e s0 es a s l s' Hr Hstep Hs0 Hprefix Htaken Hfact u Hw; reflexivity.
  - intros s0 es a s l s' Hr Hstep Hs0 Hprefix Hstay Hfact u Hw; exact (Hfact u Hw).
  - exact DenseCounter.post.
  - reflexivity.
  - exact DenseCounter.history.
  - vm_compute; tauto.
Qed.

Definition busy_problem : Dense.t bool unit bool :=
  Dense.of_pure DenseCounter.cfg Backward bool_lattice
    (fun n => if n then Some true else None) (fun _ _ => false).
Definition busy_sigma (n : bool) := n.

Lemma busy_post : post_solution (Dense.lat busy_problem) (Dense.system busy_problem) busy_sigma.
Proof.
  apply (proj2 (Dense.post_solution_iff busy_problem busy_sigma bool_laws)); split.
  - intros [] a Hin Ha; vm_compute in Ha; try discriminate; inversion Ha; reflexivity.
  - intros [] He; reflexivity.
Qed.

Example backward_witness_positive : witness DenseCounter.C0 [tt] DenseCounter.C2 tt.
Proof.
  eapply (DenseWitness.backward_witness_sound DenseCounter.m busy_problem DenseCounter.lk
    must_holds (fun s => s = DenseCounter.C2) witness busy_sigma).
  - reflexivity.
  - exact bool_laws.
  - exact DenseCounter.link_ok.
  - exact must_order.
  - intros t u Hr -> Hu; discriminate Hu.
  - intros [] es t a s l s' Hr Hstep Hrun HQ Htaken Hfact [] Hu.
    vm_compute; tauto.
  - intros es t a s l s' Hr Hstep Hrun HQ Hstay Hfact u Hu; exact (Hfact u Hu).
  - exact busy_post.
  - exists DenseCounter.C0, []; split; [reflexivity|constructor].
  - exact DenseCounter.history.
  - reflexivity.
  - reflexivity.
Qed.

Definition unseeded : Dense.t bool unit bool :=
  Dense.of_pure DenseCounter.cfg Forward bool_lattice (fun _ => None) (fun _ _ => false).

Example absent_entry_negative :
  post_solution (Dense.lat unseeded) (Dense.system unseeded) (fun _ => false) /\
  must_holds false tt /\ ~ witness DenseCounter.C0 [] DenseCounter.C0 tt /\
  ~ DenseForward.boundary_covers unseeded.
Proof.
  split.
  - apply (proj2 (Dense.post_solution_iff unseeded _ bool_laws)); split.
    + intros n a Hn Ha; discriminate Ha.
    + intros e He; reflexivity.
  - split; [reflexivity|]; split; [vm_compute; tauto|].
    intro Hcovers.
    destruct (Hcovers false (or_introl eq_refl)) as [a Ha]; discriminate Ha.
Qed.

Definition bad_terminal : Dense.t bool unit bool :=
  Dense.of_pure DenseCounter.cfg Backward bool_lattice (fun _ => None) (fun _ _ => false).

Example terminal_seed_negative :
  post_solution (Dense.lat bad_terminal) (Dense.system bad_terminal) (fun _ => false) /\
  must_holds false tt /\ ~ witness DenseCounter.C2 [] DenseCounter.C2 tt.
Proof.
  split.
  - apply (proj2 (Dense.post_solution_iff bad_terminal _ bool_laws)); split.
    + intros n a Hn Ha; discriminate Ha.
    + intros e He; reflexivity.
  - vm_compute; tauto.
Qed.

Example empty_history_boundary :
  ~ must_holds (must_sigma false) tt /\ ~ witness DenseCounter.C0 [] DenseCounter.C0 tt.
Proof.
  vm_compute; intuition discriminate.
Qed.

Example terminal_continuation_boundary :
  ~ must_holds (busy_sigma true) tt /\ ~ witness DenseCounter.C2 [] DenseCounter.C2 tt.
Proof.
  vm_compute; intuition discriminate.
Qed.

End CounterWitness.
