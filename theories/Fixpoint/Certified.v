(** * Certified solver results

    Certification checks candidates and applies checked refinement.
    For example, a failed check rejects the candidate.

    Main results
    - [analyze_spec] Certification checks solved candidates and keeps the other solver outcomes.
    - [analyze_sound] Every certified solved candidate is a post-solution.
    - [analyze_complexity] Certification is linear in the solver clock and the work of a solved
      candidate.

    Builds on: Fixpoint.CertifiedSig. *)

From Stdlib Require Import NArith Lia.
From Argent Require Import Time Tactics Std Complexity.
From Galois.Base Require Import MapSig.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import SystemSig PolicySig SolverSig CheckSig NarrowSig CertifiedSig.
Import ComplexityNotations.

Module CertifiedCode (L : WLATTICE_OPS) (S : SYSTEM_OPS L)
    (V : SOLVER_OPS L S) (C : CHECK_OPS L S) (R : NARROW_OPS L S C)
    <: CERTIFIED_OPS L S V C R.
  Definition analyze p pol fuel :=
    match V.run p pol fuel with
    | Solved m =>
      if C.check p m then Solved (R.refine p (passes pol) m)
      else Rejected Check_failed
    | OutOfFuel m => OutOfFuel m
    | Rejected why => Rejected why
    end.
End CertifiedCode.

Module Certified (L : WLATTICE) (S : SYSTEM L) (V : SOLVER_OPS L S)
    (C : CHECK L S) (R : NARROW L S C) <: CERTIFIED L S V C R.
  Include CertifiedCode L S V C R.
  (** The public equation retains every solver outcome and checks solved candidates. *)
  Lemma analyze_spec : forall p pol fuel,
    analyze p pol fuel =
      match V.run p pol fuel with
      | Solved m => if C.check p m then Solved (R.refine p (passes pol) m)
                    else Rejected Check_failed
      | OutOfFuel m => OutOfFuel m
      | Rejected why => Rejected why
      end.
  Proof.
    reflexivity.
  Qed.
  Lemma analyze_sound : forall p pol fuel m,
    analyze p pol fuel = Solved m -> S.post_solution p (C.look m).
  Proof.
    intros p pol fuel m Hrun. unfold analyze in Hrun.
    destruct (V.run p pol fuel) as [candidate | candidate | why]; try discriminate.
    destruct (C.check p candidate) eqn:Hcheck; try discriminate.
    injection Hrun as <-. apply R.refine_post. apply C.check_sound. exact Hcheck.
  Qed.
End Certified.

Module CertifiedT (L : WLATTICE_T) (S : SYSTEM_T L) (V : SOLVER_T L S)
    (C : CHECK_T L S) (B : BUDGET L S) (R : NARROW_T L S C B) <: CERTIFIED_T L S V C B R.
  Include Certified L S V C R.
  Definition candidate_work p pol fuel : N :=
    match V.run p pol fuel with
    | Solved m => (C.T_check p m + R.T_refine p (passes pol) m)%N
    | OutOfFuel _ => 0%N
    | Rejected _ => 0%N
    end.
  TimeFun analyze.
  Definition c_cert : N := 2%N.

  (** Solving is always charged; checking and refinement are charged for solved candidates. *)
  Lemma T_analyze_le : forall p pol fuel,
    (T_analyze p pol fuel <= c_cert *
      (V.T_run p pol fuel + candidate_work p pol fuel + 1))%N.
  Proof.
    intros p pol fuel.
    unfold c_cert, candidate_work.
    time_step.
  Qed.

  (** Certification is linear in the solver clock and the work of a solved candidate. *)
  Lemma analyze_complexity :
    T_analyze p pol fuel ∈ 𝑂((V.T_run p pol fuel + candidate_work p pol fuel)%N)
    for (p, pol, fuel).
  Proof.
    apply bigO_intro with (c := c_cert).
    intros [[p pol] fuel] _; cbn [fst snd].
    pose proof (T_analyze_le p pol fuel) as Hbound.
    rewrite N.mul_add_distr_l, N.mul_1_r in Hbound.
    exact Hbound.
  Qed.
End CertifiedT.
