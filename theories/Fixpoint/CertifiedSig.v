(** * Certified solver candidates

    Certification checks solved candidates before applying checked narrowing.
    For example, a failed initial check returns [Rejected Check_failed].
    Builds on: Fixpoint.SolverSig, Fixpoint.CheckSig and Fixpoint.NarrowSig. *)

From Stdlib Require Import NArith.
From Galois.Base Require Import MapSig.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import SystemSig PolicySig SolverSig CheckSig NarrowSig.

Module Type CERTIFIED_OPS (L : WLATTICE_OPS) (S : SYSTEM_OPS L)
    (V : SOLVER_OPS L S) (C : CHECK_OPS L S) (R : NARROW_OPS L S C).
  Parameter analyze : S.prog -> policy L.wparam -> N -> outcome (kmap S.key L.t).
End CERTIFIED_OPS.

Module Type CERTIFIED_LAWS (L : WLATTICE) (S : SYSTEM L)
    (V : SOLVER_OPS L S) (C : CHECK L S) (R : NARROW L S C)
    (Import A : CERTIFIED_OPS L S V C R).
  (** Certification checks solved candidates and keeps the other solver outcomes. *)
  Parameter analyze_spec : forall p pol fuel,
    analyze p pol fuel =
      match V.run p pol fuel with
      | Solved m =>
        if C.check p m then Solved (R.refine p (passes pol) m)
        else Rejected Check_failed
      | OutOfFuel m => OutOfFuel m
      | Rejected why => Rejected why
      end.
  (** Every certified solved candidate is a post-solution. *)
  Parameter analyze_sound : forall p pol fuel m,
    analyze p pol fuel = Solved m -> S.post_solution p (C.look m).
End CERTIFIED_LAWS.

Module Type CERTIFIED (L : WLATTICE) (S : SYSTEM L)
    (V : SOLVER_OPS L S) (C : CHECK L S) (R : NARROW L S C) :=
  CERTIFIED_OPS L S V C R <+ CERTIFIED_LAWS L S V C R.

Module Type CERTIFIED_TIME (L : WLATTICE_T) (S : SYSTEM_T L)
    (V : SOLVER_T L S) (C : CHECK_T L S) (R : NARROW_T L S C)
    (Import A : CERTIFIED L S V C R).
  Parameter T_analyze : S.prog -> policy L.wparam -> N -> N.
  (** Only solved candidates incur checking and narrowing row evaluations. *)
  Definition candidate_work p pol fuel : N :=
    match V.run p pol fuel with
    | Solved m => (C.T_check p m + R.T_eval_all p m)%N
    | OutOfFuel _ => 0%N
    | Rejected _ => 0%N
    end.
  (** Certification pays for solving and the requested checks and row evaluations. *)
  Parameter T_analyze_le : forall p pol fuel,
    (T_analyze p pol fuel <= V.T_run p pol fuel +
      N.of_nat (passes pol + 1) * (candidate_work p pol fuel + 1))%N.
End CERTIFIED_TIME.

Module Type CERTIFIED_T (L : WLATTICE_T) (S : SYSTEM_T L)
    (V : SOLVER_T L S) (C : CHECK_T L S) (R : NARROW_T L S C) :=
  CERTIFIED L S V C R <+ CERTIFIED_TIME L S V C R.
