(** * Solver outcomes and laws

    Untrusted computational solvers return explicit candidates, exhaustion or rejection.
    For example, a bad candidate can be rejected by the certified wrapper.
    Builds on: FixpointAnalysis and FixpointLeast. *)

From Stdlib Require Import PArith.
From Galois.Cost Require Import CostMonad.
From Galois.Lattice Require Import LatticeCore.
From Galois.Fixpoint Require Import FixpointSystem FixpointLeast FixpointAnalysis.

Module Reason.

(** Rejections identify the failed preparation or certificate boundary. *)
Inductive t :=
  | Bad_index
  | Bad_plan
  | Bad_wto
  | Bad_stratification
  | Check_failed
  | Bad_certificate.

End Reason.
Import Reason.

Module Outcome.

(** Exhausted assignments are explicitly unchecked. *)
Inductive t (X A R : Type) :=
  | Solved (result : R)
  | OutOfFuel (have : assignment X A)
  | Rejected (why : Reason.t).

Arguments Solved {X A R}.
Arguments OutOfFuel {X A R}.
Arguments Rejected {X A R}.

End Outcome.
Import Outcome.

Module Solver.

(** Computational solvers accept analyses without requiring law or termination proofs. *)
Record t (X C A : Type) := Make {
  run_c : Analysis.t X C A -> positive -> Cost.t (Outcome.t X A (assignment X A))
}.

Arguments Make {X C A}.
Arguments run_c {X C A}.

Definition run {X C A} (sv : t X C A) a fuel := Cost.value (run_c sv a fuel).

(** Solver laws separate candidate soundness from joining reachability. *)
Record laws {X C A} (sv : t X C A) : Prop := {
  solved_sound : forall a fuel m, Analysis.laws a ->
    run sv a fuel = Outcome.Solved m ->
    post_solution (Analysis.lat a) (Analysis.system a)
      (lookup (Analysis.key_enc a) (Analysis.lat a) m);
  solved_reached : forall a fuel m, Analysis.laws a -> lub_laws (Analysis.lat a) ->
    Analysis.joining a -> run sv a fuel = Outcome.Solved m ->
    reached (Analysis.key_enc a) (Analysis.lat a) (Analysis.system a)
      (lookup (Analysis.key_enc a) (Analysis.lat a) m)
}.

Arguments solved_sound {X C A sv}.
Arguments solved_reached {X C A sv}.

End Solver.
Import Solver.
