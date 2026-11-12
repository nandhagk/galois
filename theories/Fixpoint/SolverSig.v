(** * Untrusted solver results

    A solver returns a candidate, exhausts fuel, or rejects a policy.
    For example, certification checks a [Solved] candidate before exposing soundness.
    Builds on: Fixpoint.PolicySig, Fixpoint.SystemSig and Base.MapSig. *)

From Stdlib Require Import NArith.
From Galois.Base Require Import MapSig Trie.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import Query SystemSig PolicySig.

Inductive reason :=
  | Bad_policy
  | Check_failed.

Inductive outcome (M : Type) :=
  | Solved (m : M)
  | OutOfFuel (m : M)
  | Rejected (why : reason).

Arguments Solved {M} m.
Arguments OutOfFuel {M} m.
Arguments Rejected {M} why.

Module Type SOLVER_OPS (L : WLATTICE_OPS) (S : SYSTEM_OPS L).
  Parameter run : S.prog -> policy L.wparam -> N -> outcome (kmap S.key L.t).
End SOLVER_OPS.

Module Type SOLVER_TIME (L : WLATTICE_T) (S : SYSTEM_T L)
    (Import V : SOLVER_OPS L S).
  (* spec: fits work fuel_for *)
  Parameter fits : S.prog -> policy L.wparam -> Prop.
  Parameter work : S.prog -> policy L.wparam -> N.
  Parameter fuel_for : S.prog -> policy L.wparam -> N.
  Parameter T_run : S.prog -> policy L.wparam -> N -> N.
  Parameter c_solve : N.
  (** Running pays for bounded work and the bit length of fuel. *)
  Parameter T_run_le : forall p pol fuel, fits p pol ->
    (T_run p pol fuel <= c_solve * (work p pol + N.of_nat (N.size_nat fuel) + 1))%N.
  (** Sufficient fuel produces a candidate on fitting inputs. *)
  Parameter run_enough : forall p pol fuel, fits p pol -> (fuel_for p pol <= fuel)%N ->
    exists m, run p pol fuel = Solved m.
End SOLVER_TIME.

Module Type SOLVER_T (L : WLATTICE_T) (S : SYSTEM_T L) :=
  SOLVER_OPS L S <+ SOLVER_TIME L S.

Module Type SOLVER_LEAST (L : WLATTICE) (S : SYSTEM L)
    (Import V : SOLVER_OPS L S).
  (** A policy without heads performs no widening. *)
  Definition widening_free (pol : policy L.wparam) : Prop :=
    forall c, trie_get c (heads pol) = None.
  (** A solved widening-free candidate lies below every post-solution. *)
  Parameter run_least : forall p pol fuel m s', S.wf p -> S.monotone p ->
    widening_free pol -> run p pol fuel = Solved m -> S.post_solution p s' ->
    forall x, L.leb (look_or S.key_code L.bot m x) (s' x) = true.
End SOLVER_LEAST.
