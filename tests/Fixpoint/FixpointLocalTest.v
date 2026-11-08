(** * Actual demand-driven joining clients

    Local runs compute cyclic closures, smaller unrelated regions and checked partial outcomes.
    For example, deleting a required read from an external candidate makes the partial gate reject.
    Builds on: FixpointLocal, FixpointLocalProof and FixpointLocalLeast. *)

From Stdlib Require Import List Bool Arith NArith PArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Lattice Require Import LatticeCore LatticeSimple.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointAnalysis
  FixpointSolver FixpointLocal FixpointLocalProof FixpointLocalLeast.
Import List.ListNotations.

Module LocalTest.

Definition system : System.t nat nat bool :=
  System.Make [3; 0; 1; 2; 0]
    (fun c => Cost.ret (if Nat.eqb c 3 then 20 else c))
    (fun c => Cost.ret (match c with
      | O => Query.Ask 1 (fun b => Cost.ret (Query.Ret b))
      | S O => Query.Ask 0 (fun b => Cost.ret (Query.Ret b))
      | S (S O) => Query.Side 0 true (Query.Side 0 false (Query.Ret false))
      | _ => Query.Ret true
      end)).

Definition summaries : System.static system :=
  System.Static
    (fun c => Cost.ret (match c with O => [1] | S O => [0] | _ => [] end))
    (fun c => Cost.ret (match c with S (S O) => [0; 0] | _ => [] end)).

Definition analysis : Analysis.t nat nat bool :=
  Analysis.Make nat_encoding nat_encoding bool_lattice system summaries (Policy.flat nat).

Definition laws : Analysis.laws analysis.
Proof.
  constructor.
  - exact nat_encoding_laws.
  - exact nat_encoding_laws.
  - exact bool_laws.
  - constructor; intros c s x Hin; destruct c as [|[|[|c]]];
      vm_compute in *; exact Hin.
Qed.

Definition termination : Terminates.t analysis.
Proof.
  refine (@Terminates.Finite nat nat bool analysis (fun _ => True) bool_height _ _ _);
    intros; exact I.
Defined.

Definition ix := index_system nat_encoding system summaries.
Definition cyclic : Local.result nat bool :=
  Local.Result (FinSet.of_list nat_encoding [0; 1; 2])
    (Map.of_list nat_encoding [(0, true); (1, true)]).

Definition observation (outcome : Outcome.t nat bool (Local.result nat bool)) :=
  match outcome with
  | Outcome.Solved r =>
    (FinSet.elements (Local.explored r),
      map (lookup nat_encoding bool_lattice (Local.values r)) [0; 1; 2; 20; 99])
  | _ => ([], [])
  end.

Example cyclic_run : Local.run analysis termination [0] 64%positive = Outcome.Solved cyclic.
Proof.
  vm_compute; reflexivity.
Qed.

Example checked_cyclic :
  observation (Local.checked analysis termination [0] 64%positive) =
    ([1; 0; 2], [true; true; false; false; false]).
Proof.
  vm_compute; reflexivity.
Qed.

Example unrelated_region :
  observation (Local.checked analysis termination [20] 64%positive) =
    ([20], [false; false; false; true; false]).
Proof.
  vm_compute; reflexivity.
Qed.

Example unknown_root :
  observation (Local.checked analysis termination [99] 4%positive) =
    ([99], [false; false; false; false; false]).
Proof.
  vm_compute; reflexivity.
Qed.

Example empty_roots :
  observation (Local.checked analysis termination [] 1%positive) =
    ([], [false; false; false; false; false]).
Proof.
  vm_compute; reflexivity.
Qed.

Example exhausted_discovery :
  Local.checked analysis termination [0] 1%positive = Outcome.OutOfFuel Map.empty.
Proof.
  vm_compute; reflexivity.
Qed.

Example tampered_partial :
  Local.check analysis ix [0]
    (Local.Result (FinSet.of_list nat_encoding [0]) (Local.values cyclic)) =
    Outcome.Rejected Reason.Check_failed.
Proof.
  vm_compute; reflexivity.
Qed.

Example missing_root_rejects :
  Local.check analysis ix [99] cyclic = Outcome.Rejected Reason.Check_failed.
Proof.
  vm_compute; reflexivity.
Qed.

(** The computed checked cyclic result discharges the importing partial-soundness client. *)
Theorem checked_sound_client :
  exists r, Local.checked analysis termination [0] 64%positive = Outcome.Solved r /\
    FixpointPartial.closed_partial nat_encoding bool_lattice system summaries
      (Local.explored r) (lookup nat_encoding bool_lattice (Local.values r)).
Proof.
  exists cyclic; assert (Hrun : Local.checked analysis termination [0] 64%positive =
    Outcome.Solved cyclic) by (vm_compute; reflexivity).
  split; [exact Hrun|].
  exact (proj1 (proj2 (LocalProof.local_checked_sound analysis termination [0] 64%positive
    cyclic laws Hrun))).
Qed.

Definition monotone : monotone_system bool_lattice system.
Proof.
  intros c Hc; destruct c as [|[|[|c]]]; split.
  - intros s t Hle; exact (Hle 1%nat).
  - intros s t Hle x v Hin; vm_compute in Hin; contradiction.
  - intros s t Hle; exact (Hle 0%nat).
  - intros s t Hle x v Hin; vm_compute in Hin; contradiction.
  - intros s t Hle; apply (leb_refl bool_laws).
  - intros s t Hle x v Hin; exists v; split; [exact Hin|apply (leb_refl bool_laws)].
  - intros s t Hle; apply (leb_refl bool_laws).
  - intros s t Hle x v Hin; vm_compute in Hin; contradiction.
Qed.

(** The actual local engine's root values agree with the actual global least solution. *)
Theorem least_client :
  leb bool_lattice (lookup nat_encoding bool_lattice (Local.values cyclic) 0)
    (lookup nat_encoding bool_lattice (FixpointTotal.Total.run analysis termination) 0) = true /\
  leb bool_lattice
    (lookup nat_encoding bool_lattice (FixpointTotal.Total.run analysis termination) 0)
    (lookup nat_encoding bool_lattice (Local.values cyclic) 0) = true.
Proof.
  apply (LocalLeast.local_least analysis termination [0%nat] 64%positive cyclic
    laws bool_lub monotone cyclic_run 0%nat); now left.
Qed.

Example local_is_charged :
  (0 < Cost.ticks (Local.checked_c analysis termination [0%nat] 64%positive))%N.
Proof.
  vm_compute; reflexivity.
Qed.

End LocalTest.
Import LocalTest.
