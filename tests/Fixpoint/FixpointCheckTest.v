(** * Full, partial and cut checks

    Fixtures check cycles, repeated constraints, repeated sides and empty boundaries.
    For example, the seed constraint contributes twice to the cycle head.
    Builds on: FixpointCheck, FixpointPartial and FixpointCut. *)

From Stdlib Require Import List Bool NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Lattice Require Import LatticeCore LatticeSimple.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointEval FixpointIndex
  FixpointCheck FixpointPartial FixpointCut.
Import List.ListNotations Cost.Notations.

Definition cycle_system : System.t nat nat bool :=
  System.Make [0; 1; 2; 0] (fun c => Cost.ret c)
    (fun c => Cost.ret
      (if Nat.eqb c 0 then Query.Ask 1 (fun a => Cost.ret (Query.Ret a))
       else if Nat.eqb c 1 then Query.Ask 0 (fun a => Cost.ret (Query.Ret a))
       else Query.Side 0 true (Query.Side 0 false (Query.Ret false)))).

Definition cycle_static : System.static cycle_system :=
  System.Static
    (fun c => Cost.ret (if Nat.eqb c 0 then [1] else if Nat.eqb c 1 then [0] else []))
    (fun c => Cost.ret (if Nat.eqb c 0 then [] else if Nat.eqb c 1 then [] else [0; 0])).

Definition cycle_values : assignment nat bool :=
  Map.set nat_encoding 1 true (Map.set nat_encoding 0 true Map.empty).

Definition cycle_index := index_system nat_encoding cycle_system cycle_static.
Definition explored := FinSet.of_list nat_encoding [0; 1].

Definition empty_system : System.t nat nat bool :=
  System.Make [] (fun c => Cost.ret c) (fun _ => Cost.ret (Query.Ret true)).
Definition empty_static : System.static empty_system :=
  System.Static (fun _ => Cost.ret []) (fun _ => Cost.ret []).
Definition empty_index := index_system nat_encoding empty_system empty_static.

Example index_repeated_sides :
  contributors_of nat_encoding cycle_index 0 = [0; 2; 0] /\
  readers_of nat_encoding cycle_index 0 = [1] /\
  contributors_of nat_encoding cycle_index 99 = [].
Proof.
  vm_compute; auto.
Qed.

Example full_accept :
  check_post bool_lattice cycle_system (lookup nat_encoding bool_lattice cycle_values) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example full_reject : check_post bool_lattice cycle_system (fun _ => false) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example full_empty : check_post bool_lattice empty_system (fun _ => false) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example full_cycle_ticks :
  Cost.ticks (check_post_c bool_lattice cycle_system
    (fun x => Cost.ret (negb (Nat.eqb x 2)))) = 51%N.
Proof.
  vm_compute; reflexivity.
Qed.

Example partial_accept :
  check_partial nat_encoding nat_encoding bool_lattice cycle_system cycle_static cycle_index
    explored cycle_values = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example partial_reject_open_read :
  check_partial nat_encoding nat_encoding bool_lattice cycle_system cycle_static cycle_index
    (FinSet.of_list nat_encoding [0]) cycle_values = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example partial_empty :
  check_partial nat_encoding nat_encoding bool_lattice cycle_system cycle_static cycle_index
    FinSet.empty Map.empty = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example partial_visits_once :
  partial_rows nat_encoding nat_encoding cycle_index explored = [1; 0; 2].
Proof.
  vm_compute; reflexivity.
Qed.

Definition cycle_certificate :=
  CutCertificate (FinSet.of_list nat_encoding [0])
    (Map.set nat_encoding 99 true (Map.set nat_encoding 0 true Map.empty)) [1; 2].

Example cut_accept :
  option_map (fun m => map (lookup nat_encoding bool_lattice m) [0; 1; 2; 99])
    (expand nat_encoding bool_lattice cycle_system cycle_static cycle_index cycle_certificate) =
    Some [true; true; false; false].
Proof.
  vm_compute; reflexivity.
Qed.

Example cut_reject_order :
  expand nat_encoding bool_lattice cycle_system cycle_static cycle_index
    (CutCertificate FinSet.empty Map.empty [0; 1; 2]) = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example cut_reject_duplicate :
  expand nat_encoding bool_lattice cycle_system cycle_static cycle_index
    (CutCertificate (cuts cycle_certificate) (stored cycle_certificate) [1; 2; 1]) = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example cut_reject_value :
  expand nat_encoding bool_lattice cycle_system cycle_static cycle_index
    (CutCertificate (cuts cycle_certificate) Map.empty [1; 2]) = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example cut_empty :
  expand nat_encoding bool_lattice empty_system empty_static empty_index
    (CutCertificate FinSet.empty Map.empty []) = Some Map.empty.
Proof.
  vm_compute; reflexivity.
Qed.

Example empty_checker_ticks :
  (Cost.ticks (check_post_c bool_lattice empty_system (fun _ => Cost.ret false)),
    Cost.ticks (check_partial_c nat_encoding nat_encoding bool_lattice empty_system empty_static
      empty_index FinSet.empty Map.empty),
    Cost.ticks (expand_c nat_encoding bool_lattice empty_system empty_static empty_index
      (CutCertificate FinSet.empty Map.empty []))) = (0%N, 0%N, 0%N).
Proof.
  vm_compute; reflexivity.
Qed.

Example assignment_lookup_cost_client {X A} (EX : encoding X) (L : lattice A) m x :
  Cost.ticks (lookup_c EX L m x) = Cost.ticks (Map.get_c EX x m).
Proof.
  apply lookup_cost.
Qed.

Example assignment_lookup_present_missing_ticks :
  let m := Map.set nat_encoding 0 true Map.empty in
  (lookup nat_encoding bool_lattice m 0, lookup nat_encoding bool_lattice m 1,
    Cost.ticks (lookup_c nat_encoding bool_lattice m 0),
    Cost.ticks (lookup_c nat_encoding bool_lattice m 1)) = (true, false, 3%N, 4%N).
Proof.
  vm_compute; reflexivity.
Qed.
