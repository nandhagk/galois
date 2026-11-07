(** * Set representation boundaries

    Set comparisons through enumerated keys require well-formed stored codes.
    For example, a mismatched stored key makes an unvalidated set reject itself.
    Builds on: CostList, BaseEncoding and BaseSet. *)

From Stdlib Require Import List PArith NArith.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseSet.
From Galois.Lattice Require Import LatticeCore LatticeHeight LatticeSet.
Import List.ListNotations Cost.Notations.

(** This fixture follows the requested single traversal over left-hand members. *)
Definition fixture_subset_c {K} (E : encoding K) (s t : FinSet.t K) :=
  let* keys := FinSet.elements_c s in
  forallb_c (fun k => FinSet.mem_c E k t) keys.

(** This local mathematical model observes membership by stored code. *)
Local Definition reference_list_mem p (xs : list (positive * (positive * unit))) :=
  existsb (fun e => Pos.eqb p (fst e)) xs.

(** This local model enumerates stored keys without repairing mismatched codes. *)
Local Definition reference_list_elements (xs : list (positive * (positive * unit))) :=
  List.map (fun e => fst (snd e)) xs.

(** This local model compares the enumerated left keys with right code membership. *)
Local Definition reference_list_subset xs ys :=
  forallb (fun k => reference_list_mem k ys) (reference_list_elements xs).

(** This deliberately malformed local list stores key two at code one. *)
Local Definition reference_mismatched_raw_set : list (positive * (positive * unit)) :=
  [(1%positive, (2%positive, tt))].

Example raw_enumeration_comparison_not_reflexive :
  reference_list_subset reference_mismatched_raw_set reference_mismatched_raw_set = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example raw_enumeration_differs_from_membership :
  (reference_list_elements reference_mismatched_raw_set,
    reference_list_mem 1%positive reference_mismatched_raw_set,
    reference_list_mem 2%positive reference_mismatched_raw_set) =
  ([2%positive], true, false).
Proof.
  vm_compute. reflexivity.
Qed.

Definition constructed_set := FinSet.of_list positive_encoding [2%positive; 2%positive].

Example constructed_enumeration_comparison_reflexive :
  Cost.value (fixture_subset_c positive_encoding constructed_set constructed_set) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example empty_enumeration_comparison :
  Cost.value (fixture_subset_c positive_encoding FinSet.empty constructed_set) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Definition set_universe := [1%positive; 2%positive; 3%positive].
Definition s0 := set_empty positive_encoding.
Definition s1 := set_of_list positive_encoding [1%positive].
Definition s2 := set_of_list positive_encoding [2%positive].
Definition s12 := set_of_list positive_encoding [1%positive; 2%positive].
Definition s123 := set_of_list positive_encoding set_universe.
Definition may_pos := may positive_encoding.
Definition must_pos := must positive_encoding.

Example may_boundary_and_order :
  (leb may_pos s0 s1, leb may_pos s1 s1, leb may_pos s1 s2, leb may_pos s2 s1) =
  (true, true, false, false).
Proof.
  vm_compute. reflexivity.
Qed.

Example may_operations :
  (FinSet.elements (set_raw (join may_pos s1 s2)),
    FinSet.elements (set_raw (widen may_pos s1 s2)),
    FinSet.elements (set_raw (narrow may_pos s1 s2))) =
  ([2%positive; 1%positive], [2%positive; 1%positive], [1%positive]).
Proof.
  vm_compute. reflexivity.
Qed.

Example may_cost_observations :
  (Cost.ticks (leb_c may_pos s1 s1), Cost.ticks (join_c may_pos s0 s0)) =
  (9%N, 1%N).
Proof.
  vm_compute. reflexivity.
Qed.

Example may_height_reaches_bound :
  (List.map (rank (may_height positive_encoding positive_encoding_laws set_universe))
    [s0; s1; s12; s123],
    bound (may_height positive_encoding positive_encoding_laws set_universe)) =
  ([0; 1; 2; 3], 3)%nat.
Proof.
  vm_compute. reflexivity.
Qed.

Example may_chain_has_three_strict_steps :
  List.map (fun p => (leb may_pos (fst p) (snd p), leb may_pos (snd p) (fst p)))
    [(s0, s1); (s1, s12); (s12, s123)] =
  [(true, false); (true, false); (true, false)].
Proof.
  vm_compute. reflexivity.
Qed.

Example must_boundary_and_order :
  (leb must_pos All (Only s123), leb must_pos (Only s123) All,
    leb must_pos (Only s1) (Only s2), leb must_pos (Only s2) (Only s1)) =
  (true, false, false, false).
Proof.
  vm_compute. reflexivity.
Qed.

Definition must_members (s : must_t positive_encoding) :=
  match s with
  | All => None
  | Only s => Some (FinSet.elements (set_raw s))
  end.

Example must_operations :
  (must_members (join must_pos (Only s1) (Only s2)),
    must_members (widen must_pos (Only s1) (Only s2)),
    must_members (narrow must_pos (Only s1) (Only s2))) =
  (Some [], Some [], Some [1%positive]).
Proof.
  vm_compute. reflexivity.
Qed.

Example must_height_fresh_bottom_overhead :
  (List.map (rank (must_height positive_encoding positive_encoding_laws set_universe))
    [All; Only s123; Only s12; Only s1; Only s0],
    bound (must_height positive_encoding positive_encoding_laws set_universe)) =
  ([0; 1; 2; 3; 4], 4)%nat.
Proof.
  vm_compute. reflexivity.
Qed.

Example must_empty_universe_still_has_a_step :
  (rank (must_height positive_encoding positive_encoding_laws []) All,
    rank (must_height positive_encoding positive_encoding_laws []) (Only s0),
    bound (must_height positive_encoding positive_encoding_laws [])) = (0, 1, 1)%nat.
Proof.
  vm_compute. reflexivity.
Qed.
