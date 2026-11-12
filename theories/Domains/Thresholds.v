(** * Threshold trees

    Threshold trees store sorted distinct integers and search for nearby bounds.
    For example, the least threshold above four in [0; 8] is eight.
    Builds on: ThresholdsSig. *)

From Stdlib Require Import List ZArith Arith Sorting.Sorted Sorting.Permutation.
From Argent Require Import Time Tactics Std BigO.
From Galois.Domains Require Import ThresholdsSig.
Import List.ListNotations.

Module Nat.
  TimeFun Stdlib.Arith.PeanoNat.Nat.divmod.
  TimeFun Stdlib.Arith.PeanoNat.Nat.div.
End Nat.

Module ListDef.
  TimeFun Corelib.Lists.ListDef.firstn.
  TimeFun Corelib.Lists.ListDef.skipn.
End ListDef.

Module ThresholdsCode <: THRESHOLDS_OPS.
  Fixpoint merge (fuel : nat) (xs ys : list Z) : list Z :=
    match fuel with
    | 0 => []
    | S fuel =>
      match xs, ys with
      | [], _ => ys
      | _, [] => xs
      | x :: xt, y :: yt =>
        if Z.leb x y then x :: merge fuel xt ys else y :: merge fuel xs yt
      end
    end.

  Fixpoint sort_fuel (fuel : nat) (xs : list Z) : list Z :=
    match fuel with
    | 0 => xs
    | S fuel =>
      match xs with
      | [] | [_] => xs
      | _ =>
        let middle := length xs / 2 in
        let lhs := sort_fuel fuel (firstn middle xs) in
        let rhs := sort_fuel fuel (skipn middle xs) in
        merge (length xs) lhs rhs
      end
    end.

  Definition msort (xs : list Z) := sort_fuel (length xs) xs.

  Fixpoint dedup_sorted (xs : list Z) : list Z :=
    match xs with
    | [] => []
    | x :: rest =>
      match rest with
      | [] => [x]
      | y :: _ => if Z.eqb x y then dedup_sorted rest else x :: dedup_sorted rest
      end
    end.

  Fixpoint build (fuel : nat) (xs : list Z) : ttree :=
    match fuel with
    | 0 => TLeaf
    | S fuel =>
      let middle := length xs / 2 in
      match skipn middle xs with
      | [] => TLeaf
      | x :: rhs => TNode (build fuel (firstn middle xs)) x (build fuel rhs)
      end
    end.

  Definition make (xs : list Z) : ttree :=
    let sorted := dedup_sorted (msort xs) in build (length sorted) sorted.

  Fixpoint below (tree : ttree) (z : Z) : option Z :=
    match tree with
    | TLeaf => None
    | TNode lhs value rhs =>
      if Z.leb value z then
        match below rhs z with
        | Some x => Some (Z.max value x)
        | None => Some value
        end
      else below lhs z
    end.

  Fixpoint above (tree : ttree) (z : Z) : option Z :=
    match tree with
    | TLeaf => None
    | TNode lhs value rhs =>
      if negb (Z.ltb value z) then
        match above lhs z with
        | Some x => Some (Z.min value x)
        | None => Some value
        end
      else above rhs z
    end.
End ThresholdsCode.

Module Thresholds <: THRESHOLDS.
  Include ThresholdsCode.
  Include THRESHOLDS_SPEC.
  (** Construction retains precisely the supplied thresholds. *)
  Lemma make_vals : forall zs x, In x (vals (make zs)) <-> In x zs.
  Proof. Admitted. (* CONVERT: threshold_index_membership: The variable build_membership was not found. *)
  (** Construction orders and deduplicates thresholds. *)
  Lemma make_ordered : forall zs, ordered (make zs).
  Proof. Admitted. (* CONVERT: threshold_index_ordered: The variable threshold_of_list_wf was not found. *)
  (** Construction produces a logarithmic-depth tree. *)
  Lemma make_depth : forall zs, depth (make zs) <= Nat.log2 (length zs) + 1.
  Proof. Admitted. (* CONVERT: threshold_depth_bound: The variable build_depth was not found. *)
  (** Upper search returns the least eligible threshold or proves none exists. *)
  Lemma above_spec : forall t z, ordered t ->
    match above t z with
    | Some u => In u (vals t) /\ (z <= u)%Z /\
      forall v, In v (vals t) -> (z <= v)%Z -> (u <= v)%Z
    | None => forall v, In v (vals t) -> (v < z)%Z
    end.
  Proof. Admitted. (* CONVERT: upper_threshold_least: No product even after head-reduction. *)
  (** Lower search returns the greatest eligible threshold or proves none exists. *)
  Lemma below_spec : forall t z, ordered t ->
    match below t z with
    | Some u => In u (vals t) /\ (u <= z)%Z /\
      forall v, In v (vals t) -> (v <= z)%Z -> (v <= u)%Z
    | None => forall v, In v (vals t) -> (z < v)%Z
    end.
  Proof. Admitted. (* CONVERT: lower_threshold_greatest: No product even after head-reduction. *)
  (** Upper search is sound even when the tree is unordered. *)
  Lemma above_sound : forall t z u,
    above t z = Some u -> In u (vals t) /\ (z <= u)%Z.
  Proof. Admitted. (* CONVERT: upper_threshold_member: In environment *)
  (** Lower search is sound even when the tree is unordered. *)
  Lemma below_sound : forall t z u,
    below t z = Some u -> In u (vals t) /\ (u <= z)%Z.
  Proof. Admitted. (* CONVERT: lower_threshold_member: In environment *)
End Thresholds.

Module ThresholdsT <: THRESHOLDS_ALL.
  Include Thresholds.

  TimeFun merge.
  TimeFun sort_fuel.
  TimeFun msort.
  TimeFun dedup_sorted.
  TimeFun build.
  TimeFun make.
  TimeFun below.
  TimeFun above.

  Definition c_thresholds : N := 1%N. (* STUB *)
  Definition k_sort : N := 1%N. (* STUB *)
  Definition k_dedup : N := 1%N. (* STUB *)
  Definition k_build : N := 1%N. (* STUB *)
  Definition k_search : N := 1%N. (* STUB *)

  Lemma T_make_le : forall zs,
    (T_make zs <= c_thresholds * N.of_nat (length zs *
      (Nat.log2 (length zs) + 1) + 1) * N.of_nat (zb zs + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T_above_le : forall t z,
    (T_above t z <= c_thresholds * N.of_nat ((depth t + 1)%nat) *
      N.of_nat ((tree_bits t + 1)%nat))%N.
  Proof. Admitted. (* STUB *)

  Lemma T_below_le : forall t z,
    (T_below t z <= c_thresholds * N.of_nat ((depth t + 1)%nat) *
      N.of_nat ((tree_bits t + 1)%nat))%N.
  Proof. Admitted. (* STUB *)

  Lemma make_bigO : (bigO (fun _ => True)
    (fun zs => N.of_nat
      (((length zs * (Nat.log2 (length zs) + 1) + 1) * (zb zs + 1))%nat)) T_make)%N.
  Proof. Admitted. (* STUB *)

  Lemma F1_msort_sorted : forall zs, Sorted Z.le (msort zs).
  Proof. Admitted. (* STUB *)

  Lemma F2_msort_perm : forall zs, Permutation zs (msort zs).
  Proof. Admitted. (* STUB *)

  Lemma F3_dedup_vals : forall zs x, In x (dedup_sorted zs) <-> In x zs.
  Proof. Admitted. (* STUB *)

  Lemma F4_dedup_ordered : forall zs, Sorted Z.le zs ->
    StronglySorted Z.lt (dedup_sorted zs).
  Proof. Admitted. (* STUB *)

  Lemma F5_build_vals : forall fuel zs, length zs <= fuel ->
    vals (build fuel zs) = zs.
  Proof. Admitted. (* STUB *)

  Lemma F6_build_depth : forall fuel zs, length zs <= fuel ->
    depth (build fuel zs) <= Nat.log2 (length zs) + 1.
  Proof. Admitted. (* STUB *)

  Lemma F7_make_eq : forall zs,
    make zs = build (length zs) (dedup_sorted (msort zs)).
  Proof. Admitted. (* STUB *)

  Lemma T1_msort : forall zs,
    (T_msort zs <= k_sort * N.of_nat
      (length zs * (Nat.log2 (length zs) + 1) + 1) *
      N.of_nat (zb zs + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T2_dedup : forall zs,
    (T_dedup_sorted zs <= k_dedup * N.of_nat ((length zs + 1)%nat) *
      N.of_nat ((zb zs + 1)%nat))%N.
  Proof. Admitted. (* STUB *)

  Lemma T3_build : forall fuel zs, length zs <= fuel ->
    (T_build fuel zs <= k_build * N.of_nat
      ((length zs * (Nat.log2 (length zs) + 1) + fuel + 1)%nat))%N.
  Proof. Admitted. (* STUB *)

  Lemma T4_above : forall t z,
    (T_above t z <= k_search * N.of_nat ((depth t + 1)%nat) *
      N.of_nat ((tree_bits t + 1)%nat))%N.
  Proof. Admitted. (* STUB *)

  Lemma T5_below : forall t z,
    (T_below t z <= k_search * N.of_nat ((depth t + 1)%nat) *
      N.of_nat ((tree_bits t + 1)%nat))%N.
  Proof. Admitted. (* STUB *)
End ThresholdsT.
