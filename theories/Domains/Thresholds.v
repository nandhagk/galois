(** * Threshold trees

    Threshold trees store sorted distinct integers and search for nearby bounds.
    For example, the least threshold above four in [0; 8] is eight.
    Builds on: ThresholdsSig. *)

From Stdlib Require Import List ZArith Arith.
From Galois.Domains Require Import ThresholdsSig.
Import List.ListNotations.

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
    | [x] => [x]
    | x :: (y :: _ as rest) =>
      if Z.eqb x y then dedup_sorted rest else x :: dedup_sorted rest
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
  Proof. Admitted.
  (** Upper search returns the least eligible threshold or proves none exists. *)
  Lemma above_spec : forall t z, ordered t ->
    match above t z with
    | Some u => In u (vals t) /\ (z <= u)%Z /\
      forall v, In v (vals t) -> (z <= v)%Z -> (u <= v)%Z
    | None => forall v, In v (vals t) -> (v < z)%Z
    end.
  Proof. Admitted.
  (** Lower search returns the greatest eligible threshold or proves none exists. *)
  Lemma below_spec : forall t z, ordered t ->
    match below t z with
    | Some u => In u (vals t) /\ (u <= z)%Z /\
      forall v, In v (vals t) -> (v <= z)%Z -> (v <= u)%Z
    | None => forall v, In v (vals t) -> (z < v)%Z
    end.
  Proof. Admitted.
  (** Upper search is sound even when the tree is unordered. *)
  Lemma above_sound : forall t z u,
    above t z = Some u -> In u (vals t) /\ (z <= u)%Z.
  Proof. Admitted.
  (** Lower search is sound even when the tree is unordered. *)
  Lemma below_sound : forall t z u,
    below t z = Some u -> In u (vals t) /\ (u <= z)%Z.
  Proof. Admitted.
End Thresholds.
