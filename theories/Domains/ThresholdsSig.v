(** * Threshold search interfaces

    Balanced threshold trees support widening to the nearest supplied bound.
    For example, searching above 4 in thresholds 0 and 8 returns 8.
    Builds on: Stdlib List and ZArith, Argent BigO. *)

From Stdlib Require Import List ZArith Arith Sorting.Sorted Sorting.Permutation.
From Argent Require Import Std BigO.

Inductive ttree : Type :=
  | TLeaf
  | TNode (l : ttree) (z : Z) (r : ttree).

Module Type THRESHOLDS_OPS.
  Parameter make : list Z -> ttree.
  Parameter above below : ttree -> Z -> option Z.
End THRESHOLDS_OPS.

Module Type THRESHOLDS_SPEC (T : THRESHOLDS_OPS).
  Fixpoint vals (t : ttree) : list Z :=
    match t with
    | TLeaf => nil
    | TNode l z r => vals l ++ z :: vals r
    end.
  Fixpoint depth (t : ttree) : nat :=
    match t with
    | TLeaf => 0
    | TNode l _ r => S (Nat.max (depth l) (depth r))
    end.
  Definition ordered (t : ttree) : Prop := StronglySorted Z.lt (vals t).
  Definition zbits (z : Z) : nat := Z.size_nat z.
  Definition zb (zs : list Z) : nat := fold_right Nat.max 0 (map zbits zs).
  Definition tree_bits (t : ttree) : nat := zb (vals t).
End THRESHOLDS_SPEC.

Module Type THRESHOLDS_LAWS (Import T : THRESHOLDS_OPS) (Import S : THRESHOLDS_SPEC T).
  (** Construction retains precisely the supplied thresholds. *)
  Parameter make_vals : forall zs x, In x (vals (make zs)) <-> In x zs.
  (** Construction orders and deduplicates thresholds. *)
  Parameter make_ordered : forall zs, ordered (make zs).
  (** Construction produces a logarithmic-depth tree. *)
  Parameter make_depth : forall zs, depth (make zs) <= Nat.log2 (length zs) + 1.
  (** Upper search returns the least eligible threshold or proves none exists. *)
  Parameter above_spec : forall t z, ordered t ->
    match above t z with
    | Some u => In u (vals t) /\ (z <= u)%Z /\
      forall v, In v (vals t) -> (z <= v)%Z -> (u <= v)%Z
    | None => forall v, In v (vals t) -> (v < z)%Z
    end.
  (** Lower search returns the greatest eligible threshold or proves none exists. *)
  Parameter below_spec : forall t z, ordered t ->
    match below t z with
    | Some u => In u (vals t) /\ (u <= z)%Z /\
      forall v, In v (vals t) -> (v <= z)%Z -> (v <= u)%Z
    | None => forall v, In v (vals t) -> (z < v)%Z
    end.
  (** Upper search is sound even when the tree is unordered. *)
  Parameter above_sound : forall t z u,
    above t z = Some u -> In u (vals t) /\ (z <= u)%Z.
  (** Lower search is sound even when the tree is unordered. *)
  Parameter below_sound : forall t z u,
    below t z = Some u -> In u (vals t) /\ (u <= z)%Z.
End THRESHOLDS_LAWS.

Module Type THRESHOLDS := THRESHOLDS_OPS <+ THRESHOLDS_SPEC <+ THRESHOLDS_LAWS.

Module Type THRESHOLDS_TIME (Import T : THRESHOLDS).
  Parameter T_make : list Z -> N.
  Parameter T_above T_below : ttree -> Z -> N.
  Parameter c_thresholds : N.
  (** Construction charges comparison sorting and the largest threshold size. *)
  Parameter T_make_le : forall zs,
    (T_make zs <= c_thresholds * N.of_nat (length zs * (Nat.log2 (length zs) + 1) + 1) *
      N.of_nat (zb zs + 1))%N.
  (** Upper search charges a path and comparison bit sizes. *)
  Parameter T_above_le : forall t z, (T_above t z <=
    c_thresholds * N.of_nat ((depth t + 1)%nat) * N.of_nat ((tree_bits t + 1)%nat))%N.
  (** Lower search charges a path and comparison bit sizes. *)
  Parameter T_below_le : forall t z, (T_below t z <=
    c_thresholds * N.of_nat ((depth t + 1)%nat) * N.of_nat ((tree_bits t + 1)%nat))%N.
  (** Construction has the published comparison-sort bound. *)
  Parameter make_bigO : (bigO (fun _ => True)
    (fun zs => N.of_nat
      (((length zs * (Nat.log2 (length zs) + 1) + 1) * (zb zs + 1))%nat)) T_make)%N.
End THRESHOLDS_TIME.

Module Type THRESHOLDS_T := THRESHOLDS <+ THRESHOLDS_TIME.

Module Type THRESHOLDS_PLAN (Import T : THRESHOLDS_T).
  Parameter msort dedup_sorted : list Z -> list Z.
  Parameter build : nat -> list Z -> ttree.
  Parameter T_msort T_dedup_sorted : list Z -> N.
  Parameter T_build : nat -> list Z -> N.
  Parameter k_sort k_dedup k_build k_search : N.
  (** Sorting orders the input. *)
  Parameter F1_msort_sorted : forall zs, Sorted Z.le (msort zs).
  (** Sorting keeps the input multiset. *)
  Parameter F2_msort_perm : forall zs, Permutation zs (msort zs).
  (** Deduplication keeps exactly the input values. *)
  Parameter F3_dedup_vals : forall zs x, In x (dedup_sorted zs) <-> In x zs.
  (** Deduplication turns sorted input into strict order. *)
  Parameter F4_dedup_ordered : forall zs, Sorted Z.le zs ->
    StronglySorted Z.lt (dedup_sorted zs).
  (** Median construction keeps every input value when fuel suffices. *)
  Parameter F5_build_vals : forall fuel zs, length zs <= fuel ->
    vals (build fuel zs) = zs.
  (** Median construction bounds depth when fuel suffices. *)
  Parameter F6_build_depth : forall fuel zs, length zs <= fuel ->
    depth (build fuel zs) <= Nat.log2 (length zs) + 1.
  (** The public constructor uses sorting, deduplication and median construction. *)
  Parameter F7_make_eq : forall zs,
    make zs = build (length zs) (dedup_sorted (msort zs)).
  (** Sorting charges logarithmically many comparison levels. *)
  Parameter T1_msort : forall zs,
    (T_msort zs <= k_sort * N.of_nat (length zs * (Nat.log2 (length zs) + 1) + 1) *
      N.of_nat (zb zs + 1))%N.
  (** Deduplication charges one pass of integer comparisons. *)
  Parameter T2_dedup : forall zs, (T_dedup_sorted zs <=
    k_dedup * N.of_nat ((length zs + 1)%nat) * N.of_nat ((zb zs + 1)%nat))%N.
  (** Median construction charges one logarithmic splitting pass per level. *)
  Parameter T3_build : forall fuel zs, length zs <= fuel -> (T_build fuel zs <=
    k_build * N.of_nat ((length zs * (Nat.log2 (length zs) + 1) + fuel + 1)%nat))%N.
  (** Upper search compares the threshold first at each visited level. *)
  Parameter T4_above : forall t z, (T_above t z <=
    k_search * N.of_nat ((depth t + 1)%nat) * N.of_nat ((tree_bits t + 1)%nat))%N.
  (** Lower search compares the threshold first at each visited level. *)
  Parameter T5_below : forall t z, (T_below t z <=
    k_search * N.of_nat ((depth t + 1)%nat) * N.of_nat ((tree_bits t + 1)%nat))%N.
End THRESHOLDS_PLAN.

Module Type THRESHOLDS_ALL := THRESHOLDS_T <+ THRESHOLDS_PLAN.
