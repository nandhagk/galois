(** * Balanced rank and compression accounting fixtures

    Equal-rank unions reach logarithmic rank and path compression reduces subsequent find work.
    For example, eight known keys reach rank three and a three-link path compresses to one link.
    Builds on: BaseUnionFindRank, BaseUnionFindCost and the public support observations. *)

From Stdlib Require Import List NArith PeanoNat Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseUnionFind BaseUnionFindRank
  BaseUnionFindCost BaseUnionFindLoop.
Import List.ListNotations.

Definition balanced_pairs : list (positive * positive) :=
  [(1, 2); (3, 4); (5, 6); (7, 8); (1, 3); (5, 7); (1, 5)]%positive.
Definition balanced_forest := UnionFind.of_unions positive_encoding balanced_pairs.
Definition balanced_compressed :=
  snd (UnionFind.find positive_encoding 8%positive balanced_forest).

Example union_find_balanced_rank :
  (UnionFind.max_rank balanced_forest,
    Nat.log2 (length (UnionFind.keys positive_encoding balanced_forest))) = (3, 3).
Proof.
  vm_compute. reflexivity.
Qed.

Example union_find_before_compression :
  Map.get positive_encoding 8%positive (UnionFind.parents balanced_forest) = Some 7%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example union_find_after_compression :
  Map.get positive_encoding 8%positive (UnionFind.parents balanced_compressed) = Some 1%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example union_find_long_path_ticks :
  Cost.ticks (UnionFind.find_c positive_encoding 8%positive balanced_forest) = 51%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example union_find_shortened_path_ticks :
  Cost.ticks (UnionFind.find_c positive_encoding 8%positive balanced_compressed) = 26%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example union_find_unknown_ticks :
  Cost.ticks (UnionFind.find_c positive_encoding 16%positive balanced_forest) = 16%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example union_find_known_key_budget :
  forallb (fun k =>
    N.leb (Cost.ticks (encode_c positive_encoding k) +
      N.pos (Pos.size (encode positive_encoding k))) 5)
    (UnionFind.keys positive_encoding balanced_forest) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example union_find_unknown_query_budget :
  (Cost.ticks (encode_c positive_encoding 16%positive) +
    N.pos (Pos.size (encode positive_encoding 16%positive)))%N = 6%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example union_find_compression_cost_bound :
  N.leb (Cost.ticks (UnionFind.find_c positive_encoding 8%positive balanced_forest))
    (UnionFindCost.uf_k * (1 + N.log2 8) * (1 + 5)) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Definition cyclic_forest :=
  UnionFind.Forest
    (Map.set positive_encoding 1%positive 2%positive
      (Map.set positive_encoding 2%positive 1%positive Map.empty))
    Map.empty 0.

Example union_find_raw_cycle_prefix :
  fst (UnionFind.find_fuel positive_encoding 1 1%positive cyclic_forest) = 2%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example union_find_raw_cycle_compression :
  let compressed := snd (UnionFind.find_fuel positive_encoding 2 1%positive cyclic_forest) in
  (Map.get positive_encoding 1%positive (UnionFind.parents compressed),
    Map.get positive_encoding 2%positive (UnionFind.parents compressed)) =
    (Some 1%positive, Some 1%positive).
Proof.
  vm_compute. reflexivity.
Qed.

(** * Clients of the public proof contracts *)

Local Lemma balanced_rank_certificate :
  UnionFindRank.rank_size_inv positive_encoding balanced_forest.
Proof.
  apply UnionFindRank.of_unions_rank_size_inv. exact positive_encoding_laws.
Qed.

Local Lemma balanced_forest_wf : UnionFind.wf positive_encoding balanced_forest.
Proof.
  exact (UnionFindRank.forest_wf _ _ balanced_rank_certificate).
Qed.

Local Lemma balanced_support_budget :
  UnionFindCost.support_budget positive_encoding 5 balanced_forest.
Proof.
  intros k Hsupport.
  pose proof (proj2 (UnionFind.keys_spec positive_encoding positive_encoding_laws
    balanced_forest k balanced_forest_wf) Hsupport) as Hin.
  pose proof (proj1 (forallb_forall _ _) union_find_known_key_budget k Hin) as Hbound.
  apply N.leb_le in Hbound. exact Hbound.
Qed.

Local Lemma balanced_eight_bound : UnionFindCost.key_bound positive_encoding 5 8%positive.
Proof.
  apply balanced_support_budget. left.
  rewrite union_find_before_compression. discriminate.
Qed.

Local Lemma balanced_support_budget_six :
  UnionFindCost.support_budget positive_encoding 6 balanced_forest.
Proof.
  intros k Hsupport. pose proof (balanced_support_budget k Hsupport) as Hbound.
  unfold UnionFindCost.key_bound in *. lia.
Qed.

Local Lemma balanced_eight_bound_six :
  UnionFindCost.key_bound positive_encoding 6 8%positive.
Proof.
  pose proof balanced_eight_bound as Hbound.
  unfold UnionFindCost.key_bound in *. lia.
Qed.

Local Lemma balanced_unknown_bound :
  UnionFindCost.key_bound positive_encoding 6 16%positive.
Proof.
  unfold UnionFindCost.key_bound. rewrite union_find_unknown_query_budget.
  apply N.le_refl.
Qed.

Local Lemma balanced_unknown_outside :
  ~ UnionFind.support positive_encoding balanced_forest 16%positive.
Proof.
  unfold UnionFind.support. intros [Hparent|Hrank].
  - apply Hparent. vm_compute. reflexivity.
  - apply Hrank. vm_compute. reflexivity.
Qed.

(** The supported-query client discharges its certificate and width through public support facts. *)
Theorem union_find_supported_cost_client :
  (Cost.ticks (UnionFind.find_c positive_encoding 8%positive balanced_forest) <=
    UnionFindCost.uf_k *
    N.of_nat (S (Nat.log2 (length (UnionFind.keys positive_encoding balanced_forest)))) *
    (1 + 5))%N.
Proof.
  exact (UnionFindCost.find_cost positive_encoding positive_encoding_laws Map.cost_laws_hold
    8%positive balanced_forest 5 balanced_rank_certificate balanced_support_budget
    balanced_eight_bound).
Qed.

Local Lemma compressed_rank_certificate :
  UnionFindRank.rank_size_inv positive_encoding balanced_compressed.
Proof.
  exact (UnionFindRank.find_rank_size_inv positive_encoding positive_encoding_laws
    balanced_forest 8%positive balanced_rank_certificate).
Qed.

Local Lemma compressed_support_budget :
  UnionFindCost.support_budget positive_encoding 5 balanced_compressed.
Proof.
  intros k Hsupport. apply balanced_support_budget.
  apply (proj1 (UnionFind.find_support positive_encoding positive_encoding_laws
    8%positive balanced_forest k balanced_forest_wf)). exact Hsupport.
Qed.

(** The compressed-query client transports the certificate through the actual returned forest. *)
Theorem union_find_compressed_cost_client :
  (Cost.ticks (UnionFind.find_c positive_encoding 8%positive balanced_compressed) <=
    UnionFindCost.uf_k *
    (1 + N.log2 (N.of_nat (length (UnionFind.keys positive_encoding balanced_compressed)))) *
    (1 + 5))%N.
Proof.
  exact (UnionFindCost.find_cost_logN positive_encoding positive_encoding_laws Map.cost_laws_hold
    8%positive balanced_compressed 5 compressed_rank_certificate compressed_support_budget
    balanced_eight_bound).
Qed.

(** An outside-support query has its own wider budget and does not enlarge the known-key count. *)
Theorem union_find_unknown_cost_client :
  ~ UnionFind.support positive_encoding balanced_forest 16%positive /\
  (Cost.ticks (UnionFind.find_c positive_encoding 16%positive balanced_forest) <=
    UnionFindCost.uf_k *
    (1 + N.log2 (N.of_nat (length (UnionFind.keys positive_encoding balanced_forest)))) *
    (1 + 6))%N.
Proof.
  split; [exact balanced_unknown_outside|].
  exact (UnionFindCost.find_cost_logN positive_encoding positive_encoding_laws Map.cost_laws_hold
    16%positive balanced_forest 6 balanced_rank_certificate balanced_support_budget_six
    balanced_unknown_bound).
Qed.

(** Union's client supplies both supported and unknown query budgets to the public cost theorem. *)
Theorem union_find_union_cost_client :
  (Cost.ticks (UnionFind.union_c positive_encoding 8%positive 16%positive balanced_forest) <=
    UnionFindCost.uf_k *
    N.of_nat (S (Nat.log2 (length (UnionFind.keys positive_encoding balanced_forest)))) *
    (1 + 6))%N.
Proof.
  exact (UnionFindCost.union_cost positive_encoding positive_encoding_laws Map.cost_laws_hold
    8%positive 16%positive balanced_forest 6 balanced_rank_certificate balanced_support_budget_six
    balanced_eight_bound_six balanced_unknown_bound).
Qed.

(** Equivalence testing uses the same complete supported and unknown-query premises. *)
Theorem union_find_equivb_cost_client :
  (Cost.ticks (UnionFind.equivb_c positive_encoding 8%positive 16%positive balanced_forest) <=
    UnionFindCost.uf_k *
    N.of_nat (S (Nat.log2 (length (UnionFind.keys positive_encoding balanced_forest)))) *
    (1 + 6))%N.
Proof.
  exact (UnionFindCost.equivb_cost positive_encoding positive_encoding_laws Map.cost_laws_hold
    8%positive 16%positive balanced_forest 6 balanced_rank_certificate balanced_support_budget_six
    balanced_eight_bound_six balanced_unknown_bound).
Qed.

Definition balanced_universe : list positive := [1; 2; 3; 4; 5; 6; 7; 8]%positive.

Example union_find_universe_key_budget :
  forallb (fun k =>
    N.leb (Cost.ticks (encode_c positive_encoding k) +
      N.pos (Pos.size (encode positive_encoding k))) 5) balanced_universe = true.
Proof.
  vm_compute. reflexivity.
Qed.

Local Lemma balanced_universe_bounds k :
  In k balanced_universe -> UnionFindCost.key_bound positive_encoding 5 k.
Proof.
  intro Hin.
  pose proof (proj1 (forallb_forall _ _) union_find_universe_key_budget k Hin) as Hbound.
  apply N.leb_le in Hbound. exact Hbound.
Qed.

Local Lemma balanced_pair_universe :
  Forall (fun xy => In (fst xy) balanced_universe /\ In (snd xy) balanced_universe)
    balanced_pairs.
Proof.
  rewrite Forall_forall. intros [x y] Hin.
  cbn [balanced_pairs] in Hin.
  destruct Hin as [Hpair|[Hpair|[Hpair|[Hpair|[Hpair|[Hpair|[Hpair|Hfalse]]]]]]];
    try contradiction; inversion Hpair; subst;
    cbn [fst snd balanced_universe In]; intuition congruence.
Qed.

(** The builder client proves every finite-universe premise of the public numeric theorem. *)
Theorem union_find_builder_cost_client :
  (Cost.ticks (UnionFind.of_unions_c positive_encoding balanced_pairs) <=
    N.of_nat (length balanced_pairs) * UnionFindCost.uf_k *
    N.of_nat (S (Nat.log2 (length balanced_universe))) * (1 + 5))%N.
Proof.
  exact (UnionFindCost.of_unions_cost positive_encoding positive_encoding_laws Map.cost_laws_hold
    balanced_pairs balanced_universe 5 balanced_universe_bounds balanced_pair_universe).
Qed.

(** Reached-accumulator accounting remains exact on the existing malformed-cycle fixture. *)
Theorem union_find_raw_builder_recurrence :
  Cost.ticks
    (UnionFind.unions_from_c positive_encoding ((1, 2)%positive :: balanced_pairs) cyclic_forest) =
  (1 + Cost.ticks (UnionFind.union_c positive_encoding 1%positive 2%positive cyclic_forest) +
    Cost.ticks (UnionFind.unions_from_c positive_encoding balanced_pairs
      (UnionFind.union positive_encoding 1%positive 2%positive cyclic_forest)))%N.
Proof.
  apply UnionFindCost.unions_from_cost_cons.
Qed.

(** A concrete relative builder client needs only its reached union callee's own charge. *)
Theorem union_find_singleton_relative_builder_client :
  (Cost.ticks (UnionFind.of_unions_c positive_encoding [(1, 1)]%positive) <=
    1 + Cost.ticks
      (UnionFind.union_c positive_encoding 1%positive 1%positive UnionFind.make))%N.
Proof.
  set (domain := fun (pairs : list (positive * positive)) (acc : UnionFind.t positive) =>
    match pairs with
    | [] => True
    | [(x, y)] => x = 1%positive /\ y = 1%positive /\ acc = UnionFind.make
    | _ => False
    end).
  assert (Hstep : forall x y rest acc, domain ((x, y) :: rest) acc ->
    (Cost.ticks (UnionFind.union_c positive_encoding x y acc) <=
      Cost.ticks (UnionFind.union_c positive_encoding 1%positive 1%positive UnionFind.make))%N /\
    domain rest (UnionFind.union positive_encoding x y acc)).
  { intros x y rest acc Hdomain. destruct rest as [|pair rest].
    - destruct Hdomain as [Hx [Hy Hacc]]. subst x y acc.
      split; [apply N.le_refl|exact I].
    - contradiction. }
  pose proof (UnionFindCost.of_unions_cost_callee positive_encoding domain
    (Cost.ticks (UnionFind.union_c positive_encoding 1%positive 1%positive UnionFind.make))
    [(1, 1)]%positive Hstep (conj eq_refl (conj eq_refl eq_refl))) as Hcost.
  cbn [length] in Hcost. lia.
Qed.

Example union_find_charged_fuel :
  (Cost.value (UnionFindLoop.sufficient_fuel_c 4),
    Cost.ticks (UnionFindLoop.sufficient_fuel_c 4)) = (16%positive, 4%N).
Proof.
  vm_compute. reflexivity.
Qed.
