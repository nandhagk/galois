(** * Map traversal cost boundaries

    Physical skeleton size and callback sums account for map-wide traversal work.
    For example, one binding at a long code has one callback and many physical path nodes.
    Builds on: BaseMap and the public BaseTrieCost contracts. *)

From Stdlib Require Import List NArith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseTrie BaseTrieMerge BaseTrieCost BaseMap.
Import List.ListNotations.

Module MapCost.

(** Raw-map emptiness is a zero-tick root observation without a well-formedness premise. *)
Theorem is_empty_cost {K V} (m : Map.t K V) : Cost.ticks (Map.is_empty_c m) = 0%N.
Proof.
  reflexivity.
Qed.

(** Physical nodes count branching and unary nodes independently of binding cardinality. *)
Definition skeleton_nodes {K V} (m : Map.t K V) : N := TrieCost.skeleton_nodes m.

(** Map size counting is linear in physical skeleton nodes, including empty overhead. *)
Theorem size_cost {K V} (m : Map.t K V) :
  (Cost.ticks (Map.size_c m) <= TrieCost.trie_k * (1 + skeleton_nodes m))%N.
Proof.
  rewrite Map.size_backend. apply TrieCost.size_cost.
Qed.

(** Map enumeration traverses physical nodes and retains stored keys without rebuilding codes. *)
Theorem elements_cost {K V} (m : Map.t K V) :
  (Cost.ticks (Map.elements_c m) <= TrieCost.trie_k * (1 + skeleton_nodes m))%N.
Proof.
  apply TrieCost.map_elements_cost.
Qed.

Local Lemma callback_sum {K V W} (f : V -> Cost.t W) (xs : list (positive * (K * V))) :
  fold_right (fun pv n =>
    (Cost.ticks (Cost.map (fun w => (fst (snd pv), w)) (f (snd (snd pv)))) + n)%N)
    0%N xs =
  fold_right (fun kv n => (Cost.ticks (f (snd kv)) + n)%N) 0%N (List.map snd xs).
Proof.
  induction xs as [|[p [k v]] xs IH]; cbn [fold_right List.map snd fst];
    rewrite ?Cost.ticks_map, ?IH; reflexivity.
Qed.

(** Mapping separates physical-node overhead and every actual stored callback charge. *)
Theorem map_cost {K V W} (f : V -> Cost.t W) (m : Map.t K V) :
  (Cost.ticks (Map.map_c f m) <= 1 + 2 * skeleton_nodes m +
    fold_right (fun kv n => Cost.ticks (f (snd kv)) + n)%N 0%N (Map.elements m))%N.
Proof.
  rewrite Map.map_backend.
  pose proof (TrieCost.map_cost_relative
    (fun kv => Cost.map (fun w => (fst kv, w)) (f (snd kv))) m) as Hcost.
  rewrite TrieCost.binding_weight_elements, callback_sum in Hcost.
  rewrite Map.elements_backend. unfold skeleton_nodes. lia.
Qed.

(** Actual stored-key widths bound physical skeleton size under map well-formedness. *)
Theorem skeleton_width {K V} (E : encoding K) (m : Map.t K V) b :
  Map.wf E m ->
  (forall k v, Map.get E k m = Some v -> (key_bits E k <= b)%N) ->
  (skeleton_nodes m <= N.of_nat (Map.size m) * b)%N.
Proof.
  intros Hwf Hbits. apply TrieCost.skeleton_width.
  intros p [k v] Hget.
  pose proof (Map.stored_code E m p k v Hwf Hget) as Hcode.
  pose proof (Map.stored_get E m p k v Hwf Hget) as Hkey.
  specialize (Hbits k v Hkey). unfold key_bits in Hbits. now rewrite Hcode in Hbits.
Qed.

(** Finite stored-key widths give a cardinality bound for the actual map enumeration. *)
Theorem elements_numeric_cost {K V} (E : encoding K) (m : Map.t K V) b :
  Map.wf E m ->
  (forall k v, Map.get E k m = Some v -> (key_bits E k <= b)%N) ->
  (Cost.ticks (Map.elements_c m) <=
    TrieCost.trie_k * (1 + N.of_nat (Map.size m) * b))%N.
Proof.
  intros Hwf Hbits. pose proof (elements_cost m) as Hcost.
  pose proof (skeleton_width E m b Hwf Hbits) as Hnodes. nia.
Qed.

(** A finite stored-code-width premise gives the cardinality corollary with full callbacks. *)
Theorem map_numeric_cost {K V W} (E : encoding K) (f : V -> Cost.t W)
    (m : Map.t K V) b :
  Map.wf E m ->
  (forall k v, Map.get E k m = Some v -> (key_bits E k <= b)%N) ->
  (Cost.ticks (Map.map_c f m) <= 1 + 2 * N.of_nat (Map.size m) * b +
    fold_right (fun kv n => Cost.ticks (f (snd kv)) + n)%N 0%N (Map.elements m))%N.
Proof.
  intros Hwf Hbits. pose proof (map_cost f m) as Hcost.
  pose proof (skeleton_width E m b Hwf Hbits) as Hnodes. nia.
Qed.

(** Difference charges only the left stored-key width product, for arbitrary right storage. *)
Theorem diff_numeric_cost {K V W} (E : encoding K) (m : Map.t K V)
    (n : Map.t K W) b :
  Map.wf E m ->
  (forall k v, Map.get E k m = Some v -> (key_bits E k <= b)%N) ->
  (Cost.ticks (Map.diff_c m n) <=
    TrieCost.trie_k * (1 + N.of_nat (Map.size m) * b))%N.
Proof.
  intros Hwf Hbits. rewrite Map.diff_backend.
  pose proof (TrieCost.diff_cost m n) as Hcost.
  pose proof (N.le_min_l (TrieCost.skeleton_nodes m) (TrieCost.skeleton_nodes n)) as Hleft.
  pose proof (skeleton_width E m b Hwf Hbits) as Hnodes.
  change (TrieCost.skeleton_nodes m <= N.of_nat (Map.size m) * b)%N in Hnodes.
  nia.
Qed.

(** Union retains every collision callback and the physical overlap traversal separately. *)
Theorem union_with_cost {K V} (f : V -> V -> Cost.t V) (m n : Map.t K V) :
  (Cost.ticks (Map.union_with_c f m n) <=
    TrieCost.trie_k * (1 + TrieCost.shared_nodes m n) +
    TrieCost.overlap (TrieCost.callback_weight
      (fun a b : K * V => Cost.ticks (f (snd a) (snd b)))) m n)%N.
Proof.
  rewrite Map.union_with_backend.
  pose proof (TrieCost.union_with_cost
    (fun a b => Cost.map (fun v => (fst a, v)) (f (snd a) (snd b))) m n) as Hcost.
  exact Hcost.
Qed.

(** A right-operand width budget bounds union independently of arbitrary left storage. *)
Theorem union_with_numeric_cost_right {K V} (E : encoding K)
    (f : V -> V -> Cost.t V) (m n : Map.t K V) b c :
  Map.wf E n ->
  (forall k v, Map.get E k n = Some v -> (key_bits E k <= b)%N) ->
  (forall v w, (Cost.ticks (f v w) <= c)%N) ->
  (Cost.ticks (Map.union_with_c f m n) <=
    (TrieCost.trie_k + c) * (1 + N.of_nat (Map.size n) * b))%N.
Proof.
  intros Hwf Hbits Hcallback. rewrite Map.union_with_backend.
  pose proof (TrieCost.union_with_cost_numeric
    (fun a b => Cost.map (fun v => (fst a, v)) (f (snd a) (snd b))) m n c
    (fun a b => Hcallback (snd a) (snd b))) as Hcost.
  pose proof (TrieCost.shared_nodes_right m n) as Hright.
  pose proof (skeleton_width E n b Hwf Hbits) as Hnodes.
  change (TrieCost.skeleton_nodes n <= N.of_nat (Map.size n) * b)%N in Hnodes.
  nia.
Qed.

End MapCost.
