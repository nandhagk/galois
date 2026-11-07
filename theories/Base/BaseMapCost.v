(** * Map traversal cost boundaries

    Physical skeleton size and callback sums account for map-wide traversal work.
    For example, one binding at a long code has one callback and many physical path nodes.
    Builds on: BaseMap and the public BaseTrieCost contracts. *)

From Stdlib Require Import List NArith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseTrie BaseTrieMerge BaseTrieCost BaseMap.
Import List.ListNotations.

Module MapCost.

(** Physical nodes count branching and unary nodes independently of binding cardinality. *)
Definition skeleton_nodes {K V} (m : Map.t K V) : N := TrieCost.skeleton_nodes m.

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

End MapCost.
