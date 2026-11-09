(** * Primitive finite-domain cost bounds for dominance

    These bounds price actual queries and traversals using finite support and encoded widths.
    For example, enumeration of a canonical set pays its physical trie paths and emitted keys.
    Builds on: public map, set and costed-list contracts. *)

From Stdlib Require Import List Bool PArith NArith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet BaseMapCost BaseTrieCost.
Import Cost.Notations.

Module DomCostBasis.
Local Open Scope N_scope.

(** Positive-key operations retain the call overhead, unit encoder and actual code width. *)
Theorem get_cost {A} (m : Map.t positive A) v :
  Cost.ticks (Map.get_c positive_encoding v m) = 2 + key_bits positive_encoding v.
Proof.
  rewrite Map.get_cost. reflexivity.
Qed.

(** Insertion has the same key price independently of the stored value and existing support. *)
Theorem set_cost {A} (m : Map.t positive A) v a :
  Cost.ticks (Map.set_c positive_encoding v a m) = 2 + key_bits positive_encoding v.
Proof.
  rewrite Map.set_cost. reflexivity.
Qed.

(** Set membership charges the actual queried code even when it is absent. *)
Theorem mem_cost s v :
  Cost.ticks (FinSet.mem_c positive_encoding v s) = 2 + key_bits positive_encoding v.
Proof.
  rewrite FinSet.mem_cost. reflexivity.
Qed.

(** Membership-restricted callback bounds suffice for a linear charged mapping bound. *)
Theorem map_cost {A B} (f : A -> Cost.t B) xs k :
  (forall x, In x xs -> Cost.ticks (f x) <= k) ->
  Cost.ticks (map_c f xs) <= N.of_nat (length xs) * (1 + k).
Proof.
  rewrite ticks_map_c.
  induction xs as [|x rest IH]; intro Hcost.
  - reflexivity.
  - cbn [fold_right].
    pose proof (Hcost x (or_introl eq_refl)) as Hhead.
    specialize (IH ltac:(intros y Hy; apply Hcost; now right)).
    cbn [length]. rewrite Nat2N.inj_succ. nia.
Qed.

(** Filtering charges every input occurrence, including those whose predicate is false. *)
Theorem filter_cost {A} (f : A -> Cost.t bool) xs k :
  (forall x, In x xs -> Cost.ticks (f x) <= k) ->
  Cost.ticks (filter_c f xs) <= N.of_nat (length xs) * (1 + k).
Proof.
  rewrite ticks_filter_c.
  induction xs as [|x rest IH]; intro Hcost.
  - reflexivity.
  - cbn [fold_right].
    pose proof (Hcost x (or_introl eq_refl)) as Hhead.
    specialize (IH ltac:(intros y Hy; apply Hcost; now right)).
    cbn [length]. rewrite Nat2N.inj_succ. nia.
Qed.

(** Short-circuit conjunction retains an upper bound without assuming any successful result. *)
Theorem forallb_cost {A} (f : A -> Cost.t bool) xs k :
  (forall x, In x xs -> Cost.ticks (f x) <= k) ->
  Cost.ticks (forallb_c f xs) <= N.of_nat (length xs) * (1 + k).
Proof.
  induction xs as [|x rest IH]; intro Hcost.
  - rewrite ticks_forallb_c_nil. reflexivity.
  - rewrite ticks_forallb_c_cons.
    pose proof (Hcost x (or_introl eq_refl)) as Hhead.
    specialize (IH ltac:(intros y Hy; apply Hcost; now right)).
    cbn [length]. rewrite Nat2N.inj_succ. destruct (Cost.value (f x)); nia.
Qed.

(** Right-fold prices may depend on the finite input domain and remain uniform in the accumulator. *)
Theorem fold_right_cost {A B} (f : A -> B -> Cost.t B) xs initial k :
  (forall x b, In x xs -> Cost.ticks (f x b) <= k) ->
  Cost.ticks (fold_right_c f initial xs) <= N.of_nat (length xs) * (1 + k).
Proof.
  intro Hcost.
  pose proof (proj2 (ticks_fold_right_c_potential f (fun _ => True) (fun _ => 0) k
    xs initial ltac:(intros x b Hx _; split; [exact I|];
      pose proof (Hcost x b Hx); cbn beta; lia) I)) as Hfold.
  cbn beta in Hfold. rewrite N.add_comm. lia.
Qed.

(** Constructing a positive-key set charges every occurrence even when keys repeat. *)
Theorem of_list_cost xs w :
  (forall v, In v xs -> key_bits positive_encoding v <= w) ->
  Cost.ticks (FinSet.of_list_c positive_encoding xs) <=
    N.of_nat (length xs) * (4 + w).
Proof.
  intro Hwidth.
  apply (FinSet.of_list_numeric_cost Map.cost_laws_hold positive_encoding xs 1 w).
  intros v Hv. split; [reflexivity|now apply Hwidth].
Qed.

(** Canonical set construction cannot create more bindings than its supplied occurrences. *)
Theorem of_list_size xs :
  (FinSet.size (FinSet.of_list positive_encoding xs) <= length xs)%nat.
Proof.
  apply (Map.size_support_bound positive_encoding positive_encoding_laws).
  - apply FinSet.wf_of_list.
  - intros v [] Hget. apply FinSet.mem_spec in Hget.
    rewrite FinSet.mem_of_list, existsb_exists in Hget.
    destruct Hget as [u [Hu Heq]]. apply (eqb_true_iff _ positive_encoding_laws) in Heq.
    now subst u.
Qed.

(** Query support bounds physical enumeration without assuming any previous successful computation. *)
Theorem elements_cost s n w :
  FinSet.wf positive_encoding s ->
  (FinSet.size s <= n)%nat ->
  (forall v, FinSet.mem positive_encoding v s = true -> key_bits positive_encoding v <= w) ->
  Cost.ticks (FinSet.elements_c s) <=
    TrieCost.trie_k * (1 + N.of_nat n * w) + N.of_nat n.
Proof.
  intros Hset Hsize Hwidth.
  pose proof (MapCost.elements_numeric_cost positive_encoding s w Hset
    ltac:(intros v [] Hget; apply Hwidth; now apply FinSet.mem_spec)) as Hmap.
  rewrite FinSet.elements_cost_equation.
  assert (Hscale : TrieCost.trie_k * (1 + N.of_nat (FinSet.size s) * w) <=
    TrieCost.trie_k * (1 + N.of_nat n * w)).
  { apply N.mul_le_mono; [reflexivity|].
    apply N.add_le_mono; [reflexivity|]. apply N.mul_le_mono; [lia|reflexivity]. }
  change (Map.size s <= n)%nat in Hsize.
  change (Cost.ticks (Map.elements_c s) +
    N.of_nat (Map.size s) <= TrieCost.trie_k * (1 + N.of_nat n * w) + N.of_nat n).
  change (TrieCost.trie_k * (1 + N.of_nat (Map.size s) * w) <=
    TrieCost.trie_k * (1 + N.of_nat n * w)) in Hscale.
  eapply N.add_le_mono; [eapply N.le_trans; [exact Hmap|exact Hscale]|lia].
Qed.

End DomCostBasis.
