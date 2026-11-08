(** * Interning cost clients

    Primitive equations expose lookup and allocation charges to clients.
    For example, a repeated key pays just its forward lookup.
    Builds on: BaseIntern, BaseMap and BaseSet. *)

From Stdlib Require Import List NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet BaseIntern BaseInternCost.
Import List.ListNotations.

Example intern_hit_cost_client {K} (E : encoding K) k i (s : Intern.t K) :
  Intern.find E k s = Some i ->
  Cost.ticks (Intern.intern_c E k s) = Cost.ticks (Map.get_c E k (Intern.table s)).
Proof.
  intro Hhit. rewrite Intern.intern_cost_equation, Hhit. apply N.add_0_r.
Qed.

Example map_mem_cost_client {K V} (E : encoding K) k (m : Map.t K V) :
  Cost.ticks (Map.mem_c E k m) =
    (1 + Cost.ticks (encode_c E k) + key_bits E k)%N.
Proof.
  apply Map.mem_cost.
Qed.

Example set_cost_client {K} (E : encoding K) k (s : FinSet.t K) :
  Cost.ticks (FinSet.mem_c E k s) = Cost.ticks (FinSet.add_c E k s).
Proof.
  rewrite FinSet.mem_cost, FinSet.add_cost. reflexivity.
Qed.

Example primitive_empty_counts :
  (Cost.ticks (Map.mem_c nat_encoding 0 (@Map.empty nat nat)),
    Cost.ticks (FinSet.mem_c nat_encoding 0 FinSet.empty),
    Cost.ticks (FinSet.add_c nat_encoding 0 FinSet.empty)) = (3, 3, 3)%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example intern_allocation_counts :
  (Cost.ticks (Intern.intern_c nat_encoding 0 Intern.empty),
    Cost.ticks (Intern.intern_c nat_encoding 0
      (Intern.of_list nat_encoding [0])),
    Cost.ticks (Intern.of_list_c nat_encoding [])) = (9, 3, 0)%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example dense_bits_client {K} (E : encoding K) (HE : encoding_laws E)
    k i (s : Intern.t K) :
  Intern.wf E s -> Intern.find E k s = Some i ->
  (key_bits positive_encoding i <=
    N.pos (Pos.size (Pos.of_succ_nat (Intern.size s))))%N.
Proof.
  apply (InternCost.dense_id_bits E HE).
Qed.

Example dense_boundary_bits :
  (key_bits positive_encoding 1%positive, key_bits positive_encoding 2%positive,
    key_bits positive_encoding 3%positive, key_bits positive_encoding 4%positive) =
    (1, 2, 2, 3)%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example intern_list_tick_count :
  Cost.ticks (Intern.of_list_c nat_encoding [2; 1; 2]) = 30%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example intern_numeric_bound_client :
  (Cost.ticks (Intern.of_list_c nat_encoding [2; 1; 2]%nat) <= 42)%N.
Proof.
  apply (InternCost.of_list_cost Map.cost_laws_hold nat_encoding [2; 1; 2] 1 2).
  intros k [Heq|[Heq|[Heq|Hfalse]]]; try contradiction; subst k;
    vm_compute; split; discriminate.
Qed.

Example intern_missing_lookup_ticks :
  (Intern.find nat_encoding 4 (Intern.of_list nat_encoding [2; 1; 2]),
    Cost.ticks (Intern.find_c nat_encoding 4 (Intern.of_list nat_encoding [2; 1; 2]))) =
    (None, 5%N).
Proof.
  vm_compute. reflexivity.
Qed.

Example intern_forward_cardinality_client {K} (s : Intern.t K) :
  Intern.size s = Map.size (Intern.table s).
Proof.
  apply Intern.size_equation.
Qed.
