(** * Interning cost clients

    Primitive equations expose lookup and allocation charges to clients.
    For example, a repeated key pays just its forward lookup.
    Builds on: BaseIntern, BaseMap and BaseSet. *)

From Stdlib Require Import List NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet BaseIntern.
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
