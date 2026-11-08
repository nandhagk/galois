(** * Exact raw-checker agreement clients

    The charged checker is compared directly with the fixed reference checker.
    For example, both checkers reject the same cyclic candidate.
    Builds on: GraphCheckDomCost and hand-written GraphFixtures. *)

From Stdlib Require Import List Bool PArith NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Graph Require Import GraphModel GraphPrepared GraphDomSpec GraphFixtures
  GraphCheckDom GraphCheckDomCost GraphReach GraphVisitor.
Import List.ListNotations Cost.Notations.
Open Scope positive_scope.

Example symbolic_raw_check_client {V E} (p : Prepared.t V E) m :
  Cost.value (DomCheckCost.check_c p m) = DomCheck.check p m.
Proof.
  apply DomCheckCost.check_c_value.
Qed.

Example checked_line :
  Cost.value (DomCheckCost.check_c Fixtures.Line.prepared Fixtures.Line.parents) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example checked_diamond :
  Cost.value (DomCheckCost.check_c Fixtures.Diamond.prepared Fixtures.Diamond.parents) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example checked_empty :
  Cost.value (DomCheckCost.check_c Fixtures.Empty.prepared Map.empty) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example checked_singleton :
  Cost.value (DomCheckCost.check_c Fixtures.Singleton.prepared Map.empty) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example checked_multiple_entries :
  Cost.value (DomCheckCost.check_c Fixtures.TwoEntry.prepared Fixtures.TwoEntry.parents) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejected_candidate_cycle :
  Cost.value (DomCheckCost.check_c Fixtures.Line.prepared
    (Fixtures.parents [(2, 3); (3, 2); (4, 3)])) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example zero_chain_budget :
  Cost.value (DomCheckCost.chain_c 0 Fixtures.Line.parents 4) = [4].
Proof.
  vm_compute. reflexivity.
Qed.

Example zero_termination_budget :
  Cost.value (DomCheckCost.ends_c 0 Fixtures.Line.parents 4) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example cyclic_chain_order :
  Cost.value (DomCheckCost.chain_c 4 (Fixtures.parents [(2, 3); (3, 2)]) 2) =
    [2; 3; 2; 3; 2].
Proof.
  vm_compute. reflexivity.
Qed.

Example singleton_parent_cost :
  (Cost.ticks (DomCheckCost.chain_c 0 Map.empty 1),
   Cost.ticks (DomCheckCost.ends_c 0 Map.empty 1),
   Cost.ticks (DomCheckCost.ends_c 1 Map.empty 1)) = (1, 1, 4)%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example blocked_scope_constructor_client d :
  Reach.blocked d = Scope.Make (FinSet.add positive_encoding d FinSet.empty) None.
Proof.
  apply Reach.blocked_equation.
Qed.

Example arbitrary_raw_storage_agreement :
  let m := Map.set_code 2 3 1
    (Map.set_code 3 2 2 (Map.set positive_encoding 4 3 Map.empty)) in
  (Cost.value (DomCheckCost.check_c Fixtures.Line.prepared m),
   DomCheck.check Fixtures.Line.prepared m) = (true, true).
Proof.
  vm_compute. reflexivity.
Qed.

Example chain_numeric_contract_client fuel m v w :
  DomCheckCost.parent_width m w -> (key_bits positive_encoding v <= w)%N ->
  (Cost.ticks (DomCheckCost.chain_c fuel m v) <=
    N.of_nat (S fuel) * (1 + DomCheckCost.id_get_budget w))%N.
Proof.
  apply DomCheckCost.chain_cost.
Qed.

Example termination_numeric_contract_client fuel m v w :
  DomCheckCost.parent_width m w -> (key_bits positive_encoding v <= w)%N ->
  (Cost.ticks (DomCheckCost.ends_c fuel m v) <=
    N.of_nat (S fuel) * (1 + DomCheckCost.id_get_budget w))%N.
Proof.
  apply DomCheckCost.ends_cost.
Qed.

Example ancestry_numeric_contract_client m d n w :
  DomCheckCost.parent_width m w ->
  (key_bits positive_encoding d <= w)%N -> (key_bits positive_encoding n <= w)%N ->
  (Cost.ticks (DomCheckCost.ancestor_b_c m d n) <= DomCheckCost.ancestor_budget m w)%N.
Proof.
  apply DomCheckCost.ancestor_cost.
Qed.

Example actual_checked_exact_client :
  Dom.exact Fixtures.Line.prepared
    (DomCheck.of_parents Fixtures.Line.prepared Fixtures.Line.parents).
Proof.
  apply DomCheckCost.checked_exact.
  - exact Fixtures.Line.fixture_ready.
  - exact Fixtures.Line.parents_wf.
  - vm_compute. reflexivity.
Qed.

Definition expensive_encoding :=
  Encoding (fun n : nat => Cost.tick 19 ;; encode_c nat_encoding n).

Definition expensive_line :=
  Prepared.prepare expensive_encoding (Prepared.graph Fixtures.Line.prepared).

Example supplied_encoder_does_not_change_check_value :
  Cost.value (DomCheckCost.check_c expensive_line Fixtures.Line.parents) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example every_supplied_encoding_charge_is_retained :
  Cost.ticks (DomCheckCost.check_c expensive_line Fixtures.Line.parents) =
    (Cost.ticks (DomCheckCost.check_c Fixtures.Line.prepared Fixtures.Line.parents) + 380)%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example total_checker_ticks :
  (Cost.ticks (DomCheckCost.check_c Fixtures.Line.prepared Fixtures.Line.parents),
   Cost.ticks (DomCheckCost.check_c Fixtures.Empty.prepared Fixtures.Empty.parents)) =
    (1724, 1)%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example ancestry_scan_ticks :
  (Cost.ticks (DomCheckCost.ancestor_b_c Fixtures.Line.parents 1 4),
   Cost.ticks (DomCheckCost.ancestor_b_c Fixtures.Line.parents 9 4)) = (32, 36)%N.
Proof.
  vm_compute. reflexivity.
Qed.
