(** * Constructor inventories and checked certificates

    Inventories select full constructor slots, and certificates unfold through earlier entries.
    For example, shared children contribute their tree cost each time they occur, while a
    forward reference is rejected before costing.
    Builds on: Extract, Database and Index code towers. *)

From Stdlib Require Import List PArith NArith Arith Lia.
From Argent Require Import Time.
From Galois.Base Require Import Trie HeapSig Heap.
From Galois.Egglog Require Import ValueSig Syntax IndexSig DatabaseSig Index Database ExtractSig
  Extract.

Import List.ListNotations.

Module InventoryValue <: VALUE.
  Definition t := positive.
  Definition eqb := Pos.eqb.
  Definition encode (p : positive) := p.
  Definition prim (_ : positive) (_ : list positive) : option positive := None.
  Definition merge (_ : positive) := Pos.max.
  Definition bits (v : t) := Pos.size_nat (encode v).
  Lemma encode_inj : forall a b, encode a = encode b -> a = b.
  Proof.
    intros a b Heq. exact Heq.
  Qed.
  Lemma eqb_spec : forall a b, reflect (a = b) (eqb a b).
  Proof.
    apply Pos.eqb_spec.
  Qed.
  Lemma merge_comm : forall m a b, merge m a b = merge m b a.
  Proof.
    intros m a b. apply Pos.max_comm.
  Qed.
  Lemma merge_assoc : forall m a b c, merge m a (merge m b c) = merge m (merge m a b) c.
  Proof.
    intros m a b c. apply Pos.max_assoc.
  Qed.
  Lemma merge_idem : forall m a, merge m a a = a.
  Proof.
    intros m a. apply Pos.max_id.
  Qed.
End InventoryValue.

Module InventoryIndex := IndexCode InventoryValue.
Module InventoryDatabase := DatabaseCode InventoryValue InventoryIndex.

Module InventoryMeasuredIndex := Index InventoryValue.
Module InventoryMeasuredDatabase := Database InventoryValue InventoryMeasuredIndex.
Module InventoryRows :=
  ConstructorRows InventoryValue InventoryMeasuredIndex InventoryMeasuredDatabase.

Module InventoryCost <: COST_OPS InventoryValue.
  Definition fn_cost (_ : positive) (cs : list N) := N.succ (fold_right N.add 0%N cs).
  Definition val_cost (_ : positive) := 1%N.
End InventoryCost.

Module InventoryExtract :=
  ExtractCode InventoryValue InventoryIndex InventoryDatabase InventoryCost HeapCode.

(** A nullary alternative seeds a class that also contains a self cycle. *)
Definition cheapest_cycle_database : InventoryDatabase.t :=
  let db := InventoryDatabase.init
    [Decl 10%positive [SVal] OId; Decl 20%positive [] OId; Decl 30%positive [SId] OId]
    [(10%positive, [0; 1]); (20%positive, [0]); (30%positive, [0; 1])] in
  let db := snd (InventoryDatabase.make 10%positive [Val 7%positive] db) in
  let db := snd (InventoryDatabase.make 20%positive [] db) in
  let db := snd (InventoryDatabase.make 30%positive [Id 1%positive] db) in
  InventoryDatabase.rebuild
    (InventoryDatabase.union 1%positive 2%positive
      (InventoryDatabase.union 1%positive 3%positive db)).

Definition cheapest_cycle_inventory : list (positive * (N * nat)) :=
  [(10%positive, (0%N, 1)); (20%positive, (1%N, 0)); (30%positive, (2%N, 1))].

Example best_cheapest_alternative_in_cycle :
  InventoryExtract.best cheapest_cycle_inventory cheapest_cycle_database =
    [(1%positive, (1%N, (20%positive, [])))].
Proof.
  vm_compute. reflexivity.
Qed.

Example extract_cheapest_finite_cycle_witness :
  InventoryExtract.extract cheapest_cycle_inventory cheapest_cycle_database 1%positive =
    Some [(1%positive, (20%positive, []))].
Proof.
  vm_compute. reflexivity.
Qed.

Example extract_noncanonical_root_is_rejected :
  InventoryExtract.extract cheapest_cycle_inventory cheapest_cycle_database 3%positive = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example best_pure_cycle_has_no_finite_witness :
  InventoryExtract.best_rows tt [(30%positive, [Id 1%positive], 1%positive)] = [].
Proof.
  vm_compute. reflexivity.
Qed.

Example best_repeated_waiting_child :
  InventoryExtract.best_rows tt
    [(20%positive, [Id 1%positive; Id 1%positive], 2%positive);
     (10%positive, [Val 7%positive], 1%positive)] =
    [(2%positive, (5%N, (20%positive, [Id 1%positive; Id 1%positive])));
     (1%positive, (2%N, (10%positive, [Val 7%positive])))].
Proof.
  vm_compute. reflexivity.
Qed.

Example best_decrease_keeps_cheapest_candidate :
  InventoryExtract.best_rows tt
    [(10%positive, [Val 7%positive], 1%positive);
     (20%positive, [], 1%positive)] =
    [(1%positive, (1%N, (20%positive, [])))].
Proof.
  vm_compute. reflexivity.
Qed.

Example best_equal_cost_preserves_first_candidate :
  InventoryExtract.best_rows tt
    [(10%positive, [], 1%positive); (20%positive, [], 1%positive)] =
    [(1%positive, (1%N, (10%positive, [])))].
Proof.
  vm_compute. reflexivity.
Qed.

Module ZeroCost <: COST_OPS InventoryValue.
  Definition fn_cost (_ : positive) (cs : list N) := fold_right N.max 0%N cs.
  Definition val_cost (_ : positive) := 0%N.
End ZeroCost.

Module ZeroSearch := SearchCode InventoryValue ZeroCost HeapCode.

Example best_zero_cost_cycle_uses_finite_seed :
  ZeroSearch.best_rows tt
    [(30%positive, [Id 1%positive], 1%positive); (20%positive, [], 1%positive)] =
    [(1%positive, (0%N, (20%positive, [])))].
Proof.
  vm_compute. reflexivity.
Qed.

Example inventory_full_slots_only :
  InventoryExtract.inventory
    [Decl 3%positive [SId; SVal] OId; Decl 4%positive [] ORel;
     Decl 3%positive [] ORel; Decl 5%positive [] OId; Decl 6%positive [] (OLat 1%positive)]
    [(3%positive, [0; 2; 1]); (4%positive, []); (3%positive, [0; 1; 2]);
     (5%positive, [0]); (3%positive, [0; 1; 2]); (99%positive, [0])] =
    [(3%positive, (2%N, 2)); (5%positive, (3%N, 0))].
Proof.
  vm_compute. reflexivity.
Qed.

Example inventory_first_declaration_wins :
  InventoryExtract.inventory [Decl 3%positive [] ORel; Decl 3%positive [] OId]
    [(3%positive, [0])] = [].
Proof.
  vm_compute. reflexivity.
Qed.

Example inventory_matching_arity :
  InventoryExtract.inventory [Decl 3%positive [SVal] OId]
    [(3%positive, [0]); (3%positive, [0; 1; 2]); (3%positive, [0; 1])] =
    [(3%positive, (2%N, 1))].
Proof.
  vm_compute. reflexivity.
Qed.

Example inventory_empty_layout :
  InventoryExtract.inventory [Decl 3%positive [SVal] OId] [] = [].
Proof.
  vm_compute. reflexivity.
Qed.

Example unfold_shared_children :
  dag_unfold [(1%positive, (10%positive, [Val 7%positive]));
    (2%positive, (20%positive, [Id 1%positive; Id 1%positive]))] 2%positive =
    Some (Model.EApp 20%positive
      [Model.EApp 10%positive [Model.ELit 7%positive];
       Model.EApp 10%positive [Model.ELit 7%positive]]).
Proof.
  vm_compute. reflexivity.
Qed.

Example unfold_forward_reference :
  @dag_unfold positive
    [(1%positive, (10%positive, [Id 2%positive])); (2%positive, (20%positive, []))]
    1%positive = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example unfold_self_reference :
  @dag_unfold positive [(1%positive, (10%positive, [Id 1%positive]))] 1%positive = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example unfold_independent_root :
  @dag_unfold positive
    [(1%positive, (10%positive, [Id 1%positive])); (2%positive, (20%positive, []))]
    2%positive = Some (Model.EApp 20%positive []).
Proof.
  vm_compute. reflexivity.
Qed.

Example unfold_missing_root :
  @dag_unfold positive [(1%positive, (10%positive, []))] 2%positive = None.
Proof.
  vm_compute. reflexivity.
Qed.

Definition checker_database : InventoryDatabase.t :=
  let db := InventoryDatabase.init
    [Decl 10%positive [SVal] OId; Decl 20%positive [SId; SId] OId;
     Decl 30%positive [] OId]
    [(10%positive, [0; 1]); (20%positive, [0; 1; 2]); (30%positive, [0])] in
  let db := snd (InventoryDatabase.make 10%positive [Val 7%positive] db) in
  let db := snd (InventoryDatabase.make 20%positive [Id 1%positive; Id 1%positive] db) in
  snd (InventoryDatabase.make 30%positive [] db).

Definition checker_graph : extraction_dag positive :=
  [(1%positive, (10%positive, [Val 7%positive]));
   (2%positive, (20%positive, [Id 1%positive; Id 1%positive]));
   (3%positive, (30%positive, []))].

Example check_dag_shared_children :
  InventoryExtract.check_dag checker_database 2%positive checker_graph = Some 5%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example check_dag_root_before_unrelated_rows :
  InventoryExtract.check_dag checker_database 1%positive checker_graph = Some 2%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example check_dag_unrelated_invalid_row :
  InventoryExtract.check_dag checker_database 2%positive
    (checker_graph ++ [(4%positive, (99%positive, []))]) = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example check_dag_forward_child :
  InventoryExtract.check_dag checker_database 2%positive
    [(2%positive, (20%positive, [Id 1%positive; Id 1%positive]));
     (1%positive, (10%positive, [Val 7%positive]))] = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example check_dag_duplicate_name :
  InventoryExtract.check_dag checker_database 1%positive
    [(1%positive, (10%positive, [Val 7%positive]));
     (1%positive, (10%positive, [Val 7%positive]))] = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example check_dag_wrong_output :
  InventoryExtract.check_dag checker_database 2%positive
    [(2%positive, (10%positive, [Val 7%positive]))] = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example check_dag_missing_root :
  InventoryExtract.check_dag checker_database 4%positive checker_graph = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example check_dag_empty :
  InventoryExtract.check_dag checker_database 1%positive [] = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example dag_needed_excludes_unrelated_rows :
  dag_seen (dag_needed checker_graph (PTrieCode.set 1%positive tt Empty)) 2%positive = false.
Proof.
  vm_compute. reflexivity.
Qed.


Example index_paths_single_tuple :
  let ix := InventoryIndex.insert [Id 2%positive; Val 7%positive] InventoryIndex.empty in
  index_paths (InventoryIndex.child ix) (InventoryIndex.children ix) 2
    (InventoryIndex.root ix) = [[Id 2%positive; Val 7%positive]].
Proof.
  vm_compute. reflexivity.
Qed.

Example index_paths_empty_positive_depth :
  index_paths (InventoryIndex.child InventoryIndex.empty)
    (InventoryIndex.children InventoryIndex.empty) 1
    (InventoryIndex.root InventoryIndex.empty) = [].
Proof.
  vm_compute. reflexivity.
Qed.

Example constructor_rows_count :
  length (InventoryRows.rows checker_database) = 3.
Proof.
  vm_compute. reflexivity.
Qed.

Example constructor_rows_maximum_arity :
  InventoryRows.maximum_arity (InventoryRows.rows checker_database) = 2.
Proof.
  vm_compute. reflexivity.
Qed.

Example constructor_rows_deduplicate_full_and_partial_slots :
  let db := InventoryDatabase.init [Decl 30%positive [] OId]
    [(30%positive, [0]); (30%positive, [0]); (30%positive, [])] in
  let db := snd (InventoryDatabase.make 30%positive [] db) in
  (length (InventoryRows.rows db), InventoryRows.maximum_arity (InventoryRows.rows db)) = (1, 0).
Proof.
  vm_compute. reflexivity.
Qed.

Example constructor_rows_empty :
  InventoryRows.rows (InventoryDatabase.init [] []) = [].
Proof.
  vm_compute. reflexivity.
Qed.

Definition candidate_entries : extraction_best positive :=
  [(3%positive, (1%N, (30%positive, [])));
   (2%positive, (5%N, (20%positive, [Id 1%positive; Id 1%positive])));
   (1%positive, (2%N, (10%positive, [Val 7%positive])))].

Example extraction_candidate_accepts_shared_tree :
  extraction_candidate (InventoryExtract.check_dag checker_database)
    2%positive 2%positive candidate_entries = Some checker_graph.
Proof.
  vm_compute. reflexivity.
Qed.

Example extraction_candidate_checks_budget :
  extraction_candidate (InventoryExtract.check_dag checker_database)
    2%positive 2%positive
    [(2%positive, (4%N, (20%positive, [Id 1%positive; Id 1%positive])));
     (1%positive, (2%N, (10%positive, [Val 7%positive])))] = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example extraction_candidate_rejects_missing_root :
  extraction_candidate (InventoryExtract.check_dag checker_database)
    4%positive 4%positive candidate_entries = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example extraction_candidate_rejects_cycle :
  extraction_candidate (fun c g => dag_check (fun _ _ _ => true)
    InventoryCost.fn_cost InventoryCost.val_cost g c)
    1%positive 1%positive [(1%positive, (0%N, (10%positive, [Id 1%positive])))] = None.
Proof.
  vm_compute. reflexivity.
Qed.

(** The public index laws remain valid when its next counter is constantly one. *)
Module ConstantNextIndex (V : VALUE) (I : INDEX V) <: INDEX V.
  Definition t := I.t.
  Definition empty := I.empty.
  Definition insert := I.insert.
  Definition remove := I.remove.
  Definition next (_ : t) := 1%positive.
  Definition root := I.root.
  Definition child := I.child.
  Definition children := I.children.
  Definition degree := I.degree.
  Definition wf := I.wf.
  Definition mem := I.mem.
  Definition node := I.node.
  Definition next_empty : next empty = 1%positive := eq_refl.
  Lemma next_insert : forall a r ix, wf a ix ->
    (next (insert r ix) <= next ix + Pos.of_nat (length r))%positive.
  Proof.
    intros a r ix Hwf. unfold next. lia.
  Qed.
  Lemma next_remove : forall a r ix, wf a ix -> next (remove r ix) = next ix.
  Proof.
    reflexivity.
  Qed.
  Definition wf_empty := I.wf_empty.
  Definition mem_empty := I.mem_empty.
  Definition wf_insert := I.wf_insert.
  Definition wf_remove := I.wf_remove.
  Definition mem_insert := I.mem_insert.
  Definition mem_remove := I.mem_remove.
  Definition mem_arity := I.mem_arity.
  Definition node_root := I.node_root.
  Definition node_live := I.node_live.
  Definition node_fun := I.node_fun.
  Definition child_spec := I.child_spec.
  Definition children_spec := I.children_spec.
  Definition degree_spec := I.degree_spec.
End ConstantNextIndex.

(** A stored tuple may be deeper than the next counter under the published index interface. *)
Module IndexFuelCounterexample (V : VALUE) (I : INDEX V).
  Module C := ConstantNextIndex V I.
  Lemma next_does_not_bound_stored_arity : forall v : V.t,
    exists ix, C.wf 2 ix /\ C.mem ix [Val v; Val v] /\
      Pos.to_nat (C.next ix) < length [Val v; Val v].
  Proof.
    intro v. exists (C.insert [Val v; Val v] C.empty). split.
    - apply (C.wf_insert 2 [Val v; Val v] C.empty (C.wf_empty 2) eq_refl).
    - split.
      + apply (proj2 (C.mem_insert 2 [Val v; Val v] C.empty [Val v; Val v]
          (C.wf_empty 2) eq_refl)). now left.
      + change (1 < 2). lia.
  Qed.
End IndexFuelCounterexample.

(** Ghost queue potentials have no clock operation in the published timed queue interface. *)
Module GhostQueueClockProbe (Q : PQ_T).
  Definition potential_probe (q : Q.t) : N := Q.phi 1 1 q.
  TimeFunFails "E_OPAQUE" potential_probe.
End GhostQueueClockProbe.

(** The ghost row enumerator depends on observations with no published clock operations. *)
Module GhostDatabaseClockProbe (V : VALUE_T) (I : INDEX_T V) (D : DATABASE_T V I).
  Definition slots_probe (db : D.t) := D.slots db.
  TimeFunFails "E_OPAQUE" slots_probe.
  Definition old_probe (db : D.t) f k := D.old db f k.
  TimeFunFails "E_OPAQUE" old_probe.
End GhostDatabaseClockProbe.
