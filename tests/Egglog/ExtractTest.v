(** * Constructor inventories and checked certificates

    Inventories select full constructor slots, and certificates unfold through earlier entries.
    For example, shared children contribute their tree cost each time they occur, while a
    forward reference is rejected before costing.
    Builds on: Extract, Database and Index code towers.

    Groups:
    - CycleTests: the cheapest finite alternative breaks a cycle.
    - BestRowsTests: the best row of each candidate, and a zero-cost search.
    - InventoryTests: the inventory keeps the full constructor slots of the declared arity.
    - UnfoldTests: a DAG unfolds through earlier entries only.
    - CheckerTests: a certificate DAG is accepted only when every entry is valid.
    - IndexPathTests: index paths of stored tuples.
    - RowTests: the constructor rows of a database.
    - CandidateTests: an extraction candidate is checked against its budget and root.
    - CodedTests: the coded extraction state of a row.
    - Probes: the index interface and the timed queue and database observations. *)

From Stdlib Require Import List PArith NArith Arith Lia.
From Argent Require Import Time.
From Galois.Base Require Import Trie HeapSig Heap.
From Galois.Egglog Require Import ValueSig Syntax IndexSig DatabaseSig Index Database ExtractSig
  Extract.

Import List.ListNotations.

(** * Fixtures *)

(** A value type of positive numbers, merged by maximum. *)
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

(** Each constructor costs one more than the sum of its children, and a value costs one. *)
Module InventoryCost <: COST_OPS InventoryValue.
  Definition fn_cost (_ : positive) (cs : list N) := N.succ (fold_right N.add 0%N cs).
  Definition val_cost (_ : positive) := 1%N.
End InventoryCost.

Module InventoryExtract :=
  ExtractCode InventoryValue InventoryIndex InventoryDatabase InventoryCost HeapCode.

(** A database with a nullary alternative that also contains a self cycle. *)
Definition checker_database : InventoryDatabase.t :=
  let db := InventoryDatabase.init
    [Decl 10%positive [SVal] OId; Decl 20%positive [SId; SId] OId;
     Decl 30%positive [] OId]
    [(10%positive, [0; 1]); (20%positive, [0; 1; 2]); (30%positive, [0])] in
  let db := snd (InventoryDatabase.make 10%positive [Val 7%positive] db) in
  let db := snd (InventoryDatabase.make 20%positive [Id 1%positive; Id 1%positive] db) in
  snd (InventoryDatabase.make 30%positive [] db).

(** A DAG of three entries: a literal, a constructor with a shared child, and a nullary one. *)
Definition checker_graph : extraction_dag positive :=
  [(1%positive, (10%positive, [Val 7%positive]));
   (2%positive, (20%positive, [Id 1%positive; Id 1%positive]));
   (3%positive, (30%positive, []))].

Module CycleTests.

  (** A class that holds a nullary alternative and a self cycle is cycled through. *)
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

  (** The inventory of the cycle database, with costs and arities for each constructor. *)
  Definition cheapest_cycle_inventory : list (positive * (N * nat)) :=
    [(10%positive, (0%N, 1)); (20%positive, (1%N, 0)); (30%positive, (2%N, 1))].

  (** The best row of the cycle is the cheapest finite alternative, the nullary constructor. *)
  Example best_picks_cheapest_alternative :
    InventoryExtract.best cheapest_cycle_inventory cheapest_cycle_database =
      [(1%positive, (1%N, (20%positive, [])))].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Extraction of the cycle class returns the finite witness of the cheapest alternative. *)
  Example extract_returns_cheapest_witness :
    InventoryExtract.extract cheapest_cycle_inventory cheapest_cycle_database 1%positive =
      Some [(1%positive, (20%positive, []))].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A root that is not the canonical identifier of its class has no extraction. *)
  Example extract_rejects_noncanonical_root :
    InventoryExtract.extract cheapest_cycle_inventory cheapest_cycle_database 3%positive = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A row that only refers to itself gives no finite best row. *)
  Example pure_cycle_has_no_finite_row :
    InventoryExtract.best_rows tt [(30%positive, [Id 1%positive], 1%positive)] = [].
  Proof.
    vm_compute. reflexivity.
  Qed.

End CycleTests.

Module BestRowsTests.

  Local Open Scope positive_scope.

  (** A child that occurs twice adds its cost once for each occurrence. *)
  Example repeated_child_counted_per_occurrence :
    InventoryExtract.best_rows tt
      [(20, [Id 1; Id 1], 2);
       (10, [Val 7], 1)] =
      [(2, (5%N, (20, [Id 1; Id 1])));
       (1, (2%N, (10, [Val 7])))].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A later row with a lower cost replaces the first candidate of its class. *)
  Example cheaper_later_row_replaces_first :
    InventoryExtract.best_rows tt
      [(10, [Val 7], 1);
       (20, [], 1)] =
      [(1, (1%N, (20, [])))].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Among rows of equal cost, the first row of the class is kept. *)
  Example equal_cost_keeps_first_row :
    InventoryExtract.best_rows tt
      [(10, [], 1); (20, [], 1)] =
      [(1, (1%N, (10, [])))].
  Proof.
    vm_compute. reflexivity.
  Qed.

  Module ZeroCost <: COST_OPS InventoryValue.
    Definition fn_cost (_ : positive) (cs : list N) := fold_right N.max 0%N cs.
    Definition val_cost (_ : positive) := 0%N.
  End ZeroCost.

  Module ZeroSearch := SearchCode InventoryValue ZeroCost HeapCode.

  (** With zero costs, a cycle is resolved by the finite alternative that seeds it. *)
  Example zero_cost_cycle_uses_finite_seed :
    ZeroSearch.best_rows tt
      [(30, [Id 1], 1); (20, [], 1)] =
      [(1, (0%N, (20, [])))].
  Proof.
    vm_compute. reflexivity.
  Qed.

End BestRowsTests.

Module InventoryTests.

  (** Only the full constructor slots of the declared arity enter the inventory. *)
  Example keeps_only_full_slots :
    InventoryExtract.inventory
      [Decl 3%positive [SId; SVal] OId; Decl 4%positive [] ORel;
       Decl 3%positive [] ORel; Decl 5%positive [] OId; Decl 6%positive [] (OLat 1%positive)]
      [(3%positive, [0; 2; 1]); (4%positive, []); (3%positive, [0; 1; 2]);
       (5%positive, [0]); (3%positive, [0; 1; 2]); (99%positive, [0])] =
      [(3%positive, (2%N, 2)); (5%positive, (3%N, 0))].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A duplicate declaration of a relation with another kind makes the inventory empty. *)
  Example first_declaration_wins :
    InventoryExtract.inventory [Decl 3%positive [] ORel; Decl 3%positive [] OId]
      [(3%positive, [0])] = [].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Rows whose length differs from the declared arity are left out. *)
  Example keeps_rows_of_declared_arity :
    InventoryExtract.inventory [Decl 3%positive [SVal] OId]
      [(3%positive, [0]); (3%positive, [0; 1; 2]); (3%positive, [0; 1])] =
      [(3%positive, (2%N, 1))].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An empty layout gives an empty inventory. *)
  Example empty_layout_gives_empty_inventory :
    InventoryExtract.inventory [Decl 3%positive [SVal] OId] [] = [].
  Proof.
    vm_compute. reflexivity.
  Qed.

End InventoryTests.

Module UnfoldTests.

  Local Open Scope positive_scope.

  (** A shared child unfolds into a copy of its tree at each occurrence. *)
  Example shared_children_unfold_each_occurrence :
    dag_unfold [(1, (10, [Val 7]));
      (2, (20, [Id 1; Id 1]))] 2 =
      Some (Model.EApp 20
        [Model.EApp 10 [Model.ELit 7];
         Model.EApp 10 [Model.ELit 7]]).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A child that refers to a later entry makes the unfolding fail. *)
  Example forward_reference_fails :
    @dag_unfold positive
      [(1, (10, [Id 2])); (2, (20, []))]
      1 = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An entry that refers to itself makes the unfolding fail. *)
  Example self_reference_fails :
    @dag_unfold positive [(1, (10, [Id 1]))] 1 = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An entry that does not depend on a cyclic entry unfolds on its own. *)
  Example independent_root_unfolds_alone :
    @dag_unfold positive
      [(1, (10, [Id 1])); (2, (20, []))]
      2 = Some (Model.EApp 20 []).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A root that is not in the DAG has no unfolding. *)
  Example missing_root_fails :
    @dag_unfold positive [(1, (10, []))] 2 = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

End UnfoldTests.

Module CheckerTests.

  Local Open Scope positive_scope.

  (** The cost of a root counts a shared child once for each of its occurrences. *)
  Example shared_children_count_per_occurrence :
    InventoryExtract.check_dag checker_database 2 checker_graph = Some 5%N.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A root's cost does not depend on rows after it in the DAG. *)
  Example root_cost_ignores_later_rows :
    InventoryExtract.check_dag checker_database 1 checker_graph = Some 2%N.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** One invalid row in the DAG rejects the whole certificate, even when it is unrelated. *)
  Example invalid_unrelated_row_rejects_graph :
    InventoryExtract.check_dag checker_database 2
      (checker_graph ++ [(4, (99, []))]) = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A child that refers to a later row is rejected. *)
  Example forward_child_rejected :
    InventoryExtract.check_dag checker_database 2
      [(2, (20, [Id 1; Id 1]));
       (1, (10, [Val 7]))] = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Two rows with the same name are rejected. *)
  Example duplicate_name_rejected :
    InventoryExtract.check_dag checker_database 1
      [(1, (10, [Val 7]));
       (1, (10, [Val 7]))] = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A row whose constructor does not match the database's output is rejected. *)
  Example wrong_output_rejected :
    InventoryExtract.check_dag checker_database 2
      [(2, (10, [Val 7]))] = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A root that the DAG does not contain is rejected. *)
  Example missing_root_rejected :
    InventoryExtract.check_dag checker_database 4 checker_graph = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An empty DAG is rejected. *)
  Example empty_graph_rejected :
    InventoryExtract.check_dag checker_database 1 [] = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Rows that the root does not need are not marked as needed. *)
  Example unrelated_row_not_needed :
    dag_seen (dag_needed checker_graph (PTrieCode.set 1 tt Empty)) 2 = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

End CheckerTests.

Module IndexPathTests.

  (** The path of a stored tuple of depth two is that tuple. *)
  Example single_tuple_path :
    let ix := InventoryIndex.insert [Id 2%positive; Val 7%positive] InventoryIndex.empty in
    index_paths (InventoryIndex.child ix) (InventoryIndex.children ix) 2
      (InventoryIndex.root ix) = [[Id 2%positive; Val 7%positive]].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An empty index has no path, even at depth one. *)
  Example empty_index_has_no_path :
    index_paths (InventoryIndex.child InventoryIndex.empty)
      (InventoryIndex.children InventoryIndex.empty) 1
      (InventoryIndex.root InventoryIndex.empty) = [].
  Proof.
    vm_compute. reflexivity.
  Qed.

End IndexPathTests.

Module RowTests.

  (** Each stored tuple of the checker database gives one constructor row. *)
  Example one_row_per_stored_tuple :
    length (InventoryRows.rows checker_database) = 3.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The maximum arity is the number of children of the widest row. *)
  Example maximum_arity_is_widest_row :
    InventoryRows.maximum_arity (InventoryRows.rows checker_database) = 2.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Duplicate and partial slots of one constructor collapse into a single row. *)
  Definition dedup_database : InventoryDatabase.t :=
    snd (InventoryDatabase.make 30%positive []
      (InventoryDatabase.init [Decl 30%positive [] OId]
        [(30%positive, [0]); (30%positive, [0]); (30%positive, [])])).

  (** The deduplicated constructor has one row. *)
  Example deduplicated_rows_count :
    length (InventoryRows.rows dedup_database) = 1.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The one remaining row has no children, so the maximum arity is zero. *)
  Example deduplicated_rows_maximum_arity :
    InventoryRows.maximum_arity (InventoryRows.rows dedup_database) = 0.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A database with no declarations has no constructor rows. *)
  Example no_rows_for_empty_database :
    InventoryRows.rows (InventoryDatabase.init [] []) = [].
  Proof.
    vm_compute. reflexivity.
  Qed.

End RowTests.

Module CandidateTests.

  Local Open Scope positive_scope.

  (** The candidate entries of a shared tree, with a budget for each entry. *)
  Definition candidate_entries : extraction_best positive :=
    [(3, (1%N, (30, [])));
     (2, (5%N, (20, [Id 1; Id 1])));
     (1, (2%N, (10, [Val 7])))].

  (** A candidate for a shared tree within its budget is accepted as the checker graph. *)
  Example shared_tree_candidate_accepted :
    extraction_candidate (InventoryExtract.check_dag checker_database)
      2 2 candidate_entries = Some checker_graph.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A candidate whose budget is below the cost of its root is rejected. *)
  Example candidate_over_budget_rejected :
    extraction_candidate (InventoryExtract.check_dag checker_database)
      2 2
      [(2, (4%N, (20, [Id 1; Id 1])));
       (1, (2%N, (10, [Val 7])))] = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A candidate without the requested root is rejected. *)
  Example missing_root_candidate_rejected :
    extraction_candidate (InventoryExtract.check_dag checker_database)
      4 4 candidate_entries = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A candidate whose entries form a cycle is rejected. *)
  Example cyclic_candidate_rejected :
    extraction_candidate (fun c g => dag_check (fun _ _ _ => true)
      InventoryCost.fn_cost InventoryCost.val_cost g c)
      1 1 [(1, (0%N, (10, [Id 1])))] = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

End CandidateTests.

Module CodedTests.

  (** The rows of a coded extraction, with the number of the row that is not yet extracted. *)
  Definition coded_source_rows : list (search_row positive) :=
    [(3%positive, [Id 2%positive; Val 7%positive; Id 2%positive; Id 5%positive], 9%positive);
     (4%positive, [Val 7%positive], 10%positive);
     (6%positive, [], 11%positive)].

  (** The extraction state that holds the coded source rows. *)
  Definition coded_observer_state : extraction_state positive unit unit :=
    ExtractionState tt coded_source_rows 3 Empty Empty Empty tt [].

  (** Row children keep each child identifier, including repeated ones. *)
  Example children_keep_repeated_identifiers :
    extraction_row_children (extraction_row_code (fun p : positive => p)
      (3%positive, [Id 2%positive; Val 7%positive; Id 2%positive; Id 5%positive], 9%positive)) =
      [2%positive; 2%positive; 5%positive].
  Proof. vm_compute. reflexivity. Qed.

  (** The counter counts each unfinished child occurrence of a row. *)
  Example counter_counts_unfinished_occurrences :
    extraction_row_counter coded_observer_state (extraction_row_code (fun p : positive => p)
      (3%positive, [Id 2%positive; Val 7%positive; Id 2%positive; Id 5%positive], 9%positive)) = 3.
  Proof. vm_compute. reflexivity. Qed.

  (** Rows with literal or nullary children are ready with their costs. *)
  Example ready_rows_include_literal_and_nullary :
    extraction_ready_rows (fun p : positive => p) InventoryCost.fn_cost InventoryCost.val_cost
      coded_observer_state =
      [(extraction_row_code (fun p : positive => p) (4%positive, [Val 7%positive], 10%positive),
         2%N);
       (extraction_row_code (fun p : positive => p) (6%positive, [], 11%positive), 1%N)].
  Proof. vm_compute. reflexivity. Qed.

End CodedTests.

(** * Index interface probes *)

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

(** * Clock probes *)

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
