(** * Incremental transition observations

    Demands solve and check missing regions, while edits remove affected stored values.
    For example, a changed constant row is recomputed after its old binding is invalidated.

    Groups:
    - [DemandTests] A demand solves the missing rows of a region, and a covered demand changes
      nothing.
    - [EditTests] An edit drops the stored values that depend on the edited row.
    - [GraphTests] Demands and edits on a graph of rows with reads, sides and moved targets.
    - [MetadataTests] The buckets and snapshots that a graph demand records.
    - [DiscoveryTests] Encoded keys, the visits that discover missing keys, and the merges after
      them.

    Builds on: Incremental, Restrict and Worklist. *)

From Stdlib Require Import List Bool Arith NArith PArith Lia.
From Argent Require Import Loop.
From Galois.Base Require Import MapSig Trie Heap.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import Query SystemSig PolicySig SolverSig CheckSig
  Policy Check Worklist.
From Galois.Incremental Require Import RestrictSig Restrict IncrementalSig Incremental.

Import List.ListNotations.

(** * Fixtures *)

(** The Boolean lattice that the witness solver uses, with its laws. *)
Module WitnessBool <: WLATTICE.
  Definition t := bool.
  Definition leb := implb.
  Definition bot := false.
  Definition is_bot := negb.
  Definition join := orb.
  Definition wparam := unit.
  Definition widen (_ : unit) := orb.
  Definition narrow := andb.
  Definition wrank (_ : unit) (_ : bool) := 0%nat.

  (** Boolean implication relates each value to itself. *)
  Lemma leb_refl : forall a, leb a a = true.
  Proof.
    intros []; reflexivity.
  Qed.

  (** Boolean implication composes. *)
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof.
    intros [] [] []; cbn; congruence.
  Qed.

  (** False is below every Boolean value. *)
  Lemma bot_least : forall a, leb bot a = true.
  Proof.
    intros []; reflexivity.
  Qed.

  (** Negation recognizes the false bottom. *)
  Lemma is_bot_bot : is_bot bot = true.
  Proof.
    reflexivity.
  Qed.

  (** Every recognized bottom is below every Boolean value. *)
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof.
    intros [] []; cbn; congruence.
  Qed.

  (** Disjunction includes its left operand. *)
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof.
    intros [] []; reflexivity.
  Qed.

  (** Disjunction includes its right operand. *)
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof.
    intros [] []; reflexivity.
  Qed.

  (** Boolean widening includes the previous value. *)
  Lemma widen_ub_l : forall p a b, leb a (widen p a b) = true.
  Proof.
    intros [] [] []; reflexivity.
  Qed.

  (** Boolean widening includes the candidate value. *)
  Lemma widen_ub_r : forall p a b, leb b (widen p a b) = true.
  Proof.
    intros [] [] []; reflexivity.
  Qed.

  (** A candidate already included by the old value does not change it. *)
  Lemma widen_stable : forall p a b, leb b a = true -> widen p a b = a.
  Proof.
    intros [] [] []; cbn; congruence.
  Qed.

  (** No strict widening step starts at the only nonbottom Boolean value. *)
  Lemma wrank_widen : forall p a b,
    is_bot a = false -> leb b a = false -> wrank p (widen p a b) < wrank p a.
  Proof.
    intros [] [] []; cbn; congruence.
  Qed.

  (** The constant rank cannot increase. *)
  Lemma wrank_widen_le : forall p a b,
    is_bot a = false -> wrank p (widen p a b) <= wrank p a.
  Proof.
    intros [] [] []; cbn; lia.
  Qed.

  (** Conjunction stays between an ordered candidate and the old value. *)
  Lemma narrow_between : forall a b, leb b a = true ->
    leb b (narrow a b) = true /\ leb (narrow a b) a = true.
  Proof.
    intros [] []; cbn; intuition congruence.
  Qed.
End WitnessBool.

(** A system with one row, one key and one target, which returns the frame's Boolean. *)
Module OneRow <: LOCAL_SYSTEM WitnessBool.
  Definition prog := bool.
  Definition key := unit.
  Definition row := unit.
  Definition frame := unit.
  Definition key_code (_ : key) := 1%positive.
  Definition key_eqb (_ _ : key) := true.
  Definition rows (_ : prog) : list row := [tt].
  Definition target (_ : prog) (_ : row) := tt.
  Definition start (p : prog) (_ : row) : query key bool frame := Ret p.
  Definition resume (_ : prog) (_ : frame) (a : bool) : query key bool frame := Ret a.
  Definition deps (_ : prog) (_ : row) : list key := [].
  Definition sides (_ : prog) (_ : row) : list key := [].
  Include SYSTEM_SPEC WitnessBool.
  Definition wf (_ : prog) : Prop := True.

  (** The singleton key type has an injective constant code. *)
  Lemma key_code_inj : forall a b, key_code a = key_code b -> a = b.
  Proof.
    intros [] [] _; reflexivity.
  Qed.

  (** All singleton keys are equal. *)
  Lemma key_eqb_spec : forall a b, reflect (a = b) (key_eqb a b).
  Proof.
    intros [] []; constructor; reflexivity.
  Qed.

  (** The one return instruction always finishes. *)
  Lemma eval_total : forall p r look,
    wf p -> In r (rows p) -> eval p r look <> None.
  Proof.
    intros p [] look _ _; discriminate.
  Qed.

  (** The return instruction ignores the lookup. *)
  Lemma reads_within : forall p r s u, wf p -> In r (rows p) ->
    (forall x, In x (deps p r) -> s x = u x) -> eval p r s = eval p r u.
  Proof.
    intros p [] s u _ _ _; reflexivity.
  Qed.

  (** The return instruction never reaches a read. *)
  Lemma asks_within : forall p r look n q acc x f, wf p -> In r (rows p) ->
    loop_fuel (eval_step (resume p) look) n (start p r, nil) = inl (q, acc) ->
    fst (peel q acc) = inr (x, f) -> In x (deps p r).
  Proof.
    intros p [] look [|n] q acc x f _ _ Hrun Hask.
    - cbn [loop_fuel start] in Hrun. injection Hrun as <- <-. discriminate Hask.
    - discriminate Hrun.
  Qed.

  (** The return instruction produces no side contribution. *)
  Lemma sides_within : forall p r look a ss x b, wf p -> In r (rows p) ->
    eval p r look = Some (a, ss) -> In (x, b) ss -> In x (sides p r).
  Proof.
    intros p [] look a ss x b _ _ Heval Hside.
    injection Heval as <- <-. contradiction.
  Qed.

  (** The empty side declaration pays for all produced side contributions. *)
  Lemma sides_count : forall p r look a ss, wf p -> In r (rows p) ->
    eval p r look = Some (a, ss) -> length ss <= length (sides p r).
  Proof.
    intros p [] look a ss _ _ Heval. injection Heval as <- <-. reflexivity.
  Qed.

  Definition row_code (_ : row) := 1%positive.
  Definition rows_of (_ : prog) (_ : key) : list row := [tt].

  (** The singleton row type has an injective constant code. *)
  Lemma row_code_inj : forall p a b, wf p -> In a (rows p) -> In b (rows p) ->
    row_code a = row_code b -> a = b.
  Proof.
    intros p [] [] _ _ _ _; reflexivity.
  Qed.

  (** The only row is exactly the only contributor to the only key. *)
  Lemma rows_of_spec : forall p x r, wf p ->
    (In r (rows_of p x) <-> In r (rows p) /\ In x (writes p r)).
  Proof.
    intros p [] [] _; cbn [rows_of rows writes target sides]; tauto.
  Qed.
End OneRow.

Module RestrictionWitness := Restrict WitnessBool OneRow.

Module PolicyWitness := PolicyCode WitnessBool.
Module SolverWitness :=
  WorklistCode WitnessBool RestrictionWitness.RS PolicyWitness HeapCode.
Module CheckerWitness := CheckCode WitnessBool OneRow.

(** The incremental solver on the witness system. *)
Module IncWitness.
  Include IncrementalCode WitnessBool OneRow RestrictionWitness.RS
    RestrictionWitness.Impl SolverWitness CheckerWitness.
  Include INCREMENTAL_SPEC WitnessBool OneRow RestrictionWitness.RS
    RestrictionWitness.Impl SolverWitness CheckerWitness.
End IncWitness.

(** A policy with no heads and no delays. *)
Definition witness_flat : policy unit :=
  Policy unit PTrieCode.empty PTrieCode.empty tt 0.

(** A state that stores the given Boolean for the one key. *)
Definition singleton_value (v : bool) : IncWitness.state :=
  {| inc_values := PTrieCode.set 1%positive (tt, v) PTrieCode.empty;
     inc_influence := PTrieCode.empty;
     inc_cowrites := PTrieCode.empty;
     inc_snapshots := PTrieCode.empty |}.

(** A state that stores false for the one key. *)
Definition one_false : IncWitness.state := singleton_value false.

(** * Demand *)

Module DemandTests.

  (** Empty demands finish without any fuel. *)
  Example empty_demand_is_done :
    fst (IncWitness.demand false witness_flat [] 0%N IncWitness.init) = Done.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Empty demands leave the initial state unchanged. *)
  Example empty_demand_keeps_init_state :
    snd (IncWitness.demand false witness_flat [] 0%N IncWitness.init) = IncWitness.init.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The initial state has no value for the key. *)
  Example init_lookup_is_absent : IncWitness.value IncWitness.init tt = None.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A stored bottom looks up as Some false. *)
  Example stored_false_lookup_is_some_false : IncWitness.value one_false tt = Some false.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A stored nonbottom value looks up as Some true. *)
  Example stored_true_lookup_is_some_true :
    IncWitness.value (singleton_value true) tt = Some true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Covered roots finish at once, before inspecting the program, the policy or the fuel. *)
  Example covered_demand_is_done :
    fst (IncWitness.demand true witness_flat [tt; tt] 0%N one_false) = Done.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Covered roots return the original state. *)
  Example covered_demand_keeps_state :
    snd (IncWitness.demand true witness_flat [tt; tt] 0%N one_false) = one_false.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A missing root with zero fuel runs out of fuel. *)
  Example missing_demand_is_out_of_fuel :
    fst (IncWitness.demand true witness_flat [tt] 0%N IncWitness.init) = DemandOutOfFuel.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A missing root with zero fuel leaves the old state unchanged. *)
  Example missing_demand_keeps_init_state :
    snd (IncWitness.demand true witness_flat [tt] 0%N IncWitness.init) = IncWitness.init.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The restricted worklist computes the constant row as true. *)
  Definition true_row_demand :=
    IncWitness.demand true witness_flat [tt] 16%N IncWitness.init.

  (** A demand of the true row finishes. *)
  Example true_row_demand_is_done : fst true_row_demand = Done.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The demanded true row stores true. *)
  Example true_row_stores_true : IncWitness.value (snd true_row_demand) tt = Some true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The restricted worklist computes the constant row as false, and it finishes. *)
  Definition false_row_demand :=
    IncWitness.demand false witness_flat [tt] 16%N IncWitness.init.

  (** A demand of the false row finishes. *)
  Example false_row_demand_is_done : fst false_row_demand = Done.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Completion stores bottom explicitly, so the requested root belongs to the domain. *)
  Example false_row_stores_false : IncWitness.value (snd false_row_demand) tt = Some false.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** An untrusted solver can propose a candidate below the row's required value. *)
  Module ForgedSolver <: SOLVER_OPS WitnessBool RestrictionWitness.RS.
    Definition run (_ : RestrictionWitness.RS.prog) (_ : policy unit) (_ : N)
        : outcome (kmap unit bool) := Solved PTrieCode.empty.
  End ForgedSolver.

  Module CheckedWitness := IncrementalCode WitnessBool OneRow RestrictionWitness.RS
    RestrictionWitness.Impl ForgedSolver CheckerWitness.

  (** The authoritative row checker rejects the forged proposal with Check_failed. *)
  Example rejected_candidate_reports_check_failure :
    fst (CheckedWitness.demand true witness_flat [tt] 16%N CheckedWitness.init) =
      DemandRejected Check_failed.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A rejected candidate keeps the state that the demand started from. *)
  Example rejected_candidate_keeps_init_state :
    snd (CheckedWitness.demand true witness_flat [tt] 16%N CheckedWitness.init) =
      CheckedWitness.init.
  Proof.
    vm_compute; reflexivity.
  Qed.

End DemandTests.

(** * Edit *)

Module EditTests.

  (** Naming the only row covers replacement of its constant value. *)
  Example changed_row_is_covered : IncWitness.edit_covers false true [tt].
  Proof.
    intros [] Houtside; exfalso; apply Houtside; now left.
  Qed.

  (** The stored false value is sound for the old false row. *)
  Example stored_false_is_sound_for_old_row : IncWitness.inv false one_false.
  Proof.
    split.
    - intros [] [] [] _ _ Hdom _; exact Hdom.
    - intros [] [] _ _ _; vm_compute; reflexivity.
  Qed.

  (** The edit that changes the row's constant value. *)
  Definition witness_edited := IncWitness.edit false true [tt] one_false.

  (** A changed target loses its old binding. *)
  Example changed_edit_drops_old_binding : IncWitness.value witness_edited tt = None.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** An empty covered edit preserves the complete state. *)
  Example empty_edit_keeps_state : IncWitness.edit false false [] one_false = one_false.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The demand that follows the edit recomputes the changed row. *)
  Definition witness_redemanded :=
    IncWitness.demand true witness_flat [tt] 16%N witness_edited.

  (** The demand after the edit finishes. *)
  Example redemand_after_edit_is_done : fst witness_redemanded = Done.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The demand after the edit stores the new value true. *)
  Example redemand_after_edit_stores_true :
    IncWitness.value (snd witness_redemanded) tt = Some true.
  Proof.
    vm_compute; reflexivity.
  Qed.

End EditTests.

(** * Graph fixtures *)

(** A graph program with a source, an island, a second writer and a moving target. *)
Record incremental_graph_program := {
  graph_source : bool;
  graph_island : bool;
  graph_second_side_writer : bool;
  graph_moving_target : nat
}.

Module IncGraphBool <: WLATTICE_OPS.
  Definition t := bool.
  Definition leb := implb.
  Definition bot := false.
  Definition is_bot := negb.
  Definition join := orb.
  Definition wparam := unit.
  Definition widen (_ : unit) := orb.
  Definition narrow := andb.
End IncGraphBool.

(** The graph system: rows 0 to 7, with reads, sides and targets that depend on the program. *)
Module IncGraphSystem <: LOCAL_SYSTEM_OPS IncGraphBool.
  Definition prog := incremental_graph_program.
  Definition key := nat.
  Definition row := nat.
  Definition frame := unit.
  Definition key_code := Pos.of_succ_nat.
  Definition key_eqb := Nat.eqb.

  (** Readers precede their producers, so propagation must revisit pending work. *)
  Definition rows (_ : prog) : list row := [2; 5; 6; 1; 4; 7; 0; 3].

  Definition target (p : prog) (r : row) : key :=
    match r with
    | 3 => 20
    | 4 => 40
    | 5 => 50
    | 6 => graph_moving_target p
    | 7 => 41
    | _ => r
    end.

  Definition start (p : prog) (r : row) : query key bool frame :=
    match r with
    | 0 => Ret (graph_source p)
    | 1 => Ask 0 tt
    | 2 => Ask 1 tt
    | 3 => Ret (graph_island p)
    | 4 => Side 41 true (Ret true)
    | 5 => Ask 41 tt
    | 6 => Ret true
    | 7 => Ret (graph_second_side_writer p)
    | _ => Ret false
    end.

  Definition resume (_ : prog) (_ : frame) (a : bool) : query key bool frame := Ret a.

  Definition deps (_ : prog) (r : row) : list key :=
    match r with 1 => [0] | 2 => [1] | 5 => [41] | _ => [] end.

  Definition sides (_ : prog) (r : row) : list key :=
    match r with 4 => [41] | _ => [] end.

  Definition row_code := Pos.of_succ_nat.

  Definition rows_of (p : prog) (x : key) : list row :=
    filter (fun r => existsb (Nat.eqb x) (target p r :: sides p r)) (rows p).
End IncGraphSystem.

Module IncGraphRestriction := RestrictCode IncGraphBool IncGraphSystem.
Module IncGraphPolicy := PolicyCode IncGraphBool.
Module IncGraphSolver :=
  WorklistCode IncGraphBool IncGraphRestriction.RS IncGraphPolicy HeapCode.
Module IncGraphChecker := CheckCode IncGraphBool IncGraphSystem.
Module IncGraph := IncrementalCode IncGraphBool IncGraphSystem IncGraphRestriction.RS
  IncGraphRestriction.Code IncGraphSolver IncGraphChecker.

(** A graph policy with no heads and no delays. *)
Definition graph_flat : policy unit :=
  Policy unit PTrieCode.empty PTrieCode.empty tt 0.

(** The original graph program: the source and the island are true, and row 6 targets key 30. *)
Definition graph_original : incremental_graph_program :=
  {| graph_source := true; graph_island := true;
     graph_second_side_writer := false; graph_moving_target := 30 |}.

(** The original program with the source changed to false. *)
Definition graph_source_false : incremental_graph_program :=
  {| graph_source := false; graph_island := true;
     graph_second_side_writer := false; graph_moving_target := 30 |}.

(** The original program with the island changed to false. *)
Definition graph_island_false : incremental_graph_program :=
  {| graph_source := true; graph_island := false;
     graph_second_side_writer := false; graph_moving_target := 30 |}.

(** The original program with row 7 writing its side contribution. *)
Definition graph_side_changed : incremental_graph_program :=
  {| graph_source := true; graph_island := true;
     graph_second_side_writer := true; graph_moving_target := 30 |}.

(** The original program with row 6 moved to key 31. *)
Definition graph_target_moved : incremental_graph_program :=
  {| graph_source := true; graph_island := true;
     graph_second_side_writer := false; graph_moving_target := 31 |}.

(** The stored values of the given keys in a state. *)
Definition graph_values (xs : list nat) (st : IncGraph.state) : list (option bool) :=
  map (IncGraph.value st) xs.

(** The status of a demand, with the stored values of the given keys. *)
Definition graph_observe (xs : list nat) (result : demand_status * IncGraph.state)
    : demand_status * list (option bool) :=
  (fst result, graph_values xs (snd result)).

(** The state after demanding the keys 2 and 20 of the original program. *)
Definition graph_loaded :=
  IncGraph.demand graph_original graph_flat [2; 20] 64%N IncGraph.init.

(** The state after demanding the keys 50 and 20 of the original program. *)
Definition graph_side_loaded :=
  IncGraph.demand graph_original graph_flat [50; 20] 64%N IncGraph.init.

(** The state after the side-writer change, applied to the side-loaded state. *)
Definition graph_side_edited :=
  IncGraph.edit graph_original graph_side_changed [7] (snd graph_side_loaded).

(** The buckets of a metadata map, read at the key of a natural number. *)
Definition graph_bucket (buckets : PTrieCode.t (list positive)) (x : nat)
    : option (list positive) := PTrieCode.get (IncGraphSystem.key_code x) buckets.

(** The snapshot of an owner row as its owner, writes and liveness. *)
Definition graph_snapshot_view (st : IncGraph.state) (owner : nat)
    : option (nat * list nat * bool) :=
  match IncGraph.snapshot_get (IncGraphSystem.key_code owner) st with
  | Some ss => Some (snapshot_owner ss, snapshot_writes ss, snapshot_live ss)
  | None => None
  end.

(** A state with hidden influence and co-write buckets at key 99 and no values. *)
Definition graph_hidden_buckets : IncGraph.state :=
  {| inc_values := PTrieCode.empty;
     inc_influence := PTrieCode.set (IncGraphSystem.key_code 99) [1000%positive] PTrieCode.empty;
     inc_cowrites := PTrieCode.set (IncGraphSystem.key_code 99) [2000%positive] PTrieCode.empty;
     inc_snapshots := PTrieCode.empty |}.

(** A state whose stored value at key 0 has a payload that does not match its key. *)
Definition graph_malformed_value : IncGraph.state :=
  {| inc_values := PTrieCode.set (IncGraphSystem.key_code 0) (99, true) PTrieCode.empty;
     inc_influence := PTrieCode.empty;
     inc_cowrites := PTrieCode.empty;
     inc_snapshots := PTrieCode.empty |}.

(** * Graph *)

Module GraphTests.

  (** A demand of two roots finishes and stores the read chain and the island. *)
  Example two_roots_demand_is_done :
    fst (graph_observe [0; 1; 2; 20; 40; 99] graph_loaded) = Done.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The demand stores the read chain and the island, and leaves unrelated keys absent. *)
  Example two_roots_store_chain_and_island :
    snd (graph_observe [0; 1; 2; 20; 40; 99] graph_loaded) =
      [Some true; Some true; Some true; Some true; None; None].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The island edit that makes the island false. *)
  Definition island_edited :=
    IncGraph.edit graph_original graph_island_false [3] (snd graph_loaded).

  (** Editing the disconnected island keeps every checked binding of the read chain. *)
  Example island_edit_keeps_chain :
    graph_values [0; 1; 2; 20] island_edited = [Some true; Some true; Some true; None].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The demand after the island edit restores the island as explicit bottom. *)
  Definition island_redemanded :=
    IncGraph.demand graph_island_false graph_flat [20] 64%N island_edited.

  (** The demand after the island edit finishes. *)
  Example island_redemand_is_done : fst (graph_observe [0; 1; 2; 20] island_redemanded) = Done.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The demand after the island edit keeps the chain and stores the island as false. *)
  Example island_redemand_stores_false_island :
    snd (graph_observe [0; 1; 2; 20] island_redemanded) =
      [Some true; Some true; Some true; Some false].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The edit that makes the source false. *)
  Definition chain_edited :=
    IncGraph.edit graph_original graph_source_false [0] (snd graph_loaded).

  (** Invalidation follows two read edges and retains the disconnected island verbatim. *)
  Example chain_edit_follows_transitive_reads :
    graph_values [0; 1; 2; 20] chain_edited = [None; None; None; Some true].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Editing the source leaves the unrelated island's stored value intact. *)
  Example chain_edit_retains_unrelated_value : IncGraph.value chain_edited 20 = Some true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The demand after the chain edit recomputes the chain as false. *)
  Definition chain_redemanded :=
    IncGraph.demand graph_source_false graph_flat [2] 64%N chain_edited.

  (** The demand after the chain edit finishes. *)
  Example chain_redemand_is_done : fst (graph_observe [0; 1; 2; 20] chain_redemanded) = Done.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The demand after the chain edit replaces the three former true values by stored false. *)
  Example chain_redemand_stores_false_chain :
    snd (graph_observe [0; 1; 2; 20] chain_redemanded) =
      [Some false; Some false; Some false; Some true].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Loading the side roots finishes. *)
  Example side_load_is_done : fst (graph_observe [40; 41; 50; 20] graph_side_loaded) = Done.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Loading the side roots stores true at the writer, co-written, reader and island keys. *)
  Example side_load_stores_true_values :
    snd (graph_observe [40; 41; 50; 20] graph_side_loaded) =
      [Some true; Some true; Some true; Some true].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Changing the separate writer of 41 invalidates its co-written peer 40 and its reader 50. *)
  Example side_edit_closes_cowrites_and_reads :
    graph_values [40; 41; 50; 20] graph_side_edited = [None; None; None; Some true].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The state after demanding the target roots 30, 31 and 20 of the original program. *)
  Definition target_loaded :=
    IncGraph.demand graph_original graph_flat [30; 31; 20] 64%N IncGraph.init.

  (** The edit moves row 6 from its loaded target to the new target. *)
  Definition target_edited :=
    IncGraph.edit graph_original graph_target_moved [6] (snd target_loaded).

  (** Loading the target roots finishes. *)
  Example target_load_is_done : fst (graph_observe [30; 31; 20] target_loaded) = Done.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Loading the target roots stores true at key 30 false at key 31, and true at key 20. *)
  Example target_load_stores_values :
    snd (graph_observe [30; 31; 20] target_loaded) = [Some true; Some false; Some true].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Moving a row invalidates its previous target and an already stored new target. *)
  Example target_edit_uses_old_and_new_targets :
    graph_values [30; 31; 20] target_edited = [None; None; Some true].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The demand after the move recomputes the new target. *)
  Definition target_redemanded :=
    IncGraph.demand graph_target_moved graph_flat [30; 31] 64%N target_edited.

  (** The demand after the move finishes. *)
  Example target_redemand_is_done : fst (graph_observe [30; 31; 20] target_redemanded) = Done.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** After the move, the old target is unknown bottom and the new target receives true. *)
  Example target_redemand_stores_new_target :
    snd (graph_observe [30; 31; 20] target_redemanded) = [Some false; Some true; Some true].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The boundary demand of row 0 in the original program. *)
  Definition boundary :=
    IncGraph.demand graph_original graph_flat [0] 64%N IncGraph.init.

  (** The demand of the boundary finishes. *)
  Example boundary_demand_is_done : fst (graph_observe [0; 1; 2; 20] boundary) = Done.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The boundary stores true at key 0 only. *)
  Example boundary_stores_true_at_root :
    snd (graph_observe [0; 1; 2; 20] boundary) = [Some true; None; None; None].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The demand of row 2 under the false source, from the boundary state, finishes. *)
  Definition frozen_boundary :=
    IncGraph.demand graph_source_false graph_flat [2] 64%N (snd boundary).

  (** The frozen demand finishes. *)
  Example frozen_demand_is_done :
    fst (graph_observe [0; 1; 2; 20] frozen_boundary) = Done.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A sound true boundary is retained and propagated even when its source now returns false.
      Its true value differs from a fresh run's least false value, which makes freezing visible. *)
  Example frozen_demand_keeps_true_boundary :
    snd (graph_observe [0; 1; 2; 20] frozen_boundary) = [Some true; Some true; Some true; None].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Duplicate roots finish with the same status as the unique roots. *)
  Definition duplicate_roots :=
    IncGraph.demand graph_original graph_flat [2; 20; 2; 20; 2] 64%N IncGraph.init.

  (** Duplicate roots leave the completed status unchanged. *)
  Example duplicate_roots_are_done :
    fst (graph_observe [0; 1; 2; 20; 40; 99] duplicate_roots) = Done.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Duplicate roots leave the completed values unchanged. *)
  Example duplicate_roots_keep_values :
    snd (graph_observe [0; 1; 2; 20; 40; 99] duplicate_roots) =
      [Some true; Some true; Some true; Some true; None; None].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** An unknown root with four fuel. *)
  Definition unknown_root :=
    IncGraph.demand graph_original graph_flat [99] 4%N IncGraph.init.

  (** An unknown root finishes. *)
  Example unknown_root_is_done : fst (graph_observe [0; 20; 99] unknown_root) = Done.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** An unknown root becomes explicitly stored bottom, and unrelated keys stay absent. *)
  Example unknown_root_is_present_bottom :
    snd (graph_observe [0; 20; 99] unknown_root) = [None; None; Some false].
  Proof.
    vm_compute; reflexivity.
  Qed.

End GraphTests.

(** * Metadata *)

Module MetadataTests.

  (** The state after the side roots load. *)
  Definition loaded_state := snd graph_side_loaded.

  (** A row reached through two missing keys is recorded once for key 41's influence. *)
  Example loaded_influence_of_41 :
    graph_bucket (inc_influence loaded_state) 41 = Some [51%positive].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Key 40 has two co-written entries, both from row 41. *)
  Example loaded_cowrites_of_40 :
    graph_bucket (inc_cowrites loaded_state) 40 = Some [41%positive; 41%positive].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Key 41 has three co-written entries from rows 41 and 42. *)
  Example loaded_cowrites_of_41 :
    graph_bucket (inc_cowrites loaded_state) 41 =
      Some [41%positive; 42%positive; 41%positive].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The snapshot of owner 40 lists its writes and is live. *)
  Example loaded_snapshot_of_40 :
    graph_snapshot_view loaded_state 40 = Some (40, [40; 41; 40; 41], true).
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The snapshot of owner 41 lists its single write and is live. *)
  Example loaded_snapshot_of_41 :
    graph_snapshot_view loaded_state 41 = Some (41, [41], true).
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Invalidated influence buckets disappear after the side edit. *)
  Example retired_influence_of_41 : graph_bucket (inc_influence graph_side_edited) 41 = None.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Invalidated co-written buckets of key 40 disappear after the side edit. *)
  Example retired_cowrites_of_40 : graph_bucket (inc_cowrites graph_side_edited) 40 = None.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Invalidated co-written buckets of key 41 disappear after the side edit. *)
  Example retired_cowrites_of_41 : graph_bucket (inc_cowrites graph_side_edited) 41 = None.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A visited snapshot of owner 40 remains as a retired, not live, group. *)
  Example retired_snapshot_of_40 :
    graph_snapshot_view graph_side_edited 40 = Some (40, [40; 41; 40; 41], false).
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A visited snapshot of owner 41 remains as a retired group. *)
  Example retired_snapshot_of_41 :
    graph_snapshot_view graph_side_edited 41 = Some (41, [41], false).
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** An unaffected snapshot of owner 20 stays live after the side edit. *)
  Example unaffected_snapshot_of_20 :
    graph_snapshot_view graph_side_edited 20 = Some (20, [20], true).
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The state after the redemand of the retired group. *)
  Definition redemanded_state :=
    snd (IncGraph.demand graph_side_changed graph_flat [50] 64%N graph_side_edited).

  (** The redemand records the reach of row 41 from its missing key. *)
  Example redemand_influence_of_41 :
    graph_bucket (inc_influence redemanded_state) 41 = Some [51%positive].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The redemand records both co-writes of key 40. *)
  Example redemand_cowrites_of_40 :
    graph_bucket (inc_cowrites redemanded_state) 40 = Some [41%positive; 41%positive].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The redemand records three co-writes of key 41. *)
  Example redemand_cowrites_of_41 :
    graph_bucket (inc_cowrites redemanded_state) 41 =
      Some [41%positive; 42%positive; 41%positive].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The redemanded snapshot of owner 40 is live again. *)
  Example redemand_snapshot_of_40 :
    graph_snapshot_view redemanded_state 40 = Some (40, [40; 41; 40; 41], true).
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The redemanded snapshot of owner 41 is live again. *)
  Example redemand_snapshot_of_41 :
    graph_snapshot_view redemanded_state 41 = Some (41, [41], true).
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The state after recording row 4 twice and row 7 once. *)
  Definition repeated_owner_state :=
    IncGraph.record_rows graph_original [4; 4; 7] IncGraph.init.

  (** Recording the same owner twice keeps both co-write entries of key 40. *)
  Example repeated_owner_cowrites_of_40 :
    graph_bucket (inc_cowrites repeated_owner_state) 40 =
      Some [41%positive; 41%positive].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Recording the same owner twice keeps the shared group's entries for key 41. *)
  Example repeated_owner_cowrites_of_41 :
    graph_bucket (inc_cowrites repeated_owner_state) 41 =
      Some [42%positive; 41%positive; 41%positive].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The repeated owner's snapshot lists both of its writes and is live. *)
  Example repeated_owner_snapshot_of_40 :
    graph_snapshot_view repeated_owner_state 40 = Some (40, [40; 41; 40; 41], true).
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The state after a demand of key 99 from the hidden buckets. *)
  Definition hidden_state :=
    snd (IncGraph.demand graph_original graph_flat [99] 4%N graph_hidden_buckets).

  (** A new key stores false and does not inherit the hidden value. *)
  Example hidden_key_stores_false : IncGraph.value hidden_state 99 = Some false.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A new key does not inherit hidden influence entries. *)
  Example hidden_influence_is_cleared :
    graph_bucket (inc_influence hidden_state) 99 = None.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A new key does not inherit hidden co-write entries. *)
  Example hidden_cowrites_are_cleared :
    graph_bucket (inc_cowrites hidden_state) 99 = None.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A malformed payload is hidden at its own key 0. *)
  Example malformed_payload_is_hidden_at_zero :
    IncGraph.value graph_malformed_value 0 = None.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A malformed payload is not visible at the different key 99. *)
  Example malformed_payload_is_hidden_at_new_key :
    IncGraph.value graph_malformed_value 99 = None.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The state after a demand of key 99 from the malformed state. *)
  Definition malformed_state :=
    snd (IncGraph.demand graph_original graph_flat [99] 4%N graph_malformed_value).

  (** The malformed payload stays stored at key 0 after the demand. *)
  Example malformed_payload_stays_stored :
    PTrieCode.get (IncGraphSystem.key_code 0) (inc_values malformed_state) = Some (99, true).
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The new key 99 is stored as false after the demand from the malformed state. *)
  Example malformed_state_stores_false_at_new_key :
    IncGraph.value malformed_state 99 = Some false.
  Proof.
    vm_compute; reflexivity.
  Qed.

End MetadataTests.

(** * Discovery *)

Module DiscoveryTests.

  (** Encoded reads of an absent key return None. *)
  Example absent_code_value_is_none :
    IncWitness.value_code 1%positive tt IncWitness.init = None.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Encoded reads of a stored false return Some false. *)
  Example stored_false_code_value_is_some_false :
    IncWitness.value_code 1%positive tt one_false = Some false.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** An encoded absent key counts as missing. *)
  Example absent_code_is_missing :
    IncWitness.missing_code 1%positive tt IncWitness.init = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** An encoded stored key does not count as missing. *)
  Example stored_false_code_is_not_missing :
    IncWitness.missing_code 1%positive tt one_false = false.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A payload that does not match its key reads as None. *)
  Example mismatched_code_value_is_none :
    IncGraph.value_code (IncGraphSystem.key_code 0) 0 graph_malformed_value = None.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A payload that does not match its key counts as missing. *)
  Example mismatched_code_is_missing :
    IncGraph.missing_code (IncGraphSystem.key_code 0) 0 graph_malformed_value = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The visit of an absent key from the empty discovery. *)
  Definition absent_visit :=
    IncWitness.discovery_visit IncWitness.init tt IncWitness.empty_discovery.

  (** The visit of a stored false key from the empty discovery. *)
  Definition stored_visit :=
    IncWitness.discovery_visit one_false tt IncWitness.empty_discovery.

  (** A visit queues an absent key once. *)
  Example absent_visit_queues_key : discovery_pending absent_visit = [tt].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A visit marks an absent key as missing. *)
  Example absent_visit_marks_key_missing : discovery_missing absent_visit = [tt].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A visit of an absent key freezes nothing. *)
  Example absent_visit_freezes_nothing : discovery_frozen absent_visit = [].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A visit of a stored key queues nothing. *)
  Example stored_visit_queues_nothing : discovery_pending stored_visit = [].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A visit of a stored key marks nothing as missing. *)
  Example stored_visit_marks_nothing_missing : discovery_missing stored_visit = [].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A visit of a stored key freezes its explicitly stored bottom. *)
  Example stored_visit_freezes_bottom : discovery_frozen stored_visit = [(tt, false)].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** An encoded visit of an absent key is the same as the public visit. *)
  Example visit_code_matches_visit_on_absent :
    IncWitness.discovery_visit_code 1%positive IncWitness.init tt IncWitness.empty_discovery =
      IncWitness.discovery_visit IncWitness.init tt IncWitness.empty_discovery.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** An encoded visit of a stored key is the same as the public visit. *)
  Example visit_code_matches_visit_on_stored :
    IncWitness.discovery_visit_code 1%positive one_false tt IncWitness.empty_discovery =
      IncWitness.discovery_visit one_false tt IncWitness.empty_discovery.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A repeated visit leaves the first discovery unchanged. *)
  Example repeated_visit_keeps_first_discovery :
    IncWitness.discovery_visit IncWitness.init tt absent_visit = absent_visit.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A seed of an absent key after discovery leaves the first discovery unchanged. *)
  Example seed_after_discovery_keeps_first :
    IncWitness.discovery_seed_one IncWitness.init absent_visit tt = absent_visit.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A seed of a stored key leaves the empty discovery unchanged. *)
  Example seed_of_stored_key_keeps_empty :
    IncWitness.discovery_seed_one one_false IncWitness.empty_discovery tt =
      IncWitness.empty_discovery.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The visit of the malformed payload at key 0 is pending, as an absent key. *)
  Definition malformed_visit :=
    IncGraph.discovery_visit graph_malformed_value 0 IncGraph.empty_discovery.

  (** A mismatched stored payload queues its key during discovery. *)
  Example malformed_visit_is_pending : discovery_pending malformed_visit = [0].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A mismatched stored payload is marked as missing during discovery. *)
  Example malformed_visit_is_missing : discovery_missing malformed_visit = [0].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A mismatched stored payload freezes nothing during discovery. *)
  Example malformed_visit_freezes_nothing : discovery_frozen malformed_visit = [].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The visit of key 2 in the loaded graph state. *)
  Definition stored_graph_visit :=
    IncGraph.discovery_visit (snd graph_loaded) 2 IncGraph.empty_discovery.

  (** A visit of a stored key below several trie branches queues nothing. *)
  Example stored_graph_visit_queues_nothing : discovery_pending stored_graph_visit = [].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A visit of a stored key below several trie branches marks nothing as missing. *)
  Example stored_graph_visit_marks_nothing_missing :
    discovery_missing stored_graph_visit = [].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A visit of a stored key freezes its existing nonbottom value. *)
  Example stored_graph_visit_freezes_true : discovery_frozen stored_graph_visit = [(2, true)].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Duplicate roots discover an absent key without duplicate output keys. *)
  Example duplicate_root_discovers_key_once :
    IncGraph.discovery graph_original [99; 99] 4%N IncGraph.init = Some ([99], [], []).
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The base map of keys 7 and 9, before filling. *)
  Definition fill_base :=
    PTrieCode.set (IncGraphSystem.key_code 7) (7, true)
      (PTrieCode.set (IncGraphSystem.key_code 9) (9, true) PTrieCode.empty).

  (** The base map after filling keys 0 and 7 from the malformed payload's raw candidates. *)
  Definition fill_result :=
    IncGraph.fill_local [0; 7] (inc_values graph_malformed_value) fill_base.

  (** Filling writes the requested key 0 from its raw candidate. *)
  Example fill_writes_requested_key_zero :
    PTrieCode.get (IncGraphSystem.key_code 0) fill_result = Some (0, true).
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Filling overwrites the requested key 7 with its raw candidate. *)
  Example fill_overwrites_requested_key_seven :
    PTrieCode.get (IncGraphSystem.key_code 7) fill_result = Some (7, false).
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Filling retains the base binding of the unrequested key 9. *)
  Example fill_keeps_unrequested_key_nine :
    PTrieCode.get (IncGraphSystem.key_code 9) fill_result = Some (9, true).
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The state after merging the discovered values into the hidden buckets. *)
  Definition merged_state :=
    IncGraph.merge_discovered graph_hidden_buckets [0; 7] (inc_values graph_malformed_value).

  (** Merging stores the discovered true value of key 0. *)
  Example merge_stores_key_zero : IncGraph.value merged_state 0 = Some true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Merging stores the discovered false value of key 7. *)
  Example merge_stores_key_seven : IncGraph.value merged_state 7 = Some false.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Merging keeps the influence bucket of key 99 for the finishing pass. *)
  Example merge_keeps_influence_of_99 :
    graph_bucket (inc_influence merged_state) 99 = Some [1000%positive].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Merging keeps the co-write bucket of key 99 for the finishing pass. *)
  Example merge_keeps_cowrites_of_99 :
    graph_bucket (inc_cowrites merged_state) 99 = Some [2000%positive].
  Proof.
    vm_compute; reflexivity.
  Qed.

End DiscoveryTests.

(** * Contract client *)

(** An importing client can apply the complete timed functor under its released parameters. *)
Module IncrementalContractClient (L : WLATTICE_T) (LB : LUB L) (Top : HAS_TOP L)
    (S : LOCAL_SYSTEM_T L)
    (RS : SYSTEM_T L with Definition key := S.key with Definition key_code := S.key_code)
    (R : RESTRICT_T L S RS) (Sol : SOLVER_T L RS) (Checker : CHECK_T L S)
    (Least : SOLVER_LEAST L LB RS Sol).
  Module Certified <: INCREMENTAL_ALL L LB Top S RS R Sol Checker Least :=
    IncrementalT L LB Top S RS R Sol Checker Least.
End IncrementalContractClient.
