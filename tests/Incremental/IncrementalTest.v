(** * Incremental transition observations

    Demands solve and check missing regions, while edits remove affected stored values.
    For example, a changed constant row is recomputed after its old binding is invalidated.
    Builds on: Incremental, Restrict and Worklist. *)

From Stdlib Require Import List Bool Arith NArith PArith Lia.
From Argent Require Import Loop.
From Galois.Base Require Import MapSig Trie Heap.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import Query SystemSig PolicySig SolverSig Policy Check Worklist.
From Galois.Incremental Require Import RestrictSig Restrict IncrementalSig Incremental.

Import List.ListNotations.

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

Module IncWitness.
  Include IncrementalCode WitnessBool OneRow RestrictionWitness.RS
    RestrictionWitness.Impl SolverWitness CheckerWitness.
  Include INCREMENTAL_SPEC WitnessBool OneRow RestrictionWitness.RS
    RestrictionWitness.Impl SolverWitness CheckerWitness.
End IncWitness.

Definition witness_flat : policy unit :=
  Policy unit PTrieCode.empty PTrieCode.empty tt 0.

(** Empty demands succeed even with no fuel. *)
Example empty_demand_status :
  IncWitness.demand false witness_flat [] 0%N IncWitness.init = (Done, IncWitness.init).
Proof.
  vm_compute; reflexivity.
Qed.

Definition singleton_value (v : bool) : IncWitness.state :=
  {| inc_values := PTrieCode.set 1%positive (tt, v) PTrieCode.empty;
     inc_influence := PTrieCode.empty;
     inc_cowrites := PTrieCode.empty;
     inc_snapshots := PTrieCode.empty |}.

Definition one_false : IncWitness.state := singleton_value false.

(** Lookup distinguishes absence, stored bottom and a stored nonbottom value. *)
Example real_lookup_observations :
  (IncWitness.value IncWitness.init tt,
   IncWitness.value one_false tt,
   IncWitness.value (singleton_value true) tt) = (None, Some false, Some true).
Proof.
  vm_compute; reflexivity.
Qed.

(** Covered roots return the original state before inspecting program, policy or fuel. *)
Example covered_demand_noop :
  IncWitness.demand true witness_flat [tt; tt] 0%N one_false = (Done, one_false).
Proof.
  vm_compute; reflexivity.
Qed.

(** Missing roots exhaust zero fuel without changing the old state. *)
Example missing_demand_zero_fuel :
  IncWitness.demand true witness_flat [tt] 0%N IncWitness.init =
    (DemandOutOfFuel, IncWitness.init).
Proof.
  vm_compute; reflexivity.
Qed.

(** The real restricted worklist computes the constant row. *)
Example demand_true_row :
  let result := IncWitness.demand true witness_flat [tt] 16%N IncWitness.init in
  (fst result, IncWitness.value (snd result) tt) = (Done, Some true).
Proof.
  vm_compute; reflexivity.
Qed.

(** Completion stores bottom explicitly so the requested root belongs to the domain. *)
Example demand_false_row :
  let result := IncWitness.demand false witness_flat [tt] 16%N IncWitness.init in
  (fst result, IncWitness.value (snd result) tt) = (Done, Some false).
Proof.
  vm_compute; reflexivity.
Qed.

(** Naming the only row covers replacement of its constant value. *)
Example changed_row_is_covered : IncWitness.edit_covers false true [tt].
Proof.
  intros [] Houtside; exfalso; apply Houtside; now left.
Qed.

(** The stored false value is sound for the old false row. *)
Example old_region_sound : IncWitness.inv false one_false.
Proof.
  split.
  - intros [] [] [] _ _ Hdom _; exact Hdom.
  - intros [] [] _ _ _; vm_compute; reflexivity.
Qed.

(** A changed target loses its old binding. *)
Example changed_edit_invalidates :
  IncWitness.value (IncWitness.edit false true [tt] one_false) tt = None.
Proof.
  vm_compute; reflexivity.
Qed.

(** An empty covered edit preserves the complete state. *)
Example unchanged_edit_noop : IncWitness.edit false false [] one_false = one_false.
Proof.
  vm_compute; reflexivity.
Qed.

(** Demand after an edit recomputes the changed row. *)
Example demand_after_edit :
  let edited := IncWitness.edit false true [tt] one_false in
  let result := IncWitness.demand true witness_flat [tt] 16%N edited in
  (fst result, IncWitness.value (snd result) tt) = (Done, Some true).
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

(** The authoritative row checker rejects that proposal and retains the old state. *)
Example rejected_candidate_preserves_state :
  CheckedWitness.demand true witness_flat [tt] 16%N CheckedWitness.init =
    (DemandRejected Check_failed, CheckedWitness.init).
Proof.
  vm_compute; reflexivity.
Qed.

(** * Selective graph transitions *)

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

Definition graph_flat : policy unit :=
  Policy unit PTrieCode.empty PTrieCode.empty tt 0.

Definition graph_original : incremental_graph_program :=
  {| graph_source := true; graph_island := true;
     graph_second_side_writer := false; graph_moving_target := 30 |}.

Definition graph_source_false : incremental_graph_program :=
  {| graph_source := false; graph_island := true;
     graph_second_side_writer := false; graph_moving_target := 30 |}.

Definition graph_island_false : incremental_graph_program :=
  {| graph_source := true; graph_island := false;
     graph_second_side_writer := false; graph_moving_target := 30 |}.

Definition graph_side_changed : incremental_graph_program :=
  {| graph_source := true; graph_island := true;
     graph_second_side_writer := true; graph_moving_target := 30 |}.

Definition graph_target_moved : incremental_graph_program :=
  {| graph_source := true; graph_island := true;
     graph_second_side_writer := false; graph_moving_target := 31 |}.

Definition graph_values (xs : list nat) (st : IncGraph.state) : list (option bool) :=
  map (IncGraph.value st) xs.

Definition graph_observe (xs : list nat) (result : demand_status * IncGraph.state)
    : demand_status * list (option bool) :=
  (fst result, graph_values xs (snd result)).

Definition graph_loaded :=
  IncGraph.demand graph_original graph_flat [2; 20] 64%N IncGraph.init.

(** Demand stores the read chain and island while leaving unrelated keys absent. *)
Example graph_demand_two_components :
  graph_observe [0; 1; 2; 20; 40; 99] graph_loaded =
    (Done, [Some true; Some true; Some true; Some true; None; None]).
Proof.
  vm_compute; reflexivity.
Qed.

Definition graph_island_edited :=
  IncGraph.edit graph_original graph_island_false [3] (snd graph_loaded).

(** Editing the disconnected island preserves every checked read-chain binding. *)
Example graph_edit_keeps_disconnected_chain :
  graph_values [0; 1; 2; 20] graph_island_edited =
    [Some true; Some true; Some true; None].
Proof.
  vm_compute; reflexivity.
Qed.

(** A later demand restores the edited island at explicit bottom without losing the chain. *)
Example graph_redemand_changed_island :
  graph_observe [0; 1; 2; 20]
    (IncGraph.demand graph_island_false graph_flat [20] 64%N graph_island_edited) =
    (Done, [Some true; Some true; Some true; Some false]).
Proof.
  vm_compute; reflexivity.
Qed.

Definition graph_chain_edited :=
  IncGraph.edit graph_original graph_source_false [0] (snd graph_loaded).

(** Invalidation follows two read edges and retains the disconnected island verbatim. *)
Example graph_edit_follows_transitive_reads :
  graph_values [0; 1; 2; 20] graph_chain_edited = [None; None; None; Some true].
Proof.
  vm_compute; reflexivity.
Qed.

(** Recomputing the edited chain replaces all three former true values by stored false. *)
Example graph_redemand_changed_chain :
  graph_observe [0; 1; 2; 20]
    (IncGraph.demand graph_source_false graph_flat [2] 64%N graph_chain_edited) =
    (Done, [Some false; Some false; Some false; Some true]).
Proof.
  vm_compute; reflexivity.
Qed.

Definition graph_side_loaded :=
  IncGraph.demand graph_original graph_flat [50; 20] 64%N IncGraph.init.

Definition graph_side_edited :=
  IncGraph.edit graph_original graph_side_changed [7] (snd graph_side_loaded).

(** Changing the separate writer of 41 also invalidates its co-written peer 40 and reader 50. *)
Example graph_edit_closes_cowrites_and_reads :
  (graph_observe [40; 41; 50; 20] graph_side_loaded,
   graph_values [40; 41; 50; 20] graph_side_edited) =
    ((Done, [Some true; Some true; Some true; Some true]),
     [None; None; None; Some true]).
Proof.
  vm_compute; reflexivity.
Qed.

Definition graph_target_loaded :=
  IncGraph.demand graph_original graph_flat [30; 31; 20] 64%N IncGraph.init.

Definition graph_target_edited :=
  IncGraph.edit graph_original graph_target_moved [6] (snd graph_target_loaded).

(** Moving a row invalidates both its previous target and an already stored new target. *)
Example graph_edit_uses_old_and_new_targets :
  (graph_observe [30; 31; 20] graph_target_loaded,
   graph_values [30; 31; 20] graph_target_edited) =
    ((Done, [Some true; Some false; Some true]), [None; None; Some true]).
Proof.
  vm_compute; reflexivity.
Qed.

(** After the move, the old target is unknown bottom and the new target receives true. *)
Example graph_redemand_moved_target :
  graph_observe [30; 31; 20]
    (IncGraph.demand graph_target_moved graph_flat [30; 31] 64%N graph_target_edited) =
    (Done, [Some false; Some true; Some true]).
Proof.
  vm_compute; reflexivity.
Qed.

Definition graph_boundary :=
  IncGraph.demand graph_original graph_flat [0] 64%N IncGraph.init.

(** A sound true boundary is retained and propagated even when its source now returns false.
    The old singleton remains closed and post-sound for graph_source_false; its true value
    deliberately differs from a fresh run's least false value, making freezing observable. *)
Example graph_demand_preserves_frozen_boundary :
  (graph_observe [0; 1; 2; 20] graph_boundary,
   graph_observe [0; 1; 2; 20]
     (IncGraph.demand graph_source_false graph_flat [2] 64%N (snd graph_boundary))) =
    ((Done, [Some true; None; None; None]),
     (Done, [Some true; Some true; Some true; None])).
Proof.
  vm_compute; reflexivity.
Qed.

(** Duplicate roots leave the completed values and domain observations unchanged. *)
Example graph_duplicate_roots_keep_results :
  graph_observe [0; 1; 2; 20; 40; 99]
    (IncGraph.demand graph_original graph_flat [2; 20; 2; 20; 2] 64%N IncGraph.init) =
    (Done, [Some true; Some true; Some true; Some true; None; None]).
Proof.
  vm_compute; reflexivity.
Qed.

(** An unknown root becomes explicitly stored bottom while unrelated components stay absent. *)
Example graph_unknown_root_is_present_bottom :
  graph_observe [0; 20; 99]
    (IncGraph.demand graph_original graph_flat [99] 4%N IncGraph.init) =
    (Done, [None; None; Some false]).
Proof.
  vm_compute; reflexivity.
Qed.
