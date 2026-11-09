(** * Exact-tree reducibility observations

    Actual event visitors distinguish nested loops from irreducible cycle entries.
    For example, replacing the exact nested-loop tree by an empty tree changes acceptance.
    Builds on: GraphReducibility and GraphFixtures. *)

From Stdlib Require Import List PArith.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Graph Require Import GraphModel GraphPrepared GraphDomSpec GraphHierSpec
  GraphReducibility GraphFixtures GraphCheckDom.
Import List.ListNotations.
Open Scope positive_scope.

Example nested_reducible :
  Reducibility.test Fixtures.NestedLoop.prepared Fixtures.NestedLoop.tree = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example irreducible_rejected :
  Reducibility.test Fixtures.Irreducible.prepared Fixtures.Irreducible.tree = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example line_reducible :
  Reducibility.test Fixtures.Line.prepared Fixtures.Line.tree = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example self_loop_reducible :
  Reducibility.test Fixtures.SelfLoop.prepared Fixtures.SelfLoop.tree = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example empty_reducible :
  Reducibility.test Fixtures.Empty.prepared Fixtures.Empty.tree = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example missing_ranks_do_not_accept_cycle :
  Reducibility.test Fixtures.NestedLoop.prepared (Dom.Tree Map.empty Map.empty Map.empty) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example exact_tree_dominance_client :
  Reducibility.dominates Fixtures.NestedLoop.tree 2 3 = true <->
    GraphDomSpec.dominates (Prepared.graph Fixtures.NestedLoop.prepared) 2%nat 3%nat.
Proof.
  apply (Reducibility.dominates_correct Fixtures.NestedLoop.prepared
    Fixtures.NestedLoop.tree 3%nat 2%nat 3 2 Fixtures.NestedLoop.fixture_ready
    Fixtures.NestedLoop.tree_exact).
  - apply reachable_iff_path. exists 1%nat, [(1%nat, 2%nat); (2%nat, 3%nat)].
    split; [vm_compute; now left|].
    apply (@path_cons nat (nat * nat) (Prepared.graph Fixtures.NestedLoop.prepared)
      (1%nat, 2%nat) [(2%nat, 3%nat)] 3%nat).
    + vm_compute. auto.
    + apply (@path_cons nat (nat * nat) (Prepared.graph Fixtures.NestedLoop.prepared)
        (2%nat, 3%nat) [] 3%nat); [vm_compute; auto|constructor].
  - apply reachable_iff_path. exists 1%nat, [(1%nat, 2%nat)].
    split; [vm_compute; now left|].
    apply (@path_cons nat (nat * nat) (Prepared.graph Fixtures.NestedLoop.prepared)
      (1%nat, 2%nat) [] 2%nat); [vm_compute; auto|constructor].
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.

Example nested_semantically_reducible : reducible (Prepared.graph Fixtures.NestedLoop.prepared).
Proof.
  apply (Reducibility.reducible_b_sound Fixtures.NestedLoop.prepared Fixtures.NestedLoop.tree
    Fixtures.NestedLoop.fixture_ready Fixtures.NestedLoop.tree_exact).
  exact nested_reducible.
Qed.

Example irreducible_semantic_rejection :
  ~ reducible (Prepared.graph Fixtures.Irreducible.prepared).
Proof.
  intro Hreducible.
  apply (proj2 (Reducibility.reducible_b_correct Fixtures.Irreducible.prepared
    Fixtures.Irreducible.tree Fixtures.Irreducible.fixture_ready
    Fixtures.Irreducible.tree_exact)) in Hreducible.
  rewrite irreducible_rejected in Hreducible. discriminate.
Qed.

Example empty_semantically_reducible : reducible (Prepared.graph Fixtures.Empty.prepared).
Proof.
  apply (Reducibility.reducible_b_sound Fixtures.Empty.prepared Fixtures.Empty.tree
    Fixtures.Empty.fixture_ready Fixtures.Empty.tree_exact).
  exact empty_reducible.
Qed.

(** * Detached irreducible component *)

(** Node 0 is isolated and node 1 offers two entries into the cycle 2 -> 3 -> 2. *)
Definition detached roots :=
  Fixtures.prepare roots [0%nat; 1%nat; 2%nat; 3%nat]
    [(1%nat, 2%nat); (1%nat, 3%nat); (2%nat, 3%nat); (3%nat, 2%nat)].

Local Lemma detached_ready roots :
  incl roots [0%nat; 1%nat; 2%nat; 3%nat] -> Prepared.ready (detached roots).
Proof.
  intro Hroots.
  apply Prepared.prepare_ready; [exact nat_encoding_laws| |].
  - constructor.
    + vm_compute. repeat (apply NoDup_cons; [cbn; intuition congruence|]).
      apply NoDup_nil.
    + exact Hroots.
    + intros v [a b] Hin.
      apply filter_In in Hin. destruct Hin as [_ Hsame].
      cbn in Hsame |- *. now apply PeanoNat.Nat.eqb_eq in Hsame.
    + intros v [a b] Hv Hin.
      apply filter_In in Hin. destruct Hin as [Hin _].
      vm_compute in Hin |- *. intuition congruence.
  - intro v. apply NoDup_filter.
    vm_compute. repeat (apply NoDup_cons; [cbn; intuition congruence|]).
    apply NoDup_nil.
Qed.

Definition no_entries := detached [].
Definition isolated_entry := detached [0%nat].
Definition no_entries_tree := DomCheck.of_parents no_entries (Fixtures.parents []).
Definition isolated_entry_tree := DomCheck.of_parents isolated_entry (Fixtures.parents []).

Example no_entries_ready : Prepared.ready no_entries.
Proof.
  apply detached_ready. intros v Hin. contradiction.
Qed.

Example isolated_entry_ready : Prepared.ready isolated_entry.
Proof.
  apply detached_ready. intros v Hin. vm_compute in Hin |- *. tauto.
Qed.

Example no_entries_tree_exact : Dom.exact no_entries no_entries_tree.
Proof.
  apply DomCheck.check_sound; [exact no_entries_ready|apply Fixtures.parents_wf|].
  vm_compute. reflexivity.
Qed.

Example no_entries_hand_written_tree_control :
  no_entries_tree = Dom.Tree Map.empty Map.empty Map.empty.
Proof.
  vm_compute. reflexivity.
Qed.

Example isolated_entry_tree_exact : Dom.exact isolated_entry isolated_entry_tree.
Proof.
  apply DomCheck.check_sound; [exact isolated_entry_ready|apply Fixtures.parents_wf|].
  vm_compute. reflexivity.
Qed.

Example no_entries_nonempty_control :
  Graph.nodes (Prepared.graph no_entries) = [0%nat; 1%nat; 2%nat; 3%nat] /\
  Graph.entries (Prepared.graph no_entries) = [] /\
  Prepared.entry_ids no_entries = [].
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Example no_entries_reducer_accepts :
  Reducibility.test no_entries no_entries_tree = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example isolated_entry_reducer_accepts :
  Reducibility.test isolated_entry isolated_entry_tree = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example no_entries_semantically_reducible : reducible (Prepared.graph no_entries).
Proof.
  apply (Reducibility.reducible_b_sound no_entries no_entries_tree
    no_entries_ready no_entries_tree_exact).
  exact no_entries_reducer_accepts.
Qed.

Example isolated_entry_semantically_reducible : reducible (Prepared.graph isolated_entry).
Proof.
  apply (proj1 (Reducibility.reducible_b_correct isolated_entry isolated_entry_tree
    isolated_entry_ready isolated_entry_tree_exact)).
  exact isolated_entry_reducer_accepts.
Qed.

Example detached_listed_cycle roots :
  In 2%nat (Graph.nodes (Prepared.graph (detached roots))) /\
  path (Prepared.graph (detached roots)) 2%nat [(2%nat, 3%nat); (3%nat, 2%nat)] 2%nat.
Proof.
  split; [vm_compute; tauto|].
  apply (@path_cons nat (nat * nat) (Prepared.graph (detached roots))
    (2%nat, 3%nat) [(3%nat, 2%nat)] 2%nat); [vm_compute; auto|].
  apply (@path_cons nat (nat * nat) (Prepared.graph (detached roots))
    (3%nat, 2%nat) [] 2%nat); [vm_compute; auto|constructor].
Qed.

Example detached_cycle_unreachable :
  ~ reachable (Prepared.graph no_entries) 2%nat /\
  ~ reachable (Prepared.graph isolated_entry) 2%nat.
Proof.
  split.
  - intro Hreach. apply reachable_iff_path in Hreach.
    destruct Hreach as [s [es [Hentry Hpath]]].
    vm_compute in Hentry. contradiction.
  - assert (Honly : forall v, reachable (Prepared.graph isolated_entry) v -> v = 0%nat).
    { intros v Hreach. induction Hreach as [v Hentry|e Hreach IH Hedge].
      - vm_compute in Hentry. intuition congruence.
      - rewrite IH in Hedge. change (In e []) in Hedge. contradiction. }
    intro Hreach. specialize (Honly 2%nat Hreach). discriminate.
Qed.

(** Unreachable semantic dominance is vacuous even when the interval query lacks ranks. *)
Example no_entries_vacuous_dominance :
  GraphDomSpec.dominates (Prepared.graph no_entries) 3%nat 2%nat /\
  Reducibility.dominates no_entries_tree 4 3 = false.
Proof.
  split.
  - intros s es Hentry Hpath.
    change (In s []) in Hentry. contradiction.
  - vm_compute. reflexivity.
Qed.

(** The original predicate also supplies a back edge when the graph has no entries. *)
Example no_entries_cycle_semantic_client :
  exists e, In e [(2%nat, 3%nat); (3%nat, 2%nat)] /\
    back_edge (Prepared.graph no_entries) e.
Proof.
  destruct (detached_listed_cycle []) as [Hlisted Hcycle].
  exact (no_entries_semantically_reducible 2%nat
    [(2%nat, 3%nat); (3%nat, 2%nat)] Hlisted Hcycle ltac:(discriminate)).
Qed.

(** The imported predicate still supplies a back edge on the listed unreachable cycle. *)
Example detached_cycle_semantic_client :
  exists e, In e [(2%nat, 3%nat); (3%nat, 2%nat)] /\
    back_edge (Prepared.graph isolated_entry) e.
Proof.
  destruct (detached_listed_cycle [0%nat]) as [Hlisted Hcycle].
  exact (isolated_entry_semantically_reducible 2%nat
    [(2%nat, 3%nat); (3%nat, 2%nat)] Hlisted Hcycle ltac:(discriminate)).
Qed.

(** Re-rooting the same topology at its split exposes its irreducible component. *)
Definition attached_cycle := detached [1%nat].
Definition attached_cycle_tree :=
  DomCheck.of_parents attached_cycle (Fixtures.parents [(3, 2); (4, 2)]).

Example attached_cycle_ready : Prepared.ready attached_cycle.
Proof.
  apply detached_ready. intros v Hin. vm_compute in Hin |- *. tauto.
Qed.

Example attached_cycle_tree_exact : Dom.exact attached_cycle attached_cycle_tree.
Proof.
  apply DomCheck.check_sound; [exact attached_cycle_ready|apply Fixtures.parents_wf|].
  vm_compute. reflexivity.
Qed.

Example attached_cycle_reducer_rejects :
  Reducibility.test attached_cycle attached_cycle_tree = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example attached_cycle_semantic_rejection : ~ reducible (Prepared.graph attached_cycle).
Proof.
  intro Hreducible.
  apply (proj2 (Reducibility.reducible_b_correct attached_cycle attached_cycle_tree
    attached_cycle_ready attached_cycle_tree_exact)) in Hreducible.
  rewrite attached_cycle_reducer_rejects in Hreducible. discriminate.
Qed.
