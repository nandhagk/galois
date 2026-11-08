(** * Explicit-stack search fixtures

    These computations observe root order, scoped rejection, labelled events and visitor state.
    For example, two distinct labels with identical endpoints produce Tree then Forward.
    Builds on: GraphSearch and GraphFixtures. *)

From Stdlib Require Import List Bool Arith PArith NArith.
From Galois.Cost Require Import CostMonad CostLoop.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor GraphSearchSpec
  GraphSearch GraphSearchInvariant GraphSearchExact GraphSearchOrder GraphFixtures.
Import List.ListNotations.

Module SearchFixtures.
Local Open Scope nat_scope.

Definition unrestricted := Scope.Make FinSet.empty None.
Definition blocked_one :=
  Scope.Make (FinSet.of_list positive_encoding [1%positive]) None.
Definition right_branch :=
  Scope.Make FinSet.empty (Some (FinSet.of_list positive_encoding [1; 3; 4]%positive)).

Definition single := Fixtures.prepare [1] [1] [].
Definition self_loop := Fixtures.prepare [1] [1] [(1, 1)].
Definition diamond := Fixtures.Diamond.prepared.
Definition line := Fixtures.Line.prepared.

Definition orders {V E} (p : Prepared.t V E) scope roots :=
  let r := SearchRun.dfs p scope roots in (Search.preorder r, Search.postorder r).

Definition count_edge {E} : Visitor.t E nat :=
  Visitor.of_pure (fun _ _ n => n) (fun _ _ _ _ n => S n) (fun _ _ n => n).

Definition count_kinds {E} : Visitor.t E (nat * nat * nat * nat) :=
  Visitor.of_pure (fun _ _ s => s)
    (fun _ _ _ k s =>
      let '(tree, back, forward, cross) := s in
      match k with
      | Search.Tree => (S tree, back, forward, cross)
      | Search.Back => (tree, S back, forward, cross)
      | Search.Forward => (tree, back, S forward, cross)
      | Search.Cross => (tree, back, forward, S cross)
      end)
    (fun _ _ s => s).

Definition labelled_graph :=
  Graph.of_pure [1] [1; 2]
    (fun v => if Nat.eqb v 1 then [10; 11] else [])
    (fun _ => 1) (fun _ => 2).
Definition parallel := Prepared.prepare nat_encoding labelled_graph.

Example singleton_orders : orders single unrestricted [1]%positive = ([1], [1])%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example self_loop_events :
  SearchRun.events self_loop unrestricted [1]%positive =
    [Search.Enter 1 None; Search.Edge (1, 1)%nat 1 1 Search.Back;
     Search.Exit 1 None]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example diamond_orders :
  orders diamond unrestricted [1]%positive = ([1; 2; 4; 3], [4; 2; 3; 1])%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example repeated_roots :
  orders line unrestricted [3; 1; 3]%positive = ([3; 4; 1; 2], [4; 3; 2; 1])%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example unknown_roots :
  orders diamond unrestricted [99; 1; 99]%positive = ([1; 2; 4; 3], [4; 2; 3; 1])%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example empty_roots : orders diamond unrestricted [] = ([], []).
Proof.
  vm_compute. reflexivity.
Qed.

Example blocked_root : SearchRun.events diamond blocked_one [1]%positive = [].
Proof.
  vm_compute. reflexivity.
Qed.

Example within_orders :
  orders diamond right_branch [1]%positive = ([1; 3; 4], [4; 3; 1])%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example diamond_kind_counts :
  snd (Cost.value
    (SearchRun.run_c diamond count_kinds unrestricted [1]%positive (0, 0, 0, 0))) =
    (3, 0, 0, 1).
Proof.
  vm_compute. reflexivity.
Qed.

Example parallel_label_events :
  SearchRun.events parallel unrestricted [1]%positive =
    [Search.Enter 1 None;
     Search.Edge 10%nat 1 2 Search.Tree; Search.Enter 2 (Some (10%nat, 1));
     Search.Exit 2 (Some 1); Search.Edge 11%nat 1 2 Search.Forward;
     Search.Exit 1 None]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example parallel_parent_label :
  Map.get positive_encoding 2%positive
    (Search.parent_edge (SearchRun.dfs parallel unrestricted [1]%positive)) =
    Some (10, 1%positive).
Proof.
  vm_compute. reflexivity.
Qed.

Example endpoint_classification_loses_label :
  Search.classify (SearchRun.dfs parallel unrestricted [1]%positive) 1%positive 2%positive =
    Some Search.Tree.
Proof.
  vm_compute. reflexivity.
Qed.

Example eligible_callback_count :
  snd (Cost.value (SearchRun.run_c diamond count_edge right_branch [1]%positive 0)) = 2.
Proof.
  vm_compute. reflexivity.
Qed.

Definition reject_two :=
  Scope.Make (FinSet.of_list positive_encoding [2%positive]) None.
Definition one_rejected := Fixtures.prepare [1] [1; 2] [(1, 2)].
Definition no_edges := Fixtures.prepare [1] [1; 2] [].

Example rejected_occurrence_has_no_callback :
  snd (Cost.value (SearchRun.run_c one_rejected count_edge reject_two [1]%positive 0)) = 0.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejected_occurrence_still_costs :
  (Cost.ticks (SearchRun.run_c no_edges count_edge reject_two [1]%positive 0%nat) <
    Cost.ticks (SearchRun.run_c one_rejected count_edge reject_two [1]%positive 0%nat))%N.
Proof.
  vm_compute. reflexivity.
Qed.

Definition unknown_target :=
  Prepared.Make (Prepared.graph parallel) (Prepared.node_enc parallel) (Prepared.names parallel)
    (Map.set positive_encoding 1%positive [(10, 99%positive)] Map.empty)
    Map.empty [1]%positive (Prepared.fuel parallel).

Example unknown_cached_target_is_rejected :
  SearchRun.events unknown_target unrestricted [1]%positive =
    [Search.Enter 1 None; Search.Exit 1 None]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

End SearchFixtures.

(** * Public theorem clients

    The clients retain the actual visitor result and the same final core as its complete trace.
    The restricted region admits an unknown ID while excluding the diamond's left branch. *)

Module SearchTheoremClients.
Local Open Scope nat_scope.

Definition scope :=
  Scope.Make FinSet.empty
    (Some (FinSet.of_list positive_encoding [1; 3; 4; 99]%positive)).
Definition roots := [99; 1; 1; 3; 99]%positive.
Definition visitor := @SearchFixtures.count_kinds Fixtures.Edge.
Definition initial_counts := (0, 0, 0, 0).
Definition visitor_run :=
  SearchRun.run_c SearchFixtures.diamond visitor scope roots initial_counts.

(** Readiness comes from the fixture's public preparation contract. *)
Example diamond_ready : Prepared.ready SearchFixtures.diamond.
Proof.
  exact Fixtures.Diamond.fixture_ready.
Qed.

(** The ready-only producer theorem applies to the actual nontrivial visitor run. *)
Example restricted_visitor_exact :
  Search.exact SearchFixtures.diamond scope roots (fst (Cost.value visitor_run)).
Proof.
  apply SearchExact.run_exact. exact diamond_ready.
Qed.

Example restricted_unknown_domain :
  (Scope.admits scope 99%positive, Prepared.name_of SearchFixtures.diamond 99%positive,
    Scope.admits scope 2%positive) = (true, None, false).
Proof.
  vm_compute. reflexivity.
Qed.

Example restricted_visitor_observations :
  (Search.preorder (fst (Cost.value visitor_run)),
    Search.postorder (fst (Cost.value visitor_run)), snd (Cost.value visitor_run)) =
    ([1; 3; 4]%positive, [4; 3; 1]%positive, (2, 0, 0, 0)).
Proof.
  vm_compute. reflexivity.
Qed.

Example restricted_selected_parent :
  Map.get positive_encoding 4%positive
    (Search.parent_edge (fst (Cost.value visitor_run))) = Some ((3, 4), 3%positive).
Proof.
  vm_compute. reflexivity.
Qed.

Example restricted_numbering_observations :
  (Map.get positive_encoding 3%positive (Search.pre_num (fst (Cost.value visitor_run))),
    Map.get positive_encoding 4%positive (Search.pre_num (fst (Cost.value visitor_run))),
    Map.get positive_encoding 3%positive (Search.post_num (fst (Cost.value visitor_run))),
    Map.get positive_encoding 4%positive (Search.post_num (fst (Cost.value visitor_run)))) =
    (Some 2, Some 3, Some 2, Some 1)%positive.
Proof.
  vm_compute. reflexivity.
Qed.

(** The public numbering contract is instantiated at the actual visitor result. *)
Example restricted_numbering_client :
  Map.get positive_encoding 4%positive (Search.pre_num (fst (Cost.value visitor_run))) =
    Some 3%positive <->
  nth_error (Search.preorder (fst (Cost.value visitor_run)))
    (Nat.pred (Pos.to_nat 3%positive)) = Some 4%positive.
Proof.
  exact (Search.pre_num_index _ _ _ _ restricted_visitor_exact 4%positive 3%positive).
Qed.

Example restricted_selected_interval :
  Search.interval (fst (Cost.value visitor_run)) 3%positive 4%positive.
Proof.
  exists 2%positive, 3%positive, 1%positive, 2%positive.
  repeat split; vm_compute; congruence.
Qed.

(** Interval-to-ancestry agreement uses computed membership and ready-only exactness. *)
Example restricted_ancestor_client :
  Search.ancestor (fst (Cost.value visitor_run)) 3%positive 4%positive.
Proof.
  apply (proj1 (Search.ancestor_iff _ _ _ _ restricted_visitor_exact
    3%positive 4%positive ltac:(vm_compute; auto) ltac:(vm_compute; auto))).
  exact restricted_selected_interval.
Qed.

(** The white-path client keeps every source condition indexed by the actual visitor preorder. *)
Example restricted_white_path_client :
  exists es, Search.scoped_path SearchFixtures.diamond scope 1%positive es 4%positive /\
    (4%positive = 1%positive \/
      before (Search.preorder (fst (Cost.value visitor_run))) 1%positive 4%positive) /\
    forall a e b, In e es -> Prepared.arc SearchFixtures.diamond a e b ->
      a = 1%positive \/
        before (Search.preorder (fst (Cost.value visitor_run))) 1%positive a.
Proof.
  assert (Hroot : In 1%positive (Search.preorder (fst (Cost.value visitor_run))))
    by (vm_compute; auto).
  assert (Hjoin : In 4%positive (Search.preorder (fst (Cost.value visitor_run))))
    by (vm_compute; auto).
  apply (proj1 (Search.white_path _ _ _ _ restricted_visitor_exact 1%positive 4%positive
    Hroot Hjoin)).
  apply (proj1 (Search.ancestor_iff _ _ _ _ restricted_visitor_exact 1%positive 4%positive
    Hroot Hjoin)).
  exists 1%positive, 3%positive, 1%positive, 3%positive.
  repeat split; vm_compute; congruence.
Qed.

Example restricted_selected_path :
  SearchOrder.tree_path SearchFixtures.diamond (fst (Cost.value visitor_run)) 4%positive =
    Some [(1, 3); (3, 4)].
Proof.
  vm_compute. reflexivity.
Qed.

(** The trace witness is the same final core that supplies the actual result and selected parent. *)
Example restricted_same_final_core :
  exists final,
    fst (Cost.value visitor_run) = SearchRun.result final /\
    SearchRun.trace_roots SearchFixtures.diamond scope roots SearchRun.initial
      (SearchRun.events SearchFixtures.diamond scope roots) final /\
    Search.ancestor (SearchRun.result final) 3%positive 4%positive /\
    Map.get positive_encoding 4%positive (Search.parent_edge (SearchRun.result final)) =
      Some ((3, 4), 3%positive).
Proof.
  destruct (SearchExact.events_wf SearchFixtures.diamond scope roots diamond_ready)
    as [final [Hresult Htrace]].
  assert (Hactual : fst (Cost.value visitor_run) = SearchRun.result final).
  { transitivity (SearchRun.dfs SearchFixtures.diamond scope roots).
    - apply SearchRun.run_result.
    - exact Hresult. }
  exists final. split; [exact Hactual|]. split; [exact Htrace|].
  rewrite <- Hactual. split; [exact restricted_ancestor_client|exact restricted_selected_parent].
Qed.

Definition root_start : (SearchRun.work Fixtures.Edge * (nat * nat * nat * nat))%type :=
  (([(1%positive, Prepared.succ_edges SearchFixtures.diamond 1%positive)],
    SearchRun.discover 1%positive None SearchRun.initial),
    Visitor.apply visitor (Search.Enter 1%positive None) initial_counts).

(** Adequacy is applied to the actual binary driver and the fixture's own prepared fuel. *)
Example restricted_actual_root_adequacy :
  exists final state,
    Cost.value (iterate (SearchRun.step_c SearchFixtures.diamond visitor scope)
      (Prepared.fuel SearchFixtures.diamond) root_start) = inr (final, state) /\
    fst final = [] /\ SearchInvariant.representation (snd final).
Proof.
  unfold root_start.
  eapply SearchInvariant.root_loop_adequate with (name := 1%nat).
  - exact diamond_ready.
  - apply SearchInvariant.initial_representation.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.

Example restricted_actual_root_observations :
  (match Cost.value (iterate (SearchRun.step_c SearchFixtures.diamond visitor scope)
    (Prepared.fuel SearchFixtures.diamond) root_start) with
  | inl _ => None
  | inr (work, state) => Some (fst work, SearchRun.result (snd work), state)
  end) = Some ([], fst (Cost.value visitor_run), (2, 0, 0, 0)).
Proof.
  vm_compute. reflexivity.
Qed.

End SearchTheoremClients.
