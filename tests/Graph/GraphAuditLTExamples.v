(** * Lengauer--Tarjan audit examples

    These examples exercise bucket indexing, correction and captured callback operands.
    For example, a missing provisional parent leaves the correction map untouched.
    Builds on: GraphAuditLengauerTarjan and the graph and collection models. *)

From Stdlib Require Import List PArith NArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsTrie
  CollectionsAuditMap CollectionsAuditCompare.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphSemiDominators
  GraphLengauerTarjan GraphDominators
  GraphAuditSemiDominators GraphAuditLengauerTarjan.
Import List.ListNotations.

(** The callback records the key that was encoded. *)
Definition lt_example_encode (v : nat) : positive * list nat :=
  (encode nat_encoding v, [100 + v]).

(** The source callback records the edge it receives. *)
Definition lt_example_source (edge : nat) : nat * list nat := (0, [200 + edge]).

(** A single tree edge links vertex one to vertex zero. *)
Definition lt_example_search : dfs_result nat nat :=
  DfsResult [1] [] (Map.set nat_encoding 1 7 Map.empty) Map.empty Map.empty FinSet.empty.

(** A one-row semidominator map sends vertex one to bucket zero. *)
Definition lt_example_semis : Map.t nat nat := Map.set nat_encoding 1 0 Map.empty.

Example lt_empty_buckets :
  audit_lt_buckets_counted (E := nat) nat_encoding Map.empty [] Map.empty =
    (Map.empty, [AuditLtCase 0]).
Proof.
  reflexivity.
Qed.

Example lt_bucket_missing_and_present :
  fst (audit_lt_buckets_counted (E := nat) nat_encoding lt_example_semis [0; 1] Map.empty) =
    Map.set nat_encoding 0 [1] Map.empty /\
  length (snd (audit_lt_buckets_counted (E := nat) nat_encoding lt_example_semis [0; 1]
    Map.empty)) = 9.
Proof.
  split; reflexivity.
Qed.

Example lt_correction_missing :
  audit_lt_correct_counted (E := nat) nat_encoding Map.empty Map.empty Map.empty 1 =
    (Map.empty, [AuditLtInner (AuditSemiGet 1 Map.empty None); AuditLtCase 11]).
Proof.
  reflexivity.
Qed.

Example lt_correction_equal_and_deferred :
  fst (audit_lt_correct_counted (E := nat) nat_encoding lt_example_semis
    (Map.set nat_encoding 1 0 Map.empty) Map.empty 1) = Map.set nat_encoding 1 0 Map.empty /\
  fst (audit_lt_correct_counted (E := nat) nat_encoding Map.empty
    (Map.set nat_encoding 1 0 Map.empty) (Map.set nat_encoding 0 2 Map.empty) 1) =
    Map.set nat_encoding 1 2 (Map.set nat_encoding 0 2 Map.empty).
Proof.
  split; reflexivity.
Qed.

Example lt_nested_source_receipt :
  exists result events,
    audit_lt_nested_reverse_run lt_example_encode lt_example_source lt_example_search
      lt_example_semis Map.empty (LtState.Make semi_links_empty Map.empty) 1 result events /\
    In (LtNestedSource 7 0 [207]) events.
Proof.
  eexists; eexists; split.
  - eapply LtNestedReverseNode with (edge := 7) (parent := 0) (source_body := [207])
      (members := []) (settled := LtState.Make semi_links_empty Map.empty).
    + reflexivity.
    + reflexivity.
    + constructor.
    + reflexivity.
    + reflexivity.
    + reflexivity.
  - cbn; repeat (first [left; reflexivity | right]).
Qed.

Example lt_source_body_work :
  audit_lt_nested_event_work (fun n : nat => n) (LtNestedSource 7 0 [207]) = 271 /\
  audit_lt_nested_body_event_work (fun n : nat => n) (LtNestedSource 7 0 [207]) = 207.
Proof.
  split; reflexivity.
Qed.

(** Vertex two reaches the lower-ranked vertex one during bucket settlement. *)
Definition lt_recursive_search : dfs_result nat nat :=
  DfsResult [1; 2] [] Map.empty
    (Map.set nat_encoding 2 2%positive (Map.set nat_encoding 1 1%positive Map.empty))
    Map.empty FinSet.empty.

(** The linked state makes the settlement recurse before selecting a label. *)
Definition lt_recursive_state : LtState.t nat :=
  LtState.Make (SemiLinks.Make Map.empty (Map.set nat_encoding 2 1 Map.empty) Map.empty) Map.empty.

Example lt_nested_member_recursive_comparison :
  exists result events,
    audit_lt_nested_member_run lt_example_encode lt_recursive_search Map.empty 1
      lt_recursive_state 2 result events /\
    In (LtNestedSemi (SemiNestedCompare 1%positive 2%positive true
      (snd (audit_positive_ltb 1%positive 2%positive)))) events.
Proof.
  eexists; eexists; split.
  - eapply LtNestedMember with (root := 1) (part := Some 2) (u := 2)
      (links := semi_shortcut_set nat_encoding (LtState.links lt_recursive_state) 2 1 2)
      (score := 2%positive) (rank := 1%positive) (choose := false).
    + eapply SemiNestedRecurNone with (a := 1) (ra := 1%positive) (rv := 2%positive)
        (root := 1) (label := 2) (st' := LtState.links lt_recursive_state).
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * apply SemiNestedRoot; reflexivity.
      * reflexivity.
      * reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
  - cbn; repeat (first [left; reflexivity | right]).
Qed.

(** A self-bucket forces the integrated producer to settle a member before its tree link. *)
Definition lt_self_semis : Map.t nat nat := Map.set nat_encoding 1 1 Map.empty.

(** Recognize the bucket-building lookup together with its encoder callback body. *)
Definition lt_semis_receipt (event : audit_lt_nested_event nat nat nat) : bool :=
  match event with
  | LtNestedSemi (SemiNestedVertexMap (AuditMapGet key code _ _ body _)) =>
    Nat.eqb key 1 && Pos.eqb code (encode nat_encoding 1) &&
      match body with
      | [item] => Nat.eqb item 101
      | _ => false
      end
  | _ => false
  end.

Example lt_nested_complete_source_receipt :
  exists events,
    audit_lt_nested_run lt_example_encode lt_example_source lt_example_search lt_self_semis
      (Map.set nat_encoding 1 1 Map.empty) events /\
    In (LtNestedSource 7 0 [207]) events /\ existsb lt_semis_receipt events = true.
Proof.
  eexists; split.
  - unfold audit_lt_nested_run; cbn [preorder rev].
    eexists; eexists; split.
    + eapply LtNestedReverseCons.
      * eapply LtNestedReverseNode with (edge := 7) (parent := 0) (source_body := [207])
          (members := [1]).
        -- reflexivity.
        -- reflexivity.
        -- eapply LtNestedMembersCons.
           ++ eapply LtNestedMember with (root := 1) (part := None) (u := 1)
                (score := 1%positive) (rank := 1%positive) (choose := false).
              ** apply SemiNestedRoot; reflexivity.
              ** reflexivity.
              ** reflexivity.
              ** reflexivity.
              ** reflexivity.
              ** reflexivity.
           ++ constructor.
        -- reflexivity.
        -- reflexivity.
        -- reflexivity.
      * constructor.
    + split; reflexivity.
  - split.
    + cbn; repeat (first [left; reflexivity | right]).
    + reflexivity.
Qed.

(** This binary calculation checks the coefficient formula without expanding the unary budget. *)
Example lt_one_vertex_binary_budget_arithmetic :
  (512 * 1601 * 1601 + 1600 * (512 + 64 * 2) = 1313382912)%N.
Proof.
  vm_compute; reflexivity.
Qed.

(** The source graph supplies the edge source used by the one-vertex receipt. *)
Definition lt_example_graph : Graph.t nat nat :=
  {| Graph.entries := [1];
     Graph.nodes := [0; 1];
     Graph.out := fun _ => [];
     Graph.source := fun _ => 0;
     Graph.target := fun _ => 1 |}.

Example lt_one_vertex_input_dimensions :
  audit_lt_nested_input_event_bound lt_example_search = 1600 /\
  audit_lt_nested_input_width nat_encoding lt_example_graph lt_example_search lt_self_semis = 2.
Proof.
  vm_compute; split; reflexivity.
Qed.

(** This malformed row stores key seven at the encoded position of vertex one. *)
Definition lt_malformed_semis : Map.t nat nat :=
  Trie.set (encode nat_encoding 1) (7, 0) Trie.empty.

Example lt_malformed_bucket_lookup_receipt :
  audit_lt_buckets_counted (E := nat) nat_encoding lt_malformed_semis [1] Map.empty =
    (Map.set nat_encoding 0 [1] Map.empty,
     [AuditLtCase 1; AuditLtInner (AuditSemiGet 1 lt_malformed_semis (Some 0)); AuditLtCase 3;
      AuditLtBucketGet 0 Map.empty None; AuditLtBucketSet 0 [1] Map.empty; AuditLtCase 0]).
Proof.
  reflexivity.
Qed.

(** The small equal-parent correction records seven operations and five encoder bodies. *)
Example lt_small_correction_actual_work :
  let events := snd (audit_lt_nested_correct (E := nat) lt_example_encode lt_self_semis
    (Map.set nat_encoding 1 1 Map.empty) Map.empty 1) in
  length events = 7 /\ audit_lt_nested_work (fun n : nat => n) events = 1204 /\
  audit_lt_nested_body_work (fun n : nat => n) events = 505.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** A reachable edge gives vertex one the immediate dominator zero. *)
Definition lt_one_edge_graph : Graph.t nat nat :=
  {| Graph.entries := [0];
     Graph.nodes := [0; 1];
     Graph.out := fun v => if Nat.eqb v 0 then [7] else [];
     Graph.source := fun _ => 0;
     Graph.target := fun _ => 1 |}.

Example lt_producer_accepted_by_independent_checker :
  let p := prepare nat_encoding lt_one_edge_graph in
  Map.get nat_encoding 1 (simple_lt_idom p) = Some 0 /\
  check_idom p (simple_lt_idom p) = true /\ check_idom p Map.empty = false.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.
