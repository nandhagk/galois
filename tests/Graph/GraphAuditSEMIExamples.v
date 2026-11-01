(** * Semidominator audit examples

    These examples check compressed-path branches and the operands in their receipts.
    For example, a root query records the missing shortcut before stopping.
    Builds on: GraphDfs, GraphSemiDominators, GraphAuditSemiDominators and CollectionsAuditMap. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditMap CollectionsAuditCompare.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphSemiDominators
  GraphAuditSemiDominators.
Import List.ListNotations.

(** An empty DFS result makes every rank default to one. *)
Definition semi_empty_search : dfs_result nat nat :=
  DfsResult [] [] Map.empty Map.empty Map.empty FinSet.empty.

(** A two-vertex search gives vertex 1 the smaller discovery number. *)
Definition semi_two_search : dfs_result nat nat :=
  DfsResult [1; 2] [] Map.empty
    (Map.set nat_encoding 2 2%positive (Map.set nat_encoding 1 1%positive Map.empty))
    Map.empty FinSet.empty.

(** The shortcut from vertex 2 reaches vertex 1. *)
Definition semi_two_links : SemiLinks.t nat :=
  SemiLinks.Make Map.empty (Map.set nat_encoding 2 1 Map.empty) Map.empty.

Example semi_empty_root_receipt :
  audit_semi_compress_run nat_encoding semi_empty_search Map.empty semi_links_empty 0
    (semi_links_empty, (0, None))
    [AuditSemiGet 0 Map.empty None; AuditSemiCase 0].
Proof.
  apply AuditSemiCompressRoot; reflexivity.
Qed.

Example semi_equal_rank_stops :
  audit_semi_compress_run nat_encoding semi_empty_search Map.empty semi_two_links 2
    (semi_two_links, (2, None))
    [AuditSemiGet 2 (SemiLinks.shortcut semi_two_links) (Some 1);
     AuditSemiRankGet 1 (pre_num semi_empty_search) None;
     AuditSemiRankGet 2 (pre_num semi_empty_search) None;
     AuditSemiLess 1%positive 1%positive false; AuditSemiCase 1].
Proof.
  eapply AuditSemiCompressStopped with (a := 1) (ra := 1%positive) (rv := 1%positive)
    (ea := [AuditSemiRankGet 1 (pre_num semi_empty_search) None])
    (ev := [AuditSemiRankGet 2 (pre_num semi_empty_search) None]); reflexivity.
Qed.

Example semi_decreasing_rank_receipt :
  audit_semi_compress_run nat_encoding semi_two_search Map.empty semi_two_links 2
    (semi_shortcut_set nat_encoding semi_two_links 2 1 2, (1, Some 2))
    [AuditSemiGet 2 (SemiLinks.shortcut semi_two_links) (Some 1);
     AuditSemiRankGet 1 (pre_num semi_two_search) (Some 1%positive);
     AuditSemiRankGet 2 (pre_num semi_two_search) (Some 2%positive);
     AuditSemiLess 1%positive 2%positive true; AuditSemiCase 2;
     AuditSemiGet 1 (SemiLinks.shortcut semi_two_links) None; AuditSemiCase 0;
     AuditSemiCase 3; AuditSemiGet 2 (SemiLinks.labels semi_two_links) None;
     AuditSemiSet 2 1 (SemiLinks.shortcut semi_two_links);
     AuditSemiSet 2 2 (SemiLinks.labels semi_two_links)].
Proof.
  eapply AuditSemiCompressRecurNone with (a := 1) (ra := 1%positive) (rv := 2%positive)
    (ea := [AuditSemiRankGet 1 (pre_num semi_two_search) (Some 1%positive)])
    (ev := [AuditSemiRankGet 2 (pre_num semi_two_search) (Some 2%positive)])
    (inner := [AuditSemiGet 1 (SemiLinks.shortcut semi_two_links) None; AuditSemiCase 0])
    (label_events := [AuditSemiGet 2 (SemiLinks.labels semi_two_links) None]);
    try reflexivity.
  apply AuditSemiCompressRoot; reflexivity.
Qed.

(** The counted encoder includes its vertex operand in its receipt. *)
Definition semi_recording_encode (v : nat) : positive * list nat :=
  (encode nat_encoding v, [100 + v]).

(** Recognize the operand and encoder body of a rank lookup. *)
Definition semi_rank_receipt (expected : nat) (event : audit_map_event nat positive nat) : bool :=
  match event with
  | AuditMapGet key code _ _ body _ =>
    Nat.eqb expected key && Pos.eqb code (encode nat_encoding expected) &&
      match body with
      | [item] => Nat.eqb item (100 + expected)
      | _ => false
      end
  | _ => false
  end.

Example semi_rank_callback_operand :
  existsb (semi_rank_receipt 2) (snd (audit_map_get semi_recording_encode 2
    (pre_num semi_two_search))) = true /\
  existsb (semi_rank_receipt 1) (snd (audit_map_get semi_recording_encode 2
    (pre_num semi_two_search))) = false.
Proof.
  split; reflexivity.
Qed.

Example semi_counted_comparison_operands :
  fst (audit_positive_ltb 1%positive 2%positive) = true /\
  fst (audit_positive_ltb 2%positive 1%positive) = false.
Proof.
  split; reflexivity.
Qed.

(** A single indexed edge leads from vertex zero to vertex one. *)
Definition semi_one_edge_graph : Graph.t nat nat :=
  {| Graph.entries := [0];
     Graph.nodes := [0; 1];
     Graph.out := fun v => if Nat.eqb v 0 then [7] else [];
     Graph.source := fun _ => 0;
     Graph.target := fun _ => 1 |}.

(** The fixture settles vertex one with edge seven as its tree edge. *)
Definition semi_one_edge_search : dfs_result nat nat :=
  DfsResult [1] [] (Map.set nat_encoding 1 7 Map.empty) Map.empty Map.empty FinSet.empty.

(** The source callback records its edge operand. *)
Definition semi_recording_source (edge : nat) : nat * list nat := (0, [200 + edge]).

Example semi_nested_producer_source_receipt :
  exists result events,
    audit_semi_producer_nested_run semi_recording_encode semi_recording_source
      (prepare nat_encoding semi_one_edge_graph) semi_one_edge_search result events /\
    In (SemiProducerSource 7 0 [207]) events.
Proof.
  eexists; eexists; split.
  - unfold audit_semi_producer_nested_run; cbn [preorder rev].
    eexists; split; [|reflexivity].
    eapply SemiProducerSettlesCons.
    + eapply SemiProducerSettleNode with (edge := 7) (parent := 0)
        (incoming := Some [7]) (edges := [7]).
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * eapply SemiProducerPredsCons.
        -- eapply SemiProducerPredMissing with (vertex := 0) (source_body := [207]).
           ++ reflexivity.
           ++ reflexivity.
        -- constructor.
      * reflexivity.
      * reflexivity.
    + constructor.
  - cbn; repeat (first [left; reflexivity | right]).
Qed.

Example semi_nested_comparison_receipt :
  exists result events,
    audit_semi_nested_compress_run semi_recording_encode semi_two_search Map.empty semi_two_links 2
      result events /\
    In (SemiNestedCompare 1%positive 2%positive true
      (snd (audit_positive_ltb 1%positive 2%positive))) events.
Proof.
  eexists; eexists; split.
  - eapply SemiNestedRecurNone with (a := 1) (ra := 1%positive) (rv := 2%positive)
      (root := 1) (label := 2) (st' := semi_two_links).
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + apply SemiNestedRoot; reflexivity.
    + reflexivity.
    + reflexivity.
  - cbn; repeat (first [left; reflexivity | right]).
Qed.

Example semi_source_body_cost :
  audit_semi_producer_nested_event_work (fun n : nat => n) (SemiProducerSource 7 0 [207]) = 271 /\
  audit_semi_producer_nested_body_event_work (fun n : nat => n)
    (SemiProducerSource 7 0 [207]) = 207.
Proof.
  split; reflexivity.
Qed.

(** Recognize the actual shortcut lookup and its encoder callback body. *)
Definition semi_nested_encoder_receipt (event : audit_semi_nested_event nat nat) : bool :=
  match event with
  | SemiNestedVertexMap (AuditMapGet key code _ _ body _) =>
    Nat.eqb key 2 && Pos.eqb code (encode nat_encoding 2) &&
      match body with
      | [item] => Nat.eqb item 102
      | _ => false
      end
  | _ => false
  end.

Example semi_nested_encoder_operand :
  exists result events,
    audit_semi_nested_compress_run semi_recording_encode semi_two_search Map.empty semi_two_links 2
      result events /\ existsb semi_nested_encoder_receipt events = true.
Proof.
  eexists; eexists; split.
  - eapply SemiNestedRecurNone with (a := 1) (ra := 1%positive) (rv := 2%positive)
      (root := 1) (label := 2) (st' := semi_two_links).
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + apply SemiNestedRoot; reflexivity.
    + reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

Example semi_nested_two_vertex_count :
  exists result events,
    audit_semi_nested_compress_run semi_recording_encode semi_two_search Map.empty semi_two_links 2
      result events /\ length events = 11.
Proof.
  eexists; eexists; split.
  - eapply SemiNestedRecurNone with (a := 1) (ra := 1%positive) (rv := 2%positive)
      (root := 1) (label := 2) (st' := semi_two_links).
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + apply SemiNestedRoot; reflexivity.
    + reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

(** * Recursive label selection *)

(** Three descending ranks force two recursive compression levels. *)
Definition semi_three_search : dfs_result nat nat :=
  DfsResult [1; 2; 3] [] Map.empty
    (Map.set nat_encoding 3 3%positive
      (Map.set nat_encoding 2 2%positive (Map.set nat_encoding 1 1%positive Map.empty)))
    Map.empty FinSet.empty.

(** The chain has shortcuts 3 to 2 and 2 to 1. *)
Definition semi_three_shortcuts : Map.t nat nat :=
  Map.set nat_encoding 3 2 (Map.set nat_encoding 2 1 Map.empty).

(** These labels make the outer score larger than the recursive score. *)
Definition semi_three_choose_inner : SemiLinks.t nat :=
  SemiLinks.Make Map.empty semi_three_shortcuts
    (Map.set nat_encoding 3 3 (Map.set nat_encoding 2 2 Map.empty)).

(** These labels make the outer score smaller than the recursive score. *)
Definition semi_three_choose_outer : SemiLinks.t nat :=
  SemiLinks.Make Map.empty semi_three_shortcuts
    (Map.set nat_encoding 3 1 (Map.set nat_encoding 2 2 Map.empty)).

Example semi_nested_recur_some_chooses_inner :
  exists state events,
    audit_semi_nested_compress_run semi_recording_encode semi_three_search Map.empty
      semi_three_choose_inner 3 (state, (1, Some 2)) events /\
    Map.get nat_encoding 3 (SemiLinks.labels state) = Some 2 /\
    In (SemiNestedCompare 3%positive 2%positive false
      (snd (audit_positive_leb 3%positive 2%positive))) events.
Proof.
  eexists; eexists; split.
  - eapply SemiNestedRecurSome with (a := 2) (ra := 2%positive) (rv := 3%positive)
      (root := 1) (u := 2) (label := 3) (sl := 3%positive) (su := 2%positive)
      (choose := false).
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + eapply SemiNestedRecurNone with (a := 1) (ra := 1%positive) (rv := 2%positive)
        (root := 1) (label := 2) (st' := semi_three_choose_inner).
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
  - split; [reflexivity|].
    cbn; repeat (first [left; reflexivity | right]).
Qed.

Example semi_nested_recur_some_chooses_outer :
  exists state events,
    audit_semi_nested_compress_run semi_recording_encode semi_three_search Map.empty
      semi_three_choose_outer 3 (state, (1, Some 1)) events /\
    Map.get nat_encoding 3 (SemiLinks.labels state) = Some 1 /\
    In (SemiNestedCompare 1%positive 2%positive true
      (snd (audit_positive_leb 1%positive 2%positive))) events.
Proof.
  eexists; eexists; split.
  - eapply SemiNestedRecurSome with (a := 2) (ra := 2%positive) (rv := 3%positive)
      (root := 1) (u := 2) (label := 1) (sl := 1%positive) (su := 2%positive)
      (choose := true).
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + eapply SemiNestedRecurNone with (a := 1) (ra := 1%positive) (rv := 2%positive)
        (root := 1) (label := 2) (st' := semi_three_choose_outer).
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
  - split; [reflexivity|].
    cbn; repeat (first [left; reflexivity | right]).
Qed.

(** * Numbered producer receipts *)

(** The predecessor source is numbered, so the producer invokes compression. *)
Definition semi_numbered_search : dfs_result nat nat :=
  DfsResult [1] [] (Map.set nat_encoding 1 7 Map.empty)
    (Map.set nat_encoding 0 1%positive Map.empty) Map.empty FinSet.empty.

(** Recognize the source callback operand, return value, and body. *)
Definition semi_producer_source_receipt (event : audit_semi_producer_nested_event nat nat nat) :
    bool :=
  match event with
  | SemiProducerSource edge vertex [body] =>
    Nat.eqb edge 7 && Nat.eqb vertex 0 && Nat.eqb body 207
  | _ => false
  end.

(** Recognize the numbered predecessor's rank lookup and encoder callback body. *)
Definition semi_producer_encoder_receipt (event : audit_semi_producer_nested_event nat nat nat) :
    bool :=
  match event with
  | SemiProducerInner (SemiNestedRankMap (AuditMapGet key code _ (Some rank) [body] _)) =>
    Nat.eqb key 0 && Pos.eqb code (encode nat_encoding 0) && Pos.eqb rank 1%positive &&
      Nat.eqb body 100
  | _ => false
  end.

(** Recognize the score comparison performed by the numbered predecessor. *)
Definition semi_producer_comparison_receipt (event : audit_semi_producer_nested_event nat nat nat) :
    bool :=
  match event with
  | SemiProducerInner (SemiNestedCompare first second result _) =>
    Pos.eqb first 1%positive && Pos.eqb second 1%positive && result
  | _ => false
  end.

(** Recognize the root case within the producer's compression query. *)
Definition semi_producer_compression_receipt
    (event : audit_semi_producer_nested_event nat nat nat) : bool :=
  match event with
  | SemiProducerInner (SemiNestedCase 0) => true
  | _ => false
  end.

(** Recognize adjacent source and numbered-rank callbacks from the predecessor step. *)
Definition semi_producer_pred_callbacks_receipt
    (pair : audit_semi_producer_nested_event nat nat nat *
      audit_semi_producer_nested_event nat nat nat) : bool :=
  match pair with
  | (SemiProducerSource edge vertex [source_body],
      SemiProducerInner (SemiNestedRankMap (AuditMapGet key code _ (Some rank) [encode_body] _))) =>
    Nat.eqb edge 7 && Nat.eqb vertex 0 && Nat.eqb source_body 207 && Nat.eqb key 0 &&
      Pos.eqb code (encode nat_encoding 0) && Pos.eqb rank 1%positive && Nat.eqb encode_body 100
  | _ => false
  end.

(** Recognize the selected-value read immediately after the compression step. *)
Definition semi_producer_value_read_receipt
    (pair : audit_semi_producer_nested_event nat nat nat *
      audit_semi_producer_nested_event nat nat nat) : bool :=
  match pair with
  | (SemiProducerCase 2,
      SemiProducerInner (SemiNestedVertexMap (AuditMapGet key code _ None [body] _))) =>
    Nat.eqb key 0 && Pos.eqb code (encode nat_encoding 0) && Nat.eqb body 100
  | _ => false
  end.

Example semi_numbered_producer_same_run_receipts :
  exists result events,
    audit_semi_producer_nested_run semi_recording_encode semi_recording_source
      (prepare nat_encoding semi_one_edge_graph) semi_numbered_search result events /\
    Map.get nat_encoding 1 (SemiState.result result) = Some 0 /\
    existsb semi_producer_source_receipt events = true /\
    existsb semi_producer_encoder_receipt events = true /\
    existsb semi_producer_comparison_receipt events = true /\
    existsb semi_producer_compression_receipt events = true /\
    existsb semi_producer_pred_callbacks_receipt (combine events (tl events)) = true /\
    existsb semi_producer_value_read_receipt (combine events (tl events)) = true.
Proof.
  eexists; eexists; split.
  - unfold audit_semi_producer_nested_run; cbn [preorder rev].
    eexists; split; [|reflexivity].
    eapply SemiProducerSettlesCons.
    + eapply SemiProducerSettleNode with (edge := 7) (parent := 0)
        (incoming := Some [7]) (edges := [7]).
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * eapply SemiProducerPredsCons.
        -- eapply SemiProducerPredNumbered with (vertex := 0) (source_body := [207])
             (number := 1%positive) (st' := semi_links_empty) (root := 0) (part := None)
             (u := 0) (value := None) (best_rank := 1%positive) (value_rank := 1%positive)
             (choose := true).
           ++ reflexivity.
           ++ reflexivity.
           ++ apply SemiNestedRoot; reflexivity.
           ++ reflexivity.
           ++ reflexivity.
           ++ reflexivity.
           ++ reflexivity.
           ++ reflexivity.
        -- constructor.
      * reflexivity.
      * reflexivity.
    + constructor.
  - repeat split; reflexivity.
Qed.
