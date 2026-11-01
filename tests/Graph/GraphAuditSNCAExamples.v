(** * Semi-NCA audit examples

    These examples check walk branches and the callback receipts of a forward pass.
    For example, a descending parent walk reaches vertex 1 from vertex 2.
    Builds on: GraphAuditSemiNca and the collection audit models. *)

From Stdlib Require Import List PArith NArith Bool.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditMap CollectionsAuditCompare.
From Galois.Graph Require Import GraphCore GraphDfs GraphSemiDominators GraphSemiNca
  GraphAuditSemiDominators GraphAuditSemiNca.
Import List.ListNotations.

(** * Small graph and callback fixtures *)

(** Missing ranks use the source algorithm's rank-one default. *)
Definition nca_empty_search : dfs_result nat nat :=
  DfsResult [] [] Map.empty Map.empty Map.empty FinSet.empty.

(** The two tree edges build a parent of 2 before the query from 3. *)
Definition nca_search : dfs_result nat nat :=
  DfsResult [2; 3] []
    (Map.set nat_encoding 3 8 (Map.set nat_encoding 2 7 Map.empty))
    (Map.set nat_encoding 3 3%positive
      (Map.set nat_encoding 2 2%positive (Map.set nat_encoding 1 1%positive Map.empty)))
    Map.empty FinSet.empty.

(** Edge 7 starts at 1 and edge 8 starts at 2. *)
Definition nca_graph : Graph.t nat nat :=
  {| Graph.entries := [1];
     Graph.nodes := [1; 2; 3];
     Graph.out := fun v => if Nat.eqb v 1 then [7] else if Nat.eqb v 2 then [8] else [];
     Graph.source := fun e => if Nat.eqb e 7 then 1 else 2;
     Graph.target := fun e => if Nat.eqb e 7 then 2 else 3 |}.

(** Vertex 3 uses vertex 1 as its semidominator. *)
Definition nca_semis : Map.t nat nat := Map.set nat_encoding 3 1 Map.empty.

(** Encoder receipts retain the exact vertex operand. *)
Definition nca_encode (v : nat) : positive * list nat := (encode nat_encoding v, [100 + v]).

(** Source receipts retain the exact edge operand. *)
Definition nca_source (e : nat) : nat * list nat :=
  (Graph.source nca_graph e, [200 + e]).

(** The intermediate parent map makes the descent from 2 to 1 explicit. *)
Definition nca_parents : Map.t nat nat := Map.set nat_encoding 2 1 Map.empty.

(** Recognize a source callback with its edge, result and body. *)
Definition nca_source_receipt (edge vertex body : nat) (event : audit_nca_source_event nat nat nat)
    : bool :=
  match event with
  | NcaSourceSource e v [b] => Nat.eqb e edge && Nat.eqb v vertex && Nat.eqb b body
  | _ => false
  end.

(** Recognize a comparison inside the producer's actual ancestor walk. *)
Definition nca_compare_receipt (event : audit_nca_source_event nat nat nat) : bool :=
  match event with
  | NcaSourceInner (SemiNestedCompare lhs rhs true _) =>
    Pos.eqb lhs 1%positive && Pos.eqb rhs 2%positive
  | _ => false
  end.

(** Recognize the ancestor lookup and the encoder body for vertex 2. *)
Definition nca_parent_receipt (event : audit_nca_source_event nat nat nat) : bool :=
  match event with
  | NcaSourceInner (SemiNestedVertexMap (AuditMapGet key code _ (Some value) [body] _)) =>
    Nat.eqb key 2 && Pos.eqb code (encode nat_encoding 2) && Nat.eqb value 1 && Nat.eqb body 102
  | _ => false
  end.

(** * Boundary walks *)

Example nca_empty_compute :
  nca_compute nat_encoding nca_graph nca_empty_search Map.empty = Map.empty.
Proof.
  reflexivity.
Qed.

Example nca_empty_source_receipt :
  audit_nca_source_run nca_encode nca_source nca_empty_search Map.empty Map.empty
    [NcaSourceCase 2].
Proof.
  constructor.
Qed.

Example nca_threshold_stops :
  audit_nca_walk_run nat_encoding nca_empty_search 1%positive Map.empty 0 0
    [AuditSemiRankGet 0 Map.empty None; AuditSemiLe 1%positive 1%positive true; AuditSemiCase 20].
Proof.
  eapply AuditNcaThreshold with (rank := 1%positive)
    (events := [AuditSemiRankGet 0 Map.empty None]); reflexivity.
Qed.

Example nca_missing_parent_above_threshold :
  audit_nca_walk_run nat_encoding nca_search 1%positive Map.empty 2 2
    [AuditSemiRankGet 2 (pre_num nca_search) (Some 2%positive);
     AuditSemiLe 2%positive 1%positive false; AuditSemiCase 21;
     AuditSemiGet 2 Map.empty None; AuditSemiCase 22].
Proof.
  eapply AuditNcaNoParent with (rank := 2%positive)
    (events := [AuditSemiRankGet 2 (pre_num nca_search) (Some 2%positive)]); reflexivity.
Qed.

Example nca_equal_parent_rank_stops :
  exists events, audit_nca_walk_run nat_encoding nca_search 1%positive
    (Map.set nat_encoding 2 2 Map.empty) 2 2 events /\
    In (AuditSemiLess 2%positive 2%positive false) events.
Proof.
  eexists; split.
  - eapply AuditNcaStop with (a := 2) (ra := 2%positive) (rv := 2%positive); reflexivity.
  - cbn; repeat (first [left; reflexivity|right]).
Qed.

Example nca_source_missing_tree_edge :
  exists events, audit_nca_source_step_run nca_encode nca_source nca_search nca_semis
    Map.empty 1 Map.empty events /\ length events = 2.
Proof.
  eexists; split.
  - apply NcaSourceRoot; reflexivity.
  - reflexivity.
Qed.

Example nca_descending_walk_receipts :
  exists events,
    audit_nca_source_walk_run nca_encode nca_search 1%positive nca_parents 2 1 events /\
    In (SemiNestedCompare 1%positive 2%positive true
      (snd (audit_positive_ltb 1%positive 2%positive))) events /\
    length events = 11.
Proof.
  eexists; split.
  - eapply NcaSourceRecur with (a := 1) (ra := 1%positive) (rv := 2%positive).
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + eapply NcaSourceThreshold; reflexivity.
  - split; [cbn; repeat (first [left; reflexivity|right])|reflexivity].
Qed.

(** * Integrated forward pass *)

Example nca_integrated_source_receipts :
  exists result events,
    audit_nca_source_run nca_encode nca_source nca_search nca_semis result events /\
    Map.get nat_encoding 2 result = Some 1 /\ Map.get nat_encoding 3 result = Some 1 /\
    existsb (nca_source_receipt 7 1 207) events = true /\
    existsb (nca_source_receipt 8 2 208) events = true /\
    existsb nca_parent_receipt events = true /\ existsb nca_compare_receipt events = true /\
    audit_nca_source_body_work (fun n => n) events = 1842 /\
    Nat.leb (audit_nca_source_work (fun n => n) events) (100 * 100) = true.
Proof.
  eexists; eexists; split.
  - unfold audit_nca_source_run; cbn [preorder].
    eapply NcaSourceStepsCons.
    + eapply NcaSourceNode with (edge := 7) (value := None) (limit := 2%positive)
        (origin := 1) (body := [207]) (result := 1).
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * eapply NcaSourceThreshold; reflexivity.
      * reflexivity.
    + eapply NcaSourceStepsCons.
      * eapply NcaSourceNode with (edge := 8) (value := Some 1) (limit := 1%positive)
          (origin := 2) (body := [208]) (result := 1).
        -- reflexivity.
        -- reflexivity.
        -- reflexivity.
        -- reflexivity.
        -- eapply NcaSourceRecur with (a := 1) (ra := 1%positive) (rv := 2%positive).
           ++ reflexivity.
           ++ reflexivity.
           ++ reflexivity.
           ++ reflexivity.
           ++ reflexivity.
           ++ reflexivity.
           ++ eapply NcaSourceThreshold; reflexivity.
        -- reflexivity.
      * constructor.
  - repeat split; reflexivity.
Qed.

(** The large budget is checked in binary, separate from the small receipt computation. *)
Example nca_integrated_input_dimensions :
  audit_nca_compute_width nat_encoding nca_graph nca_search nca_semis = 3 /\
  audit_semi_producer_input_rank nca_search = 3 /\
  64 * S (length (preorder nca_search)) * S (audit_semi_producer_input_rank nca_search) = 768.
Proof.
  repeat split; reflexivity.
Qed.

Example nca_integrated_binary_budget :
  (512 * 769 * 769 + 768 * (512 + 64 * 3) = 303317504)%N.
Proof.
  reflexivity.
Qed.
