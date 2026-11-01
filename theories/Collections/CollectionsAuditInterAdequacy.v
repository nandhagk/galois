(** * Set intersection traversal adequacy

    The counted intersection retains the source filtering and merge operations.
    For example, intersecting with empty still visits and discards the other tree.
    Builds on: CollectionsAuditInter and trie node adequacy. *)

From Stdlib Require Import List Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsAuditElements CollectionsAuditTrie CollectionsAuditTrieAdequacy
  CollectionsAuditInter.

(** * Intersection equations and bounds *)

Lemma audit_inter_work_app K (first second : list (audit_inter_event K)) :
  audit_finset_inter_source_work (first ++ second) =
    audit_finset_inter_source_work first + audit_finset_inter_source_work second.
Proof.
  induction first as [|event rest IH]; cbn; auto.
  destruct event; cbn; rewrite IH; lia.
Qed.

Lemma audit_inter_drop_ne_adequate K (node : Trie.ne (K * unit)) :
  fst (audit_inter_drop_ne node) = Trie.filter_ne (fun _ => None) node /\
  length (snd (audit_inter_drop_ne node)) <= 3 * audit_elements_nodes node /\
  audit_finset_inter_source_work (snd (audit_inter_drop_ne node)) <=
    18 * audit_elements_nodes node.
Proof.
  induction node as [r IHr | v | v r IHr | l IHl | l IHl r IHr | l IHl v |
    l IHl v r IHr]; cbn [audit_inter_drop_ne Trie.filter_ne audit_elements_nodes].
  all: try (destruct (audit_inter_drop_ne l) as [lo le]).
  all: try (destruct (audit_inter_drop_ne r) as [ro re]).
  all: try destruct IHl as [Hl [Hlc Hlw]]; try destruct IHr as [Hr [Hrc Hrw]].
  all: try rewrite <- Hl; try rewrite <- Hr.
  all: try destruct lo; try destruct ro.
  all: cbn in *; repeat rewrite List.length_app in *; repeat rewrite audit_inter_work_app in *;
    cbn in *; try
    match goal with
    | |- context [audit_trie_node_work ?l ?v ?r] =>
      pose proof (audit_node_bound _ l v r)
    end; repeat rewrite List.length_app in *; repeat rewrite audit_inter_work_app in *;
    cbn in *; intuition congruence || lia.
Qed.

Lemma audit_inter_drop_adequate K (input : FinSet.t K) :
  fst (audit_inter_drop input) = Trie.filter_map (fun _ => None) input /\
  length (snd (audit_inter_drop input)) <= 3 * audit_trie_nodes input /\
  audit_finset_inter_source_work (snd (audit_inter_drop input)) <= 18 * audit_trie_nodes input.
Proof.
  destruct input as [|node]; cbn [audit_inter_drop Trie.filter_map audit_trie_nodes].
  - cbn; repeat split; reflexivity.
  - apply audit_inter_drop_ne_adequate.
Qed.

Lemma audit_inter_children K (node : Trie.ne (K * unit)) :
  audit_trie_nodes (Trie.left (Trie.Nodes node)) +
    audit_trie_nodes (Trie.right (Trie.Nodes node)) < audit_elements_nodes node.
Proof.
  destruct node; cbn [Trie.left Trie.right audit_trie_nodes audit_elements_nodes]; lia.
Qed.

Definition audit_inter_original_value {K} : option (K * unit) -> option (K * unit) ->
    option (K * unit) :=
  Map.combine_pair (fun a b =>
    match a, b with
    | Some _, Some _ => Some tt
    | _, _ => None
    end).

Lemma audit_inter_value_adequate K (a b : option (K * unit)) :
  fst (audit_inter_value a b) = audit_inter_original_value a b.
Proof.
  destruct a as [[k []]|], b as [[j []]|]; reflexivity.
Qed.

Lemma audit_inter_merge_ne_adequate K (node : Trie.ne (K * unit)) :
  forall other,
    fst (audit_inter_merge_ne node other) =
      Trie.merge_ne audit_inter_original_value (Trie.filter_map (fun _ => None))
        (Trie.filter_map (fun _ => None)) node other /\
    length (snd (audit_inter_merge_ne node other)) <=
      6 * (audit_elements_nodes node + audit_trie_nodes other) /\
    audit_finset_inter_source_work (snd (audit_inter_merge_ne node other)) <=
      30 * (audit_elements_nodes node + audit_trie_nodes other).
Proof.
  induction node as [r IHr | v | v r IHr | l IHl | l IHl r IHr | l IHl v |
    l IHl v r IHr]; intros [|other]; cbn [audit_inter_merge_ne Trie.merge_ne].
  all: try
    match goal with
    | |- context [audit_inter_drop_ne ?n] =>
      pose proof (audit_inter_drop_ne_adequate K n) as Hdrop;
      destruct (audit_inter_drop_ne n) as [o e]
    end.
  all: cbn [Trie.filter_map audit_trie_nodes audit_elements_nodes] in *.
  all: try (cbn in Hdrop |- *; intuition congruence || lia).
  all: pose proof (audit_inter_children K other) as Hchildren.
  all: try specialize (IHl (Trie.left (Trie.Nodes other))).
  all: try specialize (IHr (Trie.right (Trie.Nodes other))).
  all: pose proof (audit_inter_drop_adequate K (Trie.left (Trie.Nodes other))) as Hleft.
  all: pose proof (audit_inter_drop_adequate K (Trie.right (Trie.Nodes other))) as Hright.
  all: try (destruct (audit_inter_merge_ne l (Trie.left (Trie.Nodes other))) as [lo le]).
  all: try (destruct (audit_inter_merge_ne r (Trie.right (Trie.Nodes other))) as [ro re]).
  all: try (destruct (audit_inter_drop (Trie.left (Trie.Nodes other))) as [lo le]).
  all: try (destruct (audit_inter_drop (Trie.right (Trie.Nodes other))) as [ro re]).
  all: unfold audit_inter_value; cbn.
  all: cbn in *; repeat rewrite List.length_app in *; repeat rewrite audit_inter_work_app in *;
    cbn in *; repeat rewrite List.length_app in *; repeat rewrite audit_inter_work_app in *;
    cbn in *.
  all: try destruct IHl as [IHle [IHlc IHlw]]; try destruct IHr as [IHre [IHrc IHrwork]].
  all: destruct Hleft as [Hle [Hlc Hlw]]; destruct Hright as [Hre [Hrc Hrw]].
  all: try rewrite <- IHle; try rewrite <- IHre; try rewrite <- Hle; try rewrite <- Hre.
  all: try
    match goal with
    | |- context [audit_trie_node_work ?l ?v ?r] =>
      pose proof (audit_node_bound _ l v r)
    end.
  all: try destruct lo; try destruct ro; cbn in *;
    destruct other; cbn in *;
    unfold audit_inter_original_value, Map.combine_pair in *; cbn in *;
    intuition congruence || lia.
Qed.

Lemma audit_inter_filter_none K (input : FinSet.t K)
    (f : K * unit -> option (K * unit)) (Hf : forall x, f x = None) :
  Trie.filter_map f input = Trie.filter_map (fun _ => None) input.
Proof.
  destruct input as [|node]; cbn [Trie.filter_map]; try reflexivity.
  induction node as [r IHr | v | v r IHr | l IHl | l IHl r IHr | l IHl v |
    l IHl v r IHr]; cbn [Trie.filter_ne]; rewrite ?IHl, ?IHr, ?Hf; reflexivity.
Qed.

Lemma audit_inter_merge_filter_agrees K (node : Trie.ne (K * unit)) :
  forall other left right,
    (forall t, left t = Trie.filter_map (fun _ => None) t) ->
    (forall t, right t = Trie.filter_map (fun _ => None) t) ->
    Trie.merge_ne audit_inter_original_value left right node other =
      Trie.merge_ne audit_inter_original_value (Trie.filter_map (fun _ => None))
        (Trie.filter_map (fun _ => None)) node other.
Proof.
  induction node as [r IHr | v | v r IHr | l IHl | l IHl r IHr | l IHl v |
    l IHl v r IHr]; intros [|other] left right Hleft Hright;
    cbn [Trie.merge_ne]; rewrite ?Hleft, ?Hright, ?IHl, ?IHr; auto.
Qed.

(** Intersection erases to the original set intersection. *)
Theorem audit_finset_inter_erases : audit_finset_inter_erases_statement.
Proof.
  intros K enc [|node] other; unfold audit_finset_inter, FinSet.inter, Map.combine, Trie.combine,
    Trie.merge.
  - pose proof (audit_inter_drop_adequate K other) as [H _].
    destruct (audit_inter_drop other); cbn in *; rewrite audit_inter_filter_none;
      [exact H | intros [k []]; reflexivity].
  - pose proof (audit_inter_merge_ne_adequate K node other) as [H _].
    destruct (audit_inter_merge_ne node other); cbn in *;
      rewrite audit_inter_merge_filter_agrees;
      [exact H | intros tree; apply audit_inter_filter_none; intros [k []]; reflexivity |
       intros tree; apply audit_inter_filter_none; intros [k []]; reflexivity].
Qed.

(** Intersection emits at most six events per input node plus its root. *)
Theorem audit_finset_inter_count : audit_finset_inter_count_statement.
Proof.
  intros K [|node] other; unfold audit_finset_inter; cbn [audit_trie_nodes].
  - pose proof (audit_inter_drop_adequate K other) as [_ [H _]].
    destruct (audit_inter_drop other); cbn in *; lia.
  - pose proof (audit_inter_merge_ne_adequate K node other) as [_ [H _]].
    destruct (audit_inter_merge_ne node other); cbn in *; lia.
Qed.

(** Intersection source work is bounded by both input node counts. *)
Theorem audit_finset_inter_source_bound : audit_finset_inter_source_bound_statement.
Proof.
  intros K [|node] other; unfold audit_finset_inter; cbn [audit_trie_nodes].
  - pose proof (audit_inter_drop_adequate K other) as [_ [_ H]].
    destruct (audit_inter_drop other); cbn in *; lia.
  - pose proof (audit_inter_merge_ne_adequate K node other) as [_ [_ H]].
    destruct (audit_inter_merge_ne node other); cbn in *; lia.
Qed.
