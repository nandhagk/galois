(** * Set union traversal adequacy

    The observer retains the source union and bounds its recorded work.
    For example, an empty second operand shares the first subtree.
    Builds on: CollectionsAuditUnion and trie node adequacy. *)

From Stdlib Require Import List Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsAuditElements CollectionsAuditTrie CollectionsAuditTrieAdequacy
  CollectionsAuditUnion.
(** * Union equations and bounds *)

Lemma audit_union_work_app K (first second : list (audit_union_event K)) :
  audit_finset_union_source_work (first ++ second) =
  audit_finset_union_source_work first + audit_finset_union_source_work second.
Proof.
  induction first as [|event rest IH]; cbn; auto.
  destruct event; cbn; rewrite IH; lia.
Qed.

Lemma audit_union_ne_adequate K (node : Trie.ne (K * unit)) :
  forall other,
    fst (audit_set_union_ne node other) =
      Trie.merge_ne (Trie.union_opt (fun x y => (fst x, (fun v _ => v) (snd x) (snd y))))
        (fun tr => tr) (fun tr => tr) node other /\
    length (snd (audit_set_union_ne node other)) <= 2 * audit_elements_nodes node /\
    audit_finset_union_source_work (snd (audit_set_union_ne node other)) <=
      15 * audit_elements_nodes node.
Proof.
  induction node as [r IHr | v | v r IHr | l IHl | l IHl r IHr | l IHl v |
    l IHl v r IHr]; intros [|other]; cbn [audit_set_union_ne Trie.merge_ne audit_elements_nodes].
  all: try (cbn [audit_finset_union_source_work]; repeat split; lia).
  all: try specialize (IHl (Trie.left (Trie.Nodes other))).
  all: try specialize (IHr (Trie.right (Trie.Nodes other))).
  all: try (destruct (audit_set_union_ne l (Trie.left (Trie.Nodes other))) as [lo le]).
  all: try (destruct (audit_set_union_ne r (Trie.right (Trie.Nodes other))) as [ro re]).
  all: cbn in *; repeat rewrite List.length_app in *; repeat rewrite audit_union_work_app in *;
    cbn in *; unfold audit_set_union_value in *;
    try
    match goal with
    | |- context [audit_trie_node_work ?l ?v ?r] =>
        pose proof (audit_node_bound _ l v r)
    end;
    intuition congruence || lia.
Qed.

(** Set union erases to the original operation. *)
Theorem audit_finset_union_erases : audit_finset_union_erases_statement.
Proof.
  intros K enc [|node] other; cbn [audit_finset_union FinSet.union Map.union_with Trie.union_with
    Trie.merge]; auto.
  destruct (audit_union_ne_adequate K node other) as [H _].
  destruct (audit_set_union_ne node other); exact H.
Qed.

(** Union emits at most two events per left node plus its root. *)
Theorem audit_finset_union_count : audit_finset_union_count_statement.
Proof.
  intros K [|node] other; cbn [audit_finset_union]; cbn; try lia.
  destruct (audit_union_ne_adequate K node other) as [_ [H _]].
  destruct (audit_set_union_ne node other); cbn in *; lia.
Qed.

(** Union source work is bounded by the left node count. *)
Theorem audit_finset_union_source_bound : audit_finset_union_source_bound_statement.
Proof.
  intros K [|node] other; cbn [audit_finset_union audit_trie_nodes
    audit_finset_union_source_work]; cbn; try lia.
  destruct (audit_union_ne_adequate K node other) as [_ [_ H]].
  destruct (audit_set_union_ne node other); cbn in *; lia.
Qed.
