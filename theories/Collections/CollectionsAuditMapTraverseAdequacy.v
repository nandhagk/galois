(** * Map transformation and union traversal adequacy

    Counted traversals retain callback values and bound their source-frame work.
    For example, a missing union operand shares its corresponding subtree.
    Builds on: CollectionsAuditMapTraverse and trie node adequacy. *)

From Stdlib Require Import List Lia.
From Galois.Collections Require Import CollectionsTrie CollectionsMap CollectionsAuditElements
  CollectionsAuditTrie CollectionsAuditTrieAdequacy CollectionsAuditMapTraverse.
(** * Transformation and union equations and bounds *)

Lemma audit_transform_work_app K V W E work
    (first second : list (audit_map_transform_event K V W E)) :
  audit_map_transform_source_work work (first ++ second) =
    audit_map_transform_source_work work first + audit_map_transform_source_work work second /\
  audit_map_transform_child_work work (first ++ second) =
    audit_map_transform_child_work work first + audit_map_transform_child_work work second.
Proof.
  induction first as [|event rest IH]; cbn; try (split; lia).
  destruct event; cbn in *; destruct IH; split; lia.
Qed.

Lemma audit_transform_ne_adequate K V W E (f : V -> W * list E) original work
    (Hf : forall v, fst (f v) = original v) (node : Trie.ne (K * V)) :
  fst (audit_map_transform_ne f node) =
    Trie.filter_ne (fun kv => Some (fst kv, original (snd kv))) node /\
  length (snd (audit_map_transform_ne f node)) <= 3 * audit_elements_nodes node /\
  audit_map_transform_source_work work (snd (audit_map_transform_ne f node)) <=
    18 * audit_elements_nodes node +
    audit_map_transform_child_work work (snd (audit_map_transform_ne f node)).
Proof.
  induction node as [r IHr | [k v] | [k v] r IHr | l IHl | l IHl r IHr |
    l IHl [k v] | l IHl [k v] r IHr];
    cbn [audit_map_transform_ne Trie.filter_ne audit_elements_nodes].
  all: try (destruct (audit_map_transform_ne f l) as [lo le]).
  all: try (destruct (audit_map_transform_ne f r) as [ro re]).
  all: try (pose proof (Hf v) as Hcall; destruct (f v) as [value ce]).
  all: cbn in *; repeat rewrite List.length_app in *;
    repeat rewrite (proj1 (audit_transform_work_app _ _ _ _ _ _ _)) in *;
    repeat rewrite (proj2 (audit_transform_work_app _ _ _ _ _ _ _)) in *; cbn in *.
  all: try destruct IHl as [Hl [Hlc Hlw]]; try destruct IHr as [Hr [Hrc Hrw]].
  all: try rewrite <- Hl; try rewrite <- Hr; try rewrite <- Hcall.
  all: try destruct lo; try destruct ro; cbn in *;
    repeat rewrite List.length_app in *;
    repeat rewrite (proj1 (audit_transform_work_app _ _ _ _ _ _ _)) in *;
    repeat rewrite (proj2 (audit_transform_work_app _ _ _ _ _ _ _)) in *;
    cbn in *; intuition congruence || lia.
Qed.

(** Transformation erases to the original map operation. *)
Theorem audit_map_transform_erases : audit_map_transform_erases_statement.
Proof.
  intros K V W E f original [|node] Hf; cbn [audit_map_transform Map.map Trie.map Trie.filter_map].
  - reflexivity.
  - exact (proj1 (audit_transform_ne_adequate K V W E f original (fun _ => 0) Hf node)).
Qed.

(** Transformation emits at most three events per input node. *)
Theorem audit_map_transform_count : audit_map_transform_count_statement.
Proof.
  intros K V W E f node.
  exact (proj1 (proj2 (audit_transform_ne_adequate K V W E f (fun v => fst (f v))
    (fun _ => 0) (fun _ => eq_refl) node))).
Qed.

(** Transformation work includes the retained callback executions. *)
Theorem audit_map_transform_source_bound : audit_map_transform_source_bound_statement.
Proof.
  intros K V W E f work [|node]; cbn [audit_map_transform audit_trie_nodes]; cbn; try lia.
  exact (proj2 (proj2 (audit_transform_ne_adequate K V W E f (fun v => fst (f v))
    work (fun _ => eq_refl) node))).
Qed.

Lemma audit_map_union_work_app K V E work (first second : list (audit_map_union_event K V E)) :
  audit_map_union_source_work work (first ++ second) =
    audit_map_union_source_work work first + audit_map_union_source_work work second /\
  audit_map_union_child_work work (first ++ second) =
    audit_map_union_child_work work first + audit_map_union_child_work work second.
Proof.
  induction first as [|event rest IH]; cbn; try (split; lia).
  destruct event; cbn in *; destruct IH; split; lia.
Qed.

Lemma audit_map_union_value_adequate K V E (f : V -> V -> V * list E) original work
    (Hf : forall x y, fst (f x y) = original x y) (a b : option (K * V)) :
  fst (audit_map_union_value f a b) =
    Trie.union_opt (fun x y => (fst x, original (snd x) (snd y))) a b /\
  length (snd (audit_map_union_value f a b)) <= 1 /\
  audit_map_union_source_work work (snd (audit_map_union_value f a b)) <=
    3 + audit_map_union_child_work work (snd (audit_map_union_value f a b)).
Proof.
  destruct a as [[ka va]|], b as [[kb vb]|]; cbn [audit_map_union_value Trie.union_opt].
  - pose proof (Hf va vb) as Hcall; destruct (f va vb) as [out events]; cbn in *.
    intuition congruence || lia.
  - cbn; repeat split; try reflexivity; lia.
  - cbn; repeat split; try reflexivity; lia.
  - cbn; repeat split; try reflexivity; lia.
Qed.

Lemma audit_map_union_ne_adequate K V E (f : V -> V -> V * list E) original work
    (Hf : forall x y, fst (f x y) = original x y) (node : Trie.ne (K * V)) :
  forall other,
    fst (audit_map_union_ne f node other) =
      Trie.merge_ne (Trie.union_opt (fun x y => (fst x, original (snd x) (snd y))))
        (fun tr => tr) (fun tr => tr) node other /\
    length (snd (audit_map_union_ne f node other)) <= 3 * audit_elements_nodes node /\
    audit_map_union_source_work work (snd (audit_map_union_ne f node other)) <=
      18 * audit_elements_nodes node +
      audit_map_union_child_work work (snd (audit_map_union_ne f node other)).
Proof.
  induction node as [r IHr | v | v r IHr | l IHl | l IHl r IHr | l IHl v |
    l IHl v r IHr]; intros [|other]; cbn [audit_map_union_ne Trie.merge_ne audit_elements_nodes].
  all: try (cbn [audit_map_union_source_work audit_map_union_child_work]; cbn;
    repeat split; try reflexivity; lia).
  all: try specialize (IHl (Trie.left (Trie.Nodes other))).
  all: try specialize (IHr (Trie.right (Trie.Nodes other))).
  all: try (destruct (audit_map_union_ne f l (Trie.left (Trie.Nodes other))) as [lo le]).
  all: try (destruct (audit_map_union_ne f r (Trie.right (Trie.Nodes other))) as [ro re]).
  all:
    match goal with
    | |- context [audit_map_union_value ?callback ?a ?b] =>
      pose proof (audit_map_union_value_adequate K V E callback original work Hf a b) as Hvalue;
      destruct (audit_map_union_value callback a b) as [vo ve]
    end.
  all: cbn in *; repeat rewrite List.length_app in *;
    repeat rewrite (proj1 (audit_map_union_work_app _ _ _ _ _ _)) in *;
    repeat rewrite (proj2 (audit_map_union_work_app _ _ _ _ _ _)) in *; cbn in *.
  all: try destruct IHl as [Hl [Hlc Hlw]]; try destruct IHr as [Hr [Hrc Hrw]].
  all: destruct Hvalue as [Hv [Hvc Hvw]].
  all: try rewrite <- Hl; try rewrite <- Hr; try rewrite <- Hv.
  all: try destruct lo; try destruct ro; destruct vo; destruct other; cbn in *;
    repeat rewrite List.length_app in *;
    repeat rewrite (proj1 (audit_map_union_work_app _ _ _ _ _ _)) in *;
    repeat rewrite (proj2 (audit_map_union_work_app _ _ _ _ _ _)) in *;
    cbn in *; intuition congruence || lia.
Qed.

(** Union erases to the original map union with the corresponding callback. *)
Theorem audit_map_union_erases : audit_map_union_erases_statement.
Proof.
  intros K V E f original [|node] other Hf;
    cbn [audit_map_union Map.union_with Trie.union_with Trie.merge]; auto.
  pose proof (audit_map_union_ne_adequate K V E f original (fun _ => 0) Hf node other) as [H _].
  destruct (audit_map_union_ne f node other); exact H.
Qed.

(** Union emits at most three events per left node plus its root. *)
Theorem audit_map_union_count : audit_map_union_count_statement.
Proof.
  intros K V E f [|node] other; cbn [audit_map_union]; cbn; try lia.
  pose proof (audit_map_union_ne_adequate K V E f (fun x y => fst (f x y)) (fun _ => 0)
    (fun _ _ => eq_refl) node other) as [_ [H _]].
  destruct (audit_map_union_ne f node other); cbn in *; lia.
Qed.

(** Union source work includes the retained callback executions. *)
Theorem audit_map_union_source_bound : audit_map_union_source_bound_statement.
Proof.
  intros K V E f work [|node] other; cbn [audit_map_union audit_trie_nodes]; cbn; try lia.
  pose proof (audit_map_union_ne_adequate K V E f (fun x y => fst (f x y)) work
    (fun _ _ => eq_refl) node other) as [_ [_ H]].
  destruct (audit_map_union_ne f node other); cbn in *; lia.
Qed.
