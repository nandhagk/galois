(** * Enumeration traversal adequacy

    Counted enumeration preserves the trie, map and set results and bounds its work.
    For example, a singleton emits one binding and traverses it once per projection.
    Builds on: CollectionsAuditElements. *)

From Stdlib Require Import List PArith Lia.
From Galois.Collections Require Import CollectionsTrie CollectionsMap CollectionsFinSet
  CollectionsAuditElements.
Import List.ListNotations.
(** * Traversal equations and bounds *)

Lemma audit_elements_work_app A (first second : list (audit_elements_event A)) :
  audit_elements_work (first ++ second) =
    audit_elements_work first + audit_elements_work second.
Proof.
  induction first as [|event rest IH]; cbn; auto.
  rewrite IH; lia.
Qed.

Lemma audit_elements_fold_adequate A (node : Trie.ne A) :
  forall path acc,
    fst (audit_elements_fold_ne path node acc) =
      Trie.fold_ne (fun acc p v => (p, v) :: acc) path node acc /\
    length (fst (audit_elements_fold_ne path node acc)) <= length acc + audit_elements_nodes node /\
    length (snd (audit_elements_fold_ne path node acc)) <= 2 * audit_elements_nodes node /\
    audit_elements_work (snd (audit_elements_fold_ne path node acc)) <=
      13 * audit_elements_nodes node + audit_elements_bits path node.
Proof.
  induction node as [r IHr | v | v r IHr | l IHl | l IHl r IHr | l IHl v |
    l IHl v r IHr]; intros path acc;
    cbn [audit_elements_fold_ne Trie.fold_ne audit_elements_nodes audit_elements_bits].
  all: try specialize (IHl (fun p => path (xO p)) acc).
  all: try (destruct (audit_elements_fold_ne (fun p => path (xO p)) l acc) as [lo le]).
  all: try specialize (IHr (fun p => path (xI p)) ((path xH, v) :: lo)).
  all: try specialize (IHr (fun p => path (xI p)) lo).
  all: try specialize (IHr (fun p => path (xI p)) ((path xH, v) :: acc)).
  all: try specialize (IHr (fun p => path (xI p)) acc).
  all: try (destruct (audit_elements_fold_ne (fun p => path (xI p)) r
    ((path xH, v) :: lo)) as [ro re]).
  all: try (destruct (audit_elements_fold_ne (fun p => path (xI p)) r lo) as [ro re]).
  all: try (destruct (audit_elements_fold_ne (fun p => path (xI p)) r
    ((path xH, v) :: acc)) as [ro re]).
  all: try (destruct (audit_elements_fold_ne (fun p => path (xI p)) r acc) as [ro re]).
  all: cbn in *; repeat rewrite List.length_app in *;
    repeat rewrite audit_elements_work_app in *; cbn in *; intuition congruence || lia.
Qed.

(** The fold emits at most two events per input node. *)
Theorem audit_elements_fold_count : audit_elements_fold_count_statement.
Proof.
  intros A path node acc.
  destruct (audit_elements_fold_adequate A node path acc) as [_ [_ [H _]]].
  exact H.
Qed.

Lemma audit_elements_reverse_adequate A (input acc : list (positive * A)) :
  fst (audit_elements_reverse input acc) = rev_append input acc /\
  audit_elements_work (snd (audit_elements_reverse input acc)) = 2 * (length input + 1).
Proof.
  revert acc; induction input as [|x rest IH]; intro acc; cbn [audit_elements_reverse rev_append].
  - repeat split; reflexivity.
  - specialize (IH (x :: acc)).
    destruct (audit_elements_reverse rest (x :: acc)) as [out events].
    cbn in *; intuition congruence || lia.
Qed.

Lemma audit_elements_values_adequate A (input : list (positive * A)) :
  fst (audit_elements_values input) = map snd input /\
  audit_elements_work (snd (audit_elements_values input)) = 2 * (length input + 1) /\
  length (fst (audit_elements_values input)) = length input.
Proof.
  induction input as [|[position value] rest IH]; cbn [audit_elements_values List.map].
  - repeat split; reflexivity.
  - destruct (audit_elements_values rest) as [out events].
    cbn in *; intuition congruence || lia.
Qed.

Lemma audit_elements_project_adequate K (input : list (K * unit)) :
  fst (audit_set_elements_project input) = map fst input /\
  audit_set_elements_work (snd (audit_set_elements_project input)) = 2 * (length input + 1).
Proof.
  induction input as [|[key value] rest IH]; cbn [audit_set_elements_project List.map].
  - repeat split; reflexivity.
  - destruct (audit_set_elements_project rest) as [out events].
    cbn in *; intuition congruence || lia.
Qed.

Lemma audit_set_elements_work_app K (first second : list (audit_set_elements_event K)) :
  audit_set_elements_work (first ++ second) =
    audit_set_elements_work first + audit_set_elements_work second.
Proof.
  induction first as [|event rest IH]; cbn; auto.
  destruct event; cbn; rewrite IH; lia.
Qed.

Lemma audit_set_elements_work_map K (events : list (audit_elements_event (K * unit))) :
  audit_set_elements_work (map AuditSetElementsTrie events) = audit_elements_work events.
Proof.
  induction events as [|event rest IH]; cbn; auto.
Qed.

(** Trie enumeration erases to the original enumeration. *)
Theorem audit_trie_elements_erases : audit_trie_elements_erases_statement.
Proof.
  intros A [|node]; unfold audit_trie_elements, Trie.elements, Trie.fold, Trie.fold_path.
  - repeat split; reflexivity.
  - pose proof (audit_elements_fold_adequate A node (fun p => p) []) as [H _].
    destruct (audit_elements_fold_ne (fun p => p) node []) as [out events].
    cbn in H; rewrite <- H.
    destruct (audit_elements_reverse_adequate A out []) as [Hreverse _].
    destruct (audit_elements_reverse out []); exact Hreverse.
Qed.

(** Map enumeration erases to the original enumeration. *)
Theorem audit_map_elements_erases : audit_map_elements_erases_statement.
Proof.
  intros K V input; unfold audit_map_elements, Map.elements.
  pose proof (audit_trie_elements_erases (K * V)%type input) as Htrie.
  destruct (audit_trie_elements input) as [positions events]; cbn in Htrie.
  pose proof (audit_elements_values_adequate (K * V)%type positions) as [Hvalues _].
  destruct (audit_elements_values positions); cbn in *; congruence.
Qed.

(** Set enumeration erases to the original enumeration. *)
Theorem audit_finset_elements_erases : audit_finset_elements_erases_statement.
Proof.
  intros K input; unfold audit_finset_elements, FinSet.elements.
  pose proof (audit_map_elements_erases K unit input) as Hmap.
  destruct (audit_map_elements input) as [values events]; cbn in Hmap.
  pose proof (audit_elements_project_adequate K values) as [Hproject _].
  destruct (audit_set_elements_project values); cbn in *; congruence.
Qed.

Lemma audit_trie_elements_quantitative A (input : Trie.t A) :
  length (fst (audit_trie_elements input)) <= audit_trie_nodes input /\
  audit_elements_work (snd (audit_trie_elements input)) <=
    15 * audit_trie_nodes input + audit_trie_output_bits input + 2.
Proof.
  destruct input as [|node]; unfold audit_trie_elements;
    cbn [audit_trie_nodes audit_trie_output_bits].
  - cbn; lia.
  - pose proof (audit_elements_fold_adequate A node (fun p => p) []) as Hfold.
    destruct (audit_elements_fold_ne (fun p => p) node []) as [out events].
    pose proof (audit_elements_reverse_adequate A out []) as Hreverse.
    destruct (audit_elements_reverse out []) as [result reverse_events].
    cbn in *; destruct Hfold as [_ [Hlength [_ Hwork]]].
    destruct Hreverse as [Hresult Hreverse].
    rewrite audit_elements_work_app; cbn in *.
    rewrite Hresult, rev_append_rev, app_nil_r, length_rev; lia.
Qed.

(** Trie enumeration work is bounded by input nodes and emitted position bits. *)
Theorem audit_trie_elements_work_bound : audit_trie_elements_work_bound_statement.
Proof.
  intros A input; exact (proj2 (audit_trie_elements_quantitative A input)).
Qed.

Lemma audit_map_elements_quantitative K V (input : Map.t K V) :
  length (fst (audit_map_elements input)) <= audit_trie_nodes input /\
  audit_elements_work (snd (audit_map_elements input)) <=
    17 * audit_trie_nodes input + audit_trie_output_bits input + 4.
Proof.
  unfold audit_map_elements.
  pose proof (audit_trie_elements_quantitative (K * V)%type input) as Htrie.
  destruct (audit_trie_elements input) as [positions events].
  pose proof (audit_elements_values_adequate (K * V)%type positions) as Hvalues.
  destruct (audit_elements_values positions) as [values values_events].
  cbn in *; destruct Htrie as [Hlength Hwork].
  destruct Hvalues as [_ [Hvalues Hout]].
  rewrite audit_elements_work_app; cbn in *; lia.
Qed.

(** Map enumeration work includes its projection pass. *)
Theorem audit_map_elements_work_bound : audit_map_elements_work_bound_statement.
Proof.
  intros K V input; exact (proj2 (audit_map_elements_quantitative K V input)).
Qed.

(** Set enumeration work includes both projection passes. *)
Theorem audit_finset_elements_work_bound : audit_finset_elements_work_bound_statement.
Proof.
  intros K input; unfold audit_finset_elements.
  pose proof (audit_map_elements_quantitative K unit input) as Hmap.
  destruct (audit_map_elements input) as [values events].
  pose proof (audit_elements_project_adequate K values) as Hproject.
  destruct (audit_set_elements_project values) as [keys project_events].
  cbn in *; destruct Hmap as [Hlength Hwork]; destruct Hproject as [_ Hproject].
  rewrite audit_set_elements_work_app, audit_set_elements_work_map; cbn in *; lia.
Qed.
