(** * Map fold traversal adequacy

    The counted fold retains the source accumulator and bounds its traversal work.
    For example, a callback receives the accumulator returned by the preceding binding.
    Builds on: CollectionsAuditMapFold. *)

From Stdlib Require Import List PArith Lia.
From Galois.Collections Require Import CollectionsTrie CollectionsMap CollectionsAuditElements
  CollectionsAuditMapFold.
(** * Fold equations and bounds *)

Lemma audit_map_fold_work_app K V B E work (first second : list (audit_map_fold_event K V B E)) :
  audit_map_fold_source_work work (first ++ second) =
    audit_map_fold_source_work work first + audit_map_fold_source_work work second /\
  audit_map_fold_child_work work (first ++ second) =
    audit_map_fold_child_work work first + audit_map_fold_child_work work second.
Proof.
  induction first as [|event rest IH]; cbn; try (split; lia).
  destruct event; cbn in *; destruct IH; split; lia.
Qed.

Lemma audit_map_fold_ne_adequate K V B E (f : B -> K -> V -> B * list E) original work
    (Hf : forall b k v, fst (f b k v) = original b k v) (node : Trie.ne (K * V)) :
  forall path acc,
    fst (audit_map_fold_ne f path node acc) =
      Trie.fold_ne (fun b _ kv => original b (fst kv) (snd kv)) path node acc /\
    length (snd (audit_map_fold_ne f path node acc)) <= 2 * audit_elements_nodes node /\
    audit_map_fold_source_work work (snd (audit_map_fold_ne f path node acc)) <=
      13 * audit_elements_nodes node + audit_elements_bits path node +
      audit_map_fold_child_work work (snd (audit_map_fold_ne f path node acc)).
Proof.
  induction node as [r IHr | [k v] | [k v] r IHr | l IHl | l IHl r IHr |
    l IHl [k v] | l IHl [k v] r IHr]; intros path acc;
    cbn [audit_map_fold_ne Trie.fold_ne audit_elements_nodes audit_elements_bits].
  all: try specialize (IHl (fun p => path (xO p)) acc).
  all: try (destruct (audit_map_fold_ne f (fun p => path (xO p)) l acc) as [lo le]).
  all: try (pose proof (Hf lo k v) as Hcall; destruct (f lo k v) as [co ce]).
  all: try (pose proof (Hf acc k v) as Hcall; destruct (f acc k v) as [co ce]).
  all: try specialize (IHr (fun p => path (xI p)) co).
  all: try specialize (IHr (fun p => path (xI p)) lo).
  all: try specialize (IHr (fun p => path (xI p)) acc).
  all: try (destruct (audit_map_fold_ne f (fun p => path (xI p)) r co) as [ro re]).
  all: try (destruct (audit_map_fold_ne f (fun p => path (xI p)) r lo) as [ro re]).
  all: try (destruct (audit_map_fold_ne f (fun p => path (xI p)) r acc) as [ro re]).
  all: cbn in *; repeat rewrite List.length_app in *;
    repeat rewrite (proj1 (audit_map_fold_work_app _ _ _ _ _ _ _)) in *;
    repeat rewrite (proj2 (audit_map_fold_work_app _ _ _ _ _ _ _)) in *;
    cbn in *; intuition congruence || lia.
Qed.

(** Erasing the events retains the original fold with the corresponding callback. *)
Theorem audit_map_fold_erases : audit_map_fold_erases_statement.
Proof.
  intros K V B E f original [|node] acc Hf; cbn [audit_map_fold Map.fold Trie.fold Trie.fold_path].
  - reflexivity.
  - exact (proj1 (audit_map_fold_ne_adequate K V B E f original (fun _ => 0) Hf node _ acc)).
Qed.

(** Fold node and callback events are bounded by twice the input node count. *)
Theorem audit_map_fold_count : audit_map_fold_count_statement.
Proof.
  intros K V B E f [|node] acc; cbn [audit_map_fold audit_trie_nodes]; cbn; try lia.
  pose proof (audit_map_fold_ne_adequate K V B E f (fun b k v => fst (f b k v))
    (fun _ => 0) (fun _ _ _ => eq_refl) node (fun p => p) acc) as [_ [H _]].
  exact H.
Qed.

(** Fold work includes position bits and the retained callback executions. *)
Theorem audit_map_fold_source_work_bound : audit_map_fold_source_work_bound_statement.
Proof.
  intros K V B E f work [|node] acc; cbn [audit_map_fold audit_trie_nodes
    audit_trie_output_bits]; cbn; try lia.
  pose proof (audit_map_fold_ne_adequate K V B E f (fun b k v => fst (f b k v)) work
    (fun _ _ _ => eq_refl) node (fun p => p) acc) as [_ [_ H]].
  exact H.
Qed.
