(** * Depth-first search

    Search visits roots and successor occurrences in their supplied order.
    For example, an edge to an active vertex produces a back-edge event.
    Builds on: graph data, binary-fuel loops and the search signature. *)

From Stdlib Require Import List NArith PArith Sorting.Permutation.
From Galois.Base Require Import Trie Loop.
From Galois.Graph Require Import Data Spec SearchSig.
Import List.ListNotations.

Definition search_step (g : digraph) (s : search_state) : search_state + (list event) :=
  match s with
  | SearchState [] _ es => inr (rev es)
  | SearchState (task :: tasks) colours es =>
    match task with
    | SearchRoot v =>
      match trie_get v colours with
      | Some _ => inl (SearchState tasks colours es)
      | None => inl (SearchState (SearchRow v (succs g v) :: SearchLeave v :: tasks)
          (PTrieCode.set v true colours) (Enter v :: es))
      end
    | SearchRow u [] => inl (SearchState tasks colours es)
    | SearchRow u (v :: vs) =>
      match trie_get v colours with
      | None => inl (SearchState (SearchRoot v :: SearchRow u vs :: tasks) colours
          (Edge Tree u v :: es))
      | Some active => inl (SearchState (SearchRow u vs :: tasks) colours
          (Edge (if active then Back else Done) u v :: es))
      end
    | SearchLeave v => inl (SearchState tasks (PTrieCode.set v false colours) (Leave v :: es))
    end
  end.

Definition search_budget (g : digraph) (roots : list positive) : N :=
  N.of_nat (4 * (length roots +
    fold_right (fun entry n => length (snd entry) + n) 0 (PTrieCode.elements (succ g)) + 1)).

Definition search_trace (g : digraph) (roots : list positive) : list event :=
  match loopN (search_step g) (search_budget g roots)
      (SearchState (map SearchRoot roots) Empty []) with
  | inl s => rev (search_events s)
  | inr es => es
  end.

Module SearchCode (V : VISITOR_OPS) <: SEARCH_OPS V.
  Definition dfs (g : prepared) (roots : list positive) (s : V.state) : V.state :=
    fold_events V.enter V.leave V.edge (search_trace (base g) roots) s.
End SearchCode.

Opaque search_trace.

Module Search (V : VISITOR) <: SEARCH V.
  Include SearchCode V.

  Definition trace (g : prepared) (roots : list positive) := search_trace (base g) roots.

  Lemma trace_depth_first : forall g roots,
    exists final, dfs_roots (base g) [] roots (trace g roots) final.
  Proof. Admitted. (* SIG-QUESTION: landed trace proofs assume prepared readiness. *)

  Lemma dfs_fold : forall g roots s,
    dfs g roots s = fold_events V.enter V.leave V.edge (trace g roots) s.
  Proof.
    reflexivity.
  Qed.

  Lemma trace_reach : forall g roots v,
    In v (entered (trace g roots)) <-> reach (base g) roots v.
  Proof. Admitted. (* SIG-QUESTION: landed reachability proofs assume prepared readiness. *)

  Lemma trace_unique : forall g roots, NoDup (entered (trace g roots)).
  Proof. Admitted. (* SIG-QUESTION: landed numbering proofs assume prepared readiness. *)

  Lemma trace_nested : forall g roots, trace_stack [] (trace g roots) [].
  Proof. Admitted. (* SIG-QUESTION: landed trace proofs assume prepared readiness. *)

  Lemma trace_edges : forall g roots u, reach (base g) roots u ->
    Permutation (edge_targets u (trace g roots)) (succs (base g) u).
  Proof. Admitted. (* SIG-QUESTION: landed edge proofs assume prepared readiness. *)

  Lemma trace_edges_sound : forall g roots kind u v,
    In (Edge kind u v) (trace g roots) -> reach (base g) roots u /\ edge (base g) u v.
  Proof. Admitted. (* SIG-QUESTION: landed edge proofs assume prepared readiness. *)

  Lemma trace_kinds : forall g roots prefix kind u v suffix,
    trace g roots = prefix ++ Edge kind u v :: suffix -> event_kind_correct prefix kind v.
  Proof. Admitted. (* SIG-QUESTION: landed classification proofs assume prepared readiness. *)
End Search.

Transparent search_trace.
