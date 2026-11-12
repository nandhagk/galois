(** * Depth-first search

    Search visits roots and successor occurrences in their supplied order.
    For example, an edge to an active vertex produces a back-edge event.
    Builds on: graph data, binary-fuel loops and the search signature. *)

From Stdlib Require Import List NArith PArith.
From Galois.Base Require Import Trie Loop.
From Galois.Graph Require Import Data SearchSig.
Import List.ListNotations.

Inductive search_task :=
  | SearchRoot (v : positive)
  | SearchRow (u : positive) (vs : list positive)
  | SearchLeave (v : positive).

Record search_state := SearchState {
  search_tasks : list search_task;
  search_colours : ptrie bool;
  search_events : list event
}.

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
