(** * Function calls and resolver graphs

    Inventories and resolver tables retain site and target order.
    For example, repeated targets produce repeated graph successors.
    Builds on: Program.CallsSig and Base.Trie. *)

From Stdlib Require Import List.
From Galois.Base Require Import KeySig Trie.
From Galois.Graph Require Import Data Spec.
From Galois.Program Require Import CallsSig.

Record calls_tables (F S : Type) := CallsTables {
  call_functions : list F;
  call_roots : list F;
  call_sites : ptrie (list S);
  call_callers : ptrie F;
  call_default_caller : F;
  call_targets : ptrie (list F)
}.

Arguments CallsTables {F S}.
Arguments call_functions {F S}.
Arguments call_roots {F S}.
Arguments call_sites {F S}.
Arguments call_callers {F S}.
Arguments call_default_caller {F S}.
Arguments call_targets {F S}.

Module Type CALLS_DATA (P : TYPE) (F S : KEY_OPS).
  Parameter tables : P.t -> calls_tables F.t S.t.
End CALLS_DATA.

Module CallsCode (P : TYPE) (F S : KEY_OPS) (D : CALLS_DATA P F S)
    <: CALLS_OPS P F S.
  Definition functions p := call_functions (D.tables p).
  Definition roots p := call_roots (D.tables p).
  Definition sites_of p f :=
    match trie_get (F.encode f) (call_sites (D.tables p)) with
    | Some sites => sites
    | None => nil
    end.
  Definition caller_of p site :=
    match trie_get (S.encode site) (call_callers (D.tables p)) with
    | Some f => f
    | None => call_default_caller (D.tables p)
    end.
  Definition resolve p site :=
    match trie_get (S.encode site) (call_targets (D.tables p)) with
    | Some fs => fs
    | None => nil
    end.
  Definition call_graph p :=
    Digraph (map F.encode (functions p))
      (fold_left (fun adj f => PTrieCode.set (F.encode f)
        (map (fun e => F.encode (edge_callee e)) (call_edges (resolve p) (sites_of p f))) adj)
        (functions p) PTrieCode.empty).
End CallsCode.
