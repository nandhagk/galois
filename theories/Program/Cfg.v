(** * Control-flow graph helpers

    Prepare adjacency tables from a client presentation.
    For example, parallel edges remain separate entries in each adjacency list.
    Builds on: Program.CfgSig and Graph.Data. *)
From Stdlib Require Import List PArith.
From Galois.Base Require Import KeySig Trie.
From Galois.Graph Require Import Data.
From Galois.Program Require Import CfgSig.
Import List.ListNotations.

Fixpoint occurrences {E} (es : list E) (i : nat) : list (E * nat) :=
  match es with
  | [] => []
  | e :: rest => (e, i) :: occurrences rest (S i)
  end.

Record cfg_prepared (P N E : Type) := CfgPrepared {
  cfg_program : P;
  cfg_nodes : list N;
  cfg_out : ptrie (list E);
  cfg_inc : ptrie (list E)
}.

Arguments CfgPrepared {P N E} _ _ _ _.
Arguments cfg_program {P N E} _.
Arguments cfg_nodes {P N E} _.
Arguments cfg_out {P N E} _.
Arguments cfg_inc {P N E} _.

Definition cfg_add {A} (k : positive) (x : A) (m : ptrie (list A)) :=
  PTrieCode.set k (x :: match trie_get k m with Some xs => xs | None => [] end) m.

Definition cfg_distinct {A} (encode : A -> positive) (xs : list A) : list A :=
  rev (snd (fold_left (fun acc x =>
    let c := encode x in
    match trie_get c (fst acc) with
    | Some _ => acc
    | None => (PTrieCode.set c tt (fst acc), x :: snd acc)
    end) xs (Empty, []))).

Module CfgCode (P : TYPE) (N : KEY_OPS) (E : TYPE) (C : CFG_OPS P N E).
  Definition nodes p := cfg_distinct N.encode
    (C.entries p ++ flat_map (fun e => [C.src p e; C.dst p e]) (C.edges p)).
  Definition graph_of p : digraph :=
    Digraph (map N.encode (nodes p))
      (fold_right (fun e m => cfg_add (N.encode (C.src p e)) (N.encode (C.dst p e)) m)
        Empty (C.edges p)).
  Definition prepare p : cfg_prepared P.t N.t E.t :=
    CfgPrepared p (nodes p)
      (fold_right (fun e m => cfg_add (N.encode (C.src p e)) e m) Empty (C.edges p))
      (fold_right (fun e m => cfg_add (N.encode (C.dst p e)) e m) Empty (C.edges p)).
End CfgCode.

Module PreparedType (P : TYPE) (N : KEY_OPS) (E : TYPE) <: TYPE.
  Definition t := cfg_prepared P.t N.t E.t.
End PreparedType.

Module PreparedCfg (P : TYPE) (N : KEY_OPS) (E : TYPE) (C : CFG_OPS P N E).
  Module PT := PreparedType P N E.
  Module Ops <: CFG_OPS PT N E.
    Definition entries (p : PT.t) := C.entries (cfg_program p).
    Definition edges (p : PT.t) := C.edges (cfg_program p).
    Definition src (p : PT.t) := C.src (cfg_program p).
    Definition dst (p : PT.t) := C.dst (cfg_program p).
  End Ops.
  Module Adj <: CFG_ADJ_OPS PT N E Ops.
    Definition nodes := @cfg_nodes P.t N.t E.t.
    Definition out (p : PT.t) n := match trie_get (N.encode n) (cfg_out p) with
      | Some es => es | None => [] end.
    Definition inc (p : PT.t) n := match trie_get (N.encode n) (cfg_inc p) with
      | Some es => es | None => [] end.
  End Adj.
End PreparedCfg.

Module PreparedCfgLaws (P : TYPE) (N : KEY) (E : TYPE) (C : CFG_OPS P N E).
  Module PC := PreparedCfg P N E C.
  Module Laws <: CFG PC.PT N E.
  Include PC.Ops.
  Include PC.Adj.

  Definition wf (_ : PC.PT.t) := True.

  Lemma entries_nodes : forall p n, wf p -> In n (entries p) -> In n (nodes p).
  Proof. Admitted.

  Lemma edges_nodes : forall p e, wf p -> In e (edges p) ->
    In (src p e) (nodes p) /\ In (dst p e) (nodes p).
  Proof. Admitted.

  Lemma out_spec : forall p n e, wf p ->
    (In e (out p n) <-> In e (edges p) /\ src p e = n).
  Proof. Admitted.

  Lemma inc_spec : forall p n e, wf p ->
    (In e (inc p n) <-> In e (edges p) /\ dst p e = n).
  Proof. Admitted.
  End Laws.
  Include Laws.
End PreparedCfgLaws.
