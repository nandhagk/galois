(** * Control-flow graph helpers

    Prepare adjacency tables from a client presentation.
    For example, parallel edges remain separate entries in each adjacency list.
    Builds on: Program.CfgSig and Graph.Data. *)
From Stdlib Require Import List PArith NArith.
From Argent Require Import Time Tactics Std.
From Galois.Base Require Import KeySig Trie Code.
From Galois.Graph Require Import Data.
From Galois.Program Require Import CfgSig.
Import List.ListNotations.
Import Code.List.

Fixpoint occurrences {E} (es : list E) (i : nat) : list (E * nat) :=
  match es with
  | [] => []
  | e :: rest => (e, i) :: occurrences rest (S i)
  end.

(** Projecting occurrence values recovers the original edge list. *)
Theorem occurrences_project {E} (es : list E) i : map fst (occurrences es i) = es.
Proof.
  revert i; induction es as [|e es IH]; intro i; cbn [occurrences map fst];
    rewrite ?IH; reflexivity.
Qed.

(** Occurrence counters form a contiguous sequence. *)
Theorem occurrences_positions {E} (es : list E) i :
  map snd (occurrences es i) = seq i (length es).
Proof.
  revert i; induction es as [|e es IH]; intro i; cbn [occurrences map snd seq length];
    rewrite ?IH; reflexivity.
Qed.

(** Occurrence keys distinguish duplicate client edges. *)
Theorem occurrences_nodup {E} (es : list E) i : NoDup (occurrences es i).
Proof.
  apply (NoDup_map_inv snd); rewrite occurrences_positions; apply seq_NoDup.
Qed.

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

TimeFun cfg_add.

Definition cfg_distinct {A} (encode : A -> positive) (xs : list A) : list A :=
  rev (snd (fold_left (fun acc x =>
    let c := encode x in
    match trie_get c (fst acc) with
    | Some _ => acc
    | None => (PTrieCode.set c tt (fst acc), x :: snd acc)
    end) xs (Empty, []))).

TimeFun cfg_distinct.
TimeFun cfg_program.
TimeFun cfg_nodes.
TimeFun cfg_out.
TimeFun cfg_inc.

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
  Module Code := CfgCode P N E C.
  Module PC := PreparedCfg P N E C.
  Module Laws <: CFG PC.PT N E.
  Include PC.Ops.
  Include PC.Adj.

  Definition wf (p : PC.PT.t) := p = Code.prepare (cfg_program p).

  (** Preparation establishes the cache and node correspondence used by the laws. *)
  Lemma prepare_wf : forall p, wf (Code.prepare p).
  Proof. Admitted.

  Lemma nodes_nodup : forall p, wf p -> NoDup (nodes p).
  Proof. Admitted.

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

Module CfgT (P : TYPE) (N : KEY_T) (E : TYPE) (C : CFG_BASE_T P N E).
  Include CfgCode P N E C.
  TimeFun nodes.
  TimeFun graph_of.
  TimeFun prepare.
  Definition c_cfg_prep : N := 1%N. (* STUB *)

  (** Preparation pays for every indexed endpoint and entry. *)
  Lemma T_prepare_le : forall p,
    (T_prepare p <= c_cfg_prep * N.of_nat (length (C.entries p) + length (C.edges p) + 1) *
      N.of_nat (fold_right Nat.max 0%nat (List.map N.bits (C.entries p ++
        flat_map (fun e => C.src p e :: C.dst p e :: nil) (C.edges p))) + 1))%N.
  Proof. Admitted. (* STUB *)
End CfgT.
