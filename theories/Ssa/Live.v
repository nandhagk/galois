(** * Placeholder liveness producer

    This module provides the interface for computing live variables.
    For example, its placeholder returns no rows.
    Builds on: LiveSig. *)

From Stdlib Require Import List PArith NArith.
From Argent Require Import Time Tactics Std BigO.
From Galois.Base Require Import KeySig Key Trie.
From Galois.Graph Require Import DigraphSig.
From Galois.Program Require Import CfgSig VarsSig SsaSig.
From Galois.Ssa Require Import Lang LiveSig.
Import List.ListNotations.

Module LiveCode (O : OPS)
    (P : TYPE with Definition t := func positive O.K O.G)
    (Q : TYPE) (R : LANG_PREPARE_OPS O Q)
    (BE E : TYPE) (N : KEY_OPS)
    (BC : CFG_INDEXED_OPS Q PosKeyCode BE) (C : CFG_INDEXED_OPS Q N E)
    (U : VARS_OPS Q N E C PosKeyCode)
    (SP : SSA_POINTS_OPS Q PosKeyCode BE BC N E C PosKeyCode U)
    <: LIVE_OPS O P Q R BE E N BC C U SP.
  (* STUB-CODE *)
  Definition live_in (_ : P.t) : list (positive * list positive) := [].
End LiveCode.

Module Live (O : OPS)
    (P : TYPE with Definition t := func positive O.K O.G)
    (Q : TYPE) (R : LANG_PREPARE_OPS O Q)
    (BE E : TYPE) (N : KEY)
    (BC : CFG Q PosKey BE) (C : CFG Q N E) (U : VARS Q N E C PosKey)
    (SP : SSA_POINTS Q PosKey BE BC N E C PosKey U)
    <: LIVE O P Q R BE E N BC C U SP.
  Include LiveCode O P Q R BE E N BC C U SP.
End Live.

Module LiveT (O : OPS)
    (P : TYPE with Definition t := func positive O.K O.G)
    (Q : TYPE) (R : LANG_PREPARE_T O Q)
    (BE E N : KEY_T)
    (BC : CFG_T Q PosKeyT BE) (C : CFG_T Q N E) (U : VARS_T Q N E C PosKeyT)
    (SP : SSA_POINTS_T Q PosKeyT BE BC N E C PosKeyT U)
    (PB : LANG_PRESENT_BUDGET O Q R BE E N BC C U SP)
    <: LIVE_ALL O P Q R BE E N BC C U SP PB.
  Include Live O P Q R BE E N BC C U SP.
  TimeFun live_in.
  (* STUB-CODE *)
  Definition live_region (_ : P.t) : list (N.t * positive) := [].
  (** The cost region enumerates each live point/value pair exactly once. *)
  Lemma live_region_spec : forall p,
    NoDup (live_region p) /\ forall n x,
      (In (n, x) (live_region p) <-> In n (C.nodes (R.prepare p)) /\
        In x (U.universe (R.prepare p)) /\
        point_live (C.nodes (R.prepare p)) (C.out (R.prepare p)) (C.dst (R.prepare p))
          (U.uses (R.prepare p)) (U.defs (R.prepare p)) (U.exits (R.prepare p)) x n).
  Proof. Admitted. (* STUB *)
  Definition live_size p := fold_right (fun pair n =>
    1 + length (C.inc (R.prepare p) (fst pair)) + n) 0 (live_region p).
  Definition rows_size (rows : list (positive * list positive)) :=
    fold_right (fun row n => 1 + length (snd row) + n) 0 rows.
  (** The producer emits at most one row entry per charged block and live pair. *)
  Lemma live_in_size : forall p,
    rows_size (live_in p) <= length (blocks _ _ _ p) + live_size p.
  Proof. Admitted. (* STUB *)
  Definition c_live : N := 1. (* STUB *)
  (** Path exploration pays for syntax and live predecessor incidences. *)
  Lemma T_live_in_le : forall p,
    (T_live_in p <= c_live * N.of_nat (function_size p + live_size p + 1) *
      N.of_nat (function_width p + 1))%N.
  Proof. Admitted. (* STUB *)
  (** The producer has the published output-sensitive bit-cost bound. *)
  Lemma live_in_bigO : bigO (fun _ : P.t => True)
    (fun p => N.of_nat ((function_size p + live_size p + 1) * (function_width p + 1)))
    T_live_in.
  Proof. Admitted. (* STUB *)
  (* STUB-CODE *)
  Definition use_index (_ : Q.t) : ptrie (list N.t) := Empty.
  TimeFun use_index.
  Definition kill_index (q : Q.t) : ptrie (ptrie unit) :=
    fold_right (fun e rows =>
      fold_right (fun x acc =>
        let row := match trie_get x acc with Some m => m | None => Empty end in
        PTrieCode.set x (PTrieCode.set (E.encode e) tt row) acc) rows (U.defs q e))
      Empty (C.edges q).
  TimeFun kill_index.
  (* STUB-CODE *)
  Definition explore (_ : Q.t) (_ : ptrie (list N.t)) (_ : ptrie (ptrie unit))
      (_ : positive) : list N.t := [].
  TimeFun explore.
  Definition k_index : N := 1. (* STUB *)
  Definition k_explore : N := 1. (* STUB *)
  Definition k_rows : N := 1. (* STUB *)
  Definition visits p x := filter (fun pair => Pos.eqb (snd pair) x) (live_region p).
  Definition variable_work p x := fold_right (fun pair n =>
    1 + length (C.inc (R.prepare p) (fst pair)) + n) 0 (visits p x).
  Definition searched p x :=
    explore (R.prepare p) (use_index (R.prepare p)) (kill_index (R.prepare p)) x.
  (** Indexed use points of a variable are distinct charged live pairs. *)
  Lemma F0_use_index : forall p x,
    NoDup (index_row (use_index (R.prepare p)) x) /\
    forall n, In n (index_row (use_index (R.prepare p)) x) -> In (n, x) (live_region p).
  Proof. Admitted. (* STUB *)
  (** The kill index answers, for a variable and a listed edge, whether the edge defines it. *)
  Lemma F0b_kill_index : forall p x e, In e (C.edges (R.prepare p)) ->
    ((exists m, trie_get x (kill_index (R.prepare p)) = Some m /\
      trie_get (E.encode e) m = Some tt) <-> In x (U.defs (R.prepare p) e)).
  Proof. Admitted. (* STUB *)
  (** Each per-variable search visits a point at most once. *)
  Lemma F1_explore_nodup : forall p x, NoDup (searched p x).
  Proof. Admitted. (* STUB *)
  (** Every visited search point belongs to its charged semantic region. *)
  Lemma F2_explore_region : forall p x n,
    In n (searched p x) -> In (n, x) (live_region p).
  Proof. Admitted. (* STUB *)
  (** Deduplicated variables partition the total live-incidence budget. *)
  Lemma F3_partition : forall p,
    fold_right (fun x n => variable_work p x + n) 0 (U.universe (R.prepare p)) =
      live_size p.
  Proof. Admitted. (* STUB *)
  (** Indexing reads each variable occurrence once at the syntax width. *)
  Lemma T0_use_index : forall p,
    (T_use_index (R.prepare p) <= k_index * N.of_nat (function_size p + 1) *
      N.of_nat (function_width p + 1))%N.
  Proof. Admitted. (* STUB *)
  (** The kill index reads each definition occurrence once at the syntax width. *)
  Lemma T0_kill_index : forall p,
    (T_kill_index (R.prepare p) <= k_index * N.of_nat (function_size p + 1) *
      N.of_nat (function_width p + 1))%N.
  Proof. Admitted. (* STUB *)
  (** A variable's search charges each visited point and incoming occurrence. *)
  Lemma T1_explore : forall p x,
    (T_explore (R.prepare p) (use_index (R.prepare p)) (kill_index (R.prepare p)) x <=
      k_explore * N.of_nat (variable_work p x + 1) * N.of_nat (function_width p + 1))%N.
  Proof. Admitted. (* STUB *)
  (** The driver prepares once, builds both indexes, searches each variable and groups
      rows. *)
  Lemma T2_rows : forall p,
    (T_live_in p <= R.T_prepare p +
      k_rows * N.of_nat (function_size p + live_size p + 1) *
        N.of_nat (function_width p + 1) + T_use_index (R.prepare p) +
      T_kill_index (R.prepare p) +
      fold_right N.add 0%N
        (map (T_explore (R.prepare p) (use_index (R.prepare p)) (kill_index (R.prepare p)))
          (U.universe (R.prepare p))))%N.
  Proof. Admitted. (* STUB *)

End LiveT.
