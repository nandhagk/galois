(** * Placeholder liveness producer

    This module provides the interface for computing live variables.
    For example, its placeholder returns no rows.
    Builds on: LiveSig. *)

From Stdlib Require Import List PArith NArith.
From Argent Require Import Time Tactics Std BigO.
From Galois.Base Require Import KeySig Key.
From Galois.Graph Require Import DigraphSig.
From Galois.Program Require Import CfgSig VarsSig SsaSig.
From Galois.Ssa Require Import Lang LiveSig.
Import List.ListNotations.

Module LiveCode (O : OPS)
    (P : TYPE with Definition t := func positive O.K O.G)
    (BE E : TYPE) (N : KEY_OPS)
    (BC : CFG_INDEXED_OPS P PosKeyCode BE) (C : CFG_INDEXED_OPS P N E)
    (U : VARS_OPS P N E C PosKeyCode)
    (SP : SSA_POINTS_OPS P PosKeyCode BE BC N E C PosKeyCode U)
    <: LIVE_OPS O P BE E N BC C U SP.
  (* STUB-CODE *)
  Definition live_in (_ : P.t) : list (positive * list positive) := [].
End LiveCode.

Module Live (O : OPS)
    (P : TYPE with Definition t := func positive O.K O.G)
    (BE E : TYPE) (N : KEY)
    (BC : CFG P PosKey BE) (C : CFG P N E) (U : VARS P N E C PosKey)
    (SP : SSA_POINTS P PosKey BE BC N E C PosKey U)
    <: LIVE O P BE E N BC C U SP.
  Include LiveCode O P BE E N BC C U SP.
End Live.

Module LiveT (O : OPS)
    (P : TYPE with Definition t := func positive O.K O.G)
    (BE E : TYPE) (N : KEY_T)
    (BC : CFG_T P PosKeyT BE) (C : CFG_T P N E) (U : VARS_T P N E C PosKeyT)
    (SP : SSA_POINTS_T P PosKeyT BE BC N E C PosKeyT U)
    <: LIVE_ALL O P BE E N BC C U SP.
  Include Live O P BE E N BC C U SP.
  TimeFun live_in.
  (* STUB-CODE *)
  Definition live_region (_ : P.t) : list (N.t * positive) := [].
  TimeFun live_region.
  Lemma live_region_spec : forall p,
    NoDup (live_region p) /\ forall n x,
      (In (n, x) (live_region p) <-> In n (C.nodes p) /\ In x (U.universe p) /\
        point_live (C.out p) (C.dst p) (U.uses p) (U.defs p) (U.exits p) x n).
  Proof. Admitted. (* STUB *)
  Definition live_size p := fold_right (fun pair n =>
    1 + length (C.inc p (fst pair)) + n) 0 (live_region p).
  Definition c_live : N := 1. (* STUB *)
  Lemma T_live_in_le : forall p,
    (T_live_in p <= c_live * N.of_nat (function_size p + live_size p + 1) *
      N.of_nat (function_width p + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma live_in_bigO : bigO (fun _ : P.t => True)
    (fun p => N.of_nat ((function_size p + live_size p + 1) * (function_width p + 1)))
    T_live_in.
  Proof. Admitted. (* STUB *)
  (* STUB-CODE *)
  Definition explore (_ : P.t) (_ : positive) : list N.t := [].
  TimeFun explore.
  Definition k_explore : N := 1. (* STUB *)
  Definition k_rows : N := 1. (* STUB *)
  Definition visits p x := filter (fun pair => Pos.eqb (snd pair) x) (live_region p).
  Definition variable_work p x := fold_right (fun pair n =>
    1 + length (C.inc p (fst pair)) + n) 0 (visits p x).
  Lemma F1_explore_nodup : forall p x, NoDup (explore p x).
  Proof. Admitted. (* STUB *)
  Lemma F2_explore_region : forall p x n, In n (explore p x) ->
    In (n, x) (live_region p).
  Proof. Admitted. (* STUB *)
  Lemma F3_partition : forall p,
    fold_right (fun x n => variable_work p x + n) 0 (U.universe p) = live_size p.
  Proof. Admitted. (* STUB *)
  Lemma T1_explore : forall p x,
    (T_explore p x <= k_explore * N.of_nat (variable_work p x + 1) *
      N.of_nat (function_width p + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T2_rows : forall p,
    (T_live_in p <= k_rows * N.of_nat (function_size p + live_size p + 1) *
      N.of_nat (function_width p + 1))%N.
  Proof. Admitted. (* STUB *)
End LiveT.
