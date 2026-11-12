(** * Placeholder SSA destruction

    This module supplies the checked destruction interface.
    For example, its placeholder rejects every input.
    Builds on: DestroySig. *)

From Stdlib Require Import List PArith NArith.
From Argent Require Import Time Tactics Std BigO.
From Galois.Base Require Import KeySig Key.
From Galois.Program Require Import CfgSig SsaSig.
From Galois.Ssa Require Import Lang LiveSig ValidateSig ParMoveSig DestroySig.
Import List.ListNotations.

Module DestroyCode (O : OPS)
    (K : KEY_OPS with Definition t := O.K) (G : KEY_OPS with Definition t := O.G)
    (P : TYPE with Definition t := func positive O.K O.G) (E : TYPE)
    (C : CFG_INDEXED_OPS P PosKeyCode E) (S : SSA_OPS P PosKeyCode E C PosKeyCode K G)
    (PM : PARMOVE_OPS) <: DESTROY_OPS O K G P E C S PM.
  (* STUB-CODE *)
  Definition destroy (_ : P.t) : option P.t := None.
End DestroyCode.

Module Destroy (O : OPS)
    (K : KEY with Definition t := O.K) (G : KEY with Definition t := O.G)
    (P : TYPE with Definition t := func positive O.K O.G) (E : TYPE)
    (C : CFG P PosKey E) (S : SSA P PosKey E C PosKey K G)
    (PM : PARMOVE) (OL : LAWS O) (B : LANG_SSA_LINK O K G P E C S)
    <: DESTROY O K G P E C S PM OL B.
  Include DestroyCode O K G P E C S PM.
  Lemma destroy_imp : forall s p, destroy s = Some p -> imp_form p.
  Proof. Admitted.
  Lemma destroy_correct : forall s p, ssa_wf s -> destroy s = Some p ->
    forall n ins r, r <> Timeout ->
      (run_with O.eval O.test n s ins = r -> run_with O.eval O.test (2 * n) p ins = r) /\
      (run_with O.eval O.test n p ins = r -> run_with O.eval O.test n s ins = r).
  Proof. Admitted.
End Destroy.

Module DestroyT (O : OPS)
    (K : KEY_T with Definition t := O.K) (G : KEY_T with Definition t := O.G)
    (P : TYPE with Definition t := func positive O.K O.G) (E : TYPE)
    (C : CFG_T P PosKeyT E) (S : SSA_T P PosKeyT E C PosKeyT K G)
    (PM : PARMOVE_T) (OL : LAWS O) (B : LANG_SSA_LINK O K G P E C S)
    <: DESTROY_ALL O K G P E C S PM OL B.
  Include Destroy O K G P E C S PM OL B.
  TimeFun destroy.
  Definition c_ds : N := 1. (* STUB *)
  Definition destroy_work (s : P.t) :=
    function_size s + destroy_edge_args s + split_count s + 1.
  Lemma T_destroy_le : forall s,
    (T_destroy s <= c_ds * N.of_nat (destroy_work s) * N.of_nat (function_width s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma destroy_bigO : bigO (fun _ : P.t => True)
    (fun s => N.of_nat (destroy_work s * (function_width s + 1))) T_destroy.
  Proof. Admitted. (* STUB *)
  (* STUB-CODE *)
  Definition split (_ : P.t) : option P.t := None.
  (* STUB-CODE *)
  Definition copies (_ : P.t) : option P.t := None.
  (* STUB-CODE *)
  Definition checked_moves (_ : P.t) : list move_check := [].
  TimeFun split.
  TimeFun copies.
  TimeFun checked_moves.
  Definition k_split : N := 1. (* STUB *)
  Definition k_copies : N := 1. (* STUB *)
  Definition k_wrap : N := 1. (* STUB *)
  Definition entered_agree (s p : P.t) (ss sp : machine_state O.C) :=
    let '(bs, actuals_s, es) := ss in
    let '(bp, actuals_p, ep) := sp in
    bs = bp /\
    match find_block bs (blocks _ _ _ s), find_block bp (blocks _ _ _ p) with
    | None, None => True
    | Some sb, Some pb =>
        match bind_vars (params _ _ _ sb) actuals_s es,
          bind_vars (params _ _ _ pb) actuals_p ep with
        | None, None => True
        | Some entered_s, Some entered_p =>
            forall x, In x (function_vars s) -> lookup x entered_s = lookup x entered_p
        | _, _ => False
        end
    | _, _ => False
    end.
  Definition copy_outcomes s p (os op : machine_state O.C + result O.C) :=
    match os, op with
    | inl ss, inl sp => entered_agree s p ss sp
    | inr rs, inr rp => rs = rp
    | _, _ => False
    end.
  Lemma F1_destroy_phases : forall s, destroy s =
    match split s with None => None | Some split_s => copies split_s end.
  Proof. Admitted. (* STUB *)
  Lemma F2_split_preserves : forall s split_s, ssa_wf s -> split s = Some split_s ->
    ssa_wf split_s /\ forall n ins r, r <> Timeout ->
      (run_with O.eval O.test n s ins = r -> run_with O.eval O.test (2 * n) split_s ins = r) /\
      (run_with O.eval O.test n split_s ins = r -> run_with O.eval O.test n s ins = r).
  Proof. Admitted. (* STUB *)
  Lemma F3_moves_checked : forall s p par tmp sq, copies s = Some p ->
    In (par, tmp, sq) (checked_moves s) ->
    NoDup (map fst par) /\ ~ In tmp (map fst par ++ map snd par) /\
      PM.check_moves par tmp sq = true.
  Proof. Admitted. (* STUB *)
  Lemma F4_edge_copy_sim : forall s p par tmp sq, copies s = Some p ->
    In (par, tmp, sq) (checked_moves s) -> forall (e : positive -> option O.C) x,
      x <> tmp -> exec_seq sq e x = exec_par par e x.
  Proof. Admitted. (* STUB *)
  Lemma F5_block_sim : forall s p ss sp, ssa_wf s -> copies s = Some p ->
    entered_agree s p ss sp ->
    copy_outcomes s p (step O.eval O.test s ss) (step O.eval O.test p sp).
  Proof. Admitted. (* STUB *)
  Lemma F6_copies_run : forall s p, ssa_wf s -> copies s = Some p ->
    forall n ins, run_with O.eval O.test n s ins = run_with O.eval O.test n p ins.
  Proof. Admitted. (* STUB *)
  Lemma F7_copies_imp : forall s p, copies s = Some p -> imp_form p.
  Proof. Admitted. (* STUB *)
  Lemma F8_run_mono : forall (p : P.t) n m ins r, n <= m -> r <> Timeout ->
    run_with O.eval O.test n p ins = r -> run_with O.eval O.test m p ins = r.
  Proof. Admitted. (* STUB *)
  Lemma T1_split : forall s,
    (T_split s <= k_split * N.of_nat (destroy_work s) * N.of_nat (function_width s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T2_copies : forall s split_s, split s = Some split_s ->
    (T_copies split_s <= k_copies * N.of_nat (destroy_work s) *
      N.of_nat (function_width s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T3_wrapper : forall s,
    (T_destroy s <= T_split s +
      match split s with None => k_wrap | Some split_s => T_copies split_s + k_wrap end)%N.
  Proof. Admitted. (* STUB *)
End DestroyT.
