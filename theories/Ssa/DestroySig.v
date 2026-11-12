(** * SSA destruction by checked edge copies

    Destruction splits parameter-carrying branch edges and checks parallel-copy sequences.
    For example, a swap uses a fresh temporary on its own incoming edge.
    Builds on: Ssa.Lang, core SSA presentations and checked parallel moves. *)

From Stdlib Require Import List PArith NArith.
From Argent Require Import Time Std BigO.
From Galois.Base Require Import KeySig Key.
From Galois.Program Require Import CfgSig SsaSig.
From Galois.Ssa Require Import Lang LiveSig ValidateSig ParMoveSig.
Import List.ListNotations.

Definition destroy_edge_args {K G} (p : func positive K G) : nat :=
  fold_right (fun item n =>
    match term _ _ _ (snd item) with
    | Jump _ xs => length xs + n
    | Branch _ _ _ xs _ ys => length xs + length ys + n
    | Return _ => n
    end) 0 (blocks _ _ _ p).
TimeFun destroy_edge_args.

Definition split_count {K G} (p : func positive K G) : nat :=
  fold_right (fun item n =>
    match term _ _ _ (snd item) with
    | Branch _ _ _ xs _ ys =>
        (match xs with [] => 0 | _ :: _ => 1 end) +
        (match ys with [] => 0 | _ :: _ => 1 end) + n
    | _ => n
    end) 0 (blocks _ _ _ p).
TimeFun split_count.

Definition move_check := (moves * positive * moves)%type.

Module Type DESTROY_OPS (O : OPS)
    (K : KEY_OPS with Definition t := O.K) (G : KEY_OPS with Definition t := O.G)
    (P : TYPE with Definition t := func positive O.K O.G) (E : TYPE)
    (C : CFG_INDEXED_OPS P PosKeyCode E) (S : SSA_OPS P PosKeyCode E C PosKeyCode K G)
    (PM : PARMOVE_OPS).
  Parameter destroy : P.t -> option P.t.
End DESTROY_OPS.

Module Type DESTROY_LAWS (O : OPS)
    (K : KEY with Definition t := O.K) (G : KEY with Definition t := O.G)
    (P : TYPE with Definition t := func positive O.K O.G) (E : TYPE)
    (C : CFG P PosKey E) (S : SSA P PosKey E C PosKey K G)
    (PM : PARMOVE)
    (OL : LAWS O) (B : LANG_SSA_LINK O K G P E C S)
    (Import A : DESTROY_OPS O K G P E C S PM).
  (** Every returned program has imperative form. *)
  Parameter destroy_imp : forall s p, destroy s = Some p -> imp_form p.
  (** Destruction adds at most one block step per original edge and retains finite results. *)
  Parameter destroy_correct : forall s p, ssa_wf s -> destroy s = Some p ->
    forall n ins r, r <> Timeout ->
      (run_with O.eval O.test n s ins = r -> run_with O.eval O.test (2 * n) p ins = r) /\
      (run_with O.eval O.test n p ins = r -> run_with O.eval O.test n s ins = r).
End DESTROY_LAWS.

Module Type DESTROY (O : OPS)
    (K : KEY with Definition t := O.K) (G : KEY with Definition t := O.G)
    (P : TYPE with Definition t := func positive O.K O.G) (E : TYPE)
    (C : CFG P PosKey E) (S : SSA P PosKey E C PosKey K G)
    (PM : PARMOVE)
    (OL : LAWS O) (B : LANG_SSA_LINK O K G P E C S) :=
  DESTROY_OPS O K G P E C S PM <+ DESTROY_LAWS O K G P E C S PM OL B.

Module Type DESTROY_TIME (O : OPS)
    (K : KEY_T with Definition t := O.K) (G : KEY_T with Definition t := O.G)
    (P : TYPE with Definition t := func positive O.K O.G) (E : TYPE)
    (C : CFG_T P PosKeyT E) (S : SSA_T P PosKeyT E C PosKeyT K G)
    (PM : PARMOVE_T)
    (OL : LAWS O) (B : LANG_SSA_LINK O K G P E C S)
    (Import A : DESTROY O K G P E C S PM OL B).
  Parameter T_destroy : P.t -> N.
  Parameter c_ds : N.
  Definition destroy_work (s : P.t) :=
    function_size s + destroy_edge_args s + split_count s + 1.
  (** Destruction charges syntax, copied arguments and split-edge blocks. *)
  Parameter T_destroy_le : forall s,
    (T_destroy s <= c_ds * N.of_nat (destroy_work s) * N.of_nat (function_width s + 1))%N.
  (** Destruction has the published linear bit-cost bound. *)
  Parameter destroy_bigO : bigO (fun _ : P.t => True)
    (fun s => N.of_nat (destroy_work s * (function_width s + 1))) T_destroy.
End DESTROY_TIME.

Module Type DESTROY_T (O : OPS)
    (K : KEY_T with Definition t := O.K) (G : KEY_T with Definition t := O.G)
    (P : TYPE with Definition t := func positive O.K O.G) (E : TYPE)
    (C : CFG_T P PosKeyT E) (S : SSA_T P PosKeyT E C PosKeyT K G)
    (PM : PARMOVE_T)
    (OL : LAWS O) (B : LANG_SSA_LINK O K G P E C S) :=
  DESTROY O K G P E C S PM OL B <+ DESTROY_TIME O K G P E C S PM OL B.

Module Type DESTROY_PLAN (O : OPS)
    (K : KEY_T with Definition t := O.K) (G : KEY_T with Definition t := O.G)
    (P : TYPE with Definition t := func positive O.K O.G) (E : TYPE)
    (C : CFG_T P PosKeyT E) (S : SSA_T P PosKeyT E C PosKeyT K G)
    (PM : PARMOVE_T)
    (OL : LAWS O) (B : LANG_SSA_LINK O K G P E C S)
    (Import A : DESTROY_T O K G P E C S PM OL B).
  Parameter split : P.t -> option P.t.
  Parameter copies : P.t -> option P.t.
  Parameter checked_moves : P.t -> list move_check.
  Parameter T_split T_copies T_checked_moves : P.t -> N.
  Parameter k_split k_copies k_wrap : N.
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
  (** The public operation first splits edges and then inserts checked copies. *)
  Parameter F1_destroy_phases : forall s, destroy s =
    match split s with None => None | Some split_s => copies split_s end.
  (** Splitting keeps SSA and has the required one-extra-step simulation in both directions. *)
  Parameter F2_split_preserves : forall s split_s, ssa_wf s -> split s = Some split_s ->
    ssa_wf split_s /\ forall n ins r, r <> Timeout ->
      (run_with O.eval O.test n s ins = r -> run_with O.eval O.test (2 * n) split_s ins = r) /\
      (run_with O.eval O.test n split_s ins = r -> run_with O.eval O.test n s ins = r).
  (** Each emitted edge sequence passes the move checker with a fresh temporary. *)
  Parameter F3_moves_checked : forall s p par tmp sq, copies s = Some p ->
    In (par, tmp, sq) (checked_moves s) ->
    NoDup (map fst par) /\ ~ In tmp (map fst par ++ map snd par) /\
      PM.check_moves par tmp sq = true.
  (** Checked sequential moves agree with incoming parallel parameter binding. *)
  Parameter F4_edge_copy_sim : forall s p par tmp sq, copies s = Some p ->
    In (par, tmp, sq) (checked_moves s) -> forall (e : positive -> option O.C) x,
      x <> tmp -> exec_seq sq e x = exec_par par e x.
  (** Copy insertion simulates one block after its incoming parameter bindings. *)
  Parameter F5_block_sim : forall s p ss sp, ssa_wf s -> copies s = Some p ->
    entered_agree s p ss sp ->
    copy_outcomes s p (step O.eval O.test s ss) (step O.eval O.test p sp).
  (** The block simulation and matching inputs give equal fuelled copy-stage runs. *)
  Parameter F6_copies_run : forall s p, ssa_wf s -> copies s = Some p ->
    forall n ins, run_with O.eval O.test n s ins = run_with O.eval O.test n p ins.
  (** Copy insertion removes every block parameter and outgoing argument. *)
  Parameter F7_copies_imp : forall s p, copies s = Some p -> imp_form p.
  (** Additional fuel retains every non-timeout result. *)
  Parameter F8_run_mono : forall (p : P.t) n m ins r, n <= m -> r <> Timeout ->
    run_with O.eval O.test n p ins = r -> run_with O.eval O.test m p ins = r.
  (** Splitting charges each source block and each parameter-carrying branch edge. *)
  Parameter T1_split : forall s,
    (T_split s <= k_split * N.of_nat (destroy_work s) * N.of_nat (function_width s + 1))%N.
  (** Copy production and checking fit the original argument-occurrence budget. *)
  Parameter T2_copies : forall s split_s, split s = Some split_s ->
    (T_copies split_s <= k_copies * N.of_nat (destroy_work s) *
      N.of_nat (function_width s + 1))%N.
  (** The wrapper charges exactly the selected transformation phases. *)
  Parameter T3_wrapper : forall s,
    (T_destroy s <= T_split s +
      match split s with None => k_wrap | Some split_s => T_copies split_s + k_wrap end)%N.
  (* SIG-QUESTION: fresh block/value/temporary widths, indexed block lookups and the actual
     parallel-move calls need composition budgets at the published source-only width. *)
End DESTROY_PLAN.

Module Type DESTROY_ALL (O : OPS)
    (K : KEY_T with Definition t := O.K) (G : KEY_T with Definition t := O.G)
    (P : TYPE with Definition t := func positive O.K O.G) (E : TYPE)
    (C : CFG_T P PosKeyT E) (S : SSA_T P PosKeyT E C PosKeyT K G)
    (PM : PARMOVE_T)
    (OL : LAWS O) (B : LANG_SSA_LINK O K G P E C S) :=
  DESTROY_T O K G P E C S PM OL B <+ DESTROY_PLAN O K G P E C S PM OL B.
