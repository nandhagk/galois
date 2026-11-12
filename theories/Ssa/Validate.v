(** * Placeholder SSA validation

    This module supplies the translation and SSA checkers.
    For example, its placeholder rejects every certificate.
    Builds on: ValidateSig. *)

From Stdlib Require Import List PArith NArith.
From Argent Require Import Time Tactics Std BigO Loop.
From Galois.Base Require Import KeySig Key Trie.
From Galois.Graph Require Import Data Spec DigraphSig DomSig.
From Galois.Program Require Import CfgSig SsaSig.
From Galois.Ssa Require Import Lang LiveSig ValidateSig.
Import List.ListNotations.

Module ValidateCode (O : OPS)
    (K : KEY_OPS with Definition t := O.K) (G : KEY_OPS with Definition t := O.G)
    (P : TYPE with Definition t := func positive O.K O.G) (E : TYPE)
    (C : CFG_INDEXED_OPS P PosKeyCode E) (S : SSA_OPS P PosKeyCode E C PosKeyCode K G)
    (DG : DIGRAPH_OPS) (D : DOM_OPS) <: VALIDATE_OPS O K G P E C S DG D.
  (* STUB-CODE *)
  Definition check (_ _ : P.t) (_ : cert) : bool := false.
  (* STUB-CODE *)
  Definition check_ssa (_ : P.t) : bool := false.
End ValidateCode.

Module Validate (O : OPS)
    (K : KEY with Definition t := O.K) (G : KEY with Definition t := O.G)
    (P : TYPE with Definition t := func positive O.K O.G) (E : TYPE)
    (C : CFG P PosKey E) (S : SSA P PosKey E C PosKey K G)
    (DG : DIGRAPH) (D : DOM) (B : LANG_SSA_LINK O K G P E C S)
    <: VALIDATE O K G P E C S DG D B.
  Include ValidateCode O K G P E C S DG D.
  Include VALIDATE_SPEC O K G P E C S DG D.
  Lemma check_sound : forall p s c, imp_form p -> check p s c = true ->
    forall n ins, run_with O.eval O.test n s ins = run_with O.eval O.test n p ins.
  Proof. Admitted.
  Lemma check_ssa_sound : forall s, check_ssa s = true -> ssa_wf s.
  Proof. Admitted.
  Lemma check_core_ssa_sound : forall s, check_ssa s = true -> S.wf s.
  Proof. Admitted.
End Validate.

Module ValidateT (O : OPS)
    (K : KEY_T with Definition t := O.K) (G : KEY_T with Definition t := O.G)
    (P : TYPE with Definition t := func positive O.K O.G) (E : TYPE)
    (C : CFG_T P PosKeyT E) (S : SSA_T P PosKeyT E C PosKeyT K G)
    (DG : DIGRAPH_T) (D : DOM_T) (B : LANG_SSA_LINK O K G P E C S)
    <: VALIDATE_ALL O K G P E C S DG D B.
  Include Validate O K G P E C S DG D B.
  TimeFun check.
  TimeFun check_ssa.
  TimeFun graph.
  Definition c_val : N := 1. (* STUB *)
  Definition dom_bound s := N.of_nat ((graph_n (base (graph s)) +
    graph_e (base (graph s)) + 1) * (Nat.log2 (graph_n (base (graph s))) + 1)).
  Lemma T_check_le : forall p s c,
    (T_check p s c <= c_val * N.of_nat (function_size p + function_size s + cert_size c + 1) *
      N.of_nat (function_width p + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_check_ssa_le : forall s,
    (T_check_ssa s <= c_val * (N.of_nat (function_size s + 1) + dom_bound s) *
      N.of_nat (function_width s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma check_bigO : bigO (fun _ : P.t * P.t * cert => True)
    (fun '(p, s, c) => N.of_nat ((function_size p + function_size s + cert_size c + 1) *
      (function_width p + 1))) (fun '(p, s, c) => T_check p s c).
  Proof. Admitted. (* STUB *)
  Lemma check_ssa_bigO : bigO (fun _ : P.t => True)
    (fun s => ((N.of_nat (function_size s + 1) + dom_bound s) *
      N.of_nat (function_width s + 1))%N) T_check_ssa.
  Proof. Admitted. (* STUB *)
  (* STUB-CODE *)
  Definition check_entry (_ _ : P.t) (_ : cert) : bool := false.
  (* STUB-CODE *)
  Definition check_block (_ _ : P.t) (_ : cert) (_ : positive) : bool := false.
  (* STUB-CODE *)
  Definition check_code (_ _ : list (positive * O.K * list positive))
      (_ : renaming) (_ : list positive) : option renaming := None.
  (* STUB-CODE *)
  Definition check_edge (_ _ : P.t) (_ : cert) (_ _ : positive) (_ : renaming) : bool := false.
  (* STUB-CODE *)
  Definition dom_cert (_ : P.t) : ptrie positive * list positive := (Empty, []).
  TimeFun check_entry.
  TimeFun check_block.
  TimeFun check_code.
  TimeFun check_edge.
  TimeFun dom_cert.
  Definition k_entry : N := 1. (* STUB *)
  Definition k_code : N := 1. (* STUB *)
  Definition k_edge : N := 1. (* STUB *)
  Definition k_blocks : N := 1. (* STUB *)
  Definition k_ssa : N := 1. (* STUB *)
  Definition agrees (rho : renaming) (xs : list positive) (ss si : env O.C) :=
    forall x, In x xs -> exists y, lookup x rho = Some y /\ lookup y ss = lookup x si.
  Definition code_defs (xs : list (positive * O.K * list positive)) :=
    map (fun i => fst (fst i)) xs.
  Lemma F1_checks : forall p s c, check p s c = true ->
    check_entry p s c = true /\ forall b body, In (b, body) (blocks _ _ _ p) ->
      check_block p s c b = true.
  Proof. Admitted. (* STUB *)
  Lemma F2_code_sim : forall ic sc rho rho' live ss si,
    check_code ic sc rho live = Some rho' -> agrees rho live ss si ->
    match exec_code O.eval sc ss, exec_code O.eval ic si with
    | None, None => True
    | Some ss', Some si' => agrees rho' (code_defs ic ++ live) ss' si'
    | _, _ => False
    end.
  Proof. Admitted. (* STUB *)
  Lemma F3_edge_sim : forall p s c b target rho ss si sa ia sb ib sx ix choice,
    check p s c = true -> check_edge p s c b target rho = true ->
    find_block b (blocks _ _ _ s) = Some sb ->
    find_block b (blocks _ _ _ p) = Some ib ->
    edge_choice (term _ _ _ sb) choice = Some (target, sx) ->
    edge_choice (term _ _ _ ib) choice = Some (target, ix) ->
    read_vars ss sx = Some sa -> read_vars si ix = Some ia ->
    agrees rho (cert_live c target) ss si ->
    state_sim p s c (target, sa, ss) (target, ia, si).
  Proof. Admitted. (* STUB *)
  Lemma F4_block_sim : forall p s c ss si,
    imp_form p -> check p s c = true -> state_sim p s c ss si ->
    outcome_sim p s c (step O.eval O.test s ss) (step O.eval O.test p si).
  Proof. Admitted. (* STUB *)
  Lemma F5_entry_sim : forall p s c ins ss si,
    imp_form p -> check p s c = true ->
    bind_vars (inputs _ _ _ s) ins [] = Some ss ->
    bind_vars (inputs _ _ _ p) ins [] = Some si ->
    state_sim p s c (entry _ _ _ s, [], ss) (entry _ _ _ p, [], si).
  Proof. Admitted. (* STUB *)
  Lemma F6_input_arity : forall p s c, check p s c = true ->
    length (inputs _ _ _ s) = length (inputs _ _ _ p).
  Proof. Admitted. (* STUB *)
  Lemma F7_run_sim : forall p s c n ss si,
    imp_form p -> check p s c = true -> state_sim p s c ss si ->
    outcome_sim p s c (loop_fuel (step O.eval O.test s) n ss)
      (loop_fuel (step O.eval O.test p) n si).
  Proof. Admitted. (* STUB *)
  Lemma F8_dom_checked : forall s, check_ssa s = true ->
    D.check (graph s) (entry _ _ _ s) (fst (dom_cert s)) (snd (dom_cert s)) = true.
  Proof. Admitted. (* STUB *)
  Lemma F9_ssa_wf : forall s, check_ssa s = true -> ssa_wf s.
  Proof. Admitted. (* STUB *)
  Lemma T1_dom : forall s,
    (T_graph s + T_dom_cert s +
      D.T_check (graph s) (entry _ _ _ s) (fst (dom_cert s)) (snd (dom_cert s)) <=
      k_ssa * (N.of_nat (function_size s + 1) + dom_bound s) *
        N.of_nat (function_width s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T2_checks : forall p s c,
    (T_check p s c <= k_blocks *
      N.of_nat (function_size p + function_size s + cert_size c + 1) *
      N.of_nat (function_width p + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T3_ssa : forall s,
    (T_check_ssa s <= k_ssa * (N.of_nat (function_size s + 1) + dom_bound s) *
      N.of_nat (function_width s + 1))%N.
  Proof. Admitted. (* STUB *)
End ValidateT.
