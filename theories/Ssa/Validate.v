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
    (P : TYPE with Definition t := func positive O.K O.G)
    (Q : TYPE) (R : LANG_PREPARE_OPS O Q) (E : TYPE)
    (C : CFG_INDEXED_OPS Q PosKeyCode E) (S : SSA_OPS Q PosKeyCode E C PosKeyCode K G)
    (DG : DIGRAPH_OPS) (D : DOM_OPS) <: VALIDATE_OPS O K G P Q R E C S DG D.
  (* STUB-CODE *)
  Definition check (_ _ : P.t) (_ : cert) : bool := false.
  (* STUB-CODE *)
  Definition check_ssa (_ : P.t) : bool := false.
End ValidateCode.

Module Validate (O : OPS)
    (K : KEY with Definition t := O.K) (G : KEY with Definition t := O.G)
    (P : TYPE with Definition t := func positive O.K O.G)
    (Q : TYPE) (R : LANG_PREPARE_OPS O Q) (E : TYPE)
    (C : CFG Q PosKey E) (S : SSA Q PosKey E C PosKey K G)
    (DG : DIGRAPH) (D : DOM) (B : LANG_SSA_LINK O K G Q R E C S)
    <: VALIDATE O K G P Q R E C S DG D B.
  Include ValidateCode O K G P Q R E C S DG D.
  Include VALIDATE_SPEC O K G P Q R E C S DG D.
  Lemma check_sound : forall p s c, imp_form p -> check p s c = true ->
    forall n ins, run_with O.eval O.test n s ins = run_with O.eval O.test n p ins.
  Proof. Admitted. (* STUB *)
  Lemma check_ssa_sound : forall s, check_ssa s = true -> ssa_wf s.
  Proof. Admitted. (* STUB *)
  Lemma check_core_ssa_sound : forall s, check_ssa s = true -> S.wf (R.prepare s).
  Proof. Admitted. (* STUB *)
End Validate.

Module ValidateT (O : OPS)
    (K : KEY_T with Definition t := O.K) (G : KEY_T with Definition t := O.G)
    (P : TYPE with Definition t := func positive O.K O.G)
    (Q : TYPE) (R : LANG_PREPARE_T O Q) (E : KEY_T)
    (C : CFG_T Q PosKeyT E) (S : SSA_T Q PosKeyT E C PosKeyT K G)
    (DG : DIGRAPH_T) (D : DOM_T) (B : LANG_SSA_LINK O K G Q R E C S)
    <: VALIDATE_ALL O K G P Q R E C S DG D B.
  Include Validate O K G P Q R E C S DG D B.
  TimeFun check.
  TimeFun check_ssa.
  TimeFun graph.
  Definition c_val : N := 1. (* STUB *)
  Definition dom_bound s := N.of_nat ((graph_n (base (graph s)) +
    graph_e (base (graph s)) + 1) * (Nat.log2 (graph_n (base (graph s))) + 1)).
  Definition check_width (p s : P.t) (c : cert) :=
    function_width p + function_width s + vertex_width (cert_ids c).
  Definition op_bits (p : P.t) :=
    fold_right (fun item n =>
      fold_right (fun i m => K.bits (snd (fst i)) + m) 0 (code _ _ _ (snd item)) +
      match term _ _ _ (snd item) with
      | Branch g _ _ _ _ _ => G.bits g
      | _ => 0
      end + n) 0 (blocks _ _ _ p).
  (** Translation checking charges both functions and the supplied certificate. *)
  Lemma T_check_le : forall p s c,
    (T_check p s c <= c_val * N.of_nat (function_size p + function_size s + cert_size c + 1) *
      N.of_nat (check_width p s c + 1) + c_val * N.of_nat (op_bits p + 1))%N.
  Proof. Admitted. (* STUB *)
  (** SSA checking includes the core dominator construction budget. *)
  Lemma T_check_ssa_le : forall s,
    (T_check_ssa s <= c_val * (N.of_nat (function_size s + 1) + dom_bound s) *
      N.of_nat (function_width s + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Translation checking has the published certificate-sensitive bit-cost bound. *)
  Lemma check_bigO : bigO (fun _ : P.t * P.t * cert => True)
    (fun '(p, s, c) => N.of_nat ((function_size p + function_size s + cert_size c + 1) *
      (check_width p s c + 1) + op_bits p + 1)) (fun '(p, s, c) => T_check p s c).
  Proof. Admitted. (* STUB *)
  (** SSA checking has the published syntax and dominator bit-cost bound. *)
  Lemma check_ssa_bigO : bigO (fun _ : P.t => True)
    (fun s => ((N.of_nat (function_size s + 1) + dom_bound s) *
      N.of_nat (function_width s + 1))%N) T_check_ssa.
  Proof. Admitted. (* STUB *)
  (* STUB-CODE *)
  Definition tables (_ _ : P.t) (_ : cert) : check_tables O.K O.G :=
    CheckTables Empty Empty Empty Empty.
  TimeFun tables.
  (* STUB-CODE *)
  Definition check_entry (_ _ : P.t) (_ : cert) (_ : check_tables O.K O.G) : bool := false.
  (* STUB-CODE *)
  Definition check_block (_ : check_tables O.K O.G) (_ : positive) : bool := false.
  (* STUB-CODE *)
  Definition check_code (_ _ : list (positive * O.K * list positive))
      (_ : renaming) (_ : list positive) : option renaming := None.
  (* STUB-CODE *)
  Definition check_edge (_ : check_tables O.K O.G) (_ _ : positive) (_ : renaming) : bool := false.
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
    check_entry p s c (tables p s c) = true /\ forall b body,
      In (b, body) (blocks _ _ _ p) -> check_block (tables p s c) b = true.
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
    check p s c = true -> check_edge (tables p s c) b target rho = true ->
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
  (** Graph preparation and certificate work fit the syntax and dominator budget. *)
  Lemma T1_dom : forall s,
    (T_graph s + T_dom_cert s +
      D.T_check (graph s) (entry _ _ _ s) (fst (dom_cert s)) (snd (dom_cert s)) <=
      k_ssa * (N.of_nat (function_size s + 1) + dom_bound s) *
        N.of_nat (function_width s + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Entry checking charges both input lists and the indexed certificate row. *)
  Lemma T2b_entry : forall p s c,
    (T_check_entry p s c (tables p s c) <= k_entry *
      N.of_nat (length (inputs _ _ _ p) + length (inputs _ _ _ s) +
        length (cert_live c (entry _ _ _ p)) + 1) *
      N.of_nat (check_width p s c + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Code checking indexes its initial renaming and reads both instruction streams once. *)
  Lemma T2c_code : forall ic sc rho live,
    (T_check_code ic sc rho live <= k_code *
      N.of_nat (length rho + length live + length ic + length sc +
        fold_right (fun i n => (length (snd i) + n)%nat) 0%nat (ic ++ sc) + 1) *
      N.of_nat (vertex_width (live ++
        flat_map (fun xy => [fst xy; snd xy]) rho ++
        flat_map (fun i => fst (fst i) :: snd i) (ic ++ sc)) + 1) +
      k_code * N.of_nat
        (fold_right (fun i n => (K.bits (snd (fst i)) + n)%nat) 0%nat ic + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Indexed edge checking charges the two exits and the destination certificate row. *)
  Lemma T2d_edge : forall p s c b target rho ib sb,
    find_block b (blocks _ _ _ p) = Some ib ->
    find_block b (blocks _ _ _ s) = Some sb ->
    (T_check_edge (tables p s c) b target rho <= k_edge *
      N.of_nat (length rho + length (exit_uses (term _ _ _ ib)) +
        length (exit_uses (term _ _ _ sb)) + length (cert_live c target) + 1) *
      N.of_nat (check_width p s c +
        vertex_width (flat_map (fun xy => [fst xy; snd xy]) rho) + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Translation checking indexes the certificate, checks the entry and every source block. *)
  Lemma T2_checks : forall p s c,
    (T_check p s c <= T_tables p s c +
      k_blocks * N.of_nat (function_size p + 1) * N.of_nat (check_width p s c + 1) +
      T_check_entry p s c (tables p s c) +
      fold_right N.add 0%N (map (fun item => T_check_block (tables p s c) (fst item))
        (first_blocks (blocks _ _ _ p))))%N.
  Proof. Admitted. (* STUB *)
  (** One block check charges its two bodies, its operands, its live row, its exit and its
      operators. *)
  Lemma T2a_block : forall p s c b ib,
    find_block b (blocks _ _ _ p) = Some ib ->
    (T_check_block (tables p s c) b <= k_code *
      N.of_nat (length (block_defs ib) + length (exit_uses (term _ _ _ ib)) +
        length (code _ _ _ ib) +
        fold_right (fun i n => (length (snd i) + n)%nat) 0%nat (code _ _ _ ib) +
        length (cert_live c b) + 1) *
      N.of_nat (check_width p s c + 1) +
      k_code * N.of_nat (fold_right (fun i n => (K.bits (snd (fst i)) + n)%nat) 0%nat
        (code _ _ _ ib) +
        match term _ _ _ ib with
        | Branch g _ _ _ _ _ => G.bits g
        | _ => 0
        end + 1))%N.
  Proof. Admitted. (* STUB *)
  (** SSA checking adds the strict local-order and dominance queries to the graph phase. *)
  Lemma T3_ssa : forall s,
    (T_check_ssa s <= T_graph s + T_dom_cert s +
      D.T_check (graph s) (entry _ _ _ s) (fst (dom_cert s)) (snd (dom_cert s)) +
      k_ssa * N.of_nat (function_size s + 1) * N.of_nat (function_width s + 1))%N.
  Proof. Admitted. (* STUB *)
  (** The tables retain the first body and certificate row for each identifier. *)
  Lemma F0_tables : forall p s c b,
    trie_get b (source_bodies (tables p s c)) = find_block b (blocks _ _ _ p) /\
    trie_get b (target_bodies (tables p s c)) = find_block b (blocks _ _ _ s) /\
    trie_get b (cert_envs (tables p s c)) = lookup b (fst c) /\
    index_row (cert_rows (tables p s c)) b = cert_live c b.
  Proof. Admitted. (* STUB *)
  (** Building lookup tables scans the functions and certificate once. *)
  Lemma T0_tables : forall p s c,
    (T_tables p s c <= k_blocks *
      N.of_nat (function_size p + function_size s + cert_size c + 1) *
      N.of_nat (check_width p s c + 1))%N.
  Proof. Admitted. (* STUB *)
End ValidateT.
