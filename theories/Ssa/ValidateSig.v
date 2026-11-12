(** * Translation validation for SSA construction

    A certificate relates imperative variables to SSA values at each block entry.
    For example, incoming arguments supply the values named by the target block's certificate.
    Builds on: Ssa.Lang, core SSA presentations, graph preparation and dominator checking. *)

From Stdlib Require Import List PArith NArith.
From Argent Require Import Time Std BigO Loop.
From Galois.Base Require Import KeySig Key Trie.
From Galois.Graph Require Import Data Spec DigraphSig DomSig.
From Galois.Program Require Import CfgSig SsaSig.
From Galois.Ssa Require Import Lang LiveSig.
Import List.ListNotations.

Definition renaming := list (positive * positive).
Definition cert := (list (positive * renaming) * list (positive * list positive))%type.
Definition machine_state (A : Type) := (positive * list A * env A)%type.

Definition cert_env (c : cert) (b x : positive) : option positive :=
  match lookup b (fst c) with
  | Some row => lookup x row
  | None => None
  end.
TimeFun cert_env.

Definition cert_live (c : cert) (b : positive) : list positive :=
  match lookup b (snd c) with
  | Some row => row
  | None => []
  end.
TimeFun cert_live.

Definition cert_size (c : cert) : nat :=
  fold_right (fun row n => 1 + 2 * length (snd row) + n) 0 (fst c) +
    fold_right (fun row n => 1 + length (snd row) + n) 0 (snd c).
TimeFun cert_size.

Definition cert_ids (c : cert) : list positive :=
  flat_map (fun row => fst row :: flat_map (fun xy => [fst xy; snd xy]) (snd row)) (fst c) ++
  flat_map (fun row => fst row :: snd row) (snd c).
TimeFun cert_ids.

Definition cfg_graph {E} (vs : list positive) (es : list E)
    (src dst : E -> positive) : digraph :=
  Digraph vs (fold_right (fun e rows =>
    let u := src e in
    PTrieCode.set u (dst e :: match trie_get u rows with Some xs => xs | None => [] end)
      rows) Empty es).
TimeFun cfg_graph.

Definition edge_choice {G} (e : exit positive G) (choice : bool) :
    option (positive * list positive) :=
  match e with
  | Jump b xs => Some (b, xs)
  | Branch _ _ b xs c ys => if choice then Some (b, xs) else Some (c, ys)
  | Return _ => None
  end.
TimeFun edge_choice.

(** The supplied core readers describe this block language and its path relation. *)
Module Type LANG_SSA_LINK (O : OPS) (K : KEY with Definition t := O.K)
    (G : KEY with Definition t := O.G)
    (P : TYPE with Definition t := func positive O.K O.G) (E : TYPE)
    (C : CFG P PosKey E) (S : SSA P PosKey E C PosKey K G).
  (** The core entry is the language entry. *)
  Parameter entries_agree : forall p, C.entries p = [entry _ _ _ p].
  (** The core node inventory retains the listed block order. *)
  Parameter nodes_agree : forall p, C.nodes p = map fst (blocks _ _ _ p).
  (** Core paths and language paths traverse the same block identifiers. *)
  Parameter paths_agree : forall p a route b,
    presentation_path (C.edges p) (C.src p) (C.dst p) a route b <-> Lang.path p a route b.
  (** Parameter readers use the language's first matching block. *)
  Parameter params_agree : forall p b, S.params p b =
    match find_block b (blocks _ _ _ p) with
    | Some body => params _ _ _ body
    | None => []
    end.
  (** Language SSA well-formedness supplies the public core SSA laws. *)
  Parameter wf_from_lang : forall p, ssa_wf p -> S.wf p.
End LANG_SSA_LINK.

Module Type VALIDATE_OPS (O : OPS)
    (K : KEY_OPS with Definition t := O.K) (G : KEY_OPS with Definition t := O.G)
    (P : TYPE with Definition t := func positive O.K O.G) (E : TYPE)
    (C : CFG_INDEXED_OPS P PosKeyCode E) (S : SSA_OPS P PosKeyCode E C PosKeyCode K G)
    (DG : DIGRAPH_OPS) (D : DOM_OPS).
  Parameter check : P.t -> P.t -> cert -> bool.
  Parameter check_ssa : P.t -> bool.
End VALIDATE_OPS.

Module Type VALIDATE_SPEC (O : OPS)
    (K : KEY_OPS with Definition t := O.K) (G : KEY_OPS with Definition t := O.G)
    (P : TYPE with Definition t := func positive O.K O.G) (E : TYPE)
    (C : CFG_INDEXED_OPS P PosKeyCode E) (S : SSA_OPS P PosKeyCode E C PosKeyCode K G)
    (DG : DIGRAPH_OPS) (D : DOM_OPS)
    (Import V : VALIDATE_OPS O K G P E C S DG D).
  Definition graph p := DG.prepare (cfg_graph (C.nodes p) (C.edges p) (C.src p) (C.dst p)).
  Definition sim (c : cert) b (ss si : env O.C) := forall x, In x (cert_live c b) ->
    exists y, cert_env c b x = Some y /\ lookup y ss = lookup x si.
  Definition state_sim (p s : P.t) (c : cert)
      (ss si : machine_state O.C) : Prop :=
    let '(bs, actuals_s, es) := ss in
    let '(bi, actuals_i, ei) := si in
    bs = bi /\
    match find_block bs (blocks _ _ _ s), find_block bi (blocks _ _ _ p) with
    | None, None => True
    | Some sb, Some ib =>
        match bind_vars (params _ _ _ sb) actuals_s es,
          bind_vars (params _ _ _ ib) actuals_i ei with
        | None, None => True
        | Some entered_s, Some entered_i => sim c bi entered_s entered_i
        | _, _ => False
        end
    | _, _ => False
    end.
  Definition outcome_sim p s c (os oi : machine_state O.C + result O.C) :=
    match os, oi with
    | inl ss, inl si => state_sim p s c ss si
    | inr rs, inr ri => rs = ri
    | _, _ => False
    end.
End VALIDATE_SPEC.

Module Type VALIDATE_LAWS (O : OPS)
    (K : KEY with Definition t := O.K) (G : KEY with Definition t := O.G)
    (P : TYPE with Definition t := func positive O.K O.G) (E : TYPE)
    (C : CFG P PosKey E) (S : SSA P PosKey E C PosKey K G)
    (DG : DIGRAPH) (D : DOM)
    (B : LANG_SSA_LINK O K G P E C S)
    (Import V : VALIDATE_OPS O K G P E C S DG D).
  (** An accepted translation has the same result at every fuel and input list. *)
  Parameter check_sound : forall p s c, imp_form p -> check p s c = true ->
    forall n ins, run_with O.eval O.test n s ins = run_with O.eval O.test n p ins.
  (** Acceptance of the SSA checker establishes the language's strict definition discipline. *)
  Parameter check_ssa_sound : forall s, check_ssa s = true -> ssa_wf s.
  (** Accepted SSA functions also meet the supplied core presentation's laws. *)
  Parameter check_core_ssa_sound : forall s, check_ssa s = true -> S.wf s.
End VALIDATE_LAWS.

Module Type VALIDATE (O : OPS)
    (K : KEY with Definition t := O.K) (G : KEY with Definition t := O.G)
    (P : TYPE with Definition t := func positive O.K O.G) (E : TYPE)
    (C : CFG P PosKey E) (S : SSA P PosKey E C PosKey K G)
    (DG : DIGRAPH) (D : DOM)
    (B : LANG_SSA_LINK O K G P E C S) :=
  VALIDATE_OPS O K G P E C S DG D <+ VALIDATE_SPEC O K G P E C S DG D <+
  VALIDATE_LAWS O K G P E C S DG D B.

Module Type VALIDATE_TIME (O : OPS)
    (K : KEY_T with Definition t := O.K) (G : KEY_T with Definition t := O.G)
    (P : TYPE with Definition t := func positive O.K O.G) (E : KEY_T)
    (C : CFG_T P PosKeyT E) (S : SSA_T P PosKeyT E C PosKeyT K G)
    (DG : DIGRAPH_T) (D : DOM_T)
    (B : LANG_SSA_LINK O K G P E C S)
    (Import V : VALIDATE O K G P E C S DG D B).
  Parameter T_check : P.t -> P.t -> cert -> N.
  Parameter T_check_ssa : P.t -> N.
  Parameter c_val : N.
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
  Parameter T_check_le : forall p s c,
    (T_check p s c <= c_val * N.of_nat (function_size p + function_size s + cert_size c + 1) *
      N.of_nat (check_width p s c + 1) + c_val * N.of_nat (op_bits p + 1))%N.
  (** SSA checking includes the core dominator construction budget. *)
  Parameter T_check_ssa_le : forall s,
    (T_check_ssa s <= c_val * (N.of_nat (function_size s + 1) + dom_bound s) *
      N.of_nat (function_width s + 1))%N.
  (** Translation checking has the published certificate-sensitive bit-cost bound. *)
  Parameter check_bigO : bigO (fun _ : P.t * P.t * cert => True)
    (fun '(p, s, c) => N.of_nat ((function_size p + function_size s + cert_size c + 1) *
      (check_width p s c + 1) + op_bits p + 1)) (fun '(p, s, c) => T_check p s c).
  (** SSA checking has the published syntax and dominator bit-cost bound. *)
  Parameter check_ssa_bigO : bigO (fun _ : P.t => True)
    (fun s => ((N.of_nat (function_size s + 1) + dom_bound s) *
      N.of_nat (function_width s + 1))%N) T_check_ssa.
End VALIDATE_TIME.

Module Type VALIDATE_T (O : OPS)
    (K : KEY_T with Definition t := O.K) (G : KEY_T with Definition t := O.G)
    (P : TYPE with Definition t := func positive O.K O.G) (E : KEY_T)
    (C : CFG_T P PosKeyT E) (S : SSA_T P PosKeyT E C PosKeyT K G)
    (DG : DIGRAPH_T) (D : DOM_T)
    (B : LANG_SSA_LINK O K G P E C S) :=
  VALIDATE O K G P E C S DG D B <+ VALIDATE_TIME O K G P E C S DG D B.

Module Type VALIDATE_PLAN (O : OPS)
    (K : KEY_T with Definition t := O.K) (G : KEY_T with Definition t := O.G)
    (P : TYPE with Definition t := func positive O.K O.G) (E : KEY_T)
    (C : CFG_T P PosKeyT E) (S : SSA_T P PosKeyT E C PosKeyT K G)
    (DG : DIGRAPH_T) (D : DOM_T)
    (B : LANG_SSA_LINK O K G P E C S)
    (Import V : VALIDATE_T O K G P E C S DG D B).
  Parameter check_entry : P.t -> P.t -> cert -> bool.
  Parameter check_block : P.t -> P.t -> cert -> positive -> bool.
  Parameter check_code : list (positive * O.K * list positive) ->
    list (positive * O.K * list positive) -> renaming -> list positive -> option renaming.
  Parameter check_edge : P.t -> P.t -> cert -> positive -> positive -> renaming -> bool.
  Parameter dom_cert : P.t -> ptrie positive * list positive.
  Parameter T_graph : P.t -> N.
  Parameter T_check_entry : P.t -> P.t -> cert -> N.
  Parameter T_check_block : P.t -> P.t -> cert -> positive -> N.
  Parameter T_check_code : list (positive * O.K * list positive) ->
    list (positive * O.K * list positive) -> renaming -> list positive -> N.
  Parameter T_check_edge : P.t -> P.t -> cert -> positive -> positive -> renaming -> N.
  Parameter T_dom_cert : P.t -> N.
  Parameter k_entry k_code k_edge k_blocks k_ssa : N.
  Definition agrees (rho : renaming) (xs : list positive) (ss si : env O.C) :=
    forall x, In x xs -> exists y, lookup x rho = Some y /\ lookup y ss = lookup x si.
  Definition code_defs (xs : list (positive * O.K * list positive)) :=
    map (fun i => fst (fst i)) xs.
  (** Acceptance checks the entry and every listed source block. *)
  Parameter F1_checks : forall p s c, check p s c = true ->
    check_entry p s c = true /\ forall b body, In (b, body) (blocks _ _ _ p) ->
      check_block p s c b = true.
  (** Statement checking carries the extended variable relation through equal operations. *)
  Parameter F2_code_sim : forall ic sc rho rho' live ss si,
    check_code ic sc rho live = Some rho' -> agrees rho live ss si ->
    match exec_code O.eval sc ss, exec_code O.eval ic si with
    | None, None => True
    | Some ss', Some si' => agrees rho' (code_defs ic ++ live) ss' si'
    | _, _ => False
    end.
  (** Checked outgoing copies re-establish the destination's entry relation. *)
  Parameter F3_edge_sim : forall p s c b target rho ss si sa ia sb ib sx ix choice,
    check p s c = true -> check_edge p s c b target rho = true ->
    find_block b (blocks _ _ _ s) = Some sb ->
    find_block b (blocks _ _ _ p) = Some ib ->
    edge_choice (term _ _ _ sb) choice = Some (target, sx) ->
    edge_choice (term _ _ _ ib) choice = Some (target, ix) ->
    read_vars ss sx = Some sa -> read_vars si ix = Some ia ->
    agrees rho (cert_live c target) ss si ->
    state_sim p s c (target, sa, ss) (target, ia, si).
  (** A checked block has equal ending outcomes or related successor states. *)
  Parameter F4_block_sim : forall p s c ss si,
    imp_form p -> check p s c = true -> state_sim p s c ss si ->
    outcome_sim p s c (step O.eval O.test s ss) (step O.eval O.test p si).
  (** A successful input binding establishes the entry simulation. *)
  Parameter F5_entry_sim : forall p s c ins ss si,
    imp_form p -> check p s c = true ->
    bind_vars (inputs _ _ _ s) ins [] = Some ss ->
    bind_vars (inputs _ _ _ p) ins [] = Some si ->
    state_sim p s c (entry _ _ _ s, [], ss) (entry _ _ _ p, [], si).
  (** The checked input lists reject the same arity mismatches. *)
  Parameter F6_input_arity : forall p s c, check p s c = true ->
    length (inputs _ _ _ s) = length (inputs _ _ _ p).
  (** Induction on fuel transports the block simulation to matching loop outcomes. *)
  Parameter F7_run_sim : forall p s c n ss si,
    imp_form p -> check p s c = true -> state_sim p s c ss si ->
    outcome_sim p s c (loop_fuel (step O.eval O.test s) n ss)
      (loop_fuel (step O.eval O.test p) n si).
  (** The SSA checker validates the dominator certificate it uses. *)
  Parameter F8_dom_checked : forall s, check_ssa s = true ->
    D.check (graph s) (entry _ _ _ s) (fst (dom_cert s)) (snd (dom_cert s)) = true.
  (** Accepted strict local-order and dominance checks establish language SSA form. *)
  Parameter F9_ssa_wf : forall s, check_ssa s = true -> ssa_wf s.
  (** Graph preparation and certificate work fit the syntax and dominator budget. *)
  Parameter T1_dom : forall s,
    (T_graph s + T_dom_cert s +
      D.T_check (graph s) (entry _ _ _ s) (fst (dom_cert s)) (snd (dom_cert s)) <=
      k_ssa * (N.of_nat (function_size s + 1) + dom_bound s) *
        N.of_nat (function_width s + 1))%N.
  (** Entry checking charges both input lists and the indexed certificate row. *)
  Parameter T2b_entry : forall p s c,
    (T_check_entry p s c <= k_entry *
      N.of_nat (length (inputs _ _ _ p) + length (inputs _ _ _ s) +
        length (cert_live c (entry _ _ _ p)) + 1) *
      N.of_nat (check_width p s c + 1))%N.
  (** Code checking indexes its initial renaming and reads both instruction streams once. *)
  Parameter T2c_code : forall ic sc rho live,
    (T_check_code ic sc rho live <= k_code *
      N.of_nat (length rho + length live + length ic + length sc +
        fold_right (fun i n => (length (snd i) + n)%nat) 0%nat (ic ++ sc) + 1) *
      N.of_nat (vertex_width (live ++
        flat_map (fun xy => [fst xy; snd xy]) rho ++
        flat_map (fun i => fst (fst i) :: snd i) (ic ++ sc)) + 1) +
      k_code * N.of_nat
        (fold_right (fun i n => (K.bits (snd (fst i)) + n)%nat) 0%nat ic + 1))%N.
  (** Indexed edge checking charges the two exits and the destination certificate row. *)
  Parameter T2d_edge : forall p s c b target rho ib sb,
    find_block b (blocks _ _ _ p) = Some ib ->
    find_block b (blocks _ _ _ s) = Some sb ->
    (T_check_edge p s c b target rho <= k_edge *
      N.of_nat (length rho + length (exit_uses (term _ _ _ ib)) +
        length (exit_uses (term _ _ _ sb)) + length (cert_live c target) + 1) *
      N.of_nat (check_width p s c +
        vertex_width (flat_map (fun xy => [fst xy; snd xy]) rho) + 1))%N.
  (** Translation checking indexes the certificate, checks the entry and every source block. *)
  Parameter T2_checks : forall p s c,
    (T_check p s c <= k_blocks * N.of_nat (cert_size c + function_size s + 1) *
      N.of_nat (check_width p s c + 1) + T_check_entry p s c +
      fold_right N.add 0%N (map (fun item => T_check_block p s c (fst item)) (blocks _ _ _ p)))%N.
  (** One block check charges its two bodies, its operands, its exit and its operators. *)
  Parameter T2a_block : forall p s c b ib,
    find_block b (blocks _ _ _ p) = Some ib ->
    (T_check_block p s c b <= k_code *
      N.of_nat (length (block_defs ib) + length (exit_uses (term _ _ _ ib)) +
        length (code _ _ _ ib) +
        fold_right (fun i n => (length (snd i) + n)%nat) 0%nat (code _ _ _ ib) + 1) *
      N.of_nat (check_width p s c + 1) +
      k_code * N.of_nat (fold_right (fun i n => (K.bits (snd (fst i)) + n)%nat) 0%nat
        (code _ _ _ ib) +
        match term _ _ _ ib with
        | Branch g _ _ _ _ _ => G.bits g
        | _ => 0
        end + 1))%N.
  (** SSA checking adds the strict local-order and dominance queries to the graph phase. *)
  Parameter T3_ssa : forall s,
    (T_check_ssa s <= T_graph s + T_dom_cert s +
      D.T_check (graph s) (entry _ _ _ s) (fst (dom_cert s)) (snd (dom_cert s)) +
      k_ssa * N.of_nat (function_size s + 1) * N.of_nat (function_width s + 1))%N.
End VALIDATE_PLAN.

Module Type VALIDATE_ALL (O : OPS)
    (K : KEY_T with Definition t := O.K) (G : KEY_T with Definition t := O.G)
    (P : TYPE with Definition t := func positive O.K O.G) (E : KEY_T)
    (C : CFG_T P PosKeyT E) (S : SSA_T P PosKeyT E C PosKeyT K G)
    (DG : DIGRAPH_T) (D : DOM_T)
    (B : LANG_SSA_LINK O K G P E C S) :=
  VALIDATE_T O K G P E C S DG D B <+ VALIDATE_PLAN O K G P E C S DG D B.
