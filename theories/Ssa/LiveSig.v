(** * Untrusted liveness production

    A producer lists variables needed at each block entry for the SSA certificate.
    For example, an operand read before any assignment is live at its block's entry.
    Builds on: Ssa.Lang, Program variable and point presentations, and graph measures. *)

From Stdlib Require Import List PArith NArith.
From Argent Require Import Time Std BigO.
From Galois.Base Require Import KeySig Key Trie.
From Galois.Graph Require Import DigraphSig.
From Galois.Program Require Import CfgSig VarsSig SsaSig.
From Galois.Ssa Require Import Lang.
Import List.ListNotations.

Definition function_vars {K G} (p : func positive K G) : list positive :=
  inputs _ _ _ p ++ flat_map (fun item =>
    params _ _ _ (snd item) ++ flat_map (fun '(x, _, ys) => x :: ys)
      (code _ _ _ (snd item)) ++ exit_uses (term _ _ _ (snd item))) (blocks _ _ _ p).
TimeFun function_vars.

Definition exit_targets {X G} (e : exit X G) : list positive :=
  match e with
  | Jump b _ => [b]
  | Branch _ _ b _ c _ => [b; c]
  | Return _ => []
  end.
TimeFun exit_targets.

(** Every exit target of a listed block is the identifier of a listed block. *)
Definition targets_listed {K G} (p : func positive K G) : Prop :=
  forall b body t, In (b, body) (blocks _ _ _ p) -> In t (exit_targets (term _ _ _ body)) ->
    In t (map fst (blocks _ _ _ p)).

Definition function_ids {K G} (p : func positive K G) : list positive :=
  entry _ _ _ p :: function_vars p ++ flat_map (fun item =>
    fst item :: exit_targets (term _ _ _ (snd item))) (blocks _ _ _ p).
TimeFun function_ids.

Definition function_size {K G} (p : func positive K G) : nat :=
  length (function_vars p) + length (blocks _ _ _ p) +
    fold_right (fun item n => length (code _ _ _ (snd item)) + n) 0 (blocks _ _ _ p).
TimeFun function_size.

Definition function_width {K G} (p : func positive K G) : nat :=
  graph_max (vertex_width (function_ids p))
    (Pos.size_nat (Pos.of_succ_nat (function_size p))).
TimeFun function_width.

(** Liveness follows listed outgoing edges to a use without an intervening definition. *)
Inductive point_live {N E V} (nodes : list N) (out : N -> list E) (dst : E -> N)
    (uses defs : E -> list V) (exits : N -> list V) (x : V) : N -> Prop :=
  | Point_live_exit : forall n, In x (exits n) ->
      point_live nodes out dst uses defs exits x n
  | Point_live_use : forall n e, In e (out n) -> In x (uses e) ->
      point_live nodes out dst uses defs exits x n
  | Point_live_next : forall n e, In e (out n) -> ~ In x (defs e) -> In (dst e) nodes ->
      point_live nodes out dst uses defs exits x (dst e) ->
      point_live nodes out dst uses defs exits x n.

Definition index_row {A} (m : ptrie (list A)) (x : positive) : list A :=
  match trie_get x m with
  | Some row => row
  | None => []
  end.
TimeFun index_row.

(** The first block of each identifier, in block order, as `find_block` selects it. *)
Definition first_blocks {K G} (bs : list (positive * block positive K G))
    : list (positive * block positive K G) :=
  rev_append (snd (fold_left (fun acc item =>
    match trie_get (fst item) (fst acc) with
    | Some _ => acc
    | None => (PTrieCode.set (fst item) tt (fst acc), item :: snd acc)
    end) bs (Empty, []))) [].
TimeFun first_blocks.

Module Type LANG_PREPARE_OPS (O : OPS) (Q : TYPE).
  Parameter prepare : func positive O.K O.G -> Q.t.
End LANG_PREPARE_OPS.

Module Type LANG_PREPARE_TIME (O : OPS) (Q : TYPE) (Import R : LANG_PREPARE_OPS O Q).
  Parameter T_prepare : func positive O.K O.G -> N.
  Parameter c_prepare : N.
  (** Preparation reads each syntax item once at the syntax width. *)
  Parameter T_prepare_le : forall p,
    (T_prepare p <= c_prepare * N.of_nat (function_size p + 1) *
      N.of_nat (function_width p + 1))%N.
  (** Preparation has the published linear bit-cost bound. *)
  Parameter prepare_bigO : bigO (fun _ : func positive O.K O.G => True)
    (fun p => N.of_nat ((function_size p + 1) * (function_width p + 1))) T_prepare.
End LANG_PREPARE_TIME.

Module Type LANG_PREPARE_T (O : OPS) (Q : TYPE) :=
  LANG_PREPARE_OPS O Q <+ LANG_PREPARE_TIME O Q.

Module Type LANG_PRESENT_BUDGET (O : OPS) (Q : TYPE) (R : LANG_PREPARE_OPS O Q)
    (BE E N : KEY_T)
    (BC : CFG_T Q PosKeyT BE) (C : CFG_T Q N E) (U : VARS_T Q N E C PosKeyT)
    (SP : SSA_POINTS_T Q PosKeyT BE BC N E C PosKeyT U).
  Parameter c_present : N.
  (** Both prepared graphs are well formed for every raw function. *)
  Parameter prepared_wf : forall p, BC.wf (R.prepare p) /\ C.wf (R.prepare p).
  (** The point laws hold on the prepared form of an SSA function. *)
  Parameter points_wf : forall p, ssa_wf p -> SP.wf (R.prepare p).
  (** The block presentation lists each block identifier at most once per listed block. *)
  Parameter block_nodes_le : forall p,
    length (BC.nodes (R.prepare p)) <= length (blocks _ _ _ p).
  (** Each listed block contributes at most its two exit edges. *)
  Parameter block_edges_le : forall p,
    length (BC.edges (R.prepare p)) <= 2 * length (BC.nodes (R.prepare p)).
  (** Presented block identifiers are identifiers of the syntax. *)
  Parameter block_bits_le : forall p b,
    (In b (BC.nodes (R.prepare p)) \/ exists e, In e (BC.edges (R.prepare p)) /\
      (BC.src (R.prepare p) e = b \/ BC.dst (R.prepare p) e = b)) ->
    PosKeyT.bits b <= function_width p.
  (** Parameter rows of listed blocks and argument rows of listed edges are syntax. *)
  Parameter block_rows_le : forall p,
    fold_right (fun b n => length (SP.block_params (R.prepare p) b) + n) 0
      (BC.nodes (R.prepare p)) +
    fold_right (fun be n => length (SP.block_edge_args (R.prepare p) be) + n) 0
      (BC.edges (R.prepare p)) <= function_size p.
  (** Points, point edges and variable occurrences are linear in the syntax. *)
  Parameter points_le : forall p,
    (N.of_nat (length (C.nodes (R.prepare p)) + length (C.edges (R.prepare p)) +
      length (U.occurrences (R.prepare p))) <=
      c_present * N.of_nat (function_size p + 1))%N.
  (** Occurring variables are identifiers of the syntax. *)
  Parameter occurrence_width_le : forall p,
    U.occurrence_width (R.prepare p) <= function_width p.
  (** Listed point keys are within a constant factor of the syntax width. *)
  Parameter point_bits_le : forall p n, In n (C.nodes (R.prepare p)) ->
    (N.of_nat (N.bits n) <= c_present * N.of_nat (function_width p + 1))%N.
  (** Listed edge keys are within a constant factor of the syntax width. *)
  Parameter edge_bits_le : forall p e, In e (C.edges (R.prepare p)) ->
    (N.of_nat (E.bits e) <= c_present * N.of_nat (function_width p + 1))%N.
  (** Listed block-edge keys are within a constant factor of the syntax width. *)
  Parameter block_edge_bits_le : forall p e, In e (BC.edges (R.prepare p)) ->
    (N.of_nat (BE.bits e) <= c_present * N.of_nat (function_width p + 1))%N.
End LANG_PRESENT_BUDGET.

Module Type LIVE_OPS (O : OPS)
    (P : TYPE with Definition t := func positive O.K O.G)
    (Q : TYPE) (R : LANG_PREPARE_OPS O Q)
    (BE E : TYPE) (N : KEY_OPS)
    (BC : CFG_INDEXED_OPS Q PosKeyCode BE) (C : CFG_INDEXED_OPS Q N E)
    (U : VARS_OPS Q N E C PosKeyCode)
    (SP : SSA_POINTS_OPS Q PosKeyCode BE BC N E C PosKeyCode U).
  Parameter live_in : P.t -> list (positive * list positive).
End LIVE_OPS.

Module Type LIVE (O : OPS)
    (P : TYPE with Definition t := func positive O.K O.G)
    (Q : TYPE) (R : LANG_PREPARE_OPS O Q)
    (BE E : TYPE) (N : KEY)
    (BC : CFG Q PosKey BE) (C : CFG Q N E) (U : VARS Q N E C PosKey)
    (SP : SSA_POINTS Q PosKey BE BC N E C PosKey U) :=
  LIVE_OPS O P Q R BE E N BC C U SP.

Module Type LIVE_TIME (O : OPS)
    (P : TYPE with Definition t := func positive O.K O.G)
    (Q : TYPE) (R : LANG_PREPARE_T O Q)
    (BE E N : KEY_T)
    (BC : CFG_T Q PosKeyT BE) (C : CFG_T Q N E) (U : VARS_T Q N E C PosKeyT)
    (SP : SSA_POINTS_T Q PosKeyT BE BC N E C PosKeyT U)
    (PB : LANG_PRESENT_BUDGET O Q R BE E N BC C U SP)
    (Import L : LIVE O P Q R BE E N BC C U SP).
  (* spec: live_region *)
  Parameter live_region : P.t -> list (N.t * positive).
  (** The cost region enumerates each live point/value pair exactly once. *)
  Parameter live_region_spec : forall p,
    NoDup (live_region p) /\ forall n x,
      (In (n, x) (live_region p) <-> In n (C.nodes (R.prepare p)) /\
        In x (U.universe (R.prepare p)) /\
        point_live (C.nodes (R.prepare p)) (C.out (R.prepare p)) (C.dst (R.prepare p))
          (U.uses (R.prepare p)) (U.defs (R.prepare p)) (U.exits (R.prepare p)) x n).
  Definition live_size p := fold_right (fun pair n =>
    1 + length (C.inc (R.prepare p) (fst pair)) + n) 0 (live_region p).
  Definition rows_size (rows : list (positive * list positive)) :=
    fold_right (fun row n => 1 + length (snd row) + n) 0 rows.
  (** The producer emits at most one row entry per charged block and live pair. *)
  Parameter live_in_size : forall p,
    rows_size (live_in p) <= length (blocks _ _ _ p) + live_size p.
  (** Emitted rows name listed blocks and variables of the universe. *)
  Parameter live_in_ids : forall p row, In row (live_in p) ->
    In (fst row) (BC.nodes (R.prepare p)) /\ incl (snd row) (U.universe (R.prepare p)).
  Parameter T_live_in : P.t -> N.
  Parameter c_live : N.
  (** Path exploration pays for syntax and live predecessor incidences. *)
  Parameter T_live_in_le : forall p,
    (T_live_in p <= c_live * N.of_nat (function_size p + live_size p + 1) *
      N.of_nat (function_width p + 1))%N.
  (** The producer has the published output-sensitive bit-cost bound. *)
  Parameter live_in_bigO : bigO (fun _ : P.t => True)
    (fun p => N.of_nat ((function_size p + live_size p + 1) * (function_width p + 1)))
    T_live_in.
End LIVE_TIME.

Module Type LIVE_T (O : OPS)
    (P : TYPE with Definition t := func positive O.K O.G)
    (Q : TYPE) (R : LANG_PREPARE_T O Q)
    (BE E N : KEY_T)
    (BC : CFG_T Q PosKeyT BE) (C : CFG_T Q N E) (U : VARS_T Q N E C PosKeyT)
    (SP : SSA_POINTS_T Q PosKeyT BE BC N E C PosKeyT U)
    (PB : LANG_PRESENT_BUDGET O Q R BE E N BC C U SP) :=
  LIVE O P Q R BE E N BC C U SP <+ LIVE_TIME O P Q R BE E N BC C U SP PB.

Module Type LIVE_PLAN (O : OPS)
    (P : TYPE with Definition t := func positive O.K O.G)
    (Q : TYPE) (R : LANG_PREPARE_T O Q)
    (BE E N : KEY_T)
    (BC : CFG_T Q PosKeyT BE) (C : CFG_T Q N E) (U : VARS_T Q N E C PosKeyT)
    (SP : SSA_POINTS_T Q PosKeyT BE BC N E C PosKeyT U)
    (PB : LANG_PRESENT_BUDGET O Q R BE E N BC C U SP)
    (Import L : LIVE_T O P Q R BE E N BC C U SP PB).
  Parameter use_index : Q.t -> ptrie (list N.t).
  Parameter kill_index : Q.t -> ptrie (ptrie unit).
  Parameter T_use_index T_kill_index : Q.t -> N.
  Parameter explore : Q.t -> ptrie (list N.t) -> ptrie (ptrie unit) -> positive -> list N.t.
  Parameter T_explore : Q.t -> ptrie (list N.t) -> ptrie (ptrie unit) -> positive -> N.
  Parameter k_index : N.
  Parameter k_explore k_rows : N.
  Definition visits p x := filter (fun pair => Pos.eqb (snd pair) x) (live_region p).
  Definition variable_work p x := fold_right (fun pair n =>
    1 + length (C.inc (R.prepare p) (fst pair)) + n) 0 (visits p x).
  Definition searched p x :=
    explore (R.prepare p) (use_index (R.prepare p)) (kill_index (R.prepare p)) x.
  (** Indexed use points of a variable are distinct charged live pairs. *)
  Parameter F0_use_index : forall p x,
    NoDup (index_row (use_index (R.prepare p)) x) /\
    forall n, In n (index_row (use_index (R.prepare p)) x) -> In (n, x) (live_region p).
  (** The kill index answers, for a variable and a listed edge, whether the edge defines it. *)
  Parameter F0b_kill_index : forall p x e, In e (C.edges (R.prepare p)) ->
    ((exists m, trie_get x (kill_index (R.prepare p)) = Some m /\
      trie_get (E.encode e) m = Some tt) <-> In x (U.defs (R.prepare p) e)).
  (** Each per-variable search visits a point at most once. *)
  Parameter F1_explore_nodup : forall p x, NoDup (searched p x).
  (** Every visited search point belongs to its charged semantic region. *)
  Parameter F2_explore_region : forall p x n,
    In n (searched p x) -> In (n, x) (live_region p).
  (** Deduplicated variables partition the total live-incidence budget. *)
  Parameter F3_partition : forall p,
    fold_right (fun x n => variable_work p x + n) 0 (U.universe (R.prepare p)) =
      live_size p.
  (** Indexing reads each variable occurrence once at the syntax width. *)
  Parameter T0_use_index : forall p,
    (T_use_index (R.prepare p) <= k_index * N.of_nat (function_size p + 1) *
      N.of_nat (function_width p + 1))%N.
  (** The kill index reads each definition occurrence once at the syntax width. *)
  Parameter T0_kill_index : forall p,
    (T_kill_index (R.prepare p) <= k_index * N.of_nat (function_size p + 1) *
      N.of_nat (function_width p + 1))%N.
  (** A search for a variable of the universe charges each visited point and incoming
      occurrence. *)
  Parameter T1_explore : forall p x, In x (U.universe (R.prepare p)) ->
    (T_explore (R.prepare p) (use_index (R.prepare p)) (kill_index (R.prepare p)) x <=
      k_explore * N.of_nat (variable_work p x + 1) * N.of_nat (function_width p + 1))%N.
  (** The driver prepares once, builds both indexes, searches each variable and groups
      rows. *)
  Parameter T2_rows : forall p,
    (T_live_in p <= R.T_prepare p +
      k_rows * N.of_nat (function_size p + live_size p + 1) *
        N.of_nat (function_width p + 1) + T_use_index (R.prepare p) +
      T_kill_index (R.prepare p) +
      fold_right N.add 0%N
        (map (T_explore (R.prepare p) (use_index (R.prepare p)) (kill_index (R.prepare p)))
          (U.universe (R.prepare p))))%N.
End LIVE_PLAN.

Module Type LIVE_ALL (O : OPS)
    (P : TYPE with Definition t := func positive O.K O.G)
    (Q : TYPE) (R : LANG_PREPARE_T O Q)
    (BE E N : KEY_T)
    (BC : CFG_T Q PosKeyT BE) (C : CFG_T Q N E) (U : VARS_T Q N E C PosKeyT)
    (SP : SSA_POINTS_T Q PosKeyT BE BC N E C PosKeyT U)
    (PB : LANG_PRESENT_BUDGET O Q R BE E N BC C U SP) :=
  LIVE_T O P Q R BE E N BC C U SP PB <+ LIVE_PLAN O P Q R BE E N BC C U SP PB.
