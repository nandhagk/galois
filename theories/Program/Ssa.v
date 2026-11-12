(** * Static single-assignment presentations

    Tables hold definitions, homes, parameters, arguments and guards by encoded identity.
    For example, an absent definition is arbitrary.
    Builds on: Program.SsaSig and Base.Trie. *)

From Stdlib Require Import List Bool NArith PArith.
From Galois.Base Require Import KeySig Trie Loop.
From Galois.Graph Require Import Data SearchSig Search Dom.
From Galois.Program Require Import CfgSig VarsSig SsaSig.

Record ssa_tables (N V K G : Type) := SsaTables {
  ssa_values : list V;
  ssa_defs : ptrie (definition N V K);
  ssa_homes : ptrie N;
  ssa_default_home : N;
  ssa_params : ptrie (list V);
  ssa_args : ptrie (list (V * V));
  ssa_guards : ptrie (list (G * list V))
}.

Arguments SsaTables {N V K G}.
Arguments ssa_values {N V K G}.
Arguments ssa_defs {N V K G}.
Arguments ssa_homes {N V K G}.
Arguments ssa_default_home {N V K G}.
Arguments ssa_params {N V K G}.
Arguments ssa_args {N V K G}.
Arguments ssa_guards {N V K G}.

Module Type SSA_DATA (P : TYPE) (N V : KEY_OPS) (K G : TYPE).
  Parameter tables : P.t -> ssa_tables N.t V.t K.t G.t.
End SSA_DATA.

Module SsaCode (P : TYPE) (N : KEY_OPS) (E : KEY_OPS)
    (C : CFG_INDEXED_OPS P N E) (V : KEY_OPS) (K G : TYPE)
    (D : SSA_DATA P N V K G) <: SSA_OPS P N E C V K G.
  Definition values p := ssa_values (D.tables p).
  Definition def p x :=
    match trie_get (V.encode x) (ssa_defs (D.tables p)) with
    | Some d => d
    | None => Arbitrary
    end.
  Definition home p x :=
    match trie_get (V.encode x) (ssa_homes (D.tables p)) with
    | Some n => n
    | None => ssa_default_home (D.tables p)
    end.
  Definition params p n :=
    match trie_get (N.encode n) (ssa_params (D.tables p)) with
    | Some xs => xs
    | None => nil
    end.
  Definition args p e :=
    match trie_get (E.encode e) (ssa_args (D.tables p)) with
    | Some xs => xs
    | None => nil
    end.
  Definition guards p e :=
    match trie_get (E.encode e) (ssa_guards (D.tables p)) with
    | Some gs => gs
    | None => nil
    end.
End SsaCode.

Record ssa_point_tables (B BE N E V : Type) := SsaPointTables {
  point_lists : ptrie (list N);
  instruction_lists : ptrie (list E);
  parameter_edges : ptrie E;
  default_parameter_edge : E;
  point_blocks : ptrie B;
  default_block : B;
  edge_blocks : ptrie BE;
  point_params : ptrie (list V);
  point_args : ptrie (list V);
  definitions : ptrie N
}.

Arguments SsaPointTables {B BE N E V}.
Arguments point_lists {B BE N E V}.
Arguments instruction_lists {B BE N E V}.
Arguments parameter_edges {B BE N E V}.
Arguments default_parameter_edge {B BE N E V}.
Arguments point_blocks {B BE N E V}.
Arguments default_block {B BE N E V}.
Arguments edge_blocks {B BE N E V}.
Arguments point_params {B BE N E V}.
Arguments point_args {B BE N E V}.
Arguments definitions {B BE N E V}.

Module Type SSA_POINTS_DATA (P : TYPE) (B BE N E V : KEY_OPS).
  Parameter tables : P.t -> ssa_point_tables B.t BE.t N.t E.t V.t.
End SSA_POINTS_DATA.

Module SsaPointsCode (P : TYPE) (B : KEY_OPS) (BE : KEY_OPS)
    (BC : CFG_INDEXED_OPS P B BE) (N : KEY_OPS) (E : KEY_OPS)
    (C : CFG_INDEXED_OPS P N E) (V : KEY_OPS) (U : VARS_OPS P N E C V)
    (D : SSA_POINTS_DATA P B BE N E V) <: SSA_POINTS_OPS P B BE BC N E C V U.
  Definition points_in_block p b :=
    match trie_get (B.encode b) (point_lists (D.tables p)) with
    | Some xs => xs | None => nil end.
  Definition instruction_edges p b :=
    match trie_get (B.encode b) (instruction_lists (D.tables p)) with
    | Some xs => xs | None => nil end.
  Definition parameter_edge p b :=
    match trie_get (B.encode b) (parameter_edges (D.tables p)) with
    | Some e => e | None => default_parameter_edge (D.tables p) end.
  Definition block_of_point p n :=
    match trie_get (N.encode n) (point_blocks (D.tables p)) with
    | Some b => b | None => default_block (D.tables p) end.
  Definition block_edge_of p e := trie_get (E.encode e) (edge_blocks (D.tables p)).
  Definition block_params p b :=
    match trie_get (B.encode b) (point_params (D.tables p)) with
    | Some xs => xs | None => nil end.
  Definition block_edge_args p e :=
    match trie_get (BE.encode e) (point_args (D.tables p)) with
    | Some xs => xs | None => nil end.
  Definition point_definition p v := trie_get (V.encode v) (definitions (D.tables p)).
End SsaPointsCode.

(** An edge-dominance context retains the supplied tree and prepared edge choices. *)
Record strict_context (E : Type) := StrictContext {
  strict_tree : domtree;
  strict_index : ptrie (option E);
  strict_fuel : N
}.

Arguments StrictContext {E}.
Arguments strict_tree {E}.
Arguments strict_index {E}.
Arguments strict_fuel {E}.

(** Predecessor rows retain edge occurrences and their encoded sources in input order. *)
Definition strict_predecessors {E} (src dst : E -> positive) (edges : list E) :=
  fold_right (fun e rows =>
    let d := dst e in
    let row := match trie_get d rows with Some es => es | None => nil end in
    PTrieCode.set d ((e, src e) :: row) rows) Empty edges.

Definition strict_candidates {E} (tree : domtree) (live : ptrie bool)
    (rows : ptrie (list (E * positive))) (v : positive) :=
  filter (fun es =>
    match trie_get (snd es) live with
    | Some _ => negb (DomCode.dominates_b tree v (snd es))
    | None => false
    end)
    (match trie_get v rows with Some es => es | None => nil end).

Definition strict_choice {E} (tree : domtree) (live : ptrie bool)
    (roots : list positive) (rows : ptrie (list (E * positive))) (v : positive) :=
  if existsb (Pos.eqb v) roots then None else
    match strict_candidates tree live rows v with
    | (e, _) :: nil => Some e
    | _ => None
    end.

(** Preparation records reachable sources and one eligible incoming edge per vertex. *)
Definition make_strict_context {E} (src dst : E -> positive) (edges : list E)
    (g : prepared) (roots : list positive) (tree : domtree) : strict_context E :=
  let reached := entered (prepared_search_trace g roots) in
  let live := fold_left (fun set v => PTrieCode.set v true set) reached Empty in
  let rows := strict_predecessors src dst edges in
  let choices := fold_left (fun m v => PTrieCode.set v (strict_choice tree live roots rows v) m)
    (nodes g) Empty in
  StrictContext tree choices (N.of_nat (Datatypes.S (length (PTrieCode.elements (idom tree))))).

Definition strict_walk_step {E} (ctx : strict_context E) (state : option positive * list E)
    : (option positive * list E) + list E :=
  match state with
  | (None, es) => inr es
  | (Some v, es) =>
    let parent := trie_get v (idom (strict_tree ctx)) in
    let selected := trie_get v (strict_index ctx) in
    inl (parent, match selected with Some (Some e) => e :: es | _ => es end)
  end.

(** The parent walk reports selected edges from the outermost ancestor to the target. *)
Definition dominating_edges_in {E} (ctx : strict_context E) (vertex : positive) : list E :=
  match trie_get vertex (strict_index ctx) with
  | None => nil
  | Some _ =>
    match loopN (strict_walk_step ctx) (strict_fuel ctx) (Some vertex, nil) with
    | inl (_, es) => es
    | inr es => es
    end
  end.

Definition dominating_edges_projected {E} (ctx : strict_context (E * nat))
    (vertex : positive) : list E :=
  map fst (dominating_edges_in ctx vertex).
