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

Module Ssa (P : TYPE) (N : KEY) (E : KEY)
    (C : CFG P N E) (V : KEY) (K G : TYPE) (D : SSA_DATA P N V K G)
    <: SSA P N E C V K G.
  Include SsaCode P N E C V K G D.
  Include SSA_SPEC P N E C V K G.

  Definition wf p :=
    C.wf p /\ NoDup (values p) /\
    (forall x, In x (values p) -> In (home p x) (C.nodes p)) /\
    (forall x b i, def p x = Param b i <-> nth_error (params p b) i = Some x) /\
    (forall b x, In x (params p b) -> home p x = b) /\
    (forall b x, In b (C.nodes p) -> In x (params p b) -> In x (values p)) /\
    (forall e, In e (C.edges p) -> map fst (args p e) = params p (C.dst p e)) /\
    (forall e x y, In e (C.edges p) -> In (x, y) (args p e) ->
      In y (values p) /\ forall entry route, In entry (C.entries p) ->
        presentation_path (C.edges p) (C.src p) (C.dst p) entry route (C.src p e) ->
        In (home p y) route) /\
    (forall e g xs x, In e (C.edges p) -> In (g, xs) (guards p e) -> In x xs ->
      In x (values p) /\ forall entry route, In entry (C.entries p) ->
        presentation_path (C.edges p) (C.src p) (C.dst p) entry route (C.src p e) ->
        In (home p x) route) /\
    (forall x op xs y, In x (values p) -> def p x = Op op xs -> In y xs ->
      In y (values p) /\ forall entry route, In entry (C.entries p) ->
        presentation_path (C.edges p) (C.src p) (C.dst p) entry route (home p x) ->
        In (home p y) route).

  Lemma cfg_wf : forall p, wf p -> C.wf p.
  Proof. Admitted.
  Lemma values_nodup : forall p, wf p -> NoDup (values p).
  Proof. Admitted.
  Lemma homes_listed : forall p x, wf p -> In x (values p) -> In (home p x) (C.nodes p).
  Proof. Admitted.
  Lemma param_defs : forall p x b i, wf p ->
    (def p x = Param b i <-> nth_error (params p b) i = Some x).
  Proof. Admitted.
  Lemma param_home : forall p b x, wf p -> In x (params p b) -> home p x = b.
  Proof. Admitted.
  Lemma params_listed : forall p b x, wf p -> In b (C.nodes p) ->
    In x (params p b) -> In x (values p).
  Proof. Admitted.
  Lemma args_params : forall p e, wf p -> In e (C.edges p) ->
    map fst (args p e) = params p (C.dst p e).
  Proof. Admitted.
  Lemma args_dominate : forall p e x y, wf p -> In e (C.edges p) ->
    In (x, y) (args p e) -> In y (values p) /\ forall entry route,
      In entry (C.entries p) ->
      presentation_path (C.edges p) (C.src p) (C.dst p) entry route (C.src p e) ->
      In (home p y) route.
  Proof. Admitted.
  Lemma guards_dominate : forall p e g xs x, wf p -> In e (C.edges p) ->
    In (g, xs) (guards p e) -> In x xs -> In x (values p) /\ forall entry route,
      In entry (C.entries p) ->
      presentation_path (C.edges p) (C.src p) (C.dst p) entry route (C.src p e) ->
      In (home p x) route.
  Proof. Admitted.
  Lemma op_args_dominate : forall p x op xs y, wf p -> In x (values p) ->
    def p x = Op op xs -> In y xs -> In y (values p) /\ forall entry route,
      In entry (C.entries p) ->
      presentation_path (C.edges p) (C.src p) (C.dst p) entry route (home p x) ->
      In (home p y) route.
  Proof. Admitted.
End Ssa.

Module SsaPoints (P : TYPE) (B : KEY) (BE : KEY)
    (BC : CFG P B BE) (N : KEY) (E : KEY) (C : CFG P N E)
    (V : KEY) (U : VARS P N E C V) (D : SSA_POINTS_DATA P B BE N E V)
    <: SSA_POINTS P B BE BC N E C V U.
  Include SsaPointsCode P B BE BC N E C V U D.
  Definition wf p :=
    (C.wf p /\ BC.wf p) /\
    (forall n, NoDup (C.out p n)) /\
    (forall b, NoDup (BC.out p b)) /\
    (forall n, (In n (C.nodes p) <-> exists b, In b (BC.nodes p) /\ In n (points_in_block p b))) /\
    (forall b, NoDup (points_in_block p b)) /\
    (forall b n, In b (BC.nodes p) ->
    In n (points_in_block p b) -> block_of_point p n = b) /\
    (forall b, In b (BC.nodes p) ->
    points_in_block p b <> nil) /\
    (forall b, In b (BC.nodes p) ->
    presentation_chain (C.edges p) (C.src p) (C.dst p)
      (points_in_block p b) (instruction_edges p b)) /\
    (forall b e, In b (BC.nodes p) ->
    In e (instruction_edges p b) -> block_edge_of p e = None) /\
    (forall e, In e (C.edges p) ->
    block_edge_of p e = None -> In e (instruction_edges p (block_of_point p (C.src p e)))) /\
    (forall b, In b (BC.nodes p) ->
    nth_error (instruction_edges p b) 0 = Some (parameter_edge p b)) /\
    (forall b x, In b (BC.nodes p) ->
    (In x (U.defs p (parameter_edge p b)) <-> In x (block_params p b))) /\
    (forall e, In e (C.edges p) ->
    match block_edge_of p e with
    | None => block_of_point p (C.src p e) = block_of_point p (C.dst p e)
    | Some be => In be (BC.edges p) /\ BC.src p be = block_of_point p (C.src p e) /\
        BC.dst p be = block_of_point p (C.dst p e) /\
        last (points_in_block p (block_of_point p (C.src p e))) (C.src p e) = C.src p e /\
        nth_error (points_in_block p (BC.dst p be)) 0 = Some (C.dst p e)
    end) /\
    (forall be, In be (BC.edges p) ->
    length (block_edge_args p be) = length (block_params p (BC.dst p be))) /\
    (forall e be x, In e (C.edges p) ->
    block_edge_of p e = Some be -> In x (block_edge_args p be) -> In x (U.uses p e)) /\
    (forall be, In be (BC.edges p) ->
    exists e, In e (C.edges p) /\ block_edge_of p e = Some be) /\
    (forall e1 e2 be, In e1 (C.edges p) -> In e2 (C.edges p) ->
    block_edge_of p e1 = Some be -> block_edge_of p e2 = Some be -> e1 = e2).

  Lemma graphs_wf : forall p, wf p -> C.wf p /\ BC.wf p.
  Proof. Admitted.
  Lemma points_out_nodup : forall p n, wf p -> NoDup (C.out p n).
  Proof. Admitted.
  Lemma blocks_out_nodup : forall p b, wf p -> NoDup (BC.out p b).
  Proof. Admitted.
  Lemma points_covered : forall p n, wf p ->
    (In n (C.nodes p) <-> exists b, In b (BC.nodes p) /\ In n (points_in_block p b)).
  Proof. Admitted.
  Lemma points_unique : forall p b, wf p -> NoDup (points_in_block p b).
  Proof. Admitted.
  Lemma points_owner : forall p b n, wf p -> In b (BC.nodes p) ->
    In n (points_in_block p b) -> block_of_point p n = b.
  Proof. Admitted.
  Lemma blocks_nonempty : forall p b, wf p -> In b (BC.nodes p) ->
    points_in_block p b <> nil.
  Proof. Admitted.
  Lemma points_ordered : forall p b, wf p -> In b (BC.nodes p) ->
    presentation_chain (C.edges p) (C.src p) (C.dst p)
      (points_in_block p b) (instruction_edges p b).
  Proof. Admitted.
  Lemma instruction_edges_internal : forall p b e, wf p -> In b (BC.nodes p) ->
    In e (instruction_edges p b) -> block_edge_of p e = None.
  Proof. Admitted.
  Lemma instruction_edges_complete : forall p e, wf p -> In e (C.edges p) ->
    block_edge_of p e = None -> In e (instruction_edges p (block_of_point p (C.src p e))).
  Proof. Admitted.
  Lemma parameter_edge_first : forall p b, wf p -> In b (BC.nodes p) ->
    nth_error (instruction_edges p b) 0 = Some (parameter_edge p b).
  Proof. Admitted.
  Lemma parameter_edge_defs : forall p b x, wf p -> In b (BC.nodes p) ->
    (In x (U.defs p (parameter_edge p b)) <-> In x (block_params p b)).
  Proof. Admitted.
  Lemma point_edge_projection : forall p e, wf p -> In e (C.edges p) ->
    match block_edge_of p e with
    | None => block_of_point p (C.src p e) = block_of_point p (C.dst p e)
    | Some be => In be (BC.edges p) /\ BC.src p be = block_of_point p (C.src p e) /\
        BC.dst p be = block_of_point p (C.dst p e) /\
        last (points_in_block p (block_of_point p (C.src p e))) (C.src p e) = C.src p e /\
        nth_error (points_in_block p (BC.dst p be)) 0 = Some (C.dst p e)
    end.
  Proof. Admitted.
  Lemma phi_args_length : forall p be, wf p -> In be (BC.edges p) ->
    length (block_edge_args p be) = length (block_params p (BC.dst p be)).
  Proof. Admitted.
  Lemma phi_edge_use : forall p e be x, wf p -> In e (C.edges p) ->
    block_edge_of p e = Some be -> In x (block_edge_args p be) -> In x (U.uses p e).
  Proof. Admitted.
  Lemma block_edge_covered : forall p be, wf p -> In be (BC.edges p) ->
    exists e, In e (C.edges p) /\ block_edge_of p e = Some be.
  Proof. Admitted.
  Lemma block_edge_unique : forall p e1 e2 be, wf p ->
    In e1 (C.edges p) -> In e2 (C.edges p) ->
    block_edge_of p e1 = Some be -> block_edge_of p e2 = Some be -> e1 = e2.
  Proof. Admitted.
End SsaPoints.

Module Type SSA_POINTS_STRICT_WITNESS (P : TYPE) (B : KEY) (BE : TYPE)
    (BC : CFG P B BE) (N : KEY) (E : TYPE) (C : CFG P N E)
    (V : KEY) (U : VARS P N E C V) (S : SSA_POINTS P B BE BC N E C V U).
  Definition point_reachable p n := exists entry route, In entry (C.entries p) /\
    presentation_path (C.edges p) (C.src p) (C.dst p) entry route n.
  Definition point_dominates p d n := forall entry route, In entry (C.entries p) ->
    presentation_path (C.edges p) (C.src p) (C.dst p) entry route n -> In d route.
  Definition point_use_at p n x := In x (U.exits p n) \/
    exists e, In e (C.out p n) /\ In x (U.uses p e).
  Parameter single_entry : forall p, S.wf p -> exists entry, C.entries p = entry :: nil.
  Parameter uses_defined : forall p n x, S.wf p -> point_reachable p n ->
    point_use_at p n x -> exists d, S.point_definition p x = Some d /\
      point_reachable p d /\ point_dominates p d n /\ d <> n.
  Parameter defs_at_home : forall p n e x, S.wf p -> point_reachable p n ->
    In e (C.out p n) -> In x (U.defs p e) -> S.point_definition p x = Some n.
  Parameter home_kills : forall p x d e, S.wf p -> S.point_definition p x = Some d ->
    point_reachable p d -> In e (C.out p d) -> In x (U.defs p e).
End SSA_POINTS_STRICT_WITNESS.

Module SsaPointsStrict (P : TYPE) (B : KEY) (BE : TYPE)
    (BC : CFG P B BE) (N : KEY) (E : TYPE) (C : CFG P N E)
    (V : KEY) (U : VARS P N E C V) (S : SSA_POINTS P B BE BC N E C V U)
    (W : SSA_POINTS_STRICT_WITNESS P B BE BC N E C V U S)
    <: SSA_POINTS_STRICT_LAWS P B BE BC N E C V U S.
  Definition point_reachable := W.point_reachable.
  Definition point_dominates := W.point_dominates.
  Definition point_use_at := W.point_use_at.
  Definition single_entry := W.single_entry.
  Definition uses_defined := W.uses_defined.
  Definition defs_at_home := W.defs_at_home.
  Definition home_kills := W.home_kills.

  Lemma definitions_unique : forall p n1 n2 e1 e2 x, S.wf p ->
    point_reachable p n1 -> point_reachable p n2 ->
    In e1 (C.out p n1) -> In e2 (C.out p n2) ->
    In x (U.defs p e1) -> In x (U.defs p e2) -> n1 = n2.
  Proof.
    intros p n1 n2 e1 e2 x Hwf Hn1 Hn2 He1 He2 Hdef1 Hdef2.
    pose proof (defs_at_home p n1 e1 x Hwf Hn1 He1 Hdef1) as Hhome1.
    pose proof (defs_at_home p n2 e2 x Hwf Hn2 He2 Hdef2) as Hhome2.
    rewrite Hhome1 in Hhome2; inversion Hhome2; reflexivity.
  Qed.
End SsaPointsStrict.

(** Projecting occurrence identifiers retains the selected edge order. *)
Theorem dominating_edges_projected_equation : forall E (ctx : strict_context (E * nat)) n,
  dominating_edges_projected ctx n = map fst (dominating_edges_in ctx n).
Proof.
  reflexivity.
Qed.
