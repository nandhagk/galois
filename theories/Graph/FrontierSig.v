(** * Dominance frontier signatures

    Frontiers identify dominated predecessors across a strict-dominance boundary.
    For example, either arm of a diamond has the join in its frontier.
    Builds on: graph semantics, dominator predicates and preparation measures. *)

From Stdlib Require Import PArith NArith List.
From Argent Require Import Time Std BigO Loop.
From Galois.Base Require Import Trie Loop.
From Galois.Graph Require Import Data Spec DigraphSig DomSig.
Import List.ListNotations.

Definition frontier_row (rows : ptrie (list positive)) (u : positive) : list positive :=
  match trie_get u rows with
  | Some vs => vs
  | None => []
  end.
TimeFun frontier_row.

(** Frontier membership is the requested dominated-predecessor boundary. *)
Definition in_frontier (g : digraph) (r x y : positive) : Prop :=
  (exists p, reach g [r] p /\ edge g p y /\ dominates g r x p) /\
  ~ strictly_dominates g r x y.

(** Iteration work counts the entries in rows visited from seeds and discovered targets. *)
Definition idf_work
    (idf : ptrie (list positive) -> list positive -> list positive)
    (rows : ptrie (list positive)) (seeds : list positive) : nat :=
  fold_right (fun x n => length (frontier_row rows x) + n) 0 (seeds ++ idf rows seeds).
TimeFun idf_work.

(** Iterated frontiers form the least nonreflexive closure reached from the seeds. *)
Inductive in_iterated_frontier (g : digraph) (r : positive) (seeds : list positive) :
    positive -> Prop :=
  | frontier_seed : forall x y,
      In x seeds -> in_frontier g r x y -> in_iterated_frontier g r seeds y
  | frontier_step : forall x y,
      in_iterated_frontier g r seeds x -> in_frontier g r x y ->
      in_iterated_frontier g r seeds y.

(** Row closure starts with a row edge from a seed and keeps following row edges. *)
Inductive in_row_closure (rows : ptrie (list positive)) (seeds : list positive) :
    positive -> Prop :=
  | row_seed : forall x y,
      In x seeds -> In y (frontier_row rows x) -> in_row_closure rows seeds y
  | row_step : forall x y,
      in_row_closure rows seeds x -> In y (frontier_row rows x) ->
      in_row_closure rows seeds y.

(** A target task records a discovered row edge even when its vertex was a seed. *)
Inductive idf_task :=
  | IdfSeed (v : positive)
  | IdfTarget (v : positive).

Record idf_state := IdfState {
  idf_pending : list idf_task;
  idf_expanded : ptrie unit;
  idf_discovered : ptrie unit;
  idf_answer : list positive
}.
TimeFun idf_pending.
TimeFun idf_expanded.
TimeFun idf_discovered.
TimeFun idf_answer.

(** Entry counts retain every row occurrence, including repeated targets. *)
Definition frontier_entries (rows : ptrie (list positive)) (vs : list positive) : nat :=
  fold_right (fun v n => length (frontier_row rows v) + n) 0 vs.
TimeFun frontier_entries.

(** A target column shares its seen ancestors across all predecessor occurrences. *)
Record df_state := DfState {
  df_pending : list positive;
  df_seen : ptrie unit;
  df_column_answer : list positive
}.
TimeFun df_pending.
TimeFun df_seen.
TimeFun df_column_answer.

Module Type FRONTIER_OPS.
  Parameter df : prepared -> domtree -> ptrie (list positive).
  Parameter idf : ptrie (list positive) -> list positive -> list positive.
End FRONTIER_OPS.

Module Type FRONTIER_SPEC (Import F : FRONTIER_OPS).
  Definition df_size (g : prepared) (t : domtree) : nat :=
    fold_right (fun x n => length (frontier_row (df g t) x) + n) 0 (nodes g).
End FRONTIER_SPEC.

Module Type FRONTIER_LAWS (Import F : FRONTIER_OPS).
  (** Frontier rows meet the requested semantic boundary for the root argument. *)
  Parameter df_spec : forall g t r x y,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    In y (frontier_row (df g t) x) <-> in_frontier (base g) r x y.
  (** Frontier rows contain no repeated targets. *)
  Parameter df_unique : forall g t x, NoDup (frontier_row (df g t) x).
  (** Iteration returns precisely the least frontier closure seeded by definitions. *)
  Parameter idf_spec : forall g t r seeds y,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    In y (idf (df g t) seeds) <-> in_iterated_frontier (base g) r seeds y.
  (** Iterated frontiers contain each discovered target once. *)
  Parameter idf_unique : forall rows seeds, NoDup (idf rows seeds).
End FRONTIER_LAWS.

Module Type FRONTIER := FRONTIER_OPS <+ FRONTIER_SPEC <+ FRONTIER_LAWS.

Module Type FRONTIER_TIME (Import F : FRONTIER).
  Parameter T_df : prepared -> domtree -> N.
  Parameter T_idf : ptrie (list positive) -> list positive -> N.
  Parameter c_frontier : N.
  (** Frontier construction charges graph occurrences and emitted frontier members. *)
  Parameter T_df_le : forall g t r,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    (T_df g t <= c_frontier * N.of_nat (graph_n (base g) + graph_e (base g) + df_size g t + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
  (** Iteration charges the frontier rows visited from seeds and newly found targets. *)
  Parameter T_idf_le : forall rows seeds,
    (T_idf rows seeds <= c_frontier * N.of_nat (length seeds + idf_work idf rows seeds + 1) *
      N.of_nat (vertex_width
        (seeds ++ flat_map (frontier_row rows) (seeds ++ idf rows seeds)) + 1))%N.
  (** Frontier construction has the published output-sensitive bound. *)
  Parameter df_bigO : bigO (fun '(g, t, r) =>
      wf_graph (base g) /\ prepared_ok g /\ domtree_exact g r t)
    (fun '(g, t, _) => N.of_nat ((graph_n (base g) + graph_e (base g) + df_size g t + 1) *
      (graph_width (base g) + 1))) (fun '(g, t, _) => T_df g t).
  (** Iteration has the published visited-frontier bound. *)
  Parameter idf_bigO : bigO (fun _ : ptrie (list positive) * list positive => True)
    (fun '(rows, seeds) => N.of_nat ((length seeds + idf_work idf rows seeds + 1) *
      (vertex_width (seeds ++ flat_map (frontier_row rows) (seeds ++ idf rows seeds)) + 1)))
    (fun '(rows, seeds) => T_idf rows seeds).
End FRONTIER_TIME.

Module Type FRONTIER_T := FRONTIER <+ FRONTIER_TIME.

(** * Frontier proof plan *)

Module Type FRONTIER_PLAN (Import F : FRONTIER_T).
  Parameter df_step : prepared -> domtree -> positive -> df_state ->
    df_state + list positive.
  Parameter T_df_step : prepared -> domtree -> positive -> df_state -> N.
  Parameter df_column : prepared -> domtree -> positive -> list positive.
  Parameter T_df_column : prepared -> domtree -> positive -> N.
  Parameter df_transpose : list (positive * list positive) -> ptrie (list positive).
  Parameter T_df_transpose : list (positive * list positive) -> N.
  Parameter k_df_step k_df_stop k_df_column k_df_transpose k_df : N.

  Definition df_initial g y := DfState (preds g y) Empty [].

  Definition df_advance g t y st :=
    match df_step g t y st with
    | inl next => next
    | inr _ => st
    end.

  (** A column stops at the target's parent and skips unreachable or seen ancestors. *)
  Definition df_invariant g t y st : Prop :=
    (exists n, Nat.iter n (df_advance g t y) (df_initial g y) = st) /\
    NoDup (df_column_answer st) /\
    (forall x, trie_get x (df_seen st) = Some tt <-> In x (df_column_answer st)) /\
    incl (df_column_answer st) (df_column g t y) /\
    incl (df_pending st) (nodes g).

  (** White credit covers each emitted ancestor once, even with parallel predecessors. *)
  Definition df_potential g t y st : N :=
    N.of_nat (2 * length (filter (fun x =>
      match trie_get x (df_seen st) with
      | None => true
      | Some _ => false
      end)
      (df_column g t y)) + length (df_pending st)).

  Definition df_credit g t y st :=
    ((k_df_step * N.of_nat (graph_width (base g) + 1) + 1) *
      df_potential g t y st)%N.

  (** The binary budget bounds distinct ancestors and predecessor task retirements. *)
  Definition df_fuel g y : N :=
    (4 * (nv g + N.of_nat (length (preds g y)) + 1))%N.

  Definition df_columns g t : list (positive * list positive) :=
    map (fun y => (y, df_column g t y)) (nodes g).

  (** Each predecessor occurrence starts one runner with a shared column membership table. *)
  Parameter F1_df_initial : forall g t r y,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t -> In y (nodes g) ->
    df_invariant g t y (df_initial g y).

  (** Every continuing step retires a task or emits one previously unseen ancestor. *)
  Parameter F2_df_step : forall g t r y st next,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t -> In y (nodes g) ->
    df_invariant g t y st -> df_step g t y st = inl next ->
    df_invariant g t y next /\ (df_potential g t y next < df_potential g t y st)%N.

  (** The stopped answer lists exactly the ancestors emitted for this target. *)
  Parameter F3_df_stop : forall g t r y st result,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t -> In y (nodes g) ->
    df_invariant g t y st -> df_step g t y st = inr result ->
    df_pending st = [] /\ result = rev (df_column_answer st) /\ result = df_column g t y.

  (** Fuel suffices without computing a whole-tree size or a unary iteration budget. *)
  Parameter F4_df_driver : forall g t r y,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t -> In y (nodes g) ->
    loopN (df_step g t y) (df_fuel g y) (df_initial g y) = inr (df_column g t y).

  (** Columns describe the same boundary as the public rows, with duplicate pairs removed. *)
  Parameter F5_df_column : forall g t r y,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    NoDup (df_column g t y) /\ incl (df_column g t y) (nodes g) /\
      forall x, In x (df_column g t y) <-> in_frontier (base g) r x y.

  (** Transposition conses each distinct column member into its source row. *)
  Parameter F6_df_transpose : forall columns x y,
    In y (frontier_row (df_transpose columns) x) <->
      exists column, In (y, column) columns /\ In x column.

  (** Construction transposes the listed target columns. *)
  Parameter F7_df_equation : forall g t, df g t = df_transpose (df_columns g t).

  (** The emitted pair count is exactly the public output size. *)
  Parameter F8_df_pairs : forall g t r,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    fold_right (fun entry n => length (snd entry) + n) 0 (df_columns g t) = df_size g t.

  (** A local runner uses key lookups and equality, without interval-number arithmetic. *)
  Parameter T1_df_step : forall g t r y st next,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t -> In y (nodes g) ->
    df_invariant g t y st -> df_step g t y st = inl next ->
    (T_df_step g t y st + df_credit g t y next < df_credit g t y st)%N.

  (** Stopping pays one reversal of the emitted column. *)
  Parameter T2_df_stop : forall g t r y st result,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t -> In y (nodes g) ->
    df_invariant g t y st -> df_step g t y st = inr result ->
    (T_df_step g t y st <= k_df_stop * N.of_nat (length (df_column g t y) + 1))%N.

  (** The loop bound charges initial credit, stopping, task setup and binary fuel width. *)
  Parameter T3_df_loop : forall g t r y,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t -> In y (nodes g) ->
    (T_df_column g t y <= k_df_column *
      (df_credit g t y (df_initial g y) +
        k_df_stop * N.of_nat (length (df_column g t y) + 1) +
        N.of_nat (length (preds g y) + N.size_nat (df_fuel g y) + 1)))%N.

  (** Summed fuel widths are absorbed by listed vertices, predecessor occurrences and keys. *)
  Parameter T4_df_columns : forall g t r,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    (fold_right (fun y cost => T_df_column g t y + cost)%N 0%N (nodes g) <=
      k_df_column * N.of_nat (graph_n (base g) + graph_e (base g) + df_size g t + 1) *
        N.of_nat (graph_width (base g) + 1))%N.

  (** Transposition traverses emitted pairs and their trie paths once. *)
  Parameter T5_df_transpose : forall g t r,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    (T_df_transpose (df_columns g t) <= k_df_transpose *
      N.of_nat (graph_n (base g) + df_size g t + 1) *
        N.of_nat (graph_width (base g) + 1))%N.

  (** The wrapper pays the listed-node scan, columns and transposition. *)
  Parameter T6_df_wrapper : forall g t,
    (T_df g t <= k_df * (N.of_nat (length (nodes g) + 1) +
      fold_right (fun y cost => T_df_column g t y + cost)%N 0%N (nodes g) +
      T_df_transpose (df_columns g t)))%N.

  (** Column accounting and transposition give the published frontier bound. *)
  Parameter T7_df_public : forall g t r,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    (T_df g t <= c_frontier * N.of_nat (graph_n (base g) + graph_e (base g) + df_size g t + 1) *
      N.of_nat (graph_width (base g) + 1))%N.

  Parameter idf_step : ptrie (list positive) -> idf_state -> idf_state + list positive.
  Parameter T_idf_step : ptrie (list positive) -> idf_state -> N.
  Parameter idf_walk : ptrie (list positive) -> list positive -> list positive.
  Parameter T_idf_walk : ptrie (list positive) -> list positive -> N.
  Parameter k_idf_step k_idf_stop k_idf_walk : N.

  Definition idf_initial (seeds : list positive) : idf_state :=
    IdfState (map IdfSeed seeds) Empty Empty [].

  Definition idf_advance rows st :=
    match idf_step rows st with
    | inl next => next
    | inr _ => st
    end.

  (** The worklist starts with seed tasks and records target tasks separately. *)
  Definition idf_reachable rows seeds st : Prop :=
    exists n, Nat.iter n (idf_advance rows) (idf_initial seeds) = st.

  Definition idf_task_supported rows seeds task : Prop :=
    match task with
    | IdfSeed v => In v seeds
    | IdfTarget v => in_row_closure rows seeds v
    end.

  (** Expansion and discovery are separate so a returning seed enters the answer. *)
  Definition idf_invariant rows seeds st : Prop :=
    idf_reachable rows seeds st /\ NoDup (idf_answer st) /\
    (forall v, trie_get v (idf_discovered st) = Some tt <-> In v (idf_answer st)) /\
    (forall v, In v (idf_answer st) -> in_row_closure rows seeds v) /\
    (forall v, trie_get v (idf_expanded st) = Some tt ->
      In v seeds \/ in_row_closure rows seeds v) /\
    Forall (idf_task_supported rows seeds) (idf_pending st).

  (** This support is a ghost list and is never scanned to choose executable fuel. *)
  Definition idf_support rows seeds : list positive :=
    nodup Pos.eq_dec (seeds ++ idf rows seeds).

  Definition idf_white rows seeds st : nat :=
    fold_right (fun v n =>
      match trie_get v (idf_expanded st) with
      | None => 2 + length (frontier_row rows v) + n
      | Some _ => n
      end) 0 (idf_support rows seeds).

  (** Expanding a row transfers its occurrences from white credit to pending tasks. *)
  Definition idf_potential rows seeds st : N :=
    N.of_nat (2 * idf_white rows seeds st + length (idf_pending st)).

  Definition idf_width rows seeds : nat :=
    vertex_width (seeds ++ flat_map (frontier_row rows) (seeds ++ idf rows seeds)).

  Definition idf_credit rows seeds st : N :=
    ((k_idf_step * N.of_nat (idf_width rows seeds + 1) + 1) *
      idf_potential rows seeds st)%N.

  (** The subset carries erased invariant evidence over the concrete first-order state. *)
  Definition idf_guard rows seeds := { st : idf_state | idf_invariant rows seeds st }.

  (** The termination relation compares ghost pending-task credit in Prop. *)
  Definition idf_decreases rows seeds (next st : idf_guard rows seeds) : Prop :=
    (idf_potential rows seeds (proj1_sig next) <
      idf_potential rows seeds (proj1_sig st))%N.

  Parameter idf_checked_step : forall rows seeds (st : idf_guard rows seeds),
    { next : idf_guard rows seeds | idf_decreases rows seeds next st } + list positive.
  Parameter T_idf_checked_step : forall rows seeds, idf_guard rows seeds -> N.

  Definition idf_loop_credit rows seeds (st : idf_guard rows seeds) : N :=
    (k_idf_walk * idf_credit rows seeds (proj1_sig st))%N.

  (** Finite row bindings give a ghost universe without an executable whole-map scan. *)
  Parameter F1_idf_finite : forall rows seeds,
    exists universe, NoDup universe /\ incl seeds universe /\
      forall x y, In y (frontier_row rows x) -> In y universe.

  (** The lazy closure driver terminates from every finite row map and seed list. *)
  Parameter F2_idf_done : forall rows seeds,
    exists n st result,
      Nat.iter n (idf_advance rows) (idf_initial seeds) = st /\
      idf_step rows st = inr result /\ result = idf_walk rows seeds.

  (** The driver computes the least nonreflexive closure of the supplied rows. *)
  Parameter F3_idf_closure : forall rows seeds y,
    In y (idf_walk rows seeds) <-> in_row_closure rows seeds y.

  (** The public operation is the lazy row driver with no frontier reconstruction. *)
  Parameter F4_idf_equation : forall rows seeds, idf rows seeds = idf_walk rows seeds.

  (** Semantic frontier rows transport row closure to iterated graph frontiers. *)
  Parameter F5_idf_transport : forall g t r seeds y,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    (in_row_closure (df g t) seeds y <-> in_iterated_frontier (base g) r seeds y).

  (** Initialization starts with empty expansion and discovery tables. *)
  Parameter F6_idf_initial : forall rows seeds,
    idf_invariant rows seeds (idf_initial seeds).

  (** Continuing transitions keep supported tasks and spend pending or white work. *)
  Parameter F7_idf_step : forall rows seeds st next,
    idf_invariant rows seeds st -> idf_step rows st = inl next ->
    idf_invariant rows seeds next /\
      (idf_potential rows seeds next < idf_potential rows seeds st)%N.

  (** Stopping reverses the accumulated answer after all pending tasks are consumed. *)
  Parameter F8_idf_stop : forall rows seeds st result,
    idf_invariant rows seeds st -> idf_step rows st = inr result ->
    idf_pending st = [] /\ result = rev (idf_answer st) /\ result = idf rows seeds.

  (** Erasing the checked callback's evidence gives exactly the raw task transition. *)
  Parameter F8a_idf_checked : forall rows seeds st,
    match idf_checked_step rows seeds st with
    | inl next => inl (proj1_sig (proj1_sig next))
    | inr result => inr result
    end = idf_step rows (proj1_sig st).

  (** The ghost binary measure supplies accessibility for every invariant state. *)
  Parameter F8b_idf_accessible : forall rows seeds st, Acc (idf_decreases rows seeds) st.

  (** The driver uses Argent's lazy accessibility loop with erased invariant evidence. *)
  Parameter F8c_idf_loop : forall rows seeds,
    idf_walk rows seeds = Argent.Loop.loop (idf_decreases rows seeds)
      (idf_checked_step rows seeds)
      (exist _ (idf_initial seeds) (F6_idf_initial rows seeds))
      (F8b_idf_accessible rows seeds _).

  (** Every output target has an occurrence in a visited frontier row. *)
  Parameter F9_idf_output : forall rows seeds,
    length (idf rows seeds) <= idf_work idf rows seeds.

  (** Initial credit counts supplied seeds and the rows of discovered vertices. *)
  Parameter F10_idf_credit : forall rows seeds,
    (idf_potential rows seeds (idf_initial seeds) <=
      7 * N.of_nat (length seeds + idf_work idf rows seeds + 1))%N.

  (** Continuing steps pay row lookup, occurrence tasks and both membership tables. *)
  Parameter T1_idf_step : forall rows seeds st next,
    idf_invariant rows seeds st -> idf_step rows st = inl next ->
    (T_idf_step rows st + idf_credit rows seeds next < idf_credit rows seeds st)%N.

  (** The stopping callback pays one reversal of the unique discovered targets. *)
  Parameter T2_idf_stop : forall rows seeds st result,
    idf_invariant rows seeds st -> idf_step rows st = inr result ->
    (T_idf_step rows st <= k_idf_stop * N.of_nat (length (idf rows seeds) + 1))%N.

  (** The derived checked-callback clock pays its lifted pending-task potential. *)
  Parameter T2a_idf_checked_step : forall rows seeds st next Hnext,
    idf_checked_step rows seeds st = inl (exist _ next Hnext) ->
    (T_idf_checked_step rows seeds st + idf_loop_credit rows seeds next <
      idf_loop_credit rows seeds st)%N.

  (** The checked stopping callback has the same reversal charge up to its wrapper. *)
  Parameter T2b_idf_checked_stop : forall rows seeds st result,
    idf_checked_step rows seeds st = inr result ->
    (T_idf_checked_step rows seeds st <=
      k_idf_walk * (k_idf_stop * N.of_nat (length (idf rows seeds) + 1) + 1))%N.

  (** Argent's T_loop_le sums checked steps without computing an executable fuel. *)
  Parameter T2c_idf_loop : forall rows seeds st Hacc,
    (Argent.Loop.T_loop (idf_decreases rows seeds) (idf_checked_step rows seeds)
      (T_idf_checked_step rows seeds) st Hacc <= idf_loop_credit rows seeds st +
      k_idf_walk * (k_idf_stop * N.of_nat (length (idf rows seeds) + 1) + 1) + 1)%N.

  (** Accessibility recursion charges its decreasing credit and final reversal. *)
  Parameter T3_idf_walk : forall rows seeds,
    (T_idf_walk rows seeds <= k_idf_walk *
      (idf_credit rows seeds (idf_initial seeds) +
        k_idf_stop * N.of_nat (length (idf rows seeds) + 1) +
        N.of_nat (length seeds) + 1))%N.

  (** The public wrapper forwards the supplied row map and seeds once. *)
  Parameter T4_idf_wrapper : forall rows seeds,
    (T_idf rows seeds <= k_idf_walk * (T_idf_walk rows seeds + 1))%N.

  (** Combining worklist credit and output size gives the published row bound. *)
  Parameter T5_idf_public : forall rows seeds,
    (T_idf rows seeds <= c_frontier * N.of_nat (length seeds + idf_work idf rows seeds + 1) *
      N.of_nat (idf_width rows seeds + 1))%N.
End FRONTIER_PLAN.

Module Type FRONTIER_ALL := FRONTIER_T <+ FRONTIER_PLAN.
