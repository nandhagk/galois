(** * Weak topological order signatures

    A checked order covers the reachable vertices and sends backward edges to enclosing heads.
    For example, a self-loop requires its vertex to be a loop head.
    Builds on: graph semantics, preparation measures and Argent time interfaces. *)

From Stdlib Require Import PArith NArith List Arith Sorting.Permutation.
From Argent Require Import Time Std BigO.
From Galois.Base Require Import Trie Loop.
From Galois.Graph Require Import Data Spec DigraphSig SearchSig.
Import List.ListNotations.

Fixpoint wto_order (w : wto) : list positive :=
  match w with
  | WNil => []
  | WVertex v rest => v :: wto_order rest
  | WLoop h inside rest => h :: (wto_order inside ++ wto_order rest)
  end.
TimeFun wto_order.

Fixpoint wto_heads (w : wto) : list positive :=
  match w with
  | WNil => []
  | WVertex _ rest => wto_heads rest
  | WLoop h inside rest => h :: (wto_heads inside ++ wto_heads rest)
  end.
TimeFun wto_heads.

Fixpoint wto_depth (w : wto) : nat :=
  match w with
  | WNil => 0
  | WVertex _ rest => wto_depth rest
  | WLoop _ inside rest => graph_max (S (wto_depth inside)) (wto_depth rest)
  end.
TimeFun wto_depth.

(** A vertex lies in the loop headed by [h], including the head itself. *)
Inductive wto_encloses (h v : positive) : wto -> Prop :=
  | encloses_here : forall inside rest,
      (v = h \/ In v (wto_order inside)) -> wto_encloses h v (WLoop h inside rest)
  | encloses_vertex : forall u rest,
      wto_encloses h v rest -> wto_encloses h v (WVertex u rest)
  | encloses_body : forall u inside rest,
      wto_encloses h v inside -> wto_encloses h v (WLoop u inside rest)
  | encloses_rest : forall u inside rest,
      wto_encloses h v rest -> wto_encloses h v (WLoop u inside rest).

(** List order compares positions rather than vertex identifiers. *)
Definition graph_before (vs : list positive) (u v : positive) : Prop :=
  exists prefix middle suffix, vs = prefix ++ u :: middle ++ v :: suffix.

(** Valid orders have unique exact coverage and forward or enclosing-head edges. *)
Definition is_wto (g : prepared) (roots : list positive) (w : wto) : Prop :=
  NoDup (wto_order w) /\
  (forall v, In v (wto_order w) <-> reach (base g) roots v) /\
  forall u v, edge (base g) u v -> reach (base g) roots u ->
    graph_before (wto_order w) u v \/ wto_encloses v u w.

Inductive wto_task :=
  | WtoExpand (within : option (list positive)) (entries owners : ptrie positive)
      (component : list positive)
  | WtoClose (head : positive).

Record wto_state := WtoState {
  wto_tasks : list wto_task;
  wto_partial : wto;
  wto_parents : list wto
}.

TimeFun wto_tasks.
TimeFun wto_partial.
TimeFun wto_parents.

Inductive wto_check_task :=
  | WtoCheckVisit (w : wto)
  | WtoCheckClose (h : positive).

Record wto_check_state := WtoCheckState {
  wto_check_tasks : list wto_check_task;
  wto_check_next : N;
  wto_check_ranks : ptrie N;
  wto_check_intervals : ptrie (N * N);
  wto_check_vertices : list positive
}.
TimeFun wto_check_tasks.
TimeFun wto_check_next.
TimeFun wto_check_ranks.
TimeFun wto_check_intervals.
TimeFun wto_check_vertices.

Module Type WTO_OPS.
  Parameter build : prepared -> list positive -> wto.
  Parameter check : prepared -> list positive -> wto -> bool.
  Parameter heads : wto -> list positive.
  Parameter ranks : wto -> ptrie positive.
End WTO_OPS.

Module Type WTO_LAWS (Import W : WTO_OPS).
  (** Acceptance establishes exact rooted coverage and the nesting edge condition. *)
  Parameter check_sound : forall g roots w,
    check g roots w = true -> is_wto g roots w.
  (** Heads are the structural loop heads in traversal order. *)
  Parameter heads_spec : forall w, heads w = wto_heads w.
  (** Ranks number the unique linear order starting at one. *)
  Parameter ranks_spec : forall w, NoDup (wto_order w) -> forall v i,
    nth_error (wto_order w) i = Some v ->
    trie_get v (ranks w) = Some (Pos.of_succ_nat i).
  (** Vertices outside the linear order have no rank. *)
  Parameter ranks_absent : forall w v,
    ~ In v (wto_order w) -> trie_get v (ranks w) = None.
  (** Every reachable cycle contains a structural loop head. *)
  Parameter check_cuts : forall g roots w,
    check g roots w = true -> forall vs, cycle (base g) vs ->
    (forall v, In v vs -> reach (base g) roots v) ->
    exists h, In h vs /\ In h (heads w).
  (** Edges increase rank unless their target is a backward loop head. *)
  Parameter ranks_forward : forall g roots w u v,
    check g roots w = true -> edge (base g) u v -> reach (base g) roots u ->
    exists ru rv, trie_get u (ranks w) = Some ru /\ trie_get v (ranks w) = Some rv /\
      ((ru < rv)%positive \/ (In v (heads w) /\ (rv <= ru)%positive)).
End WTO_LAWS.

Module Type WTO := WTO_OPS <+ WTO_LAWS.

Module Type WTO_TIME (Import W : WTO).
  Parameter T_build : prepared -> list positive -> N.
  Parameter T_check : prepared -> list positive -> wto -> N.
  Parameter T_heads : wto -> N.
  Parameter T_ranks : wto -> N.
  Parameter c_wto : N.
  (** Checking has the published linear graph bit-cost bound, including rejection. *)
  Parameter T_check_le : forall g roots w,
    (T_check g roots w <= c_wto *
      N.of_nat (graph_n (base g) + graph_e (base g) + length roots + 1) *
      N.of_nat (graph_max (graph_width (base g)) (vertex_width roots) + 1))%N.
  (** Building charges each graph occurrence once per nesting level. *)
  Parameter T_build_le : forall g roots,
    (T_build g roots <= c_wto * N.of_nat (graph_n (base g) + graph_e (base g) + length roots + 1) *
      N.of_nat (wto_depth (build g roots) + 1) *
      N.of_nat (graph_max (graph_width (base g)) (vertex_width roots) + 1))%N.
  (** Head projection charges the supplied order. *)
  Parameter T_heads_le : forall w,
    (T_heads w <= c_wto * N.of_nat (length (wto_order w) + 1))%N.
  (** Ranking charges emitted keys and binary positions. *)
  Parameter T_ranks_le : forall w,
    (T_ranks w <= c_wto * N.of_nat (length (wto_order w) + 1) *
      N.of_nat (vertex_width (wto_order w) + Nat.log2 (length (wto_order w)) + 1))%N.
  (** Checking is linear in graph size and identifier width. *)
  Parameter check_bigO : bigO (fun _ : prepared * list positive * wto => True)
    (fun '(g, roots, _) => N.of_nat ((graph_n (base g) + graph_e (base g) + length roots + 1) *
      (graph_max (graph_width (base g)) (vertex_width roots) + 1)))
    (fun '(g, roots, w) => T_check g roots w).
  (** Building has the published nesting-sensitive bound. *)
  Parameter build_bigO : bigO (fun _ : prepared * list positive => True)
    (fun '(g, roots) => N.of_nat ((graph_n (base g) + graph_e (base g) + length roots + 1) *
      (wto_depth (build g roots) + 1) *
      (graph_max (graph_width (base g)) (vertex_width roots) + 1)))
    (fun '(g, roots) => T_build g roots).
End WTO_TIME.

Module Type WTO_T := WTO <+ WTO_TIME.

(** * WTO proof plan

    The functional chain checks the supplied order independently of the producer.
    [GraphHierWork] and [GraphHierCost] at [87192fe] supply additive source mass
    and depth charging for scoped SCC expansion. The converted scope materializes
    filtered rows by list membership. The selected checker also scans suffix lists.
    Their costs are kept in [scope_work] and [check_work] before the public targets. *)

Module Type WTO_PLAN (Import W : WTO_T).
  Parameter wto_key_fits : nat -> positive -> bool.
  Parameter T_wto_key_fits : nat -> positive -> N.
  Parameter wto_check_index : N -> nat -> ptrie bool -> list wto_check_task -> N ->
    ptrie N -> ptrie (N * N) -> list positive ->
    option (ptrie N * ptrie (N * N) * list positive).
  Parameter T_wto_check_index : N -> nat -> ptrie bool -> list wto_check_task -> N ->
    ptrie N -> ptrie (N * N) -> list positive -> N.
  Parameter wto_interval_edge : ptrie N -> ptrie (N * N) -> positive -> positive -> bool.
  Parameter T_wto_interval_edge : ptrie N -> ptrie (N * N) -> positive -> positive -> N.
  Parameter wto_member : positive -> list positive -> bool.
  Parameter wto_unique : list positive -> bool.
  Parameter wto_annotate : list positive -> wto -> list (positive * list positive).
  Parameter wto_positions : list (positive * list positive) ->
    ptrie (list positive * list positive).
  Parameter wto_edge_b : ptrie (list positive * list positive) -> positive -> positive -> bool.
  Parameter wto_rank_rows : positive -> list positive -> ptrie positive.
  Parameter wto_scoped : prepared -> option (list positive) -> prepared.
  Parameter wto_components : prepared -> list positive -> scc.
  Parameter wto_entries : prepared -> list positive -> scc -> ptrie positive.
  Parameter wto_preferred : ptrie positive -> ptrie positive -> list positive -> option positive.
  Parameter wto_select : option positive -> list positive -> option (positive * list positive).
  Parameter wto_reverse_into : wto -> wto -> wto.
  Parameter wto_expand_tasks : option (list positive) -> ptrie positive -> ptrie positive ->
    list (list positive) -> list wto_task.
  Parameter wto_step : prepared -> wto_state -> wto_state + wto.
  Parameter search_trace : digraph -> list positive -> list event.
  Parameter T_wto_member : positive -> list positive -> N.
  Parameter T_wto_unique : list positive -> N.
  Parameter T_wto_annotate : list positive -> wto -> N.
  Parameter T_wto_positions : list (positive * list positive) -> N.
  Parameter T_wto_edge_b : ptrie (list positive * list positive) -> positive -> positive -> N.
  Parameter T_wto_rank_rows : positive -> list positive -> N.
  Parameter T_wto_scoped : prepared -> option (list positive) -> N.
  Parameter T_wto_components : prepared -> list positive -> N.
  Parameter T_wto_entries : prepared -> list positive -> scc -> N.
  Parameter T_wto_preferred : ptrie positive -> ptrie positive -> list positive -> N.
  Parameter T_wto_select : option positive -> list positive -> N.
  Parameter T_wto_reverse_into : wto -> wto -> N.
  Parameter T_wto_expand_tasks : option (list positive) -> ptrie positive -> ptrie positive ->
    list (list positive) -> N.
  Parameter T_wto_step : prepared -> wto_state -> N.
  Parameter T_search_trace : digraph -> list positive -> N.
  Parameter history : prepared -> list positive -> list wto_state.
  Parameter k_member k_index k_check k_scope k_expand k_build k_heads k_ranks : N.

  Definition live (g : prepared) roots := entered (search_trace (base g) roots).
  Definition checked_index w := wto_positions (wto_annotate [] w).

  (** The index records all later vertices and the enclosing structural heads. *)
  Definition index_correct w : Prop :=
    forall u,
      (trie_get u (checked_index w) = None <-> ~ In u (wto_order w)) /\
      forall after stack, trie_get u (checked_index w) = Some (after, stack) ->
        In u (wto_order w) /\
        (forall v, In v after <-> graph_before (wto_order w) u v) /\
        (forall h, In h stack <-> wto_encloses h u w).

  (** Accepted candidates have exact live coverage and indexed legal edges. *)
  Definition checked g roots w : Prop :=
    (forall v, In v roots -> In v (nodes g)) /\
    (forall v, In v (wto_order w) -> In v (nodes g)) /\
    NoDup (wto_order w) /\
    (forall v, In v (wto_order w) <-> In v (live g roots)) /\
    forall u v, In u (wto_order w) -> edge (base g) u v ->
      wto_edge_b (checked_index w) u v = true.

  Definition source_mass (g : prepared) (vs : list positive) : nat :=
    fold_right (fun v n => 1 + length (succs (base g) v) + n) 0 vs.

  (** Materialized scopes index allowed keys and filter each outgoing occurrence once. *)
  Definition scope_work g vs :=
    (source_mass g vs + 1) *
      (graph_max (graph_width (base g)) (vertex_width vs) + 1).

  Definition task_members (task : wto_task) : list positive :=
    match task with WtoExpand _ _ _ c => c | WtoClose _ => [] end.

  Definition task_mass (g : prepared) task :=
    match task with WtoExpand _ _ _ c => 3 * length c | WtoClose _ => 1 end.

  (** Header removal spends one vertex and reserves one matching close task.
      This nat measure counts transitions for termination. *)
  Definition potential g st :=
    fold_right (fun task n => task_mass g task + n) 0 (wto_tasks st).

  Definition initial g roots :=
    let r := wto_components g roots in
    WtoState (wto_expand_tasks None (wto_entries g roots r) (comp r) (rev (comps r)))
      WNil [].

  Definition advance g st :=
    match wto_step g st with inl next => next | inr _ => st end.

  (** The builder inventory counts pending members, partial output and suspended parent output. *)
  Definition inventory (vertices : list positive) (st : wto_state) : Prop :=
    Permutation vertices
      (concat (map task_members (wto_tasks st)) ++ wto_order (wto_partial st) ++
        concat (map wto_order (wto_parents st)) ++
        fold_right (fun task hs =>
          match task with WtoClose h => h :: hs | _ => hs end) [] (wto_tasks st)) /\
    length (wto_parents st) =
      length (filter (fun task => match task with WtoClose _ => true | _ => false end)
        (wto_tasks st)).

  Definition invariant g roots st : Prop :=
    (exists n, Nat.iter n (advance g) (initial g roots) = st) /\
    inventory (concat (comps (wto_components g roots))) st.

  Definition level_mass g level states :=
    fold_right (fun st n =>
      if Nat.eqb (length (wto_parents st)) level then
        match wto_tasks st with
        | WtoExpand _ _ _ c :: _ => source_mass g c + n
        | _ => n
        end
      else n) 0 states.

  Definition scope_charge g states :=
    fold_right (fun st n =>
      match wto_tasks st with
      | WtoExpand _ entries owners c :: _ =>
        match wto_select (wto_preferred owners entries c) c with
        | Some (_, body) => scope_work g body + n
        | None => n
        end
      | _ => n
      end) 0 states.

  Definition execution_cost g states : N :=
    fold_right (fun st n => (T_wto_step g st + n)%N) 0%N states.

  (** List scans are charged even for candidates that the checker rejects. *)
  Definition check_work g roots (w : wto) :=
    N.of_nat ((graph_n (base g) + graph_e (base g) + length roots + 1) *
      (graph_max (graph_width (base g)) (vertex_width roots) + 1)).

  (** Membership and duplicate checking describe the supplied lists. *)
  Parameter F1_lists :
    (forall v vs, wto_member v vs = true <-> In v vs) /\
    (forall vs, wto_unique vs = true <-> NoDup vs).

  (** Annotation retains order and records the structural nesting relation. *)
  Parameter F2_annotation : forall w, NoDup (wto_order w) ->
    map fst (wto_annotate [] w) = wto_order w /\
    forall u stack, In (u, stack) (wto_annotate [] w) ->
      forall h, In h stack <-> wto_encloses h u w.

  (** Unique annotations make every stored suffix agree with linear order. *)
  Parameter F3_index : forall w, NoDup (wto_order w) -> index_correct w.

  (** The selected checker tests uniqueness, exact coverage and each indexed edge. *)
  Parameter F4_check : forall g roots w, check g roots w = true <-> checked g roots w.

  (** Search completeness supplies rooted coverage even for raw graphs and unlisted roots. *)
  Parameter F5_live : forall g roots v, In v (live g roots) <-> reach (base g) roots v.

  (** Acceptance and the index relation establish the public WTO specification. *)
  Parameter F6_sound : forall g roots w, check g roots w = true -> is_wto g roots w.

  (** An enclosing head belongs to both the structural order and its head projection. *)
  Parameter F7_encloses : forall w h v,
    wto_encloses h v w -> In h (wto_heads w) /\ In h (wto_order w).

  (** A reachable cycle without heads would strictly increase position at every edge. *)
  Parameter F8_cycle : forall g roots w,
    is_wto g roots w -> forall vs, cycle (base g) vs ->
    (forall v, In v vs -> reach (base g) roots v) ->
    exists h, In h vs /\ In h (wto_heads w).

  (** Ranking starts at one and excludes all vertices absent from the structural order. *)
  Parameter F9_ranks : forall w,
    ranks w = wto_rank_rows 1%positive (wto_order w) /\
    (forall v, ~ In v (wto_order w) -> trie_get v (ranks w) = None) /\
    (NoDup (wto_order w) -> forall v i,
      nth_error (wto_order w) i = Some v ->
      trie_get v (ranks w) = Some (Pos.of_succ_nat i)).

  (** Position comparison becomes the accepted edge's rank comparison. *)
  Parameter F10_forward : forall g roots w u v,
    check g roots w = true -> edge (base g) u v -> reach (base g) roots u ->
    exists ru rv, trie_get u (ranks w) = Some ru /\ trie_get v (ranks w) = Some rv /\
      ((ru < rv)%positive \/ (In v (heads w) /\ (rv <= ru)%positive)).

  (** Selection removes exactly one header occurrence from a nonempty component. *)
  Parameter F11_select : forall preferred c h body,
    wto_select preferred c = Some (h, body) -> Permutation c (h :: body).

  (** Child scopes keep the allowed vertices and their filtered successor occurrences. *)
  Parameter F12_scope : forall g vs,
    nodes (wto_scoped g (Some vs)) = vs /\
    forall v, In v vs -> succs (base (wto_scoped g (Some vs))) v =
      filter (fun u => wto_member u vs) (succs (base g) v).

  (** Child SCC lists partition the header-deleted body and conserve additive original-row mass. *)
  Parameter F13_partition : forall g body,
    NoDup body ->
    let r := wto_components (wto_scoped g (Some body)) (rev body) in
    Permutation (concat (comps r)) body /\
    fold_right (fun c n => source_mass g c + n) 0 (comps r) = source_mass g body.

  (** Actual builder states maintain the member and parent inventory. *)
  Parameter F14_initial : forall g roots,
    invariant g roots (initial g roots) /\
    potential g (initial g roots) = 3 * length (concat (comps (wto_components g roots))).

  (** A continuing expansion spends member credit and a close step spends its reserved unit. *)
  Parameter F15_step : forall g roots st next,
    invariant g roots st -> wto_step g st = inl next ->
    invariant g roots next /\ potential g next < potential g st.

  (** The producer fuel pays the entire expansion inventory without asserting producer soundness. *)
  Parameter F16_done : forall g roots,
    exists w, loopN (wto_step g)
      (N.of_nat (3 * length (concat (comps (wto_components g roots))) + 1))
      (initial g roots) = inr w.

  (** The history enumerates actual callback states through the terminal step. *)
  Parameter F17_history : forall g roots,
    exists terminal prefix, history g roots = prefix ++ [terminal] /\
      (match prefix with [] => terminal | first :: _ => first end) = initial g roots /\
      Forall2 (fun before after => wto_step g before = inl after)
        prefix (tl (history g roots)) /\
      wto_step g terminal = inr (build g roots).

  (** Components expanded at one parent depth have disjoint original vertex inventories. *)
  Parameter F18_level_mass : forall g roots level,
    level_mass g level (history g roots) <=
      source_mass g (concat (comps (wto_components g roots))).

  (** Each expansion depth is bounded by the produced structural nesting depth. *)
  Parameter F19_depth : forall g roots st within entries owners c tasks,
    In st (history g roots) ->
    wto_tasks st = WtoExpand within entries owners c :: tasks ->
    length (wto_parents st) <= wto_depth (build g roots).

  (** Each membership query scans at most its list length and the compared key widths. *)
  Parameter T1_member : forall v vs,
    (T_wto_member v vs <= k_member * N.of_nat (length vs + 1) *
      N.of_nat (graph_max (Pos.size_nat v) (vertex_width vs) + 1))%N.

  (** Index construction retains the quadratic suffix materialization cost. *)
  Parameter T2_index : forall rows,
    (T_wto_positions rows <= k_index * N.of_nat (length rows + 1) *
      N.of_nat (length rows + vertex_width (map fst rows) + 1))%N.

  (** Materialized filtering pays a list membership scan for each outgoing occurrence. *)
  Parameter T3_scope : forall g vs,
    (T_wto_scoped g (Some vs) <= k_scope * N.of_nat (scope_work g vs))%N.

  (** The selected checker has a candidate-sensitive scan budget before any public absorption. *)
  Parameter T4_check_scans : forall g roots w,
    (T_check g roots w <= k_check * check_work g roots w)%N.

  (** The public checker target needs a linear checker and a candidate rejection boundary. *)
  Parameter T5_check_public : forall g roots w,
    (T_check g roots w <= c_wto *
      N.of_nat (graph_n (base g) + graph_e (base g) + length roots + 1) *
      N.of_nat (graph_max (graph_width (base g)) (vertex_width roots) + 1))%N.

  (** A child expansion pays scope materialization, SCC, entries and task assembly separately. *)
  Parameter T6_expand : forall g within entries owners c tasks partial parents h body,
    wto_select (wto_preferred owners entries c) c = Some (h, body) -> body <> [] ->
    (T_wto_step g (WtoState (WtoExpand within entries owners c :: tasks) partial parents) <=
      k_expand * (T_wto_preferred owners entries c +
        T_wto_select (wto_preferred owners entries c) c + T_wto_scoped g (Some body) +
        T_wto_components (wto_scoped g (Some body)) (rev body) +
        T_wto_entries (wto_scoped g (Some body)) (rev body)
          (wto_components (wto_scoped g (Some body)) (rev body)) +
        N.of_nat (length body) + N.of_nat (length c) + 1))%N.

  (** The unchanged builder target needs depth charging for materialized scopes and root scans. *)
  Parameter T7_build_public : forall g roots,
    (T_build g roots <= c_wto * N.of_nat (graph_n (base g) + graph_e (base g) + length roots + 1) *
      N.of_nat (wto_depth (build g roots) + 1) *
      N.of_nat (graph_max (graph_width (base g)) (vertex_width roots) + 1))%N.

  (** The current structural head traversal retains the cost of each body-list append. *)
  Parameter T8_heads_source : forall w,
    (T_heads w <= k_heads * (T_wto_heads w + 1))%N.

  (** The linear head target needs an append-accounting or accumulator implementation argument. *)
  Parameter T9_heads_public : forall w,
    (T_heads w <= c_wto * N.of_nat (length (wto_order w) + 1))%N.

  (** Ranking pays structural flattening before inserting binary positions. *)
  Parameter T10_ranks_source : forall w,
    (T_ranks w <= k_ranks * (T_wto_order w +
      T_wto_rank_rows 1%positive (wto_order w) + 1))%N.

  (** The public rank target must absorb structural flattening as well as trie insertion. *)
  Parameter T11_ranks_public : forall w,
    (T_ranks w <= c_wto * N.of_nat (length (wto_order w) + 1) *
      N.of_nat (vertex_width (wto_order w) + Nat.log2 (length (wto_order w)) + 1))%N.
End WTO_PLAN.

Module Type WTO_ALL := WTO_T <+ WTO_PLAN.
