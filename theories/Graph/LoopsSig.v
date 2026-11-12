(** * Natural loop forest signatures

    Natural loops group back-edge sources under dominating headers.
    For example, a two-vertex cycle has its DFS entry as its natural loop header.
    Builds on: DFS trace derivations, graph dominance and preparation measures. *)

From Stdlib Require Import PArith NArith List Bool.
From Argent Require Import Time Std BigO.
From Galois.Base Require Import Trie Loop.
From Galois.Graph Require Import Data Spec DigraphSig SearchSig DomSig.
Import List.ListNotations.

(** Back edges target a reachable dominator of their source. *)
Definition natural_header (g : digraph) (r h : positive) : Prop :=
  exists latch, reach g [r] latch /\ edge g latch h /\ dominates g r h latch.

(** A natural loop contains its header and paths to latches that avoid the header. *)
Definition natural_loop (g : digraph) (r h v : positive) : Prop :=
  natural_header g r h /\
  (v = h \/ exists latch vs, reach g [r] v /\ reach g [r] latch /\ edge g latch h /\
    dominates g r h latch /\ path g v vs latch /\ forall x, In x vs -> x <> h).

(** Strict containment compares the complete semantic loop bodies. *)
Definition loop_inside (g : digraph) (r inner outer : positive) : Prop :=
  inner <> outer /\ natural_header g r inner /\ natural_header g r outer /\
  (forall v, natural_loop g r inner v -> natural_loop g r outer v).

(** An immediate outer loop has no intervening strict containing loop. *)
Definition immediate_outer (g : digraph) (r inner outer : positive) : Prop :=
  loop_inside g r inner outer /\
  ~ exists middle, loop_inside g r inner middle /\ loop_inside g r middle outer.

(** The innermost header contains the vertex without a smaller containing loop. *)
Definition innermost_header (g : digraph) (r v h : positive) : Prop :=
  natural_loop g r h v /\
  ~ exists inner, natural_loop g r inner v /\ loop_inside g r inner h.

(** Retreating edges are back-edge events in a depth-first traversal from the root. *)
Definition retreating_edge (g : digraph) (r u v : positive) : Prop :=
  exists es final, dfs_roots g [] [r] es final /\ In (Edge Back u v) es.

(** Reducibility requires every retreating edge to target a dominator. *)
Definition reducible (g : digraph) (r : positive) : Prop :=
  forall u v, retreating_edge g r u v -> dominates g r v u.

Definition loop_body (l : loops) (h : positive) : list positive :=
  match l with
  | Loops _ _ rows =>
    match trie_get h rows with
    | Some vs => vs
    | None => []
    end
  end.
TimeFun loop_body.

Fixpoint loop_parent_depth (fuel : nat) (parents : ptrie positive) (h : positive) : nat :=
  match fuel with
  | 0 => 0
  | S remaining =>
    match trie_get h parents with
    | None => 0
    | Some outer => S (loop_parent_depth remaining parents outer)
    end
  end.
TimeFun loop_parent_depth.

Definition loop_depth (g : prepared) (l : loops) : nat :=
  match l with
  | Loops _ parents rows =>
    fold_right (fun h depth =>
      match trie_get h rows with
      | None => depth
      | Some _ => graph_max (S (loop_parent_depth (length (nodes g)) parents h)) depth
      end) 0 (nodes g)
  end.
TimeFun loop_depth.

(** Classification retains preorder, latch occurrences and constant-width edge membership. *)
Record loop_scan := LoopScan {
  loop_order : list positive;
  loop_latches : ptrie (list positive);
  loop_back_rows : ptrie (ptrie unit)
}.
TimeFun loop_order.
TimeFun loop_latches.
TimeFun loop_back_rows.

Definition loop_latches_at (scan : loop_scan) (h : positive) : list positive :=
  match trie_get h (loop_latches scan) with
  | Some vs => vs
  | None => []
  end.
TimeFun loop_latches_at.

Definition loop_headers_of (scan : loop_scan) : list positive :=
  filter (fun h =>
    match loop_latches_at scan h with
    | [] => false
    | _ => true
    end)
    (loop_order scan).
TimeFun loop_headers_of.

Inductive loop_tree_task :=
  | LoopTreeRoot (v : positive)
  | LoopTreeEnter (v : positive)
  | LoopTreeChildren (vs : list positive)
  | LoopTreeEdges (u : positive) (vs : list positive)
  | LoopTreeLeave (v : positive).

Record loop_tree_state := LoopTreeState {
  loop_tree_pending : list loop_tree_task;
  loop_tree_stack : list positive;
  loop_tree_active : ptrie unit;
  loop_tree_output : loop_scan
}.
TimeFun loop_tree_pending.
TimeFun loop_tree_stack.
TimeFun loop_tree_active.
TimeFun loop_tree_output.

(** A reverse traversal marks the header first so it never expands the header's predecessors. *)
Record loop_body_state := LoopBodyState {
  loop_body_pending : list positive;
  loop_body_seen : ptrie unit;
  loop_body_answer : list positive
}.
TimeFun loop_body_pending.
TimeFun loop_body_seen.
TimeFun loop_body_answer.

Module Type LOOPS_OPS.
  Parameter forest : prepared -> domtree -> loops.
  Parameter reducible_b : prepared -> domtree -> bool.
End LOOPS_OPS.

Module Type LOOPS_LAWS (Import L : LOOPS_OPS).
  (** Body bindings exist precisely at targets of dominance back edges. *)
  Parameter headers_spec : forall g t r h,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    (exists vs, trie_get h (body (forest g t)) = Some vs) <-> natural_header (base g) r h.
  (** Each header row is the semantic natural loop of that header. *)
  Parameter body_spec : forall g t r h v,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    In v (loop_body (forest g t) h) <-> natural_loop (base g) r h v.
  (** Loop bodies contain no repeated vertex. *)
  Parameter body_unique : forall g t h, NoDup (loop_body (forest g t) h).
  (** Header lookup chooses the innermost loop containing a vertex. *)
  Parameter header_spec : forall g t r v h,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    trie_get v (header (forest g t)) = Some h <-> innermost_header (base g) r v h.
  (** Parent lookup gives immediate strict containment of natural loops. *)
  Parameter parent_spec : forall g t r inner outer,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    trie_get inner (parent (forest g t)) = Some outer <->
    immediate_outer (base g) r inner outer.
  (** The Boolean test reflects the requested retreating-edge condition. *)
  Parameter reducible_b_spec : forall g t r,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    reflect (reducible (base g) r) (reducible_b g t).
End LOOPS_LAWS.

Module Type LOOPS := LOOPS_OPS <+ LOOPS_LAWS.

Module Type LOOPS_TIME (Import L : LOOPS).
  Parameter T_forest : prepared -> domtree -> N.
  Parameter T_reducible_b : prepared -> domtree -> N.
  Parameter c_loops : N.
  (** Forest construction charges graph occurrences at every loop nesting depth. *)
  Parameter T_forest_le : forall g t r,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    (T_forest g t <= c_loops * N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
      N.of_nat (loop_depth g (forest g t) + 1) * N.of_nat (graph_width (base g) + 1))%N.
  (** Reducibility checking has the published nesting-sensitive graph bound. *)
  Parameter T_reducible_b_le : forall g t r,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    (T_reducible_b g t <= c_loops * N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
      N.of_nat (loop_depth g (forest g t) + 1) * N.of_nat (graph_width (base g) + 1))%N.
  (** Forest construction has the published nesting-sensitive bit-cost bound. *)
  Parameter forest_bigO : bigO (fun '(g, t, r) =>
      wf_graph (base g) /\ prepared_ok g /\ domtree_exact g r t)
    (fun '(g, t, _) => N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
      (loop_depth g (forest g t) + 1) * (graph_width (base g) + 1)))
    (fun '(g, t, _) => T_forest g t).
  (** Reducibility checking has the published nesting-sensitive bit-cost bound. *)
  Parameter reducible_b_bigO : bigO (fun '(g, t, r) =>
      wf_graph (base g) /\ prepared_ok g /\ domtree_exact g r t)
    (fun '(g, t, _) => N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
      (loop_depth g (forest g t) + 1) * (graph_width (base g) + 1)))
    (fun '(g, t, _) => T_reducible_b g t).
End LOOPS_TIME.

Module Type LOOPS_T := LOOPS <+ LOOPS_TIME.

(** * Loop forest proof plan *)

Module Type LOOPS_PLAN (Import L : LOOPS_T).
  Parameter tree_step : prepared -> domtree -> loop_tree_state -> loop_tree_state + loop_scan.
  Parameter T_tree_step : prepared -> domtree -> loop_tree_state -> N.
  Parameter classify : prepared -> domtree -> loop_scan.
  Parameter T_classify : prepared -> domtree -> N.
  Parameter body_step : prepared -> domtree -> positive -> loop_body_state ->
    loop_body_state + list positive.
  Parameter T_body_step : prepared -> domtree -> positive -> loop_body_state -> N.
  Parameter collect : prepared -> domtree -> positive -> list positive -> list positive.
  Parameter T_collect : prepared -> domtree -> positive -> list positive -> N.
  Parameter install : loops -> positive * list positive -> loops.
  Parameter T_install : loops -> positive * list positive -> N.
  Parameter assemble : list (positive * list positive) -> loops.
  Parameter T_assemble : list (positive * list positive) -> N.
  Parameter retreat_trace : prepared -> list positive -> list event.
  Parameter T_retreat_trace : prepared -> list positive -> N.
  Parameter test_back : ptrie (ptrie unit) -> list event -> bool.
  Parameter T_test_back : ptrie (ptrie unit) -> list event -> N.
  Parameter k_tree_step k_tree_stop k_classify k_body_step k_body_stop k_collect : N.
  Parameter k_install k_trace k_test k_forest k_reducible : N.

  Definition latches := loop_latches_at.

  Definition back_member scan u v : Prop :=
    exists row, trie_get u (loop_back_rows scan) = Some row /\ trie_get v row = Some tt.

  Definition tree_initial g :=
    LoopTreeState (map LoopTreeRoot (nodes g)) [] Empty (LoopScan [] Empty Empty).

  Definition tree_advance g t st :=
    match tree_step g t st with
    | inl next => next
    | inr _ => st
    end.

  (** Active membership represents the current parent chain, independently of interval numbers. *)
  Definition tree_invariant g t r st : Prop :=
    (exists n, Nat.iter n (tree_advance g t) (tree_initial g) = st) /\
    NoDup (loop_order (loop_tree_output st)) /\
    (forall v, In v (loop_order (loop_tree_output st)) -> reach (base g) [r] v) /\
    NoDup (loop_tree_stack st) /\
    (forall v, trie_get v (loop_tree_active st) = Some tt <-> In v (loop_tree_stack st)) /\
    Forall (fun uv => trie_get (fst uv) (idom t) = Some (snd uv))
      (combine (loop_tree_stack st) (tl (loop_tree_stack st))).

  Definition tree_pending st : nat :=
    fold_right (fun task n =>
      match task with
      | LoopTreeRoot _ => 2 + n
      | LoopTreeEnter _ | LoopTreeLeave _ => 1 + n
      | LoopTreeChildren vs => 2 * length vs + 1 + n
      | LoopTreeEdges _ vs => length vs + 1 + n
      end) 0 (loop_tree_pending st).

  (** White credit reserves successor and doubled child-row cursors for each unentered vertex. *)
  Definition tree_white g t st : nat :=
    fold_right (fun v n =>
      if existsb (Pos.eqb v) (loop_order (loop_tree_output st)) then n
      else 4 + length (succs (base g) v) + 2 * length (children t v) + n) 0 (nodes g).

  Definition tree_potential g t st := N.of_nat (tree_white g t st + tree_pending st).

  Definition tree_credit g t st :=
    ((k_tree_step * N.of_nat (graph_width (base g) + 1) + 1) *
      tree_potential g t st)%N.

  Definition tree_fuel g : N := (8 * (nv g + ne g + 1))%N.

  Definition headers g t : list positive :=
    loop_headers_of (classify g t).

  Definition collected g t h := collect g t h (latches (classify g t) h).

  Definition forest_rows g t : list (positive * list positive) :=
    let scan := classify g t in
    map (fun h => (h, collect g t h (latches scan h))) (loop_headers_of scan).

  Definition body_initial h sources :=
    LoopBodyState sources (PTrieCode.set h tt Empty) [h].

  Definition body_advance g t h st :=
    match body_step g t h st with
    | inl next => next
    | inr _ => st
    end.

  (** Reverse tasks stay reachable and the seen trie agrees with the distinct body prefix. *)
  Definition body_invariant g t r h st : Prop :=
    (exists n, Nat.iter n (body_advance g t h)
      (body_initial h (latches (classify g t) h)) = st) /\
    NoDup (loop_body_answer st) /\ In h (loop_body_answer st) /\
    (forall v, trie_get v (loop_body_seen st) = Some tt <-> In v (loop_body_answer st)) /\
    incl (loop_body_answer st) (collected g t h) /\
    (forall v, In v (loop_body_pending st) -> reach (base g) [r] v).

  (** White body vertices reserve all predecessor occurrences before they become tasks. *)
  Definition body_white g t h st : nat :=
    fold_right (fun v n =>
      match trie_get v (loop_body_seen st) with
      | Some _ => n
      | None => 2 + length (preds g v) + n
      end) 0 (collected g t h).

  Definition body_potential g t h st :=
    N.of_nat (2 * body_white g t h st + length (loop_body_pending st)).

  Definition body_credit g t h st :=
    ((k_body_step * N.of_nat (graph_width (base g) + 1) + 1) *
      body_potential g t h st)%N.

  Definition body_fuel g (sources : list positive) : N :=
    (4 * (nv g + ne g + N.of_nat (length sources) + 1))%N.

  Definition body_work g vs : nat :=
    fold_right (fun v n => 1 + length (preds g v) + n) 0 vs.

  (** Each installed key and stored vertex belongs to the listed graph. *)
  Definition forest_supported g l : Prop :=
    (forall v h, trie_get v (header l) = Some h -> In v (nodes g) /\ In h (nodes g)) /\
    (forall h p, trie_get h (parent l) = Some p -> In h (nodes g) /\ In p (nodes g)) /\
    forall h vs, trie_get h (body l) = Some vs -> In h (nodes g) /\ incl vs (nodes g).

  Definition assembly_prefix g t n :=
    fold_left install (firstn n (forest_rows g t)) (Loops Empty Empty Empty).

  (** Every tree root task starts outside an active ancestor chain. *)
  Parameter F1_tree_initial : forall g t r,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    tree_invariant g t r (tree_initial g).

  (** Tree cursors spend white or pending work while maintaining active ancestry. *)
  Parameter F2_tree_step : forall g t r st next,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    tree_invariant g t r st -> tree_step g t st = inl next ->
    tree_invariant g t r next /\ (tree_potential g t next < tree_potential g t st)%N.

  (** Binary graph fuel covers the listed-root scan, tree cursors and successor occurrences. *)
  Parameter F3_tree_driver : forall g t r,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    loopN (tree_step g t) (tree_fuel g) (tree_initial g) = inr (classify g t).

  (** Classification orders every reachable vertex with each proper dominator first. *)
  Parameter F4_tree_order : forall g t r,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    NoDup (loop_order (classify g t)) /\ hd_error (loop_order (classify g t)) = Some r /\
    (forall v, In v (loop_order (classify g t)) <-> reach (base g) [r] v) /\
    forall u v, reach (base g) [r] v -> strictly_dominates (base g) r u v ->
      order_before (loop_order (classify g t)) u v.

  (** Active ancestor membership recognizes exactly the dominance back edges. *)
  Parameter F5_back_edges : forall g t r u v,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    (back_member (classify g t) u v <->
      reach (base g) [r] u /\ edge (base g) u v /\ dominates (base g) r v u) /\
    (In u (latches (classify g t) v) <-> back_member (classify g t) u v).

  (** Latch lists retain occurrences within the graph's edge budget. *)
  Parameter F6_latch_count : forall g t r,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    NoDup (headers g t) /\ incl (headers g t) (nodes g) /\
    fold_right (fun h n => length (latches (classify g t) h) + n) 0 (headers g t) <=
      graph_e (base g).

  (** Premarking a natural header starts a supported reverse traversal. *)
  Parameter F7_body_initial : forall g t r h,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t -> In h (headers g t) ->
    body_invariant g t r h (body_initial h (latches (classify g t) h)).

  (** Fresh reverse vertices transfer their predecessor occurrences into pending tasks. *)
  Parameter F8_body_step : forall g t r h st next,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t -> In h (headers g t) ->
    body_invariant g t r h st -> body_step g t h st = inl next ->
    body_invariant g t r h next /\ (body_potential g t h next < body_potential g t h st)%N.

  (** Reverse traversal finishes within the cached graph and latch occurrence budget. *)
  Parameter F9_body_driver : forall g t r h,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t -> In h (headers g t) ->
    loopN (body_step g t h) (body_fuel g (latches (classify g t) h))
      (body_initial h (latches (classify g t) h)) = inr (collected g t h).

  (** Collected bodies are distinct reachable vertices of exactly the semantic natural loop. *)
  Parameter F10_body_exact : forall g t r h,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t -> In h (headers g t) ->
    NoDup (collected g t h) /\ incl (collected g t h) (nodes g) /\
      forall v, In v (collected g t h) <-> natural_loop (base g) r h v.

  (** Distinct natural loops that meet are strictly nested. *)
  Parameter F11_laminar : forall g r h outer v,
    natural_loop g r h v -> natural_loop g r outer v -> h <> outer ->
    loop_inside g r h outer \/ loop_inside g r outer h.

  (** Outer headers precede inner headers in the dominator preorder. *)
  Parameter F12_header_order : forall g t r inner outer,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    loop_inside (base g) r inner outer -> order_before (headers g t) outer inner.

  (** Installation reads the header's previous owner before assigning the new body owner. *)
  Parameter F13_install : forall l h vs,
    body (install l (h, vs)) = PTrieCode.set h vs (body l) /\
    parent (install l (h, vs)) =
      match trie_get h (header l) with
      | Some outer => PTrieCode.set h outer (parent l)
      | None => parent l
      end /\
    header (install l (h, vs)) =
      fold_left (fun owners v => PTrieCode.set v h owners) vs (header l).

  (** Header order makes the last owner innermost and its previous owner immediately outer. *)
  Parameter F14_assembly : forall g t r,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    (forall n, forest_supported g (assembly_prefix g t n)) /\
    (forall v h, trie_get v (header (assembly_prefix g t (length (headers g t)))) = Some h <->
      innermost_header (base g) r v h) /\
    forall h outer,
      trie_get h (parent (assembly_prefix g t (length (headers g t)))) = Some outer <->
      immediate_outer (base g) r h outer.

  (** Construction shares one classification and installs the ordered natural-loop bodies. *)
  Parameter F15_forest_equation : forall g t,
    forest g t = fold_left install (forest_rows g t) (Loops Empty Empty Empty).

  (** The assembly helper is the single ordered fold used by construction. *)
  Parameter F15a_assemble : forall rows,
    assemble rows = fold_left install rows (Loops Empty Empty Empty).

  (** A vertex and each predecessor occurrence are charged at most once per containing loop. *)
  Parameter F16_nesting_charge : forall g t r,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    fold_right (fun h n => body_work g (collected g t h) + n) 0 (headers g t) <=
      (graph_n (base g) + graph_e (base g)) * loop_depth g (forest g t).

  (** The DFS trace is generated from the classified root without consulting interval values. *)
  Parameter F17_retreat_trace : forall g t r,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    exists final, dfs_roots (base g) []
      (firstn 1 (loop_order (classify g t)))
      (retreat_trace g (firstn 1 (loop_order (classify g t)))) final.

  (** Back-event checking tests only membership in the classified dominance-edge rows. *)
  Parameter F18_test_back : forall scan es,
    test_back (loop_back_rows scan) es = true <->
      forall u v, In (Edge Back u v) es -> back_member scan u v.

  (** Any complete DFS gives the same retreating-edge dominance criterion. *)
  Parameter F19_retreat_reflect : forall g r es final,
    dfs_roots g [] [r] es final ->
    ((forall u v, In (Edge Back u v) es -> dominates g r v u) <-> reducible g r).

  (** Reducibility shares classification between root discovery and back-event tests. *)
  Parameter F20_reducible_equation : forall g t,
    reducible_b g t = test_back (loop_back_rows (classify g t))
      (retreat_trace g (firstn 1 (loop_order (classify g t)))).

  (** Local tree cursor steps have constant trie work at graph key width. *)
  Parameter T1_tree_step : forall g t r st next,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    tree_invariant g t r st -> tree_step g t st = inl next ->
    (T_tree_step g t st + tree_credit g t next + c_loopN <= tree_credit g t st)%N.

  (** The final tree step reverses the reachable preorder once. *)
  Parameter T2_tree_stop : forall g t r st scan,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    tree_invariant g t r st -> tree_step g t st = inr scan ->
    (T_tree_step g t st <= k_tree_stop * N.of_nat (graph_n (base g) + 1))%N.

  (** The tree loop potential and binary fuel width fit the linear classification budget. *)
  Parameter T3_classify : forall g t r,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    (T_classify g t <= k_classify * N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
      N.of_nat (graph_width (base g) + 1))%N.

  (** Reverse steps pay predecessor scheduling from white credit at graph key width. *)
  Parameter T4_body_step : forall g t r h st next,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t -> In h (headers g t) ->
    body_invariant g t r h st -> body_step g t h st = inl next ->
    (T_body_step g t h st + body_credit g t h next + c_loopN <= body_credit g t h st)%N.

  (** The last reverse step pays one body reversal. *)
  Parameter T5_body_stop : forall g t r h st result,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t -> In h (headers g t) ->
    body_invariant g t r h st -> body_step g t h st = inr result ->
    (T_body_step g t h st <= k_body_stop * N.of_nat (length (collected g t h) + 1))%N.

  (** Each reverse loop pays its body work, latch tasks and additive binary fuel width. *)
  Parameter T6_collect : forall g t r h,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t -> In h (headers g t) ->
    (T_collect g t h (latches (classify g t) h) <= k_collect *
      (N.of_nat (body_work g (collected g t h) + length (latches (classify g t) h) + 1) *
        N.of_nat (graph_width (base g) + 1) +
        N.of_nat (N.size_nat (body_fuel g (latches (classify g t) h)))))%N.

  (** Body installation touches each listed vertex once and stores listed header values. *)
  Parameter T7_install : forall g l h vs,
    forest_supported g l -> In h (nodes g) -> incl vs (nodes g) ->
    (T_install l (h, vs) <= k_install * N.of_nat (length vs + 1) *
      N.of_nat (graph_width (base g) + 1))%N.

  (** Summing installation charges every stored body member and one parent lookup per header. *)
  Parameter T7a_assemble : forall g t r,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    (T_assemble (forest_rows g t) <= k_install *
      N.of_nat (fold_right (fun h n => (length (collected g t h) + 1 + n)%nat)
        0%nat (headers g t) + 1) *
        N.of_nat (graph_width (base g) + 1))%N.

  (** Aggregate fuel widths fit graph occurrences and identifier width without a depth scan. *)
  Parameter T7b_fuel_widths : forall g t r,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    (fold_right (fun h cost =>
      N.of_nat (N.size_nat (body_fuel g (latches (classify g t) h))) + cost)%N
        0%N (headers g t) <= k_collect *
      N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
        N.of_nat (graph_width (base g) + 1))%N.

  (** The wrapper shares classification and pays header filtering, collectors and assembly. *)
  Parameter T7c_forest_wrapper : forall g t,
    (T_forest g t <= k_forest * (T_classify g t +
      fold_right (fun h cost => T_collect g t h (latches (classify g t) h) + cost)%N
        0%N (headers g t) + T_assemble (forest_rows g t) +
      N.of_nat (graph_n (base g) + 1) * N.of_nat (graph_width (base g) + 1) + 1))%N.

  (** Nested bodies and occurrence budgets absorb all collector fuel widths and installation. *)
  Parameter T8_forest : forall g t r,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    (T_forest g t <= c_loops * N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
      N.of_nat (loop_depth g (forest g t) + 1) * N.of_nat (graph_width (base g) + 1))%N.

  (** One graph DFS and membership tests have a linear graph bit-cost bound. *)
  Parameter T9_retreat_test : forall g t r,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    (T_retreat_trace g (firstn 1 (loop_order (classify g t))) +
      T_test_back (loop_back_rows (classify g t))
        (retreat_trace g (firstn 1 (loop_order (classify g t)))) <=
      (k_trace + k_test) * N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
        N.of_nat (graph_width (base g) + 1))%N.

  (** The public Boolean wrapper pays classification and the single retreating-edge scan. *)
  Parameter T10_reducible_wrapper : forall g t,
    (T_reducible_b g t <= k_reducible * (T_classify g t +
      T_retreat_trace g (firstn 1 (loop_order (classify g t))) +
      T_test_back (loop_back_rows (classify g t))
        (retreat_trace g (firstn 1 (loop_order (classify g t)))) + 1))%N.

  (** Linear classification and testing imply the published nesting-sensitive Boolean bound. *)
  Parameter T11_reducible_public : forall g t r,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    (T_reducible_b g t <= c_loops * N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
      N.of_nat (loop_depth g (forest g t) + 1) * N.of_nat (graph_width (base g) + 1))%N.
End LOOPS_PLAN.

Module Type LOOPS_ALL := LOOPS_T <+ LOOPS_PLAN.
