(** * Weak topological order production and checking

    The producer recursively removes an entry header from each cyclic component.
    For example, a singleton self edge produces an empty loop body.
    Builds on: Tarjan search, first-order graph data and the WTO signature. *)

From Stdlib Require Import List Bool PArith NArith Sorting.Permutation.
From Argent Require Import Time Tactics Std BigO.
From Galois.Base Require Import Trie Loop.
From Galois.Graph Require Import Data Spec DigraphSig SearchSig Search SccSig Scc WtoSig.
Import List.ListNotations.

Module TimeHelpers.
  Module List.
    TimeFun List.concat.
  End List.
End TimeHelpers.

Definition wto_member (v : positive) xs := existsb (Pos.eqb v) xs.
TimeFun wto_member.

Definition wto_scoped (g : prepared) (within : option (list positive)) : prepared :=
  match within with
  | None => g
  | Some vs =>
    let listed := fold_left (fun acc v => PTrieCode.set v true acc) vs Empty in
    let adjacency := fold_left (fun acc v =>
      PTrieCode.set v (filter (fun u =>
        match trie_get u listed with Some _ => true | None => false end)
        (succs (base g) v)) acc) vs Empty in
    Prepared (Digraph vs adjacency) Empty (nv g) (ne g)
  end.
TimeFun wto_scoped.

Definition wto_components g roots :=
  let ready := scc_graph g in
  let listed_roots := filter (fun v =>
    match trie_get v (succ (base ready)) with Some _ => true | None => false end) roots in
  let s := TarjanSearch.dfs ready listed_roots tarjan_initial in
  Scc (tarjan_owners s) (rev (tarjan_emitted s)).
TimeFun wto_components.

Definition wto_offer i v (entries : ptrie positive) :=
  match trie_get i entries with Some _ => entries | None => PTrieCode.set i v entries end.
TimeFun wto_offer.

Definition wto_root_entry owners entries v :=
  match trie_get v owners with None => entries | Some i => wto_offer i v entries end.
TimeFun wto_root_entry.

Definition wto_edge_entry owners source entries v :=
  match source, trie_get v owners with
  | Some i, Some j => if Pos.eqb i j then entries else wto_offer j v entries
  | _, _ => entries
  end.
TimeFun wto_edge_entry.

Definition wto_entries g roots r :=
  let owners := comp r in
  let seeded := fold_left (wto_root_entry owners) roots Empty in
  fold_left (fun entries c => fold_left (fun entries u =>
    fold_left (wto_edge_entry owners (trie_get u owners)) (succs (base g) u) entries)
    c entries) (comps r) seeded.
TimeFun wto_entries.

Definition wto_preferred (owners entries : ptrie positive) (c : list positive) :=
  match c with
  | [] => None
  | v :: _ => match trie_get v owners with None => None | Some i => trie_get i entries end
  end.
TimeFun wto_preferred.

Fixpoint wto_select (preferred : option positive) (c : list positive) :=
  match c with
  | [] => None
  | v :: rest =>
    if match preferred with None => false | Some h => Pos.eqb v h end
    then Some (v, rest)
    else match wto_select preferred rest with
      | None => Some (v, rest)
      | Some (h, body) => Some (h, v :: body)
      end
  end.
TimeFun wto_select.

Fixpoint wto_reverse_into (w tail : wto) : wto :=
  match w with
  | WNil => tail
  | WVertex v rest => wto_reverse_into rest (WVertex v tail)
  | WLoop h body rest => wto_reverse_into rest (WLoop h body tail)
  end.
TimeFun wto_reverse_into.

Definition wto_expand_tasks within entries owners cs :=
  map (fun c => WtoExpand within entries owners c) cs.
TimeFun wto_expand_tasks.

Definition wto_step (g : prepared) (s : wto_state) : wto_state + wto :=
  match s with
  | WtoState [] partial _ => inr (wto_reverse_into partial WNil)
  | WtoState (WtoClose h :: tasks) partial (parent :: parents) =>
    inl (WtoState tasks (WLoop h (wto_reverse_into partial WNil) parent) parents)
  | WtoState (WtoClose _ :: tasks) partial [] => inl (WtoState tasks partial [])
  | WtoState (WtoExpand within entries owners c :: tasks) partial parents =>
    match wto_select (wto_preferred owners entries c) c with
    | None => inl (WtoState tasks partial parents)
    | Some (h, []) =>
      let tree := if wto_member h (succs (base g) h)
        then WLoop h WNil partial else WVertex h partial in
      inl (WtoState tasks tree parents)
    | Some (h, body) =>
      let child := Some body in
      let scoped := wto_scoped g child in
      let roots := rev body in
      let r := wto_components scoped roots in
      let entries' := wto_entries scoped roots r in
      inl (WtoState
        (wto_expand_tasks child entries' (comp r) (rev (comps r)) ++ WtoClose h :: tasks)
        WNil (partial :: parents))
    end
  end.
TimeFun wto_step.

Fixpoint wto_unique (xs : list positive) :=
  match xs with
  | [] => true
  | v :: rest => negb (wto_member v rest) && wto_unique rest
  end.
TimeFun wto_unique.

Fixpoint wto_annotate (stack : list positive) (w : wto) :
    list (positive * list positive) :=
  match w with
  | WNil => []
  | WVertex v rest => (v, stack) :: wto_annotate stack rest
  | WLoop h body rest =>
    (h, h :: stack) :: (wto_annotate (h :: stack) body ++ wto_annotate stack rest)
  end.
TimeFun wto_annotate.

Fixpoint wto_positions (rows : list (positive * list positive)) :
    ptrie (list positive * list positive) :=
  match rows with
  | [] => Empty
  | (v, stack) :: rest => PTrieCode.set v (map fst rest, stack) (wto_positions rest)
  end.
TimeFun wto_positions.

Definition wto_edge_b index a b :=
  match trie_get a index with
  | None => false
  | Some (after, stack) => wto_member b after || wto_member b stack
  end.
TimeFun wto_edge_b.

Fixpoint wto_rank_rows (start : positive) (vs : list positive) : ptrie positive :=
  match vs with
  | [] => Empty
  | v :: rest => PTrieCode.set v start (wto_rank_rows (Pos.succ start) rest)
  end.
TimeFun wto_rank_rows.

(** Width rejection stops before traversing an oversized candidate key. *)
Fixpoint wto_key_fits (width : nat) (v : positive) : bool :=
  match width, v with
  | O, _ => false
  | S _, xH => true
  | S rest, xO tail | S rest, xI tail => wto_key_fits rest tail
  end.
TimeFun wto_key_fits.

(** Each candidate transition visits one constructor or closes one loop interval. *)
Definition wto_check_step (width : nat) (listed : ptrie bool) (s : wto_check_state)
    : wto_check_state + option (ptrie N * ptrie (N * N) * list positive) :=
  match s with
  | WtoCheckState [] _ ranks intervals vs => inr (Some (ranks, intervals, rev vs))
  | WtoCheckState (task :: rest) next ranks intervals vs =>
    match task with
    | WtoCheckClose h =>
      match trie_get h ranks with
      | None => inr None
      | Some lo => inl (WtoCheckState rest next ranks
          (PTrieCode.set h (lo, next) intervals) vs)
      end
    | WtoCheckVisit WNil => inl (WtoCheckState rest next ranks intervals vs)
    | WtoCheckVisit (WVertex v tail) =>
      if wto_key_fits width v then
        match trie_get v listed, trie_get v ranks with
        | Some _, None => inl (WtoCheckState (WtoCheckVisit tail :: rest) (N.succ next)
            (PTrieCode.set v next ranks) intervals (v :: vs))
        | _, _ => inr None
        end
      else inr None
    | WtoCheckVisit (WLoop h body tail) =>
      if wto_key_fits width h then
        match trie_get h listed, trie_get h ranks with
        | Some _, None => inl (WtoCheckState
            (WtoCheckVisit body :: WtoCheckClose h :: WtoCheckVisit tail :: rest)
            (N.succ next) (PTrieCode.set h next ranks) intervals (h :: vs))
        | _, _ => inr None
        end
      else inr None
    end
  end.
TimeFun wto_check_step.

Definition wto_check_index (fuel : N) (width : nat) (listed : ptrie bool)
    (tasks : list wto_check_task) (next : N) (ranks : ptrie N)
    (intervals : ptrie (N * N)) (vs : list positive)
    : option (ptrie N * ptrie (N * N) * list positive) :=
  match loopN (wto_check_step width listed) fuel (WtoCheckState tasks next ranks intervals vs) with
  | inl _ => None
  | inr result => result
  end.
TimeFun wto_check_index.


Definition wto_interval_edge (ranks : ptrie N) (intervals : ptrie (N * N))
    (u v : positive) : bool :=
  match trie_get u ranks, trie_get v ranks with
  | Some ru, Some rv =>
    N.ltb ru rv ||
      match trie_get v intervals with
      | Some (lo, hi) => N.leb lo ru && N.ltb ru hi
      | None => false
      end
  | _, _ => false
  end.
TimeFun wto_interval_edge.

(** The edge scan is the final conjunct of the checker. *)
Definition wto_edges_ok (b : digraph) (ranks : ptrie N) (intervals : ptrie (N * N))
    (vs : list positive) : bool :=
  forallb (fun u => forallb (wto_interval_edge ranks intervals u) (succs b u)) vs.
TimeFun wto_edges_ok.

(** The checker builds its own listed-row graph and never reads prepared caches. *)
Definition wto_check_linear (g : prepared) (roots : list positive) (w : wto) : bool :=
  let b := base g in
  let listed := listed_of g in
  if forallb (fun v => match trie_get v listed with Some _ => true | None => false end) roots
  then
    match wto_check_index (check_fuel g) (graph_width b) listed
        [WtoCheckVisit w] 0%N Empty Empty [] with
    | None => false
    | Some (ranks, intervals, vs) =>
      let ready := scc_graph g in
      let live := entered (prepared_search_trace ready roots) in
      let reached := fold_left (fun acc v => PTrieCode.set v true acc) live Empty in
      forallb (fun v => match trie_get v reached with Some _ => true | None => false end) vs &&
      forallb (fun v => match trie_get v ranks with Some _ => true | None => false end) live &&
      wto_edges_ok b ranks intervals vs
    end
  else false.
TimeFun wto_check_linear.

Module WtoCode <: WTO_OPS.
  Definition build (g : prepared) (roots : list positive) : wto :=
    let r := wto_components g roots in
    let entries := wto_entries g roots r in
    let cs := comps r in
    let size := length (concat cs) in
    let initial := WtoState (wto_expand_tasks None entries (comp r) (rev cs)) WNil [] in
    match loopN (wto_step g) (N.of_nat (3 * size + 1)) initial with
    | inl s => wto_reverse_into (wto_partial s) WNil
    | inr w => w
    end.

  Definition check := wto_check_linear.

  Definition heads := wto_heads.
  Definition ranks w := wto_rank_rows 1%positive (wto_order w).
End WtoCode.

Module Wto <: WTO.
  Include WtoCode.

  (** Acceptance establishes exact rooted coverage and the nesting edge condition. *)
  Lemma check_sound : forall g roots w,
    check g roots w = true -> is_wto g roots w.
  Proof. Admitted. (* CONVERT: WtoCheck.check_correct: interval checker requires the new proof. *)

  (** Heads are the structural loop heads in traversal order. *)
  Lemma heads_spec : forall w, heads w = wto_heads w.
  Proof.
    reflexivity.
  Qed.

  (** Ranks number the unique linear order starting at one. *)
  Lemma ranks_spec : forall w, NoDup (wto_order w) -> forall v i,
    nth_error (wto_order w) i = Some v ->
    trie_get v (ranks w) = Some (Pos.of_succ_nat i).
  Proof. Admitted. (* SIG-QUESTION: WeakOrder.ranks_spec uses membership and advance ranks. *)

  (** Vertices outside the linear order have no rank. *)
  Lemma ranks_absent : forall w v,
    ~ In v (wto_order w) -> trie_get v (ranks w) = None.
  Proof. Admitted. (* SIG-QUESTION: landed rank lemmas do not state absent-key lookup. *)

  (** Every reachable cycle contains a structural loop head. *)
  Lemma check_cuts : forall g roots w,
    check g roots w = true -> forall vs, cycle (base g) vs ->
    (forall v, In v vs -> reach (base g) roots v) ->
    exists h, In h vs /\ In h (heads w).
  Proof. Admitted. (* SIG-QUESTION: WeakOrder.cycles_have_head concerns producer token annotations. *)

  (** Edges increase rank unless their target is a backward loop head. *)
  Lemma ranks_forward : forall g roots w u v,
    check g roots w = true -> edge (base g) u v -> reach (base g) roots u ->
    exists ru rv, trie_get u (ranks w) = Some ru /\ trie_get v (ranks w) = Some rv /\
      ((ru < rv)%positive \/ (In v (heads w) /\ (rv <= ru)%positive)).
  Proof. Admitted. (* SIG-QUESTION: WeakOrder.ranks_forward concludes annotation membership. *)
End Wto.

Module WtoT <: WTO_ALL.
  Include Wto.
  Definition wto_key_fits := wto_key_fits.
  TimeFun wto_key_fits.
  Definition wto_check_index := wto_check_index.
  TimeFun wto_check_index.
  Definition wto_interval_edge := wto_interval_edge.
  TimeFun wto_interval_edge.
  Definition wto_edges_ok := wto_edges_ok.
  TimeFun wto_edges_ok.
  TimeFun build.
  TimeFun check.
  TimeFun heads.
  TimeFun ranks.
  Definition c_wto : N := 1%N. (* STUB *)

  Lemma T_check_le : forall g roots w,
    (T_check g roots w <= c_wto *
      N.of_nat (graph_n (base g) + graph_e (base g) + length roots + 1) *
      N.of_nat (graph_max (graph_width (base g)) (vertex_width roots) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T_build_le : forall g roots,
    (T_build g roots <= c_wto * N.of_nat (graph_n (base g) + graph_e (base g) + length roots + 1) *
      N.of_nat (wto_depth (build g roots) + 1) *
      N.of_nat (graph_max (graph_width (base g)) (vertex_width roots) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T_heads_le : forall w,
    (T_heads w <= c_wto * N.of_nat (length (wto_order w) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T_ranks_le : forall w,
    (T_ranks w <= c_wto * N.of_nat (length (wto_order w) + 1) *
      N.of_nat (vertex_width (wto_order w) + Nat.log2 (length (wto_order w)) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma check_bigO : bigO (fun _ : prepared * list positive * wto => True)
    (fun '(g, roots, _) => N.of_nat ((graph_n (base g) + graph_e (base g) + length roots + 1) *
      (graph_max (graph_width (base g)) (vertex_width roots) + 1)))
    (fun '(g, roots, w) => T_check g roots w).
  Proof. Admitted. (* STUB *)

  Lemma build_bigO : bigO (fun _ : prepared * list positive => True)
    (fun '(g, roots) => N.of_nat ((graph_n (base g) + graph_e (base g) + length roots + 1) *
      (wto_depth (build g roots) + 1) *
      (graph_max (graph_width (base g)) (vertex_width roots) + 1)))
    (fun '(g, roots) => T_build g roots).
  Proof. Admitted. (* STUB *)

  Definition wto_member := wto_member.
  TimeFun wto_member.
  Definition wto_unique := wto_unique.
  TimeFun wto_unique.
  Definition wto_annotate := wto_annotate.
  TimeFun wto_annotate.
  Definition wto_positions := wto_positions.
  TimeFun wto_positions.
  Definition wto_edge_b := wto_edge_b.
  TimeFun wto_edge_b.
  Definition wto_rank_rows := wto_rank_rows.
  TimeFun wto_rank_rows.
  Definition wto_scoped := wto_scoped.
  TimeFun wto_scoped.
  Definition wto_components := wto_components.
  TimeFun wto_components.
  Definition wto_entries := wto_entries.
  TimeFun wto_entries.
  Definition wto_preferred := wto_preferred.
  TimeFun wto_preferred.
  Definition wto_select := wto_select.
  TimeFun wto_select.
  Definition wto_reverse_into := wto_reverse_into.
  TimeFun wto_reverse_into.
  Definition wto_expand_tasks := wto_expand_tasks.
  TimeFun wto_expand_tasks.
  Definition wto_step := wto_step.
  TimeFun wto_step.
  Definition search_trace := search_trace.
  TimeFun search_trace.

  Definition k_member : N := 1%N. (* STUB *)
  Definition k_index : N := 1%N. (* STUB *)
  Definition k_check : N := 1%N. (* STUB *)
  Definition k_scope : N := 1%N. (* STUB *)
  Definition k_expand : N := 1%N. (* STUB *)
  Definition k_build : N := 1%N. (* STUB *)
  Definition k_heads : N := 1%N. (* STUB *)
  Definition k_ranks : N := 1%N. (* STUB *)

  Definition live (g : prepared) roots := entered (search_trace (base g) roots).
  Definition checked_index w := wto_positions (wto_annotate [] w).
  Definition index_correct w : Prop :=
    forall u,
      (trie_get u (checked_index w) = None <-> ~ In u (wto_order w)) /\
      forall after stack, trie_get u (checked_index w) = Some (after, stack) ->
        In u (wto_order w) /\
        (forall v, In v after <-> graph_before (wto_order w) u v) /\
        (forall h, In h stack <-> wto_encloses h u w).
  Definition checked g roots w : Prop :=
    (forall v, In v roots -> In v (nodes g)) /\
    (forall v, In v (wto_order w) -> In v (nodes g)) /\
    NoDup (wto_order w) /\
    (forall v, In v (wto_order w) <-> In v (live g roots)) /\
    forall u v, In u (wto_order w) -> edge (base g) u v ->
      wto_edge_b (checked_index w) u v = true.
  Definition source_mass (g : prepared) (vs : list positive) : nat :=
    fold_right (fun v n => 1 + length (succs (base g) v) + n) 0 vs.
  Definition scope_work g vs :=
    (source_mass g vs + 1) *
      (graph_max (graph_width (base g)) (vertex_width vs) + 1).
  Definition task_members (task : wto_task) : list positive :=
    match task with WtoExpand _ _ _ c => c | WtoClose _ => [] end.
  Definition task_mass (g : prepared) task :=
    match task with WtoExpand _ _ _ c => 3 * length c | WtoClose _ => 1 end.
  Definition potential g st :=
    fold_right (fun task n => task_mass g task + n) 0 (wto_tasks st).
  Definition initial g roots :=
    let r := wto_components g roots in
    WtoState (wto_expand_tasks None (wto_entries g roots r) (comp r) (rev (comps r))) WNil [].
  Definition advance g st :=
    match wto_step g st with inl next => next | inr _ => st end.
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
  Definition check_work g roots (w : wto) :=
    N.of_nat ((graph_n (base g) + graph_e (base g) + length roots + 1) *
      (graph_max (graph_width (base g)) (vertex_width roots) + 1)).

  Fixpoint history_from (g : prepared) (fuel : nat) (st : wto_state) : list wto_state :=
    match wto_step g st with
    | inr _ => [st]
    | inl next =>
      match fuel with
      | O => [st]
      | S remaining => st :: history_from g remaining next
      end
    end.
  Definition history (g : prepared) (roots : list positive) : list wto_state :=
    history_from g (3 * length (concat (comps (wto_components g roots))) + 1)
      (initial g roots).

  Lemma F1_lists :
    (forall v vs, wto_member v vs = true <-> In v vs) /\
    (forall vs, wto_unique vs = true <-> NoDup vs).
  Proof. Admitted. (* STUB *)

  Lemma F2_annotation : forall w, NoDup (wto_order w) ->
    map fst (wto_annotate [] w) = wto_order w /\
    forall u stack, In (u, stack) (wto_annotate [] w) ->
      forall h, In h stack <-> wto_encloses h u w.
  Proof. Admitted. (* STUB *)

  Lemma F3_index : forall w, NoDup (wto_order w) -> index_correct w.
  Proof. Admitted. (* STUB *)

  Lemma F4_check : forall g roots w, check g roots w = true <-> checked g roots w.
  Proof. Admitted. (* STUB *)

  Lemma F5_live : forall g roots v, In v (live g roots) <-> reach (base g) roots v.
  Proof. Admitted. (* STUB *)

  Lemma F6_sound : forall g roots w, check g roots w = true -> is_wto g roots w.
  Proof. Admitted. (* STUB *)

  Lemma F7_encloses : forall w h v,
    wto_encloses h v w -> In h (wto_heads w) /\ In h (wto_order w).
  Proof. Admitted. (* STUB *)

  Lemma F8_cycle : forall g roots w,
    is_wto g roots w -> forall vs, cycle (base g) vs ->
    (forall v, In v vs -> reach (base g) roots v) ->
    exists h, In h vs /\ In h (wto_heads w).
  Proof. Admitted. (* STUB *)

  Lemma F9_ranks : forall w,
    ranks w = wto_rank_rows 1%positive (wto_order w) /\
    (forall v, ~ In v (wto_order w) -> trie_get v (ranks w) = None) /\
    (NoDup (wto_order w) -> forall v i,
      nth_error (wto_order w) i = Some v ->
      trie_get v (ranks w) = Some (Pos.of_succ_nat i)).
  Proof. Admitted. (* STUB *)

  Lemma F10_forward : forall g roots w u v,
    check g roots w = true -> edge (base g) u v -> reach (base g) roots u ->
    exists ru rv, trie_get u (ranks w) = Some ru /\ trie_get v (ranks w) = Some rv /\
      ((ru < rv)%positive \/ (In v (heads w) /\ (rv <= ru)%positive)).
  Proof. Admitted. (* STUB *)

  Lemma F11_select : forall preferred c h body,
    wto_select preferred c = Some (h, body) -> Permutation c (h :: body).
  Proof. Admitted. (* STUB *)

  Lemma F12_scope : forall g vs,
    nodes (wto_scoped g (Some vs)) = vs /\
    forall v, In v vs -> succs (base (wto_scoped g (Some vs))) v =
      filter (fun u => wto_member u vs) (succs (base g) v).
  Proof. Admitted. (* STUB *)

  Lemma F13_partition : forall g body,
    NoDup body ->
    let r := wto_components (wto_scoped g (Some body)) (rev body) in
    Permutation (concat (comps r)) body /\
    fold_right (fun c n => source_mass g c + n) 0 (comps r) = source_mass g body.
  Proof. Admitted. (* STUB *)

  Lemma F14_initial : forall g roots,
    invariant g roots (initial g roots) /\
    potential g (initial g roots) = 3 * length (concat (comps (wto_components g roots))).
  Proof. Admitted. (* STUB *)

  Lemma F15_step : forall g roots st next,
    invariant g roots st -> wto_step g st = inl next ->
    invariant g roots next /\ potential g next < potential g st.
  Proof. Admitted. (* STUB *)

  Lemma F16_done : forall g roots,
    exists w, loopN (wto_step g)
      (N.of_nat (3 * length (concat (comps (wto_components g roots))) + 1))
      (initial g roots) = inr w.
  Proof. Admitted. (* STUB *)

  Lemma F17_history : forall g roots,
    exists terminal prefix, history g roots = prefix ++ [terminal] /\
      (match prefix with [] => terminal | first :: _ => first end) = initial g roots /\
      Forall2 (fun before after => wto_step g before = inl after)
        prefix (tl (history g roots)) /\
      wto_step g terminal = inr (build g roots).
  Proof. Admitted. (* STUB *)

  Lemma F18_level_mass : forall g roots level,
    level_mass g level (history g roots) <=
      source_mass g (concat (comps (wto_components g roots))).
  Proof. Admitted. (* STUB *)

  Lemma F19_depth : forall g roots st within entries owners c tasks,
    In st (history g roots) ->
    wto_tasks st = WtoExpand within entries owners c :: tasks ->
    length (wto_parents st) <= wto_depth (build g roots).
  Proof. Admitted. (* STUB *)

  Lemma T1_member : forall v vs,
    (T_wto_member v vs <= k_member * N.of_nat (length vs + 1) *
      N.of_nat (graph_max (Pos.size_nat v) (vertex_width vs) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T3_scope : forall g vs,
    (T_wto_scoped g (Some vs) <= k_scope * N.of_nat (scope_work g vs))%N.
  Proof. Admitted. (* STUB *)

  (** The index loop checks each key's width and listing before it reads a trie. *)
  Lemma T4a_index : forall g w,
    (T_wto_check_index (check_fuel g) (graph_width (base g)) (listed_of g)
      [WtoCheckVisit w] 0 Empty Empty [] <=
    k_index * N.of_nat (graph_n (base g) + 1) * N.of_nat (graph_width (base g) + 1))%N.
  Proof. Admitted. (* STUB *)

  (** An index result lists distinct listed vertices. *)
  Lemma F4a_index : forall g w ranks intervals vs,
    wto_check_index (check_fuel g) (graph_width (base g)) (listed_of g)
      [WtoCheckVisit w] 0 Empty Empty [] = Some (ranks, intervals, vs) ->
    NoDup vs /\ (forall v, In v vs -> In v (nodes g)).
  Proof. Admitted. (* STUB *)

  (** The edge scan is the final conjunct of the checker. *)
  Lemma F4b_edges : forall b ranks intervals vs,
    wto_edges_ok b ranks intervals vs =
      forallb (fun u => forallb (wto_interval_edge ranks intervals u) (succs b u)) vs.
  Proof. Admitted. (* STUB *)

  (** The edge scan reads the rows of distinct listed vertices once each. *)
  Lemma T4b_edges : forall g w ranks intervals vs,
    wto_check_index (check_fuel g) (graph_width (base g)) (listed_of g)
      [WtoCheckVisit w] 0 Empty Empty [] = Some (ranks, intervals, vs) ->
    (T_wto_edges_ok (base g) ranks intervals vs <=
     k_check * N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
       N.of_nat (graph_width (base g) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T5_check_public : forall g roots w,
    (T_check g roots w <= c_wto *
      N.of_nat (graph_n (base g) + graph_e (base g) + length roots + 1) *
      N.of_nat (graph_max (graph_width (base g)) (vertex_width roots) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T6_expand : forall g within entries owners c tasks partial parents h body,
    wto_select (wto_preferred owners entries c) c = Some (h, body) -> body <> [] ->
    (T_wto_step g (WtoState (WtoExpand within entries owners c :: tasks) partial parents) <=
      k_expand * (T_wto_preferred owners entries c +
        T_wto_select (wto_preferred owners entries c) c + T_wto_scoped g (Some body) +
        T_wto_components (wto_scoped g (Some body)) (rev body) +
        T_wto_entries (wto_scoped g (Some body)) (rev body)
          (wto_components (wto_scoped g (Some body)) (rev body)) +
        N.of_nat (length body) + N.of_nat (length c) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T7_build_public : forall g roots,
    (T_build g roots <= c_wto * N.of_nat (graph_n (base g) + graph_e (base g) + length roots + 1) *
      N.of_nat (wto_depth (build g roots) + 1) *
      N.of_nat (graph_max (graph_width (base g)) (vertex_width roots) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T8_heads_source : forall w,
    (T_heads w <= k_heads * (T_wto_heads w + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T9_heads_public : forall w,
    (T_heads w <= c_wto * N.of_nat (length (wto_order w) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T10_ranks_source : forall w,
    (T_ranks w <= k_ranks *
      (T_wto_order w + T_wto_rank_rows 1%positive (wto_order w) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T11_ranks_public : forall w,
    (T_ranks w <= c_wto * N.of_nat (length (wto_order w) + 1) *
      N.of_nat (vertex_width (wto_order w) + Nat.log2 (length (wto_order w)) + 1))%N.
  Proof. Admitted. (* STUB *)
End WtoT.
