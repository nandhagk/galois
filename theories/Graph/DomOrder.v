(** * Low-high order construction

    The producer derives sibling sources and inserts children beside recorded anchors.
    For example, a join without a parent edge needs sibling sources on both sides.
    Builds on: the numeric Lengauer and Tarjan producer and binary-fuel loops. *)

From Stdlib Require Import List Bool PArith NArith Arith Lia.
From Argent Require Import Time Tactics Std.
From Galois.Base Require Import Trie Loop.
From Galois.Graph Require Import Data Spec DigraphSig DomSig DomProducer.
Import List.ListNotations.

Definition dom_order_row (rows : ptrie (list N)) (v : N) : list N :=
  match trie_get (dom_lt_key v) rows with None => [] | Some row => row end.
TimeFun dom_order_row.

Definition dom_order_number (rows : ptrie N) (v : N) : N :=
  match trie_get (dom_lt_key v) rows with None => 0%N | Some n => n end.
TimeFun dom_order_number.

Definition dom_order_child_add (parents : ptrie N) (rows : ptrie (list N)) (v : N)
    : ptrie (list N) :=
  match trie_get (dom_lt_key v) parents with
  | None => rows
  | Some p => PTrieCode.set (dom_lt_key p) (v :: dom_order_row rows p) rows
  end.
TimeFun dom_order_child_add.

Inductive dom_order_task :=
  | DomOrderEnter (v : N)
  | DomOrderLeave (v : N).

Record dom_order_walk := DomOrderWalk {
  order_tasks : list dom_order_task;
  order_pre : ptrie N;
  order_post : ptrie N;
  order_clock : N
}.
TimeFun order_tasks.
TimeFun order_pre.
TimeFun order_post.
TimeFun order_clock.

Definition dom_order_number_step (rows : ptrie (list N)) (st : dom_order_walk)
    : dom_order_walk + dom_order_walk :=
  match order_tasks st with
  | [] => inr st
  | DomOrderLeave v :: tasks =>
    inl (DomOrderWalk tasks (order_pre st)
      (PTrieCode.set (dom_lt_key v) (N.pred (order_clock st)) (order_post st)) (order_clock st))
  | DomOrderEnter v :: tasks =>
    match trie_get (dom_lt_key v) (order_pre st) with
    | Some _ => inl (DomOrderWalk tasks (order_pre st) (order_post st) (order_clock st))
    | None => inl (DomOrderWalk
        (map DomOrderEnter (dom_order_row rows v) ++ DomOrderLeave v :: tasks)
        (PTrieCode.set (dom_lt_key v) (order_clock st) (order_pre st))
        (order_post st) (N.succ (order_clock st)))
    end
  end.
TimeFun dom_order_number_step.

Definition dom_order_number_tree (limit : N) (rows : ptrie (list N)) : dom_order_walk :=
  let initial := DomOrderWalk [DomOrderEnter 1%N] Empty Empty 0%N in
  match loopN (dom_order_number_step rows) (N.double limit + limit + 3)%N initial with
  | inl st | inr st => st
  end.
TimeFun dom_order_number_tree.

Inductive dom_child_index :=
  | DomChildEmpty
  | DomChildNode (child position : N) (lower upper : dom_child_index).

Fixpoint dom_order_half (n : nat) : nat :=
  match n with O | S O => O | S (S rest) => S (dom_order_half rest) end.
TimeFun dom_order_half.

Fixpoint dom_order_split (n : nat) (vs : list N) : list N * list N :=
  match n, vs with
  | O, _ | _, [] => ([], vs)
  | S rest, v :: tail =>
    let '(prefix, suffix) := dom_order_split rest tail in (v :: prefix, suffix)
  end.
TimeFun dom_order_split.

Fixpoint dom_order_index_build (fuel : nat) (pre : ptrie N) (vs : list N) : dom_child_index :=
  match fuel, vs with
  | O, _ | _, [] => DomChildEmpty
  | S remaining, _ =>
    let '(lower, upper) := dom_order_split (dom_order_half (length vs)) vs in
    match upper with
    | [] => DomChildEmpty
    | v :: tail => DomChildNode v (dom_order_number pre v)
        (dom_order_index_build remaining pre lower) (dom_order_index_build remaining pre tail)
    end
  end.
TimeFun dom_order_index_build.

Definition dom_order_indexes (order : list N) (rows : ptrie (list N)) (pre : ptrie N)
    : ptrie dom_child_index :=
  fold_left (fun indexes v =>
    let children := dom_order_row rows v in
    PTrieCode.set (dom_lt_key v)
      (dom_order_index_build (N.size_nat (N.of_nat (length children))) pre children) indexes)
    order Empty.
TimeFun dom_order_indexes.

Fixpoint dom_order_index_search (position : N) (index : dom_child_index) : option N :=
  match index with
  | DomChildEmpty => None
  | DomChildNode child start lower upper =>
    if N.ltb position start then dom_order_index_search position lower else
      match dom_order_index_search position upper with None => Some child | Some v => Some v end
  end.
TimeFun dom_order_index_search.

Definition dom_order_derived (indexes : ptrie dom_child_index) (walk : dom_order_walk)
    (parent source : N) : N :=
  if N.eqb parent source then parent else
    match trie_get (dom_lt_key parent) indexes, trie_get (dom_lt_key source) (order_pre walk) with
    | Some index, Some position =>
      match dom_order_index_search position index with
      | None => parent
      | Some child =>
        if N.leb position (dom_order_number (order_post walk) child) then child else parent
      end
    | _, _ => parent
    end.
TimeFun dom_order_derived.

Record dom_order_sources := DomOrderSources {
  source_blue : ptrie N;
  source_red : ptrie N;
  source_colour : ptrie bool
}.
TimeFun source_blue.
TimeFun source_red.
TimeFun source_colour.

Definition dom_order_colour (numeric : dom_lt_numeric) (semis minimizer relative parents : ptrie N)
    (indexes : ptrie dom_child_index) (walk : dom_order_walk) (st : dom_order_sources) (v : N)
    : dom_order_sources :=
  let key := dom_lt_key v in
  match trie_get key parents with
  | None => st
  | Some p =>
    let relative_red := match trie_get (dom_lt_key (dom_lt_identity relative v))
        (source_colour st) with Some true => true | _ => false end in
    let blue := N.eqb (dom_lt_identity semis v) p || relative_red in
    let f := dom_lt_identity (lt_numeric_parent numeric) v in
    let g := dom_lt_identity minimizer v in
    let b := if blue then g else f in
    let red := if blue then f else g in
    let direct := existsb (N.eqb p) (dom_order_row (lt_numeric_pred numeric) v) in
    DomOrderSources
      (PTrieCode.set key (if direct then p else dom_order_derived indexes walk p b)
        (source_blue st))
      (PTrieCode.set key (if direct then p else dom_order_derived indexes walk p red)
        (source_red st))
      (PTrieCode.set key (negb blue) (source_colour st))
  end.
TimeFun dom_order_colour.

Definition dom_order_source_maps (numeric : dom_lt_numeric) (semis minimizer relative parents
    : ptrie N) : dom_order_sources :=
  let rows := fold_left (dom_order_child_add parents) (lt_numeric_order numeric) Empty in
  let walk := dom_order_number_tree (lt_numeric_limit numeric) rows in
  let indexes := dom_order_indexes (lt_numeric_order numeric) rows (order_pre walk) in
  fold_left (dom_order_colour numeric semis minimizer relative parents indexes walk)
    (rev_append (lt_numeric_order numeric) []) (DomOrderSources Empty Empty Empty).
TimeFun dom_order_source_maps.

Record dom_source_tree := DomSourceTree {
  source_parent : ptrie N;
  source_children : ptrie (list N);
  source_count : ptrie N
}.
TimeFun source_parent.
TimeFun source_children.
TimeFun source_count.

Definition dom_source_add (tree : dom_source_tree) (v source parent : N) : dom_source_tree :=
  let sources := PTrieCode.set (dom_lt_key v) source (source_parent tree) in
  if N.eqb source parent then DomSourceTree sources (source_children tree) (source_count tree)
  else DomSourceTree sources
    (PTrieCode.set (dom_lt_key source) (v :: dom_order_row (source_children tree) source)
      (source_children tree))
    (PTrieCode.set (dom_lt_key source) (N.succ (dom_order_number (source_count tree) source))
      (source_count tree)).
TimeFun dom_source_add.

Definition dom_source_initial (parents sources : ptrie N) (order : list N) : dom_source_tree :=
  fold_left (fun tree v => match trie_get (dom_lt_key v) parents with
    | None => tree
    | Some p => dom_source_add tree v (dom_lt_identity sources v) p
    end) order (DomSourceTree Empty Empty Empty).
TimeFun dom_source_initial.

Definition dom_source_remove (tree : dom_source_tree) (v parent : N) : dom_source_tree :=
  let source := dom_lt_identity (source_parent tree) v in
  if N.eqb source parent then tree else
    DomSourceTree (source_parent tree) (source_children tree)
      (PTrieCode.set (dom_lt_key source) (N.pred (dom_order_number (source_count tree) source))
        (source_count tree)).
TimeFun dom_source_remove.

Definition dom_source_redirect (tree : dom_source_tree) (v source parent : N)
    : dom_source_tree :=
  dom_source_add (dom_source_remove tree v parent) v source parent.
TimeFun dom_source_redirect.

Definition dom_order_active (active : ptrie bool) (v : N) : bool :=
  match trie_get (dom_lt_key v) active with Some true => true | _ => false end.
TimeFun dom_order_active.

(** Stale inverse entries are inspected only when their source is removed. *)
Fixpoint dom_source_child (sources : ptrie N) (active : ptrie bool) (source : N)
    (row : list N) : option N :=
  match row with
  | [] => None
  | v :: rest =>
    if dom_order_active active v && N.eqb (dom_lt_identity sources v) source then Some v
    else dom_source_child sources active source rest
  end.
TimeFun dom_source_child.

Fixpoint dom_order_fallback (active : ptrie bool) (remaining : list N) : option (N * list N) :=
  match remaining with
  | [] => None
  | v :: rest =>
    if dom_order_active active v then Some (v, rest) else dom_order_fallback active rest
  end.
TimeFun dom_order_fallback.

Record dom_order_removal_state := DomOrderRemovalState {
  removal_blue : dom_source_tree;
  removal_red : dom_source_tree;
  removal_active : ptrie bool;
  removal_queue : list N;
  removal_fallback : list N;
  removal_records : list (N * N * N)
}.
TimeFun removal_blue.
TimeFun removal_red.
TimeFun removal_active.
TimeFun removal_queue.
TimeFun removal_fallback.
TimeFun removal_records.

Definition dom_order_remove_step (parents : ptrie N) (st : dom_order_removal_state)
    : dom_order_removal_state + list (N * N * N) :=
  match removal_queue st with
  | [] =>
    match dom_order_fallback (removal_active st) (removal_fallback st) with
    | None => inr (removal_records st)
    | Some (v, remaining) =>
      let p := dom_lt_identity parents v in
      inl (DomOrderRemovalState (removal_blue st) (removal_red st)
        (PTrieCode.set (dom_lt_key v) false (removal_active st)) [] remaining
        ((v, p, p) :: removal_records st))
    end
  | v :: queue =>
    let blue := removal_blue st in
    let red := removal_red st in
    let popped := DomOrderRemovalState blue red (removal_active st) queue
      (removal_fallback st) (removal_records st) in
    if dom_order_active (removal_active st) v then
      let b := dom_lt_identity (source_parent blue) v in
      let r := dom_lt_identity (source_parent red) v in
      let nb := dom_order_number (source_count blue) v in
      let nr := dom_order_number (source_count red) v in
      let distinct := if N.eqb b r then 1%N else 2%N in
      if N.ltb (N.add nb nr) distinct then
        let p := dom_lt_identity parents v in
        let red_leaf := N.eqb nr 0%N in
        let anchor := if red_leaf then b else r in
        let witness := if red_leaf then r else b in
        let source_tree := if red_leaf then blue else red in
        let child := dom_source_child (source_parent source_tree) (removal_active st) v
          (dom_order_row (source_children source_tree) v) in
        let blue := dom_source_remove blue v p in
        let red := dom_source_remove red v p in
        let blue := match child with
          | Some w => if red_leaf then dom_source_redirect blue w anchor p else blue
          | None => blue
          end in
        let red := match child with
          | Some w => if red_leaf then red else dom_source_redirect red w anchor p
          | None => red
          end in
        let queue := anchor :: witness ::
          match child with None => queue | Some w => w :: queue end in
        inl (DomOrderRemovalState blue red
          (PTrieCode.set (dom_lt_key v) false (removal_active st)) queue (removal_fallback st)
          ((v, anchor, witness) :: removal_records st))
      else inl popped
    else inl popped
  end.
TimeFun dom_order_remove_step.

Definition dom_order_removal (limit : N) (parents : ptrie N) (order : list N)
    (sources : dom_order_sources) : list (N * N * N) :=
  let children := filter (fun v => match trie_get (dom_lt_key v) parents with
    | None => false | Some _ => true end) order in
  let active := fold_left (fun active v => PTrieCode.set (dom_lt_key v) true active)
    children Empty in
  let initial := DomOrderRemovalState
    (dom_source_initial parents (source_blue sources) children)
    (dom_source_initial parents (source_red sources) children) active children children [] in
  match loopN (dom_order_remove_step parents)
      (N.double (N.double (N.double (N.double limit))) + 3)%N initial with
  | inr removed => removed
  | inl st => removal_records st
  end.
TimeFun dom_order_removal.

Definition dom_anchor_size (sizes : ptrie N) (v : N) : N :=
  match trie_get (dom_lt_key v) sizes with None => 1%N | Some n => n end.
TimeFun dom_anchor_size.

Definition dom_anchor_sizes (parents : ptrie N) (removed : list (N * N * N)) : ptrie N :=
  fold_left (fun sizes entry =>
    let '(v, anchor, _) := entry in
    let own := dom_anchor_size sizes v in
    let sizes := PTrieCode.set (dom_lt_key v) own sizes in
    if N.eqb anchor (dom_lt_identity parents v) then sizes else
      PTrieCode.set (dom_lt_key anchor) (N.add own (dom_anchor_size sizes anchor)) sizes)
    (rev_append removed []) Empty.
TimeFun dom_anchor_sizes.

Definition dom_anchor_capacity (parents sizes : ptrie N) (removed : list (N * N * N))
    : ptrie N :=
  fold_left (fun caps entry =>
    let '(v, anchor, _) := entry in
    let p := dom_lt_identity parents v in
    if N.eqb anchor p then PTrieCode.set (dom_lt_key p)
      (N.add (dom_order_number caps p) (dom_anchor_size sizes v)) caps else caps) removed Empty.
TimeFun dom_anchor_capacity.

Record dom_anchor_state := DomAnchorState {
  anchor_intervals : ptrie (N * N);
  anchor_free : ptrie (N * N)
}.
TimeFun anchor_intervals.
TimeFun anchor_free.

Definition dom_anchor_start (intervals : ptrie (N * N)) (v : N) : N :=
  match trie_get (dom_lt_key v) intervals with None => 0%N | Some (lo, _) => lo end.
TimeFun dom_anchor_start.

Definition dom_anchor_at_parent (caps : ptrie N) (st : dom_anchor_state)
    (v p size : N) : dom_anchor_state :=
  let '(lo, hi) := match trie_get (dom_lt_key p) (anchor_free st) with
    | Some bounds => bounds
    | None => (0%N, N.pred (dom_order_number caps p))
    end in
  DomAnchorState (PTrieCode.set (dom_lt_key v) (lo, N.pred (N.add lo size)) (anchor_intervals st))
    (PTrieCode.set (dom_lt_key p) (N.add lo size, hi) (anchor_free st)).
TimeFun dom_anchor_at_parent.

Definition dom_anchor_insert (parents sizes caps : ptrie N) (st : dom_anchor_state)
    (entry : N * N * N) : dom_anchor_state :=
  let '(v, anchor, witness) := entry in
  let p := dom_lt_identity parents v in
  let size := dom_anchor_size sizes v in
  if N.eqb anchor p then dom_anchor_at_parent caps st v p size else
    match trie_get (dom_lt_key anchor) (anchor_intervals st) with
    | None => dom_anchor_at_parent caps st v p size
    | Some (lo, hi) =>
      let witness_before := N.ltb (dom_anchor_start (anchor_intervals st) witness) lo in
      let '(own, rest) := if witness_before then
          ((lo, N.pred (N.add lo size)), (N.add lo size, hi))
        else ((N.sub (N.succ hi) size, hi), (lo, N.sub hi size)) in
      DomAnchorState
        (PTrieCode.set (dom_lt_key v) own
          (PTrieCode.set (dom_lt_key anchor) rest (anchor_intervals st))) (anchor_free st)
    end.
TimeFun dom_anchor_insert.

Definition dom_anchor_order (parents : ptrie N) (removed : list (N * N * N))
    : ptrie (N * N) :=
  let sizes := dom_anchor_sizes parents removed in
  let caps := dom_anchor_capacity parents sizes removed in
  anchor_intervals (fold_left (dom_anchor_insert parents sizes caps) removed
    (DomAnchorState Empty Empty)).
TimeFun dom_anchor_order.

Record dom_order_merge_state := DomOrderMergeState {
  merge_lower : list N;
  merge_upper : list N;
  merge_reverse : list N
}.
TimeFun merge_lower.
TimeFun merge_upper.
TimeFun merge_reverse.

Definition dom_order_merge_step (positions : ptrie (N * N)) (st : dom_order_merge_state)
    : dom_order_merge_state + list N :=
  match merge_lower st, merge_upper st with
  | [], ys => inr (rev_append (merge_reverse st) ys)
  | xs, [] => inr (rev_append (merge_reverse st) xs)
  | x :: xt, y :: yt =>
    if N.leb (dom_anchor_start positions x) (dom_anchor_start positions y)
    then inl (DomOrderMergeState xt (merge_upper st) (x :: merge_reverse st))
    else inl (DomOrderMergeState (merge_lower st) yt (y :: merge_reverse st))
  end.
TimeFun dom_order_merge_step.

Definition dom_order_merge (positions : ptrie (N * N)) (xs ys : list N) : list N :=
  match loopN (dom_order_merge_step positions) (N.of_nat (length xs + length ys + 1))
      (DomOrderMergeState xs ys []) with
  | inr vs => vs
  | inl st => rev_append (merge_reverse st) (merge_lower st ++ merge_upper st)
  end.
TimeFun dom_order_merge.


Fixpoint dom_order_sort (fuel : nat) (positions : ptrie (N * N)) (vs : list N) : list N :=
  match fuel, vs with
  | O, _ | _, [] | _, [_] => vs
  | S remaining, _ =>
    let '(lower, upper) := dom_order_split (dom_order_half (length vs)) vs in
    dom_order_merge positions (dom_order_sort remaining positions lower)
      (dom_order_sort remaining positions upper)
  end.
TimeFun dom_order_sort.

Definition dom_order_sorted_rows (order : list N) (parents : ptrie N)
    (positions : ptrie (N * N)) : ptrie (list N) :=
  let rows := fold_left (dom_order_child_add parents) order Empty in
  PTrieCode.map (fun row => dom_order_sort (N.size_nat (N.of_nat (length row))) positions row) rows.
TimeFun dom_order_sorted_rows.

Record dom_order_emit_state := DomOrderEmitState {
  emit_pending : list N;
  emit_seen : ptrie bool;
  emit_reverse : list positive
}.
TimeFun emit_pending.
TimeFun emit_seen.
TimeFun emit_reverse.

Definition dom_order_emit_step (vertices : ptrie positive) (rows : ptrie (list N))
    (st : dom_order_emit_state) : dom_order_emit_state + list positive :=
  match emit_pending st with
  | [] => inr (rev_append (emit_reverse st) [])
  | v :: remaining =>
    if dom_order_active (emit_seen st) v then
      inl (DomOrderEmitState remaining (emit_seen st) (emit_reverse st))
    else
      let emitted := match trie_get (dom_lt_key v) vertices with
        | None => emit_reverse st
        | Some vertex => vertex :: emit_reverse st
        end in
      inl (DomOrderEmitState (dom_order_row rows v ++ remaining)
        (PTrieCode.set (dom_lt_key v) true (emit_seen st)) emitted)
  end.
TimeFun dom_order_emit_step.

Definition dom_order_emit (numeric : dom_lt_numeric) (rows : ptrie (list N)) : list positive :=
  match loopN (dom_order_emit_step (lt_numeric_vertex numeric) rows)
      (N.double (lt_numeric_limit numeric) + 3)%N (DomOrderEmitState [1%N] Empty []) with
  | inr order => order
  | inl st => rev_append (emit_reverse st) []
  end.
TimeFun dom_order_emit.

Record dom_lt_result := DomLtResult {
  result_numeric : dom_lt_numeric;
  result_semi : dom_lt_semi_state;
  result_bucket : dom_lt_bucket_state;
  result_parent : ptrie N
}.
TimeFun result_numeric.
TimeFun result_semi.
TimeFun result_bucket.
TimeFun result_parent.

Definition dom_lt_pipeline (g : prepared) (r : positive) : dom_lt_result :=
  let numeric := dom_lt_numeric_of g r in
  let semi := dom_lt_semidominators numeric in
  let bucket := dom_lt_buckets numeric (lt_semis semi) in
  DomLtResult numeric semi bucket (dom_lt_correct numeric (lt_semis semi) (lt_relative bucket)).
TimeFun dom_lt_pipeline.

Definition dom_order_of_result (result : dom_lt_result) : list positive :=
  let numeric := result_numeric result in
  let semi := result_semi result in
  let bucket := result_bucket result in
  let parents := result_parent result in
  let sources := dom_order_source_maps numeric (lt_semis semi) (lt_minimizer semi)
    (lt_relative bucket) parents in
  let removed := dom_order_removal (lt_numeric_limit numeric) parents
    (lt_numeric_order numeric) sources in
  let positions := dom_anchor_order parents removed in
  dom_order_emit numeric (dom_order_sorted_rows (lt_numeric_order numeric) parents positions).
TimeFun dom_order_of_result.

Definition dom_build_candidate (g : prepared) (r : positive) : ptrie positive * list positive :=
  let result := dom_lt_pipeline g r in
  (dom_lt_erase (result_numeric result) (result_parent result), dom_order_of_result result).
TimeFun dom_build_candidate.

Definition dom_build_order (g : prepared) (r : positive) : list positive :=
  dom_order_of_result (dom_lt_pipeline g r).
TimeFun dom_build_order.

Definition dom_lt_ops (g : prepared) (r : positive) : list lt_op :=
  let result := dom_lt_pipeline g r in
  rev_append (lt_operations (lt_semi_links (result_semi result)))
    (rev_append (lt_operations (lt_bucket_links (result_bucket result))) []).
TimeFun dom_lt_ops.

Record dom_lt_replay := DomLtReplay {
  replay_links : dom_lt_links;
  replay_semis : ptrie N;
  replay_fuel : N;
  replay_boundary : N;
  replay_index : N
}.
TimeFun replay_links.
TimeFun replay_semis.
TimeFun replay_fuel.
TimeFun replay_boundary.
TimeFun replay_index.

(** The bucket phase starts a fresh forest after the semidominator operation prefix. *)
Definition dom_lt_replay_step (st : dom_lt_replay) (op : lt_op) : dom_lt_replay :=
  let links := if N.eqb (replay_index st) (replay_boundary st)
    then DomLtLinks Empty Empty [] else replay_links st in
  let links := match op with
    | LtLink child parent => dom_lt_link links child parent
    | LtEval v => fst (dom_lt_eval (replay_fuel st) (replay_semis st) links v)
    end in
  DomLtReplay links (replay_semis st) (replay_fuel st) (replay_boundary st)
    (N.succ (replay_index st)).
TimeFun dom_lt_replay_step.

Definition dom_lt_replay_initial (g : prepared) (r : positive) : dom_lt_replay :=
  let result := dom_lt_pipeline g r in
  DomLtReplay (DomLtLinks Empty Empty []) (lt_semis (result_semi result))
    (lt_numeric_limit (result_numeric result))
    (N.of_nat (length (lt_operations (lt_semi_links (result_semi result))))) 0%N.
TimeFun dom_lt_replay_initial.

Definition dom_lt_run_ops (ops : list lt_op) (st : dom_lt_replay) : dom_lt_replay :=
  fold_left dom_lt_replay_step ops st.
TimeFun dom_lt_run_ops.

(** Discovery and predecessor inventories imply the public linear operation-count budget. *)
Lemma dom_lt_operation_count_budget vertices edges discovered predecessors :
  discovered <= vertices -> discovered <= edges + 1 -> predecessors <= edges ->
  (discovered + predecessors) + 2 * discovered <= 2 * (vertices + edges) + 1.
Proof.
  lia.
Qed.

(** The two producer phases record at most the published number of links and evaluations. *)
Lemma dom_lt_operations_length g r :
  prepared_ok g ->
  length (dom_lt_ops g r) <= 2 * (graph_n (base g) + graph_e (base g)) + 1.
Proof.
  intro Hprepared.
  set (numeric := dom_lt_numeric_of g r).
  set (semi := dom_lt_semidominators numeric).
  set (bucket := dom_lt_buckets numeric (lt_semis semi)).
  pose proof (dom_lt_semidominators_operations numeric) as Hsemi.
  fold semi in Hsemi.
  pose proof (dom_lt_buckets_operations numeric (lt_semis semi)
    (dom_lt_numeric_order_unique g r)) as Hbucket.
  fold bucket in Hbucket.
  pose proof (dom_lt_numeric_pred_total g r Hprepared) as Hpredecessors.
  fold numeric in Hpredecessors.
  destruct (dom_lt_dfs_inventory g r) as [_ [_ [Hvertices Hedges]]].
  rewrite <- (dom_lt_numeric_order_length g r) in Hvertices, Hedges.
  fold numeric in Hvertices, Hedges.
  unfold dom_lt_ops, dom_lt_pipeline.
  fold numeric. fold semi. fold bucket.
  change (length (rev_append (lt_operations (lt_semi_links semi))
    (rev_append (lt_operations (lt_bucket_links bucket)) [])) <=
      2 * (graph_n (base g) + graph_e (base g)) + 1).
  rewrite !rev_append_rev, !length_app, !length_rev. cbn [length].
  rewrite Nat.add_0_r.
  eapply Nat.le_trans.
  - apply Nat.add_le_mono; [exact Hsemi|exact Hbucket].
  - apply dom_lt_operation_count_budget; assumption.
Qed.

(** * Semantic consequences of a low-high certificate *)

(** The first occurrence supplies a natural measure for certificate proofs. *)
Fixpoint dom_cert_position (o : list positive) (v : positive) : nat :=
  match o with
  | [] => 0
  | u :: rest => if Pos.eqb v u then 0 else S (dom_cert_position rest v)
  end.
TimeFun dom_cert_position.

Lemma dom_cert_position_nth o : NoDup o ->
  forall i v, nth_error o i = Some v -> dom_cert_position o v = i.
Proof.
  intro Hunique. induction Hunique as [|u rest Hfresh Hunique IH]; intros i v Hnth.
  - destruct i; discriminate.
  - destruct i as [|i].
    + cbn in Hnth. injection Hnth as <-. cbn [dom_cert_position].
      now rewrite Pos.eqb_refl.
    + cbn in Hnth. cbn [dom_cert_position].
      destruct (Pos.eqb v u) eqn:Heq.
      * apply Pos.eqb_eq in Heq. subst v. exfalso. apply Hfresh.
        eapply nth_error_In. exact Hnth.
      * f_equal. now apply IH.
Qed.

Lemma dom_cert_position_bound o v : NoDup o -> In v o ->
  dom_cert_position o v < length o.
Proof.
  intros Hunique Hin. apply In_nth_error in Hin as [i Hnth].
  rewrite (dom_cert_position_nth o Hunique i v Hnth).
  apply nth_error_Some. rewrite Hnth. discriminate.
Qed.

Lemma dom_cert_before_positions o u v : NoDup o ->
  order_before o u v -> dom_cert_position o u < dom_cert_position o v.
Proof.
  intros Hunique [i [j [Hi [Hj Hlt]]]].
  rewrite (dom_cert_position_nth o Hunique i u Hi).
  rewrite (dom_cert_position_nth o Hunique j v Hj). exact Hlt.
Qed.

Lemma dom_cert_positions_before o u v : NoDup o -> In u o -> In v o ->
  dom_cert_position o u < dom_cert_position o v -> order_before o u v.
Proof.
  intros Hunique Hu Hv Hlt.
  apply In_nth_error in Hu as [i Hi]. apply In_nth_error in Hv as [j Hj].
  exists i, j. repeat split; try assumption.
  rewrite (dom_cert_position_nth o Hunique i u Hi) in Hlt.
  rewrite (dom_cert_position_nth o Hunique j v Hj) in Hlt. exact Hlt.
Qed.

Lemma dom_cert_before_members o u v : order_before o u v -> In u o /\ In v o.
Proof.
  intros [i [j [Hi [Hj Hlt]]]]. split; eapply nth_error_In; eassumption.
Qed.

Lemma dom_cert_before_trans o u v w : NoDup o ->
  order_before o u v -> order_before o v w -> order_before o u w.
Proof.
  intros Hunique Huv Hvw.
  destruct (dom_cert_before_members o u v Huv) as [Hu Hv].
  destruct (dom_cert_before_members o v w Hvw) as [_ Hw].
  apply dom_cert_positions_before; try assumption.
  pose proof (dom_cert_before_positions o u v Hunique Huv).
  pose proof (dom_cert_before_positions o v w Hunique Hvw). lia.
Qed.

Lemma dom_cert_parent_before g r m o v p : dom_cert g r m o ->
  trie_get v m = Some p -> order_before o p v.
Proof.
  intros [Hpre Hremaining] Hget.
  destruct Hpre as [Hunique [Hhead [Hroot [Hparent [Hdomain Hinterval]]]]].
  assert (Hv : In v o) by (eapply Hdomain; exact Hget).
  assert (Hne : v <> r) by (intro Heq; subst v; congruence).
  destruct (Hparent v Hv Hne) as [q [Hq Hbefore]].
  rewrite Hget in Hq. injection Hq as <-. exact Hbefore.
Qed.

Lemma dom_cert_anc_cases m u v : tree_anc m u v ->
  u = v \/ exists p, trie_get v m = Some p /\ tree_anc m u p.
Proof.
  intro Hanc. destruct Hanc as [|p v Hparent Hanc].
  - now left.
  - right. exists p. auto.
Qed.

Lemma dom_cert_anc_trans m u v w : tree_anc m u v -> tree_anc m v w -> tree_anc m u w.
Proof.
  intros Huv Hvw. induction Hvw as [|p w Hparent Hanc IH].
  - exact Huv.
  - eapply tree_anc_step; eassumption.
Qed.

(** Every strict ancestor precedes its descendant in the certificate order. *)
Lemma dom_cert_anc_before g r m o u v : dom_cert g r m o ->
  tree_anc m u v -> u <> v -> order_before o u v.
Proof.
  intros Hcert Hanc. induction Hanc as [|p v Hparent Hanc IH]; intro Hne.
  - contradiction.
  - pose proof (dom_cert_parent_before g r m o v p Hcert Hparent) as Hpv.
    destruct (Pos.eq_dec u p) as [Heq|Hup].
    + now subst u.
    + eapply dom_cert_before_trans; [exact (proj1 (proj1 Hcert))| |exact Hpv].
      exact (IH Hup).
Qed.

Lemma dom_cert_anc_antisym g r m o u v : dom_cert g r m o ->
  tree_anc m u v -> tree_anc m v u -> u = v.
Proof.
  intros Hcert Huv Hvu. destruct (Pos.eq_dec u v) as [Heq|Hne]; [exact Heq|].
  pose proof (dom_cert_anc_before g r m o u v Hcert Huv Hne) as Hbefore.
  pose proof (dom_cert_anc_before g r m o v u Hcert Hvu ltac:(congruence)) as Hafter.
  apply (dom_cert_before_positions o u v (proj1 (proj1 Hcert))) in Hbefore.
  apply (dom_cert_before_positions o v u (proj1 (proj1 Hcert))) in Hafter. lia.
Qed.

(** Following a parent always decreases the finite certificate position. *)
Lemma dom_cert_parent_wf g r m o : dom_cert g r m o ->
  well_founded (fun u v => trie_get v m = Some u).
Proof.
  intro Hcert. apply (well_founded_lt_compat positive (dom_cert_position o)).
  intros v p Hparent. apply dom_cert_before_positions.
  - exact (proj1 (proj1 Hcert)).
  - eapply dom_cert_parent_before; eassumption.
Qed.

(** The root reaches every listed vertex through candidate parent links. *)
Lemma dom_cert_root_anc g r m o v : dom_cert g r m o -> In v o -> tree_anc m r v.
Proof.
  intro Hcert. induction v as [v IH] using
    (well_founded_induction (dom_cert_parent_wf g r m o Hcert)).
  intro Hv. destruct (Pos.eq_dec v r) as [Heq|Hne].
  - subst v. constructor.
  - destruct Hcert as [Hpre Hremaining].
    destruct Hpre as [Hunique [Hhead [Hroot [Hparent [Hdomain Hinterval]]]]].
    destruct (Hparent v Hv Hne) as [p [Hget Hbefore]].
    eapply tree_anc_step; [exact Hget|].
    apply (IH p Hget). exact (proj1 (dom_cert_before_members o p v Hbefore)).
Qed.

Lemma dom_cert_root_listed g r m o : dom_cert g r m o -> In r o.
Proof.
  intros [[Hunique [Hhead Hrest]] Hmore].
  destruct o as [|v rest]; [discriminate|]. cbn in Hhead.
  injection Hhead as <-. now left.
Qed.

Lemma dom_cert_path_listed g r m o a vs b : dom_cert g r m o ->
  In a o -> path g a vs b -> In b o.
Proof.
  intros Hcert Ha Hpath. revert Ha.
  induction Hpath as [v|u v vs w Hedge Hpath IH]; intro Ha.
  - exact Ha.
  - apply IH. exact (proj1 (proj1 (proj2 Hcert) u v Ha Hedge)).
Qed.

(** The parent certificate keeps every root-reachable vertex in its order. *)
Lemma dom_cert_reach_listed g r m o v : dom_cert g r m o ->
  reach g [r] v -> In v o.
Proof.
  intros Hcert [a [vs [Ha Hpath]]]. destruct Ha as [<-|Ha]; [|contradiction].
  eapply dom_cert_path_listed; [exact Hcert| |exact Hpath].
  eapply dom_cert_root_listed. exact Hcert.
Qed.

Lemma dom_cert_path_start g a vs b : path g a vs b -> In a vs.
Proof.
  intro Hpath. destruct Hpath; now left.
Qed.

Lemma dom_cert_path_end g a vs b : path g a vs b -> In b vs.
Proof.
  intro Hpath. induction Hpath; [now left|now right].
Qed.

Lemma dom_cert_path_snoc g a vs b c : path g a vs b -> edge g b c ->
  path g a (vs ++ [c]) c.
Proof.
  intros Hpath Hedge. induction Hpath as [v|u v vs w Hfirst Hpath IH].
  - cbn. eapply path_step; [exact Hedge|constructor].
  - cbn. eapply path_step; [exact Hfirst|now apply IH].
Qed.

Lemma dom_cert_path_join g a xs b ys c : path g a xs b -> path g b ys c ->
  exists zs, path g a zs c /\ forall v, In v zs -> In v xs \/ In v ys.
Proof.
  intros Hleft Hright. revert ys c Hright.
  induction Hleft as [b|a v xs b Hedge Hpath IH]; intros ys c Hright.
  - exists ys. split; [exact Hright|]. intros v Hv. now right.
  - destruct (IH ys c Hright) as [zs [Hz Hmembers]].
    exists (a :: zs). split.
    + eapply path_step; eassumption.
    + intros y [<-|Hy]; [left; now left|].
      destruct (Hmembers y Hy) as [Hin|Hin]; [left; now right|now right].
Qed.

Lemma dom_cert_positions_eq o u v : NoDup o -> In u o -> In v o ->
  dom_cert_position o u = dom_cert_position o v -> u = v.
Proof.
  intros Hunique Hu Hv Heq.
  apply In_nth_error in Hu as [i Hi]. apply In_nth_error in Hv as [j Hj].
  rewrite (dom_cert_position_nth o Hunique i u Hi) in Heq.
  rewrite (dom_cert_position_nth o Hunique j v Hj) in Heq. subst j. congruence.
Qed.

Lemma dom_cert_anc_listed g r m o u v : dom_cert g r m o ->
  tree_anc m u v -> In v o -> In u o.
Proof.
  intros Hcert Hanc Hv. destruct (Pos.eq_dec u v) as [->|Hne]; [exact Hv|].
  apply (dom_cert_anc_before g r m o u v Hcert Hanc) in Hne.
  exact (proj1 (dom_cert_before_members o u v Hne)).
Qed.

Lemma dom_cert_anc_parent m u v p : trie_get v m = Some p -> tree_anc m u v ->
  u <> v -> tree_anc m u p.
Proof.
  intros Hget Hanc Hne. apply dom_cert_anc_cases in Hanc.
  destruct Hanc as [Heq|[q [Hq Hanc]]]; [contradiction|].
  rewrite Hget in Hq. injection Hq as <-. exact Hanc.
Qed.

Lemma dom_cert_path_anc g r m o a vs b : dom_cert g r m o ->
  In a o -> path g a vs b -> forall u, tree_anc m u b ->
  tree_anc m u a \/ In u vs.
Proof.
  intros Hcert Ha Hpath. revert Ha.
  induction Hpath as [v|a v vs b Hedge Hpath IH]; intros Ha u Hanc.
  - now left.
  - destruct (proj1 (proj2 Hcert) a v Ha Hedge) as [Hv Hparents].
    destruct (IH Hv u Hanc) as [Huv|Hin]; [|right; now right].
    destruct (Pos.eq_dec u v) as [Heq|Hne].
    + subst u. right. right. eapply dom_cert_path_start. exact Hpath.
    + destruct (dom_cert_anc_cases m u v Huv) as [Heq|[p [Hget Hup]]];
        [contradiction|].
      left. eapply dom_cert_anc_trans; [exact Hup|]. now apply Hparents.
Qed.

(** The parent property forces every candidate ancestor onto every root path. *)
Lemma dom_cert_anc_dominates g r m o u v : dom_cert g r m o ->
  In v o -> tree_anc m u v -> dominates g r u v.
Proof.
  intros Hcert Hv Hanc vs Hpath.
  destruct (dom_cert_path_anc g r m o r vs v Hcert
    (dom_cert_root_listed g r m o Hcert) Hpath u Hanc) as [Hur|Hin]; [|exact Hin].
  destruct (dom_cert_anc_cases m u r Hur) as [Heq|[p [Hget Hup]]].
  - subst u. eapply dom_cert_path_start. exact Hpath.
  - pose proof (proj1 (proj2 (proj2 (proj1 Hcert)))) as Hroot. congruence.
Qed.

(** Well-founded parent links decide ancestry without an extra logical principle. *)
Lemma dom_cert_anc_dec g r m o u v : dom_cert g r m o ->
  tree_anc m u v \/ ~ tree_anc m u v.
Proof.
  intro Hcert. induction v as [v IH] using
    (well_founded_induction (dom_cert_parent_wf g r m o Hcert)).
  destruct (Pos.eq_dec u v) as [Heq|Hne].
  - subst u. left. constructor.
  - destruct (trie_get v m) as [p|] eqn:Hget.
    + destruct (IH p eq_refl) as [Hanc|Hnot].
      * left. eapply tree_anc_step; eassumption.
      * right. intro Hanc. apply Hnot. eapply dom_cert_anc_parent; eassumption.
    + right. intro Hanc. apply dom_cert_anc_cases in Hanc.
      destruct Hanc as [Heq|[p [Hp Hanc]]]; congruence.
Qed.

(** A low predecessor yields a root path containing no later vertex. *)
Lemma dom_cert_low_path g r m o v : dom_cert g r m o -> In v o ->
  exists vs, path g r vs v /\ forall y, In y vs -> y = v \/ order_before o y v.
Proof.
  intro Hcert. induction v as [v IH] using
    (well_founded_induction (well_founded_ltof positive (dom_cert_position o))).
  intro Hv. destruct (Pos.eq_dec v r) as [Heq|Hne].
  - subst v. exists [r]. split; [constructor|].
    intros y [<-|Hy]; [now left|contradiction].
  - pose proof (proj1 (proj1 Hcert)) as Hunique.
    destruct (proj2 (proj2 (proj2 (proj1 Hcert)))) as [Hparent Hrest].
    destruct (Hparent v Hv Hne) as [p [Hget Hpv]].
    assert (Hpredecessor : exists u, edge g u v /\ order_before o u v).
    { destruct (proj2 (proj2 Hcert) v p Hget) as [Hdirect|Hlow].
      - exists p. auto.
      - destruct Hlow as [u [w [Hu [Hw [Huv [Hwv [Hbefore Hafter]]]]]]].
        exists u. auto. }
    destruct Hpredecessor as [u [Hedge Hbefore]].
    destruct (dom_cert_before_members o u v Hbefore) as [Hu _].
    destruct (IH u (dom_cert_before_positions o u v Hunique Hbefore) Hu)
      as [vs [Hpath Hmembers]].
    exists (vs ++ [v]). split.
    + eapply dom_cert_path_snoc; eassumption.
    + intros y Hy. apply in_app_or in Hy. destruct Hy as [Hy|[<-|Hy]].
      * right. destruct (Hmembers y Hy) as [->|Hyv]; [exact Hbefore|].
        eapply dom_cert_before_trans; eassumption.
      * now left.
      * contradiction.
Qed.

(** Every listed vertex has a graph path from the root. *)
Lemma dom_cert_listed_reach g r m o v : dom_cert g r m o -> In v o -> reach g [r] v.
Proof.
  intros Hcert Hv. destruct (dom_cert_low_path g r m o v Hcert Hv) as [vs [Hpath Hmembers]].
  exists r, vs. split; [now left|exact Hpath].
Qed.

Lemma dom_cert_other_branch_after g r m o v p w x : dom_cert g r m o ->
  trie_get v m = Some p -> order_before o v w -> ~ tree_anc m v w ->
  tree_anc m p x -> tree_anc m x w -> x <> p -> order_before o v x.
Proof.
  intros Hcert Hget Hvw Hnot Hpx Hxw Hxp.
  destruct (proj1 Hcert) as [Hunique [Hhead [Hroot [Hparent [Hdomain Hinterval]]]]].
  destruct (dom_cert_before_members o v w Hvw) as [Hv Hw].
  pose proof (dom_cert_anc_listed g r m o x w Hcert Hxw Hw) as Hx.
  destruct (Nat.lt_trichotomy (dom_cert_position o x) (dom_cert_position o v))
    as [Hlt|[Heq|Hgt]].
  - assert (Hxv : order_before o x v) by (apply dom_cert_positions_before; assumption).
    assert (Hanc : tree_anc m x v) by (eapply Hinterval; eassumption).
    assert (Hxv_ne : x <> v).
    { intro Heq. subst x. lia. }
    pose proof (dom_cert_anc_parent m x v p Hget Hanc Hxv_ne) as Hxp_anc.
    exfalso. apply Hxp. eapply dom_cert_anc_antisym; eassumption.
  - assert (Heqv : x = v) by (eapply dom_cert_positions_eq; eassumption).
    subst x. contradiction.
  - apply dom_cert_positions_before; assumption.
Qed.

Lemma dom_cert_high_chain g r m o v p w : dom_cert g r m o ->
  trie_get v m = Some p -> order_before o v w -> ~ tree_anc m v w ->
  (forall x q, order_before o v x -> trie_get x m = Some q ->
    exists vs, path g q vs x /\
      forall y, In y vs -> y = q \/ y = x \/ order_before o x y) ->
  forall x, tree_anc m p x -> tree_anc m x w ->
    exists vs, path g p vs x /\ forall y, In y vs -> y = p \/ order_before o v y.
Proof.
  intros Hcert Hget Hvw Hnot Hlater x Hpx. induction Hpx as [|q x Hparent Hpq IH].
  - intros Hpw. exists [p]. split; [constructor|].
    intros y [<-|Hy]; [now left|contradiction].
  - intro Hxw. destruct (Pos.eq_dec x p) as [Heq|Hxp].
    + subst x. exists [p]. split; [constructor|].
      intros y [<-|Hy]; [now left|contradiction].
    + assert (Hpx : tree_anc m p x) by (eapply tree_anc_step; eassumption).
      pose proof (dom_cert_other_branch_after g r m o v p w x Hcert Hget Hvw
        Hnot Hpx Hxw Hxp) as Hvx.
      assert (Hqw : tree_anc m q w).
      { eapply dom_cert_anc_trans; [|exact Hxw].
        eapply tree_anc_step; [exact Hparent|constructor]. }
      destruct (IH Hqw) as [left [Hleft Hleft_members]].
      destruct (Hlater x q Hvx Hparent) as [right [Hright Hright_members]].
      destruct (dom_cert_path_join g p left q right x Hleft Hright)
        as [vs [Hpath Hmembers]].
      exists vs. split; [exact Hpath|]. intros y Hy.
      destruct (Hmembers y Hy) as [Hin|Hin].
      * exact (Hleft_members y Hin).
      * destruct (Hright_members y Hin) as [->|[->|Hxy]].
        -- apply Hleft_members. eapply dom_cert_path_end. exact Hleft.
        -- now right.
        -- right. eapply dom_cert_before_trans;
             [exact (proj1 (proj1 Hcert))|exact Hvx|exact Hxy].
Qed.

(** A high predecessor yields a parent path whose internal vertices follow the child. *)
Lemma dom_cert_high_path g r m o v p : dom_cert g r m o -> trie_get v m = Some p ->
  exists vs, path g p vs v /\
    forall y, In y vs -> y = p \/ y = v \/ order_before o v y.
Proof.
  intro Hcert. revert p. induction v as [v IH] using
    (well_founded_induction (well_founded_ltof positive
      (fun x => length o - dom_cert_position o x))).
  intros p Hget. destruct (proj2 (proj2 Hcert) v p Hget) as [Hdirect|Hlow].
  - exists [p; v]. split.
    + eapply path_step; [exact Hdirect|constructor].
    + intros y [<-|[<-|Hy]]; [now left|right; now left|contradiction].
  - destruct Hlow as [u [w [Hu [Hw [Huv [Hwv [Hbefore [Hafter Hnot]]]]]]]].
    assert (Hpw : tree_anc m p w).
    { apply (proj2 (proj1 (proj2 Hcert) w v Hw Hwv) p Hget). }
    assert (Hlater : forall x q, order_before o v x -> trie_get x m = Some q ->
      exists vs, path g q vs x /\
        forall y, In y vs -> y = q \/ y = x \/ order_before o x y).
    { intros x q Hvx Hxq. apply IH; [|exact Hxq].
      unfold ltof. pose proof (proj1 (proj1 Hcert)) as Hunique.
      pose proof (dom_cert_before_positions o v x Hunique Hvx) as Hposition.
      destruct (dom_cert_before_members o v x Hvx) as [Hv Hx].
      pose proof (dom_cert_position_bound o x Hunique Hx). lia. }
    destruct (dom_cert_high_chain g r m o v p w Hcert Hget Hafter Hnot Hlater
      w Hpw (tree_anc_refl m w)) as [vs [Hpath Hmembers]].
    exists (vs ++ [v]). split.
    + eapply dom_cert_path_snoc; eassumption.
    + intros y Hy. apply in_app_or in Hy. destruct Hy as [Hy|[<-|Hy]].
      * destruct (Hmembers y Hy) as [->|Hyv]; [now left|right; now right].
      * right. now left.
      * contradiction.
Qed.

(** A nonancestor is avoided by a root path assembled from low and high paths. *)
Lemma dom_cert_avoid g r m o x v : dom_cert g r m o -> In v o ->
  ~ tree_anc m x v -> exists vs, path g r vs v /\ ~ In x vs.
Proof.
  intro Hcert. induction v as [v IH] using
    (well_founded_induction (dom_cert_parent_wf g r m o Hcert)).
  intros Hv Hnot. destruct (Pos.eq_dec v r) as [Heq|Hvr].
  - subst v. exists [r]. split; [constructor|].
    intros [Heq|Hfalse]; [subst x; apply Hnot; constructor|contradiction].
  - pose proof (proj1 (proj1 Hcert)) as Hunique.
    destruct (in_dec Pos.eq_dec x o) as [Hx|Houtside].
    + assert (Hne : x <> v) by (intro Heq; subst x; apply Hnot; constructor).
      destruct (Nat.lt_trichotomy (dom_cert_position o x) (dom_cert_position o v))
        as [Hlt|[Heq|Hgt]].
      * destruct (proj2 (proj2 (proj2 (proj1 Hcert)))) as [Hparent Hrest].
        destruct (Hparent v Hv Hvr) as [p [Hget Hpv]].
        destruct (dom_cert_before_members o p v Hpv) as [Hp _].
        assert (Hnotp : ~ tree_anc m x p).
        { intro Hanc. apply Hnot. eapply tree_anc_step; eassumption. }
        destruct (IH p Hget Hp Hnotp) as [left [Hleft Havoid]].
        destruct (dom_cert_high_path g r m o v p Hcert Hget)
          as [right [Hright Hright_members]].
        destruct (dom_cert_path_join g r left p right v Hleft Hright)
          as [vs [Hpath Hmembers]].
        exists vs. split; [exact Hpath|]. intro Hin.
        destruct (Hmembers x Hin) as [Hinleft|Hinright]; [contradiction|].
        destruct (Hright_members x Hinright) as [Heq|[Heq|Hbefore]].
        -- subst x. apply Hnotp. constructor.
        -- contradiction.
        -- apply (dom_cert_before_positions o v x Hunique) in Hbefore. lia.
      * exfalso. apply Hne. eapply dom_cert_positions_eq; eassumption.
      * destruct (dom_cert_low_path g r m o v Hcert Hv) as [vs [Hpath Hmembers]].
        exists vs. split; [exact Hpath|]. intro Hin.
        destruct (Hmembers x Hin) as [Heq|Hbefore]; [contradiction|].
        apply (dom_cert_before_positions o x v Hunique) in Hbefore. lia.
    + destruct (dom_cert_low_path g r m o v Hcert Hv) as [vs [Hpath Hmembers]].
      exists vs. split; [exact Hpath|]. intro Hin. apply Houtside.
      destruct (Hmembers x Hin) as [->|Hbefore]; [exact Hv|].
      exact (proj1 (dom_cert_before_members o x v Hbefore)).
Qed.

(** Low-high witnesses exclude every semantic dominator outside the candidate ancestry. *)
Lemma dom_cert_dominates_anc g r m o x v : dom_cert g r m o ->
  In v o -> dominates g r x v -> tree_anc m x v.
Proof.
  intros Hcert Hv Hdom. destruct (dom_cert_anc_dec g r m o x v Hcert) as [Hanc|Hnot];
    [exact Hanc|].
  destruct (dom_cert_avoid g r m o x v Hcert Hv Hnot) as [vs [Hpath Havoid]].
  exfalso. apply Havoid. now apply Hdom.
Qed.

Lemma dom_cert_parent_immediate g r m o v p : dom_cert g r m o ->
  trie_get v m = Some p -> immediately_dominates g r p v.
Proof.
  intros Hcert Hget.
  pose proof (dom_cert_parent_before g r m o v p Hcert Hget) as Hpv.
  destruct (dom_cert_before_members o p v Hpv) as [Hp Hv].
  split.
  - split.
    + eapply dom_cert_anc_dominates; [exact Hcert|exact Hv|].
      eapply tree_anc_step; [exact Hget|constructor].
    + intro Heq. subst p.
      apply (dom_cert_before_positions o v v (proj1 (proj1 Hcert))) in Hpv. lia.
  - intros x [Hdom Hne].
    pose proof (dom_cert_dominates_anc g r m o x v Hcert Hv Hdom) as Hanc.
    eapply dom_cert_anc_dominates; [exact Hcert|exact Hp|].
    eapply dom_cert_anc_parent; eassumption.
Qed.

(** A low-high certificate makes the complete candidate parent map semantically exact. *)
Lemma dom_cert_exact g r m o : dom_cert (base g) r m o -> dom_exact g r m.
Proof.
  intro Hcert. split.
  - intros v p Hget.
    pose proof (dom_cert_parent_before (base g) r m o v p Hcert Hget) as Hpv.
    destruct (dom_cert_before_members o p v Hpv) as [Hp Hv].
    split; [eapply dom_cert_listed_reach; eassumption|].
    split; [eapply dom_cert_listed_reach; eassumption|].
    eapply dom_cert_parent_immediate; eassumption.
  - split.
    + intros v Hreach. pose proof (dom_cert_reach_listed (base g) r m o v Hcert Hreach)
        as Hv. split.
      * intros Hnone [x [Hdom Hne]].
        pose proof (dom_cert_dominates_anc (base g) r m o x v Hcert Hv Hdom) as Hanc.
        destruct (dom_cert_anc_cases m x v Hanc) as [Heq|[p [Hget Hxp]]]; congruence.
      * intro Hnot. destruct (trie_get v m) as [p|] eqn:Hget; [|reflexivity].
        exfalso. apply Hnot. exists p.
        exact (proj1 (dom_cert_parent_immediate (base g) r m o v p Hcert Hget)).
    + eapply dom_cert_parent_wf. exact Hcert.
Qed.

(** Sharing the producer result costs no more than the separate parent and order phases. *)
Lemma T_dom_build_candidate_phases g r :
  (T_dom_build_candidate g r <= T_dom_lt_parents g r + T_dom_build_order g r + 32)%N.
Proof.
  unfold T_dom_build_candidate, T_dom_lt_parents, T_dom_build_order, T_dom_lt_pipeline.
  time_simpl. time_cbn. lia.
Qed.

Lemma dom_sem_path_prefix g a vs b : path g a vs b ->
  forall y, In y vs -> exists prefix, path g a prefix y /\ incl prefix vs.
Proof.
  intro Hpath. induction Hpath as [v|u v vs w Huv Hpath IH]; intros y Hin.
  - destruct Hin as [<-|Hin]; [|contradiction].
    exists [v]. split; [constructor|intros z Hz; exact Hz].
  - destruct Hin as [<-|Hin].
    + exists [u]. split; [constructor|].
      intros z [<-|Hz]; [now left|contradiction].
    + destruct (IH y Hin) as [prefix [Hprefix Hincl]].
      exists (u :: prefix). split.
      * eapply path_step; eassumption.
      * intros z [<-|Hz]; [now left|right; now apply Hincl].
Qed.

(** Dominance is transitive because a path prefix witnesses the intermediate target. *)
Lemma dom_sem_dominates_trans g r x y v :
  dominates g r x y -> dominates g r y v -> dominates g r x v.
Proof.
  intros Hxy Hyv vs Hpath.
  destruct (dom_sem_path_prefix g r vs v Hpath y (Hyv vs Hpath)) as
    [prefix [Hprefix Hincl]].
  apply Hincl. exact (Hxy prefix Hprefix).
Qed.

Lemma dom_map_no_return m v : Acc (fun u v => trie_get v m = Some u) v ->
  forall u, trie_get u m = Some v -> ~ tree_anc m u v.
Proof.
  intro Hacc. induction Hacc as [v Hacc IH]. intros u Huv Hanc.
  destruct (dom_cert_anc_cases m u v Hanc) as [Heq|[p [Hvp Hup]]].
  - subst u. apply (IH v Huv v Huv). constructor.
  - apply (IH p Hvp v Hvp). eapply dom_cert_anc_trans; [|exact Hup].
    eapply tree_anc_step; [exact Huv|constructor].
Qed.

(** Parent ancestry in any exact map implies semantic dominance. *)
Lemma dom_exact_anc_dominates g r m x v : dom_exact g r m ->
  tree_anc m x v -> dominates (base g) r x v.
Proof.
  intros Hexact Hanc. induction Hanc as [|p v Hparent Hanc IH].
  - intros vs Hpath. eapply dom_cert_path_end. exact Hpath.
  - destruct (proj1 Hexact v p Hparent) as [_ [_ [[Hdom Hne] Himmediate]]].
    eapply dom_sem_dominates_trans; eassumption.
Qed.

(** A semantic dominator of a reachable vertex occurs in its exact parent ancestry. *)
Lemma dom_exact_dominates_anc g r m x v : dom_exact g r m ->
  reach (base g) [r] v -> dominates (base g) r x v -> tree_anc m x v.
Proof.
  intros [Hparents [Hnone Hwf]]. revert x.
  induction v as [v IH] using (well_founded_induction Hwf).
  intros x Hreach Hdom. destruct (Pos.eq_dec x v) as [Heq|Hne].
  - subst x. constructor.
  - destruct (trie_get v m) as [p|] eqn:Hget.
    + destruct (Hparents v p Hget) as [Hp [_ [Hstrict Himmediate]]].
      eapply tree_anc_step; [exact Hget|].
      apply (IH p eq_refl x Hp). apply Himmediate. split; assumption.
    + exfalso. apply (proj1 (Hnone v Hreach) Hget). exists x. split; assumption.
Qed.

(** An exact map identifies dominance with its parent ancestry on reachable targets. *)
Lemma dom_exact_ancestry g r m x v : dom_exact g r m -> reach (base g) [r] v ->
  (tree_anc m x v <-> dominates (base g) r x v).
Proof.
  intros Hexact Hreach. split.
  - eapply dom_exact_anc_dominates. exact Hexact.
  - eapply dom_exact_dominates_anc; eassumption.
Qed.

(** Strict dominators of a child are exactly the ancestors of its exact parent. *)
Lemma dom_exact_parent_strict g r m x v p : dom_exact g r m ->
  trie_get v m = Some p ->
  (strictly_dominates (base g) r x v <-> tree_anc m x p).
Proof.
  intros Hexact Hget.
  destruct (proj1 Hexact v p Hget) as [Hp [Hv [[Hpv Hpv_ne] Himmediate]]].
  split.
  - intros [Hdom Hne]. eapply dom_cert_anc_parent; [exact Hget| |exact Hne].
    eapply dom_exact_dominates_anc; eassumption.
  - intro Hanc. split.
    + eapply dom_sem_dominates_trans; [|exact Hpv].
      eapply dom_exact_anc_dominates; eassumption.
    + intro Heq. subst x.
      eapply (dom_map_no_return m p (proj2 (proj2 Hexact) p) v Hget). exact Hanc.
Qed.

(** Every reachable predecessor lies below the target's exact parent. *)
Lemma dom_exact_edge_parent g r m p y b : dom_exact g r m -> reach (base g) [r] p ->
  edge (base g) p y -> trie_get y m = Some b -> tree_anc m b p.
Proof.
  intros Hexact Hp Hedge Hget.
  destruct (proj1 Hexact y b Hget) as [_ [_ [[Hdom Hne] Himmediate]]].
  apply (dom_exact_dominates_anc g r m b p Hexact Hp).
  intros vs Hpath.
  pose proof (Hdom (vs ++ [y]) (dom_cert_path_snoc (base g) r vs p y Hpath Hedge)) as Hin.
  apply in_app_or in Hin. destruct Hin as [Hin|[Heq|Hin]].
  - exact Hin.
  - congruence.
  - contradiction.
Qed.

(** Two ancestors of one vertex are comparable along its unique parent chain. *)
Lemma dom_anc_chain_comparable m a b v : tree_anc m a v -> tree_anc m b v ->
  tree_anc m a b \/ tree_anc m b a.
Proof.
  intro Ha. induction Ha as [|p v Hvp Hap IH]; intro Hb.
  - now right.
  - destruct (dom_cert_anc_cases m b v Hb) as [Heq|[q [Hvq Hbq]]].
    + subst b. left. eapply tree_anc_step; eassumption.
    + rewrite Hvp in Hvq. injection Hvq as <-. now apply IH.
Qed.

(** An acyclic parent map has antisymmetric ancestry. *)
Lemma dom_anc_wf_antisym m :
  well_founded (fun u v => trie_get v m = Some u) ->
  forall a b, tree_anc m a b -> tree_anc m b a -> a = b.
Proof.
  intros Hwf a b Hab Hba.
  destruct (dom_cert_anc_cases m b a Hba) as [Heq|[p [Hparent Hbp]]].
  - symmetry. exact Heq.
  - exfalso. apply (dom_map_no_return m p (Hwf p) a Hparent).
    eapply dom_cert_anc_trans; eassumption.
Qed.

(** Distinct positive keys fit strictly below the capacity of their maximum bit width. *)
Lemma dom_distinct_keys_cardinality xs w : NoDup xs ->
  (forall v, In v xs -> Pos.size_nat v <= w) -> length xs < Nat.pow 2 w.
Proof.
  intros Hunique Hwidth.
  assert (Hcodes : NoDup (map Pos.to_nat xs)).
  { clear Hwidth. induction Hunique as [|v xs Hfresh Hunique IH].
    - constructor.
    - cbn [map]. constructor; [|exact IH].
      intro Hin. apply in_map_iff in Hin as [u [Heq Hin]].
      apply Pos2Nat.inj in Heq. subst u. exact (Hfresh Hin). }
  assert (Hrange : incl (map Pos.to_nat xs) (seq 1 (Nat.pow 2 w - 1))).
  { intros code Hin. apply in_map_iff in Hin as [v [<- Hin]].
    apply in_seq.
    pose proof (Pos2Nat.is_pos v) as Hpositive.
    pose proof (Pos.size_nat_upper v) as Hupper.
    pose proof (Nat.pow_le_mono_r 2 _ _ ltac:(lia) (Hwidth v Hin)) as Hpow.
    pose proof (Nat.pow_lower_bound 2 w ltac:(lia)) as Hnonzero. lia. }
  pose proof (NoDup_incl_length Hcodes Hrange) as Hlength.
  rewrite length_map, length_seq in Hlength.
  pose proof (Nat.pow_lower_bound 2 w ltac:(lia)) as Hnonzero. lia.
Qed.

(** Values bounded by a distinct key count fit within those keys' width. *)
Lemma dom_distinct_value_width xs w a : NoDup xs ->
  (forall v, In v xs -> Pos.size_nat v <= w) ->
  (a <= N.of_nat (length xs))%N -> N.size_nat a <= w.
Proof.
  intros Hunique Hwidth Hvalue.
  pose proof (dom_distinct_keys_cardinality xs w Hunique Hwidth) as Hlength.
  destruct a as [|p]; [cbn; lia|].
  assert (Hnatural : N.to_nat (N.pos p) <= length xs) by lia.
  cbn [N.to_nat] in Hnatural. apply Pos.size_nat_least. lia.
Qed.

(** Twice a distinct key count plus one needs at most one additional bit. *)
Lemma dom_distinct_twice_width xs w a : NoDup xs ->
  (forall v, In v xs -> Pos.size_nat v <= w) ->
  (a <= 2 * N.of_nat (length xs) + 1)%N -> N.size_nat a <= w + 1.
Proof.
  intros Hunique Hwidth Hvalue.
  pose proof (dom_distinct_keys_cardinality xs w Hunique Hwidth) as Hlength.
  destruct a as [|p]; [cbn; lia|].
  assert (Hnatural : N.to_nat (N.pos p) <= 2 * length xs + 1) by lia.
  cbn [N.to_nat] in Hnatural. apply Pos.size_nat_least.
  rewrite Nat.add_1_r, Nat.pow_succ_r'. nia.
Qed.

(** * Primitive numeric costs for the producer *)

(** Encoding a numeric rank as a positive trie key adds at most one bit. *)
Lemma dom_lt_key_width rank :
  Pos.size_nat (dom_lt_key rank) <= N.size_nat rank + 1.
Proof.
  unfold dom_lt_key. destruct rank as [|p]; [reflexivity|].
  cbn [N.succ_pos N.size_nat]. induction p as [p IH|p IH|];
    cbn [Pos.succ Pos.size_nat] in *; lia.
Qed.

(** Numeric-key encoding costs at most its input width plus two calls. *)
Lemma dom_lt_time_key rank :
  (T_dom_lt_key rank <= N.of_nat (N.size_nat rank) + 2)%N.
Proof.
  pose proof (N.T_succ_pos_le rank) as Hsucc.
  time_unfold T_dom_lt_key. lia.
Qed.

(** Identity-default lookup costs only the numeric key's bit width. *)
Lemma dom_lt_time_identity table rank :
  (T_dom_lt_identity table rank <= 8 * N.of_nat (N.size_nat rank + 1))%N.
Proof.
  pose proof (dom_lt_time_key rank) as Hkey.
  pose proof (dom_lt_key_width rank) as Hwidth.
  unfold T_dom_lt_identity. rewrite PTrieT.trie_get_clock.
  destruct (trie_get (dom_lt_key rank) table); time_simpl;
    rewrite !Nat2N.inj_add in *; lia.
Qed.

(** Numeric comparison inspects at most the left operand's bit width. *)
Lemma dom_lt_time_ltb left right :
  (N.T_ltb left right <= N.of_nat (N.size_nat left) + 3)%N.
Proof.
  pose proof (N.T_compare_le left right) as Hcompare.
  time_unfold N.T_ltb. destruct (N.compare left right); lia.
Qed.

(** Linking writes two cells whose keys share the child's bounded bit width. *)
Lemma dom_lt_time_link width before child parent : N.size_nat child <= width ->
  (T_dom_lt_link before child parent <=
    64 * (PTrieT.c_trie + 1) * N.of_nat (width + 1))%N.
Proof.
  intro Hwidth.
  pose proof (dom_lt_key_width child) as Hkey_width.
  pose proof (dom_lt_time_key child) as Hkey_time.
  pose proof (PTrieT.T_set_le N (dom_lt_key child) parent (lt_shortcut before)) as Hshort.
  pose proof (PTrieT.T_set_le N (dom_lt_key child) child (lt_label before)) as Hlabel.
  change (PTrieCode.T_set (dom_lt_key child) parent (lt_shortcut before) <=
    PTrieT.c_trie * N.of_nat (Pos.size_nat (dom_lt_key child) + 1))%N in Hshort.
  change (PTrieCode.T_set (dom_lt_key child) child (lt_label before) <=
    PTrieT.c_trie * N.of_nat (Pos.size_nat (dom_lt_key child) + 1))%N in Hlabel.
  unfold T_dom_lt_link. time_simpl.
  clear -Hwidth Hkey_width Hkey_time Hshort Hlabel. rewrite !Nat2N.inj_add in *. nia.
Qed.

(** * Generated fold clocks *)

(** A fold telescopes credit while its invariant tracks the unprocessed operation suffix. *)
Lemma dom_lt_fold_credit {A B : Type} (step : A -> B -> A) (T_step : A -> B -> N)
    (Inv : list B -> A -> Prop) (credit : A -> N) (charge : N) ops :
  (forall op rest st, Inv (op :: rest) st -> Inv rest (step st op)) ->
  (forall op rest st, Inv (op :: rest) st ->
    (T_step st op + credit (step st op) <= credit st + charge)%N) ->
  forall st, Inv ops st ->
  Inv [] (fold_left step ops st) /\
    (List.T_fold_left step T_step ops st + credit (fold_left step ops st) <=
      credit st + (charge + 1) * N.of_nat (length ops) + 1)%N.
Proof.
  intros Hpreserve Hcost. induction ops as [|op rest IH]; intros st Hinv.
  - split; [exact Hinv|]. time_unfold @List.T_fold_left. cbn [fold_left length]. nia.
  - pose proof (Hcost op rest st Hinv) as Hhead.
    destruct (IH (step st op) (Hpreserve op rest st Hinv)) as [Hfinal Htail].
    split; [exact Hfinal|]. time_unfold @List.T_fold_left.
    cbn [fold_left length]. fold (List.T_fold_left step T_step).
    rewrite Nat2N.inj_succ. clear -Hhead Htail. nia.
Qed.

(** The generated list clock counts the empty call once for each separately run segment. *)
Lemma dom_lt_fold_clock_app {A B : Type} (step : A -> B -> A) (T_step : A -> B -> N)
    xs ys : forall st,
  (List.T_fold_left step T_step (xs ++ ys) st + 1 =
    List.T_fold_left step T_step xs st +
      List.T_fold_left step T_step ys (fold_left step xs st))%N.
Proof.
  induction xs as [|head tail IH]; intro st.
  - cbn [app fold_left]. time_unfold @List.T_fold_left. nia.
  - cbn [app]. time_unfold @List.T_fold_left. cbn [fold_left].
    fold (List.T_fold_left step T_step).
    pose proof (IH (step st head)) as Htail. lia.
Qed.

(** * Numeric ranges through semidominator settlement *)

Definition dom_lt_links_bounded (bound : N) (links : dom_lt_links) : Prop :=
  dom_lt_trie_all (fun value => (value <= bound)%N) (lt_shortcut links) /\
  dom_lt_trie_all (fun value => (value <= bound)%N) (lt_label links).

Definition dom_lt_walk_bounded (bound : N) (st : dom_lt_walk) : Prop :=
  dom_lt_links_bounded bound (lt_walk_links st) /\
  match lt_walk_phase st with
  | DomLtDescend vertex stack =>
      (vertex <= bound)%N /\ Forall (fun value => (value <= bound)%N) stack
  | DomLtUnwind root part stack =>
      (root <= bound)%N /\
      (match part with None => True | Some value => (value <= bound)%N end) /\
      Forall (fun value => (value <= bound)%N) stack
  end.

(** Selecting one of two labels preserves their common numeric bound. *)
Lemma dom_lt_minimum_bounded bound semis left right :
  (left <= bound)%N -> (right <= bound)%N -> (dom_lt_minimum semis left right <= bound)%N.
Proof.
  intros Hleft Hright. unfold dom_lt_minimum.
  destruct (N.ltb (dom_lt_identity semis right) (dom_lt_identity semis left)); assumption.
Qed.

(** A link preserves payload bounds when its child and parent lie in the same range. *)
Lemma dom_lt_link_bounded bound before vertex parent :
  dom_lt_links_bounded bound before -> (vertex <= bound)%N -> (parent <= bound)%N ->
  dom_lt_links_bounded bound (dom_lt_link before vertex parent).
Proof.
  intros [Hshort Hlabels] Hvertex Hparent.
  unfold dom_lt_links_bounded, dom_lt_link. cbn [lt_shortcut lt_label]. split;
    apply dom_lt_trie_all_set; assumption.
Qed.

(** Each compression transition preserves bounded frames, shortcuts and labels. *)
Lemma dom_lt_compress_bounded bound semis st : dom_lt_walk_bounded bound st ->
  match dom_lt_compress_step semis st with
  | inl next => dom_lt_walk_bounded bound next
  | inr result => dom_lt_links_bounded bound (fst result) /\ (snd result <= bound)%N
  end.
Proof.
  destruct st as [links [vertex stack|root part stack]].
  - cbn [dom_lt_walk_bounded lt_walk_phase lt_walk_links].
    intros [[Hshort Hlabels] [Hvertex Hstack]].
    cbn [dom_lt_compress_step lt_walk_phase lt_walk_links].
    destruct (trie_get (dom_lt_key vertex) (lt_shortcut links)) as [parent|] eqn:Hget.
    + pose proof (Hshort (dom_lt_key vertex) parent Hget) as Hparent.
      destruct (N.ltb parent vertex).
      * split; [split; assumption|]. split; [exact Hparent|]. now constructor.
      * split; [split; assumption|]. repeat split; assumption.
    + split; [split; assumption|]. repeat split; assumption.
  - cbn [dom_lt_walk_bounded lt_walk_phase lt_walk_links].
    intros [[Hshort Hlabels] [Hroot [Hpart Hstack]]].
    destruct stack as [|vertex stack].
    + cbn [dom_lt_compress_step lt_walk_phase lt_walk_links fst snd].
      split; [split; assumption|]. destruct part; assumption.
    + inversion Hstack as [|head tail Hvertex Htail]; subst head tail.
      set (label := dom_lt_identity (lt_label links) vertex).
      set (best := match part with None => label |
        Some previous => dom_lt_minimum semis label previous end).
      assert (Hlabel : (label <= bound)%N).
      { unfold label. now apply dom_lt_identity_bounded. }
      assert (Hbest : (best <= bound)%N).
      { unfold best. destruct part as [previous|]; [|exact Hlabel].
        now apply dom_lt_minimum_bounded. }
      change (dom_lt_walk_bounded bound
        (DomLtWalk (DomLtLinks
          (PTrieCode.set (dom_lt_key vertex) root (lt_shortcut links))
          (PTrieCode.set (dom_lt_key vertex) best (lt_label links)) (lt_operations links))
          (DomLtUnwind root (Some best) stack))).
      split.
      * split; apply dom_lt_trie_all_set; assumption.
      * repeat split; assumption.
Qed.

(** Evaluation preserves payload support even when the supplied binary fuel is exhausted. *)
Lemma dom_lt_eval_bounded bound fuel semis before vertex :
  dom_lt_links_bounded bound before -> (vertex <= bound)%N ->
  dom_lt_links_bounded bound (fst (dom_lt_eval fuel semis before vertex)) /\
    (snd (dom_lt_eval fuel semis before vertex) <= bound)%N.
Proof.
  intros Hlinks Hvertex.
  set (initial := DomLtWalk
    (DomLtLinks (lt_shortcut before) (lt_label before) (LtEval vertex :: lt_operations before))
    (DomLtDescend vertex [])).
  assert (Hinitial : dom_lt_walk_bounded bound initial).
  { unfold initial. split; [exact Hlinks|]. split; [exact Hvertex|constructor]. }
  pose proof (dom_lt_loop_invariant (dom_lt_compress_step semis)
    (dom_lt_walk_bounded bound)
    (fun result => dom_lt_links_bounded bound (fst result) /\ (snd result <= bound)%N)
    (N.double fuel + 3)%N initial) as Hrun.
  assert (Hgo : forall st next, dom_lt_walk_bounded bound st ->
    dom_lt_compress_step semis st = inl next -> dom_lt_walk_bounded bound next).
  { intros st next Hinv Hstep. pose proof (dom_lt_compress_bounded bound semis st Hinv) as Hnext.
    now rewrite Hstep in Hnext. }
  assert (Hstop : forall st result, dom_lt_walk_bounded bound st ->
    dom_lt_compress_step semis st = inr result ->
    dom_lt_links_bounded bound (fst result) /\ (snd result <= bound)%N).
  { intros st result Hinv Hstep.
    pose proof (dom_lt_compress_bounded bound semis st Hinv) as Hnext.
    now rewrite Hstep in Hnext. }
  specialize (Hrun Hgo Hstop Hinitial).
  unfold dom_lt_eval. fold initial.
  destruct (loopN (dom_lt_compress_step semis) (N.double fuel + 3)%N initial)
    as [state|result].
  - split; [exact (proj1 Hrun)|exact Hvertex].
  - exact Hrun.
Qed.

(** A fold preserves its invariant when every input satisfies the callback's guard. *)
Lemma dom_lt_fold_guarded {A B : Type} (step : A -> B -> A) (Inv : A -> Prop)
    (Guard : B -> Prop) xs :
  (forall state value, Inv state -> Guard value -> Inv (step state value)) ->
  Forall Guard xs -> forall initial, Inv initial -> Inv (fold_left step xs initial).
Proof.
  intros Hstep Hxs. induction Hxs as [|value rest Hvalue Hrest IH]; intros initial Hinitial.
  - exact Hinitial.
  - cbn [fold_left]. apply IH. now apply Hstep.
Qed.

Definition dom_lt_predecessor_bounded (bound : N) (acc : dom_lt_links * N * N) : Prop :=
  dom_lt_links_bounded bound (fst (fst acc)) /\
    (snd (fst acc) <= bound)%N /\ (snd acc <= bound)%N.

(** A predecessor evaluation keeps its forest, best score and witness in range. *)
Lemma dom_lt_predecessor_range bound limit semis acc source :
  dom_lt_trie_all (fun value => (value <= bound)%N) semis ->
  dom_lt_predecessor_bounded bound acc -> (source <= bound)%N ->
  dom_lt_predecessor_bounded bound (dom_lt_predecessor limit semis acc source).
Proof.
  intros Hsemis Hacc Hsource. destruct acc as [[links best] witness].
  destruct Hacc as [Hlinks [Hbest Hwitness]].
  pose proof (dom_lt_eval_bounded bound limit semis links source Hlinks Hsource) as Heval.
  unfold dom_lt_predecessor. destruct (dom_lt_eval limit semis links source)
    as [after chosen]. cbn [fst snd] in Heval.
  destruct Heval as [Hafter Hchosen].
  pose proof (dom_lt_identity_bounded bound semis chosen Hsemis Hchosen) as Hcandidate.
  destruct (N.ltb (dom_lt_identity semis chosen) best);
    (split; [exact Hafter|split; assumption]).
Qed.

Definition dom_lt_semi_bounded (bound : N) (st : dom_lt_semi_state) : Prop :=
  dom_lt_trie_all (fun value => (value <= bound)%N) (lt_semis st) /\
  dom_lt_trie_all (fun value => (value <= bound)%N) (lt_minimizer st) /\
  dom_lt_links_bounded bound (lt_semi_links st).

(** Settling one bounded vertex preserves all semidominator-state payload bounds. *)
Lemma dom_lt_settle_range bound numeric before vertex :
  dom_lt_numeric_ranges bound numeric -> dom_lt_semi_bounded bound before ->
  (vertex <= bound)%N -> dom_lt_semi_bounded bound (dom_lt_settle numeric before vertex).
Proof.
  intros [Horder Hparents Hpreds] [Hsemis [Hmin Hlinks]] Hvertex.
  unfold dom_lt_settle.
  destruct (trie_get (dom_lt_key vertex) (lt_numeric_parent numeric)) as [parent|] eqn:Hget.
  2: { split; [exact Hsemis|]. split; assumption. }
  pose proof (Hparents (dom_lt_key vertex) parent Hget) as Hparent.
  set (incoming := match trie_get (dom_lt_key vertex) (lt_numeric_pred numeric) with
    None => [] | Some row => row end).
  assert (Hincoming : Forall (fun value => (value <= bound)%N) incoming).
  { unfold incoming. destruct (trie_get (dom_lt_key vertex) (lt_numeric_pred numeric))
      as [row|] eqn:Hrow; [now apply (Hpreds (dom_lt_key vertex))|constructor]. }
  pose proof (dom_lt_fold_guarded (dom_lt_predecessor (lt_numeric_limit numeric) (lt_semis before))
    (dom_lt_predecessor_bounded bound) (fun value => (value <= bound)%N) incoming
    (fun state value Hstate Hvalue =>
      dom_lt_predecessor_range bound (lt_numeric_limit numeric) (lt_semis before)
        state value Hsemis Hstate Hvalue) Hincoming
    (lt_semi_links before, parent, parent)) as Hfold.
  assert (Hinitial : dom_lt_predecessor_bounded bound (lt_semi_links before, parent, parent)).
  { split; [exact Hlinks|]. now split. }
  specialize (Hfold Hinitial).
  destruct (fold_left (dom_lt_predecessor (lt_numeric_limit numeric) (lt_semis before))
    incoming (lt_semi_links before, parent, parent)) as [[after best] witness].
  destruct Hfold as [Hafter [Hbest Hwitness]].
  split; [apply dom_lt_trie_all_set; assumption|].
  split; [apply dom_lt_trie_all_set; assumption|]. now apply dom_lt_link_bounded.
Qed.

(** A bounded numeric layout produces a bounded semidominator state. *)
Lemma dom_lt_semidominators_range bound numeric : dom_lt_numeric_ranges bound numeric ->
  dom_lt_semi_bounded bound (dom_lt_semidominators numeric).
Proof.
  intro Hnumeric. unfold dom_lt_semidominators.
  apply (dom_lt_fold_guarded (dom_lt_settle numeric) (dom_lt_semi_bounded bound)
    (fun value => (value <= bound)%N) (lt_numeric_order numeric)).
  - intros state value Hstate Hvalue. now apply dom_lt_settle_range.
  - exact (dom_lt_numeric_order_range bound numeric Hnumeric).
  - repeat split; apply dom_lt_trie_all_empty.
Qed.

(** A fold preserves an accumulator invariant when each input satisfies its callback premise. *)
Lemma dom_lt_fold_forall {A B : Type} (step : A -> B -> A) (Inv : A -> Prop)
    (P : B -> Prop) xs st :
  Forall P xs -> Inv st ->
  (forall current x, Inv current -> P x -> Inv (step current x)) ->
  Inv (fold_left step xs st).
Proof.
  intros Hinputs Hinitial Hstep.
  exact (dom_lt_fold_guarded step Inv P xs Hstep Hinputs st Hinitial).
Qed.

(** Bucket insertion retains bounded row members regardless of its semidominator key. *)
Lemma dom_lt_bucket_add_range bound semis buckets v :
  dom_lt_trie_all (Forall (fun n => (n <= bound)%N)) buckets -> (v <= bound)%N ->
  dom_lt_trie_all (Forall (fun n => (n <= bound)%N)) (dom_lt_bucket_add semis buckets v).
Proof.
  intros Hrows Hv. unfold dom_lt_bucket_add.
  destruct (trie_get (dom_lt_key v) semis) as [s|]; [|exact Hrows].
  apply dom_lt_trie_all_set; [exact Hrows|]. constructor; [exact Hv|].
  destruct (trie_get (dom_lt_key s) buckets) as [row|] eqn:Hrow;
    [now apply (Hrows (dom_lt_key s))|constructor].
Qed.

(** Every bucket member comes from the bounded numeric traversal order. *)
Lemma dom_lt_bucket_build_range bound semis order :
  Forall (fun n => (n <= bound)%N) order ->
  dom_lt_trie_all (Forall (fun n => (n <= bound)%N))
    (fold_left (dom_lt_bucket_add semis) (rev_append order []) Empty).
Proof.
  intro Horder.
  apply (dom_lt_fold_forall (dom_lt_bucket_add semis)
    (dom_lt_trie_all (Forall (fun n => (n <= bound)%N))) (fun n => (n <= bound)%N)).
  - apply Forall_forall. intros v Hv. rewrite rev_append_rev, app_nil_r, <- in_rev in Hv.
    now apply (proj1 (Forall_forall _ _) Horder v).
  - apply dom_lt_trie_all_empty.
  - intros buckets v Hrows Hv. now apply dom_lt_bucket_add_range.
Qed.

Local Opaque dom_lt_eval T_dom_lt_eval.

(** * Producer work outside the evaluator and linker

    The generated evaluator and linker clocks retain coefficient one.
    The remaining work is charged to key widths and visited row occurrences. *)

(** A predecessor visit pays only its score lookup and comparison outside evaluation. *)
Lemma dom_lt_semi_predecessor_clock width limit semis links best witness source :
  let chosen := snd (dom_lt_eval limit semis links source) in
  N.size_nat chosen <= width ->
  N.size_nat (dom_lt_identity semis chosen) <= width ->
  (T_dom_lt_predecessor limit semis (links, best, witness) source <=
    T_dom_lt_eval limit semis links source + 64 * N.of_nat (width + 1))%N.
Proof.
  cbn zeta. destruct (dom_lt_eval limit semis links source) as [after chosen] eqn:Heval.
  cbn [snd]. intros Hchosen Hscore.
  pose proof (dom_lt_time_identity semis chosen) as Hidentity.
  pose proof (dom_lt_time_ltb (dom_lt_identity semis chosen) best) as Hcompare.
  unfold T_dom_lt_predecessor. time_simpl. rewrite Heval.
  destruct (N.ltb (dom_lt_identity semis chosen) best); time_simpl;
    rewrite !Nat2N.inj_add in *; nia.
Qed.

(** A root settlement performs only its encoded-parent lookup. *)
Lemma dom_lt_semi_settle_stop_clock width numeric st v :
  N.size_nat v <= width ->
  trie_get (dom_lt_key v) (lt_numeric_parent numeric) = None ->
  (T_dom_lt_settle numeric st v <=
    128 * (PTrieT.c_trie + 1) * N.of_nat (width + 1))%N.
Proof.
  intros Hv Hparent.
  pose proof (dom_lt_time_key v) as Hkey.
  pose proof (dom_lt_key_width v) as Hwidth.
  unfold T_dom_lt_settle. time_simpl. rewrite Hparent. time_simpl.
  rewrite PTrieT.trie_get_clock. rewrite !Nat2N.inj_add in *. nia.
Qed.

(** A live settlement retains its exact predecessor fold and final link clock. *)
Lemma dom_lt_semi_settle_live_clock width numeric st v p :
  let incoming := match trie_get (dom_lt_key v) (lt_numeric_pred numeric) with
    None => [] | Some row => row end in
  let result := fold_left
    (dom_lt_predecessor (lt_numeric_limit numeric) (lt_semis st)) incoming
    (lt_semi_links st, p, p) in
  N.size_nat v <= width ->
  trie_get (dom_lt_key v) (lt_numeric_parent numeric) = Some p ->
  (T_dom_lt_settle numeric st v <=
    List.T_fold_left
      (dom_lt_predecessor (lt_numeric_limit numeric) (lt_semis st))
      (T_dom_lt_predecessor (lt_numeric_limit numeric) (lt_semis st)) incoming
      (lt_semi_links st, p, p) +
    T_dom_lt_link (fst (fst result)) v p +
    128 * (PTrieT.c_trie + 1) * N.of_nat (width + 1))%N.
Proof.
  cbn zeta. intros Hv Hparent.
  pose proof (dom_lt_time_key v) as Hkey.
  pose proof (dom_lt_key_width v) as Hwidth.
  unfold T_dom_lt_settle. time_simpl. rewrite Hparent. time_simpl.
  change (fun (acc : dom_lt_links * N * N) (source : N) =>
    T_dom_lt_predecessor (lt_numeric_limit numeric) (lt_semis st) acc source) with
    (T_dom_lt_predecessor (lt_numeric_limit numeric) (lt_semis st)).
  destruct (fold_left
    (dom_lt_predecessor (lt_numeric_limit numeric) (lt_semis st))
    (match trie_get (dom_lt_key v) (lt_numeric_pred numeric) with
      None => [] | Some row => row end) (lt_semi_links st, p, p))
    as [[links best] witness].
  cbn [fst].
  pose proof (PTrieT.T_set_le N (dom_lt_key v) best (lt_semis st)) as Hsemi.
  pose proof (PTrieT.T_set_le N (dom_lt_key v) witness (lt_minimizer st)) as Hmin.
  change (PTrieCode.T_set (dom_lt_key v) best (lt_semis st) <=
    PTrieT.c_trie * N.of_nat (Pos.size_nat (dom_lt_key v) + 1))%N in Hsemi.
  change (PTrieCode.T_set (dom_lt_key v) witness (lt_minimizer st) <=
    PTrieT.c_trie * N.of_nat (Pos.size_nat (dom_lt_key v) + 1))%N in Hmin.
  rewrite !PTrieT.trie_get_clock. time_simpl.
  rewrite !Nat2N.inj_add in *. nia.
Qed.

(** Bucket insertion needs only widths of its input rank and stored semidominator. *)
Lemma dom_lt_semi_bucket_add_clock width semis buckets v :
  N.size_nat v <= width ->
  dom_lt_trie_all (fun n => N.size_nat n <= width) semis ->
  (T_dom_lt_bucket_add semis buckets v <=
    128 * (PTrieT.c_trie + 1) * N.of_nat (width + 1))%N.
Proof.
  intros Hv Hsemis.
  pose proof (dom_lt_time_key v) as Hvkey.
  pose proof (dom_lt_key_width v) as Hvwidth.
  unfold T_dom_lt_bucket_add.
  destruct (trie_get (dom_lt_key v) semis) as [s|] eqn:Hget.
  - pose proof (Hsemis _ _ Hget) as Hs.
    change (N.size_nat s <= width) in Hs.
    pose proof (dom_lt_time_key s) as Hskey.
    pose proof (dom_lt_key_width s) as Hswidth.
    set (row := match trie_get (dom_lt_key s) buckets with None => [] | Some xs => xs end).
    pose proof (PTrieT.T_set_le (list N) (dom_lt_key s) (v :: row) buckets) as Hset.
    change (PTrieCode.T_set (dom_lt_key s) (v :: row) buckets <=
      PTrieT.c_trie * N.of_nat (Pos.size_nat (dom_lt_key s) + 1))%N in Hset.
    fold row. time_simpl. rewrite !PTrieT.trie_get_clock.
    clearbody row. clear -Hv Hs Hvkey Hvwidth Hskey Hswidth Hset.
    rewrite !Nat2N.inj_add in *. nia.
  - time_simpl. rewrite PTrieT.trie_get_clock.
    clear -Hv Hvkey Hvwidth. rewrite !Nat2N.inj_add in *. nia.
Qed.

(** A bucket member retains its exact evaluator clock and pays one relative-parent write. *)
Lemma dom_lt_semi_bucket_member_clock width limit semis s st v :
  let chosen := snd (dom_lt_eval limit semis (lt_bucket_links st) v) in
  N.size_nat v <= width -> N.size_nat chosen <= width ->
  N.size_nat (dom_lt_identity semis chosen) <= width ->
  (T_dom_lt_bucket_member limit semis s st v <=
    T_dom_lt_eval limit semis (lt_bucket_links st) v +
    128 * (PTrieT.c_trie + 1) * N.of_nat (width + 1))%N.
Proof.
  cbn zeta.
  destruct (dom_lt_eval limit semis (lt_bucket_links st) v) as [links chosen] eqn:Heval.
  cbn [snd]. intros Hv Hchosen Hscore.
  pose proof (dom_lt_time_key v) as Hkey.
  pose proof (dom_lt_key_width v) as Hwidth.
  pose proof (dom_lt_time_identity semis chosen) as Hidentity.
  pose proof (dom_lt_time_ltb (dom_lt_identity semis chosen) s) as Hcompare.
  unfold T_dom_lt_bucket_member. time_simpl. rewrite Heval.
  destruct (N.ltb (dom_lt_identity semis chosen) s).
  - pose proof (PTrieT.T_set_le N (dom_lt_key v) chosen (lt_relative st)) as Hset.
    change (PTrieCode.T_set (dom_lt_key v) chosen (lt_relative st) <=
      PTrieT.c_trie * N.of_nat (Pos.size_nat (dom_lt_key v) + 1))%N in Hset.
    time_simpl. rewrite !Nat2N.inj_add in *. nia.
  - pose proof (PTrieT.T_set_le N (dom_lt_key v) s (lt_relative st)) as Hset.
    change (PTrieCode.T_set (dom_lt_key v) s (lt_relative st) <=
      PTrieT.c_trie * N.of_nat (Pos.size_nat (dom_lt_key v) + 1))%N in Hset.
    time_simpl. rewrite !Nat2N.inj_add in *. nia.
Qed.

(** A bucket step retains its exact member fold and optional linker clock. *)
Lemma dom_lt_semi_bucket_step_clock width numeric semis buckets st s :
  let row := match trie_get (dom_lt_key s) buckets with None => [] | Some xs => xs end in
  let result := fold_left (dom_lt_bucket_member (lt_numeric_limit numeric) semis s) row st in
  N.size_nat s <= width ->
  (T_dom_lt_bucket_step numeric semis buckets st s <=
    List.T_fold_left (dom_lt_bucket_member (lt_numeric_limit numeric) semis s)
      (T_dom_lt_bucket_member (lt_numeric_limit numeric) semis s) row st +
    (match trie_get (dom_lt_key s) (lt_numeric_parent numeric) with
      None => 0 | Some p => T_dom_lt_link (lt_bucket_links result) s p end) +
    128 * (PTrieT.c_trie + 1) * N.of_nat (width + 1))%N.
Proof.
  cbn zeta. intro Hs.
  pose proof (dom_lt_time_key s) as Hkey.
  pose proof (dom_lt_key_width s) as Hwidth.
  unfold T_dom_lt_bucket_step. time_simpl.
  change (fun (current : dom_lt_bucket_state) (v : N) =>
    T_dom_lt_bucket_member (lt_numeric_limit numeric) semis s current v) with
    (T_dom_lt_bucket_member (lt_numeric_limit numeric) semis s).
  destruct (trie_get (dom_lt_key s) (lt_numeric_parent numeric));
    time_simpl; rewrite !PTrieT.trie_get_clock;
    rewrite !Nat2N.inj_add in *; nia.
Qed.

(** Correction needs only the current key and stored relative parent's width. *)
Lemma dom_lt_semi_correct_step_clock width semis relative corrected v :
  N.size_nat v <= width ->
  dom_lt_trie_all (fun n => N.size_nat n <= width) relative ->
  (T_dom_lt_correct_step semis relative corrected v <=
    128 * (PTrieT.c_trie + 1) * N.of_nat (width + 1))%N.
Proof.
  intros Hv Hrelative.
  pose proof (dom_lt_time_key v) as Hkey.
  pose proof (dom_lt_key_width v) as Hwidth.
  pose proof (dom_lt_time_identity semis v) as Hscore.
  unfold T_dom_lt_correct_step.
  destruct (trie_get (dom_lt_key v) relative) as [p|] eqn:Hget.
  - pose proof (Hrelative _ _ Hget) as Hp.
    change (N.size_nat p <= width) in Hp.
    pose proof (dom_lt_time_identity corrected p) as Hparent.
    pose proof (N.T_eqb_le p (dom_lt_identity semis v)) as Hcompare.
    destruct (N.eqb p (dom_lt_identity semis v)).
    + pose proof (PTrieT.T_set_le N (dom_lt_key v) p corrected) as Hset.
      change (PTrieCode.T_set (dom_lt_key v) p corrected <=
        PTrieT.c_trie * N.of_nat (Pos.size_nat (dom_lt_key v) + 1))%N in Hset.
      time_simpl. rewrite PTrieT.trie_get_clock. rewrite !Nat2N.inj_add in *. nia.
    + pose proof (PTrieT.T_set_le N (dom_lt_key v) (dom_lt_identity corrected p) corrected)
        as Hset.
      change (PTrieCode.T_set (dom_lt_key v) (dom_lt_identity corrected p) corrected <=
        PTrieT.c_trie * N.of_nat (Pos.size_nat (dom_lt_key v) + 1))%N in Hset.
      time_simpl. rewrite PTrieT.trie_get_clock. rewrite !Nat2N.inj_add in *. nia.
  - time_simpl. rewrite PTrieT.trie_get_clock. rewrite !Nat2N.inj_add in *. nia.
Qed.

(** Building buckets scans the order once and performs one bounded insertion per rank. *)
Lemma dom_lt_semi_bucket_build_clock width semis order :
  Forall (fun n => N.size_nat n <= width) order ->
  dom_lt_trie_all (fun n => N.size_nat n <= width) semis ->
  (List.T_rev_append order [] +
    List.T_fold_left (dom_lt_bucket_add semis) (T_dom_lt_bucket_add semis)
      (rev_append order []) Empty <=
    256 * (PTrieT.c_trie + 1) * N.of_nat ((length order + 1) * (width + 1)))%N.
Proof.
  intros Horder Hsemis.
  pose proof (List.T_rev_append_le order []) as Hreverse.
  pose proof (dom_time_fold_left (dom_lt_bucket_add semis) (T_dom_lt_bucket_add semis)
    (128 * (PTrieT.c_trie + 1) * N.of_nat (width + 1))%N
    (rev_append order []) Empty) as Hfold.
  specialize (Hfold ltac:(intros v Hv current; apply dom_lt_semi_bucket_add_clock;
    [apply (proj1 (Forall_forall _ _) Horder v);
      rewrite rev_append_rev, app_nil_r, <- in_rev in Hv; exact Hv|exact Hsemis])).
  replace (length (rev_append order [])) with (length order) in Hfold by
    (rewrite rev_append_rev, length_app, length_rev; cbn [length]; lia).
  rewrite !Nat2N.inj_mul, !Nat2N.inj_add in *. nia.
Qed.

(** Correction is one reversal followed by one bounded callback per numeric vertex. *)
Lemma dom_lt_semi_correct_clock width numeric semis relative :
  Forall (fun n => N.size_nat n <= width) (lt_numeric_order numeric) ->
  dom_lt_trie_all (fun n => N.size_nat n <= width) relative ->
  (T_dom_lt_correct numeric semis relative <=
    256 * (PTrieT.c_trie + 1) *
      N.of_nat ((length (lt_numeric_order numeric) + 1) * (width + 1)))%N.
Proof.
  intros Horder Hrelative.
  pose proof (List.T_rev_append_le (lt_numeric_order numeric) []) as Hreverse.
  pose proof (dom_time_fold_left (dom_lt_correct_step semis relative)
    (T_dom_lt_correct_step semis relative)
    (128 * (PTrieT.c_trie + 1) * N.of_nat (width + 1))%N
    (rev_append (lt_numeric_order numeric) []) Empty) as Hfold.
  specialize (Hfold ltac:(intros v Hv current; apply dom_lt_semi_correct_step_clock;
    [apply (proj1 (Forall_forall _ _) Horder v);
      rewrite rev_append_rev, app_nil_r, <- in_rev in Hv; exact Hv|exact Hrelative])).
  unfold T_dom_lt_correct. time_simpl.
  change (fun (current : ptrie N) (v : N) =>
    T_dom_lt_correct_step semis relative current v) with
    (T_dom_lt_correct_step semis relative).
  replace (length (rev_append (lt_numeric_order numeric) [])) with
    (length (lt_numeric_order numeric)) in Hfold by
    (rewrite rev_append_rev, length_app, length_rev; cbn [length]; lia).
  rewrite !Nat2N.inj_mul, !Nat2N.inj_add in *. nia.
Qed.

(** Original-key rank lookup has the same digit charge as the underlying trie read. *)
Lemma dom_lt_pipeline_rank_get_clock ranks v :
  (T_dom_lt_rank_get ranks v <= 2 * N.of_nat (Pos.size_nat v) + 2)%N.
Proof.
  unfold T_dom_lt_rank_get. destruct (trie_get v ranks); time_simpl;
    rewrite PTrieT.trie_get_clock; lia.
Qed.

(** Reading a prepared predecessor row has only an original-key trie lookup. *)
Lemma dom_lt_pipeline_preds_clock g v :
  (T_preds g v <= 2 * N.of_nat (Pos.size_nat v) + 2)%N.
Proof.
  destruct g as [graph predecessors vertex_count edge_count].
  unfold T_preds. time_simpl. rewrite PTrieT.trie_get_clock. lia.
Qed.

(** A right fold needs a uniform callback bound only on the entries it actually visits. *)
Lemma dom_lt_pipeline_fold_right_clock {A B : Type} (step : B -> A -> A)
    (T_step : B -> A -> N) k row initial :
  (forall v, In v row -> forall rest, (T_step v rest <= k)%N) ->
  (List.T_fold_right step T_step initial row <=
    (k + 1) * N.of_nat (length row) + 1)%N.
Proof.
  induction row as [|v rest IH]; intro Hbound.
  - time_unfold @List.T_fold_right. cbn [length]. lia.
  - pose proof (Hbound v (or_introl eq_refl) (fold_right step initial rest)) as Hhead.
    specialize (IH (fun x Hx => Hbound x (or_intror Hx))).
    time_unfold @List.T_fold_right. fold (List.T_fold_right step T_step).
    cbn [length]. rewrite Nat2N.inj_succ. clear -Hhead IH. nia.
Qed.

(** Rank filtering reads every predecessor occurrence once, preserving duplicate charges. *)
Lemma dom_lt_pipeline_ranked_row_clock width ranks row :
  Forall (fun v => Pos.size_nat v <= width) row ->
  (T_dom_lt_ranked_row ranks row <=
    8 * N.of_nat ((length row + 1) * (width + 1)))%N.
Proof.
  intro Hrow. unfold T_dom_lt_ranked_row. time_simpl.
  match goal with
  | |- context [List.T_fold_right ?step ?T_step ?initial ?xs] =>
    pose proof (dom_lt_pipeline_fold_right_clock step T_step
      (4 * N.of_nat (width + 1))%N xs initial) as Hfold
  end.
  specialize (Hfold ltac:(intros v Hv rest;
    pose proof (proj1 (Forall_forall _ _) Hrow v Hv) as Hwidth;
    change (Pos.size_nat v <= width) in Hwidth;
    time_simpl; destruct (trie_get v ranks); time_simpl;
    rewrite PTrieT.trie_get_clock; clear -Hwidth; rewrite !Nat2N.inj_add in *; lia)).
  rewrite !Nat2N.inj_mul, !Nat2N.inj_add in *. clear -Hfold. nia.
Qed.

(** Numeric insertion pays three encoded-key writes and one pass over its predecessor row. *)
Lemma dom_lt_pipeline_numeric_add_clock width g layout st v :
  Pos.size_nat v <= width ->
  N.size_nat (dom_lt_rank_get (lt_rank layout) v) <= width ->
  dom_lt_trie_all (fun p => Pos.size_nat p <= width) (lt_dfs_parent layout) ->
  Forall (fun p => Pos.size_nat p <= width) (preds g v) ->
  (T_dom_lt_numeric_add g layout st v <=
    128 * (PTrieT.c_trie + 1) *
      N.of_nat ((length (preds g v) + 1) * (width + 1)))%N.
Proof.
  intros Hv Hrank Hparents Hrow.
  set (rank := dom_lt_rank_get (lt_rank layout) v).
  set (key := dom_lt_key rank).
  pose proof (dom_lt_pipeline_rank_get_clock (lt_rank layout) v) as Hrankget.
  pose proof (dom_lt_time_key rank) as Hkey.
  pose proof (dom_lt_key_width rank) as Hkeywidth.
  pose proof (dom_lt_pipeline_preds_clock g v) as Hpreds.
  pose proof (dom_lt_pipeline_ranked_row_clock width (lt_rank layout) (preds g v) Hrow)
    as Hranked.
  pose proof (PTrieT.T_set_le (list N) key
    (dom_lt_ranked_row (lt_rank layout) (preds g v)) (lt_numeric_pred st)) as Hsetpred.
  pose proof (PTrieT.T_set_le positive key v (lt_numeric_vertex st)) as Hsetvertex.
  change (PTrieCode.T_set key (dom_lt_ranked_row (lt_rank layout) (preds g v))
    (lt_numeric_pred st) <= PTrieT.c_trie * N.of_nat (Pos.size_nat key + 1))%N in Hsetpred.
  change (PTrieCode.T_set key v (lt_numeric_vertex st) <=
    PTrieT.c_trie * N.of_nat (Pos.size_nat key + 1))%N in Hsetvertex.
  fold rank in Hrank. fold key in Hkeywidth.
  unfold T_dom_lt_numeric_add. time_simpl. fold rank key.
  destruct (trie_get v (lt_dfs_parent layout)) as [parent|] eqn:Hget.
  - pose proof (Hparents _ _ Hget) as Hparent.
    change (Pos.size_nat parent <= width) in Hparent.
    pose proof (dom_lt_pipeline_rank_get_clock (lt_rank layout) parent) as Hparentget.
    pose proof (PTrieT.T_set_le N key (dom_lt_rank_get (lt_rank layout) parent)
      (lt_numeric_parent st)) as Hsetparent.
    change (PTrieCode.T_set key (dom_lt_rank_get (lt_rank layout) parent)
      (lt_numeric_parent st) <= PTrieT.c_trie * N.of_nat (Pos.size_nat key + 1))%N in Hsetparent.
    time_simpl. rewrite PTrieT.trie_get_clock.
    clearbody rank key.
    clear -Hv Hrank Hrankget Hkey Hkeywidth Hpreds Hranked Hsetpred Hsetvertex
      Hparent Hparentget Hsetparent.
    rewrite !Nat2N.inj_mul, !Nat2N.inj_add in *. nia.
  - time_simpl. rewrite PTrieT.trie_get_clock.
    clearbody rank key.
    clear -Hv Hrank Hrankget Hkey Hkeywidth Hpreds Hranked Hsetpred Hsetvertex.
    rewrite !Nat2N.inj_mul, !Nat2N.inj_add in *. nia.
Qed.

(** Layout stacks and stored original parents obey the width of every entered key. *)
Definition dom_lt_pipeline_layout_width (width : nat) (layout : dom_lt_layout) : Prop :=
  Forall (fun v => Pos.size_nat v <= width) (lt_stack layout) /\
  dom_lt_trie_all (fun v => Pos.size_nat v <= width) (lt_dfs_parent layout).

(** A layout event preserves its original-key payload widths. *)
Lemma dom_lt_pipeline_layout_event_width width st event :
  dom_lt_pipeline_layout_width width st ->
  (match event with SearchSig.Enter v => Pos.size_nat v <= width | _ => True end) ->
  dom_lt_pipeline_layout_width width (dom_lt_event st event).
Proof.
  destruct st as [order ranks parents stack next]. intros [Hstack Hparents].
  destruct event as [v|v|kind u v]; cbn [dom_lt_event].
  - intro Hv. destruct stack as [|parent rest].
    + split; [now constructor|exact Hparents].
    + inversion Hstack as [|head tail Hparent Hrest]; subst head tail.
      split; [now constructor|]. apply dom_lt_trie_all_set; assumption.
  - intro Htrivial. destruct stack as [|parent rest];
      split; try exact Hparents; [constructor|].
    now inversion Hstack.
  - intro Htrivial. now split.
Qed.

(** The real layout contains only original parent keys whose widths fit the input graph. *)
Lemma dom_lt_pipeline_layout_of_width g r :
  dom_lt_pipeline_layout_width (graph_width (base g)) (dom_lt_layout_of g r).
Proof.
  unfold dom_lt_layout_of.
  apply (dom_lt_fold_forall dom_lt_event
    (dom_lt_pipeline_layout_width (graph_width (base g)))
    (fun event => match event with
      SearchSig.Enter v => Pos.size_nat v <= graph_width (base g) | _ => True end)).
  - apply Forall_forall. intros event Hevent. destruct event as [v|v|kind u v];
      [|exact I|exact I].
    apply dom_listed_key_width.
    destruct (dom_lt_trace_inventory g r) as [_ [Hlisted _]].
    apply Hlisted. now apply Search.search_entered_member.
  - split; [constructor|apply dom_lt_trie_all_empty].
  - intros st event Hst Hevent. now apply dom_lt_pipeline_layout_event_width.
Qed.

(** Every prepared predecessor occurrence names a listed original source vertex. *)
Lemma dom_lt_pipeline_preds_listed g v p :
  prepared_ok g -> In p (preds g v) -> In p (nodes g).
Proof.
  intros [_ [_ Hpreds]] Hp.
  apply (Permutation.Permutation_in p (Hpreds v)) in Hp.
  apply in_flat_map in Hp. destruct Hp as [source [Hsource Hp]].
  apply in_map_iff in Hp. destruct Hp as [ignored [Heq Hin]]. subst p. exact Hsource.
Qed.

(** Every bounded discovery rank fits in the graph's original key width. *)
Lemma dom_lt_pipeline_discovery_width g r n :
  (n <= N.of_nat (length (dom_lt_dfs g r)))%N ->
  N.size_nat n <= graph_width (base g).
Proof.
  intro Hn. destruct (dom_lt_dfs_inventory g r) as [Hunique [Hlisted Hcounts]].
  apply (dom_distinct_value_width (dom_lt_dfs g r) (graph_width (base g)) n Hunique);
    [|exact Hn].
  intros v Hv. apply dom_listed_key_width. now apply Hlisted.
Qed.

(** Numeric vertex payloads retain the widths of their original discovered keys. *)
Lemma dom_lt_pipeline_numeric_vertex_width g r :
  dom_lt_trie_all (fun v => Pos.size_nat v <= graph_width (base g))
    (lt_numeric_vertex (dom_lt_numeric_of g r)).
Proof.
  unfold dom_lt_numeric_of.
  apply (dom_lt_fold_forall (dom_lt_numeric_add g (dom_lt_layout_of g r))
    (fun st => dom_lt_trie_all (fun v => Pos.size_nat v <= graph_width (base g))
      (lt_numeric_vertex st)) (fun v => In v (nodes g))).
  - change (Forall (fun v => In v (nodes g)) (dom_lt_dfs g r)).
    apply Forall_forall. exact (proj1 (proj2 (dom_lt_dfs_inventory g r))).
  - apply dom_lt_trie_all_empty.
  - intros st v Hst Hv. cbn [dom_lt_numeric_add lt_numeric_vertex].
    apply dom_lt_trie_all_set; [exact Hst|now apply dom_listed_key_width].
Qed.

(** One closed coefficient pays layout construction and all numeric row conversion. *)
Definition dom_lt_numeric_coefficient : N :=
  (1024 * (Search.search_trace_coefficient + PTrieT.c_trie + 4096))%N.


(** Erasure pays bounded numeric reads and one write at an original vertex key. *)
Lemma dom_lt_pipeline_erase_clock width numeric parents :
  Forall (fun n => N.size_nat n <= width) (lt_numeric_order numeric) ->
  dom_lt_trie_all (fun n => N.size_nat n <= width) parents ->
  dom_lt_trie_all (fun v => Pos.size_nat v <= width) (lt_numeric_vertex numeric) ->
  (T_dom_lt_erase numeric parents <=
    512 * (PTrieT.c_trie + 1) *
      N.of_nat ((length (lt_numeric_order numeric) + 1) * (width + 1)))%N.
Proof.
  intros Horder Hparents Hvertices.
  unfold T_dom_lt_erase. time_simpl.
  match goal with
  | |- context [List.T_fold_left ?step ?T_step ?order ?initial] =>
    assert (Hcallbacks : forall v, In v order -> forall result,
      (T_step result v <=
        256 * (PTrieT.c_trie + 1) * N.of_nat (width + 1))%N) by
      (intros v Hv result;
       pose proof (proj1 (Forall_forall _ _) Horder v Hv) as Hwidth;
       change (N.size_nat v <= width) in Hwidth;
       pose proof (dom_lt_time_key v) as Hkey;
       pose proof (dom_lt_key_width v) as Hkeywidth;
       time_simpl;
       destruct (trie_get (dom_lt_key v) parents) as [p|] eqn:Hparent;
       destruct (trie_get (dom_lt_key v) (lt_numeric_vertex numeric)) as [child|] eqn:Hchild;
       [pose proof (Hparents _ _ Hparent) as Hp;
        change (N.size_nat p <= width) in Hp;
        pose proof (Hvertices _ _ Hchild) as Hchildwidth;
        change (Pos.size_nat child <= width) in Hchildwidth;
        pose proof (dom_lt_time_key p) as Hpkey;
        pose proof (dom_lt_key_width p) as Hpkeywidth;
        destruct (trie_get (dom_lt_key p) (lt_numeric_vertex numeric)) as [parent|];
        [pose proof (PTrieT.T_set_le positive child parent result) as Hset;
         change (PTrieCode.T_set child parent result <=
           PTrieT.c_trie * N.of_nat (Pos.size_nat child + 1))%N in Hset|]
       | | | ];
       time_simpl; rewrite !PTrieT.trie_get_clock;
       rewrite !Nat2N.inj_add in *; nia);
    pose proof (dom_time_fold_left step T_step
      (256 * (PTrieT.c_trie + 1) * N.of_nat (width + 1))%N
      order initial Hcallbacks) as Hfold
  end.
  rewrite !Nat2N.inj_mul, !Nat2N.inj_add in *. nia.
Qed.

Local Transparent dom_lt_eval T_dom_lt_eval.

(** * Logarithmic credit for descending shortcut paths *)

(** The logarithm of a positive sum pays the average logarithm of both summands. *)
Lemma dom_gap_log_pair : forall a b,
  0 < a -> 0 < b -> 1 + Nat.log2 a + Nat.log2 b <= 2 * Nat.log2 (a + b).
Proof.
  intros a b Ha Hb.
  pose proof (Nat.log2_le_mono a (a + b) ltac:(lia)) as Hleft.
  pose proof (Nat.log2_le_mono b (a + b) ltac:(lia)) as Hright.
  destruct (Nat.lt_trichotomy (Nat.log2 a) (Nat.log2 b)) as [Hlt|[Heq|Hgt]];
    [lia| |lia].
  pose proof (proj1 (Nat.log2_spec a Ha)) as Halower.
  pose proof (proj1 (Nat.log2_spec b Hb)) as Hblower.
  rewrite <- Heq in Hblower.
  assert (Hpower : 2 ^ S (Nat.log2 a) <= a + b).
  { change (2 * 2 ^ Nat.log2 a <= a + b). lia. }
  assert (Hstrict : S (Nat.log2 a) <= Nat.log2 (a + b)).
  { apply (proj1 (Nat.log2_le_pow2 (a + b) (S (Nat.log2 a)) ltac:(lia))).
    exact Hpower. }
  lia.
Qed.

Definition dom_gap_total (gaps : list nat) : nat := fold_right Nat.add 0 gaps.

Definition dom_gap_old_levels (gaps : list nat) : nat :=
  fold_right (fun gap levels => Nat.log2 gap + levels) 0 gaps.

Fixpoint dom_gap_new_levels (gaps : list nat) : nat :=
  match gaps with
  | [] => 0
  | gap :: rest => Nat.log2 (gap + dom_gap_total rest) + dom_gap_new_levels rest
  end.

(** Compression changes each old gap into its suffix sum. The level increase pays all
    but a logarithmic number of frames, without classifying individual frames. *)
Lemma dom_gap_path_credit : forall gaps,
  Forall (fun gap => 0 < gap) gaps ->
  length gaps + dom_gap_old_levels gaps <=
    Nat.log2 (dom_gap_total gaps) + 1 + dom_gap_new_levels gaps.
Proof.
  intros gaps Hpositive. induction Hpositive as [|gap rest Hgap Hrest IH].
  - cbn [length dom_gap_old_levels dom_gap_total dom_gap_new_levels fold_right]. lia.
  - change (S (length rest) + (Nat.log2 gap + dom_gap_old_levels rest) <=
      Nat.log2 (gap + dom_gap_total rest) + 1 +
        (Nat.log2 (gap + dom_gap_total rest) + dom_gap_new_levels rest)).
    destruct rest as [|next rest].
    + cbn [length dom_gap_old_levels dom_gap_total dom_gap_new_levels fold_right].
      rewrite !Nat.add_0_r. lia.
    + assert (Htail : 0 < dom_gap_total (next :: rest)).
      { inversion Hrest as [|head tail Hnext Hpositive']; subst head tail.
        unfold dom_gap_total. cbn [fold_right]. lia. }
      pose proof (dom_gap_log_pair gap (dom_gap_total (next :: rest)) Hgap Htail) as Hpair.
      lia.
Qed.

(** A uniform gap bound also bounds the sum of the original logarithmic levels. *)
Lemma dom_gap_old_levels_bound : forall gaps bound,
  (forall gap, In gap gaps -> gap <= bound) ->
  dom_gap_old_levels gaps <= length gaps * Nat.log2 bound.
Proof.
  intro gaps. induction gaps as [|gap rest IH]; intros bound Hbound; [reflexivity|].
  assert (Hhead : Nat.log2 gap <= Nat.log2 bound).
  { apply Nat.log2_le_mono. apply Hbound. now left. }
  specialize (IH bound ltac:(intros x Hx; apply Hbound; now right)).
  unfold dom_gap_old_levels in *. cbn [fold_right length]. lia.
Qed.

(** Every compressed suffix has at most the total gap's logarithmic level. *)
Lemma dom_gap_suffix_bound : forall gaps bound,
  dom_gap_total gaps <= bound ->
  dom_gap_new_levels gaps <= length gaps * Nat.log2 bound.
Proof.
  intro gaps. induction gaps as [|gap rest IH]; intros bound Hbound; [reflexivity|].
  assert (Htail : dom_gap_total rest <= bound).
  { unfold dom_gap_total in *. cbn [fold_right] in Hbound. lia. }
  specialize (IH bound Htail).
  pose proof (Nat.log2_le_mono (dom_gap_total (gap :: rest)) bound Hbound) as Hhead.
  change (Nat.log2 (gap + dom_gap_total rest) <= Nat.log2 bound) in Hhead.
  cbn [dom_gap_new_levels length]. lia.
Qed.

Definition dom_gap_weight (domain : list nat) (weight : nat -> nat) : nat :=
  fold_right (fun vertex total => weight vertex + total) 0 domain.

(** Pointwise equality on a finite domain preserves its total weight. *)
Lemma dom_gap_weight_ext : forall domain before after,
  (forall vertex, In vertex domain -> before vertex = after vertex) ->
  dom_gap_weight domain before = dom_gap_weight domain after.
Proof.
  intro domain. induction domain as [|vertex rest IH]; intros before after Hagree;
    [reflexivity|].
  unfold dom_gap_weight in *. cbn [fold_right].
  rewrite (Hagree vertex ltac:(now left)), (IH before after).
  - reflexivity.
  - intros key Hin. apply Hagree. now right.
Qed.

(** Replacing one unique vertex transfers exactly its old and new level. *)
Lemma dom_gap_weight_update : forall domain vertex before after,
  NoDup domain -> In vertex domain ->
  (forall key, In key domain -> key <> vertex -> after key = before key) ->
  dom_gap_weight domain after + before vertex =
    dom_gap_weight domain before + after vertex.
Proof.
  intros domain vertex before after Hunique.
  induction Hunique as [|head rest Hfresh Hunique IH]; intros Hin Hagree;
    [contradiction|].
  destruct Hin as [<-|Hin].
  - assert (Htail : dom_gap_weight rest after = dom_gap_weight rest before).
    { apply dom_gap_weight_ext. intros key Hkey. apply Hagree.
      - now right.
      - intro Heq. subst key. contradiction. }
    change (after head + dom_gap_weight rest after + before head =
      before head + dom_gap_weight rest before + after head).
    rewrite Htail. lia.
  - assert (Hhead : after head = before head).
    { apply Hagree; [now left|]. intro Heq. subst head. contradiction. }
    specialize (IH Hin ltac:(intros key Hkey Hne; apply Hagree; [now right|exact Hne])).
    change (after head + dom_gap_weight rest after + before vertex =
      before head + dom_gap_weight rest before + after vertex).
    rewrite Hhead. lia.
Qed.

(** A uniform pointwise bound limits the weight of a finite domain. *)
Lemma dom_gap_weight_bound : forall domain weight bound,
  (forall vertex, In vertex domain -> weight vertex <= bound) ->
  dom_gap_weight domain weight <= length domain * bound.
Proof.
  intro domain. induction domain as [|vertex rest IH]; intros weight bound Hbound;
    [reflexivity|].
  pose proof (Hbound vertex ltac:(now left)) as Hhead.
  specialize (IH weight bound ltac:(intros key Hin; apply Hbound; now right)).
  change (weight vertex + dom_gap_weight rest weight <= (1 + length rest) * bound).
  nia.
Qed.

Inductive dom_gap_path (parent : nat -> nat) : nat -> list nat -> nat -> Prop :=
  | dom_gap_path_stop root : dom_gap_path parent root [] root
  | dom_gap_path_step vertex next rest root :
      parent vertex = next -> next < vertex -> dom_gap_path parent next rest root ->
      dom_gap_path parent vertex (vertex :: rest) root.

(** A descending path stays between its root and its starting vertex. *)
Lemma dom_gap_path_range parent start path root : dom_gap_path parent start path root ->
  root <= start /\ (forall vertex, In vertex path -> root < vertex <= start).
Proof.
  intro Hpath. induction Hpath as [root|vertex next rest root Hparent Hless Hpath IH].
  - split; [lia|intros key Hin; contradiction].
  - destruct IH as [Hroot Hrange]. split; [lia|].
    intros key [<-|Hin]; [lia|]. specialize (Hrange key Hin). lia.
Qed.

(** Strict descent prevents repeated vertices on a path. *)
Lemma dom_gap_path_unique parent start path root : dom_gap_path parent start path root ->
  NoDup path.
Proof.
  intro Hpath. induction Hpath as [root|vertex next rest root Hparent Hless Hpath IH].
  - constructor.
  - constructor; [|exact IH]. intro Hin.
    pose proof (proj2 (dom_gap_path_range parent next rest root Hpath) vertex Hin). lia.
Qed.

(** Every traversed shortcut contributes a positive numeric gap. *)
Lemma dom_gap_path_positive parent start path root : dom_gap_path parent start path root ->
  Forall (fun gap => 0 < gap) (map (fun vertex => vertex - parent vertex) path).
Proof.
  intro Hpath. induction Hpath as [root|vertex next rest root Hparent Hless Hpath IH].
  - constructor.
  - cbn [map]. constructor; [rewrite Hparent; lia|exact IH].
Qed.

(** Consecutive shortcut gaps telescope from the starting vertex to the root. *)
Lemma dom_gap_path_total parent start path root : dom_gap_path parent start path root ->
  dom_gap_total (map (fun vertex => vertex - parent vertex) path) + root = start.
Proof.
  intro Hpath. induction Hpath as [root|vertex next rest root Hparent Hless Hpath IH].
  - reflexivity.
  - change (vertex - parent vertex +
      dom_gap_total (map (fun key => key - parent key) rest) + root = vertex).
    rewrite Hparent. lia.
Qed.

(** Original gap levels equal the path's weight in the original parent map. *)
Lemma dom_gap_path_before parent path :
  dom_gap_old_levels (map (fun vertex => vertex - parent vertex) path) =
    dom_gap_weight path (fun vertex => Nat.log2 (vertex - parent vertex)).
Proof.
  induction path as [|vertex rest IH]; [reflexivity|].
  change (Nat.log2 (vertex - parent vertex) +
      dom_gap_old_levels (map (fun key => key - parent key) rest) =
    Nat.log2 (vertex - parent vertex) +
      dom_gap_weight rest (fun key => Nat.log2 (key - parent key))).
  now rewrite IH.
Qed.

(** Suffix-gap levels equal the path's weight after redirecting every vertex to the root. *)
Lemma dom_gap_path_after parent start path root : dom_gap_path parent start path root ->
  dom_gap_new_levels (map (fun vertex => vertex - parent vertex) path) =
    dom_gap_weight path (fun vertex => Nat.log2 (vertex - root)).
Proof.
  intro Hpath. induction Hpath as [root|vertex next rest root Hparent Hless Hpath IH].
  - reflexivity.
  - pose proof (dom_gap_path_total parent next rest root Hpath) as Htotal.
    change (Nat.log2 (vertex - parent vertex +
      dom_gap_total (map (fun key => key - parent key) rest)) +
        dom_gap_new_levels (map (fun key => key - parent key) rest) =
      Nat.log2 (vertex - root) + dom_gap_weight rest (fun key => Nat.log2 (key - root))).
    rewrite IH, Hparent.
    replace (vertex - next + dom_gap_total (map (fun key => key - parent key) rest))
      with (vertex - root) by lia.
    reflexivity.
Qed.

(** The actual descending parent ranks instantiate the suffix-gap credit inequality. *)
Lemma dom_gap_path_levels parent start path root : dom_gap_path parent start path root ->
  length path + dom_gap_weight path (fun vertex => Nat.log2 (vertex - parent vertex)) <=
    Nat.log2 (start - root) + 1 +
      dom_gap_weight path (fun vertex => Nat.log2 (vertex - root)).
Proof.
  intro Hpath.
  pose proof (dom_gap_path_credit _ (dom_gap_path_positive parent start path root Hpath))
    as Hcredit.
  pose proof (dom_gap_path_total parent start path root Hpath) as Htotal.
  rewrite length_map, dom_gap_path_before,
    (dom_gap_path_after parent start path root Hpath) in Hcredit.
  replace (dom_gap_total (map (fun vertex => vertex - parent vertex) path))
    with (start - root) in Hcredit by lia.
  exact Hcredit.
Qed.

(** Pointwise growth decomposes total weight into its old value and nonnegative gain. *)
Lemma dom_gap_weight_increase : forall domain before after,
  (forall vertex, In vertex domain -> before vertex <= after vertex) ->
  dom_gap_weight domain after = dom_gap_weight domain before +
    dom_gap_weight domain (fun vertex => after vertex - before vertex).
Proof.
  intro domain. induction domain as [|vertex rest IH]; intros before after Hgrow;
    [reflexivity|].
  pose proof (Hgrow vertex ltac:(now left)) as Hhead.
  specialize (IH before after ltac:(intros key Hin; apply Hgrow; now right)).
  change (after vertex + dom_gap_weight rest after =
    before vertex + dom_gap_weight rest before +
      (after vertex - before vertex +
        dom_gap_weight rest (fun key => after key - before key))).
  lia.
Qed.

(** A unique compression path draws its level increase from the full forest potential. *)
Lemma dom_gap_credit_transport domain path before after charge :
  NoDup path -> incl path domain ->
  (forall vertex, In vertex domain -> before vertex <= after vertex) ->
  length path + dom_gap_weight path before <= charge + dom_gap_weight path after ->
  length path + dom_gap_weight domain before <= charge + dom_gap_weight domain after.
Proof.
  intros Hunique Hincl Hgrow Hpath.
  pose proof (dom_gap_weight_increase domain before after Hgrow) as Hdomain.
  pose proof (dom_gap_weight_increase path before after
    ltac:(intros vertex Hin; apply Hgrow; now apply Hincl)) as Hlocal.
  pose proof (dom_nodup_sum_incl (fun vertex => after vertex - before vertex)
    path domain Hunique Hincl) as Hgain.
  change (dom_gap_weight path (fun vertex => after vertex - before vertex) <=
    dom_gap_weight domain (fun vertex => after vertex - before vertex)) in Hgain.
  lia.
Qed.

(** Positive gaps pay for the number of traversed shortcuts. *)
Lemma dom_gap_length_total gaps : Forall (fun gap => 0 < gap) gaps ->
  length gaps <= dom_gap_total gaps.
Proof.
  intro Hpositive. induction Hpositive as [|gap rest Hgap Hrest IH]; [reflexivity|].
  change (S (length rest) <= gap + dom_gap_total rest). lia.
Qed.

(** * Guarded shortcut paths and forest levels *)

Definition dom_lt_parent_rank (links : dom_lt_links) (vertex : nat) : nat :=
  N.to_nat (dom_lt_identity (lt_shortcut links) (N.of_nat vertex)).

Inductive dom_lt_walk_path (links : dom_lt_links) : N -> list N -> N -> Prop :=
  | dom_lt_walk_path_stop root :
      (forall parent, trie_get (dom_lt_key root) (lt_shortcut links) = Some parent ->
        ~ (parent < root)%N) ->
      dom_lt_walk_path links root [] root
  | dom_lt_walk_path_step vertex parent rest root :
      trie_get (dom_lt_key vertex) (lt_shortcut links) = Some parent ->
      (parent < vertex)%N -> dom_lt_walk_path links parent rest root ->
      dom_lt_walk_path links vertex (vertex :: rest) root.

(** The executable strict-rank test gives a finite path even for malformed raw forests. *)
Lemma dom_lt_walk_path_exists links : forall start,
  exists path root, dom_lt_walk_path links start path root.
Proof.
  apply (well_founded_induction N.lt_wf_0).
  intros vertex IH.
  destruct (trie_get (dom_lt_key vertex) (lt_shortcut links)) as [parent|] eqn:Hget.
  - destruct (N.ltb parent vertex) eqn:Hless.
    + apply N.ltb_lt in Hless.
      destruct (IH parent Hless) as [rest [root Hpath]].
      exists (vertex :: rest), root. eapply dom_lt_walk_path_step; eassumption.
    + exists [], vertex. apply dom_lt_walk_path_stop.
      intros other Hother Hlt. rewrite Hget in Hother. injection Hother as <-.
      apply N.ltb_ge in Hless. lia.
  - exists [], vertex. apply dom_lt_walk_path_stop.
    intros other Hother. rewrite Hget in Hother. discriminate.
Qed.

Lemma dom_lt_walk_path_natural links start path root :
  dom_lt_walk_path links start path root ->
  dom_gap_path (dom_lt_parent_rank links) (N.to_nat start)
    (map N.to_nat path) (N.to_nat root).
Proof.
  intro Hpath.
  induction Hpath as [root Hstop|vertex parent rest root Hget Hless Hpath IH].
  - apply dom_gap_path_stop.
  - cbn [map]. eapply dom_gap_path_step with (next := N.to_nat parent).
    + unfold dom_lt_parent_rank, dom_lt_identity. rewrite N2Nat.id, Hget. reflexivity.
    + lia.
    + exact IH.
Qed.

Lemma dom_lt_walk_path_bound links start path root :
  dom_lt_walk_path links start path root ->
  length path <= N.to_nat start /\ (root <= start)%N.
Proof.
  intro Hpath. pose proof (dom_lt_walk_path_natural links start path root Hpath) as Hnatural.
  pose proof (dom_gap_path_total _ _ _ _ Hnatural) as Htotal.
  pose proof (dom_gap_length_total _ (dom_gap_path_positive _ _ _ _ Hnatural)) as Hlength.
  rewrite !length_map in Hlength. split; lia.
Qed.

Lemma dom_lt_walk_path_parent links start path root :
  dom_lt_walk_path links start path root -> forall vertex, In vertex path ->
  exists parent, trie_get (dom_lt_key vertex) (lt_shortcut links) = Some parent /\
    (root <= parent < vertex)%N.
Proof.
  intro Hpath.
  induction Hpath as [root Hstop|vertex parent rest root Hget Hless Hpath IH];
    intros key Hin; [contradiction|].
  destruct Hin as [<-|Hin].
  - exists parent. split; [exact Hget|].
    pose proof (proj2 (dom_lt_walk_path_bound links parent rest root Hpath)). lia.
  - now apply IH.
Qed.

Definition dom_lt_forest_level (links : dom_lt_links) (vertex : nat) : nat :=
  Nat.log2 (vertex - dom_lt_parent_rank links vertex).

(** Unlinked cells use their own rank as parent and contribute zero to the bounded sum. *)
Definition dom_lt_forest_levels (bound : nat) (links : dom_lt_links) : nat :=
  dom_gap_weight (seq 0 (S bound)) (dom_lt_forest_level links).

Lemma dom_lt_forest_levels_bound bound links :
  dom_lt_forest_levels bound links <= (bound + 1) * Nat.log2 bound.
Proof.
  unfold dom_lt_forest_levels. replace (bound + 1) with (S bound) by lia.
  pose proof (dom_gap_weight_bound (seq 0 (S bound)) (dom_lt_forest_level links)
    (Nat.log2 bound)) as Hbound.
  rewrite length_seq in Hbound.
  apply Hbound. intros vertex Hin. apply in_seq in Hin.
  unfold dom_lt_forest_level. apply Nat.log2_le_mono. lia.
Qed.

Lemma dom_lt_parent_rank_update_same before after vertex root :
  lt_shortcut after = PTrieCode.set (dom_lt_key vertex) root (lt_shortcut before) ->
  dom_lt_parent_rank after (N.to_nat vertex) = N.to_nat root.
Proof.
  intro Hupdate. unfold dom_lt_parent_rank, dom_lt_identity.
  rewrite N2Nat.id, Hupdate, PTrie.get_set_same. reflexivity.
Qed.

Lemma dom_lt_parent_rank_update_other before after vertex root key :
  lt_shortcut after = PTrieCode.set (dom_lt_key vertex) root (lt_shortcut before) ->
  key <> N.to_nat vertex -> dom_lt_parent_rank after key = dom_lt_parent_rank before key.
Proof.
  intros Hupdate Hne. unfold dom_lt_parent_rank, dom_lt_identity. rewrite Hupdate.
  rewrite PTrie.get_set_other; [reflexivity|].
  intro Heq. apply dom_lt_key_injective in Heq. apply Hne. lia.
Qed.

(** Redirecting a shortcut to an earlier ancestor never decreases a vertex level. *)
Lemma dom_lt_forest_level_grows before after vertex root :
  lt_shortcut after = PTrieCode.set (dom_lt_key vertex) root (lt_shortcut before) ->
  N.to_nat root <= dom_lt_parent_rank before (N.to_nat vertex) ->
  forall key, dom_lt_forest_level before key <= dom_lt_forest_level after key.
Proof.
  intros Hupdate Hearlier key. unfold dom_lt_forest_level.
  destruct (Nat.eq_dec key (N.to_nat vertex)) as [->|Hne].
  - rewrite (dom_lt_parent_rank_update_same before after vertex root Hupdate).
    apply Nat.log2_le_mono. lia.
  - rewrite (dom_lt_parent_rank_update_other before after vertex root key Hupdate Hne).
    reflexivity.
Qed.

(** A newly linked vertex starts with zero shortcut level. *)
Lemma dom_lt_link_levels_grow before vertex parent :
  trie_get (dom_lt_key vertex) (lt_shortcut before) = None ->
  forall key, dom_lt_forest_level before key <=
    dom_lt_forest_level (dom_lt_link before vertex parent) key.
Proof.
  intros Hfresh key.
  destruct (Nat.eq_dec key (N.to_nat vertex)) as [->|Hne].
  - unfold dom_lt_forest_level, dom_lt_parent_rank, dom_lt_identity.
    rewrite N2Nat.id, Hfresh, Nat.sub_diag. apply Nat.le_0_l.
  - unfold dom_lt_forest_level.
    rewrite (dom_lt_parent_rank_update_other before (dom_lt_link before vertex parent)
      vertex parent key eq_refl Hne). reflexivity.
Qed.

Lemma dom_lt_empty_levels bound :
  dom_lt_forest_levels bound (DomLtLinks Empty Empty []) = 0.
Proof.
  unfold dom_lt_forest_levels.
  assert (Hzero : forall domain,
    dom_gap_weight domain (dom_lt_forest_level (DomLtLinks Empty Empty [])) = 0).
  { intro domain. induction domain as [|vertex rest IH]; [reflexivity|].
    change (dom_lt_forest_level (DomLtLinks Empty Empty []) vertex +
      dom_gap_weight rest (dom_lt_forest_level (DomLtLinks Empty Empty [])) = 0).
    rewrite IH. unfold dom_lt_forest_level, dom_lt_parent_rank, dom_lt_identity.
    cbn [lt_shortcut]. rewrite PTrie.get_empty, Nat2N.id, Nat.sub_diag. reflexivity. }
  apply Hzero.
Qed.

Lemma dom_gap_path_parents parent start path root : dom_gap_path parent start path root ->
  forall vertex, In vertex path -> root <= parent vertex < vertex.
Proof.
  intro Hpath. induction Hpath as [root|vertex next rest root Hparent Hless Hpath IH];
    intros key Hin; [contradiction|].
  destruct Hin as [<-|Hin].
  - rewrite Hparent. pose proof (proj1 (dom_gap_path_range parent next rest root Hpath)).
    lia.
  - now apply IH.
Qed.

(** The path's actual shortcut changes pay its length from the bounded forest levels. *)
Lemma dom_lt_compression_credit bound before after start path root :
  dom_lt_walk_path before start path root -> N.to_nat start <= bound ->
  (forall key, In key (map N.to_nat path) -> dom_lt_parent_rank after key = N.to_nat root) ->
  (forall key, ~ In key (map N.to_nat path) ->
    dom_lt_parent_rank after key = dom_lt_parent_rank before key) ->
  length path + dom_lt_forest_levels bound before <=
    Nat.log2 bound + 1 + dom_lt_forest_levels bound after.
Proof.
  intros Hpath Hstart Hcompressed Houtside.
  pose proof (dom_lt_walk_path_natural before start path root Hpath) as Hnatural.
  pose proof (dom_gap_path_range _ _ _ _ Hnatural) as Hrange.
  assert (Hincl : incl (map N.to_nat path) (seq 0 (S bound))).
  { intros key Hin. apply in_seq.
    pose proof (proj2 Hrange key Hin). lia. }
  assert (Hgrow : forall key, In key (seq 0 (S bound)) ->
    dom_lt_forest_level before key <= dom_lt_forest_level after key).
  { intros key Hin. unfold dom_lt_forest_level.
    destruct (in_dec Nat.eq_dec key (map N.to_nat path)) as [Hpathkey|Hother].
    - rewrite (Hcompressed key Hpathkey). apply Nat.log2_le_mono.
      pose proof (dom_gap_path_parents _ _ _ _ Hnatural key Hpathkey). lia.
    - rewrite (Houtside key Hother). reflexivity. }
  assert (Hafter : dom_gap_weight (map N.to_nat path) (dom_lt_forest_level after) =
    dom_gap_weight (map N.to_nat path) (fun key => Nat.log2 (key - N.to_nat root))).
  { apply dom_gap_weight_ext. intros key Hin. unfold dom_lt_forest_level.
    now rewrite (Hcompressed key Hin). }
  pose proof (dom_gap_path_levels _ _ _ _ Hnatural) as Hlocal.
  change (length (map N.to_nat path) +
    dom_gap_weight (map N.to_nat path) (dom_lt_forest_level before) <=
    Nat.log2 (N.to_nat start - N.to_nat root) + 1 +
      dom_gap_weight (map N.to_nat path) (fun key => Nat.log2 (key - N.to_nat root)))
    in Hlocal.
  rewrite <- Hafter in Hlocal.
  pose proof (dom_gap_credit_transport (seq 0 (S bound)) (map N.to_nat path)
    (dom_lt_forest_level before) (dom_lt_forest_level after)
    (Nat.log2 (N.to_nat start - N.to_nat root) + 1)
    (dom_gap_path_unique _ _ _ _ Hnatural) Hincl Hgrow Hlocal) as Hglobal.
  rewrite length_map in Hglobal.
  pose proof (Nat.log2_le_mono (N.to_nat start - N.to_nat root) bound ltac:(lia)) as Hlog.
  unfold dom_lt_forest_levels. lia.
Qed.

(** * Compression shape and remaining frames *)

(** Pending frames retain their old parents, completed frames point to the root, and cells
    outside the unique path stay unchanged. *)
Definition dom_lt_unwind_shape (before current : dom_lt_links) (path stack : list N)
    (root : N) : Prop :=
  incl (map N.to_nat stack) (map N.to_nat path) /\
  NoDup (map N.to_nat stack) /\
  (forall key, In key (map N.to_nat stack) ->
    dom_lt_parent_rank current key = dom_lt_parent_rank before key) /\
  (forall key, In key (map N.to_nat path) -> ~ In key (map N.to_nat stack) ->
    dom_lt_parent_rank current key = N.to_nat root) /\
  (forall key, ~ In key (map N.to_nat path) ->
    dom_lt_parent_rank current key = dom_lt_parent_rank before key).

Lemma dom_lt_unwind_shape_initial before current path stack root :
  lt_shortcut current = lt_shortcut before ->
  NoDup (map N.to_nat stack) ->
  (forall key, In key (map N.to_nat stack) <-> In key (map N.to_nat path)) ->
  dom_lt_unwind_shape before current path stack root.
Proof.
  intros Hsame Hunique Hmembers.
  assert (Hrank : forall key, dom_lt_parent_rank current key = dom_lt_parent_rank before key).
  { intro key. unfold dom_lt_parent_rank. now rewrite Hsame. }
  split; [intros key Hin; now apply Hmembers|]. split; [exact Hunique|].
  split; [intros key Hin; apply Hrank|].
  split; [|intros key Hin; apply Hrank].
  intros key Hin Hnot. exfalso. apply Hnot. now apply Hmembers.
Qed.

(** One unwind update completes its unique head and preserves all other pending cells. *)
Lemma dom_lt_unwind_shape_step before current next path vertex stack root :
  dom_lt_unwind_shape before current path (vertex :: stack) root ->
  lt_shortcut next = PTrieCode.set (dom_lt_key vertex) root (lt_shortcut current) ->
  dom_lt_unwind_shape before next path stack root.
Proof.
  intros [Hincl [Hunique [Hpending [Hdone Houtside]]]] Hupdate.
  cbn [map] in Hunique, Hpending, Hdone, Hincl.
  inversion Hunique as [|head tail Hfresh Htail]; subst head tail.
  assert (Hvertex : In (N.to_nat vertex) (map N.to_nat path)).
  { apply Hincl. now left. }
  split; [intros key Hin; apply Hincl; now right|]. split; [exact Htail|].
  split.
  - intros key Hin.
    rewrite (dom_lt_parent_rank_update_other current next vertex root key Hupdate).
    + apply Hpending. now right.
    + intro Heq. subst key. contradiction.
  - split.
    + intros key Hin Hnot.
      destruct (Nat.eq_dec key (N.to_nat vertex)) as [->|Hne].
      * exact (dom_lt_parent_rank_update_same current next vertex root Hupdate).
      * rewrite (dom_lt_parent_rank_update_other current next vertex root key Hupdate Hne).
        apply Hdone; [exact Hin|]. intros [Heq|Hrest]; [congruence|contradiction].
    + intros key Hnot.
      rewrite (dom_lt_parent_rank_update_other current next vertex root key Hupdate).
      * now apply Houtside.
      * intro Heq. subst key. contradiction.
Qed.

Lemma dom_lt_unwind_shape_finished before current path root :
  dom_lt_unwind_shape before current path [] root ->
  (forall key, In key (map N.to_nat path) -> dom_lt_parent_rank current key = N.to_nat root) /\
  (forall key, ~ In key (map N.to_nat path) ->
    dom_lt_parent_rank current key = dom_lt_parent_rank before key).
Proof.
  intros [Hincl [Hunique [Hpending [Hdone Houtside]]]]. split; [|exact Houtside].
  intros key Hin. apply Hdone; [exact Hin|]. cbn. tauto.
Qed.

Definition dom_lt_compress_shape (before : dom_lt_links) (path : list N) (root : N)
    (st : dom_lt_walk) : Prop :=
  match lt_walk_phase st with
  | DomLtDescend vertex stack =>
      lt_shortcut (lt_walk_links st) = lt_shortcut before /\
      exists rest, dom_lt_walk_path before vertex rest root /\ path = rev stack ++ rest
  | DomLtUnwind current_root part stack =>
      current_root = root /\ dom_lt_unwind_shape before (lt_walk_links st) path stack root
  end.

(** Descent spends one frame per saved vertex; turning leaves only the unwind stack. *)
Definition dom_lt_compress_frames (count : nat) (st : dom_lt_walk) : nat :=
  match lt_walk_phase st with
  | DomLtDescend _ stack => 2 * count - length stack + 1
  | DomLtUnwind _ _ stack => length stack
  end.

Lemma dom_lt_compress_turn before current path stack root :
  lt_shortcut current = lt_shortcut before -> NoDup (map N.to_nat path) ->
  path = rev stack ->
  dom_lt_compress_shape before path root (DomLtWalk current (DomLtUnwind root None stack)) /\
  dom_lt_compress_frames (length path) (DomLtWalk current (DomLtUnwind root None stack)) <
    dom_lt_compress_frames (length path) (DomLtWalk current (DomLtDescend root stack)).
Proof.
  intros Hsame Hunique Hpath. split.
  - cbn [dom_lt_compress_shape lt_walk_phase lt_walk_links]. split; [reflexivity|].
    apply dom_lt_unwind_shape_initial; [exact Hsame| |].
    + rewrite Hpath, map_rev in Hunique. apply NoDup_rev in Hunique.
      now rewrite rev_involutive in Hunique.
    + intro key. rewrite Hpath, map_rev. apply in_rev.
  - cbn [dom_lt_compress_frames lt_walk_phase]. rewrite Hpath, length_rev. lia.
Qed.

Lemma dom_lt_compress_descend before path root semis current vertex stack rest next :
  lt_shortcut current = lt_shortcut before -> NoDup (map N.to_nat path) ->
  dom_lt_walk_path before vertex rest root -> path = rev stack ++ rest ->
  dom_lt_compress_step semis (DomLtWalk current (DomLtDescend vertex stack)) = inl next ->
  dom_lt_compress_shape before path root next /\
  dom_lt_compress_frames (length path) next <
    dom_lt_compress_frames (length path) (DomLtWalk current (DomLtDescend vertex stack)).
Proof.
  intros Hsame Hunique Hpath Hfull Hstep.
  destruct Hpath as [terminal Hstop|head parent remaining terminal Hget Hless Htail].
  - rewrite app_nil_r in Hfull.
    cbn [dom_lt_compress_step lt_walk_phase lt_walk_links] in Hstep.
    rewrite Hsame in Hstep.
    destruct (trie_get (dom_lt_key terminal) (lt_shortcut before)) as [parent|] eqn:Hget.
    + assert (Hcmp : N.ltb parent terminal = false).
      { apply N.ltb_ge. specialize (Hstop parent eq_refl). lia. }
      rewrite Hcmp in Hstep. injection Hstep as <-.
      exact (dom_lt_compress_turn before current path stack terminal Hsame Hunique Hfull).
    + injection Hstep as <-.
      exact (dom_lt_compress_turn before current path stack terminal Hsame Hunique Hfull).
  - cbn [dom_lt_compress_step lt_walk_phase lt_walk_links] in Hstep.
    rewrite Hsame, Hget in Hstep.
    assert (Hcmp : N.ltb parent head = true) by now apply N.ltb_lt.
    rewrite Hcmp in Hstep. injection Hstep as <-. split.
    + cbn [dom_lt_compress_shape lt_walk_phase lt_walk_links]. split; [exact Hsame|].
      exists remaining. split; [exact Htail|]. rewrite Hfull. cbn [rev].
      rewrite <- app_assoc. reflexivity.
    + cbn [dom_lt_compress_frames lt_walk_phase length].
      rewrite Hfull, length_app, length_rev. cbn [length]. lia.
Qed.

Lemma dom_lt_compress_shape_step before path root semis st next :
  NoDup (map N.to_nat path) -> dom_lt_compress_shape before path root st ->
  dom_lt_compress_step semis st = inl next ->
  dom_lt_compress_shape before path root next /\
    dom_lt_compress_frames (length path) next < dom_lt_compress_frames (length path) st.
Proof.
  intros Hunique Hshape Hstep. destruct st as [current [vertex stack|current_root part stack]].
  - cbn [dom_lt_compress_shape lt_walk_phase lt_walk_links] in Hshape.
    destruct Hshape as [Hsame [rest [Hpath Hfull]]].
    eapply dom_lt_compress_descend; eassumption.
  - cbn [dom_lt_compress_shape lt_walk_phase lt_walk_links] in Hshape.
    destruct Hshape as [-> Hunwind].
    destruct stack as [|vertex stack].
    + cbn [dom_lt_compress_step lt_walk_phase lt_walk_links] in Hstep. discriminate.
    + cbn [dom_lt_compress_step lt_walk_phase lt_walk_links] in Hstep.
      injection Hstep as <-. split.
      * cbn [dom_lt_compress_shape lt_walk_phase lt_walk_links]. split; [reflexivity|].
        eapply dom_lt_unwind_shape_step; [exact Hunwind|reflexivity].
      * cbn [dom_lt_compress_frames lt_walk_phase length]. lia.
Qed.

Lemma dom_lt_compress_shape_stop before path root semis st result :
  dom_lt_compress_shape before path root st -> dom_lt_compress_step semis st = inr result ->
  dom_lt_unwind_shape before (fst result) path [] root.
Proof.
  intros Hshape Hstep. destruct st as [current [vertex stack|current_root part stack]].
  - cbn [dom_lt_compress_step lt_walk_phase lt_walk_links] in Hstep.
    destruct (trie_get (dom_lt_key vertex) (lt_shortcut current)) as [parent|];
      [destruct (N.ltb parent vertex)|]; discriminate.
  - cbn [dom_lt_compress_shape lt_walk_phase lt_walk_links] in Hshape.
    destruct Hshape as [-> Hunwind]. destruct stack as [|vertex stack].
    + cbn [dom_lt_compress_step lt_walk_phase lt_walk_links] in Hstep.
      injection Hstep as <-. exact Hunwind.
    + cbn [dom_lt_compress_step lt_walk_phase lt_walk_links] in Hstep. discriminate.
Qed.

(** Sufficient binary fuel completes exactly the guarded path and compresses every frame. *)
Lemma dom_lt_eval_compressed fuel semis before start path root :
  dom_lt_walk_path before start path root -> (start <= fuel)%N ->
  dom_lt_unwind_shape before (fst (dom_lt_eval fuel semis before start)) path [] root.
Proof.
  intros Hpath Hfuel.
  pose proof (dom_lt_walk_path_natural before start path root Hpath) as Hnatural.
  pose proof (dom_gap_path_unique _ _ _ _ Hnatural) as Hunique.
  pose proof (proj1 (dom_lt_walk_path_bound before start path root Hpath)) as Hlength.
  set (initial := DomLtWalk
    (DomLtLinks (lt_shortcut before) (lt_label before) (LtEval start :: lt_operations before))
    (DomLtDescend start [])).
  assert (Hinitial : dom_lt_compress_shape before path root initial).
  { unfold initial. cbn [dom_lt_compress_shape lt_walk_phase lt_walk_links lt_shortcut].
    split; [reflexivity|]. exists path. split; [exact Hpath|reflexivity]. }
  assert (Hgo : forall st next, dom_lt_compress_shape before path root st ->
    dom_lt_compress_step semis st = inl next ->
    dom_lt_compress_shape before path root next /\
      dom_lt_compress_frames (length path) next < dom_lt_compress_frames (length path) st).
  { intros st next Hshape Hstep.
    exact (dom_lt_compress_shape_step before path root semis st next Hunique Hshape Hstep). }
  assert (Hroom : (N.of_nat (dom_lt_compress_frames (length path) initial) <
    N.double fuel + 3)%N).
  { change (N.of_nat (2 * length path - 0 + 1) < N.double fuel + 3)%N.
    rewrite Nat.sub_0_r, N.double_spec, !Nat2N.inj_add, !Nat2N.inj_mul. lia. }
  destruct (loopN_done _ _ (dom_lt_compress_step semis)
    (dom_lt_compress_shape before path root) (dom_lt_compress_frames (length path))
    (N.double fuel + 3)%N initial Hgo Hinitial Hroom) as [result Hrun].
  pose proof (dom_lt_loop_invariant (dom_lt_compress_step semis)
    (dom_lt_compress_shape before path root)
    (fun result => dom_lt_unwind_shape before (fst result) path [] root)
    (N.double fuel + 3)%N initial
    (fun st next Hshape Hstep => proj1 (Hgo st next Hshape Hstep))
    (fun st result Hshape Hstep =>
      dom_lt_compress_shape_stop before path root semis st result Hshape Hstep)
    Hinitial) as Hresult.
  rewrite Hrun in Hresult. unfold dom_lt_eval. fold initial. rewrite Hrun. exact Hresult.
Qed.

Lemma dom_lt_eval_level_credit bound fuel semis before start path root :
  dom_lt_walk_path before start path root -> N.to_nat start <= bound -> (start <= fuel)%N ->
  length path + dom_lt_forest_levels bound before <= Nat.log2 bound + 1 +
    dom_lt_forest_levels bound (fst (dom_lt_eval fuel semis before start)).
Proof.
  intros Hpath Hbound Hfuel.
  pose proof (dom_lt_eval_compressed fuel semis before start path root Hpath Hfuel) as Hshape.
  destruct (dom_lt_unwind_shape_finished before
    (fst (dom_lt_eval fuel semis before start)) path root Hshape) as [Hinside Houtside].
  eapply dom_lt_compression_credit; eassumption.
Qed.

(** The binary loop charges the remaining frames and only the initial fuel's bit length. *)
Lemma dom_lt_compress_path_time before path root semis (Inv : dom_lt_walk -> Prop)
    unit fuel initial :
  NoDup (map N.to_nat path) -> dom_lt_compress_shape before path root initial -> Inv initial ->
  (forall state next, Inv state -> dom_lt_compress_step semis state = inl next -> Inv next) ->
  (forall state, Inv state -> (T_dom_lt_compress_step semis state <= unit)%N) ->
  (T_loopN (dom_lt_compress_step semis) (T_dom_lt_compress_step semis) fuel initial <=
    c_loopN * ((unit + 1) * N.of_nat (dom_lt_compress_frames (length path) initial) +
      unit + N.of_nat (N.size_nat fuel) + 1))%N.
Proof.
  intros Hunique Hshape Hinitial Hpreserve Hcost.
  apply (T_loopN_le _ _ (dom_lt_compress_step semis) (T_dom_lt_compress_step semis)
    (fun state => dom_lt_compress_shape before path root state /\ Inv state)
    (fun state => ((unit + 1) * N.of_nat (dom_lt_compress_frames (length path) state))%N)
    unit fuel initial).
  - intros state next [Hstate Hinv] Hstep.
    destruct (dom_lt_compress_shape_step before path root semis state next
      Hunique Hstate Hstep) as [Hnext Hframes].
    split; [split; [exact Hnext|now apply (Hpreserve state next)]|].
    pose proof (Hcost state Hinv) as Htime. cbn beta. nia.
  - intros state result [Hstate Hinv] Hstep. now apply Hcost.
  - now split.
Qed.

(** * Shortcut domains and remaining forest credit *)

Definition dom_lt_shortcut_domain (before current : dom_lt_links) : Prop :=
  forall key, trie_get key (lt_shortcut current) = None <->
    trie_get key (lt_shortcut before) = None.

Lemma dom_lt_shortcut_domain_update before current next vertex root :
  dom_lt_shortcut_domain before current ->
  trie_get (dom_lt_key vertex) (lt_shortcut before) <> None ->
  lt_shortcut next = PTrieCode.set (dom_lt_key vertex) root (lt_shortcut current) ->
  dom_lt_shortcut_domain before next.
Proof.
  intros Hdomain Hpresent Hupdate key. rewrite Hupdate.
  destruct (Pos.eq_dec key (dom_lt_key vertex)) as [->|Hne].
  - rewrite PTrie.get_set_same. split; [discriminate|intro Hnone; contradiction].
  - rewrite PTrie.get_set_other by exact Hne. apply Hdomain.
Qed.

(** Every pending frame names a cell already present before evaluation began. *)
Definition dom_lt_walk_domain (before : dom_lt_links) (st : dom_lt_walk) : Prop :=
  dom_lt_shortcut_domain before (lt_walk_links st) /\
  Forall (fun vertex => trie_get (dom_lt_key vertex) (lt_shortcut before) <> None)
    (match lt_walk_phase st with
      | DomLtDescend _ stack | DomLtUnwind _ _ stack => stack
      end).

(** Every saved frame already has a shortcut; unwinding cannot create a fresh cell. *)
Lemma dom_lt_compress_domain before semis st : dom_lt_walk_domain before st ->
  match dom_lt_compress_step semis st with
  | inl next => dom_lt_walk_domain before next
  | inr result => dom_lt_shortcut_domain before (fst result)
  end.
Proof.
  destruct st as [current [vertex stack|root part stack]];
    cbn [dom_lt_walk_domain lt_walk_links lt_walk_phase]; intros [Hdomain Hstack].
  - cbn [dom_lt_compress_step lt_walk_links lt_walk_phase].
    destruct (trie_get (dom_lt_key vertex) (lt_shortcut current)) as [parent|] eqn:Hget.
    + destruct (N.ltb parent vertex).
      * split; [exact Hdomain|]. constructor; [|exact Hstack].
        intro Hnone.
        assert (Habsent : trie_get (dom_lt_key vertex) (lt_shortcut current) = None).
        { exact (proj2 (Hdomain (dom_lt_key vertex)) Hnone). }
        rewrite Hget in Habsent. discriminate.
      * now split.
    + now split.
  - destruct stack as [|vertex stack].
    + cbn [dom_lt_compress_step lt_walk_links lt_walk_phase fst]. exact Hdomain.
    + inversion Hstack as [|head tail Hpresent Htail]; subst head tail.
      cbn [dom_lt_compress_step lt_walk_links lt_walk_phase]. split; [|exact Htail].
      eapply dom_lt_shortcut_domain_update; [exact Hdomain|exact Hpresent|reflexivity].
Qed.

(** Domain preservation is independent of fuel exhaustion and semidominator scores. *)
Lemma dom_lt_eval_domain fuel semis before vertex :
  dom_lt_shortcut_domain before (fst (dom_lt_eval fuel semis before vertex)).
Proof.
  set (initial := DomLtWalk
    (DomLtLinks (lt_shortcut before) (lt_label before) (LtEval vertex :: lt_operations before))
    (DomLtDescend vertex [])).
  assert (Hinitial : dom_lt_walk_domain before initial).
  { split; [intro key; reflexivity|constructor]. }
  pose proof (dom_lt_loop_invariant (dom_lt_compress_step semis)
    (dom_lt_walk_domain before) (fun result => dom_lt_shortcut_domain before (fst result))
    (N.double fuel + 3)%N initial) as Hrun.
  assert (Hgo : forall state next, dom_lt_walk_domain before state ->
    dom_lt_compress_step semis state = inl next -> dom_lt_walk_domain before next).
  { intros state next Hinv Hstep.
    pose proof (dom_lt_compress_domain before semis state Hinv) as Hnext.
    now rewrite Hstep in Hnext. }
  assert (Hstop : forall state result, dom_lt_walk_domain before state ->
    dom_lt_compress_step semis state = inr result -> dom_lt_shortcut_domain before (fst result)).
  { intros state result Hinv Hstep.
    pose proof (dom_lt_compress_domain before semis state Hinv) as Hnext.
    now rewrite Hstep in Hnext. }
  specialize (Hrun Hgo Hstop Hinitial).
  unfold dom_lt_eval. fold initial.
  destruct (loopN (dom_lt_compress_step semis) (N.double fuel + 3)%N initial)
    as [state|result]; [exact (proj1 Hrun)|exact Hrun].
Qed.

Lemma dom_gap_weight_mono : forall domain before after,
  (forall key, In key domain -> before key <= after key) ->
  dom_gap_weight domain before <= dom_gap_weight domain after.
Proof.
  intro domain. induction domain as [|key rest IH]; intros before after Hmono;
    [reflexivity|].
  pose proof (Hmono key ltac:(now left)) as Hhead.
  specialize (IH before after ltac:(intros vertex Hin; apply Hmono; now right)).
  change (before key + dom_gap_weight rest before <= after key + dom_gap_weight rest after).
  lia.
Qed.

(** The unused part of the level bound pays for future path-compression work. *)
Definition dom_lt_forest_credit (bound : nat) (links : dom_lt_links) : N :=
  N.of_nat ((bound + 1) * Nat.log2 bound - dom_lt_forest_levels bound links).

Lemma dom_lt_forest_credit_bound bound links :
  (dom_lt_forest_credit bound links <= N.of_nat ((bound + 1) * Nat.log2 bound))%N.
Proof.
  unfold dom_lt_forest_credit. lia.
Qed.

Lemma dom_lt_empty_credit bound :
  dom_lt_forest_credit bound (DomLtLinks Empty Empty []) =
    N.of_nat ((bound + 1) * Nat.log2 bound).
Proof.
  unfold dom_lt_forest_credit. rewrite dom_lt_empty_levels, Nat.sub_0_r. reflexivity.
Qed.

Lemma dom_lt_link_credit bound before vertex parent :
  trie_get (dom_lt_key vertex) (lt_shortcut before) = None ->
  (dom_lt_forest_credit bound (dom_lt_link before vertex parent) <=
    dom_lt_forest_credit bound before)%N.
Proof.
  intro Hfresh.
  assert (Hgrow : dom_lt_forest_levels bound before <=
    dom_lt_forest_levels bound (dom_lt_link before vertex parent)).
  { apply dom_gap_weight_mono. intros key Hin. now apply dom_lt_link_levels_grow. }
  unfold dom_lt_forest_credit. lia.
Qed.

Definition dom_lt_links_fresh (links : dom_lt_links) (children : list N) : Prop :=
  forall vertex, In vertex children -> trie_get (dom_lt_key vertex) (lt_shortcut links) = None.

Lemma dom_lt_empty_fresh children : dom_lt_links_fresh (DomLtLinks Empty Empty []) children.
Proof.
  intros vertex Hin. apply PTrie.get_empty.
Qed.

Lemma dom_lt_eval_fresh fuel semis before vertex children :
  dom_lt_links_fresh before children ->
  dom_lt_links_fresh (fst (dom_lt_eval fuel semis before vertex)) children.
Proof.
  intros Hfresh child Hin.
  apply (proj2 (dom_lt_eval_domain fuel semis before vertex (dom_lt_key child))).
  now apply Hfresh.
Qed.

Lemma dom_lt_link_fresh before vertex parent children :
  ~ In vertex children -> dom_lt_links_fresh before children ->
  dom_lt_links_fresh (dom_lt_link before vertex parent) children.
Proof.
  intros Hnew Hfresh child Hin. cbn [dom_lt_link lt_shortcut].
  rewrite PTrie.get_set_other; [now apply Hfresh|].
  intro Heq. apply dom_lt_key_injective in Heq. subst child. contradiction.
Qed.

Lemma dom_lt_replay_fields st op :
  replay_semis (dom_lt_replay_step st op) = replay_semis st /\
  replay_fuel (dom_lt_replay_step st op) = replay_fuel st /\
  replay_boundary (dom_lt_replay_step st op) = replay_boundary st /\
  replay_index (dom_lt_replay_step st op) = N.succ (replay_index st).
Proof.
  repeat split; reflexivity.
Qed.

Lemma dom_lt_replay_index ops : forall st,
  replay_index (dom_lt_run_ops ops st) = (replay_index st + N.of_nat (length ops))%N.
Proof.
  induction ops as [|op rest IH]; intro st.
  - unfold dom_lt_run_ops. cbn [fold_left length]. now rewrite N.add_0_r.
  - change (replay_index (dom_lt_run_ops rest (dom_lt_replay_step st op)) =
      replay_index st + N.of_nat (S (length rest)))%N.
    rewrite IH, (proj2 (proj2 (proj2 (dom_lt_replay_fields st op)))). lia.
Qed.
