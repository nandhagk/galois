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
