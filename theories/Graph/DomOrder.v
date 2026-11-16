(** * Low-high order construction

    The producer derives sibling sources and inserts children beside recorded anchors.
    For example, a join without a parent edge needs sibling sources on both sides.
    Builds on: the numeric Lengauer and Tarjan producer and binary-fuel loops. *)

From Stdlib Require Import List Bool PArith NArith Arith Lia.
From Argent Require Import Time Tactics Std Loop.
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
  unfold T_dom_lt_identity. PTrieT.trie_get_le.
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
  PTrieT.trie_get_le. rewrite !Nat2N.inj_add in *. nia.
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
  PTrieT.trie_get_le. time_simpl.
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
    fold row. time_simpl.
    clearbody row. clear -Hv Hs Hvkey Hvwidth Hskey Hswidth Hset.
    PTrieT.trie_get_le.
    rewrite !Nat2N.inj_add in *. nia.
  - time_simpl.
    clear -Hv Hvkey Hvwidth. PTrieT.trie_get_le. rewrite !Nat2N.inj_add in *. nia.
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
    time_simpl; PTrieT.trie_get_le;
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
      time_simpl. PTrieT.trie_get_le. rewrite !Nat2N.inj_add in *. nia.
    + pose proof (PTrieT.T_set_le N (dom_lt_key v) (dom_lt_identity corrected p) corrected)
        as Hset.
      change (PTrieCode.T_set (dom_lt_key v) (dom_lt_identity corrected p) corrected <=
        PTrieT.c_trie * N.of_nat (Pos.size_nat (dom_lt_key v) + 1))%N in Hset.
      time_simpl. PTrieT.trie_get_le. rewrite !Nat2N.inj_add in *. nia.
  - time_simpl. PTrieT.trie_get_le. rewrite !Nat2N.inj_add in *. nia.
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
    PTrieT.trie_get_le; lia.
Qed.

(** Reading a prepared predecessor row has only an original-key trie lookup. *)
Lemma dom_lt_pipeline_preds_clock g v :
  (T_preds g v <= 2 * N.of_nat (Pos.size_nat v) + 2)%N.
Proof.
  destruct g as [graph predecessors vertex_count edge_count].
  unfold T_preds. time_simpl. PTrieT.trie_get_le. lia.
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
    clear -Hwidth; PTrieT.trie_get_le; rewrite !Nat2N.inj_add in *; lia)).
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
    time_simpl.
    clearbody rank key.
    clear -Hv Hrank Hrankget Hkey Hkeywidth Hpreds Hranked Hsetpred Hsetvertex
      Hparent Hparentget Hsetparent.
    PTrieT.trie_get_le.
    rewrite !Nat2N.inj_mul, !Nat2N.inj_add in *. nia.
  - time_simpl.
    clearbody rank key.
    clear -Hv Hrank Hrankget Hkey Hkeywidth Hpreds Hranked Hsetpred Hsetvertex.
    PTrieT.trie_get_le.
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
       time_simpl; PTrieT.trie_get_le;
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

(** * Generated compression clocks and amortized evaluation *)

(** The callback bounds use the public loop contract rather than reducing its driver. *)
Local Opaque Argent.Loop.loop T_loopN.

(** Selecting the lower score costs a bounded number of numeric-width operations. *)
Lemma dom_lt_time_minimum bound width semis left right :
  dom_lt_trie_all (fun value => (value <= bound)%N) semis ->
  (forall value, (value <= bound)%N -> N.size_nat value <= width) ->
  (left <= bound)%N -> (right <= bound)%N ->
  (T_dom_lt_minimum semis left right <= 32 * N.of_nat (width + 1))%N.
Proof.
  intros Hsemis Hwidth Hleft Hright.
  pose proof (dom_lt_time_identity semis left) as Hleft_time.
  pose proof (dom_lt_time_identity semis right) as Hright_time.
  pose proof (dom_lt_identity_bounded bound semis right Hsemis Hright) as Hscore.
  pose proof (Hwidth left Hleft) as Hleft_width.
  pose proof (Hwidth right Hright) as Hright_width.
  pose proof (Hwidth (dom_lt_identity semis right) Hscore) as Hscore_width.
  pose proof (dom_lt_time_ltb (dom_lt_identity semis right) (dom_lt_identity semis left)) as Hlt.
  unfold T_dom_lt_minimum.
  destruct (N.ltb (dom_lt_identity semis right) (dom_lt_identity semis left));
    time_simpl; rewrite !Nat2N.inj_add in *; lia.
Qed.

(** One compression transition costs a constant multiple of the bounded key width. *)
Lemma dom_lt_time_compress_step bound width semis st :
  dom_lt_trie_all (fun value => (value <= bound)%N) semis ->
  (forall value, (value <= bound)%N -> N.size_nat value <= width) ->
  dom_lt_walk_bounded bound st ->
  (T_dom_lt_compress_step semis st <=
    128 * (PTrieT.c_trie + 1) * N.of_nat (width + 1))%N.
Proof.
  intros Hsemis Hwidth. destruct st as [links [vertex stack|root part stack]].
  - cbn [dom_lt_walk_bounded lt_walk_links lt_walk_phase].
    intros [[Hshort Hlabels] [Hvertex Hstack]].
    pose proof (Hwidth vertex Hvertex) as Hvertex_width.
    pose proof (dom_lt_key_width vertex) as Hkey_width.
    pose proof (dom_lt_time_key vertex) as Hkey_time.
    unfold T_dom_lt_compress_step. cbn [lt_walk_links lt_walk_phase].
    destruct (trie_get (dom_lt_key vertex) (lt_shortcut links)) as [parent|] eqn:Hget.
    + pose proof (Hshort (dom_lt_key vertex) parent Hget) as Hparent.
      pose proof (Hwidth parent Hparent) as Hparent_width.
      pose proof (dom_lt_time_ltb parent vertex) as Hcompare.
      destruct (N.ltb parent vertex); time_simpl;
        clear -Hvertex_width Hkey_width Hkey_time Hparent_width Hcompare;
        PTrieT.trie_get_le; rewrite !Nat2N.inj_add in *; nia.
    + time_simpl.
      clear -Hvertex_width Hkey_width Hkey_time. PTrieT.trie_get_le.
      rewrite !Nat2N.inj_add in *. nia.
  - cbn [dom_lt_walk_bounded lt_walk_links lt_walk_phase].
    intros [[Hshort Hlabels] [Hroot [Hpart Hstack]]].
    destruct stack as [|vertex stack].
    + unfold T_dom_lt_compress_step. cbn [lt_walk_links lt_walk_phase].
      destruct part; time_simpl; rewrite Nat2N.inj_add; nia.
    + inversion Hstack as [|head tail Hvertex Htail]; subst head tail.
      set (label := dom_lt_identity (lt_label links) vertex).
      set (previous := match part with None => 0%N | Some value => value end).
      set (best := match part with None => label |
        Some value => dom_lt_minimum semis label value end).
      assert (Hlabel : (label <= bound)%N).
      { unfold label. now apply dom_lt_identity_bounded. }
      assert (Hprevious : (previous <= bound)%N).
      { unfold previous. destruct part; [exact Hpart|lia]. }
      pose proof (Hwidth vertex Hvertex) as Hvertex_width.
      pose proof (dom_lt_key_width vertex) as Hkey_width.
      pose proof (dom_lt_time_key vertex) as Hkey_time.
      pose proof (dom_lt_time_identity (lt_label links) vertex) as Hlabel_time.
      pose proof (dom_lt_time_minimum bound width semis label previous
        Hsemis Hwidth Hlabel Hprevious) as Hmin_time.
      pose proof (PTrieT.T_set_le N (dom_lt_key vertex) root (lt_shortcut links)) as Hshort_set.
      pose proof (PTrieT.T_set_le N (dom_lt_key vertex) best (lt_label links)) as Hlabel_set.
      change (PTrieCode.T_set (dom_lt_key vertex) root (lt_shortcut links) <=
        PTrieT.c_trie * N.of_nat (Pos.size_nat (dom_lt_key vertex) + 1))%N in Hshort_set.
      change (PTrieCode.T_set (dom_lt_key vertex) best (lt_label links) <=
        PTrieT.c_trie * N.of_nat (Pos.size_nat (dom_lt_key vertex) + 1))%N in Hlabel_set.
      destruct part as [part|]; unfold previous in Hmin_time; unfold best in Hlabel_set;
        unfold T_dom_lt_compress_step; cbn [lt_walk_links lt_walk_phase]; fold label;
        time_simpl;
        clear -Hvertex_width Hkey_width Hkey_time Hlabel_time Hmin_time Hshort_set Hlabel_set;
        rewrite !Nat2N.inj_add in *; nia.
Qed.

(** Doubling a binary value adds at most one representation bit. *)
Lemma dom_lt_double_width value : N.size_nat (N.double value) <= N.size_nat value + 1.
Proof.
  destruct value; cbn [N.double N.size_nat Pos.size_nat]; lia.
Qed.

(** Binary doubling is a constant-time constructor operation. *)
Lemma dom_lt_time_double value : (N.T_double value <= 1)%N.
Proof.
  destruct value; time_step.
Qed.

(** Selecting the exhausted-loop result adds at most one call. *)
Lemma dom_lt_result_branch {A B : Type} (result : A + B) :
  (match result with inl _ => 1 | inr _ => 0 end <= 1)%N.
Proof.
  destruct result; lia.
Qed.

(** * Exact producer and replay agreement *)

Local Transparent Argent.Loop.loop T_loopN.
Local Transparent dom_lt_identity T_dom_lt_identity dom_lt_minimum T_dom_lt_minimum.
Local Transparent dom_lt_compress_step T_dom_lt_compress_step dom_lt_eval T_dom_lt_eval.
Local Transparent dom_lt_settle.

(** Two accessibility loops agree without proof irrelevance when they share the same proof,
    and the right loop pays at least the left one when each of its steps does. *)
Lemma dom_lt_accessibility_agree {S R : Type} (lt : S -> S -> Prop)
    (left right : forall state, {next : S | lt next state} + R)
    (T_left T_right : S -> N) (Inv : S -> Prop) :
  (forall state, Inv state ->
    left state = right state /\ (T_left state <= T_right state)%N) ->
  (forall state next decrease, Inv state -> left state = inl (exist _ next decrease) ->
    Inv next) ->
  forall state (access : Acc lt state), Inv state ->
    Argent.Loop.loop lt left state access = Argent.Loop.loop lt right state access /\
    (T_loop lt left T_left state access <= T_loop lt right T_right state access)%N.
Proof.
  intros Hagree Hpreserve state access.
  induction access as [state Hacc IH] using Acc_ind_dep. intro Hinv.
  destruct (Hagree state Hinv) as [Hstep Hclock].
  cbn [Argent.Loop.loop]. time_unfold @T_loop. rewrite <- Hstep.
  destruct (left state) as [[next decrease]|result] eqn:Hnext.
  - specialize (IH next decrease (Hpreserve state next decrease Hinv Hnext)).
    cbn [Acc_inv]. destruct IH as [Hvalue Htime]. split; [exact Hvalue|lia].
  - split; [reflexivity|lia].
Qed.

(** Binary-fuel evaluation preserves callback agreement and a pointwise clock bound. *)
Lemma dom_lt_binary_loop_agree {S R : Type} (left right : S -> S + R)
    (T_left T_right : S -> N) (Inv : S -> Prop) :
  (forall state, Inv state ->
    left state = right state /\ (T_left state <= T_right state)%N) ->
  (forall state next, Inv state -> left state = inl next -> Inv next) ->
  forall fuel state, Inv state ->
    loopN left fuel state = loopN right fuel state /\
    (T_loopN left T_left fuel state <= T_loopN right T_right fuel state)%N.
Proof.
  intros Hagree Hpreserve fuel state Hinv.
  assert (Hstep : forall fs : N * S, Inv (snd fs) ->
    loopN_step left fs = loopN_step right fs /\
      (T_loopN_step left T_left fs <= T_loopN_step right T_right fs)%N).
  { intros [[|positive] current] Hcurrent.
    - split; [reflexivity|time_unfold @T_loopN_step; apply N.le_refl].
    - destruct (Hagree current Hcurrent) as [Hvalue Hclock].
      split.
      + cbn [loopN_step]. now rewrite Hvalue.
      + time_unfold @T_loopN_step. rewrite Hvalue. lia. }
  assert (Hnext : forall fs next decrease, Inv (snd fs) ->
    loopN_step left fs = inl (exist _ next decrease) -> Inv (snd next)).
  { intros [[|positive] current] next decrease Hcurrent Hcontinue; [discriminate|].
    cbn [loopN_step] in Hcontinue.
    destruct (left current) as [following|result] eqn:Hcallback; [|discriminate].
    inversion Hcontinue; subst next. cbn [snd].
    now apply (Hpreserve current following). }
  unfold loopN. time_unfold @T_loopN.
  match goal with
  | |- context [Argent.Loop.loop _ _ _ ?access] =>
    pose proof (dom_lt_accessibility_agree loopN_lt (loopN_step left) (loopN_step right)
      (fun fs => T_loopN_step left T_left fs) (fun fs => T_loopN_step right T_right fs)
      (fun fs => Inv (snd fs)) Hstep Hnext (fuel, state) access Hinv) as Hloop
  end.
  destruct Hloop as [Hvalue Htime]. split; [exact Hvalue|]. lia.
Qed.

Local Opaque Argent.Loop.loop T_loopN.

(** Every lookup in the right table reads at least as many nodes as in the left table. *)
Definition dom_lt_clock_below (left right : ptrie N) : Prop :=
  forall key, (T_trie_get key left <= T_trie_get key right)%N.

(** Identity lookup in a table whose lookups read more nodes pays at least as much. *)
Lemma dom_lt_identity_clock_table left right vertex :
  dom_lt_clock_below left right ->
  (T_dom_lt_identity left vertex <= T_dom_lt_identity right vertex)%N.
Proof.
  intro Hbelow. pose proof (Hbelow (dom_lt_key vertex)) as Hkey.
  unfold T_dom_lt_identity.
  destruct (trie_get (dom_lt_key vertex) left), (trie_get (dom_lt_key vertex) right);
    time_simpl; lia.
Qed.

Definition dom_lt_scores_agree (known : N -> Prop) (left right : ptrie N) : Prop :=
  forall vertex, known vertex -> dom_lt_identity left vertex = dom_lt_identity right vertex.

(** A minimum examines only the scores of the two labels it is given. *)
Lemma dom_lt_minimum_agree known left right first second :
  dom_lt_scores_agree known left right -> known first -> known second ->
  dom_lt_minimum left first second = dom_lt_minimum right first second /\
    (dom_lt_clock_below left right ->
      (T_dom_lt_minimum left first second <= T_dom_lt_minimum right first second)%N).
Proof.
  intros Hagree Hfirst Hsecond.
  pose proof (Hagree first Hfirst) as Hfirst_score.
  pose proof (Hagree second Hsecond) as Hsecond_score.
  split.
  - unfold dom_lt_minimum. now rewrite Hfirst_score, Hsecond_score.
  - intro Hbelow.
    pose proof (dom_lt_identity_clock_table left right first Hbelow) as Hfirst_clock.
    pose proof (dom_lt_identity_clock_table left right second Hbelow) as Hsecond_clock.
    unfold T_dom_lt_minimum. rewrite Hfirst_score, Hsecond_score. lia.
Qed.

Definition dom_lt_links_known (known : N -> Prop) (links : dom_lt_links) : Prop :=
  dom_lt_trie_all known (lt_label links) /\
  forall vertex parent, trie_get (dom_lt_key vertex) (lt_shortcut links) = Some parent ->
    exists label, trie_get (dom_lt_key vertex) (lt_label links) = Some label.

Lemma dom_lt_linked_label_known known links vertex :
  dom_lt_links_known known links ->
  trie_get (dom_lt_key vertex) (lt_shortcut links) <> None ->
  known (dom_lt_identity (lt_label links) vertex).
Proof.
  intros [Hlabels Hdomain] Hpresent.
  destruct (trie_get (dom_lt_key vertex) (lt_shortcut links)) as [parent|] eqn:Hget;
    [|contradiction].
  destruct (Hdomain vertex parent Hget) as [label Hlabel].
  unfold dom_lt_identity. rewrite Hlabel. now apply (Hlabels (dom_lt_key vertex)).
Qed.

Lemma dom_lt_minimum_known known semis first second : known first -> known second ->
  known (dom_lt_minimum semis first second).
Proof.
  intros Hfirst Hsecond. unfold dom_lt_minimum.
  destruct (N.ltb (dom_lt_identity semis second) (dom_lt_identity semis first)); assumption.
Qed.

Lemma dom_lt_links_known_set known before vertex root label operations :
  dom_lt_links_known known before -> known label ->
  dom_lt_links_known known
    (DomLtLinks (PTrieCode.set (dom_lt_key vertex) root (lt_shortcut before))
      (PTrieCode.set (dom_lt_key vertex) label (lt_label before)) operations).
Proof.
  intros [Hlabels Hdomain] Hlabel. split.
  - apply dom_lt_trie_all_set; assumption.
  - intros query parent Hget. cbn [lt_shortcut lt_label] in *.
    destruct (Pos.eq_dec (dom_lt_key query) (dom_lt_key vertex)) as [Heq|Hne].
    + exists label. rewrite Heq. apply PTrie.get_set_same.
    + rewrite PTrie.get_set_other in Hget by exact Hne.
      destruct (Hdomain query parent Hget) as [stored Hstored].
      exists stored. now rewrite PTrie.get_set_other by exact Hne.
Qed.

Lemma dom_lt_shortcut_set_present before vertex root query :
  trie_get (dom_lt_key query) (lt_shortcut before) <> None ->
  trie_get (dom_lt_key query) (PTrieCode.set (dom_lt_key vertex) root (lt_shortcut before))
    <> None.
Proof.
  intro Hpresent.
  destruct (Pos.eq_dec (dom_lt_key query) (dom_lt_key vertex)) as [->|Hne].
  - rewrite PTrie.get_set_same. discriminate.
  - now rewrite PTrie.get_set_other by exact Hne.
Qed.

Definition dom_lt_walk_known (known : N -> Prop) (st : dom_lt_walk) : Prop :=
  dom_lt_links_known known (lt_walk_links st) /\
  match lt_walk_phase st with
  | DomLtDescend _ stack =>
      Forall (fun vertex => trie_get (dom_lt_key vertex) (lt_shortcut (lt_walk_links st))
        <> None) stack
  | DomLtUnwind _ part stack =>
      (match part with None => True | Some label => known label end) /\
      Forall (fun vertex => trie_get (dom_lt_key vertex) (lt_shortcut (lt_walk_links st))
        <> None) stack
  end.

(** The optional minimum ranges over linked labels and excludes the unlinked stopping root. *)
Lemma dom_lt_compress_known known semis st : dom_lt_walk_known known st ->
  match dom_lt_compress_step semis st with
  | inl next => dom_lt_walk_known known next
  | inr result => dom_lt_links_known known (fst result)
  end.
Proof.
  destruct st as [links [vertex stack|root part stack]].
  - cbn [dom_lt_walk_known lt_walk_links lt_walk_phase]. intros [Hlinks Hstack].
    cbn [dom_lt_compress_step lt_walk_links lt_walk_phase].
    destruct (trie_get (dom_lt_key vertex) (lt_shortcut links)) as [parent|] eqn:Hget.
    + destruct (N.ltb parent vertex).
      * split; [exact Hlinks|]. constructor; [cbn [lt_walk_links]; congruence|exact Hstack].
      * split; [exact Hlinks|]. now split.
    + split; [exact Hlinks|]. now split.
  - cbn [dom_lt_walk_known lt_walk_links lt_walk_phase]. intros [Hlinks [Hpart Hstack]].
    destruct stack as [|vertex stack].
    + exact Hlinks.
    + inversion Hstack as [|head tail Hpresent Htail]; subst head tail.
      set (label := dom_lt_identity (lt_label links) vertex).
      set (best := match part with None => label |
        Some previous => dom_lt_minimum semis label previous end).
      assert (Hlabel : known label) by (unfold label; now apply dom_lt_linked_label_known).
      assert (Hbest : known best).
      { unfold best. destruct part; [now apply dom_lt_minimum_known|exact Hlabel]. }
      change (dom_lt_walk_known known
        (DomLtWalk (DomLtLinks
          (PTrieCode.set (dom_lt_key vertex) root (lt_shortcut links))
          (PTrieCode.set (dom_lt_key vertex) best (lt_label links)) (lt_operations links))
          (DomLtUnwind root (Some best) stack))).
      split; [now apply dom_lt_links_known_set|]. split; [exact Hbest|].
      apply Forall_forall. intros query Hin. apply dom_lt_shortcut_set_present.
      now apply (proj1 (Forall_forall _ _) Htail query).
Qed.

Lemma dom_lt_compress_agree known left right st :
  dom_lt_scores_agree known left right -> dom_lt_walk_known known st ->
  dom_lt_compress_step left st = dom_lt_compress_step right st /\
    (dom_lt_clock_below left right ->
      (T_dom_lt_compress_step left st <= T_dom_lt_compress_step right st)%N).
Proof.
  intros Hagree. destruct st as [links [vertex stack|root part stack]].
  - intro Hinv. split; [reflexivity|intros _; apply N.le_refl].
  - cbn [dom_lt_walk_known lt_walk_links lt_walk_phase]. intros [Hlinks [Hpart Hstack]].
    destruct stack as [|vertex stack]; [split; [reflexivity|intros _; apply N.le_refl]|].
    destruct part as [previous|]; [|split; [reflexivity|intros _; apply N.le_refl]].
    inversion Hstack as [|head tail Hpresent Htail]; subst head tail.
    pose proof (dom_lt_linked_label_known known links vertex Hlinks Hpresent) as Hlabel.
    destruct (dom_lt_minimum_agree known left right
      (dom_lt_identity (lt_label links) vertex) previous Hagree Hlabel Hpart)
      as [Hvalue Htime].
    split.
    + cbn [dom_lt_compress_step lt_walk_links lt_walk_phase]. now rewrite Hvalue.
    + intro Hbelow. specialize (Htime Hbelow).
      unfold T_dom_lt_compress_step. cbn [lt_walk_links lt_walk_phase].
      rewrite Hvalue. lia.
Qed.

(** Replay may use final semidominators once they agree on every already-linked label, and
    it costs at least as much when its score lookups read at least as many nodes. *)
Lemma dom_lt_eval_agree known left right fuel before vertex :
  dom_lt_scores_agree known left right -> dom_lt_links_known known before ->
  dom_lt_eval fuel left before vertex = dom_lt_eval fuel right before vertex /\
    (dom_lt_clock_below left right ->
      (T_dom_lt_eval fuel left before vertex <= T_dom_lt_eval fuel right before vertex)%N).
Proof.
  intros Hagree Hlinks.
  set (initial := DomLtWalk
    (DomLtLinks (lt_shortcut before) (lt_label before) (LtEval vertex :: lt_operations before))
    (DomLtDescend vertex [])).
  assert (Hinitial : dom_lt_walk_known known initial).
  { split; [exact Hlinks|constructor]. }
  assert (Hpreserve : forall st next, dom_lt_walk_known known st ->
    dom_lt_compress_step left st = inl next -> dom_lt_walk_known known next).
  { intros st next Hst Hnext.
    pose proof (dom_lt_compress_known known left st Hst) as Hknown. now rewrite Hnext in Hknown. }
  assert (Hloop : forall T_left T_right : dom_lt_walk -> N,
    (forall st, dom_lt_walk_known known st -> (T_left st <= T_right st)%N) ->
    loopN (dom_lt_compress_step left) (N.double fuel + 3)%N initial =
      loopN (dom_lt_compress_step right) (N.double fuel + 3)%N initial /\
    (T_loopN (dom_lt_compress_step left) T_left (N.double fuel + 3)%N initial <=
      T_loopN (dom_lt_compress_step right) T_right (N.double fuel + 3)%N initial)%N).
  { intros T_left T_right Hclock.
    apply (dom_lt_binary_loop_agree (dom_lt_compress_step left) (dom_lt_compress_step right)
      T_left T_right (dom_lt_walk_known known)); [|exact Hpreserve|exact Hinitial].
    intros st Hst. split; [|exact (Hclock st Hst)].
    exact (proj1 (dom_lt_compress_agree known left right st Hagree Hst)). }
  destruct (Hloop (T_dom_lt_compress_step left) (T_dom_lt_compress_step left)
    (fun st _ => N.le_refl _)) as [Hvalue _].
  split.
  - unfold dom_lt_eval. fold initial. now rewrite Hvalue.
  - intro Hbelow.
    destruct (Hloop (T_dom_lt_compress_step left) (T_dom_lt_compress_step right)
      (fun st Hst => proj2 (dom_lt_compress_agree known left right st Hagree Hst) Hbelow))
      as [_ Htime].
    unfold T_dom_lt_eval. fold initial. time_simpl.
    change (T_loopN (dom_lt_compress_step left)
      (fun st => T_dom_lt_compress_step left st) (N.double fuel + 3)%N initial)
      with (T_loopN (dom_lt_compress_step left) (T_dom_lt_compress_step left)
        (N.double fuel + 3)%N initial).
    change (T_loopN (dom_lt_compress_step right)
      (fun st => T_dom_lt_compress_step right st) (N.double fuel + 3)%N initial)
      with (T_loopN (dom_lt_compress_step right) (T_dom_lt_compress_step right)
        (N.double fuel + 3)%N initial).
    rewrite Hvalue. lia.
Qed.

(** Evaluating a query preserves the known-label invariant, including fuel exhaustion. *)
Lemma dom_lt_eval_known known fuel semis before vertex :
  dom_lt_links_known known before ->
  dom_lt_links_known known (fst (dom_lt_eval fuel semis before vertex)).
Proof.
  intro Hlinks.
  set (initial := DomLtWalk
    (DomLtLinks (lt_shortcut before) (lt_label before) (LtEval vertex :: lt_operations before))
    (DomLtDescend vertex [])).
  assert (Hinitial : dom_lt_walk_known known initial).
  { split; [exact Hlinks|constructor]. }
  pose proof (dom_lt_loop_invariant (dom_lt_compress_step semis)
    (dom_lt_walk_known known) (fun result => dom_lt_links_known known (fst result))
    (N.double fuel + 3)%N initial) as Hrun.
  assert (Hgo : forall st next, dom_lt_walk_known known st ->
    dom_lt_compress_step semis st = inl next -> dom_lt_walk_known known next).
  { intros st next Hst Hnext.
    pose proof (dom_lt_compress_known known semis st Hst) as Hknown.
    now rewrite Hnext in Hknown. }
  assert (Hstop : forall st result, dom_lt_walk_known known st ->
    dom_lt_compress_step semis st = inr result -> dom_lt_links_known known (fst result)).
  { intros st result Hst Hnext.
    pose proof (dom_lt_compress_known known semis st Hst) as Hknown.
    now rewrite Hnext in Hknown. }
  specialize (Hrun Hgo Hstop Hinitial).
  unfold dom_lt_eval. fold initial.
  destruct (loopN (dom_lt_compress_step semis) (N.double fuel + 3)%N initial)
    as [st|result]; [exact (proj1 Hrun)|exact Hrun].
Qed.

Local Opaque dom_lt_eval T_dom_lt_eval.

(** Enlarging the known set preserves its invariant on every stored label. *)
Lemma dom_lt_links_known_mono smaller larger links :
  (forall vertex, smaller vertex -> larger vertex) ->
  dom_lt_links_known smaller links -> dom_lt_links_known larger links.
Proof.
  intros Hincl [Hlabels Hdomain]. split; [|exact Hdomain].
  intros key value Hget. now apply Hincl, (Hlabels key value).
Qed.

(** Linking a newly settled vertex extends the known-label invariant. *)
Lemma dom_lt_link_known known links vertex parent :
  dom_lt_links_known known links -> known vertex ->
  dom_lt_links_known known (dom_lt_link links vertex parent).
Proof.
  intros Hlinks Hvertex. unfold dom_lt_link. now apply dom_lt_links_known_set.
Qed.

(** A settlement changes the score table only at its own vertex. *)
Lemma dom_lt_settle_score_other numeric before vertex query :
  query <> vertex ->
  dom_lt_identity (lt_semis (dom_lt_settle numeric before vertex)) query =
    dom_lt_identity (lt_semis before) query.
Proof.
  intro Hdifferent. unfold dom_lt_settle.
  destruct (trie_get (dom_lt_key vertex) (lt_numeric_parent numeric)) as [parent|];
    [|reflexivity].
  destruct (fold_left (dom_lt_predecessor (lt_numeric_limit numeric) (lt_semis before))
    (match trie_get (dom_lt_key vertex) (lt_numeric_pred numeric) with
      None => [] | Some row => row end) (lt_semi_links before, parent, parent))
    as [[links best] witness].
  cbn [lt_semis]. unfold dom_lt_identity.
  rewrite PTrie.get_set_other; [reflexivity|].
  intro Heq. apply Hdifferent, dom_lt_key_injective, Heq.
Qed.

(** Later settlements preserve the final score of every vertex outside their order. *)
Lemma dom_lt_settlements_score_frame numeric order before query :
  ~ In query order ->
  dom_lt_identity (lt_semis (fold_left (dom_lt_settle numeric) order before)) query =
    dom_lt_identity (lt_semis before) query.
Proof.
  revert before. induction order as [|vertex rest IH]; intros before Houtside;
    [reflexivity|].
  cbn [fold_left]. rewrite IH by (intro Hin; apply Houtside; now right).
  apply dom_lt_settle_score_other. intro Heq. apply Houtside. left. now symmetry.
Qed.

(** A settlement sets one score and removes none, so no later score lookup reads fewer nodes. *)
Lemma dom_lt_settle_clock_below numeric before vertex :
  dom_lt_clock_below (lt_semis before) (lt_semis (dom_lt_settle numeric before vertex)).
Proof.
  intro key. unfold dom_lt_settle.
  destruct (trie_get (dom_lt_key vertex) (lt_numeric_parent numeric)) as [parent|];
    [|apply N.le_refl].
  destruct (fold_left (dom_lt_predecessor (lt_numeric_limit numeric) (lt_semis before))
    (match trie_get (dom_lt_key vertex) (lt_numeric_pred numeric) with
      None => [] | Some row => row end) (lt_semi_links before, parent, parent))
    as [[links best] witness].
  cbn [lt_semis]. apply PTrieT.T_trie_get_set_le.
Qed.

(** Later settlements make no score lookup cheaper. *)
Lemma dom_lt_settlements_clock_below numeric order before :
  dom_lt_clock_below (lt_semis before)
    (lt_semis (fold_left (dom_lt_settle numeric) order before)).
Proof.
  revert before. induction order as [|vertex rest IH]; intros before key;
    [apply N.le_refl|].
  cbn [fold_left]. eapply N.le_trans; [apply dom_lt_settle_clock_below|apply IH].
Qed.

(** The operation-only phase uses the same evaluator and linker as the producer. *)
Definition dom_lt_phase_step (fuel : N) (semis : ptrie N)
    (links : dom_lt_links) (op : lt_op) : dom_lt_links :=
  match op with
  | LtLink child parent => dom_lt_link links child parent
  | LtEval vertex => fst (dom_lt_eval fuel semis links vertex)
  end.
TimeFun dom_lt_phase_step.

(** Executing a recorded phase prepends its reversed operation list to the old log. *)
Lemma dom_lt_phase_operations fuel semis operations before :
  lt_operations (fold_left (dom_lt_phase_step fuel semis) operations before) =
    rev operations ++ lt_operations before.
Proof.
  revert before. induction operations as [|op rest IH]; intros before.
  - reflexivity.
  - cbn [fold_left]. rewrite IH.
    assert (Hhead : lt_operations (dom_lt_phase_step fuel semis before op) =
      op :: lt_operations before).
    { destruct op; cbn [dom_lt_phase_step];
        [reflexivity|apply dom_lt_eval_operations]. }
    rewrite Hhead. cbn [rev]. now rewrite <- app_assoc.
Qed.

(** A settlement's operation sequence depends only on its numeric parent and row. *)
Definition dom_lt_settle_sequence (numeric : dom_lt_numeric) (vertex : N) : list lt_op :=
  match trie_get (dom_lt_key vertex) (lt_numeric_parent numeric) with
  | None => []
  | Some parent =>
      map LtEval (match trie_get (dom_lt_key vertex) (lt_numeric_pred numeric) with
        None => [] | Some row => row end) ++ [LtLink vertex parent]
  end.

Definition dom_lt_settlements_sequence (numeric : dom_lt_numeric) (order : list N) :=
  flat_map (dom_lt_settle_sequence numeric) order.

(** A replay callback uses its phase computation after applying the single boundary reset. *)
Lemma dom_lt_replay_step_phase fuel semis before boundary index op :
  dom_lt_replay_step (DomLtReplay before semis fuel boundary index) op =
    DomLtReplay
      (dom_lt_phase_step fuel semis
        (if N.eqb index boundary then DomLtLinks Empty Empty [] else before) op)
      semis fuel boundary (N.succ index).
Proof.
  destruct op; reflexivity.
Qed.

(** Replay includes the generated clock of the same evaluator or linker. *)
Lemma dom_lt_replay_clock_phase fuel semis before boundary index op :
  (T_dom_lt_phase_step fuel semis
    (if N.eqb index boundary then DomLtLinks Empty Empty [] else before) op <=
    T_dom_lt_replay_step (DomLtReplay before semis fuel boundary index) op)%N.
Proof.
  destruct op; unfold T_dom_lt_phase_step, T_dom_lt_replay_step;
    cbn [replay_links replay_semis replay_fuel replay_boundary replay_index];
    destruct (N.eqb index boundary); time_simpl; nia.
Qed.

(** A segment wholly before or strictly after the boundary performs no reset. *)
Lemma dom_lt_replay_phase_segment fuel semis operations : forall before boundary index,
  ((boundary < index) \/ (index + N.of_nat (length operations) <= boundary))%N ->
  fold_left dom_lt_replay_step operations (DomLtReplay before semis fuel boundary index) =
    DomLtReplay (fold_left (dom_lt_phase_step fuel semis) operations before)
      semis fuel boundary (index + N.of_nat (length operations))%N /\
  (List.T_fold_left (dom_lt_phase_step fuel semis) (T_dom_lt_phase_step fuel semis)
    operations before <=
    List.T_fold_left dom_lt_replay_step T_dom_lt_replay_step operations
      (DomLtReplay before semis fuel boundary index))%N.
Proof.
  induction operations as [|op rest IH]; intros before boundary index Hside.
  - cbn [fold_left length]. rewrite N.add_0_r. split; [reflexivity|].
    time_unfold @List.T_fold_left. reflexivity.
  - assert (Hdifferent : N.eqb index boundary = false).
    { apply N.eqb_neq. cbn [length] in Hside. rewrite Nat2N.inj_succ in Hside. lia. }
    assert (Hrest : ((boundary < N.succ index) \/
      (N.succ index + N.of_nat (length rest) <= boundary))%N).
    { cbn [length] in Hside. rewrite Nat2N.inj_succ in Hside. lia. }
    destruct (IH (dom_lt_phase_step fuel semis before op) boundary (N.succ index) Hrest)
      as [Hvalue Hclock].
    pose proof (dom_lt_replay_clock_phase fuel semis before boundary index op) as Hhead.
    rewrite Hdifferent in Hhead.
    assert (Hstep : dom_lt_replay_step (DomLtReplay before semis fuel boundary index) op =
      DomLtReplay (dom_lt_phase_step fuel semis before op) semis fuel boundary (N.succ index)).
    { rewrite dom_lt_replay_step_phase, Hdifferent. reflexivity. }
    split.
    + cbn [fold_left]. rewrite Hstep, Hvalue. cbn [length]. rewrite Nat2N.inj_succ.
      f_equal. lia.
    + time_unfold @List.T_fold_left. rewrite Hstep. clear -Hhead Hclock. lia.
Qed.

(** A bucket suffix starts at the reset boundary and then remains strictly beyond it. *)
Lemma dom_lt_replay_bucket_phase fuel semis operations before boundary :
  (List.T_fold_left (dom_lt_phase_step fuel semis) (T_dom_lt_phase_step fuel semis)
    operations (DomLtLinks Empty Empty []) <=
    List.T_fold_left dom_lt_replay_step T_dom_lt_replay_step operations
      (DomLtReplay before semis fuel boundary boundary))%N.
Proof.
  destruct operations as [|op rest].
  - time_unfold @List.T_fold_left. reflexivity.
  - destruct (dom_lt_replay_phase_segment fuel semis rest
      (dom_lt_phase_step fuel semis (DomLtLinks Empty Empty []) op)
      boundary (N.succ boundary)) as [_ Htail]; [left; lia|].
    pose proof (dom_lt_replay_clock_phase fuel semis before boundary boundary op) as Hhead.
    rewrite N.eqb_refl in Hhead.
    assert (Hstep : dom_lt_replay_step (DomLtReplay before semis fuel boundary boundary) op =
      DomLtReplay (dom_lt_phase_step fuel semis (DomLtLinks Empty Empty []) op)
        semis fuel boundary (N.succ boundary)).
    { rewrite dom_lt_replay_step_phase, N.eqb_refl. reflexivity. }
    time_unfold @List.T_fold_left. rewrite Hstep. clear -Hhead Htail. lia.
Qed.

(** Two separately run producer forests are paid by replay, including its one reset. *)
Lemma dom_lt_pipeline_replay_two_phases fuel semis semi_ops bucket_ops :
  (List.T_fold_left (dom_lt_phase_step fuel semis) (T_dom_lt_phase_step fuel semis)
      semi_ops (DomLtLinks Empty Empty []) +
    List.T_fold_left (dom_lt_phase_step fuel semis) (T_dom_lt_phase_step fuel semis)
      bucket_ops (DomLtLinks Empty Empty []) <=
    T_dom_lt_run_ops (semi_ops ++ bucket_ops)
      (DomLtReplay (DomLtLinks Empty Empty []) semis fuel
        (N.of_nat (length semi_ops)) 0%N) + 1)%N.
Proof.
  set (initial := DomLtReplay (DomLtLinks Empty Empty []) semis fuel
    (N.of_nat (length semi_ops)) 0%N).
  destruct (dom_lt_replay_phase_segment fuel semis semi_ops (DomLtLinks Empty Empty [])
    (N.of_nat (length semi_ops)) 0%N) as [Hvalue Hsemi]; [right; lia|].
  cbn [N.add] in Hvalue. fold initial in Hvalue, Hsemi.
  pose proof (dom_lt_replay_bucket_phase fuel semis bucket_ops
    (fold_left (dom_lt_phase_step fuel semis) semi_ops (DomLtLinks Empty Empty []))
    (N.of_nat (length semi_ops))) as Hbucket.
  pose proof (dom_lt_fold_clock_app dom_lt_replay_step T_dom_lt_replay_step
    semi_ops bucket_ops initial) as Hsplit.
  rewrite Hvalue in Hsplit. unfold T_dom_lt_run_ops. fold initial. time_simpl.
  change (fun (st : dom_lt_replay) (op : lt_op) => T_dom_lt_replay_step st op)
    with T_dom_lt_replay_step.
  clear -Hsemi Hbucket Hsplit. nia.
Qed.

(** A state projection commutes with a fold when it commutes with each guarded step. *)
Lemma dom_lt_fold_project {A B C : Type} (step : A -> B -> A) (target : C -> B -> C)
    (project : A -> C) (Inv : A -> Prop) :
  (forall st value, Inv st -> Inv (step st value)) ->
  (forall st value, Inv st -> project (step st value) = target (project st) value) ->
  forall values initial, Inv initial ->
  project (fold_left step values initial) = fold_left target values (project initial) /\
    Inv (fold_left step values initial).
Proof.
  intros Hpreserve Hproject values. induction values as [|value rest IH]; intros initial Hinv.
  - split; [reflexivity|exact Hinv].
  - destruct (IH (step initial value) (Hpreserve initial value Hinv)) as [Hvalue Hafter].
    split; [|exact Hafter].
    exact (eq_trans Hvalue
      (f_equal (fold_left target rest) (Hproject initial value Hinv))).
Qed.

(** Mapping the input operations is equivalent to supplying the mapped operation to the step. *)
Lemma dom_lt_fold_mapped {A B C : Type} (step : A -> B -> A) (key : C -> B) values :
  forall initial, fold_left step (map key values) initial =
    fold_left (fun st value => step st (key value)) values initial.
Proof.
  induction values as [|value rest IH]; intros initial; [reflexivity|].
  exact (IH (step initial (key value))).
Qed.

Local Opaque dom_lt_eval T_dom_lt_eval.
Local Transparent dom_lt_predecessor T_dom_lt_predecessor dom_lt_settle T_dom_lt_settle.

(** A predecessor visit changes its link state only through its evaluator. *)
Lemma dom_lt_predecessor_links limit semis acc source :
  fst (fst (dom_lt_predecessor limit semis acc source)) =
    fst (dom_lt_eval limit semis (fst (fst acc)) source).
Proof.
  destruct acc as [[links best] witness]. cbn [fst]. unfold dom_lt_predecessor.
  destruct (dom_lt_eval limit semis links source) as [after chosen].
  destruct (N.ltb (dom_lt_identity semis chosen) best); reflexivity.
Qed.

Local Opaque dom_lt_predecessor T_dom_lt_predecessor.

(** Replaying one predecessor row with final scores reproduces its exact link state. *)
Lemma dom_lt_predecessors_phase known limit current final incoming :
  dom_lt_scores_agree known current final -> forall acc,
  dom_lt_links_known known (fst (fst acc)) ->
  fst (fst (fold_left (dom_lt_predecessor limit current) incoming acc)) =
    fold_left (dom_lt_phase_step limit final) (map LtEval incoming) (fst (fst acc)) /\
  dom_lt_links_known known
    (fst (fst (fold_left (dom_lt_predecessor limit current) incoming acc))).
Proof.
  intros Hscores acc Hknown.
  assert (Hpreserve : forall state source,
    dom_lt_links_known known (fst (fst state)) ->
    dom_lt_links_known known (fst (fst (dom_lt_predecessor limit current state source)))).
  { intros state source Hstate. rewrite dom_lt_predecessor_links.
    now apply dom_lt_eval_known. }
  assert (Hproject : forall state source,
    dom_lt_links_known known (fst (fst state)) ->
    fst (fst (dom_lt_predecessor limit current state source)) =
      dom_lt_phase_step limit final (fst (fst state)) (LtEval source)).
  { intros state source Hstate. eapply eq_trans; [apply dom_lt_predecessor_links|].
    change (fst (dom_lt_eval limit current (fst (fst state)) source) =
      fst (dom_lt_eval limit final (fst (fst state)) source)).
    exact (f_equal (@fst dom_lt_links N)
      (proj1 (dom_lt_eval_agree known current final limit (fst (fst state)) source
        Hscores Hstate))). }
  destruct (dom_lt_fold_project (dom_lt_predecessor limit current)
    (fun links source => dom_lt_phase_step limit final links (LtEval source))
    (fun state => fst (fst state)) (fun state => dom_lt_links_known known (fst (fst state)))
    Hpreserve Hproject incoming acc Hknown) as [Hvalue Hafter].
  split; [|exact Hafter].
  exact (eq_trans Hvalue (eq_sym
    (dom_lt_fold_mapped (dom_lt_phase_step limit final) LtEval incoming (fst (fst acc))))).
Qed.

(** One settlement's final-score replay matches all row evaluations followed by its link. *)
Lemma dom_lt_settle_phase known numeric before vertex final :
  dom_lt_scores_agree known (lt_semis before) final ->
  dom_lt_links_known known (lt_semi_links before) ->
  lt_semi_links (dom_lt_settle numeric before vertex) =
    fold_left (dom_lt_phase_step (lt_numeric_limit numeric) final)
      (dom_lt_settle_sequence numeric vertex) (lt_semi_links before) /\
  dom_lt_links_known (fun query => known query \/ query = vertex)
    (lt_semi_links (dom_lt_settle numeric before vertex)).
Proof.
  intros Hscores Hknown. unfold dom_lt_settle, dom_lt_settle_sequence.
  destruct (trie_get (dom_lt_key vertex) (lt_numeric_parent numeric)) as [parent|].
  2: { split; [reflexivity|].
       eapply dom_lt_links_known_mono; [|exact Hknown]. intros query Hquery. now left. }
  set (incoming := match trie_get (dom_lt_key vertex) (lt_numeric_pred numeric) with
    None => [] | Some row => row end).
  destruct (dom_lt_predecessors_phase known (lt_numeric_limit numeric)
    (lt_semis before) final incoming Hscores (lt_semi_links before, parent, parent) Hknown)
    as [Hvalue Hafter].
  destruct (fold_left (dom_lt_predecessor (lt_numeric_limit numeric) (lt_semis before))
    incoming (lt_semi_links before, parent, parent)) as [[links best] witness].
  cbn [fst] in Hvalue, Hafter. cbn [lt_semi_links]. split.
  - rewrite fold_left_app.
    change (dom_lt_link links vertex parent =
      dom_lt_link (fold_left (dom_lt_phase_step (lt_numeric_limit numeric) final)
        (map LtEval incoming) (lt_semi_links before)) vertex parent).
    now rewrite <- Hvalue.
  - apply dom_lt_link_known; [|now right].
    eapply dom_lt_links_known_mono; [|exact Hafter]. intros query Hquery. now left.
Qed.

Local Opaque dom_lt_settle T_dom_lt_settle.

(** The current score of a linked label is already its score after every later settlement. *)
Lemma dom_lt_settlements_phase numeric order : NoDup order -> forall before,
  dom_lt_links_known (fun query => ~ In query order) (lt_semi_links before) ->
  lt_semi_links (fold_left (dom_lt_settle numeric) order before) =
    fold_left (dom_lt_phase_step (lt_numeric_limit numeric)
      (lt_semis (fold_left (dom_lt_settle numeric) order before)))
      (dom_lt_settlements_sequence numeric order) (lt_semi_links before).
Proof.
  intro Hunique. induction Hunique as [|vertex rest Hfresh Hunique IH]; intros before Hknown.
  - reflexivity.
  - set (after := dom_lt_settle numeric before vertex).
    set (final := lt_semis (fold_left (dom_lt_settle numeric) rest after)).
    assert (Hscores : dom_lt_scores_agree (fun query => ~ In query (vertex :: rest))
      (lt_semis before) final).
    { intros query Houtside. unfold final, after. symmetry.
      change (dom_lt_identity
        (lt_semis (fold_left (dom_lt_settle numeric) (vertex :: rest) before)) query =
        dom_lt_identity (lt_semis before) query).
      now apply dom_lt_settlements_score_frame. }
    destruct (dom_lt_settle_phase (fun query => ~ In query (vertex :: rest))
      numeric before vertex final Hscores Hknown) as [Hstep Hlinked].
    fold after in Hstep, Hlinked.
    assert (Hnext : dom_lt_links_known (fun query => ~ In query rest) (lt_semi_links after)).
    { eapply dom_lt_links_known_mono; [|exact Hlinked].
      intros query [Houtside|Heq] Hin.
      - apply Houtside. now right.
      - subst query. contradiction. }
    specialize (IH after Hnext). fold final in IH.
    cbn [fold_left]. fold after. fold final.
    unfold dom_lt_settlements_sequence. cbn [flat_map]. rewrite fold_left_app.
    rewrite <- Hstep. exact IH.
Qed.

(** The initial empty forest has no labels that could depend on an unsettled score. *)
Lemma dom_lt_empty_links_known known :
  dom_lt_links_known known (DomLtLinks Empty Empty []).
Proof.
  split.
  - apply dom_lt_trie_all_empty.
  - intros vertex parent Hget. rewrite PTrie.get_empty in Hget. discriminate Hget.
Qed.

(** The complete semidominator forest is the replay of its fixed numeric operation list. *)
Lemma dom_lt_semidominators_phase numeric : NoDup (lt_numeric_order numeric) ->
  lt_semi_links (dom_lt_semidominators numeric) =
    fold_left (dom_lt_phase_step (lt_numeric_limit numeric)
      (lt_semis (dom_lt_semidominators numeric)))
      (dom_lt_settlements_sequence numeric (lt_numeric_order numeric))
      (DomLtLinks Empty Empty []).
Proof.
  intro Hunique. unfold dom_lt_semidominators.
  apply dom_lt_settlements_phase; [exact Hunique|apply dom_lt_empty_links_known].
Qed.

(** The producer's reverse log is exactly the reverse of its forward phase sequence. *)
Lemma dom_lt_semidominators_log numeric : NoDup (lt_numeric_order numeric) ->
  lt_operations (lt_semi_links (dom_lt_semidominators numeric)) =
    rev (dom_lt_settlements_sequence numeric (lt_numeric_order numeric)).
Proof.
  intro Hunique. rewrite dom_lt_semidominators_phase by exact Hunique.
  rewrite dom_lt_phase_operations. cbn [lt_operations]. now rewrite app_nil_r.
Qed.

(** One list cell combines two clock bounds without exposing either computation. *)
Lemma dom_lt_phase_clock_row head tail replay_head replay_tail extra_head extra_tail total :
  (head <= replay_head + extra_head)%N ->
  (tail <= replay_tail + extra_tail)%N ->
  (extra_head + extra_tail <= total)%N ->
  (1 + (head + tail) <= 1 + (replay_head + replay_tail) + total)%N.
Proof.
  nia.
Qed.

(** A row followed by one link pays the empty-call adjustment of concatenation. *)
Lemma dom_lt_phase_clock_settle step row link replay_row replay_link replay_total
    extra row_extra total :
  (step <= row + link + extra)%N ->
  (row <= replay_row + row_extra)%N ->
  (link <= replay_link)%N ->
  (replay_total + 1 = replay_row + (replay_link + 2))%N ->
  (row_extra + extra + 1 <= total)%N ->
  (step + 2 <= replay_total + total)%N.
Proof.
  nia.
Qed.

(** Flattening a list of phases counts only one final empty call. *)
Lemma dom_lt_phase_clock_flatten head tail replay_head replay_tail replay_total
    extra_head extra_tail total :
  (head + 2 <= replay_head + extra_head)%N ->
  (tail <= replay_tail + extra_tail)%N ->
  (replay_total + 1 = replay_head + replay_tail)%N ->
  (extra_head + extra_tail <= total)%N ->
  (1 + (head + tail) <= replay_total + total)%N.
Proof.
  nia.
Qed.

(** One wrapper call is paid from the extra linear budget. *)
Lemma dom_lt_phase_clock_wrapper clock replay extra total :
  (clock <= replay + extra)%N -> (extra + 1 <= total)%N ->
  (1 + clock <= replay + total)%N.
Proof.
  nia.
Qed.

(** The generated fold clock counts both the singleton call and its empty continuation. *)
Lemma dom_lt_single_fold_clock {A B : Type} (step : A -> B -> A) (T_step : A -> B -> N)
    before value :
  List.T_fold_left step T_step [value] before = (T_step before value + 2)%N.
Proof.
  time_unfold @List.T_fold_left. time_unfold @List.T_fold_left. lia.
Qed.

(** Restore the clock-proof transparency boundary for following sections. *)
Local Transparent dom_lt_eval T_dom_lt_eval dom_lt_predecessor T_dom_lt_predecessor.
Local Transparent dom_lt_settle T_dom_lt_settle.
Local Opaque Argent.Loop.loop T_loopN.

(* BEGIN G2-G BUCKET SUPPORT *)
Local Opaque dom_lt_eval T_dom_lt_eval.

Lemma dom_lt_phase_eval_clock fuel semis links source :
  (T_dom_lt_eval fuel semis links source <=
    T_dom_lt_phase_step fuel semis links (LtEval source))%N.
Proof.
  unfold T_dom_lt_phase_step. time_simpl. lia.
Qed.

Lemma dom_lt_phase_link_clock fuel semis links child parent :
  (T_dom_lt_link links child parent <=
    T_dom_lt_phase_step fuel semis links (LtLink child parent))%N.
Proof.
  unfold T_dom_lt_phase_step. time_simpl. lia.
Qed.

(** * Bucket phase correspondence

    Bucket link states and clocks agree with the exact operation-only phase.
    The numeric range invariants also bound the later correction pass. *)

Local Transparent dom_lt_bucket_member T_dom_lt_bucket_member
  dom_lt_bucket_step T_dom_lt_bucket_step dom_lt_correct_step T_dom_lt_correct_step.

(** A bucket state's link payloads and relative parents stay in one numeric range. *)
Definition dom_lt_pipeline_bucket_bounded (bound : N) (st : dom_lt_bucket_state) : Prop :=
  dom_lt_links_bounded bound (lt_bucket_links st) /\
  dom_lt_trie_all (fun value => (value <= bound)%N) (lt_relative st).

(** Processing a member chooses either a bounded evaluator result or the bucket key. *)
Lemma dom_lt_pipeline_bucket_member_range bound fuel semis s st v :
  dom_lt_pipeline_bucket_bounded bound st -> (s <= bound)%N -> (v <= bound)%N ->
  dom_lt_pipeline_bucket_bounded bound (dom_lt_bucket_member fuel semis s st v).
Proof.
  intros [Hlinks Hrelative] Hs Hv.
  pose proof (dom_lt_eval_bounded bound fuel semis (lt_bucket_links st) v Hlinks Hv)
    as Heval.
  unfold dom_lt_bucket_member.
  destruct (dom_lt_eval fuel semis (lt_bucket_links st) v) as [links chosen].
  cbn [fst snd] in Heval. destruct Heval as [Hafter Hchosen].
  split; [exact Hafter|]. apply dom_lt_trie_all_set; [exact Hrelative|].
  destruct (N.ltb (dom_lt_identity semis chosen) s); assumption.
Qed.

(** A row fold preserves bounded link payloads and relative parents. *)
Lemma dom_lt_pipeline_bucket_members_range bound fuel semis s row st :
  Forall (fun n => (n <= bound)%N) row ->
  dom_lt_pipeline_bucket_bounded bound st -> (s <= bound)%N ->
  dom_lt_pipeline_bucket_bounded bound (fold_left (dom_lt_bucket_member fuel semis s) row st).
Proof.
  intros Hrow Hst Hs.
  apply (dom_lt_fold_forall (dom_lt_bucket_member fuel semis s)
    (dom_lt_pipeline_bucket_bounded bound) (fun n => (n <= bound)%N));
    [exact Hrow|exact Hst|].
  intros current v Hcurrent Hv. now apply dom_lt_pipeline_bucket_member_range.
Qed.

(** A complete bucket step also installs only a bounded numeric parent link. *)
Lemma dom_lt_pipeline_bucket_step_range bound numeric semis buckets st s :
  dom_lt_numeric_ranges bound numeric ->
  dom_lt_trie_all (Forall (fun n => (n <= bound)%N)) buckets ->
  dom_lt_pipeline_bucket_bounded bound st -> (s <= bound)%N ->
  dom_lt_pipeline_bucket_bounded bound (dom_lt_bucket_step numeric semis buckets st s).
Proof.
  intros Hnumeric Hrows Hst Hs. unfold dom_lt_bucket_step.
  set (row := match trie_get (dom_lt_key s) buckets with None => [] | Some xs => xs end).
  assert (Hrow : Forall (fun n => (n <= bound)%N) row).
  { unfold row. destruct (trie_get (dom_lt_key s) buckets) as [xs|] eqn:Hget;
      [exact (Hrows _ _ Hget)|constructor]. }
  pose proof (dom_lt_pipeline_bucket_members_range bound (lt_numeric_limit numeric)
    semis s row st Hrow Hst Hs) as Hfold.
  destruct (trie_get (dom_lt_key s) (lt_numeric_parent numeric)) as [parent|] eqn:Hget;
    [|exact Hfold].
  destruct Hfold as [Hlinks Hrelative]. split; [|exact Hrelative].
  apply dom_lt_link_bounded; [exact Hlinks|exact Hs|].
  exact (dom_lt_numeric_parent_range _ _ Hnumeric _ _ Hget).
Qed.

(** The complete bucket phase starts empty and preserves the numeric operand bound. *)
Lemma dom_lt_pipeline_buckets_range bound numeric semis :
  dom_lt_numeric_ranges bound numeric ->
  dom_lt_pipeline_bucket_bounded bound (dom_lt_buckets numeric semis).
Proof.
  intro Hnumeric. unfold dom_lt_buckets.
  set (buckets := fold_left (dom_lt_bucket_add semis)
    (rev_append (lt_numeric_order numeric) []) Empty).
  assert (Hrows : dom_lt_trie_all (Forall (fun n => (n <= bound)%N)) buckets).
  { apply dom_lt_bucket_build_range. exact (dom_lt_numeric_order_range _ _ Hnumeric). }
  apply (dom_lt_fold_forall (dom_lt_bucket_step numeric semis buckets)
    (dom_lt_pipeline_bucket_bounded bound) (fun n => (n <= bound)%N)).
  - exact (dom_lt_numeric_order_range _ _ Hnumeric).
  - repeat split; apply dom_lt_trie_all_empty.
  - intros st s Hst Hs. eapply dom_lt_pipeline_bucket_step_range; eassumption.
Qed.

(** Correction retains bounded relative parents, including its identity-default lookup. *)
Lemma dom_lt_pipeline_correct_step_range bound semis relative corrected v :
  dom_lt_trie_all (fun n => (n <= bound)%N) relative ->
  dom_lt_trie_all (fun n => (n <= bound)%N) corrected ->
  dom_lt_trie_all (fun n => (n <= bound)%N)
    (dom_lt_correct_step semis relative corrected v).
Proof.
  intros Hrelative Hcorrected. unfold dom_lt_correct_step.
  destruct (trie_get (dom_lt_key v) relative) as [parent|] eqn:Hget;
    [|exact Hcorrected].
  pose proof (Hrelative _ _ Hget) as Hparent.
  apply dom_lt_trie_all_set; [exact Hcorrected|].
  destruct (N.eqb parent (dom_lt_identity semis v)); [exact Hparent|].
  now apply dom_lt_identity_bounded.
Qed.

(** The correction fold produces only parents in the relative-parent range. *)
Lemma dom_lt_pipeline_correct_range bound numeric semis relative :
  dom_lt_trie_all (fun n => (n <= bound)%N) relative ->
  dom_lt_trie_all (fun n => (n <= bound)%N) (dom_lt_correct numeric semis relative).
Proof.
  intro Hrelative. unfold dom_lt_correct.
  apply (dom_lt_fold_invariant (dom_lt_correct_step semis relative)
    (dom_lt_trie_all (fun n => (n <= bound)%N))).
  - apply dom_lt_trie_all_empty.
  - intros st v Hst. now apply dom_lt_pipeline_correct_step_range.
Qed.

(** The member callback changes its link projection exactly as its recorded evaluation. *)
Lemma dom_lt_pipeline_bucket_member_links fuel semis s st v :
  lt_bucket_links (dom_lt_bucket_member fuel semis s st v) =
    dom_lt_phase_step fuel semis (lt_bucket_links st) (LtEval v).
Proof.
  unfold dom_lt_bucket_member, dom_lt_phase_step.
  destruct (dom_lt_eval fuel semis (lt_bucket_links st) v). reflexivity.
Qed.

Local Opaque dom_lt_bucket_member T_dom_lt_bucket_member.

(** A bucket row has exactly the links obtained by replaying its member evaluations. *)
Lemma dom_lt_pipeline_bucket_members_links fuel semis s row st :
  lt_bucket_links (fold_left (dom_lt_bucket_member fuel semis s) row st) =
    fold_left (dom_lt_phase_step fuel semis) (map LtEval row) (lt_bucket_links st).
Proof.
  pose proof (dom_lt_fold_project (dom_lt_bucket_member fuel semis s)
    (fun links v => dom_lt_phase_step fuel semis links (LtEval v)) lt_bucket_links
    (fun _ => True) (fun _ _ _ => I)
    (fun state vertex _ => dom_lt_pipeline_bucket_member_links fuel semis s state vertex)
    row st I) as Hproject.
  exact (eq_trans (proj1 Hproject) (eq_sym
    (dom_lt_fold_mapped (dom_lt_phase_step fuel semis) LtEval row (lt_bucket_links st)))).
Qed.

(** A bucket's recorded sequence is its member evaluations followed by its optional link. *)
Definition dom_lt_pipeline_bucket_sequence (numeric : dom_lt_numeric)
    (buckets : ptrie (list N)) (s : N) : list lt_op :=
  map LtEval (match trie_get (dom_lt_key s) buckets with None => [] | Some row => row end) ++
    match trie_get (dom_lt_key s) (lt_numeric_parent numeric) with
      None => [] | Some p => [LtLink s p] end.

(** The whole bucket phase concatenates the sequence of each processed key. *)
Definition dom_lt_pipeline_buckets_sequence numeric buckets order : list lt_op :=
  flat_map (dom_lt_pipeline_bucket_sequence numeric buckets) order.

(** Flattening an input list runs each associated segment in the same left-fold order. *)
Lemma dom_lt_pipeline_fold_flatten {A B C : Type} (step : A -> B -> A)
    (segment : C -> list B) values initial :
  fold_left step (flat_map segment values) initial =
    fold_left (fun st value => fold_left step (segment value) st) values initial.
Proof.
  revert initial. induction values as [|value rest IH]; intro initial; [reflexivity|].
  cbn [flat_map]. rewrite fold_left_app. exact (IH (fold_left step (segment value) initial)).
Qed.

(** A complete bucket step agrees exactly with its operation-only phase. *)
Lemma dom_lt_pipeline_bucket_step_links numeric semis buckets st s :
  lt_bucket_links (dom_lt_bucket_step numeric semis buckets st s) =
    fold_left (dom_lt_phase_step (lt_numeric_limit numeric) semis)
      (dom_lt_pipeline_bucket_sequence numeric buckets s) (lt_bucket_links st).
Proof.
  unfold dom_lt_bucket_step, dom_lt_pipeline_bucket_sequence.
  rewrite fold_left_app.
  set (row := match trie_get (dom_lt_key s) buckets with None => [] | Some xs => xs end).
  destruct (trie_get (dom_lt_key s) (lt_numeric_parent numeric)) as [parent|].
  - change (dom_lt_link (lt_bucket_links
      (fold_left (dom_lt_bucket_member (lt_numeric_limit numeric) semis s) row st)) s parent =
      dom_lt_link (fold_left (dom_lt_phase_step (lt_numeric_limit numeric) semis)
        (map LtEval row) (lt_bucket_links st)) s parent).
    exact (f_equal (fun links => dom_lt_link links s parent)
      (dom_lt_pipeline_bucket_members_links (lt_numeric_limit numeric) semis s row st)).
  - exact (dom_lt_pipeline_bucket_members_links (lt_numeric_limit numeric) semis s row st).
Qed.

Local Opaque dom_lt_bucket_step T_dom_lt_bucket_step.

(** Folding bucket steps concatenates their exact operation-only phases. *)
Lemma dom_lt_pipeline_bucket_steps_links numeric semis buckets order st :
  lt_bucket_links (fold_left (dom_lt_bucket_step numeric semis buckets) order st) =
    fold_left (dom_lt_phase_step (lt_numeric_limit numeric) semis)
      (dom_lt_pipeline_buckets_sequence numeric buckets order) (lt_bucket_links st).
Proof.
  pose proof (dom_lt_fold_project (dom_lt_bucket_step numeric semis buckets)
    (fun links s => fold_left (dom_lt_phase_step (lt_numeric_limit numeric) semis)
      (dom_lt_pipeline_bucket_sequence numeric buckets s) links) lt_bucket_links
    (fun _ => True) (fun _ _ _ => I)
    (fun state s _ => dom_lt_pipeline_bucket_step_links numeric semis buckets state s)
    order st I) as Hproject.
  exact (eq_trans (proj1 Hproject) (eq_sym
    (dom_lt_pipeline_fold_flatten (dom_lt_phase_step (lt_numeric_limit numeric) semis)
      (dom_lt_pipeline_bucket_sequence numeric buckets) order (lt_bucket_links st)))).
Qed.

(** The bucket phase records precisely the reverse of its forward operation sequence. *)
Lemma dom_lt_pipeline_bucket_steps_log numeric semis buckets order st :
  lt_operations (lt_bucket_links
    (fold_left (dom_lt_bucket_step numeric semis buckets) order st)) =
    rev (dom_lt_pipeline_buckets_sequence numeric buckets order) ++
      lt_operations (lt_bucket_links st).
Proof.
  rewrite dom_lt_pipeline_bucket_steps_links. apply dom_lt_phase_operations.
Qed.

(** Reversing the empty-initial bucket log recovers the exact forward phase. *)
Lemma dom_lt_pipeline_buckets_log numeric semis :
  let buckets := fold_left (dom_lt_bucket_add semis)
    (rev_append (lt_numeric_order numeric) []) Empty in
  rev_append (lt_operations (lt_bucket_links (dom_lt_buckets numeric semis))) [] =
    dom_lt_pipeline_buckets_sequence numeric buckets (lt_numeric_order numeric).
Proof.
  cbn zeta. unfold dom_lt_buckets. rewrite dom_lt_pipeline_bucket_steps_log.
  cbn [lt_bucket_links lt_operations].
  rewrite app_nil_r, rev_append_rev, app_nil_r, rev_involutive. reflexivity.
Qed.

(** A bounded member row adds only linear trie overhead to its exact phase clock. *)
Lemma dom_lt_pipeline_bucket_members_clock bound width fuel semis s row st :
  (forall n, (n <= bound)%N -> N.size_nat n <= width) ->
  dom_lt_trie_all (fun n => (n <= bound)%N) semis ->
  Forall (fun n => (n <= bound)%N) row ->
  dom_lt_pipeline_bucket_bounded bound st -> (s <= bound)%N ->
  (List.T_fold_left (dom_lt_bucket_member fuel semis s)
    (T_dom_lt_bucket_member fuel semis s) row st <=
    List.T_fold_left (dom_lt_phase_step fuel semis) (T_dom_lt_phase_step fuel semis)
      (map LtEval row) (lt_bucket_links st) +
    128 * (PTrieT.c_trie + 1) * N.of_nat (length row * (width + 1)))%N.
Proof.
  intros Hwidth Hsemis Hrow. revert st.
  induction Hrow as [|v rest Hv Hrest IH]; intros st Hst Hs.
  - cbn [map length]. time_unfold @List.T_fold_left. lia.
  - pose proof (dom_lt_pipeline_bucket_member_range bound fuel semis s st v Hst Hs Hv)
      as Hnext.
    specialize (IH (dom_lt_bucket_member fuel semis s st v) Hnext Hs).
    pose proof (dom_lt_eval_bounded bound fuel semis (lt_bucket_links st) v
      (proj1 Hst) Hv) as Heval.
    pose proof (dom_lt_semi_bucket_member_clock width fuel semis s st v
      (Hwidth v Hv) (Hwidth _ (proj2 Heval))
      (Hwidth _ (dom_lt_identity_bounded bound semis _ Hsemis (proj2 Heval)))) as Hhead.
    pose proof (dom_lt_phase_eval_clock fuel semis (lt_bucket_links st) v)
      as Hphase.
    rewrite dom_lt_pipeline_bucket_member_links in IH.
    cbn [map length]. time_unfold @List.T_fold_left.
    fold (List.T_fold_left (dom_lt_bucket_member fuel semis s)
      (T_dom_lt_bucket_member fuel semis s)).
    fold (List.T_fold_left (dom_lt_phase_step fuel semis) (T_dom_lt_phase_step fuel semis)).
    eapply dom_lt_phase_clock_row; [|exact IH|].
    + eapply N.le_trans; [exact Hhead|].
      apply N.add_le_mono; [exact Hphase|apply N.le_refl].
    + clear Hwidth Hsemis Hrest Hst Hs Hv Hnext Heval Hhead Hphase IH.
      rewrite !Nat2N.inj_mul, !Nat2N.inj_succ. nia.
Qed.

(** An empty optional link adds only the two fold-boundary call charges. *)
Lemma dom_lt_pipeline_phase_no_link_clock step row replay extra row_extra total :
  (step <= row + 0 + extra)%N -> (row <= replay + row_extra)%N ->
  (row_extra + extra + 2 <= total)%N -> (step + 2 <= replay + total)%N.
Proof.
  nia.
Qed.

(** One bucket step adds bounded row work to its exact operation-only phase. *)
Lemma dom_lt_pipeline_bucket_step_clock bound width numeric semis buckets st s :
  (forall n, (n <= bound)%N -> N.size_nat n <= width) ->
  dom_lt_numeric_ranges bound numeric ->
  dom_lt_trie_all (fun n => (n <= bound)%N) semis ->
  dom_lt_trie_all (Forall (fun n => (n <= bound)%N)) buckets ->
  dom_lt_pipeline_bucket_bounded bound st -> (s <= bound)%N ->
  (T_dom_lt_bucket_step numeric semis buckets st s + 2 <=
    List.T_fold_left (dom_lt_phase_step (lt_numeric_limit numeric) semis)
      (T_dom_lt_phase_step (lt_numeric_limit numeric) semis)
      (dom_lt_pipeline_bucket_sequence numeric buckets s) (lt_bucket_links st) +
    256 * (PTrieT.c_trie + 1) * N.of_nat
      ((length (match trie_get (dom_lt_key s) buckets with
        None => [] | Some row => row end) + 1) * (width + 1)))%N.
Proof.
  intros Hwidth Hnumeric Hsemis Hrows Hst Hs.
  set (row := match trie_get (dom_lt_key s) buckets with None => [] | Some xs => xs end).
  set (after := fold_left (dom_lt_bucket_member (lt_numeric_limit numeric) semis s) row st).
  assert (Hrow : Forall (fun n => (n <= bound)%N) row).
  { unfold row. destruct (trie_get (dom_lt_key s) buckets) as [xs|] eqn:Hget;
      [exact (Hrows _ _ Hget)|constructor]. }
  pose proof (dom_lt_pipeline_bucket_members_clock bound width (lt_numeric_limit numeric)
    semis s row st Hwidth Hsemis Hrow Hst Hs) as Hmembers.
  pose proof (dom_lt_pipeline_bucket_members_links (lt_numeric_limit numeric)
    semis s row st) as Hlinks. fold after in Hlinks.
  pose proof (dom_lt_semi_bucket_step_clock width numeric semis buckets st s
    (Hwidth s Hs)) as Hraw. fold row after in Hraw.
  unfold dom_lt_pipeline_bucket_sequence. fold row.
  destruct (trie_get (dom_lt_key s) (lt_numeric_parent numeric)) as [parent|] eqn:Hparent.
  - pose proof (dom_lt_fold_clock_app
      (dom_lt_phase_step (lt_numeric_limit numeric) semis)
      (T_dom_lt_phase_step (lt_numeric_limit numeric) semis)
      (map LtEval row) [LtLink s parent] (lt_bucket_links st)) as Happ.
    rewrite <- Hlinks in Happ.
    assert (Hsingle : List.T_fold_left
      (dom_lt_phase_step (lt_numeric_limit numeric) semis)
      (T_dom_lt_phase_step (lt_numeric_limit numeric) semis)
      [LtLink s parent] (lt_bucket_links after) =
      (T_dom_lt_phase_step (lt_numeric_limit numeric) semis
        (lt_bucket_links after) (LtLink s parent) + 2)%N).
    { apply dom_lt_single_fold_clock. }
    rewrite Hsingle in Happ.
    pose proof (dom_lt_phase_link_clock (lt_numeric_limit numeric) semis
      (lt_bucket_links after) s parent) as Hlink.
    eapply dom_lt_phase_clock_settle;
      [exact Hraw|exact Hmembers|exact Hlink|exact Happ|].
    clear Hwidth Hnumeric Hsemis Hrows Hst Hs Hrow Hlinks Hraw Hmembers Happ Hlink Hsingle.
    rewrite !Nat2N.inj_mul, !Nat2N.inj_add. nia.
  - rewrite app_nil_r.
    eapply dom_lt_pipeline_phase_no_link_clock; [exact Hraw|exact Hmembers|].
    clear Hwidth Hnumeric Hsemis Hrows Hst Hs Hrow Hlinks Hraw Hmembers.
    rewrite !Nat2N.inj_mul, !Nat2N.inj_add. nia.
Qed.

(** A bucket-order fold adds linear visited-row overhead to its exact phase clock. *)
Lemma dom_lt_pipeline_bucket_steps_clock bound width numeric semis buckets order st :
  (forall n, (n <= bound)%N -> N.size_nat n <= width) ->
  dom_lt_numeric_ranges bound numeric ->
  dom_lt_trie_all (fun n => (n <= bound)%N) semis ->
  dom_lt_trie_all (Forall (fun n => (n <= bound)%N)) buckets ->
  Forall (fun n => (n <= bound)%N) order ->
  dom_lt_pipeline_bucket_bounded bound st ->
  (List.T_fold_left (dom_lt_bucket_step numeric semis buckets)
    (T_dom_lt_bucket_step numeric semis buckets) order st <=
    List.T_fold_left (dom_lt_phase_step (lt_numeric_limit numeric) semis)
      (T_dom_lt_phase_step (lt_numeric_limit numeric) semis)
      (dom_lt_pipeline_buckets_sequence numeric buckets order) (lt_bucket_links st) +
    512 * (PTrieT.c_trie + 1) * N.of_nat
      ((dom_lt_row_mass (map dom_lt_key order) buckets + length order) * (width + 1)))%N.
Proof.
  intros Hwidth Hnumeric Hsemis Hrows Horder. revert st.
  induction Horder as [|s rest Hs Hrest IH]; intros st Hst.
  - cbn [map length dom_lt_row_mass fold_right dom_lt_pipeline_buckets_sequence flat_map].
    time_unfold @List.T_fold_left. lia.
  - pose proof (dom_lt_pipeline_bucket_step_range bound numeric semis buckets st s
      Hnumeric Hrows Hst Hs) as Hnext.
    specialize (IH (dom_lt_bucket_step numeric semis buckets st s) Hnext).
    pose proof (dom_lt_pipeline_bucket_step_clock bound width numeric semis buckets st s
      Hwidth Hnumeric Hsemis Hrows Hst Hs) as Hhead.
    pose proof (dom_lt_fold_clock_app
      (dom_lt_phase_step (lt_numeric_limit numeric) semis)
      (T_dom_lt_phase_step (lt_numeric_limit numeric) semis)
      (dom_lt_pipeline_bucket_sequence numeric buckets s)
      (dom_lt_pipeline_buckets_sequence numeric buckets rest) (lt_bucket_links st)) as Happ.
    rewrite dom_lt_pipeline_bucket_step_links in IH.
    cbn [map length dom_lt_row_mass fold_right dom_lt_pipeline_buckets_sequence flat_map].
    time_unfold @List.T_fold_left.
    fold (List.T_fold_left (dom_lt_bucket_step numeric semis buckets)
      (T_dom_lt_bucket_step numeric semis buckets)).
    fold (List.T_fold_left (dom_lt_phase_step (lt_numeric_limit numeric) semis)
      (T_dom_lt_phase_step (lt_numeric_limit numeric) semis)).
    eapply dom_lt_phase_clock_flatten; [exact Hhead|exact IH|exact Happ|].
    clear Hwidth Hnumeric Hsemis Hrows Hs Hrest Hst Hnext Hhead Happ IH.
    unfold dom_lt_row_mass.
    rewrite !Nat2N.inj_mul, !Nat2N.inj_add, !Nat2N.inj_succ. nia.
Qed.

(** With distinct numeric keys, all bucket work is linear outside its exact recorded phase. *)
Lemma dom_lt_pipeline_buckets_clock bound width numeric semis :
  (forall n, (n <= bound)%N -> N.size_nat n <= width) ->
  dom_lt_numeric_ranges bound numeric ->
  NoDup (lt_numeric_order numeric) ->
  dom_lt_trie_all (fun n => (n <= bound)%N) semis ->
  (T_dom_lt_buckets numeric semis <=
    List.T_fold_left (dom_lt_phase_step (lt_numeric_limit numeric) semis)
      (T_dom_lt_phase_step (lt_numeric_limit numeric) semis)
      (rev_append (lt_operations (lt_bucket_links (dom_lt_buckets numeric semis))) [])
      (DomLtLinks Empty Empty []) +
    2048 * (PTrieT.c_trie + 1) *
      N.of_nat ((length (lt_numeric_order numeric) + 1) * (width + 1)))%N.
Proof.
  intros Hwidth Hnumeric Hunique Hsemis.
  set (order := lt_numeric_order numeric).
  set (buckets := fold_left (dom_lt_bucket_add semis) (rev_append order []) Empty).
  assert (Horder : Forall (fun n => (n <= bound)%N) order).
  { exact (dom_lt_numeric_order_range _ _ Hnumeric). }
  assert (Horder_width : Forall (fun n => N.size_nat n <= width) order).
  { apply Forall_forall. intros n Hin. apply Hwidth.
    exact (proj1 (Forall_forall _ _) Horder n Hin). }
  assert (Hsemis_width : dom_lt_trie_all (fun n => N.size_nat n <= width) semis).
  { intros key value Hget. apply Hwidth. exact (Hsemis _ _ Hget). }
  assert (Hrows : dom_lt_trie_all (Forall (fun n => (n <= bound)%N)) buckets).
  { apply dom_lt_bucket_build_range. exact Horder. }
  assert (Hinitial : dom_lt_pipeline_bucket_bounded bound
    (DomLtBucketState (DomLtLinks Empty Empty []) Empty)).
  { repeat split; apply dom_lt_trie_all_empty. }
  pose proof (dom_lt_semi_bucket_build_clock width semis order Horder_width Hsemis_width)
    as Hbuild.
  pose proof (dom_lt_pipeline_bucket_steps_clock bound width numeric semis buckets order
    (DomLtBucketState (DomLtLinks Empty Empty []) Empty)
    Hwidth Hnumeric Hsemis Hrows Horder Hinitial) as Hsteps.
  pose proof (dom_lt_bucket_build_mass (map dom_lt_key order) semis
    (rev_append order []) Empty (dom_lt_key_map_unique order Hunique)) as Hmass.
  fold buckets in Hmass. rewrite rev_append_rev, app_nil_r, length_rev,
    dom_lt_row_mass_empty in Hmass.
  rewrite dom_lt_pipeline_buckets_log. fold order buckets.
  unfold T_dom_lt_buckets. time_simpl. fold order buckets.
  change (fun (current : ptrie (list N)) (v : N) =>
    T_dom_lt_bucket_add semis current v) with (T_dom_lt_bucket_add semis).
  change (fun (current : dom_lt_bucket_state) (s : N) =>
    T_dom_lt_bucket_step numeric semis buckets current s) with
    (T_dom_lt_bucket_step numeric semis buckets).
  cbn [lt_bucket_links] in Hsteps.
  rewrite !Nat2N.inj_mul, !Nat2N.inj_add in *.
  clear -Hbuild Hsteps Hmass. nia.
Qed.

Local Transparent dom_lt_bucket_member T_dom_lt_bucket_member
  dom_lt_bucket_step T_dom_lt_bucket_step.

Local Transparent dom_lt_eval T_dom_lt_eval.

(** Isolated numeric conversion arithmetic uses one graph budget for both row mass and width. *)
Lemma dom_lt_pipeline_numeric_fold_budget coefficient width mass budget work :
  (mass * width <= budget)%N -> (mass + 1 <= budget)%N ->
  (work <= (128 * (coefficient + 1) * width + 1) * mass + 1)%N ->
  (work <= 129 * (coefficient + 1) * budget)%N.
Proof.
  intros Hweighted Hunit Hwork. eapply N.le_trans; [exact Hwork|].
  replace ((128 * (coefficient + 1) * width + 1) * mass + 1)%N with
    (128 * (coefficient + 1) * (mass * width) + (mass + 1))%N by ring.
  eapply N.le_trans with (128 * (coefficient + 1) * budget + budget)%N.
  - apply N.add_le_mono; [now apply N.mul_le_mono_l|exact Hunit].
  - nia.
Qed.

(** Three nonnegative clocks combine after their common budget has been established. *)
Lemma dom_lt_pipeline_numeric_budget search trie budget layout reverse rows :
  (1 <= budget)%N ->
  (layout <= 16 * (search + trie + 4096) * budget)%N ->
  (reverse <= budget)%N -> (rows <= 129 * (trie + 1) * budget)%N ->
  (1 + (layout + ((1 + reverse + 1) + rows)) <=
    1024 * (search + trie + 4096) * budget)%N.
Proof.
  nia.
Qed.

(** Numeric conversion is the layout traversal plus linear work over discovered rows. *)
Lemma dom_lt_pipeline_numeric_clock g r : prepared_ok g ->
  (T_dom_lt_numeric_of g r <=
    dom_lt_numeric_coefficient *
      N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
        (graph_width (base g) + 1)))%N.
Proof.
  intro Hprepared.
  pose proof (dom_time_lt_layout g r) as Hlayout.
  pose proof (List.T_rev_append_le (lt_reverse_order (dom_lt_layout_of g r)) []) as Hreverse.
  pose proof (dom_lt_pipeline_layout_of_width g r) as Hlayout_width.
  destruct (dom_lt_dfs_inventory g r) as [Hunique [Hlisted [Hvertices Hedges]]].
  pose proof (dom_lt_predecessor_total g (dom_lt_dfs g r) Hprepared Hunique) as Hpredtotal.
  pose proof (dom_time_fold_left_state (dom_lt_numeric_add g (dom_lt_layout_of g r))
    (T_dom_lt_numeric_add g (dom_lt_layout_of g r)) (fun _ => True)
    (fun v => length (preds g v))
    (128 * (PTrieT.c_trie + 1) * N.of_nat (graph_width (base g) + 1))%N
    (dom_lt_dfs g r)
    (DomLtNumeric [] Empty Empty Empty (lt_next (dom_lt_layout_of g r))) I) as Hfold.
  specialize (Hfold ltac:(intros v Hv st Hst; split; [exact I|];
    pose proof (dom_lt_pipeline_numeric_add_clock (graph_width (base g)) g
      (dom_lt_layout_of g r) st v) as Hcallback;
    specialize (Hcallback
      (dom_listed_key_width g v (Hlisted v Hv))
      (dom_lt_pipeline_discovery_width g r _ (dom_lt_rank_get_discovered g r v))
      (proj2 Hlayout_width));
    assert (Hrow : Forall (fun p => Pos.size_nat p <= graph_width (base g)) (preds g v))
      by (apply Forall_forall; intros p Hp; apply dom_listed_key_width;
        eapply dom_lt_pipeline_preds_listed; eassumption);
    specialize (Hcallback Hrow); rewrite Nat2N.inj_mul in Hcallback; nia)).
  destruct Hfold as [Htrivial Hfold].
  rewrite dom_lt_layout_order_length in Hreverse.
  unfold T_dom_lt_numeric_of. time_simpl. fold (dom_lt_dfs g r).
  change (fun (st : dom_lt_numeric) (v : positive) =>
    T_dom_lt_numeric_add g (dom_lt_layout_of g r) st v) with
    (T_dom_lt_numeric_add g (dom_lt_layout_of g r)).
  set (budget := N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
    (graph_width (base g) + 1))) in *.
  set (mass := fold_right (fun v total => length (preds g v) + total) 0
    (dom_lt_dfs g r) + length (dom_lt_dfs g r)).
  assert (Hmass : mass <= graph_n (base g) + graph_e (base g)).
  { unfold mass. clear -Hpredtotal Hvertices. lia. }
  assert (Hweighted : (N.of_nat mass * N.of_nat (graph_width (base g) + 1) <= budget)%N).
  { unfold budget. rewrite <- Nat2N.inj_mul. apply time_of_nat_le, Nat.mul_le_mono_r. lia. }
  assert (Hunit : (N.of_nat mass + 1 <= budget)%N).
  { assert (Hnatural : mass + 1 <=
      (graph_n (base g) + graph_e (base g) + 1) * (graph_width (base g) + 1)).
    { eapply Nat.le_trans with (graph_n (base g) + graph_e (base g) + 1); [lia|].
      replace (graph_n (base g) + graph_e (base g) + 1) with
        ((graph_n (base g) + graph_e (base g) + 1) * 1) at 1 by lia.
      apply Nat.mul_le_mono_l. lia. }
    apply time_of_nat_le in Hnatural. rewrite Nat2N.inj_add in Hnatural.
    exact Hnatural. }
  fold mass in Hfold.
  pose proof (dom_lt_pipeline_numeric_fold_budget PTrieT.c_trie
    (N.of_nat (graph_width (base g) + 1)) (N.of_nat mass) budget _
    Hweighted Hunit Hfold) as Hfold_paid.
  assert (Hreverse_paid : (List.T_rev_append
    (lt_reverse_order (dom_lt_layout_of g r)) [] <= budget)%N).
  { eapply N.le_trans; [exact Hreverse|].
    eapply N.le_trans; [|exact Hunit].
    unfold mass. rewrite Nat2N.inj_add. lia. }
  assert (Hpositive : (1 <= budget)%N) by (clear -Hunit; lia).
  unfold dom_lt_numeric_coefficient.
  eapply dom_lt_pipeline_numeric_budget;
    [exact Hpositive|exact Hlayout|exact Hreverse_paid|exact Hfold_paid].
Qed.


(* END G2-G BUCKET SUPPORT *)

Local Opaque Argent.Loop.loop T_loopN.

(** One abstract loop budget absorbs the primitive setup and result-selection costs. *)
Lemma dom_lt_eval_path_budget loop_coefficient trie_coefficient count width
    loop_work setup_work double_work branch_work run_width :
  (loop_work <= loop_coefficient *
    ((128 * (trie_coefficient + 1) * (width + 1) + 1) * (2 * count + 1) +
      128 * (trie_coefficient + 1) * (width + 1) + run_width + 1))%N ->
  (setup_work <= width + 5)%N -> (double_work <= 1)%N -> (branch_work <= 1)%N ->
  (run_width <= width + 4)%N ->
  (8 + double_work + setup_work + loop_work + branch_work <=
    1024 * (loop_coefficient + 1) * (trie_coefficient + 1) *
      ((count + 1) * (width + 1)))%N.
Proof.
  intros Hloop Hsetup Hdouble Hbranch Hrun_width.
  set (base_unit := ((trie_coefficient + 1) * (width + 1))%N).
  set (frames := (count + 1)%N).
  set (budget := (base_unit * frames)%N).
  assert (Hbase_positive : (1 <= base_unit)%N) by (unfold base_unit; nia).
  assert (Hwidth_base : (width + 1 <= base_unit)%N) by (unfold base_unit; nia).
  assert (Hframes_positive : (1 <= frames)%N) by (unfold frames; lia).
  assert (Hbase_budget : (base_unit <= budget)%N) by (unfold budget; nia).
  assert (Hbudget_positive : (1 <= budget)%N) by lia.
  assert (Hunit : (128 * (trie_coefficient + 1) * (width + 1) =
    128 * base_unit)%N) by (unfold base_unit; nia).
  rewrite !Hunit in Hloop.
  assert (Hstep_unit : (128 * base_unit + 1 <= 129 * base_unit)%N) by lia.
  assert (Hframe_count : (2 * count + 1 <= 2 * frames)%N) by (unfold frames; lia).
  assert (Hscaled : ((128 * base_unit + 1) * (2 * count + 1) <=
    (129 * base_unit) * (2 * frames))%N) by (now apply N.mul_le_mono).
  replace ((129 * base_unit) * (2 * frames))%N with (258 * budget)%N
    in Hscaled by (unfold budget; nia).
  assert (Hremainder : (128 * base_unit + run_width + 1 <= 133 * budget)%N).
  { eapply N.le_trans with (133 * base_unit)%N; [lia|]. now apply N.mul_le_mono_l. }
  assert (Hinterior : ((128 * base_unit + 1) * (2 * count + 1) +
    128 * base_unit + run_width + 1 <= 391 * budget)%N).
  { clearbody budget. clear -Hscaled Hremainder. lia. }
  assert (Hloop_big : (loop_work <= 391 * loop_coefficient * budget)%N).
  { replace (391 * loop_coefficient * budget)%N with
      (loop_coefficient * (391 * budget))%N by nia.
    eapply N.le_trans; [exact Hloop|]. now apply N.mul_le_mono_l. }
  assert (Hsetup_big : (setup_work <= 5 * budget)%N).
  { eapply N.le_trans with (5 * base_unit)%N; [lia|]. now apply N.mul_le_mono_l. }
  replace (1024 * (loop_coefficient + 1) * (trie_coefficient + 1) *
    (frames * (width + 1)))%N with
      (1024 * (loop_coefficient + 1) * budget)%N by (unfold budget, base_unit; nia).
  clearbody budget base_unit frames.
  clear -Hloop_big Hsetup_big Hdouble Hbranch Hbudget_positive.
  assert (Hrest : (8 + double_work + setup_work + branch_work <= 15 * budget)%N) by lia.
  assert (Htotal : (8 + double_work + setup_work + loop_work + branch_work <=
    391 * loop_coefficient * budget + 15 * budget)%N) by lia.
  eapply N.le_trans; [exact Htotal|].
  rewrite <- N.mul_add_distr_r. apply N.mul_le_mono_r. lia.
Qed.

(** Evaluation time is bounded by the guarded path length times the numeric key width. *)
Lemma dom_lt_time_eval_path bound width fuel semis before start path root :
  dom_lt_walk_path before start path root ->
  dom_lt_trie_all (fun value => (value <= bound)%N) semis ->
  (forall value, (value <= bound)%N -> N.size_nat value <= width) ->
  dom_lt_links_bounded bound before -> (start <= bound)%N -> N.size_nat fuel <= width + 1 ->
  (T_dom_lt_eval fuel semis before start <=
    1024 * (c_loopN + 1) * (PTrieT.c_trie + 1) *
      N.of_nat ((length path + 1) * (width + 1)))%N.
Proof.
  intros Hpath Hsemis Hwidth Hlinks Hstart Hfuel_width.
  pose proof (dom_lt_walk_path_natural before start path root Hpath) as Hnatural.
  pose proof (dom_gap_path_unique _ _ _ _ Hnatural) as Hunique.
  set (initial := DomLtWalk
    (DomLtLinks (lt_shortcut before) (lt_label before) (LtEval start :: lt_operations before))
    (DomLtDescend start [])).
  set (unit := (128 * (PTrieT.c_trie + 1) * N.of_nat (width + 1))%N).
  assert (Hshape : dom_lt_compress_shape before path root initial).
  { unfold initial. split; [reflexivity|]. exists path. split; [exact Hpath|reflexivity]. }
  assert (Hinitial : dom_lt_walk_bounded bound initial).
  { split; [exact Hlinks|]. split; [exact Hstart|constructor]. }
  assert (Hpreserve : forall state next, dom_lt_walk_bounded bound state ->
    dom_lt_compress_step semis state = inl next -> dom_lt_walk_bounded bound next).
  { intros state next Hinv Hstep.
    pose proof (dom_lt_compress_bounded bound semis state Hinv) as Hnext.
    now rewrite Hstep in Hnext. }
  assert (Hcost : forall state, dom_lt_walk_bounded bound state ->
    (T_dom_lt_compress_step semis state <= unit)%N).
  { intros state Hinv. unfold unit. now apply (dom_lt_time_compress_step bound width). }
  pose proof (dom_lt_compress_path_time before path root semis (dom_lt_walk_bounded bound)
    unit (N.double fuel + 3)%N initial Hunique Hshape Hinitial Hpreserve Hcost) as Hloop.
  set (loop_cost := T_loopN (dom_lt_compress_step semis) (T_dom_lt_compress_step semis)
    (N.double fuel + 3)%N initial).
  change (loop_cost <= c_loopN * ((unit + 1) * N.of_nat (2 * length path - 0 + 1) +
    unit + N.of_nat (N.size_nat (N.double fuel + 3)) + 1))%N in Hloop.
  rewrite Nat.sub_0_r in Hloop.
  pose proof (dom_lt_double_width fuel) as Hdouble_width.
  pose proof (dom_add_width (N.double fuel) 3%N) as Hsum_width.
  change (N.size_nat (N.double fuel + 3) <= N.size_nat (N.double fuel) + 2) in Hsum_width.
  assert (Hactual_width : N.size_nat (N.double fuel + 3) <= width + 4) by lia.
  pose proof (N.T_add_le (N.double fuel) 3%N) as Hsetup.
  change (N.T_add (N.double fuel) 3 <=
    N.of_nat (N.size_nat (N.double fuel) + 2) + 1)%N in Hsetup.
  pose proof (dom_lt_time_double fuel) as Hdouble.
  pose proof (dom_lt_result_branch
    (loopN (dom_lt_compress_step semis) (N.double fuel + 3)%N initial)) as Hbranch.
  unfold T_dom_lt_eval. fold initial. time_simpl.
  change (T_loopN (dom_lt_compress_step semis)
    (fun state => T_dom_lt_compress_step semis state) (N.double fuel + 3)%N initial)
    with loop_cost.
  unfold unit in Hloop. clearbody loop_cost.
  apply time_of_nat_le in Hactual_width, Hdouble_width, Hfuel_width.
  rewrite !Nat2N.inj_add, !Nat2N.inj_mul, !Nat2N.inj_add in *.
  set (walk_result := loopN (dom_lt_compress_step semis) (N.double fuel + 3)%N initial) in *.
  set (branch_work := (match walk_result with inl _ => 1 | inr _ => 0 end)%N) in *.
  set (setup_work := N.T_add (N.double fuel) 3%N) in *.
  set (double_work := N.T_double fuel) in *.
  set (run_width := N.of_nat (N.size_nat (N.double fuel + 3))) in *.
  set (double_width := N.of_nat (N.size_nat (N.double fuel))) in *.
  set (fuel_width := N.of_nat (N.size_nat fuel)) in *.
  set (width_bits := N.of_nat width) in *.
  set (path_count := N.of_nat (length path)) in *.
  set (loop_coefficient := c_loopN) in *.
  set (trie_coefficient := PTrieT.c_trie) in *.
  clearbody branch_work walk_result setup_work double_work run_width double_width fuel_width
    width_bits path_count loop_coefficient trie_coefficient.
  clear -Hloop Hactual_width Hsetup Hdouble Hdouble_width Hfuel_width Hbranch.
  eapply N.le_trans with (8 + double_work + setup_work + loop_cost + branch_work)%N.
  - lia.
  - apply dom_lt_eval_path_budget with (run_width := run_width); try assumption. lia.
Qed.

(** * Semidominator phase clocks and complete parent-producer composition *)

Local Opaque dom_lt_eval T_dom_lt_eval dom_lt_predecessor T_dom_lt_predecessor.
Local Opaque dom_lt_settle T_dom_lt_settle.

(** Predecessor overhead is linear, and every evaluator call is charged to its final replay. *)
Lemma dom_lt_predecessors_phase_clock bound width known limit current final incoming :
  (forall n, (n <= bound)%N -> N.size_nat n <= width) ->
  dom_lt_scores_agree known current final ->
  dom_lt_clock_below current final ->
  dom_lt_trie_all (fun n => (n <= bound)%N) current ->
  Forall (fun n => (n <= bound)%N) incoming -> forall acc,
  dom_lt_predecessor_bounded bound acc ->
  dom_lt_links_known known (fst (fst acc)) ->
  (List.T_fold_left (dom_lt_predecessor limit current)
      (T_dom_lt_predecessor limit current) incoming acc <=
    List.T_fold_left (dom_lt_phase_step limit final) (T_dom_lt_phase_step limit final)
      (map LtEval incoming) (fst (fst acc)) +
    64 * N.of_nat (length incoming) * N.of_nat (width + 1))%N.
Proof.
  intros Hwidth Hscores Hbelow Hcurrent Hincoming.
  induction Hincoming as [|source rest Hsource Hrest IH]; intros acc Hbounded Hknown.
  - cbn [map length]. time_unfold @List.T_fold_left. nia.
  - pose proof (dom_lt_predecessor_range bound limit current acc source
      Hcurrent Hbounded Hsource) as Hnextbound.
    assert (Hnextknown : dom_lt_links_known known
      (fst (fst (dom_lt_predecessor limit current acc source)))).
    { rewrite dom_lt_predecessor_links. now apply dom_lt_eval_known. }
    specialize (IH (dom_lt_predecessor limit current acc source) Hnextbound Hnextknown).
    destruct (dom_lt_eval_agree known current final limit (fst (fst acc)) source
      Hscores Hknown) as [Heval Hclock].
    specialize (Hclock Hbelow).
    assert (Hnext : fst (fst (dom_lt_predecessor limit current acc source)) =
      dom_lt_phase_step limit final (fst (fst acc)) (LtEval source)).
    { rewrite dom_lt_predecessor_links, Heval. reflexivity. }
    rewrite Hnext in IH.
    assert (Hhead : (T_dom_lt_predecessor limit current acc source <=
      T_dom_lt_phase_step limit final (fst (fst acc)) (LtEval source) +
      64 * N.of_nat (width + 1))%N).
    { destruct acc as [[links best] witness].
      destruct Hbounded as [Hlinks [Hbest Hwitness]].
      destruct (dom_lt_eval_bounded bound limit current links source Hlinks Hsource)
        as [Hafter Hchosen].
      pose proof (dom_lt_identity_bounded bound current
        (snd (dom_lt_eval limit current links source)) Hcurrent Hchosen) as Hcandidate.
      pose proof (dom_lt_semi_predecessor_clock width limit current links best witness source
        (Hwidth _ Hchosen) (Hwidth _ Hcandidate)) as Hcost.
      cbn [fst] in Hclock.
      pose proof (dom_lt_phase_eval_clock limit final links source) as Hphase.
      cbn [fst]. clear -Hcost Hclock Hphase. lia. }
    cbn [map length]. time_unfold @List.T_fold_left.
    fold (List.T_fold_left (dom_lt_predecessor limit current)
      (T_dom_lt_predecessor limit current)).
    fold (List.T_fold_left (dom_lt_phase_step limit final) (T_dom_lt_phase_step limit final)).
    eapply dom_lt_phase_clock_row; [exact Hhead|exact IH|].
    clear -width rest. rewrite Nat2N.inj_succ. nia.
Qed.

(** Settlement pays its two writes outside the row replay and one final link. *)
Lemma dom_lt_settle_phase_clock bound width known numeric before vertex final :
  (forall n, (n <= bound)%N -> N.size_nat n <= width) ->
  dom_lt_numeric_ranges bound numeric -> dom_lt_semi_bounded bound before ->
  (vertex <= bound)%N ->
  dom_lt_scores_agree known (lt_semis before) final ->
  dom_lt_clock_below (lt_semis before) final ->
  dom_lt_links_known known (lt_semi_links before) ->
  (T_dom_lt_settle numeric before vertex + 2 <=
    List.T_fold_left (dom_lt_phase_step (lt_numeric_limit numeric) final)
      (T_dom_lt_phase_step (lt_numeric_limit numeric) final)
      (dom_lt_settle_sequence numeric vertex) (lt_semi_links before) +
    256 * (PTrieT.c_trie + 1) *
      N.of_nat ((length (match trie_get (dom_lt_key vertex) (lt_numeric_pred numeric) with
        None => [] | Some row => row end) + 1) * (width + 1)))%N.
Proof.
  intros Hwidth Hnumeric Hbefore Hvertex Hscores Hbelow Hknown.
  destruct Hnumeric as [Horder Hparents Hpreds].
  destruct Hbefore as [Hsemis [Hmin Hlinks]].
  unfold dom_lt_settle_sequence.
  destruct (trie_get (dom_lt_key vertex) (lt_numeric_parent numeric)) as [parent|] eqn:Hparent.
  - set (incoming := match trie_get (dom_lt_key vertex) (lt_numeric_pred numeric) with
      None => [] | Some row => row end).
    assert (Hincoming : Forall (fun n => (n <= bound)%N) incoming).
    { unfold incoming.
      destruct (trie_get (dom_lt_key vertex) (lt_numeric_pred numeric)) as [row|] eqn:Hrow;
        [now apply (Hpreds (dom_lt_key vertex))|constructor]. }
    pose proof (Hparents (dom_lt_key vertex) parent Hparent) as Hp.
    assert (Hinitial : dom_lt_predecessor_bounded bound
      (lt_semi_links before, parent, parent)).
    { split; [exact Hlinks|now split]. }
    pose proof (dom_lt_predecessors_phase_clock bound width known (lt_numeric_limit numeric)
      (lt_semis before) final incoming Hwidth Hscores Hbelow Hsemis Hincoming
      (lt_semi_links before, parent, parent) Hinitial Hknown) as Hrow.
    destruct (dom_lt_predecessors_phase known (lt_numeric_limit numeric)
      (lt_semis before) final incoming Hscores (lt_semi_links before, parent, parent) Hknown)
      as [Hvalue Hafter].
    cbn [fst] in Hvalue, Hafter.
    pose proof (dom_lt_semi_settle_live_clock width numeric before vertex parent
      (Hwidth _ Hvertex) Hparent) as Hsettle. cbn zeta in Hsettle. fold incoming in Hsettle.
    pose proof (dom_lt_fold_clock_app
      (dom_lt_phase_step (lt_numeric_limit numeric) final)
      (T_dom_lt_phase_step (lt_numeric_limit numeric) final)
      (map LtEval incoming) [LtLink vertex parent] (lt_semi_links before)) as Hsplit.
    rewrite <- Hvalue in Hsplit. cbn [fst] in Hrow.
    pose proof (dom_lt_phase_link_clock (lt_numeric_limit numeric) final
      (fst (fst (fold_left (dom_lt_predecessor (lt_numeric_limit numeric) (lt_semis before))
        incoming (lt_semi_links before, parent, parent)))) vertex parent) as Hlink.
    rewrite dom_lt_single_fold_clock in Hsplit.
    eapply dom_lt_phase_clock_settle;
      [exact Hsettle|exact Hrow|exact Hlink|exact Hsplit|].
    clear -width incoming. rewrite Nat2N.inj_mul, Nat2N.inj_add.
    assert (Hw : (1 <= N.of_nat (width + 1))%N) by lia. nia.
  - pose proof (dom_lt_semi_settle_stop_clock width numeric before vertex
      (Hwidth _ Hvertex) Hparent) as Hstop.
    time_unfold @List.T_fold_left. clear -Hstop.
    rewrite Nat2N.inj_mul, Nat2N.inj_add.
    assert (Hw : (1 <= N.of_nat (width + 1))%N) by lia. nia.
Qed.

(** The settlement work measure counts each numeric vertex and each predecessor occurrence. *)
Definition dom_lt_settlement_work (numeric : dom_lt_numeric) (order : list N) : nat :=
  fold_right (fun vertex total =>
    length (match trie_get (dom_lt_key vertex) (lt_numeric_pred numeric) with
      None => [] | Some row => row end) + 1 + total) 0 order.

(** The measure is the vertex count plus the total predecessor-row length. *)
Lemma dom_lt_settlement_work_sum numeric order :
  dom_lt_settlement_work numeric order = length order +
    fold_right (fun vertex total =>
      length (match trie_get (dom_lt_key vertex) (lt_numeric_pred numeric) with
        None => [] | Some row => row end) + total) 0 order.
Proof.
  induction order as [|vertex rest IH]; [reflexivity|].
  unfold dom_lt_settlement_work in *. cbn [fold_right length] in *. lia.
Qed.

(** The original settlement fold is its exact final-score replay plus linear overhead. *)
Lemma dom_lt_settlements_phase_clock bound width numeric order :
  (forall n, (n <= bound)%N -> N.size_nat n <= width) ->
  dom_lt_numeric_ranges bound numeric -> NoDup order ->
  Forall (fun n => (n <= bound)%N) order -> forall before,
  dom_lt_semi_bounded bound before ->
  dom_lt_links_known (fun query => ~ In query order) (lt_semi_links before) ->
  (List.T_fold_left (dom_lt_settle numeric) (T_dom_lt_settle numeric) order before <=
    List.T_fold_left
      (dom_lt_phase_step (lt_numeric_limit numeric)
        (lt_semis (fold_left (dom_lt_settle numeric) order before)))
      (T_dom_lt_phase_step (lt_numeric_limit numeric)
        (lt_semis (fold_left (dom_lt_settle numeric) order before)))
      (dom_lt_settlements_sequence numeric order) (lt_semi_links before) +
    256 * (PTrieT.c_trie + 1) *
      N.of_nat (dom_lt_settlement_work numeric order * (width + 1)))%N.
Proof.
  intros Hwidth Hnumeric Hunique.
  induction Hunique as [|vertex rest Hfresh Hunique IH]; intros Hranges before Hbefore Hknown.
  - cbn [dom_lt_settlements_sequence flat_map dom_lt_settlement_work fold_right].
    time_unfold @List.T_fold_left. nia.
  - inversion Hranges as [|head tail Hvertex Hrest]; subst head tail.
    set (after := dom_lt_settle numeric before vertex).
    set (final := lt_semis (fold_left (dom_lt_settle numeric) rest after)).
    assert (Hscores : dom_lt_scores_agree (fun query => ~ In query (vertex :: rest))
      (lt_semis before) final).
    { intros query Houtside. unfold final, after. symmetry.
      change (dom_lt_identity
        (lt_semis (fold_left (dom_lt_settle numeric) (vertex :: rest) before)) query =
        dom_lt_identity (lt_semis before) query).
      now apply dom_lt_settlements_score_frame. }
    destruct (dom_lt_settle_phase (fun query => ~ In query (vertex :: rest))
      numeric before vertex final Hscores Hknown) as [Hstep Hlinked].
    fold after in Hstep, Hlinked.
    assert (Hnext : dom_lt_links_known (fun query => ~ In query rest) (lt_semi_links after)).
    { eapply dom_lt_links_known_mono; [|exact Hlinked].
      intros query [Houtside|Heq] Hin.
      - apply Houtside. now right.
      - subst query. contradiction. }
    assert (Hafter : dom_lt_semi_bounded bound after).
    { unfold after. now apply dom_lt_settle_range. }
    specialize (IH Hrest after Hafter Hnext). fold final in IH.
    assert (Hbelow : dom_lt_clock_below (lt_semis before) final).
    { exact (dom_lt_settlements_clock_below numeric (vertex :: rest) before). }
    pose proof (dom_lt_settle_phase_clock bound width
      (fun query => ~ In query (vertex :: rest)) numeric before vertex final
      Hwidth Hnumeric Hbefore Hvertex Hscores Hbelow Hknown) as Hhead.
    pose proof (dom_lt_fold_clock_app (dom_lt_phase_step (lt_numeric_limit numeric) final)
      (T_dom_lt_phase_step (lt_numeric_limit numeric) final)
      (dom_lt_settle_sequence numeric vertex) (dom_lt_settlements_sequence numeric rest)
      (lt_semi_links before)) as Hsplit.
    rewrite <- Hstep in Hsplit.
    change (List.T_fold_left (dom_lt_settle numeric) (T_dom_lt_settle numeric)
      (vertex :: rest) before <=
      List.T_fold_left (dom_lt_phase_step (lt_numeric_limit numeric) final)
        (T_dom_lt_phase_step (lt_numeric_limit numeric) final)
        (dom_lt_settle_sequence numeric vertex ++ dom_lt_settlements_sequence numeric rest)
        (lt_semi_links before) + 256 * (PTrieT.c_trie + 1) *
        N.of_nat (dom_lt_settlement_work numeric (vertex :: rest) * (width + 1)))%N.
    time_unfold @List.T_fold_left. fold after.
    fold (List.T_fold_left (dom_lt_settle numeric) (T_dom_lt_settle numeric)).
    fold (List.T_fold_left (dom_lt_phase_step (lt_numeric_limit numeric) final)
      (T_dom_lt_phase_step (lt_numeric_limit numeric) final)).
    change (dom_lt_settlement_work numeric (vertex :: rest)) with
      (length (match trie_get (dom_lt_key vertex) (lt_numeric_pred numeric) with
        None => [] | Some row => row end) + 1 + dom_lt_settlement_work numeric rest).
    eapply dom_lt_phase_clock_flatten; [exact Hhead|exact IH|exact Hsplit|].
    rewrite !Nat2N.inj_mul, !Nat2N.inj_add.
    clear -width numeric vertex rest. nia.
Qed.

(** The semidominator wrapper and its order projection add two calls to the settlement fold. *)
Lemma dom_lt_semidominators_phase_clock bound width numeric :
  (forall n, (n <= bound)%N -> N.size_nat n <= width) ->
  dom_lt_numeric_ranges bound numeric -> NoDup (lt_numeric_order numeric) ->
  (T_dom_lt_semidominators numeric <=
    List.T_fold_left
      (dom_lt_phase_step (lt_numeric_limit numeric) (lt_semis (dom_lt_semidominators numeric)))
      (T_dom_lt_phase_step (lt_numeric_limit numeric) (lt_semis (dom_lt_semidominators numeric)))
      (dom_lt_settlements_sequence numeric (lt_numeric_order numeric))
      (DomLtLinks Empty Empty []) +
    512 * (PTrieT.c_trie + 1) *
      N.of_nat ((dom_lt_settlement_work numeric (lt_numeric_order numeric) + 1) *
        (width + 1)))%N.
Proof.
  intros Hwidth Hnumeric Hunique.
  pose proof (dom_lt_settlements_phase_clock bound width numeric (lt_numeric_order numeric)
    Hwidth Hnumeric Hunique (dom_lt_numeric_order_range bound numeric Hnumeric)
    (DomLtSemiState Empty Empty (DomLtLinks Empty Empty []))) as Hfold.
  assert (Hempty : dom_lt_semi_bounded bound
    (DomLtSemiState Empty Empty (DomLtLinks Empty Empty []))).
  { repeat split; apply dom_lt_trie_all_empty. }
  specialize (Hfold Hempty (dom_lt_empty_links_known _)).
  cbn [lt_semi_links] in Hfold. fold (dom_lt_semidominators numeric) in Hfold.
  unfold T_dom_lt_semidominators. time_simpl.
  change (fun (state : dom_lt_semi_state) (vertex : N) => T_dom_lt_settle numeric state vertex)
    with (T_dom_lt_settle numeric).
  eapply dom_lt_phase_clock_wrapper with
    (extra := (256 * (PTrieT.c_trie + 1) *
      N.of_nat (dom_lt_settlement_work numeric (lt_numeric_order numeric) * (width + 1)) + 1)%N).
  - eapply dom_lt_phase_clock_wrapper; [exact Hfold|reflexivity].
  - rewrite !Nat2N.inj_mul, !Nat2N.inj_add.
    assert (Hw : (1 <= N.of_nat (width + 1))%N) by lia.
    clear -Hw width numeric. nia.
Qed.

Local Opaque T_dom_lt_numeric_of T_dom_lt_semidominators T_dom_lt_buckets.
Local Opaque T_dom_lt_correct T_dom_lt_erase.

(** The pipeline does no more work than the parent producer, which also erases numeric keys. *)
Lemma dom_lt_pipeline_parent_clock g r :
  (T_dom_lt_pipeline g r <= T_dom_lt_parents g r)%N.
Proof.
  unfold T_dom_lt_pipeline, T_dom_lt_parents. time_simpl. lia.
Qed.

(** A closed coefficient covers numeric conversion and all work outside replay. *)
Definition dom_lt_semi_coefficient : N :=
  (dom_lt_numeric_coefficient + (16 * 4096) * (PTrieT.c_trie + 1))%N.

(** The full parent producer is linear outside the two exactly replayed link forests. *)
Lemma dom_lt_parents_replay_clock g r : prepared_ok g ->
  (T_dom_lt_parents g r + 1 <=
    dom_lt_semi_coefficient *
      N.of_nat ((graph_n (base g) + graph_e (base g) + 1) * (graph_width (base g) + 1)) +
    T_dom_lt_run_ops (dom_lt_ops g r) (dom_lt_replay_initial g r))%N.
Proof.
  intro Hprepared.
  set (numeric := dom_lt_numeric_of g r).
  set (semi := dom_lt_semidominators numeric).
  set (bucket := dom_lt_buckets numeric (lt_semis semi)).
  set (parents := dom_lt_correct numeric (lt_semis semi) (lt_relative bucket)).
  set (bound := N.of_nat (length (dom_lt_dfs g r))).
  set (width := graph_width (base g)).
  set (budget := N.of_nat ((graph_n (base g) + graph_e (base g) + 1) * (width + 1))).
  assert (Hnumeric : dom_lt_numeric_ranges bound numeric) by apply dom_lt_numeric_of_ranges.
  assert (Hunique : NoDup (lt_numeric_order numeric)) by apply dom_lt_numeric_order_unique.
  assert (Hwidth : forall n, (n <= bound)%N -> N.size_nat n <= width).
  { intros n Hn. now apply (dom_lt_pipeline_discovery_width g r). }
  pose proof (dom_lt_semidominators_range bound numeric Hnumeric) as Hsemi_range.
  fold semi in Hsemi_range.
  pose proof (dom_lt_pipeline_buckets_range bound numeric (lt_semis semi) Hnumeric)
    as Hbucket_range. fold bucket in Hbucket_range.
  pose proof (dom_lt_pipeline_correct_range bound numeric (lt_semis semi) (lt_relative bucket)
    (proj2 Hbucket_range)) as Hparent_range. fold parents in Hparent_range.
  assert (Horder_width : Forall (fun n => N.size_nat n <= width) (lt_numeric_order numeric)).
  { apply Forall_forall. intros n Hin. apply Hwidth.
    exact (proj1 (Forall_forall _ _) (dom_lt_numeric_order_range _ _ Hnumeric) n Hin). }
  assert (Hrelative_width : dom_lt_trie_all (fun n => N.size_nat n <= width)
    (lt_relative bucket)).
  { intros key n Hget. apply Hwidth. exact (proj2 Hbucket_range key n Hget). }
  assert (Hparent_width : dom_lt_trie_all (fun n => N.size_nat n <= width) parents).
  { intros key n Hget. apply Hwidth. exact (Hparent_range key n Hget). }
  pose proof (dom_lt_pipeline_numeric_clock g r Hprepared) as Hnumeric_clock.
  fold width in Hnumeric_clock. fold budget in Hnumeric_clock.
  pose proof (dom_lt_semidominators_phase_clock bound width numeric Hwidth Hnumeric Hunique)
    as Hsemi_clock. fold semi in Hsemi_clock.
  pose proof (dom_lt_pipeline_buckets_clock bound width numeric (lt_semis semi)
    Hwidth Hnumeric Hunique (proj1 Hsemi_range)) as Hbucket_clock.
  fold bucket in Hbucket_clock.
  pose proof (dom_lt_semi_correct_clock width numeric (lt_semis semi) (lt_relative bucket)
    Horder_width Hrelative_width) as Hcorrect_clock.
  pose proof (dom_lt_pipeline_erase_clock width numeric parents Horder_width Hparent_width
    (dom_lt_pipeline_numeric_vertex_width g r)) as Herase_clock.
  assert (Horder : length (lt_numeric_order numeric) <= graph_n (base g)).
  { unfold numeric. rewrite dom_lt_numeric_order_length.
    exact (proj1 (proj2 (proj2 (dom_lt_dfs_inventory g r)))). }
  assert (Hwork : dom_lt_settlement_work numeric (lt_numeric_order numeric) <=
    graph_n (base g) + graph_e (base g)).
  { rewrite dom_lt_settlement_work_sum.
    pose proof (dom_lt_numeric_pred_total g r Hprepared) as Hpredecessors.
    fold numeric in Hpredecessors. lia. }
  assert (Horderbudget : (N.of_nat ((length (lt_numeric_order numeric) + 1) * (width + 1))
    <= budget)%N).
  { unfold budget. apply time_of_nat_le, Nat.mul_le_mono_r. lia. }
  assert (Hworkbudget : (N.of_nat
    ((dom_lt_settlement_work numeric (lt_numeric_order numeric) + 1) * (width + 1)) <=
    budget)%N).
  { unfold budget. apply time_of_nat_le, Nat.mul_le_mono_r. lia. }
  set (semi_ops := dom_lt_settlements_sequence numeric (lt_numeric_order numeric)).
  set (bucket_ops := rev_append (lt_operations (lt_bucket_links bucket)) []).
  fold semi_ops in Hsemi_clock. fold bucket_ops in Hbucket_clock.
  pose proof (dom_lt_pipeline_replay_two_phases (lt_numeric_limit numeric)
    (lt_semis semi) semi_ops bucket_ops) as Hreplay.
  assert (Hsemilog : lt_operations (lt_semi_links semi) = rev semi_ops).
  { apply dom_lt_semidominators_log, Hunique. }
  assert (Hoperations : dom_lt_ops g r = semi_ops ++ bucket_ops).
  { unfold dom_lt_ops, dom_lt_pipeline. fold numeric. fold semi. fold bucket.
    cbn [result_semi result_bucket]. fold bucket_ops.
    rewrite rev_append_rev, Hsemilog, rev_involutive. reflexivity. }
  assert (Hinitial : dom_lt_replay_initial g r =
    DomLtReplay (DomLtLinks Empty Empty []) (lt_semis semi) (lt_numeric_limit numeric)
      (N.of_nat (length semi_ops)) 0%N).
  { unfold dom_lt_replay_initial, dom_lt_pipeline. fold numeric. fold semi. fold bucket.
    cbn [result_semi result_numeric]. rewrite Hsemilog, length_rev. reflexivity. }
  rewrite <- Hoperations, <- Hinitial in Hreplay.
  assert (Hsemi_paid : (T_dom_lt_semidominators numeric <=
    List.T_fold_left (dom_lt_phase_step (lt_numeric_limit numeric) (lt_semis semi))
      (T_dom_lt_phase_step (lt_numeric_limit numeric) (lt_semis semi))
      semi_ops (DomLtLinks Empty Empty []) + 512 * (PTrieT.c_trie + 1) * budget)%N).
  { pose proof (N.mul_le_mono_l _ _ (512 * (PTrieT.c_trie + 1))%N Hworkbudget) as Hscale.
    clear -Hsemi_clock Hscale. nia. }
  assert (Hbucket_paid : (T_dom_lt_buckets numeric (lt_semis semi) <=
    List.T_fold_left (dom_lt_phase_step (lt_numeric_limit numeric) (lt_semis semi))
      (T_dom_lt_phase_step (lt_numeric_limit numeric) (lt_semis semi))
      bucket_ops (DomLtLinks Empty Empty []) + 2048 * (PTrieT.c_trie + 1) * budget)%N).
  { pose proof (N.mul_le_mono_l _ _ (2048 * (PTrieT.c_trie + 1))%N Horderbudget) as Hscale.
    clear -Hbucket_clock Hscale. nia. }
  assert (Hcorrect_paid : (T_dom_lt_correct numeric (lt_semis semi) (lt_relative bucket) <=
    256 * (PTrieT.c_trie + 1) * budget)%N).
  { eapply N.le_trans; [exact Hcorrect_clock|]. now apply N.mul_le_mono_l. }
  assert (Herase_paid : (T_dom_lt_erase numeric parents <=
    512 * (PTrieT.c_trie + 1) * budget)%N).
  { eapply N.le_trans; [exact Herase_clock|]. now apply N.mul_le_mono_l. }
  assert (Hpositive : (1 <= budget)%N).
  { unfold budget. clear -g width. rewrite Nat2N.inj_mul.
    change (1 * 1 <= N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
      N.of_nat (width + 1))%N.
    apply N.mul_le_mono; lia. }
  fold width. fold budget. unfold T_dom_lt_parents. time_simpl.
  fold numeric. fold semi. fold bucket. fold parents.
  unfold dom_lt_semi_coefficient.
  clearbody numeric semi bucket parents bound width budget semi_ops bucket_ops.
  clear -Hnumeric_clock Hsemi_paid Hbucket_paid Hcorrect_paid Herase_paid Hreplay Hpositive.
  nia.
Qed.

Local Transparent dom_lt_eval T_dom_lt_eval dom_lt_predecessor T_dom_lt_predecessor.
Local Transparent dom_lt_settle T_dom_lt_settle.
Local Transparent T_dom_lt_numeric_of T_dom_lt_semidominators T_dom_lt_buckets.
Local Transparent T_dom_lt_correct T_dom_lt_erase.

(** * Amortized evaluation and producer operation support *)

Definition dom_lt_eval_unit (width : nat) : N :=
  (1024 * (c_loopN + 1) * (PTrieT.c_trie + 1) * N.of_nat (width + 1))%N.

(** Bounded forest levels turn their increase into a decrease in remaining capacity. *)
Lemma dom_lt_forest_credit_budget (capacity before after steps logarithm : nat) :
  before <= capacity -> after <= capacity -> steps + before <= logarithm + 1 + after ->
  (N.of_nat (steps + 1) + N.of_nat (capacity - after) <=
    N.of_nat (capacity - before) + N.of_nat (logarithm + 2))%N.
Proof.
  intros Hbefore Hafter Hlevels. lia.
Qed.

(** Forest credit pays every traversed frame, leaving a logarithmic evaluation charge. *)
Lemma dom_lt_time_eval_credit bound width fuel semis before start :
  dom_lt_trie_all (fun value => (value <= N.of_nat bound)%N) semis ->
  (forall value, (value <= N.of_nat bound)%N -> N.size_nat value <= width) ->
  dom_lt_links_bounded (N.of_nat bound) before -> (start <= N.of_nat bound)%N ->
  (start <= fuel)%N -> N.size_nat fuel <= width + 1 ->
  (T_dom_lt_eval fuel semis before start + dom_lt_eval_unit width *
      dom_lt_forest_credit bound (fst (dom_lt_eval fuel semis before start)) <=
    dom_lt_eval_unit width * dom_lt_forest_credit bound before +
      dom_lt_eval_unit width * N.of_nat (Nat.log2 bound + 2))%N.
Proof.
  intros Hsemis Hwidth Hlinks Hstart Hfuel Hfuel_width.
  destruct (dom_lt_walk_path_exists before start) as [path [root Hpath]].
  pose proof (dom_lt_time_eval_path (N.of_nat bound) width fuel semis before start path root
    Hpath Hsemis Hwidth Hlinks Hstart Hfuel_width) as Htime.
  pose proof (dom_lt_eval_level_credit bound fuel semis before start path root
    Hpath ltac:(lia) Hfuel) as Hlevels.
  pose proof (dom_lt_forest_levels_bound bound before) as Hbefore.
  pose proof (dom_lt_forest_levels_bound bound (fst (dom_lt_eval fuel semis before start)))
    as Hafter.
  assert (Hcredit : (N.of_nat (length path + 1) +
      dom_lt_forest_credit bound (fst (dom_lt_eval fuel semis before start)) <=
    dom_lt_forest_credit bound before + N.of_nat (Nat.log2 bound + 2))%N).
  { unfold dom_lt_forest_credit. now apply dom_lt_forest_credit_budget. }
  set (unit := dom_lt_eval_unit width).
  assert (Hwork : (T_dom_lt_eval fuel semis before start <= unit *
    N.of_nat (length path + 1))%N).
  { unfold unit, dom_lt_eval_unit. rewrite Nat2N.inj_mul in Htime.
    replace (1024 * (c_loopN + 1) * (PTrieT.c_trie + 1) * N.of_nat (width + 1) *
      N.of_nat (length path + 1))%N with
      (1024 * (c_loopN + 1) * (PTrieT.c_trie + 1) *
        (N.of_nat (length path + 1) * N.of_nat (width + 1)))%N by
      (clear -width path; nia).
    exact Htime. }
  fold unit.
  eapply N.le_trans with (unit * N.of_nat (length path + 1) + unit *
    dom_lt_forest_credit bound (fst (dom_lt_eval fuel semis before start)))%N.
  - now apply N.add_le_mono_r.
  - rewrite <- N.mul_add_distr_l, <- N.mul_add_distr_l.
    now apply N.mul_le_mono_l.
Qed.

(** The link-child projection forgets queries while retaining every recorded link child. *)
Fixpoint dom_lt_link_children (ops : list lt_op) : list N :=
  match ops with
  | [] => []
  | LtLink child _ :: rest => child :: dom_lt_link_children rest
  | LtEval _ :: rest => dom_lt_link_children rest
  end.

(** Evaluating one predecessor adds a query and leaves all recorded link children unchanged. *)
Lemma dom_lt_predecessor_children limit semis links best witness source :
  dom_lt_link_children (lt_operations (fst (fst
    (dom_lt_predecessor limit semis (links, best, witness) source)))) =
      dom_lt_link_children (lt_operations links).
Proof.
  pose proof (dom_lt_eval_operations limit semis links source) as Hlog.
  unfold dom_lt_predecessor.
  destruct (dom_lt_eval limit semis links source) as [result chosen].
  cbn [fst] in Hlog. destruct (N.ltb (dom_lt_identity semis chosen) best);
    cbn [fst]; rewrite Hlog; reflexivity.
Qed.

(** A whole predecessor row consists entirely of query operations. *)
Lemma dom_lt_predecessors_children limit semis incoming links best witness :
  dom_lt_link_children (lt_operations (fst (fst
    (fold_left (dom_lt_predecessor limit semis) incoming (links, best, witness))))) =
      dom_lt_link_children (lt_operations links).
Proof.
  apply (dom_lt_fold_invariant (dom_lt_predecessor limit semis)
    (fun st => dom_lt_link_children (lt_operations (fst (fst st))) =
      dom_lt_link_children (lt_operations links))).
  - reflexivity.
  - intros [[current selected] origin] source Hchildren.
    rewrite dom_lt_predecessor_children. exact Hchildren.
Qed.

(** Settlement records at most the current traversal key as a new link child. *)
Lemma dom_lt_settle_children numeric st v :
  dom_lt_link_children (lt_operations (lt_semi_links (dom_lt_settle numeric st v))) =
    match trie_get (dom_lt_key v) (lt_numeric_parent numeric) with
    | None => dom_lt_link_children (lt_operations (lt_semi_links st))
    | Some _ => v :: dom_lt_link_children (lt_operations (lt_semi_links st))
    end.
Proof.
  unfold dom_lt_settle.
  destruct (trie_get (dom_lt_key v) (lt_numeric_parent numeric)) as [p|]; [|reflexivity].
  set (incoming := match trie_get (dom_lt_key v) (lt_numeric_pred numeric) with
    None => [] | Some row => row end).
  pose proof (dom_lt_predecessors_children (lt_numeric_limit numeric)
    (lt_semis st) incoming (lt_semi_links st) p p) as Hchildren.
  revert Hchildren.
  generalize (fold_left (dom_lt_predecessor (lt_numeric_limit numeric) (lt_semis st))
    incoming (lt_semi_links st, p, p)).
  intros [[links best] witness] Hchildren.
  cbn [fst] in Hchildren. cbn [lt_semi_links dom_lt_link lt_operations dom_lt_link_children].
  now rewrite Hchildren.
Qed.

(** Optional prepending of distinct input keys preserves uniqueness of the recorded keys. *)
Lemma dom_lt_fold_optional_unique {A State : Type} (step : State -> A -> State)
    (recorded : State -> list A) :
  (forall st x, recorded (step st x) = recorded st \/
    recorded (step st x) = x :: recorded st) ->
  forall xs st, NoDup xs -> NoDup (recorded st) ->
  (forall x, In x xs -> ~ In x (recorded st)) ->
  NoDup (recorded (fold_left step xs st)).
Proof.
  intros Hstep xs. induction xs as [|x rest IH]; intros st Hunique Hrecorded Hfresh.
  - exact Hrecorded.
  - inversion Hunique as [|head tail Hhead Htail]; subst head tail. cbn [fold_left].
    destruct (Hstep st x) as [Hsame|Hnew].
    + apply IH; [exact Htail|now rewrite Hsame|].
      intros v Hv. rewrite Hsame. apply Hfresh. now right.
    + apply IH; [exact Htail| |].
      * rewrite Hnew. constructor; [apply Hfresh; now left|exact Hrecorded].
      * intros v Hv. rewrite Hnew. cbn [In]. intros [Heq|Hmember].
        -- subst v. contradiction.
        -- exact (Hfresh v (or_intror Hv) Hmember).
Qed.

(** The semidominator phase links each numeric traversal key at most once. *)
Lemma dom_lt_semidominators_link_unique numeric :
  NoDup (lt_numeric_order numeric) ->
  NoDup (dom_lt_link_children
    (lt_operations (lt_semi_links (dom_lt_semidominators numeric)))).
Proof.
  intro Hunique. unfold dom_lt_semidominators.
  apply (dom_lt_fold_optional_unique (dom_lt_settle numeric)
    (fun st => dom_lt_link_children (lt_operations (lt_semi_links st)))).
  - intros st v. rewrite dom_lt_settle_children.
    destruct (trie_get (dom_lt_key v) (lt_numeric_parent numeric)); auto.
  - exact Hunique.
  - constructor.
  - intros v Hv Hbad. contradiction.
Qed.

(** Visiting a bucket member adds a query and leaves all recorded link children unchanged. *)
Lemma dom_lt_bucket_member_children limit semis s st v :
  dom_lt_link_children (lt_operations
    (lt_bucket_links (dom_lt_bucket_member limit semis s st v))) =
      dom_lt_link_children (lt_operations (lt_bucket_links st)).
Proof.
  pose proof (dom_lt_eval_operations limit semis (lt_bucket_links st) v) as Hlog.
  unfold dom_lt_bucket_member.
  destruct (dom_lt_eval limit semis (lt_bucket_links st) v) as [links chosen].
  cbn [fst] in Hlog. cbn [lt_bucket_links]. rewrite Hlog. reflexivity.
Qed.

(** A whole bucket row consists entirely of query operations. *)
Lemma dom_lt_bucket_members_children limit semis s row st :
  dom_lt_link_children (lt_operations (lt_bucket_links
    (fold_left (dom_lt_bucket_member limit semis s) row st))) =
      dom_lt_link_children (lt_operations (lt_bucket_links st)).
Proof.
  apply (dom_lt_fold_invariant (dom_lt_bucket_member limit semis s)
    (fun current => dom_lt_link_children (lt_operations (lt_bucket_links current)) =
      dom_lt_link_children (lt_operations (lt_bucket_links st)))).
  - reflexivity.
  - intros current v Hchildren. rewrite dom_lt_bucket_member_children. exact Hchildren.
Qed.

(** A bucket step records at most its current traversal key as a new link child. *)
Lemma dom_lt_bucket_step_children numeric semis buckets st s :
  dom_lt_link_children
    (lt_operations (lt_bucket_links (dom_lt_bucket_step numeric semis buckets st s))) =
    match trie_get (dom_lt_key s) (lt_numeric_parent numeric) with
    | None => dom_lt_link_children (lt_operations (lt_bucket_links st))
    | Some _ => s :: dom_lt_link_children (lt_operations (lt_bucket_links st))
    end.
Proof.
  unfold dom_lt_bucket_step.
  set (row := match trie_get (dom_lt_key s) buckets with None => [] | Some row => row end).
  pose proof (dom_lt_bucket_members_children (lt_numeric_limit numeric) semis s row st)
    as Hchildren.
  revert Hchildren.
  generalize (fold_left (dom_lt_bucket_member (lt_numeric_limit numeric) semis s) row st).
  intros current Hchildren.
  destruct (trie_get (dom_lt_key s) (lt_numeric_parent numeric));
    cbn [lt_bucket_links dom_lt_link lt_operations dom_lt_link_children];
    now rewrite Hchildren.
Qed.

(** The bucket phase links each numeric traversal key at most once. *)
Lemma dom_lt_buckets_link_unique numeric semis :
  NoDup (lt_numeric_order numeric) ->
  NoDup (dom_lt_link_children (lt_operations (lt_bucket_links (dom_lt_buckets numeric semis)))).
Proof.
  intro Hunique. unfold dom_lt_buckets.
  apply (dom_lt_fold_optional_unique
    (dom_lt_bucket_step numeric semis
      (fold_left (dom_lt_bucket_add semis) (rev_append (lt_numeric_order numeric) []) Empty))
    (fun st => dom_lt_link_children (lt_operations (lt_bucket_links st)))).
  - intros st v. rewrite dom_lt_bucket_step_children.
    destruct (trie_get (dom_lt_key v) (lt_numeric_parent numeric)); auto.
  - exact Hunique.
  - constructor.
  - intros v Hv Hbad. contradiction.
Qed.

(** Link-child projection preserves concatenation of operation logs. *)
Lemma dom_lt_link_children_app left right :
  dom_lt_link_children (left ++ right) =
    dom_lt_link_children left ++ dom_lt_link_children right.
Proof.
  induction left as [|op rest IH]; [reflexivity|].
  destruct op; cbn [app dom_lt_link_children]; now rewrite IH.
Qed.

(** Reversing a log reverses exactly its link-child projection. *)
Lemma dom_lt_link_children_rev ops :
  dom_lt_link_children (rev ops) = rev (dom_lt_link_children ops).
Proof.
  induction ops as [|op rest IH]; [reflexivity|].
  cbn [rev]. rewrite dom_lt_link_children_app, IH.
  destruct op; cbn [dom_lt_link_children rev]; now rewrite ?app_nil_r.
Qed.

(** Both operands of a link and the operand of a query obey the same numeric bound. *)
Definition dom_lt_op_bounded (bound : N) (op : lt_op) : Prop :=
  match op with
  | LtLink child parent => (child <= bound /\ parent <= bound)%N
  | LtEval v => (v <= bound)%N
  end.

(** A predecessor callback records only its supplied numeric query operand. *)
Lemma dom_lt_predecessor_log limit semis links best witness source :
  lt_operations (fst (fst
    (dom_lt_predecessor limit semis (links, best, witness) source))) =
      LtEval source :: lt_operations links.
Proof.
  pose proof (dom_lt_eval_operations limit semis links source) as Hlog.
  unfold dom_lt_predecessor.
  destruct (dom_lt_eval limit semis links source) as [result chosen].
  cbn [fst] in Hlog. destruct (N.ltb (dom_lt_identity semis chosen) best); exact Hlog.
Qed.

(** Folding bounded predecessor operands preserves a bounded operation log. *)
Lemma dom_lt_predecessors_op_range bound limit semis incoming links best witness :
  Forall (fun n => (n <= bound)%N) incoming ->
  Forall (dom_lt_op_bounded bound) (lt_operations links) ->
  Forall (dom_lt_op_bounded bound) (lt_operations (fst (fst
    (fold_left (dom_lt_predecessor limit semis) incoming (links, best, witness))))).
Proof.
  intros Hinputs Hbefore.
  apply (dom_lt_fold_forall (dom_lt_predecessor limit semis)
    (fun st => Forall (dom_lt_op_bounded bound) (lt_operations (fst (fst st))))
    (fun n => (n <= bound)%N)); [exact Hinputs|exact Hbefore|].
  intros [[current selected] origin] source Hcurrent Hsource.
  rewrite dom_lt_predecessor_log. now constructor.
Qed.

(** A settlement records only its current key, bounded parent and bounded predecessor operands. *)
Lemma dom_lt_settle_op_range bound numeric st v :
  dom_lt_numeric_ranges bound numeric ->
  Forall (dom_lt_op_bounded bound) (lt_operations (lt_semi_links st)) -> (v <= bound)%N ->
  Forall (dom_lt_op_bounded bound)
    (lt_operations (lt_semi_links (dom_lt_settle numeric st v))).
Proof.
  intros [Horder Hparents Hpredecessors] Hbefore Hv. unfold dom_lt_settle.
  destruct (trie_get (dom_lt_key v) (lt_numeric_parent numeric)) as [p|] eqn:Hparent;
    [|exact Hbefore].
  pose proof (Hparents (dom_lt_key v) p Hparent) as Hp.
  set (incoming := match trie_get (dom_lt_key v) (lt_numeric_pred numeric) with
    None => [] | Some row => row end).
  assert (Hincoming : Forall (fun n => (n <= bound)%N) incoming).
  { unfold incoming.
    destruct (trie_get (dom_lt_key v) (lt_numeric_pred numeric)) as [row|] eqn:Hrow;
      [now apply (Hpredecessors (dom_lt_key v))|constructor]. }
  pose proof (dom_lt_predecessors_op_range bound (lt_numeric_limit numeric) (lt_semis st)
    incoming (lt_semi_links st) p p Hincoming Hbefore) as Hfold.
  revert Hfold.
  generalize (fold_left (dom_lt_predecessor (lt_numeric_limit numeric) (lt_semis st))
    incoming (lt_semi_links st, p, p)).
  intros [[links best] witness] Hfold. cbn [fst] in Hfold.
  cbn [lt_semi_links dom_lt_link lt_operations]. constructor; [now split|exact Hfold].
Qed.

(** The semidominator phase records only operands from the numeric layout's range. *)
Lemma dom_lt_semidominators_op_range bound numeric :
  dom_lt_numeric_ranges bound numeric ->
  Forall (dom_lt_op_bounded bound)
    (lt_operations (lt_semi_links (dom_lt_semidominators numeric))).
Proof.
  intro Hranges. unfold dom_lt_semidominators.
  apply (dom_lt_fold_forall (dom_lt_settle numeric)
    (fun st => Forall (dom_lt_op_bounded bound) (lt_operations (lt_semi_links st)))
    (fun n => (n <= bound)%N)).
  - exact (dom_lt_numeric_order_range _ _ Hranges).
  - constructor.
  - intros st v Hbefore Hv. eapply dom_lt_settle_op_range; eassumption.
Qed.

(** A bucket callback records only its supplied member as a query operand. *)
Lemma dom_lt_bucket_member_op_range bound limit semis s st v :
  Forall (dom_lt_op_bounded bound) (lt_operations (lt_bucket_links st)) -> (v <= bound)%N ->
  Forall (dom_lt_op_bounded bound)
    (lt_operations (lt_bucket_links (dom_lt_bucket_member limit semis s st v))).
Proof.
  intros Hbefore Hv.
  pose proof (dom_lt_eval_operations limit semis (lt_bucket_links st) v) as Hlog.
  unfold dom_lt_bucket_member.
  destruct (dom_lt_eval limit semis (lt_bucket_links st) v) as [links chosen].
  cbn [fst] in Hlog. cbn [lt_bucket_links]. rewrite Hlog. now constructor.
Qed.

(** Processing one bounded bucket records bounded queries and one possible bounded parent link. *)
Lemma dom_lt_bucket_step_op_range bound numeric semis buckets st s :
  dom_lt_numeric_ranges bound numeric ->
  dom_lt_trie_all (Forall (fun n => (n <= bound)%N)) buckets ->
  Forall (dom_lt_op_bounded bound) (lt_operations (lt_bucket_links st)) -> (s <= bound)%N ->
  Forall (dom_lt_op_bounded bound)
    (lt_operations (lt_bucket_links (dom_lt_bucket_step numeric semis buckets st s))).
Proof.
  intros Hranges Hrows Hbefore Hs. unfold dom_lt_bucket_step.
  set (row := match trie_get (dom_lt_key s) buckets with None => [] | Some row => row end).
  assert (Hrow : Forall (fun n => (n <= bound)%N) row).
  { unfold row. destruct (trie_get (dom_lt_key s) buckets) as [members|] eqn:Hmembers;
      [now apply (Hrows (dom_lt_key s))|constructor]. }
  assert (Hfold : Forall (dom_lt_op_bounded bound) (lt_operations (lt_bucket_links
    (fold_left (dom_lt_bucket_member (lt_numeric_limit numeric) semis s) row st)))).
  { apply (dom_lt_fold_forall (dom_lt_bucket_member (lt_numeric_limit numeric) semis s)
      (fun current => Forall (dom_lt_op_bounded bound) (lt_operations (lt_bucket_links current)))
      (fun n => (n <= bound)%N)); [exact Hrow|exact Hbefore|].
    intros current v Hcurrent Hv. now apply dom_lt_bucket_member_op_range. }
  revert Hfold.
  generalize (fold_left (dom_lt_bucket_member (lt_numeric_limit numeric) semis s) row st).
  intros current Hfold.
  destruct (trie_get (dom_lt_key s) (lt_numeric_parent numeric)) as [p|] eqn:Hparent;
    [|exact Hfold].
  cbn [lt_bucket_links dom_lt_link lt_operations]. constructor; [|exact Hfold].
  split; [exact Hs|]. exact (dom_lt_numeric_parent_range _ _ Hranges _ _ Hparent).
Qed.

(** The bucket phase records only operands from the numeric layout's range. *)
Lemma dom_lt_buckets_op_range bound numeric semis :
  dom_lt_numeric_ranges bound numeric ->
  Forall (dom_lt_op_bounded bound) (lt_operations (lt_bucket_links (dom_lt_buckets numeric semis))).
Proof.
  intro Hranges. unfold dom_lt_buckets.
  set (buckets := fold_left (dom_lt_bucket_add semis)
    (rev_append (lt_numeric_order numeric) []) Empty).
  assert (Hrows : dom_lt_trie_all (Forall (fun n => (n <= bound)%N)) buckets).
  { apply dom_lt_bucket_build_range. exact (dom_lt_numeric_order_range _ _ Hranges). }
  apply (dom_lt_fold_forall (dom_lt_bucket_step numeric semis buckets)
    (fun st => Forall (dom_lt_op_bounded bound) (lt_operations (lt_bucket_links st)))
    (fun n => (n <= bound)%N)).
  - exact (dom_lt_numeric_order_range _ _ Hranges).
  - constructor.
  - intros st s Hbefore Hs. eapply dom_lt_bucket_step_op_range; eassumption.
Qed.

(** Reversing one operation prefix preserves any elementwise operand invariant. *)
Lemma dom_lt_forall_rev_append {A : Type} (P : A -> Prop) xs ys :
  Forall P xs -> Forall P ys -> Forall P (rev_append xs ys).
Proof.
  intro Hxs. revert ys.
  induction Hxs as [|x rest Hx Hrest IH]; intros ys Hys; [exact Hys|].
  cbn [rev_append]. apply IH. now constructor.
Qed.

(** * Child-index structure and clocks *)

(** Splitting preserves the original order and every occurrence. *)
Lemma dom_order_split_partition n xs :
  fst (dom_order_split n xs) ++ snd (dom_order_split n xs) = xs.
Proof.
  revert xs. induction n as [|n IH]; intros [|v rest]; cbn [dom_order_split fst snd app];
    try reflexivity.
  specialize (IH rest). destruct (dom_order_split n rest) as [lower upper].
  cbn [fst snd app] in IH |- *. now rewrite IH.
Qed.

(** The two split parts retain exactly the input's total length. *)
Lemma dom_order_split_length n xs :
  length (fst (dom_order_split n xs)) + length (snd (dom_order_split n xs)) = length xs.
Proof.
  rewrite <- length_app, dom_order_split_partition. reflexivity.
Qed.

(** Each split part inherits every property of the original elements. *)
Lemma dom_order_split_forall (P : N -> Prop) n xs :
  Forall P xs ->
  Forall P (fst (dom_order_split n xs)) /\ Forall P (snd (dom_order_split n xs)).
Proof.
  intro Hall. rewrite <- (dom_order_split_partition n xs) in Hall.
  now apply Forall_app in Hall.
Qed.

(** Half of a unary count never exceeds that count. *)
Lemma dom_order_half_twice n : 2 * dom_order_half n <= n.
Proof.
  revert n. fix IH 1. intros [|[|n]]; cbn [dom_order_half]; try lia.
  pose proof (IH n). lia.
Qed.

(** Computing the half count reads at most one cell per original unit. *)
Lemma dom_order_half_time n :
  (T_dom_order_half n <= N.of_nat n + 1)%N.
Proof.
  revert n. fix IH 1. intros [|[|n]].
  - time_step.
  - time_step.
  - pose proof (IH n). time_step.
Qed.

(** Splitting reads at most the supplied list's cells. *)
Lemma dom_order_split_time n xs :
  (T_dom_order_split n xs <= N.of_nat (length xs) + 1)%N.
Proof.
  revert n. induction xs as [|v rest IH]; intros [|n]; time_step.
Qed.

Fixpoint dom_order_index_height (index : dom_child_index) : nat :=
  match index with
  | DomChildEmpty => 0
  | DomChildNode _ _ lower upper =>
    S (Nat.max (dom_order_index_height lower) (dom_order_index_height upper))
  end.

Fixpoint dom_order_index_values (P Q : N -> Prop) (index : dom_child_index) : Prop :=
  match index with
  | DomChildEmpty => True
  | DomChildNode child position lower upper =>
    P child /\ Q position /\
      dom_order_index_values P Q lower /\ dom_order_index_values P Q upper
  end.

(** The explicit recursion fuel bounds the constructed child index's height. *)
Lemma dom_order_index_build_height fuel pre xs :
  dom_order_index_height (dom_order_index_build fuel pre xs) <= fuel.
Proof.
  revert xs. induction fuel as [|fuel IH]; intros [|v rest];
    cbn [dom_order_index_build dom_order_index_height]; try lia.
  destruct (dom_order_split (dom_order_half (length (v :: rest))) (v :: rest))
    as [lower [|pivot upper]]; cbn [dom_order_index_height]; [lia|].
  pose proof (IH lower) as Hlower.
  pose proof (IH upper) as Hupper. lia.
Qed.

(** The constructed index stores only supplied children and their supplied position values. *)
Lemma dom_order_index_build_values (P Q : N -> Prop) fuel pre xs :
  Forall P xs -> (forall v, P v -> Q (dom_order_number pre v)) ->
  dom_order_index_values P Q (dom_order_index_build fuel pre xs).
Proof.
  revert xs. induction fuel as [|fuel IH]; intros [|v rest] Hall Hnumber;
    cbn [dom_order_index_build dom_order_index_values]; try exact I.
  pose proof (dom_order_split_forall P (dom_order_half (length (v :: rest)))
    (v :: rest) Hall) as Hparts.
  destruct (dom_order_split (dom_order_half (length (v :: rest))) (v :: rest))
    as [lower [|pivot upper]]; cbn [fst snd dom_order_index_values] in *; [exact I|].
  destruct Hparts as [Hlower Hupper].
  inversion Hupper as [|head tail Hpivot Htail]; subst head tail.
  split; [exact Hpivot|]. split; [now apply Hnumber|]. split; now apply IH.
Qed.

(** A successful index search returns one of its stored children. *)
Lemma dom_order_index_search_value (P Q : N -> Prop) index position child :
  dom_order_index_values P Q index -> dom_order_index_search position index = Some child ->
  P child.
Proof.
  induction index as [|stored start lower IHlower upper IHupper]; intros Hvalues Hsearch.
  - discriminate Hsearch.
  - destruct Hvalues as [Hstored [Hstart [Hlower Hupper]]].
    cbn [dom_order_index_search] in Hsearch.
    destruct (N.ltb position start).
    + now apply IHlower.
    + destruct (dom_order_index_search position upper) as [found|] eqn:Hfound.
      * injection Hsearch as <-. now apply IHupper.
      * now injection Hsearch as <-.
Qed.

(** Two child budgets share one parent span after removing the pivot. *)
Lemma dom_order_index_children_budget (unit depth lower upper total left_work right_work : N) :
  (lower + upper + 1 = total)%N ->
  (left_work <= unit * (depth * (lower + 1)))%N ->
  (right_work <= unit * (depth * (upper + 1)))%N ->
  (left_work + right_work <= unit * (depth * (total + 1)))%N.
Proof.
  intros Hspan Hleft Hright.
  assert (Hbudget : (unit * (depth * (total + 1)) =
    unit * (depth * (lower + 1)) + unit * (depth * (upper + 1)))%N).
  { rewrite <- Hspan. ring. }
  rewrite Hbudget. now apply N.add_le_mono.
Qed.

(** Building an index spends linear list work on each explicit recursion level. *)
Lemma dom_order_index_build_time fuel pre xs k :
  (forall v, In v xs -> (T_dom_order_number pre v <= k)%N) ->
  (T_dom_order_index_build fuel pre xs <=
    32 * (k + 1) * N.of_nat ((fuel + 1) * (length xs + 1)))%N.
Proof.
  revert xs. induction fuel as [|fuel IH]; intros xs Hnumber.
  - time_unfold T_dom_order_index_build. time_simpl.
    rewrite !Nat2N.inj_mul, !Nat2N.inj_add. nia.
  - destruct xs as [|v rest].
    + time_unfold T_dom_order_index_build. time_simpl.
      rewrite !Nat2N.inj_mul, !Nat2N.inj_add. nia.
    + pose proof (Datatypes.T_length_le (v :: rest)) as Hlength_time.
      pose proof (dom_order_half_time (length (v :: rest))) as Hhalf.
      pose proof (dom_order_split_time (dom_order_half (length (v :: rest)))
        (v :: rest)) as Hsplit_time.
      pose proof (dom_order_split_partition (dom_order_half (length (v :: rest)))
        (v :: rest)) as Hpartition.
      pose proof (dom_order_split_length (dom_order_half (length (v :: rest)))
        (v :: rest)) as Hlength.
      destruct (dom_order_split (dom_order_half (length (v :: rest))) (v :: rest))
        as [lower upper] eqn:Hsplit.
      cbn [fst snd] in Hpartition, Hlength.
      destruct upper as [|pivot upper].
      * time_unfold T_dom_order_index_build. rewrite Hsplit. time_simpl.
        rewrite !Nat2N.inj_mul, !Nat2N.inj_add in *. nia.
      * assert (Hlower : forall x, In x lower -> (T_dom_order_number pre x <= k)%N).
        { intros x Hx. apply Hnumber. rewrite <- Hpartition.
          apply in_or_app. now left. }
        assert (Hupper : forall x, In x upper -> (T_dom_order_number pre x <= k)%N).
        { intros x Hx. apply Hnumber. rewrite <- Hpartition.
          apply in_or_app. right. now right. }
        assert (Hpivot : (T_dom_order_number pre pivot <= k)%N).
        { apply Hnumber. rewrite <- Hpartition. apply in_or_app. right. now left. }
        pose proof (IH lower Hlower) as Hlower_time.
        pose proof (IH upper Hupper) as Hupper_time.
        assert (Hspan : (N.of_nat (length lower) + N.of_nat (length upper) + 1 =
          N.of_nat (length (v :: rest)))%N).
        { cbn [length] in Hlength |- *. lia. }
        set (unit := (32 * (k + 1))%N).
        assert (Hrecursive : (T_dom_order_index_build fuel pre lower +
          T_dom_order_index_build fuel pre upper <=
          unit * ((N.of_nat fuel + 1) * (N.of_nat (length (v :: rest)) + 1)))%N).
        { rewrite !Nat2N.inj_mul, !Nat2N.inj_add in Hlower_time, Hupper_time.
          fold unit in Hlower_time, Hupper_time.
          eapply dom_order_index_children_budget;
            [exact Hspan|exact Hlower_time|exact Hupper_time]. }
        assert (Hoverhead : (16 + Datatypes.T_length (v :: rest) +
          T_dom_order_half (length (v :: rest)) +
          T_dom_order_split (dom_order_half (length (v :: rest))) (v :: rest) +
          T_dom_order_number pre pivot <= unit * (N.of_nat (length (v :: rest)) + 1))%N).
        { unfold unit. clear -Hlength_time Hhalf Hsplit_time Hpivot.
          nia. }
        time_unfold T_dom_order_index_build. rewrite Hsplit. time_simpl.
        rewrite !Nat2N.inj_mul, !Nat2N.inj_add, (Nat2N.inj_succ fuel).
        rewrite !N.mul_assoc.
        rewrite N.mul_assoc in Hrecursive.
        fold unit. replace (unit * (N.succ (N.of_nat fuel) + 1) *
          (N.of_nat (length (v :: rest)) + 1))%N with
          (unit * (N.of_nat fuel + 1) * (N.of_nat (length (v :: rest)) + 1) +
            unit * (N.of_nat (length (v :: rest)) + 1))%N by (rewrite <- N.add_1_r; ring).
        clear -Hrecursive Hoverhead. lia.
Qed.

(** An index search follows only one branch and compares the supplied position. *)
Lemma dom_order_index_search_time position index :
  (T_dom_order_index_search position index <=
    (N.of_nat (N.size_nat position) + 8) *
      N.of_nat (dom_order_index_height index + 1))%N.
Proof.
  induction index as [|child start lower IHlower upper IHupper].
  - time_unfold T_dom_order_index_search. time_simpl.
    cbn [dom_order_index_height]. nia.
  - pose proof (dom_lt_time_ltb position start) as Hcompare.
    time_unfold T_dom_order_index_search.
    destruct (N.ltb position start).
    + time_simpl. cbn [dom_order_index_height].
      pose proof (Nat.le_max_l (dom_order_index_height lower)
        (dom_order_index_height upper)) as Hheight.
      apply time_of_nat_le in Hheight.
      rewrite !Nat2N.inj_add, !Nat2N.inj_succ in *. nia.
    + destruct (dom_order_index_search position upper); time_simpl;
        cbn [dom_order_index_height];
        pose proof (Nat.le_max_r (dom_order_index_height lower)
          (dom_order_index_height upper)) as Hheight;
        apply time_of_nat_le in Hheight;
        rewrite !Nat2N.inj_add, !Nat2N.inj_succ in *; nia.
Qed.

(** * Aggregate comparison credit for the replay boundary *)

(** Set-bit credit never exceeds the binary representation's width. *)
Lemma dom_positive_credit_le_size p :
  (dom_positive_credit p <= N.of_nat (Pos.size_nat p))%N.
Proof.
  induction p as [p IH|p IH|]; cbn [dom_positive_credit Pos.size_nat];
    rewrite ?Nat2N.inj_succ; lia.
Qed.

(** Binary-counter carry credit is bounded by the counter's representation width. *)
Lemma dom_counter_credit_le_size n :
  (dom_counter_credit n <= N.of_nat (N.size_nat n))%N.
Proof.
  destruct n as [|p]; cbn [dom_counter_credit N.size_nat];
    [reflexivity|apply dom_positive_credit_le_size].
Qed.

(** Carry credit is also bounded by the counter's numeric value. *)
Lemma dom_counter_credit_le_value n : (dom_counter_credit n <= n)%N.
Proof.
  eapply N.le_trans; [apply dom_counter_credit_le_size|apply dom_size_value].
Qed.

(** Doubling a positive distance extends its predecessor borrow by one bit. *)
Lemma dom_pred_double_clock n : (0 < n)%N ->
  (N.T_pred (N.double n) = N.T_pred n + 1)%N.
Proof.
  destruct n as [|[p|p|]]; intro Hpositive; [lia| | |];
    cbn [N.double]; time_unfold N.T_pred; time_unfold Pos.T_pred_N;
    time_unfold Pos.T_pred_double; lia.
Qed.

(** Positive equality compares the same low-bit prefix in either argument order. *)
Lemma dom_positive_eqb_clock_sym p q : Pos.T_eqb p q = Pos.T_eqb q p.
Proof.
  revert q. induction p as [p IH|p IH|]; intros [q|q|];
    time_unfold Pos.T_eqb; try reflexivity; now rewrite IH.
Qed.

(** Numeric equality has the same generated clock in either argument order. *)
Lemma dom_eqb_clock_sym a b : N.T_eqb a b = N.T_eqb b a.
Proof.
  destruct a as [|p], b as [|q]; time_unfold N.T_eqb; try reflexivity.
  now rewrite dom_positive_eqb_clock_sym.
Qed.

(** Equal low bits of unequal positives are bounded by the difference's borrow chain. *)
Lemma dom_positive_eqb_difference : forall p q,
  (N.pos p < N.pos q)%N ->
  (Pos.T_eqb p q <= N.T_pred (N.pos q - N.pos p) + 1)%N.
Proof.
  intro p. induction p as [p IH|p IH|]; intros [q|q|] Hlt;
    time_unfold Pos.T_eqb; try lia.
  - assert (Hsmaller : (N.pos p < N.pos q)%N).
    { change (N.succ (N.double (N.pos p)) < N.succ (N.double (N.pos q)))%N in Hlt.
      rewrite !N.double_spec in Hlt. lia. }
    assert (Hdifference : (N.pos (xI q) - N.pos (xI p) =
      N.double (N.pos q - N.pos p))%N).
    { change (N.succ (N.double (N.pos q)) - N.succ (N.double (N.pos p)) =
        N.double (N.pos q - N.pos p))%N.
      rewrite N.sub_succ, !N.double_spec. lia. }
    rewrite Hdifference, dom_pred_double_clock by lia. specialize (IH q Hsmaller). lia.
  - assert (Hsmaller : (N.pos p < N.pos q)%N).
    { change (N.double (N.pos p) < N.double (N.pos q))%N in Hlt.
      rewrite !N.double_spec in Hlt. lia. }
    assert (Hdifference : (N.pos (xO q) - N.pos (xO p) =
      N.double (N.pos q - N.pos p))%N).
    { change (N.double (N.pos q) - N.double (N.pos p) =
        N.double (N.pos q - N.pos p))%N.
      rewrite !N.double_spec. lia. }
    rewrite Hdifference, dom_pred_double_clock by lia. specialize (IH q Hsmaller). lia.
Qed.

(** An unequal comparison is bounded by the predecessor work of its positive difference. *)
Lemma dom_eqb_difference a b : (a < b)%N ->
  (N.T_eqb a b <= N.T_pred (b - a) + 2)%N.
Proof.
  destruct a as [|p], b as [|q]; intro Hlt; time_unfold N.T_eqb; try lia.
  pose proof (dom_positive_eqb_difference p q Hlt). lia.
Qed.

(** Increment carries pay for the borrow chain in the successor's predecessor. *)
Lemma dom_pred_double_succ_clock p :
  (Pos.T_pred_double (Pos.succ p) <= Pos.T_succ p + 1)%N.
Proof.
  induction p as [p IH|p IH|]; cbn [Pos.succ];
    time_unfold Pos.T_pred_double; time_unfold Pos.T_succ; time_simpl; try lia.
  time_unfold Pos.T_pred_double. lia.
Qed.

(** The successor's predecessor work is paid by the original successor carry chain. *)
Lemma dom_pred_succ_clock n : (N.T_pred (N.succ n) <= N.T_succ n + 2)%N.
Proof.
  destruct n as [|[p|p|]]; cbn [N.succ Pos.succ];
    time_unfold N.T_pred; time_unfold Pos.T_pred_N;
    time_unfold N.T_succ; time_unfold Pos.T_succ;
    try pose proof (dom_pred_double_succ_clock p); time_simpl; try lia.
  time_unfold Pos.T_pred_double. lia.
Qed.

(** The comparison credit reserves the equality scan and pays both surrounding borrow/carry runs. *)
Definition dom_eqb_credit (boundary index : N) : N :=
  if (index <=? boundary)%N then
    (N.of_nat (N.size_nat boundary) + 1 + loopN_zero_bits (boundary - index))%N
  else dom_counter_credit (index - boundary - 1)%N.

(** The initial comparison reserve is at most twice the boundary width plus one. *)
Lemma dom_eqb_credit_initial boundary :
  (dom_eqb_credit boundary 0 <= 2 * N.of_nat (N.size_nat boundary) + 1)%N.
Proof.
  unfold dom_eqb_credit. assert (Hzero : (0 <=? boundary)%N = true).
  { apply N.leb_le. lia. }
  rewrite Hzero, N.sub_0_r. pose proof (loopN_zero_bits_le_size boundary). lia.
Qed.

(** The segment immediately after the boundary starts with zero comparison credit. *)
Lemma dom_eqb_credit_after_boundary boundary : dom_eqb_credit boundary (N.succ boundary) = 0%N.
Proof.
  unfold dom_eqb_credit.
  assert (Hnext : (N.succ boundary <=? boundary)%N = false) by (apply N.leb_gt; lia).
  rewrite Hnext. replace (N.succ boundary - boundary - 1)%N with 0%N by lia. reflexivity.
Qed.

(** Consecutive comparisons against a fixed boundary have constant amortized cost. *)
Lemma dom_time_eqb_credit index boundary :
  (N.T_eqb index boundary + dom_eqb_credit boundary (N.succ index) <=
    dom_eqb_credit boundary index + 8)%N.
Proof.
  unfold dom_eqb_credit.
  destruct (N.lt_trichotomy index boundary) as [Hbefore|[Heq|Hafter]].
  - assert (Hhere : (index <=? boundary)%N = true) by (apply N.leb_le; lia).
    assert (Hnext : (N.succ index <=? boundary)%N = true) by (apply N.leb_le; lia).
    rewrite Hhere, Hnext, N.sub_succ_r.
    pose proof (dom_eqb_difference index boundary Hbefore) as Hcompare.
    pose proof (loopN_pred_credit (boundary - index)) as Hborrow. lia.
  - subst index.
    assert (Hnext : (N.succ boundary <=? boundary)%N = false) by (apply N.leb_gt; lia).
    rewrite N.leb_refl, Hnext, N.sub_diag. cbn [loopN_zero_bits].
    assert (Hzero : (N.succ boundary - boundary - 1 = 0)%N) by lia.
    rewrite Hzero. cbn [dom_counter_credit].
    pose proof (N.T_eqb_le boundary boundary). lia.
  - assert (Hhere : (index <=? boundary)%N = false) by (apply N.leb_gt; lia).
    assert (Hnext : (N.succ index <=? boundary)%N = false) by (apply N.leb_gt; lia).
    rewrite Hhere, Hnext.
    set (distance := (index - boundary - 1)%N).
    assert (Hdistance : (index - boundary = N.succ distance)%N) by (unfold distance; lia).
    assert (Hadvance : (N.succ index - boundary - 1 = N.succ distance)%N)
      by (unfold distance; lia).
    rewrite Hadvance.
    pose proof (dom_eqb_difference boundary index Hafter) as Hcompare.
    rewrite dom_eqb_clock_sym, Hdistance in Hcompare.
    pose proof (dom_pred_succ_clock distance) as Hborrow.
    pose proof (dom_time_counter_succ distance) as Hcarry. lia.
Qed.

(** * Merge and sort occurrence inventories *)

Definition dom_order_merge_mass (st : dom_order_merge_state) : nat :=
  length (merge_lower st) + length (merge_upper st) + length (merge_reverse st).

(** Each merge callback retains every occurrence in a pending row or its reverse accumulator. *)
Lemma dom_order_merge_step_mass positions st :
  match dom_order_merge_step positions st with
  | inl next => dom_order_merge_mass next
  | inr result => length result
  end = dom_order_merge_mass st.
Proof.
  destruct st as [lower upper reverse].
  unfold dom_order_merge_step, dom_order_merge_mass.
  cbn [merge_lower merge_upper merge_reverse].
  destruct lower as [|x lower], upper as [|y upper].
  - rewrite rev_append_rev, length_app, length_rev. cbn [length]. lia.
  - rewrite rev_append_rev, length_app, length_rev. cbn [length]. lia.
  - rewrite rev_append_rev, length_app, length_rev. cbn [length]. lia.
  - destruct (N.leb (dom_anchor_start positions x) (dom_anchor_start positions y));
      cbn [merge_lower merge_upper merge_reverse length]; lia.
Qed.

(** Merge preserves total length even if its explicit fuel is exhausted. *)
Lemma dom_order_merge_length positions lower upper :
  length (dom_order_merge positions lower upper) = length lower + length upper.
Proof.
  set (total := length lower + length upper).
  pose proof (dom_lt_loop_invariant (dom_order_merge_step positions)
    (fun st => dom_order_merge_mass st = total) (fun result => length result = total)
    (N.of_nat (length lower + length upper + 1)) (DomOrderMergeState lower upper [])) as Hloop.
  specialize (Hloop ltac:(intros st next Hmass Hstep;
    pose proof (dom_order_merge_step_mass positions st) as Hnext;
    rewrite Hstep in Hnext; exact (eq_trans Hnext Hmass))).
  specialize (Hloop ltac:(intros st result Hmass Hstep;
    pose proof (dom_order_merge_step_mass positions st) as Hresult;
    rewrite Hstep in Hresult; exact (eq_trans Hresult Hmass))).
  assert (Hinitial : dom_order_merge_mass (DomOrderMergeState lower upper []) = total).
  { unfold dom_order_merge_mass, total. cbn [merge_lower merge_upper merge_reverse length]. lia. }
  specialize (Hloop Hinitial).
  unfold dom_order_merge.
  destruct (loopN (dom_order_merge_step positions) (N.of_nat (length lower + length upper + 1))
    (DomOrderMergeState lower upper [])) as [st|result].
  - rewrite rev_append_rev, !length_app, length_rev.
    unfold dom_order_merge_mass in Hloop. lia.
  - exact Hloop.
Qed.

(** Every explicit recursion depth of the merge sort preserves the input length. *)
Lemma dom_order_sort_length fuel positions xs :
  length (dom_order_sort fuel positions xs) = length xs.
Proof.
  revert xs. induction fuel as [|fuel IH]; intro xs; [reflexivity|].
  destruct xs as [|x [|y rest]]; [reflexivity|reflexivity|].
  cbn [dom_order_sort].
  pose proof (dom_order_split_length (dom_order_half (length (x :: y :: rest)))
    (x :: y :: rest)) as Hlength.
  destruct (dom_order_split (dom_order_half (length (x :: y :: rest))) (x :: y :: rest))
    as [lower upper].
  cbn [fst snd] in Hlength |- *.
  rewrite dom_order_merge_length, !IH. exact Hlength.
Qed.

(** Merging retains every element predicate through both pending lists and its accumulator. *)
Lemma dom_order_merge_step_forall (P : N -> Prop) positions st :
  Forall P (merge_lower st) -> Forall P (merge_upper st) -> Forall P (merge_reverse st) ->
  match dom_order_merge_step positions st with
  | inl next =>
    Forall P (merge_lower next) /\ Forall P (merge_upper next) /\ Forall P (merge_reverse next)
  | inr result => Forall P result
  end.
Proof.
  destruct st as [lower upper reverse]. intros Hlower Hupper Hreverse.
  cbn [merge_lower merge_upper merge_reverse] in *.
  unfold dom_order_merge_step. cbn [merge_lower merge_upper merge_reverse].
  destruct lower as [|x lower], upper as [|y upper].
  - rewrite rev_append_rev. apply Forall_app. split; [now apply Forall_rev|exact Hupper].
  - rewrite rev_append_rev. apply Forall_app. split; [now apply Forall_rev|exact Hupper].
  - rewrite rev_append_rev. apply Forall_app. split; [now apply Forall_rev|exact Hlower].
  - inversion Hlower as [|head tail Hx Hlower_tail]; subst head tail.
    inversion Hupper as [|head tail Hy Hupper_tail]; subst head tail.
    destruct (N.leb (dom_anchor_start positions x) (dom_anchor_start positions y));
      cbn [merge_lower merge_upper merge_reverse].
    + split; [exact Hlower_tail|]. split; [exact Hupper|]. now constructor.
    + split; [exact Hlower|]. split; [exact Hupper_tail|]. now constructor.
Qed.

(** A complete or partial merge contains only elements satisfying its input predicate. *)
Lemma dom_order_merge_forall (P : N -> Prop) positions lower upper :
  Forall P lower -> Forall P upper -> Forall P (dom_order_merge positions lower upper).
Proof.
  intros Hlower Hupper.
  pose proof (dom_lt_loop_invariant (dom_order_merge_step positions)
    (fun st => Forall P (merge_lower st) /\ Forall P (merge_upper st) /\ Forall P (merge_reverse st))
    (Forall P) (N.of_nat (length lower + length upper + 1))
    (DomOrderMergeState lower upper [])) as Hloop.
  specialize (Hloop ltac:(intros st next [Hl [Hu Hr]] Hstep;
    pose proof (dom_order_merge_step_forall P positions st Hl Hu Hr) as Hnext;
    rewrite Hstep in Hnext; exact Hnext)).
  specialize (Hloop ltac:(intros st result [Hl [Hu Hr]] Hstep;
    pose proof (dom_order_merge_step_forall P positions st Hl Hu Hr) as Hresult;
    rewrite Hstep in Hresult; exact Hresult)
    (conj Hlower (conj Hupper (Forall_nil P)))).
  unfold dom_order_merge.
  destruct (loopN (dom_order_merge_step positions) (N.of_nat (length lower + length upper + 1))
    (DomOrderMergeState lower upper [])) as [st|result]; [|exact Hloop].
  destruct Hloop as [Hl [Hu Hr]]. rewrite rev_append_rev.
  apply Forall_app. split; [now apply Forall_rev|now apply Forall_app].
Qed.

(** Every explicit depth of sorting preserves the input element predicate. *)
Lemma dom_order_sort_forall (P : N -> Prop) fuel positions xs :
  Forall P xs -> Forall P (dom_order_sort fuel positions xs).
Proof.
  revert xs. induction fuel as [|fuel IH]; intro xs; [exact (fun H => H)|].
  destruct xs as [|x [|y rest]]; intro Hxs; try exact Hxs.
  cbn [dom_order_sort].
  pose proof (dom_order_split_forall P (dom_order_half (length (x :: y :: rest)))
    (x :: y :: rest) Hxs) as Hparts.
  destruct (dom_order_split (dom_order_half (length (x :: y :: rest))) (x :: y :: rest))
    as [lower upper].
  destruct Hparts as [Hlower Hupper]. apply dom_order_merge_forall; now apply IH.
Qed.


(** * Merge callback and loop clocks *)

(** Reading a start position spends only the encoded numeric key width. *)
Lemma dom_order_anchor_start_clock width positions vertex :
  N.size_nat vertex <= width ->
  (T_dom_anchor_start positions vertex <= 16 * N.of_nat (width + 1))%N.
Proof.
  intro Hvertex.
  pose proof (dom_lt_time_key vertex) as Hkey.
  pose proof (dom_lt_key_width vertex) as Hbits.
  unfold T_dom_anchor_start. time_simpl. PTrieT.trie_get_le.
  destruct (trie_get (dom_lt_key vertex) positions) as [[lo hi]|];
    time_simpl; rewrite !Nat2N.inj_add in *; lia.
Qed.

Definition dom_order_merge_pending (state : dom_order_merge_state) : nat :=
  length (merge_lower state) + length (merge_upper state).

Definition dom_order_merge_operand width positions vertex : Prop :=
  N.size_nat vertex <= width /\ N.size_nat (dom_anchor_start positions vertex) <= width.

(** A continuing merge transition retires exactly one pending occurrence. *)
Lemma dom_order_merge_pending_step positions state next :
  dom_order_merge_step positions state = inl next ->
  S (dom_order_merge_pending next) = dom_order_merge_pending state.
Proof.
  destruct state as [lower upper reverse].
  unfold dom_order_merge_step. cbn [merge_lower merge_upper merge_reverse].
  destruct lower as [|left lower], upper as [|right upper]; intro Hnext;
    try discriminate Hnext.
  destruct (N.leb (dom_anchor_start positions left) (dom_anchor_start positions right));
    injection Hnext as <-; unfold dom_order_merge_pending;
    cbn [merge_lower merge_upper length]; lia.
Qed.

(** A continuing callback performs two start lookups and one bounded comparison. *)
Lemma dom_order_merge_go_clock width positions state next :
  Forall (dom_order_merge_operand width positions) (merge_lower state) ->
  Forall (dom_order_merge_operand width positions) (merge_upper state) ->
  dom_order_merge_step positions state = inl next ->
  (T_dom_order_merge_step positions state <= 128 * N.of_nat (width + 1))%N.
Proof.
  destruct state as [lower upper reverse].
  cbn [merge_lower merge_upper]. intros Hlower Hupper Hnext.
  unfold dom_order_merge_step in Hnext.
  cbn [merge_lower merge_upper merge_reverse] in Hnext.
  destruct lower as [|left lower], upper as [|right upper]; try discriminate Hnext.
  inversion Hlower as [|head tail Hleft Hlower_tail]; subst head tail.
  inversion Hupper as [|head tail Hright Hupper_tail]; subst head tail.
  destruct Hleft as [Hleft_key Hleft_start], Hright as [Hright_key Hright_start].
  pose proof (dom_order_anchor_start_clock width positions left Hleft_key) as Hleft_clock.
  pose proof (dom_order_anchor_start_clock width positions right Hright_key) as Hright_clock.
  pose proof (N.T_leb_le (dom_anchor_start positions left)
    (dom_anchor_start positions right)) as Hcompare.
  unfold T_dom_order_merge_step. cbn [merge_lower merge_upper merge_reverse].
  destruct (N.leb (dom_anchor_start positions left) (dom_anchor_start positions right));
    time_simpl; clear -Hleft_start Hleft_clock Hright_clock Hcompare;
    rewrite !Nat2N.inj_add in *; lia.
Qed.

(** A terminal callback reverses the accumulated prefix once. *)
Lemma dom_order_merge_stop_clock positions state result :
  dom_order_merge_step positions state = inr result ->
  (T_dom_order_merge_step positions state <= N.of_nat (length (merge_reverse state)) + 16)%N.
Proof.
  destruct state as [lower upper reverse].
  unfold dom_order_merge_step. cbn [merge_lower merge_upper merge_reverse].
  destruct lower as [|left lower], upper as [|right upper]; intro Hstop.
  - pose proof (List.T_rev_append_le reverse []) as Hreverse.
    unfold T_dom_order_merge_step. cbn [merge_lower merge_upper merge_reverse]. time_simpl.
    clear -Hreverse. lia.
  - pose proof (List.T_rev_append_le reverse (right :: upper)) as Hreverse.
    unfold T_dom_order_merge_step. cbn [merge_lower merge_upper merge_reverse]. time_simpl.
    clear -Hreverse. lia.
  - pose proof (List.T_rev_append_le reverse (left :: lower)) as Hreverse.
    unfold T_dom_order_merge_step. cbn [merge_lower merge_upper merge_reverse]. time_simpl.
    clear -Hreverse. lia.
  - destruct (N.leb (dom_anchor_start positions left) (dom_anchor_start positions right));
      discriminate Hstop.
Qed.

(** One strict unit of potential pays a continuing callback and the retired cell. *)
Lemma dom_order_merge_credit_step cost unit before after :
  (cost <= unit)%N -> (before = after + 1)%N ->
  (cost + (unit + 1) * after < (unit + 1) * before)%N.
Proof.
  intros Hcost Hcount. rewrite Hcount, N.mul_add_distr_l, N.mul_1_r. lia.
Qed.

(** A common row budget isolates the loop's width and occurrence products. *)
Lemma dom_order_merge_loop_budget coefficient width count fuel_width clock :
  (1 <= width)%N -> (fuel_width <= count + 1)%N ->
  (clock <= coefficient *
    ((128 * width + 1) * count + (count + 16) + fuel_width + 1))%N ->
  (clock <= 256 * (coefficient + 1) * ((count + 1) * width))%N.
Proof.
  intros Hwidth Hfuel Hclock.
  set (budget := ((count + 1) * width)%N).
  assert (Hcount : (count + 1 <= budget)%N).
  { unfold budget. replace (count + 1)%N with ((count + 1) * 1)%N at 1 by ring.
    now apply N.mul_le_mono_l. }
  assert (Hpositive : (1 <= budget)%N) by lia.
  assert (Hproduct : (count * width <= budget)%N).
  { unfold budget. apply N.mul_le_mono_r. lia. }
  assert (Hsteps : ((128 * width + 1) * count <= 129 * budget)%N).
  { replace ((128 * width + 1) * count)%N with
      (128 * (count * width) + count)%N by ring.
    eapply N.le_trans with (128 * budget + budget)%N.
    - apply N.add_le_mono; [now apply N.mul_le_mono_l|lia].
    - lia. }
  assert (Hinside : (((128 * width + 1) * count + (count + 16) + fuel_width + 1)
    <= 148 * budget)%N) by lia.
  eapply N.le_trans; [exact Hclock|].
  eapply N.le_trans with (coefficient * (148 * budget))%N.
  - now apply N.mul_le_mono_l.
  - replace (coefficient * (148 * budget))%N with ((148 * coefficient) * budget)%N by ring.
    apply N.mul_le_mono_r. lia.
Qed.

(** Setup and fallback work are linear once the loop clock is paid. *)
Lemma dom_order_merge_total_budget coefficient budget clock loop_clock :
  (clock <= loop_clock + 64 * budget)%N ->
  (loop_clock <= 256 * (coefficient + 1) * budget)%N ->
  (clock <= 1024 * (coefficient + 1) * budget)%N.
Proof.
  intros Hclock Hloop. eapply N.le_trans; [exact Hclock|].
  eapply N.le_trans with (256 * (coefficient + 1) * budget + 64 * budget)%N.
  - now apply N.add_le_mono_r.
  - replace (256 * (coefficient + 1) * budget + 64 * budget)%N with
      ((256 * (coefficient + 1) + 64) * budget)%N by ring.
    apply N.mul_le_mono_r. lia.
Qed.

(** The merge loop spends one bounded callback per retired input occurrence. *)
Lemma dom_order_merge_loop_clock width positions lower upper :
  Forall (dom_order_merge_operand width positions) lower ->
  Forall (dom_order_merge_operand width positions) upper ->
  (T_loopN (dom_order_merge_step positions) (T_dom_order_merge_step positions)
    (N.of_nat (length lower + length upper + 1)) (DomOrderMergeState lower upper []) <=
    256 * (c_loopN + 1) * N.of_nat ((length lower + length upper + 1) * (width + 1)))%N.
Proof.
  intros Hlower Hupper.
  set (total := length lower + length upper).
  set (Inv := fun state => dom_order_merge_mass state = total /\
    Forall (dom_order_merge_operand width positions) (merge_lower state) /\
    Forall (dom_order_merge_operand width positions) (merge_upper state) /\
    Forall (dom_order_merge_operand width positions) (merge_reverse state)).
  set (unit := (128 * N.of_nat (width + 1))%N).
  set (credit := fun state => ((unit + 1) * N.of_nat (dom_order_merge_pending state))%N).
  assert (Hgo : forall state next, Inv state ->
    dom_order_merge_step positions state = inl next ->
    Inv next /\ (T_dom_order_merge_step positions state + credit next < credit state)%N).
  { intros state next [Hmass [Hl [Hu Hr]]] Hstep. split.
    - unfold Inv. split.
      + pose proof (dom_order_merge_step_mass positions state) as Hnext.
        rewrite Hstep in Hnext. exact (eq_trans Hnext Hmass).
      + pose proof (dom_order_merge_step_forall
          (dom_order_merge_operand width positions) positions state Hl Hu Hr) as Hnext.
        now rewrite Hstep in Hnext.
    - pose proof (dom_order_merge_go_clock width positions state next Hl Hu Hstep) as Hclock.
      pose proof (dom_order_merge_pending_step positions state next Hstep) as Hcount.
      apply (f_equal N.of_nat) in Hcount. rewrite Nat2N.inj_succ in Hcount.
      unfold credit. apply dom_order_merge_credit_step; [exact Hclock|].
      clear -Hcount. lia. }
  assert (Hstop : forall state result, Inv state ->
    dom_order_merge_step positions state = inr result ->
    (T_dom_order_merge_step positions state <= N.of_nat total + 16)%N).
  { intros state result [Hmass Hwidths] Hstep.
    pose proof (dom_order_merge_stop_clock positions state result Hstep) as Hclock.
    eapply N.le_trans; [exact Hclock|]. apply N.add_le_mono_r.
    apply time_of_nat_le. unfold dom_order_merge_mass in Hmass. lia. }
  assert (Hinitial : Inv (DomOrderMergeState lower upper [])).
  { unfold Inv, dom_order_merge_mass, total.
    cbn [merge_lower merge_upper merge_reverse length].
    split; [lia|]. split; [exact Hlower|]. split; [exact Hupper|constructor]. }
  pose proof (T_loopN_le dom_order_merge_state (list N)
    (dom_order_merge_step positions) (T_dom_order_merge_step positions)
    Inv credit (N.of_nat total + 16)%N (N.of_nat (total + 1))
    (DomOrderMergeState lower upper []) Hgo Hstop Hinitial) as Hloop.
  change (T_loopN (dom_order_merge_step positions) (T_dom_order_merge_step positions)
    (N.of_nat (total + 1)) (DomOrderMergeState lower upper []) <=
    c_loopN * (((128 * N.of_nat (width + 1) + 1) * N.of_nat total) +
      (N.of_nat total + 16) + N.of_nat (N.size_nat (N.of_nat (total + 1))) + 1))%N in Hloop.
  pose proof (dom_size_value (N.of_nat (total + 1))) as Hfuel.
  assert (Hfuel_width : (N.of_nat (N.size_nat (N.of_nat (total + 1))) <=
    N.of_nat total + 1)%N).
  { eapply N.le_trans; [exact Hfuel|]. rewrite Nat2N.inj_add. reflexivity. }
  fold total. rewrite Nat2N.inj_mul.
  replace (N.of_nat (total + 1) * N.of_nat (width + 1))%N with
    ((N.of_nat total + 1) * N.of_nat (width + 1))%N by
    (rewrite (Nat2N.inj_add total 1); reflexivity).
  eapply dom_order_merge_loop_budget with
    (fuel_width := N.of_nat (N.size_nat (N.of_nat (total + 1))));
    [clear -width; rewrite Nat2N.inj_add; lia|exact Hfuel_width|exact Hloop].
Qed.

(** Setup and the possible exhausted-loop fallback do only linear list work. *)
Lemma dom_order_merge_overhead positions lower upper :
  (T_dom_order_merge positions lower upper <=
    T_loopN (dom_order_merge_step positions) (T_dom_order_merge_step positions)
      (N.of_nat (length lower + length upper + 1)) (DomOrderMergeState lower upper []) +
    64 * N.of_nat (length lower + length upper + 1))%N.
Proof.
  set (total := length lower + length upper).
  set (initial := DomOrderMergeState lower upper []).
  set (fuel := N.of_nat (total + 1)).
  pose proof (dom_lt_loop_invariant (dom_order_merge_step positions)
    (fun state => dom_order_merge_mass state = total)
    (fun result => length result = total) fuel initial) as Hvalue.
  specialize (Hvalue ltac:(intros state next Hmass Hstep;
    pose proof (dom_order_merge_step_mass positions state) as Hnext;
    rewrite Hstep in Hnext; exact (eq_trans Hnext Hmass))).
  specialize (Hvalue ltac:(intros state result Hmass Hstep;
    pose proof (dom_order_merge_step_mass positions state) as Hnext;
    rewrite Hstep in Hnext; exact (eq_trans Hnext Hmass))).
  assert (Hinitial : dom_order_merge_mass initial = total).
  { unfold initial, total, dom_order_merge_mass.
    cbn [merge_lower merge_upper merge_reverse length]. lia. }
  specialize (Hvalue Hinitial).
  pose proof (Datatypes.T_length_le lower) as Hlower.
  pose proof (Datatypes.T_length_le upper) as Hupper.
  pose proof (Nat.T_add_le (length lower) (length upper)) as Hadd.
  pose proof (Nat.T_add_le total 1) as Hadd_one.
  pose proof (dom_time_of_nat (total + 1)) as Hconvert.
  unfold T_dom_order_merge. time_simpl. fold total. fold fuel. fold initial.
  change (fun state : dom_order_merge_state => T_dom_order_merge_step positions state)
    with (T_dom_order_merge_step positions).
  set (clock := T_loopN (dom_order_merge_step positions) (T_dom_order_merge_step positions)
    fuel initial).
  fold clock. clearbody clock.
  destruct (loopN (dom_order_merge_step positions) fuel initial) as [state|result].
  - pose proof (Datatypes.T_app_le (merge_lower state) (merge_upper state)) as Happ.
    pose proof (List.T_rev_append_le (merge_reverse state)
      (merge_lower state ++ merge_upper state)) as Hreverse.
    time_simpl. unfold dom_order_merge_mass in Hvalue.
    clear -Hvalue Hlower Hupper Hadd Hadd_one Hconvert Happ Hreverse.
    unfold total in *. rewrite !Nat2N.inj_add in *. lia.
  - time_simpl. clear -Hlower Hupper Hadd Hadd_one Hconvert.
    unfold total in *. rewrite !Nat2N.inj_add in *. lia.
Qed.

Definition dom_order_merge_coefficient : N := (1024 * (c_loopN + 1))%N.

(** Full merge time is linear in the row lengths and the bounded operand width. *)
Lemma dom_order_merge_time width positions lower upper :
  Forall (dom_order_merge_operand width positions) lower ->
  Forall (dom_order_merge_operand width positions) upper ->
  (T_dom_order_merge positions lower upper <= dom_order_merge_coefficient *
    N.of_nat ((length lower + length upper + 1) * (width + 1)))%N.
Proof.
  intros Hlower Hupper.
  pose proof (dom_order_merge_loop_clock width positions lower upper Hlower Hupper) as Hloop.
  pose proof (dom_order_merge_overhead positions lower upper) as Hraw.
  assert (Hsize : (N.of_nat (length lower + length upper + 1) <=
    N.of_nat ((length lower + length upper + 1) * (width + 1)))%N).
  { apply time_of_nat_le.
    replace (length lower + length upper + 1) with
      ((length lower + length upper + 1) * 1) at 1 by lia.
    apply Nat.mul_le_mono_l. lia. }
  unfold dom_order_merge_coefficient.
  eapply dom_order_merge_total_budget with
    (loop_clock := T_loopN (dom_order_merge_step positions) (T_dom_order_merge_step positions)
      (N.of_nat (length lower + length upper + 1)) (DomOrderMergeState lower upper [])).
  - eapply N.le_trans; [exact Hraw|]. apply N.add_le_mono_l.
    now apply N.mul_le_mono_l.
  - exact Hloop.
Qed.

(** * Sorting clocks with a per-occurrence recursion budget *)

(** The two recursive rows divide their parent mass without duplicating its budget. *)
Lemma dom_order_sort_children_budget (unit depth lower upper total left_work right_work : N) :
  (lower + upper = total)%N ->
  (left_work <= unit * (depth * lower) + 1)%N ->
  (right_work <= unit * (depth * upper) + 1)%N ->
  (left_work + right_work <= unit * (depth * total) + 2)%N.
Proof.
  intros Hspan Hleft Hright.
  replace (unit * (depth * total) + 2)%N with
    ((unit * (depth * lower) + 1) + (unit * (depth * upper) + 1))%N by
    (rewrite <- Hspan; ring).
  now apply N.add_le_mono.
Qed.

(** A nontrivial row pays splitting, merging and fixed wrappers from its own cells. *)
Lemma dom_order_sort_step_budget coefficient width size overhead merge_clock :
  (1 <= width)%N -> (2 <= size)%N ->
  (overhead <= 4 * size + 8)%N ->
  (merge_clock <= coefficient * ((size + 1) * width))%N ->
  (overhead + merge_clock + 32 <= 64 * (coefficient + 1) * width * size)%N.
Proof.
  intros Hwidth Hsize Hoverhead Hmerge.
  set (budget := (width * size)%N).
  assert (Hcells : (size <= budget)%N).
  { unfold budget. replace size with (1 * size)%N at 1 by ring.
    now apply N.mul_le_mono_r. }
  assert (Hpositive : (1 <= budget)%N) by lia.
  assert (Hspan : ((size + 1) * width <= 2 * budget)%N).
  { unfold budget. replace (2 * (width * size))%N with ((2 * size) * width)%N by ring.
    apply N.mul_le_mono_r. lia. }
  assert (Hmerge_bound : (merge_clock <= (2 * coefficient) * budget)%N).
  { eapply N.le_trans; [exact Hmerge|].
    replace ((2 * coefficient) * budget)%N with (coefficient * (2 * budget))%N by ring.
    now apply N.mul_le_mono_l. }
  replace (64 * (coefficient + 1) * width * size)%N with
    (64 * (coefficient + 1) * budget)%N by (unfold budget; ring).
  eapply N.le_trans with ((44 + 2 * coefficient) * budget)%N.
  - replace ((44 + 2 * coefficient) * budget)%N with
      (44 * budget + (2 * coefficient) * budget)%N by ring. lia.
  - apply N.mul_le_mono_r. lia.
Qed.

(** The generated sorting wrapper exposes its two recursive calls and one merge. *)
Lemma dom_order_sort_wrapper_clock fuel positions x y rest lower upper :
  dom_order_split (dom_order_half (length (x :: y :: rest))) (x :: y :: rest) =
    (lower, upper) ->
  (T_dom_order_sort (S fuel) positions (x :: y :: rest) <=
    16 + Datatypes.T_length (x :: y :: rest) +
    T_dom_order_half (length (x :: y :: rest)) +
    T_dom_order_split (dom_order_half (length (x :: y :: rest))) (x :: y :: rest) +
    T_dom_order_sort fuel positions lower + T_dom_order_sort fuel positions upper +
    T_dom_order_merge positions (dom_order_sort fuel positions lower)
      (dom_order_sort fuel positions upper))%N.
Proof.
  intro Hsplit. time_unfold T_dom_order_sort. rewrite Hsplit. time_simpl. lia.
Qed.

Definition dom_order_sort_coefficient : N := (64 * (dom_order_merge_coefficient + 1))%N.

(** Sorting charges a linear row budget per explicit level and one terminal administrative unit. *)
Lemma dom_order_sort_time width fuel positions xs :
  Forall (dom_order_merge_operand width positions) xs ->
  (T_dom_order_sort fuel positions xs <=
    dom_order_sort_coefficient * N.of_nat (width + 1) *
      N.of_nat ((fuel + 1) * length xs) + 1)%N.
Proof.
  set (unit := (dom_order_sort_coefficient * N.of_nat (width + 1))%N).
  change (Forall (dom_order_merge_operand width positions) xs ->
    (T_dom_order_sort fuel positions xs <= unit * N.of_nat ((fuel + 1) * length xs) + 1)%N).
  revert xs. induction fuel as [|fuel IH]; intros xs Hxs.
  - time_unfold T_dom_order_sort. time_simpl. lia.
  - destruct xs as [|x [|y rest]].
    + time_unfold T_dom_order_sort. time_simpl. lia.
    + time_unfold T_dom_order_sort. time_simpl. lia.
    + pose proof (dom_order_split_length (dom_order_half (length (x :: y :: rest)))
        (x :: y :: rest)) as Hlength.
      pose proof (dom_order_split_forall (dom_order_merge_operand width positions)
        (dom_order_half (length (x :: y :: rest))) (x :: y :: rest) Hxs) as Hparts.
      destruct (dom_order_split (dom_order_half (length (x :: y :: rest)))
        (x :: y :: rest)) as [lower upper] eqn:Hsplit.
      cbn [fst snd] in Hlength, Hparts. destruct Hparts as [Hlower Hupper].
      pose proof (IH lower Hlower) as Hlower_time.
      pose proof (IH upper Hupper) as Hupper_time.
      pose proof (dom_order_sort_forall (dom_order_merge_operand width positions)
        fuel positions lower Hlower) as Hlower_sorted.
      pose proof (dom_order_sort_forall (dom_order_merge_operand width positions)
        fuel positions upper Hupper) as Hupper_sorted.
      pose proof (dom_order_merge_time width positions (dom_order_sort fuel positions lower)
        (dom_order_sort fuel positions upper) Hlower_sorted Hupper_sorted) as Hmerge.
      rewrite !dom_order_sort_length, Hlength in Hmerge.
      pose proof (Datatypes.T_length_le (x :: y :: rest)) as Hlength_time.
      pose proof (dom_order_half_time (length (x :: y :: rest))) as Hhalf.
      pose proof (dom_order_split_time (dom_order_half (length (x :: y :: rest)))
        (x :: y :: rest)) as Hsplit_time.
      assert (Hspan : (N.of_nat (length lower) + N.of_nat (length upper) =
        N.of_nat (length (x :: y :: rest)))%N).
      { rewrite <- Nat2N.inj_add, Hlength. reflexivity. }
      assert (Hrecursive : (T_dom_order_sort fuel positions lower +
        T_dom_order_sort fuel positions upper <=
        unit * ((N.of_nat fuel + 1) * N.of_nat (length (x :: y :: rest))) + 2)%N).
      { rewrite !Nat2N.inj_mul, !Nat2N.inj_add in Hlower_time, Hupper_time.
        eapply dom_order_sort_children_budget;
          [exact Hspan|exact Hlower_time|exact Hupper_time]. }
      assert (Hoverhead : (Datatypes.T_length (x :: y :: rest) +
        T_dom_order_half (length (x :: y :: rest)) +
        T_dom_order_split (dom_order_half (length (x :: y :: rest))) (x :: y :: rest) +
        T_dom_order_merge positions (dom_order_sort fuel positions lower)
          (dom_order_sort fuel positions upper) + 32 <=
        unit * N.of_nat (length (x :: y :: rest)))%N).
      { unfold unit, dom_order_sort_coefficient.
        eapply dom_order_sort_step_budget.
        - clear -width. rewrite Nat2N.inj_add. lia.
        - cbn [length]. lia.
        - clear -Hlength_time Hhalf Hsplit_time. lia.
        - rewrite Nat2N.inj_mul, Nat2N.inj_add in Hmerge. exact Hmerge. }
      pose proof (dom_order_sort_wrapper_clock fuel positions x y rest lower upper Hsplit) as Hraw.
      rewrite Nat2N.inj_mul, Nat2N.inj_add, Nat2N.inj_succ.
      replace (unit * ((N.succ (N.of_nat fuel) + 1) * N.of_nat (length (x :: y :: rest))))%N
        with (unit * ((N.of_nat fuel + 1) * N.of_nat (length (x :: y :: rest))) +
          unit * N.of_nat (length (x :: y :: rest)))%N by (rewrite <- N.add_1_r; ring).
      clear -Hraw Hrecursive Hoverhead. lia.
Qed.

(** * Child-row inventories *)


(** A child insertion adds at most one occurrence over any distinct key inventory. *)
Lemma dom_order_child_add_mass keys parents rows vertex :
  NoDup keys ->
  dom_lt_row_mass keys (dom_order_child_add parents rows vertex) <=
    S (dom_lt_row_mass keys rows).
Proof.
  intro Hunique. unfold dom_order_child_add.
  destruct (trie_get (dom_lt_key vertex) parents) as [parent|]; [|lia].
  unfold dom_order_row. now apply dom_lt_row_mass_push.
Qed.

(** Building child rows adds at most one occurrence per supplied vertex. *)
Lemma dom_order_child_fold_mass keys parents order rows :
  NoDup keys ->
  dom_lt_row_mass keys (fold_left (dom_order_child_add parents) order rows) <=
    length order + dom_lt_row_mass keys rows.
Proof.
  intro Hunique. revert rows. induction order as [|vertex rest IH]; intro rows.
  - cbn [fold_left length]. reflexivity.
  - pose proof (dom_order_child_add_mass keys parents rows vertex Hunique) as Hhead.
    specialize (IH (dom_order_child_add parents rows vertex)).
    cbn [fold_left length]. clear -Hhead IH. lia.
Qed.

(** Child rows built from empty storage contain at most the input's total number of vertices. *)
Lemma dom_order_children_mass keys parents order :
  NoDup keys ->
  dom_lt_row_mass keys (fold_left (dom_order_child_add parents) order Empty) <= length order.
Proof.
  intro Hunique. pose proof (dom_order_child_fold_mass keys parents order Empty Hunique) as Hmass.
  now rewrite dom_lt_row_mass_empty, Nat.add_0_r in Hmass.
Qed.

(** Reading a row preserves a payload property, including the empty default. *)
Lemma dom_order_row_forall (P : N -> Prop) rows vertex :
  dom_lt_trie_all (Forall P) rows -> Forall P (dom_order_row rows vertex).
Proof.
  intro Hrows. unfold dom_order_row.
  destruct (trie_get (dom_lt_key vertex) rows) as [row|] eqn:Hget.
  - now apply (Hrows (dom_lt_key vertex)).
  - constructor.
Qed.

(** A child insertion retains the row predicate when its new vertex satisfies it. *)
Lemma dom_order_child_add_forall (P : N -> Prop) parents rows vertex :
  dom_lt_trie_all (Forall P) rows -> P vertex ->
  dom_lt_trie_all (Forall P) (dom_order_child_add parents rows vertex).
Proof.
  intros Hrows Hvertex. unfold dom_order_child_add.
  destruct (trie_get (dom_lt_key vertex) parents) as [parent|]; [|exact Hrows].
  apply dom_lt_trie_all_set; [exact Hrows|].
  constructor; [exact Hvertex|now apply dom_order_row_forall].
Qed.

(** Every child-row member comes from an input satisfying the same predicate. *)
Lemma dom_order_child_fold_forall (P : N -> Prop) parents order rows :
  Forall P order -> dom_lt_trie_all (Forall P) rows ->
  dom_lt_trie_all (Forall P) (fold_left (dom_order_child_add parents) order rows).
Proof.
  intro Horder. revert rows.
  induction Horder as [|vertex rest Hvertex Hrest IH]; intros rows Hrows.
  - exact Hrows.
  - cbn [fold_left]. apply IH. now apply dom_order_child_add_forall.
Qed.

(** Child-row skeleton allocation charges one bounded parent key per original input. *)
Lemma dom_order_child_fold_nodes parents order rows width :
  (forall vertex parent, In vertex order ->
    trie_get (dom_lt_key vertex) parents = Some parent ->
    Pos.size_nat (dom_lt_key parent) <= width) ->
  PTrie.nodes (fold_left (dom_order_child_add parents) order rows) <=
    PTrie.nodes rows + length order * width.
Proof.
  revert rows. induction order as [|vertex rest IH]; intros rows Hwidth.
  - cbn [fold_left length]. lia.
  - pose proof (IH (dom_order_child_add parents rows vertex)
      (fun v p Hv => Hwidth v p (or_intror Hv))) as Hrest.
    assert (Hhead : PTrie.nodes (dom_order_child_add parents rows vertex) <=
      PTrie.nodes rows + width).
    { unfold dom_order_child_add.
      destruct (trie_get (dom_lt_key vertex) parents) as [parent|] eqn:Hparent; [|lia].
      pose proof (PTrie.nodes_set (list N) (dom_lt_key parent)
        (vertex :: dom_order_row rows parent) rows) as Hset.
      pose proof (Hwidth vertex parent (or_introl eq_refl) Hparent) as Hparent_width. lia. }
    cbn [fold_left length]. clear -Hhead Hrest. lia.
Qed.

(** Any individual child row is bounded by the original order's length. *)
Lemma dom_order_children_row_length parents order vertex :
  length (dom_order_row (fold_left (dom_order_child_add parents) order Empty) vertex) <=
    length order.
Proof.
  pose proof (dom_order_children_mass [dom_lt_key vertex] parents order
    ltac:(constructor; [intro Hbad; contradiction|constructor])) as Hmass.
  unfold dom_lt_row_mass in Hmass. cbn [fold_right] in Hmass.
  unfold dom_order_row. lia.
Qed.

(** Summing actual row bindings agrees with reading those same distinct keys from the trie. *)
Lemma dom_order_elements_row_mass (rows : ptrie (list N)) :
  fold_right (fun entry total => length (snd entry) + total) 0 (PTrieCode.elements rows) =
    dom_lt_row_mass (map fst (PTrieCode.elements rows)) rows.
Proof.
  assert (Hread : forall entries,
    Forall (fun entry => trie_get (fst entry) rows = Some (snd entry)) entries ->
    fold_right (fun entry total => length (snd entry) + total) 0 entries =
      dom_lt_row_mass (map fst entries) rows).
  { intros entries Hall. induction Hall as [|[key row] rest Hget Hrest IH].
    - reflexivity.
    - unfold dom_lt_row_mass in *. cbn [map fold_right fst snd] in *.
      now rewrite Hget, IH. }
  apply Hread. apply Forall_forall. intros [key row] Hin. cbn [fst snd].
  now apply PTrie.elements_spec in Hin.
Qed.

(** All stored child rows together contain at most one occurrence per input vertex. *)
Lemma dom_order_children_elements_mass parents order :
  fold_right (fun entry total => length (snd entry) + total) 0
    (PTrieCode.elements (fold_left (dom_order_child_add parents) order Empty)) <= length order.
Proof.
  rewrite dom_order_elements_row_mass. apply dom_order_children_mass.
  apply PTrie.elements_nodup.
Qed.

(** Mapping a length-preserving row transformation retains every finite row-mass bound. *)
Lemma dom_order_row_mass_map_length keys rows (f : list N -> list N) :
  (forall row, length (f row) = length row) ->
  dom_lt_row_mass keys (PTrieCode.map f rows) = dom_lt_row_mass keys rows.
Proof.
  intro Hlength. unfold dom_lt_row_mass.
  induction keys as [|key rest IH]; cbn [fold_right]; [reflexivity|].
  rewrite PTrie.get_map. change (PTrie.get key rows) with (trie_get key rows).
  destruct (trie_get key rows); cbn [option_map];
    rewrite ?Hlength, IH; reflexivity.
Qed.

(** * Row-sensitive fold clocks *)

(** A stateful fold pays each callback's input-dependent upper bound once. *)
Lemma dom_order_fold_sum_clock {A B : Type} (step : A -> B -> A) (T_step : A -> B -> N)
    (weight : B -> N) xs st :
  (forall item, In item xs -> forall current, (T_step current item <= weight item)%N) ->
  (List.T_fold_left step T_step xs st <=
    N.of_nat (length xs) + fold_right N.add 0 (map weight xs) + 1)%N.
Proof.
  revert st. induction xs as [|item rest IH]; intros st Hstep.
  - time_unfold @List.T_fold_left. cbn [length map fold_right]. lia.
  - pose proof (Hstep item (or_introl eq_refl) st) as Hhead.
    specialize (IH (step st item) (fun x Hx => Hstep x (or_intror Hx))).
    time_unfold @List.T_fold_left. cbn [length map fold_right].
    rewrite Nat2N.inj_succ. clear -IH Hhead. lia.
Qed.

(** A uniform multiplier factors out of the finite sum of natural input weights. *)
Lemma dom_order_sum_scaled {A : Type} (weight : A -> nat) xs coefficient :
  fold_right N.add 0%N (map (fun item => coefficient * N.of_nat (weight item))%N xs) =
    (coefficient * N.of_nat (fold_right (fun item total => (weight item + total)%nat) 0%nat xs))%N.
Proof.
  induction xs as [|item rest IH]; cbn [map fold_right].
  - change (0 = coefficient * 0)%N. now rewrite N.mul_0_r.
  - rewrite IH, Nat2N.inj_add, N.mul_add_distr_l. reflexivity.
Qed.

(** Adding a fixed per-element natural allowance contributes exactly the list length. *)
Lemma dom_order_sum_allowance {A : Type} (weight : A -> nat) xs allowance :
  fold_right (fun item total => weight item + allowance + total) 0 xs =
    fold_right (fun item total => weight item + total) 0 xs + allowance * length xs.
Proof.
  induction xs as [|item rest IH]; cbn [fold_right length]; [ring|].
  rewrite IH. ring.
Qed.

(** Reading numeric child rows over an order is the row mass of the encoded order keys. *)
Lemma dom_order_rows_sum order rows :
  fold_right (fun vertex total => length (dom_order_row rows vertex) + total) 0 order =
    dom_lt_row_mass (map dom_lt_key order) rows.
Proof.
  unfold dom_lt_row_mass, dom_order_row.
  induction order as [|vertex rest IH]; cbn [fold_right map]; [reflexivity|].
  now rewrite IH.
Qed.

(** * Summed child-row callback costs *)

(** One administrative unit per callback contributes exactly the number of stored bindings. *)
Lemma dom_order_sum_unit {A : Type} (weight : A -> N) xs :
  fold_right N.add 0%N (map (fun x => (1 + weight x)%N) xs) =
    (N.of_nat (length xs) + fold_right N.add 0 (map weight xs))%N.
Proof.
  induction xs as [|x rest IH]; cbn [map fold_right length]; [reflexivity|].
  rewrite IH, Nat2N.inj_succ. lia.
Qed.

(** Trie mapping pays each present callback once, allowing rows to have different lengths. *)
Lemma dom_order_map_time_sum {A B : Type} (f : A -> B) (T_f : A -> N) rows :
  (PTrieT.T_map f T_f rows <= (PTrieT.k_filter + 1) *
    (N.of_nat (PTrie.nodes rows + 1) +
      N.of_nat (length (PTrieCode.elements rows)) +
      fold_right N.add 0 (map (fun ka => T_f (snd ka)) (PTrieCode.elements rows)) + 1))%N.
Proof.
  pose proof (@PTrieT.T3_filter_sum A B (fun a => Some (f a))
    (fun a => (1 + T_f a)%N) rows) as Hfilter.
  cbn beta in Hfilter. rewrite dom_order_sum_unit in Hfilter.
  time_unfold @PTrieT.T_map. time_simpl. nia.
Qed.

(** Quadratic values in a distinct key count need at most twice the original width plus four. *)
Lemma dom_distinct_quadratic_width xs width value :
  NoDup xs -> (forall key, In key xs -> Pos.size_nat key <= width) ->
  (value <= 8 * (N.of_nat (length xs) + 1) * (N.of_nat (length xs) + 1))%N ->
  N.size_nat value <= 2 * width + 4.
Proof.
  intros Hunique Hwidth Hvalue.
  pose proof (dom_distinct_keys_cardinality xs width Hunique Hwidth) as Hlength.
  assert (Hcapacity : length xs + 1 <= Nat.pow 2 width) by lia.
  destruct value as [|p]; [cbn; lia|].
  assert (Hnatural : N.to_nat (N.pos p) <=
    N.to_nat (8 * (N.of_nat (length xs) + 1) * (N.of_nat (length xs) + 1))%N).
  { apply Nat.compare_le_iff. rewrite <- N2Nat.inj_compare. exact Hvalue. }
  rewrite !N2Nat.inj_mul, !N2Nat.inj_add, !Nat2N.id in Hnatural.
  cbn [N.to_nat] in Hnatural. cbn [N.size_nat]. apply Pos.size_nat_least.
  replace (2 * width + 4) with (width + width + 4) by lia.
  rewrite !Nat.pow_add_r. cbn [Nat.pow]. nia.
Qed.

(** The explicit index and sorting fuel fits the logarithm of any containing size bound. *)
Lemma dom_order_value_log_width value bound :
  (value <= N.of_nat bound)%N -> N.size_nat value <= Nat.log2 bound + 1.
Proof.
  intro Hbound. destruct value as [|p]; [cbn; lia|].
  cbn [N.size_nat]. apply Pos.size_nat_least.
  assert (Hnatural : Pos.to_nat p <= bound) by lia.
  pose proof (Pos2Nat.is_pos p) as Hpositive.
  pose proof (Nat.log2_spec bound ltac:(lia)) as Hlog.
  replace (Nat.log2 bound + 1) with (S (Nat.log2 bound)) by lia. lia.
Qed.

(** * Amortized replay composition *)

Local Opaque Argent.Loop.loop T_loopN.

Definition dom_lt_replay_selected (st : dom_lt_replay) : dom_lt_links :=
  if N.eqb (replay_index st) (replay_boundary st)
  then DomLtLinks Empty Empty [] else replay_links st.

Definition dom_lt_replay_credit (bound width : nat) (st : dom_lt_replay) : N :=
  (dom_lt_eval_unit width * dom_lt_forest_credit bound (replay_links st) +
    dom_eqb_credit (replay_boundary st) (replay_index st) +
    dom_counter_credit (replay_index st))%N.

Definition dom_lt_replay_no_reset (boundary index : N) (count : nat) : Prop :=
  (boundary < index \/ index + N.of_nat count <= boundary)%N.

Lemma dom_lt_replay_no_reset_head boundary index count :
  dom_lt_replay_no_reset boundary index (S count) -> N.eqb index boundary = false.
Proof.
  intros Hphase. apply N.eqb_neq. unfold dom_lt_replay_no_reset in Hphase. lia.
Qed.

Lemma dom_lt_replay_no_reset_tail boundary index count :
  dom_lt_replay_no_reset boundary index (S count) ->
  dom_lt_replay_no_reset boundary (N.succ index) count.
Proof.
  unfold dom_lt_replay_no_reset. intros [Hafter|Hbefore]; [left|right]; lia.
Qed.

Lemma dom_lt_replay_selected_no_reset st count :
  dom_lt_replay_no_reset (replay_boundary st) (replay_index st) (S count) ->
  dom_lt_replay_selected st = replay_links st.
Proof.
  intro Hphase. unfold dom_lt_replay_selected.
  now rewrite (dom_lt_replay_no_reset_head _ _ _ Hphase).
Qed.

Lemma dom_lt_empty_bounded bound : dom_lt_links_bounded bound (DomLtLinks Empty Empty []).
Proof.
  split; apply dom_lt_trie_all_empty.
Qed.

Lemma dom_lt_replay_step_links st op :
  replay_links (dom_lt_replay_step st op) =
    match op with
    | LtLink child parent => dom_lt_link (dom_lt_replay_selected st) child parent
    | LtEval vertex =>
        fst (dom_lt_eval (replay_fuel st) (replay_semis st) (dom_lt_replay_selected st) vertex)
    end.
Proof.
  destruct op; reflexivity.
Qed.

Lemma dom_lt_replay_fold_fields ops : forall st,
  replay_semis (fold_left dom_lt_replay_step ops st) = replay_semis st /\
  replay_fuel (fold_left dom_lt_replay_step ops st) = replay_fuel st /\
  replay_boundary (fold_left dom_lt_replay_step ops st) = replay_boundary st.
Proof.
  induction ops as [|op rest IH]; intro st; [repeat split; reflexivity|].
  cbn [fold_left]. destruct (IH (dom_lt_replay_step st op)) as [Hsemis [Hfuel Hboundary]].
  destruct (dom_lt_replay_fields st op) as [Hsemis_step [Hfuel_step [Hboundary_step Hindex]]].
  repeat split; congruence.
Qed.

Lemma dom_lt_replay_step_range bound st op :
  dom_lt_links_bounded bound (dom_lt_replay_selected st) -> dom_lt_op_bounded bound op ->
  dom_lt_links_bounded bound (replay_links (dom_lt_replay_step st op)).
Proof.
  intros Hlinks Hop. rewrite dom_lt_replay_step_links.
  destruct op as [child parent|vertex].
  - destruct Hop as [Hchild Hparent]. now apply dom_lt_link_bounded.
  - exact (proj1 (dom_lt_eval_bounded bound (replay_fuel st) (replay_semis st)
      (dom_lt_replay_selected st) vertex Hlinks Hop)).
Qed.

Lemma dom_lt_replay_step_fresh st op ops :
  NoDup (dom_lt_link_children (op :: ops)) ->
  dom_lt_links_fresh (dom_lt_replay_selected st) (dom_lt_link_children (op :: ops)) ->
  dom_lt_links_fresh (replay_links (dom_lt_replay_step st op)) (dom_lt_link_children ops).
Proof.
  intros Hunique Hfresh. rewrite dom_lt_replay_step_links.
  destruct op as [child parent|vertex].
  - cbn [dom_lt_link_children] in Hunique, Hfresh.
    inversion Hunique as [|head tail Hnew Htail]; subst head tail.
    apply dom_lt_link_fresh; [exact Hnew|].
    intros key Hin. apply Hfresh. now right.
  - now apply dom_lt_eval_fresh.
Qed.

Lemma dom_lt_link_children_tail_unique op ops :
  NoDup (dom_lt_link_children (op :: ops)) -> NoDup (dom_lt_link_children ops).
Proof.
  destruct op; cbn [dom_lt_link_children]; intro Hunique; [now inversion Hunique|exact Hunique].
Qed.

Definition dom_lt_replay_fresh_op (links : dom_lt_links) (op : lt_op) : Prop :=
  match op with
  | LtLink child _ => trie_get (dom_lt_key child) (lt_shortcut links) = None
  | LtEval _ => True
  end.

(** The link branch adds only its comparison, increment, and fixed record overhead. *)
Lemma dom_lt_time_replay_link st child parent :
  (T_dom_lt_replay_step st (LtLink child parent) <=
    T_dom_lt_link (dom_lt_replay_selected st) child parent +
      N.T_eqb (replay_index st) (replay_boundary st) +
      N.T_succ (replay_index st) + 16)%N.
Proof.
  destruct st as [before semis fuel boundary index].
  unfold T_dom_lt_replay_step, dom_lt_replay_selected.
  cbn [replay_links replay_semis replay_fuel replay_boundary replay_index].
  destruct (N.eqb index boundary); time_simpl; lia.
Qed.

(** The evaluation branch adds only its comparison, increment, and fixed record overhead. *)
Lemma dom_lt_time_replay_eval st vertex :
  (T_dom_lt_replay_step st (LtEval vertex) <=
    T_dom_lt_eval (replay_fuel st) (replay_semis st) (dom_lt_replay_selected st) vertex +
      N.T_eqb (replay_index st) (replay_boundary st) +
      N.T_succ (replay_index st) + 16)%N.
Proof.
  destruct st as [before semis fuel boundary index].
  unfold T_dom_lt_replay_step, dom_lt_replay_selected.
  cbn [replay_links replay_semis replay_fuel replay_boundary replay_index].
  destruct (N.eqb index boundary); time_simpl; lia.
Qed.

(** The fixed evaluation coefficient is positive independently of the graph and its clocks. *)
Lemma dom_lt_eval_coefficient_positive :
  (1 <= 1024 * (c_loopN + 1) * (PTrieT.c_trie + 1))%N.
Proof.
  change (1 * 1 * 1 <= 1024 * (c_loopN + 1) * (PTrieT.c_trie + 1))%N.
  apply N.mul_le_mono; [|lia].
  apply N.mul_le_mono; lia.
Qed.

(** The evaluation unit contains enough constant slack for the replay bookkeeping. *)
Lemma dom_lt_eval_unit_positive width : (16 <= dom_lt_eval_unit width)%N.
Proof.
  unfold dom_lt_eval_unit.
  change (16 * 1 * 1 * 1 <=
    1024 * (c_loopN + 1) * (PTrieT.c_trie + 1) * N.of_nat (width + 1))%N.
  apply N.mul_le_mono; [|lia].
  apply N.mul_le_mono; [|lia].
  apply N.mul_le_mono; lia.
Qed.

(** One link fits within one evaluation unit at the same key width. *)
Lemma dom_lt_time_link_unit width before child parent :
  N.size_nat child <= width ->
  (T_dom_lt_link before child parent <= dom_lt_eval_unit width)%N.
Proof.
  intro Hwidth. eapply N.le_trans;
    [exact (dom_lt_time_link width before child parent Hwidth)|].
  unfold dom_lt_eval_unit. apply N.mul_le_mono_r. apply N.mul_le_mono_r. lia.
Qed.

(** Two further units pay the comparison, carry, and fixed callback overhead. *)
Lemma dom_lt_replay_charge width level :
  (dom_lt_eval_unit width * N.of_nat (level + 2) + 27 <=
    dom_lt_eval_unit width * N.of_nat (level + 4))%N.
Proof.
  pose proof (dom_lt_eval_unit_positive width) as Hunit.
  rewrite !Nat2N.inj_add, !N.mul_add_distr_l. lia.
Qed.

(** Weighted forest, comparison, and counter credits compose by linear accounting. *)
Lemma dom_lt_replay_step_accounting
    (step_work operation_work comparison_work increment_work
      forest_before forest_after eq_before eq_after carry_before carry_after
      operation_charge total_charge : N) :
  (step_work <= operation_work + comparison_work + increment_work + 16)%N ->
  (operation_work + forest_after <= forest_before + operation_charge)%N ->
  (comparison_work + eq_after <= eq_before + 8)%N ->
  (increment_work + carry_after <= 3 + carry_before)%N ->
  (operation_charge + 27 <= total_charge)%N ->
  (step_work + (forest_after + eq_after + carry_after) <=
    forest_before + eq_before + carry_before + total_charge)%N.
Proof.
  intros Hstep Hoperation Hequality Hcounter Hcharge. lia.
Qed.

(** A reset is charged separately by exposing the selected input forest in this estimate. *)
Lemma dom_lt_time_replay_step bound width st op :
  dom_lt_trie_all (fun value => (value <= N.of_nat bound)%N) (replay_semis st) ->
  (forall value, (value <= N.of_nat bound)%N -> N.size_nat value <= width) ->
  (N.of_nat bound <= replay_fuel st)%N -> N.size_nat (replay_fuel st) <= width + 1 ->
  dom_lt_links_bounded (N.of_nat bound) (dom_lt_replay_selected st) ->
  dom_lt_op_bounded (N.of_nat bound) op ->
  dom_lt_replay_fresh_op (dom_lt_replay_selected st) op ->
  (T_dom_lt_replay_step st op + dom_lt_replay_credit bound width (dom_lt_replay_step st op) <=
    dom_lt_eval_unit width * dom_lt_forest_credit bound (dom_lt_replay_selected st) +
      dom_eqb_credit (replay_boundary st) (replay_index st) +
      dom_counter_credit (replay_index st) +
      dom_lt_eval_unit width * N.of_nat (Nat.log2 bound + 4))%N.
Proof.
  intros Hsemis Hwidth Hfuel Hfuel_width Hlinks Hop Hfresh.
  pose proof (dom_time_eqb_credit (replay_index st) (replay_boundary st)) as Heq.
  pose proof (dom_time_counter_succ (replay_index st)) as Hsucc.
  destruct (dom_lt_replay_fields st op) as [_ [_ [Hboundary Hindex]]].
  unfold dom_lt_replay_credit.
  rewrite Hboundary, Hindex, dom_lt_replay_step_links.
  destruct op as [child parent|vertex].
  - destruct Hop as [Hchild Hparent].
    pose proof (dom_lt_time_link_unit width (dom_lt_replay_selected st) child parent
      (Hwidth child Hchild)) as Hwork.
    pose proof (dom_lt_link_credit bound (dom_lt_replay_selected st) child parent Hfresh)
      as Hcredit.
    assert (Hscaled : (dom_lt_eval_unit width * dom_lt_forest_credit bound
        (dom_lt_link (dom_lt_replay_selected st) child parent) <=
      dom_lt_eval_unit width * dom_lt_forest_credit bound (dom_lt_replay_selected st))%N).
    { now apply N.mul_le_mono_l. }
    assert (Hcharge : (dom_lt_eval_unit width * 1 <=
      dom_lt_eval_unit width * N.of_nat (Nat.log2 bound + 2))%N).
    { apply N.mul_le_mono_l. lia. }
    rewrite N.mul_1_r in Hcharge.
    assert (Hoperation : (T_dom_lt_link (dom_lt_replay_selected st) child parent +
      dom_lt_eval_unit width * dom_lt_forest_credit bound
        (dom_lt_link (dom_lt_replay_selected st) child parent) <=
      dom_lt_eval_unit width * dom_lt_forest_credit bound (dom_lt_replay_selected st) +
        dom_lt_eval_unit width * N.of_nat (Nat.log2 bound + 2))%N).
    { clear -Hwork Hscaled Hcharge. lia. }
    eapply dom_lt_replay_step_accounting with
      (operation_work := T_dom_lt_link (dom_lt_replay_selected st) child parent)
      (comparison_work := N.T_eqb (replay_index st) (replay_boundary st))
      (increment_work := N.T_succ (replay_index st))
      (operation_charge := (dom_lt_eval_unit width * N.of_nat (Nat.log2 bound + 2))%N).
    + exact (dom_lt_time_replay_link st child parent).
    + exact Hoperation.
    + exact Heq.
    + exact Hsucc.
    + exact (dom_lt_replay_charge width (Nat.log2 bound)).
  - assert (Hvertex_fuel : (vertex <= replay_fuel st)%N).
    { eapply N.le_trans; [exact Hop|exact Hfuel]. }
    pose proof (dom_lt_time_eval_credit bound width (replay_fuel st) (replay_semis st)
      (dom_lt_replay_selected st) vertex
      Hsemis Hwidth Hlinks Hop Hvertex_fuel Hfuel_width) as Htime.
    eapply dom_lt_replay_step_accounting with
      (operation_work := T_dom_lt_eval (replay_fuel st) (replay_semis st)
        (dom_lt_replay_selected st) vertex)
      (comparison_work := N.T_eqb (replay_index st) (replay_boundary st))
      (increment_work := N.T_succ (replay_index st))
      (operation_charge := (dom_lt_eval_unit width * N.of_nat (Nat.log2 bound + 2))%N).
    + exact (dom_lt_time_replay_eval st vertex).
    + exact Htime.
    + exact Heq.
    + exact Hsucc.
    + exact (dom_lt_replay_charge width (Nat.log2 bound)).
Qed.

(** A segment retains its numeric bounds, fresh link children, and distance from the reset. *)
Record dom_lt_replay_phase (bound width : nat) (ops : list lt_op) (st : dom_lt_replay) : Prop := {
  dom_lt_replay_phase_semis :
    dom_lt_trie_all (fun value => (value <= N.of_nat bound)%N) (replay_semis st);
  dom_lt_replay_phase_fuel : (N.of_nat bound <= replay_fuel st)%N;
  dom_lt_replay_phase_fuel_width : N.size_nat (replay_fuel st) <= width + 1;
  dom_lt_replay_phase_links : dom_lt_links_bounded (N.of_nat bound) (replay_links st);
  dom_lt_replay_phase_operations : Forall (dom_lt_op_bounded (N.of_nat bound)) ops;
  dom_lt_replay_phase_unique : NoDup (dom_lt_link_children ops);
  dom_lt_replay_phase_fresh : dom_lt_links_fresh (replay_links st) (dom_lt_link_children ops);
  dom_lt_replay_phase_no_reset :
    dom_lt_replay_no_reset (replay_boundary st) (replay_index st) (length ops)
}.

Lemma dom_lt_replay_phase_step bound width op rest st :
  dom_lt_replay_phase bound width (op :: rest) st ->
  dom_lt_replay_phase bound width rest (dom_lt_replay_step st op).
Proof.
  intros [Hsemis Hfuel Hfuel_width Hlinks Hops Hunique Hfresh Hphase].
  inversion Hops as [|head tail Hop Hrest]; subst head tail.
  pose proof (dom_lt_replay_selected_no_reset st (length rest) Hphase) as Hselected.
  destruct (dom_lt_replay_fields st op) as [Hsemis_eq [Hfuel_eq [Hboundary Hindex]]].
  constructor.
  - now rewrite Hsemis_eq.
  - now rewrite Hfuel_eq.
  - now rewrite Hfuel_eq.
  - apply dom_lt_replay_step_range; [now rewrite Hselected|exact Hop].
  - exact Hrest.
  - now apply (dom_lt_link_children_tail_unique op rest).
  - apply dom_lt_replay_step_fresh; [exact Hunique|now rewrite Hselected].
  - rewrite Hboundary, Hindex. now apply dom_lt_replay_no_reset_tail.
Qed.

Lemma dom_lt_replay_phase_time bound width ops st :
  (forall value, (value <= N.of_nat bound)%N -> N.size_nat value <= width) ->
  dom_lt_replay_phase bound width ops st ->
  dom_lt_replay_phase bound width [] (fold_left dom_lt_replay_step ops st) /\
    (List.T_fold_left dom_lt_replay_step T_dom_lt_replay_step ops st +
      dom_lt_replay_credit bound width (fold_left dom_lt_replay_step ops st) <=
    dom_lt_replay_credit bound width st +
      (dom_lt_eval_unit width * N.of_nat (Nat.log2 bound + 4) + 1) *
        N.of_nat (length ops) + 1)%N.
Proof.
  intros Hwidth Hphase.
  apply (dom_lt_fold_credit dom_lt_replay_step T_dom_lt_replay_step
    (dom_lt_replay_phase bound width) (dom_lt_replay_credit bound width)
    (dom_lt_eval_unit width * N.of_nat (Nat.log2 bound + 4))%N ops).
  - intros op rest before Hbefore. now apply dom_lt_replay_phase_step.
  - intros op rest before Hbefore.
    destruct Hbefore as [Hsemis Hfuel Hfuel_width Hlinks Hops Hunique Hfresh Hphase_before].
    inversion Hops as [|head tail Hop Hrest]; subst head tail.
    pose proof (dom_lt_replay_selected_no_reset before (length rest) Hphase_before) as Hselected.
    assert (Hnew : dom_lt_replay_fresh_op (dom_lt_replay_selected before) op).
    { rewrite Hselected. destruct op; [apply Hfresh; now left|exact I]. }
    pose proof (dom_lt_time_replay_step bound width before op Hsemis Hwidth Hfuel Hfuel_width
      ltac:(now rewrite Hselected) Hop Hnew) as Htime.
    rewrite Hselected in Htime. exact Htime.
  - exact Hphase.
Qed.

(** The first bucket operation resets the forest once; its counter credits remain continuous. *)
Lemma dom_lt_replay_reset_time bound width ops st :
  (forall value, (value <= N.of_nat bound)%N -> N.size_nat value <= width) ->
  dom_lt_trie_all (fun value => (value <= N.of_nat bound)%N) (replay_semis st) ->
  (N.of_nat bound <= replay_fuel st)%N -> N.size_nat (replay_fuel st) <= width + 1 ->
  Forall (dom_lt_op_bounded (N.of_nat bound)) ops -> NoDup (dom_lt_link_children ops) ->
  replay_index st = replay_boundary st ->
  (List.T_fold_left dom_lt_replay_step T_dom_lt_replay_step ops st +
      dom_lt_replay_credit bound width (fold_left dom_lt_replay_step ops st) <=
    dom_lt_eval_unit width * N.of_nat ((bound + 1) * Nat.log2 bound) +
      dom_eqb_credit (replay_boundary st) (replay_index st) +
      dom_counter_credit (replay_index st) +
      (dom_lt_eval_unit width * N.of_nat (Nat.log2 bound + 4) + 1) *
        N.of_nat (length ops) + 1)%N.
Proof.
  intros Hwidth Hsemis Hfuel Hfuel_width Hops Hunique Hboundary.
  destruct ops as [|op rest].
  - pose proof (dom_lt_forest_credit_bound bound (replay_links st)) as Hcredit.
    assert (Hscaled : (dom_lt_eval_unit width * dom_lt_forest_credit bound (replay_links st) <=
      dom_lt_eval_unit width * N.of_nat ((bound + 1) * Nat.log2 bound))%N).
    { now apply N.mul_le_mono_l. }
    time_unfold @List.T_fold_left. cbn [fold_left length]. unfold dom_lt_replay_credit.
    clear -Hscaled. lia.
  - assert (Hselected : dom_lt_replay_selected st = DomLtLinks Empty Empty []).
    { unfold dom_lt_replay_selected. now rewrite Hboundary, N.eqb_refl. }
    inversion Hops as [|head tail Hop Hrest]; subst head tail.
    assert (Hnew : dom_lt_replay_fresh_op (dom_lt_replay_selected st) op).
    { rewrite Hselected. destruct op; [apply PTrie.get_empty|exact I]. }
    pose proof (dom_lt_time_replay_step bound width st op Hsemis Hwidth Hfuel Hfuel_width
      ltac:(rewrite Hselected; apply dom_lt_empty_bounded) Hop Hnew) as Hhead.
    rewrite Hselected, dom_lt_empty_credit in Hhead.
    destruct (dom_lt_replay_fields st op) as [Hsemis_eq [Hfuel_eq [Hboundary_eq Hindex]]].
    assert (Hafter : dom_lt_replay_phase bound width rest (dom_lt_replay_step st op)).
    { constructor.
      - now rewrite Hsemis_eq.
      - now rewrite Hfuel_eq.
      - now rewrite Hfuel_eq.
      - apply dom_lt_replay_step_range;
          [rewrite Hselected; apply dom_lt_empty_bounded|exact Hop].
      - exact Hrest.
      - now apply (dom_lt_link_children_tail_unique op rest).
      - apply dom_lt_replay_step_fresh; [exact Hunique|].
        rewrite Hselected. apply dom_lt_empty_fresh.
      - rewrite Hboundary_eq, Hindex. unfold dom_lt_replay_no_reset. left. lia. }
    pose proof (proj2 (dom_lt_replay_phase_time bound width rest
      (dom_lt_replay_step st op) Hwidth Hafter)) as Htail.
    time_unfold @List.T_fold_left. cbn [fold_left length].
    fold (List.T_fold_left dom_lt_replay_step T_dom_lt_replay_step).
    rewrite Nat2N.inj_succ, N.mul_succ_r.
    clear -Hhead Htail. lia.
Qed.

(** Exactly two forest-capacity charges suffice for the two logged phases. *)
Lemma dom_lt_replay_two_phases bound width semis fuel first second :
  (forall value, (value <= N.of_nat bound)%N -> N.size_nat value <= width) ->
  dom_lt_trie_all (fun value => (value <= N.of_nat bound)%N) semis ->
  (N.of_nat bound <= fuel)%N -> N.size_nat fuel <= width + 1 ->
  Forall (dom_lt_op_bounded (N.of_nat bound)) first ->
  Forall (dom_lt_op_bounded (N.of_nat bound)) second ->
  NoDup (dom_lt_link_children first) -> NoDup (dom_lt_link_children second) ->
  let initial := DomLtReplay (DomLtLinks Empty Empty []) semis fuel
    (N.of_nat (length first)) 0%N in
  (List.T_fold_left dom_lt_replay_step T_dom_lt_replay_step (first ++ second) initial <=
    2 * dom_lt_eval_unit width * N.of_nat ((bound + 1) * Nat.log2 bound) +
      dom_eqb_credit (N.of_nat (length first)) 0 +
      (dom_lt_eval_unit width * N.of_nat (Nat.log2 bound + 4) + 1) *
        N.of_nat (length (first ++ second)) + 1)%N.
Proof.
  intros Hwidth Hsemis Hfuel Hfuel_width Hfirst Hsecond Hfirst_unique Hsecond_unique initial.
  assert (Hinitial : dom_lt_replay_phase bound width first initial).
  { constructor; try assumption.
    - apply dom_lt_empty_bounded.
    - apply dom_lt_empty_fresh.
    - unfold initial, dom_lt_replay_no_reset. right.
      cbn [replay_index replay_boundary]. apply N.le_refl. }
  destruct (dom_lt_replay_phase_time bound width first initial Hwidth Hinitial)
    as [Hmiddle Hfirst_time].
  set (middle := fold_left dom_lt_replay_step first initial) in *.
  destruct Hmiddle as [Hmiddle_semis Hmiddle_fuel Hmiddle_width Hmiddle_links
    Hmiddle_ops Hmiddle_unique Hmiddle_fresh Hmiddle_phase].
  assert (Hmiddle_index : replay_index middle = N.of_nat (length first)).
  { unfold middle. change (replay_index (dom_lt_run_ops first initial) =
      N.of_nat (length first)).
    rewrite dom_lt_replay_index. unfold initial. cbn [replay_index]. reflexivity. }
  assert (Hmiddle_boundary : replay_boundary middle = N.of_nat (length first)).
  { unfold middle. rewrite (proj2 (proj2 (dom_lt_replay_fold_fields first initial))).
    reflexivity. }
  assert (Hreset : replay_index middle = replay_boundary middle).
  { now rewrite Hmiddle_index, Hmiddle_boundary. }
  pose proof (dom_lt_replay_reset_time bound width second middle Hwidth Hmiddle_semis
    Hmiddle_fuel Hmiddle_width Hsecond Hsecond_unique Hreset) as Hsecond_time.
  pose proof (dom_lt_fold_clock_app dom_lt_replay_step T_dom_lt_replay_step
    first second initial) as Hjoin. fold middle in Hjoin.
  unfold dom_lt_replay_credit in Hfirst_time.
  unfold initial in Hfirst_time.
  cbn [replay_links replay_boundary replay_index dom_counter_credit] in Hfirst_time.
  rewrite dom_lt_empty_credit in Hfirst_time.
  fold initial in Hfirst_time. clearbody middle.
  rewrite length_app, Nat2N.inj_add, N.mul_add_distr_l.
  replace (2 * dom_lt_eval_unit width * N.of_nat ((bound + 1) * Nat.log2 bound))%N with
    (dom_lt_eval_unit width * N.of_nat ((bound + 1) * Nat.log2 bound) +
      dom_lt_eval_unit width * N.of_nat ((bound + 1) * Nat.log2 bound))%N by ring.
  clear -Hfirst_time Hsecond_time Hjoin. lia.
Qed.

(** The two phase capacities and the linear counter reserve fit the published product budget. *)
Lemma dom_lt_replay_budget_coefficient coefficient width discovered vertices
    level maximum ops prefix :
  (1 <= coefficient)%N -> discovered <= vertices -> level <= maximum -> prefix <= ops ->
  (2 * (coefficient * N.of_nat (width + 1)) * N.of_nat ((discovered + 1) * level) +
      (2 * N.of_nat prefix + 1) +
      (coefficient * N.of_nat (width + 1) * N.of_nat (level + 4) + 1) * N.of_nat ops + 3 <=
    32 * coefficient * N.of_nat ((ops + vertices + 1) * (maximum + 1) * (width + 1)))%N.
Proof.
  intros Hcoefficient Hvertices Hlevel Hprefix.
  set (budget := (ops + vertices + 1) * (maximum + 1)).
  set (weighted := 2 * (discovered + 1) * level + (level + 4) * ops).
  set (reserve := 2 * prefix + ops + 4).
  assert (Hweighted : weighted <= 4 * budget) by (unfold weighted, budget; nia).
  assert (Hreserve : reserve <= 4 * budget) by (unfold reserve, budget; nia).
  set (unit := (coefficient * N.of_nat (width + 1))%N).
  assert (Hpositive : (1 <= unit)%N).
  { unfold unit. clear -Hcoefficient.
    change (1 * 1 <= coefficient * N.of_nat (width + 1))%N.
    apply N.mul_le_mono; [exact Hcoefficient|lia]. }
  assert (HweightedN : (N.of_nat weighted <= 4 * N.of_nat budget)%N) by lia.
  assert (HreserveN : (N.of_nat reserve <= 4 * N.of_nat budget)%N) by lia.
  assert (Hscaled : (unit * N.of_nat weighted + N.of_nat reserve <=
    32 * unit * N.of_nat budget)%N).
  { assert (Hweighted_scaled : (unit * N.of_nat weighted <=
        unit * (4 * N.of_nat budget))%N) by now apply N.mul_le_mono_l.
    assert (Hreserve_scaled : (N.of_nat reserve <= unit * (4 * N.of_nat budget))%N).
    { eapply N.le_trans; [exact HreserveN|].
      replace (4 * N.of_nat budget)%N with (1 * (4 * N.of_nat budget))%N at 1 by ring.
      now apply N.mul_le_mono_r. }
    eapply N.le_trans with
      (unit * (4 * N.of_nat budget) + unit * (4 * N.of_nat budget))%N.
    - now apply N.add_le_mono.
    - replace (unit * (4 * N.of_nat budget) + unit * (4 * N.of_nat budget))%N with
        (8 * (unit * N.of_nat budget))%N by ring.
      replace (32 * unit * N.of_nat budget)%N with
        (32 * (unit * N.of_nat budget))%N by ring.
      apply N.mul_le_mono_r. lia. }
  unfold unit, weighted, reserve, budget in Hscaled.
  rewrite !Nat2N.inj_add, !Nat2N.inj_mul, !Nat2N.inj_add in Hscaled |- *.
  clear -Hscaled. nia.
Qed.

(** The final wrapper uses two calls beyond the fold and its three aggregate reserves. *)
Lemma dom_lt_replay_finish_budget
    (work capacity comparison phase boundary_width prefix target : N) :
  (work <= capacity + comparison + phase + 1)%N ->
  (comparison <= 2 * boundary_width + 1)%N ->
  (boundary_width <= prefix)%N ->
  (capacity + (2 * prefix + 1) + phase + 3 <= target)%N ->
  (work + 2 <= target)%N.
Proof.
  intros Hwork Hcomparison Hwidth Hbudget. lia.
Qed.

(** The actual producer replay admits duplicate input vertices and edge occurrences. *)
Lemma dom_lt_replay_time g r :
  (T_dom_lt_run_ops (dom_lt_ops g r) (dom_lt_replay_initial g r) + 1 <=
    (32 * 1024 * (c_loopN + 1) * (PTrieT.c_trie + 1)) *
      N.of_nat ((length (dom_lt_ops g r) + graph_n (base g) + 1) *
        (Nat.log2 (graph_n (base g)) + 1) * (graph_width (base g) + 1)))%N.
Proof.
  set (discovered := dom_lt_dfs g r).
  set (bound := length discovered).
  set (width := graph_width (base g)).
  set (numeric := dom_lt_numeric_of g r).
  set (semi := dom_lt_semidominators numeric).
  set (bucket := dom_lt_buckets numeric (lt_semis semi)).
  set (first := rev (lt_operations (lt_semi_links semi))).
  set (second := rev (lt_operations (lt_bucket_links bucket))).
  assert (Hops : dom_lt_ops g r = first ++ second).
  { unfold dom_lt_ops, dom_lt_pipeline. fold numeric. fold semi. fold bucket.
    cbn [result_semi result_bucket].
    change (rev_append (lt_operations (lt_semi_links semi))
      (rev_append (lt_operations (lt_bucket_links bucket)) []) = first ++ second).
    now rewrite !rev_append_rev, app_nil_r. }
  assert (Hinitial : dom_lt_replay_initial g r =
    DomLtReplay (DomLtLinks Empty Empty []) (lt_semis semi) (lt_numeric_limit numeric)
      (N.of_nat (length first)) 0%N).
  { unfold dom_lt_replay_initial, dom_lt_pipeline. fold numeric. fold semi. fold bucket.
    cbn [result_semi result_numeric].
    unfold first. rewrite length_rev. reflexivity. }
  destruct (dom_lt_dfs_inventory g r) as [Hunique [Hlisted [Hvertices Hedges]]].
  fold discovered in Hunique, Hlisted, Hvertices, Hedges.
  assert (Hkey_width : forall vertex, In vertex discovered -> Pos.size_nat vertex <= width).
  { intros vertex Hin. unfold width. apply dom_listed_key_width. now apply Hlisted. }
  assert (Hwidth : forall value, (value <= N.of_nat bound)%N -> N.size_nat value <= width).
  { intros value Hvalue. now apply (dom_distinct_value_width discovered width). }
  pose proof (dom_lt_numeric_of_ranges g r) as Hranges. fold numeric discovered bound in Hranges.
  pose proof (dom_lt_semidominators_range (N.of_nat bound) numeric Hranges) as Hsemis.
  change (dom_lt_semi_bounded (N.of_nat bound) semi) in Hsemis.
  destruct Hsemis as [Hsemis [Hminimizers Hsemi_links]].
  pose proof (dom_lt_numeric_limit_count g r) as Hlimit. fold numeric discovered bound in Hlimit.
  assert (Hfuel : (N.of_nat bound <= lt_numeric_limit numeric)%N).
  { rewrite Hlimit, Nat2N.inj_add. apply N.le_add_r. }
  assert (Hfuel_width : N.size_nat (lt_numeric_limit numeric) <= width + 1).
  { apply (dom_distinct_twice_width discovered width); [exact Hunique|exact Hkey_width|].
    rewrite Hlimit. unfold bound. rewrite Nat2N.inj_add.
    clearbody discovered. clear -discovered. lia. }
  pose proof (dom_lt_semidominators_op_range (N.of_nat bound) numeric Hranges) as Hfirst.
  pose proof (dom_lt_buckets_op_range (N.of_nat bound) numeric (lt_semis semi) Hranges)
    as Hsecond.
  fold semi in Hfirst. fold bucket in Hsecond.
  assert (Hfirst_range : Forall (dom_lt_op_bounded (N.of_nat bound)) first).
  { unfold first. now apply Forall_rev. }
  assert (Hsecond_range : Forall (dom_lt_op_bounded (N.of_nat bound)) second).
  { unfold second. now apply Forall_rev. }
  pose proof (dom_lt_numeric_order_unique g r) as Horder. fold numeric in Horder.
  assert (Hfirst_unique : NoDup (dom_lt_link_children first)).
  { unfold first. rewrite dom_lt_link_children_rev. apply NoDup_rev.
    now apply dom_lt_semidominators_link_unique. }
  assert (Hsecond_unique : NoDup (dom_lt_link_children second)).
  { unfold second. rewrite dom_lt_link_children_rev. apply NoDup_rev.
    now apply dom_lt_buckets_link_unique. }
  pose proof (dom_lt_replay_two_phases bound width (lt_semis semi) (lt_numeric_limit numeric)
    first second Hwidth Hsemis Hfuel Hfuel_width Hfirst_range Hsecond_range
    Hfirst_unique Hsecond_unique) as Htime.
  cbn zeta in Htime. rewrite <- Hinitial, <- Hops in Htime.
  pose proof (dom_eqb_credit_initial (N.of_nat (length first))) as Hcounter.
  pose proof (dom_size_value (N.of_nat (length first))) as Hcounter_width.
  assert (Hprefix : length first <= length (dom_lt_ops g r)).
  { rewrite Hops, length_app. apply Nat.le_add_r. }
  pose proof (Nat.log2_le_mono bound (graph_n (base g)) Hvertices) as Hlog.
  pose proof (dom_lt_replay_budget_coefficient
    (1024 * (c_loopN + 1) * (PTrieT.c_trie + 1))%N width bound (graph_n (base g))
    (Nat.log2 bound) (Nat.log2 (graph_n (base g))) (length (dom_lt_ops g r)) (length first)
    dom_lt_eval_coefficient_positive Hvertices Hlog Hprefix) as Hbudget.
  unfold dom_lt_eval_unit in Htime.
  pose proof (dom_lt_replay_finish_budget _ _ _ _ _ _ _
    Htime Hcounter Hcounter_width Hbudget) as Hcomplete.
  unfold T_dom_lt_run_ops. time_simpl.
  change (List.T_fold_left dom_lt_replay_step
    (fun st op => T_dom_lt_replay_step st op) (dom_lt_ops g r) (dom_lt_replay_initial g r))
    with (List.T_fold_left dom_lt_replay_step T_dom_lt_replay_step
      (dom_lt_ops g r) (dom_lt_replay_initial g r)).
  fold width.
  replace (32 * 1024 * (c_loopN + 1) * (PTrieT.c_trie + 1))%N with
    (32 * (1024 * (c_loopN + 1) * (PTrieT.c_trie + 1)))%N by ring.
  clear -Hcomplete. lia.
Qed.

(** * Passing the order-body budget to the public graph dimensions *)

(** Quadratic numeric payloads need at most five times the original key-width factor. *)
Lemma dom_order_graph_product discovered predecessors vertices edges width :
  discovered <= vertices -> predecessors <= edges ->
  (discovered + predecessors + 1) * (Nat.log2 discovered + 1) * (2 * width + 4 + 1) <=
    5 * ((vertices + edges + 1) * (Nat.log2 vertices + 1) * (width + 1)).
Proof.
  intros Hvertices Hedges.
  pose proof (Nat.log2_le_mono discovered vertices Hvertices) as Hlog.
  replace (5 * ((vertices + edges + 1) * (Nat.log2 vertices + 1) * (width + 1))) with
    (((vertices + edges + 1) * (Nat.log2 vertices + 1)) * (5 * (width + 1))) by ring.
  apply Nat.mul_le_mono.
  - apply Nat.mul_le_mono; lia.
  - lia.
Qed.

(** The recorded operations and one forest universe fit four graph-size allowances. *)
Lemma dom_order_replay_product operations vertices edges levels width :
  operations <= 2 * (vertices + edges) + 1 ->
  (operations + vertices + 1) * levels * width <=
    4 * ((vertices + edges + 1) * levels * width).
Proof.
  intro Hoperations.
  replace (4 * ((vertices + edges + 1) * levels * width)) with
    ((4 * (vertices + edges + 1)) * levels * width) by ring.
  apply Nat.mul_le_mono_r. apply Nat.mul_le_mono_r. lia.
Qed.

(** The public wrapper pays one fresh producer and one completed order body. *)
Lemma dom_order_public_sum_budget (budget body_coefficient semi_coefficient replay_coefficient
    body_clock semi_clock replay_clock total_clock : N) :
  (1 <= budget)%N ->
  (body_clock <= 5 * body_coefficient * budget)%N ->
  (semi_clock <= semi_coefficient * budget + replay_clock)%N ->
  (replay_clock <= 4 * replay_coefficient * budget)%N ->
  (total_clock <= semi_clock + body_clock + 1)%N ->
  (total_clock <= (5 * body_coefficient + semi_coefficient +
    4 * replay_coefficient + 1) * budget)%N.
Proof.
  intros Hpositive Hbody Hsemi Hreplay Htotal.
  replace ((5 * body_coefficient + semi_coefficient + 4 * replay_coefficient + 1) * budget)%N
    with (5 * body_coefficient * budget + semi_coefficient * budget +
      4 * replay_coefficient * budget + budget)%N by ring.
  lia.
Qed.

(** The two raw producer clock reserves pay both wrappers of the public order alias. *)
Lemma dom_order_graph_wrapper g r body_coefficient replay_coefficient :
  prepared_ok g ->
  (T_dom_order_of_result (dom_lt_pipeline g r) <= body_coefficient *
    N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
      (Nat.log2 (graph_n (base g)) + 1) * (graph_width (base g) + 1)))%N ->
  (T_dom_lt_run_ops (dom_lt_ops g r) (dom_lt_replay_initial g r) + 1 <= replay_coefficient *
    N.of_nat ((length (dom_lt_ops g r) + graph_n (base g) + 1) *
      (Nat.log2 (graph_n (base g)) + 1) * (graph_width (base g) + 1)))%N ->
  (T_dom_build_order g r + 1 <=
    (body_coefficient + dom_lt_semi_coefficient + 4 * replay_coefficient) *
      N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
        (Nat.log2 (graph_n (base g)) + 1) * (graph_width (base g) + 1)))%N.
Proof.
  intros Hprepared Hbody Hreplay.
  set (budget := N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
    (Nat.log2 (graph_n (base g)) + 1) * (graph_width (base g) + 1))) in *.
  assert (Hlinear : (N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
    (graph_width (base g) + 1)) <= budget)%N).
  { unfold budget. apply time_of_nat_le. apply Nat.mul_le_mono_r.
    replace (graph_n (base g) + graph_e (base g) + 1) with
      ((graph_n (base g) + graph_e (base g) + 1) * 1) at 1 by lia.
    apply Nat.mul_le_mono_l. lia. }
  assert (Hoperations : (N.of_nat ((length (dom_lt_ops g r) + graph_n (base g) + 1) *
    (Nat.log2 (graph_n (base g)) + 1) * (graph_width (base g) + 1)) <= 4 * budget)%N).
  { unfold budget. replace (4 * N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
        (Nat.log2 (graph_n (base g)) + 1) * (graph_width (base g) + 1)))%N
      with (N.of_nat (4 * ((graph_n (base g) + graph_e (base g) + 1) *
        (Nat.log2 (graph_n (base g)) + 1) * (graph_width (base g) + 1)))) by
      (rewrite Nat2N.inj_mul; reflexivity).
    apply time_of_nat_le, dom_order_replay_product. now apply dom_lt_operations_length. }
  pose proof (dom_lt_parents_replay_clock g r Hprepared) as Hsemi.
  pose proof (dom_lt_pipeline_parent_clock g r) as Hpipeline.
  assert (Hsemi_paid : (T_dom_lt_parents g r + 1 <= dom_lt_semi_coefficient * budget +
    T_dom_lt_run_ops (dom_lt_ops g r) (dom_lt_replay_initial g r))%N).
  { eapply N.le_trans; [exact Hsemi|]. apply N.add_le_mono_r.
    now apply N.mul_le_mono_l. }
  assert (Hreplay_paid : (T_dom_lt_run_ops (dom_lt_ops g r) (dom_lt_replay_initial g r) + 1 <=
    4 * replay_coefficient * budget)%N).
  { eapply N.le_trans; [exact Hreplay|].
    replace (4 * replay_coefficient * budget)%N with (replay_coefficient * (4 * budget))%N by ring.
    now apply N.mul_le_mono_l. }
  unfold T_dom_build_order. time_simpl.
  replace ((body_coefficient + dom_lt_semi_coefficient + 4 * replay_coefficient) * budget)%N with
    (body_coefficient * budget + dom_lt_semi_coefficient * budget +
      4 * replay_coefficient * budget)%N by ring.
  clear -Hpipeline Hsemi_paid Hreplay_paid Hbody. lia.
Qed.

(** * Primitive order keys and child-row clocks *)

(** Reading a child row costs only the numeric key's width. *)
Lemma dom_order_row_clock rows vertex :
  (T_dom_order_row rows vertex <= 8 * N.of_nat (N.size_nat vertex + 1))%N.
Proof.
  pose proof (dom_lt_time_key vertex) as Hkey.
  pose proof (dom_lt_key_width vertex) as Hwidth.
  unfold T_dom_order_row. PTrieT.trie_get_le.
  destruct (trie_get (dom_lt_key vertex) rows); time_simpl;
    rewrite !Nat2N.inj_add in *; lia.
Qed.

(** Reading a number costs only the numeric key's width. *)
Lemma dom_order_number_clock rows vertex :
  (T_dom_order_number rows vertex <= 8 * N.of_nat (N.size_nat vertex + 1))%N.
Proof.
  pose proof (dom_lt_time_key vertex) as Hkey.
  pose proof (dom_lt_key_width vertex) as Hwidth.
  unfold T_dom_order_number. PTrieT.trie_get_le.
  destruct (trie_get (dom_lt_key vertex) rows); time_simpl;
    rewrite !Nat2N.inj_add in *; lia.
Qed.

(** Reading an activity flag costs only the numeric key's width. *)
Lemma dom_order_active_clock active vertex :
  (T_dom_order_active active vertex <= 8 * N.of_nat (N.size_nat vertex + 1))%N.
Proof.
  pose proof (dom_lt_time_key vertex) as Hkey.
  pose proof (dom_lt_key_width vertex) as Hwidth.
  unfold T_dom_order_active. PTrieT.trie_get_le.
  destruct (trie_get (dom_lt_key vertex) active) as [[|]|]; time_simpl;
    rewrite !Nat2N.inj_add in *; lia.
Qed.

(** Adding a child row touches the vertex key and one bounded parent key. *)
Lemma dom_order_child_add_clock width parents rows vertex :
  N.size_nat vertex <= width ->
  dom_lt_trie_all (fun parent => N.size_nat parent <= width) parents ->
  (T_dom_order_child_add parents rows vertex <=
    64 * (PTrieT.c_trie + 1) * N.of_nat (width + 1))%N.
Proof.
  intros Hvertex Hparents.
  pose proof (dom_lt_time_key vertex) as Hkey.
  pose proof (dom_lt_key_width vertex) as Hkey_width.
  unfold T_dom_order_child_add. time_simpl. PTrieT.trie_get_le.
  destruct (trie_get (dom_lt_key vertex) parents) as [parent|] eqn:Hparent.
  - pose proof (Hparents (dom_lt_key vertex) parent Hparent) as Hparent_width.
    change (N.size_nat parent <= width) in Hparent_width.
    pose proof (dom_lt_time_key parent) as Hparent_key.
    pose proof (dom_lt_key_width parent) as Hparent_key_width.
    pose proof (dom_order_row_clock rows parent) as Hrow.
    pose proof (PTrieT.T_set_le (list N) (dom_lt_key parent)
      (vertex :: dom_order_row rows parent) rows) as Hset.
    change (PTrieCode.T_set (dom_lt_key parent) (vertex :: dom_order_row rows parent) rows <=
      PTrieT.c_trie * N.of_nat (Pos.size_nat (dom_lt_key parent) + 1))%N in Hset.
    time_simpl. rewrite !Nat2N.inj_add in *.
    clear -Hvertex Hkey Hkey_width Hparent_width Hparent_key Hparent_key_width Hrow Hset.
    PTrieT.trie_get_le. nia.
  - time_simpl. rewrite !Nat2N.inj_add in *.
    clear -Hvertex Hkey Hkey_width. PTrieT.trie_get_le. nia.
Qed.

(** Building child rows pays a bounded update once for each supplied input vertex. *)
Lemma dom_order_child_fold_clock width parents rows order :
  Forall (fun vertex => N.size_nat vertex <= width) order ->
  dom_lt_trie_all (fun parent => N.size_nat parent <= width) parents ->
  (List.T_fold_left (dom_order_child_add parents) (T_dom_order_child_add parents) order rows <=
    128 * (PTrieT.c_trie + 1) * N.of_nat ((length order + 1) * (width + 1)))%N.
Proof.
  intros Horder Hparents.
  pose proof (dom_time_fold_credit (dom_order_child_add parents) (T_dom_order_child_add parents)
    (fun _ => 0%N) (64 * (PTrieT.c_trie + 1) * N.of_nat (width + 1))%N order rows) as Hfold.
  specialize (Hfold ltac:(intros vertex Hin current; cbn beta; rewrite !N.add_0_r;
    apply dom_order_child_add_clock; [now apply Forall_forall with (x := vertex) in Horder|exact Hparents])).
  cbn beta in Hfold. rewrite !N.add_0_r in Hfold.
  set (unit := (64 * (PTrieT.c_trie + 1) * N.of_nat (width + 1))%N) in *.
  assert (Hunit : (1 <= unit)%N).
  { unfold unit. clear -width.
    change (1 * 1 <= (64 * (PTrieT.c_trie + 1)) * N.of_nat (width + 1))%N.
    apply N.mul_le_mono; [lia|rewrite Nat2N.inj_add; lia]. }
  replace (128 * (PTrieT.c_trie + 1) * N.of_nat ((length order + 1) * (width + 1)))%N
    with (2 * unit * (N.of_nat (length order) + 1))%N by
    (unfold unit; rewrite Nat2N.inj_mul, (Nat2N.inj_add (length order) 1);
     change (N.of_nat 1) with 1%N; ring).
  change (List.T_fold_left (dom_order_child_add parents) (T_dom_order_child_add parents)
    order rows <= (unit + 1) * N.of_nat (length order) + 1)%N in Hfold.
  clearbody unit. eapply N.le_trans; [exact Hfold|].
  replace (2 * unit * (N.of_nat (length order) + 1))%N with
    ((2 * unit) * N.of_nat (length order) + 2 * unit)%N by ring.
  apply N.add_le_mono; [apply N.mul_le_mono_r; lia|lia].
Qed.

(** Sorting child rows preserves their raw total mass over any distinct key universe. *)
Lemma dom_order_sorted_rows_mass keys order parents positions :
  NoDup keys -> dom_lt_row_mass keys (dom_order_sorted_rows order parents positions) <= length order.
Proof.
  intro Hunique. unfold dom_order_sorted_rows.
  rewrite dom_order_row_mass_map_length; [now apply dom_order_children_mass|].
  intro row. apply dom_order_sort_length.
Qed.

(** Sorted child rows keep every original bounded numeric child. *)
Lemma dom_order_sorted_rows_forall (P : N -> Prop) order parents positions :
  Forall P order -> dom_lt_trie_all (Forall P) (dom_order_sorted_rows order parents positions).
Proof.
  intros Horder key row Hget. unfold dom_order_sorted_rows in Hget.
  rewrite PTrie.get_map in Hget.
  change (PTrie.get key (fold_left (dom_order_child_add parents) order Empty))
    with (trie_get key (fold_left (dom_order_child_add parents) order Empty)) in Hget.
  destruct (trie_get key (fold_left (dom_order_child_add parents) order Empty))
    as [before|] eqn:Hbefore; [|discriminate Hget].
  injection Hget as <-. apply dom_order_sort_forall.
  eapply dom_order_child_fold_forall; [exact Horder|apply dom_lt_trie_all_empty|exact Hbefore].
Qed.

(** * Row-sensitive sorting callbacks *)

(** Naming the existing sorting callback exposes its generated clock without changing the row map. *)
Definition dom_order_sort_row (positions : ptrie (N * N)) (row : list N) : list N :=
  dom_order_sort (N.size_nat (N.of_nat (length row))) positions row.
TimeFun dom_order_sort_row.

(** Measuring a row adds linear work to its logarithmic number of sorting levels. *)
Lemma dom_order_sort_row_budget coefficient width levels size depth setup sort_clock :
  (1 <= width)%N -> (1 <= levels)%N -> (depth <= 2 * levels)%N ->
  (setup <= 8 * size + 8)%N ->
  (sort_clock <= coefficient * width * (depth * size) + 1)%N ->
  (setup + sort_clock <= 16 * (coefficient + 1) * (levels * width) * size + 16)%N.
Proof.
  intros Hwidth Hlevels Hdepth Hsetup Hsort.
  set (cells := ((levels * width) * size)%N).
  assert (Hunit : (1 <= levels * width)%N).
  { change (1 * 1 <= levels * width)%N. now apply N.mul_le_mono. }
  assert (Hcells : (size <= cells)%N).
  { unfold cells. replace size with (1 * size)%N at 1 by ring.
    now apply N.mul_le_mono_r. }
  assert (Hsort_cells : (sort_clock <= (2 * coefficient) * cells + 1)%N).
  { eapply N.le_trans; [exact Hsort|]. apply N.add_le_mono_r.
    replace ((2 * coefficient) * cells)%N with
      (coefficient * width * ((2 * levels) * size))%N by (unfold cells; ring).
    apply N.mul_le_mono_l. now apply N.mul_le_mono_r. }
  replace (16 * (coefficient + 1) * (levels * width) * size + 16)%N with
    (16 * (coefficient + 1) * cells + 16)%N by (unfold cells; ring).
  eapply N.le_trans with ((8 + 2 * coefficient) * cells + 16)%N.
  - replace ((8 + 2 * coefficient) * cells)%N with
      (8 * cells + (2 * coefficient) * cells)%N by ring. lia.
  - apply N.add_le_mono_r. apply N.mul_le_mono_r. lia.
Qed.

Definition dom_order_sort_row_coefficient : N := (16 * (dom_order_sort_coefficient + 1))%N.

(** The sorting callback has a per-cell logarithmic charge and a constant binding charge. *)
Lemma dom_order_sort_row_time width bound positions row :
  length row <= bound ->
  Forall (dom_order_merge_operand width positions) row ->
  (T_dom_order_sort_row positions row <= dom_order_sort_row_coefficient *
    N.of_nat ((Nat.log2 bound + 1) * (width + 1)) * N.of_nat (length row) + 16)%N.
Proof.
  intros Hlength Hrow.
  pose proof (dom_order_value_log_width (N.of_nat (length row)) bound
    (time_of_nat_le _ _ Hlength)) as Hfuel.
  pose proof (dom_order_sort_time width (N.size_nat (N.of_nat (length row)))
    positions row Hrow) as Hsort.
  pose proof (Datatypes.T_length_le row) as Hmeasure.
  pose proof (dom_time_of_nat (length row)) as Hconvert.
  pose proof (N.T_size_nat_le (N.of_nat (length row))) as Hbits.
  pose proof (dom_size_value (N.of_nat (length row))) as Hsize.
  assert (Hraw : (T_dom_order_sort_row positions row <=
    (4 + Datatypes.T_length row + TimeHelpers.N.T_of_nat (length row) +
      N.T_size_nat (N.of_nat (length row))) +
    T_dom_order_sort (N.size_nat (N.of_nat (length row))) positions row)%N).
  { time_unfold T_dom_order_sort_row. time_simpl. lia. }
  eapply N.le_trans; [exact Hraw|].
  unfold dom_order_sort_row_coefficient. rewrite Nat2N.inj_mul.
  eapply dom_order_sort_row_budget with
    (depth := N.of_nat (N.size_nat (N.of_nat (length row)) + 1)).
  - clear -width. rewrite Nat2N.inj_add. lia.
  - clear -bound. rewrite Nat2N.inj_add. lia.
  - clear -Hfuel. rewrite !Nat2N.inj_add. lia.
  - clear -Hmeasure Hconvert Hbits Hsize. lia.
  - rewrite Nat2N.inj_mul in Hsort. exact Hsort.
Qed.

(** Summing callback bounds keeps cell work separate from the number of bindings. *)
Lemma dom_order_sum_cells {A : Type} (cost : A -> N) (cells : A -> nat) items unit allowance :
  (forall item, In item items -> (cost item <= unit * N.of_nat (cells item) + allowance)%N) ->
  (fold_right N.add 0 (map cost items) <=
    unit * N.of_nat (fold_right (fun item total => (cells item + total)%nat) 0%nat items) +
      allowance * N.of_nat (length items))%N.
Proof.
  induction items as [|item rest IH]; intro Hcost.
  - cbn [fold_right map length]. lia.
  - assert (Hhead := Hcost item (or_introl eq_refl)).
    specialize (IH (fun x Hx => Hcost x (or_intror Hx))).
    cbn [fold_right map length]. rewrite Nat2N.inj_add, Nat2N.inj_succ.
    replace (unit * (N.of_nat (cells item) +
      N.of_nat (fold_right (fun item total => (cells item + total)%nat) 0%nat rest)) +
      allowance * N.succ (N.of_nat (length rest)))%N with
      ((unit * N.of_nat (cells item) + allowance) +
       (unit * N.of_nat (fold_right (fun item total => (cells item + total)%nat) 0%nat rest) +
        allowance * N.of_nat (length rest)))%N by (rewrite <- N.add_1_r; ring).
    now apply N.add_le_mono.
Qed.

Local Opaque dom_order_index_build T_dom_order_index_build.

(** * Summed clocks for sibling indexes *)

(** A named proof-support copy exposes the original index fold's unchanged callback. *)
Definition dom_order_index_add rows pre (indexes : ptrie dom_child_index) vertex :=
  let children := dom_order_row rows vertex in
  PTrieCode.set (dom_lt_key vertex)
    (dom_order_index_build (N.size_nat (N.of_nat (length children))) pre children) indexes.
TimeFun dom_order_index_add.

(** One index insertion pays for its row once per explicit recursion level. *)
Lemma dom_order_index_add_clock width height rows pre indexes vertex :
  N.size_nat vertex <= width ->
  Forall (fun child => N.size_nat child <= width) (dom_order_row rows vertex) ->
  N.size_nat (N.of_nat (length (dom_order_row rows vertex))) <= height ->
  (T_dom_order_index_add rows pre indexes vertex <=
    1024 * (PTrieT.c_trie + 1) *
      N.of_nat ((height + 1) * (length (dom_order_row rows vertex) + 1) * (width + 1)))%N.
Proof.
  intros Hvertex Hchildren Hheight.
  set (children := dom_order_row rows vertex) in *.
  set (fuel := N.size_nat (N.of_nat (length children))) in *.
  set (w := N.of_nat (width + 1)).
  set (h := N.of_nat (height + 1)).
  set (cells := N.of_nat (length children + 1)).
  assert (Hw : (1 <= w)%N) by (unfold w; lia).
  assert (Hh : (1 <= h)%N) by (unfold h; lia).
  assert (Hcells : (1 <= cells)%N) by (unfold cells; lia).
  assert (Hnumber : forall child, In child children ->
    (T_dom_order_number pre child <= 8 * w)%N).
  { intros child Hin. pose proof (dom_order_number_clock pre child) as Hread.
    apply Forall_forall with (x := child) in Hchildren; [|exact Hin].
    unfold w. rewrite !Nat2N.inj_add in *. lia. }
  pose proof (dom_order_index_build_time fuel pre children (8 * w)%N Hnumber) as Hbuild.
  set (budget := (w * h * cells)%N).
  assert (Hwidth_budget : (w <= budget)%N) by (unfold budget; nia).
  assert (Hcells_budget : (cells <= budget)%N) by (unfold budget; nia).
  assert (Hbuild_budget : (T_dom_order_index_build fuel pre children <= 288 * budget)%N).
  { eapply N.le_trans; [exact Hbuild|].
    replace (288 * budget)%N with ((288 * w) * (h * cells))%N by (unfold budget; ring).
    apply N.mul_le_mono; [lia|].
    rewrite Nat2N.inj_mul. fold cells. apply N.mul_le_mono_r.
    unfold h. apply time_of_nat_le. lia. }
  pose proof (dom_order_row_clock rows vertex) as Hrow.
  pose proof (dom_lt_time_key vertex) as Hkey.
  pose proof (dom_lt_key_width vertex) as Hkey_width.
  pose proof (Datatypes.T_length_le children) as Hlength.
  pose proof (dom_time_of_nat (length children)) as Hconvert.
  pose proof (N.T_size_nat_le (N.of_nat (length children))) as Hsize.
  pose proof (dom_size_value (N.of_nat (length children))) as Hsize_value.
  pose proof (PTrieT.T_set_le dom_child_index (dom_lt_key vertex)
    (dom_order_index_build fuel pre children) indexes) as Hset.
  change (PTrieCode.T_set (dom_lt_key vertex) (dom_order_index_build fuel pre children) indexes <=
    PTrieT.c_trie * N.of_nat (Pos.size_nat (dom_lt_key vertex) + 1))%N in Hset.
  assert (Hsetup : (64 + T_dom_order_row rows vertex + T_dom_lt_key vertex +
    Datatypes.T_length children + TimeHelpers.N.T_of_nat (length children) +
    N.T_size_nat (N.of_nat (length children)) +
    PTrieCode.T_set (dom_lt_key vertex) (dom_order_index_build fuel pre children) indexes <=
    128 * (PTrieT.c_trie + 1) * w + 8 * cells)%N).
  { unfold w, cells. rewrite !Nat2N.inj_add in *.
    clear -Hvertex Hrow Hkey Hkey_width Hlength Hconvert Hsize Hsize_value Hset. nia. }
  assert (Hsetup_budget : (128 * (PTrieT.c_trie + 1) * w + 8 * cells <=
    (128 * (PTrieT.c_trie + 1) + 8) * budget)%N).
  { clearbody budget. clear -Hwidth_budget Hcells_budget. nia. }
  unfold T_dom_order_index_add. time_simpl. fold children fuel.
  rewrite !Nat2N.inj_mul. fold h cells w.
  replace (1024 * (PTrieT.c_trie + 1) * (h * cells * w))%N with
    ((1024 * (PTrieT.c_trie + 1)) * budget)%N by (unfold budget; ring).
  clearbody budget. clear -Hbuild_budget Hsetup Hsetup_budget. nia.
Qed.


Local Transparent dom_order_index_build T_dom_order_index_build.

(** * Distinct removal inventories *)

Definition dom_order_record_vertices (records : list (N * N * N)) : list N :=
  map (fun entry => fst (fst entry)) records.

(** Updating an activity bit changes exactly the chosen numeric key. *)
Lemma dom_order_active_set active vertex marked query :
  dom_order_active (PTrieCode.set (dom_lt_key vertex) marked active) query =
    if N.eqb query vertex then marked else dom_order_active active query.
Proof.
  unfold dom_order_active.
  destruct (N.eq_dec query vertex) as [->|Hdifferent].
  - rewrite N.eqb_refl, PTrie.get_set_same. now destruct marked.
  - rewrite (proj2 (N.eqb_neq query vertex) Hdifferent), PTrie.get_set_other;
      [reflexivity|].
    intro Hkeys. apply dom_lt_key_injective in Hkeys. contradiction.
Qed.

(** Initial activation adds only its explicitly listed vertices. *)
Lemma dom_order_active_fold_domain xs active vertex :
  dom_order_active (fold_left
    (fun active v => PTrieCode.set (dom_lt_key v) true active) xs active) vertex = true ->
  In vertex xs \/ dom_order_active active vertex = true.
Proof.
  revert active. induction xs as [|v rest IH]; intros active Hactive.
  - now right.
  - cbn [fold_left] in Hactive. apply IH in Hactive.
    destruct Hactive as [Hin|Hactive]; [left; now right|].
    rewrite dom_order_active_set in Hactive.
    destruct (N.eqb vertex v) eqn:Heq; [|now right].
    apply N.eqb_eq in Heq. subst vertex. left. now left.
Qed.

(** A successful fallback returns an active vertex from its remaining input. *)
Lemma dom_order_fallback_active active remaining vertex rest :
  dom_order_fallback active remaining = Some (vertex, rest) ->
  dom_order_active active vertex = true /\ In vertex remaining.
Proof.
  induction remaining as [|v remaining IH]; intro Hfallback.
  - discriminate Hfallback.
  - cbn [dom_order_fallback] in Hfallback.
    destruct (dom_order_active active v) eqn:Hactive.
    + injection Hfallback as <- <-. split; [exact Hactive|now left].
    + destruct (IH Hfallback) as [Hvertex Hin]. split; [exact Hvertex|now right].
Qed.

(** Recorded vertices are distinct, originate in the initial domain, and have been retired. *)
Definition dom_order_record_inventory allowed active records : Prop :=
  (forall v, dom_order_active active v = true -> In v allowed) /\
  NoDup (dom_order_record_vertices records) /\
  incl (dom_order_record_vertices records) allowed /\
  forall v, In v (dom_order_record_vertices records) -> dom_order_active active v = false.

(** Retiring an active vertex records a fresh entry and preserves the original domain. *)
Lemma dom_order_record_inventory_add allowed active records vertex anchor witness :
  dom_order_record_inventory allowed active records ->
  dom_order_active active vertex = true ->
  dom_order_record_inventory allowed (PTrieCode.set (dom_lt_key vertex) false active)
    ((vertex, anchor, witness) :: records).
Proof.
  intros [Hactive [Hunique [Hlisted Hretired]]] Hvertex.
  assert (Hfresh : ~ In vertex (dom_order_record_vertices records)).
  { intro Hin. specialize (Hretired vertex Hin). congruence. }
  unfold dom_order_record_inventory.
  cbn [dom_order_record_vertices map fst]. split.
  - intros v Hv. rewrite dom_order_active_set in Hv.
    destruct (N.eqb v vertex); [discriminate Hv|now apply Hactive].
  - split; [constructor; assumption|]. split.
    + intros v [<-|Hin]; [now apply Hactive|now apply Hlisted].
    + intros v [<-|Hin]; rewrite dom_order_active_set.
      * now rewrite N.eqb_refl.
      * destruct (N.eqb v vertex); [reflexivity|now apply Hretired].
Qed.

(** * Credit for guarded child-row traversals *)

Definition dom_order_unmarked {A : Type} (weight : positive -> nat)
    (keys : list positive) (marks : ptrie A) : nat :=
  fold_right (fun key total =>
    (match trie_get key marks with None => weight key | Some _ => 0 end) + total) 0 keys.

(** Marking a key outside the counted domain leaves all unmarked credit unchanged. *)
Lemma dom_order_unmarked_absent {A : Type} weight keys (marks : ptrie A) key value :
  ~ In key keys ->
  dom_order_unmarked weight keys (PTrieCode.set key value marks) =
    dom_order_unmarked weight keys marks.
Proof.
  induction keys as [|head rest IH]; intro Houtside; [reflexivity|].
  unfold dom_order_unmarked in *. cbn [fold_right].
  rewrite PTrie.get_set_other by (intro Heq; apply Houtside; now left).
  rewrite IH; [reflexivity|]. intro Hin. apply Houtside. now right.
Qed.

(** A first mark spends exactly that key's weight when the counted keys are distinct. *)
Lemma dom_order_unmarked_mark {A : Type} weight keys (marks : ptrie A) key value :
  NoDup keys -> In key keys -> trie_get key marks = None ->
  dom_order_unmarked weight keys (PTrieCode.set key value marks) + weight key =
    dom_order_unmarked weight keys marks.
Proof.
  intro Hunique. induction Hunique as [|head rest Hfresh Hunique IH];
    intros Hin Hmissing; [contradiction|].
  destruct Hin as [<-|Hin].
  - cbn [dom_order_unmarked fold_right]. rewrite PTrie.get_set_same, Hmissing.
    change (dom_order_unmarked weight rest (PTrieCode.set head value marks) + weight head =
      weight head + dom_order_unmarked weight rest marks).
    rewrite dom_order_unmarked_absent by exact Hfresh. lia.
  - assert (Hdifferent : head <> key) by (intro Heq; subst head; contradiction).
    specialize (IH Hin Hmissing).
    unfold dom_order_unmarked in *. cbn [fold_right].
    rewrite PTrie.get_set_other by exact Hdifferent.
    change (PTrie.get head marks) with (trie_get head marks). lia.
Qed.

(** Initially every counted key retains its full weight. *)
Lemma dom_order_unmarked_empty {A : Type} weight keys :
  dom_order_unmarked weight keys (Empty : ptrie A) =
    fold_right (fun key total => weight key + total) 0 keys.
Proof.
  induction keys as [|key rest IH]; [reflexivity|].
  unfold dom_order_unmarked in *. cbn [fold_right].
  rewrite PTrie.get_empty, IH. reflexivity.
Qed.

(** Unit credit starts with one unit per counted key. *)
Lemma dom_order_unmarked_units_empty {A : Type} keys :
  dom_order_unmarked (fun _ => 1%nat) keys (Empty : ptrie A) = length keys.
Proof.
  rewrite dom_order_unmarked_empty.
  induction keys as [|key rest IH]; cbn [fold_right length]; lia.
Qed.

(** Row credit starts with the total row mass over the chosen domain. *)
Lemma dom_order_unmarked_rows_empty {A B : Type} keys (rows : ptrie (list B)) :
  dom_order_unmarked
    (fun key => length (match trie_get key rows with None => [] | Some row => row end))
    keys (Empty : ptrie A) = dom_lt_row_mass keys rows.
Proof.
  rewrite dom_order_unmarked_empty. reflexivity.
Qed.
(** * Numbering inventories over a finite numeric key domain *)

Definition dom_order_task_vertex (task : dom_order_task) : N :=
  match task with
  | DomOrderEnter vertex => vertex
  | DomOrderLeave vertex => vertex
  end.

Definition dom_order_walk_inventory (keys : list positive) (st : dom_order_walk) : Prop :=
  Forall (fun task => In (dom_lt_key (dom_order_task_vertex task)) keys) (order_tasks st) /\
  (order_clock st +
    N.of_nat (dom_order_unmarked (fun _ => 1%nat) keys (order_pre st)) =
      N.of_nat (length keys))%N /\
  dom_lt_trie_all (fun value => (value <= N.of_nat (length keys))%N) (order_pre st) /\
  dom_lt_trie_all (fun value => (value <= N.of_nat (length keys))%N) (order_post st).

(** The counter is bounded by its original finite key inventory. *)
Lemma dom_order_walk_inventory_clock keys st :
  dom_order_walk_inventory keys st -> (order_clock st <= N.of_nat (length keys))%N.
Proof.
  intros [_ [Hcount _]]. lia.
Qed.

(** Explicit task, counter and table bounds form the numbering invariant. *)
Lemma dom_order_walk_inventory_make keys tasks pre post clock :
  Forall (fun task => In (dom_lt_key (dom_order_task_vertex task)) keys) tasks ->
  (clock + N.of_nat (dom_order_unmarked (fun _ => 1%nat) keys pre) =
    N.of_nat (length keys))%N ->
  dom_lt_trie_all (fun value => (value <= N.of_nat (length keys))%N) pre ->
  dom_lt_trie_all (fun value => (value <= N.of_nat (length keys))%N) post ->
  dom_order_walk_inventory keys (DomOrderWalk tasks pre post clock).
Proof.
  intros Htasks Hclock Hpre Hpost. exact (conj Htasks (conj Hclock (conj Hpre Hpost))).
Qed.

(** The initial root task and empty tables satisfy the finite numbering inventory. *)
Lemma dom_order_number_initial_inventory keys :
  In (dom_lt_key 1%N) keys ->
  dom_order_walk_inventory keys (DomOrderWalk [DomOrderEnter 1%N] Empty Empty 0%N).
Proof.
  intro Hroot. apply dom_order_walk_inventory_make.
  - constructor; [exact Hroot|constructor].
  - rewrite dom_order_unmarked_units_empty. lia.
  - apply dom_lt_trie_all_empty.
  - apply dom_lt_trie_all_empty.
Qed.

(** Numbering only creates tasks for stored children and increments once per fresh key. *)
Lemma dom_order_number_step_inventory keys rows st :
  NoDup keys ->
  dom_lt_trie_all (Forall (fun vertex => In (dom_lt_key vertex) keys)) rows ->
  dom_order_walk_inventory keys st ->
  match dom_order_number_step rows st with
  | inl next => dom_order_walk_inventory keys next
  | inr result => dom_order_walk_inventory keys result
  end.
Proof.
  intros Hunique Hrows Hinv.
  pose proof (dom_order_walk_inventory_clock keys st Hinv) as Hclock_bound.
  destruct st as [tasks pre post clock].
  destruct Hinv as [Htasks [Hclock [Hpre Hpost]]].
  cbn [order_tasks order_pre order_post order_clock] in *.
  destruct tasks as [|task rest].
  - exact (conj Htasks (conj Hclock (conj Hpre Hpost))).
  - inversion Htasks as [|head tail Hmember Hrest]; subst head tail.
    destruct task as [vertex|vertex]; cbn [dom_order_task_vertex] in Hmember.
    + cbn [dom_order_number_step order_tasks order_pre order_post order_clock].
      destruct (trie_get (dom_lt_key vertex) pre) as [stored|] eqn:Hget.
      * now apply dom_order_walk_inventory_make.
      * pose proof (dom_order_unmarked_mark (fun _ => 1%nat) keys pre
          (dom_lt_key vertex) clock Hunique Hmember Hget) as Hspent.
        assert (Hrow : Forall (fun child => In (dom_lt_key child) keys)
          (dom_order_row rows vertex)) by now apply dom_order_row_forall.
        apply dom_order_walk_inventory_make.
        -- apply Forall_app. split.
           ++ apply Forall_map. exact Hrow.
           ++ constructor; assumption.
        -- apply (f_equal N.of_nat) in Hspent. rewrite Nat2N.inj_add in Hspent.
           cbn beta in Hspent. lia.
        -- now apply dom_lt_trie_all_set.
        -- exact Hpost.
    + cbn [dom_order_number_step order_tasks order_pre order_post order_clock].
      apply dom_order_walk_inventory_make; try assumption.
      apply dom_lt_trie_all_set; [exact Hpost|].
      eapply N.le_trans; [apply N.le_pred_l|exact Hclock_bound].
Qed.

(** Any explicit fuel preserves all numbering ranges, including a partial result. *)
Lemma dom_order_number_tree_inventory keys limit rows :
  NoDup keys -> In (dom_lt_key 1%N) keys ->
  dom_lt_trie_all (Forall (fun vertex => In (dom_lt_key vertex) keys)) rows ->
  dom_order_walk_inventory keys (dom_order_number_tree limit rows).
Proof.
  intros Hunique Hroot Hrows.
  set (initial := DomOrderWalk [DomOrderEnter 1%N] Empty Empty 0%N).
  assert (Hinitial : dom_order_walk_inventory keys initial).
  { now apply dom_order_number_initial_inventory. }
  pose proof (dom_lt_loop_invariant (dom_order_number_step rows)
    (dom_order_walk_inventory keys) (dom_order_walk_inventory keys)
    (N.double limit + limit + 3)%N initial) as Hloop.
  specialize (Hloop ltac:(intros st next Hst Hstep;
    pose proof (dom_order_number_step_inventory keys rows st Hunique Hrows Hst) as Hnext;
    rewrite Hstep in Hnext; exact Hnext)).
  specialize (Hloop ltac:(intros st result Hst Hstep;
    pose proof (dom_order_number_step_inventory keys rows st Hunique Hrows Hst) as Hresult;
    rewrite Hstep in Hresult; exact Hresult) Hinitial).
  unfold dom_order_number_tree. fold initial.
  destruct (loopN (dom_order_number_step rows) (N.double limit + limit + 3)%N initial);
    exact Hloop.
Qed.

Definition dom_order_number_credit keys (rows : ptrie (list N)) (st : dom_order_walk) : nat :=
  length (order_tasks st) +
  2 * dom_order_unmarked
    (fun key => length (match trie_get key rows with None => [] | Some row => row end))
    keys (order_pre st) +
  2 * dom_order_unmarked (fun _ => 1%nat) keys (order_pre st) + 1.

(** A first visit spends its complete child row and an extra task credit unit. *)
Lemma dom_order_number_fresh_credit keys rows vertex rest pre post clock :
  NoDup keys -> In (dom_lt_key vertex) keys -> trie_get (dom_lt_key vertex) pre = None ->
  dom_order_number_credit keys rows
    (DomOrderWalk (map DomOrderEnter (dom_order_row rows vertex) ++ DomOrderLeave vertex :: rest)
      (PTrieCode.set (dom_lt_key vertex) clock pre) post (N.succ clock)) +
    length (dom_order_row rows vertex) + 2 =
  dom_order_number_credit keys rows (DomOrderWalk (DomOrderEnter vertex :: rest) pre post clock).
Proof.
  intros Hunique Hmember Hmissing.
  pose proof (dom_order_unmarked_mark
    (fun key => length (match trie_get key rows with None => [] | Some row => row end))
    keys pre (dom_lt_key vertex) clock Hunique Hmember Hmissing) as Hrows.
  pose proof (dom_order_unmarked_mark (fun _ => 1%nat)
    keys pre (dom_lt_key vertex) clock Hunique Hmember Hmissing) as Hcount.
  cbn beta in Hrows, Hcount. fold (dom_order_row rows vertex) in Hrows.
  unfold dom_order_number_credit.
  cbn [order_tasks order_pre]. rewrite length_app, length_map. cbn [length]. lia.
Qed.

(** Initial numbering credit is one root task plus the original row and key inventories. *)
Lemma dom_order_number_initial_credit keys rows :
  dom_order_number_credit keys rows (DomOrderWalk [DomOrderEnter 1%N] Empty Empty 0%N) =
    2 * (dom_lt_row_mass keys rows + length keys + 1).
Proof.
  unfold dom_order_number_credit. cbn [order_tasks order_pre length].
  rewrite dom_order_unmarked_rows_empty, dom_order_unmarked_units_empty. lia.
Qed.

(** * Weighted binary-loop clocks for ordering *)

(** A fixed callback allowance and a linear row charge fit a per-row work budget. *)
Lemma dom_order_affine_work_budget (coefficient cells work : N) :
  (4 <= coefficient)%N -> (work <= coefficient + 4 * cells)%N ->
  (work <= 2 * coefficient * (cells + 1))%N.
Proof.
  intros Hcoefficient Hwork. nia.
Qed.

(** A scalar callback bound and a decreasing work potential telescope through the binary loop. *)
Lemma dom_order_work_loop {S R : Type} (step : S -> S + R) (T_step : S -> N)
    (Inv : S -> Prop) (work credit : S -> nat) coefficient fuel initial :
  (forall st, Inv st -> (T_step st + c_loopN <= coefficient * N.of_nat (work st))%N) ->
  (forall st next, Inv st -> step st = inl next ->
    Inv next /\ credit next + work st <= credit st) ->
  (forall st result, Inv st -> step st = inr result -> work st <= credit st) ->
  Inv initial ->
  (T_loopN step T_step fuel initial <=
    coefficient * N.of_nat (credit initial) + c_loopN * N.of_nat (N.size_nat fuel + 1))%N.
Proof.
  intros Hclock Hcontinue Hstop Hinitial.
  pose proof (T_loopN_amort S R step T_step Inv
    (fun st => coefficient * N.of_nat (credit st))%N (fun _ => 0%N)
    fuel initial) as Hloop.
  assert (Hgo : forall st next, Inv st -> step st = inl next ->
    Inv next /\ (T_step st + c_loopN + coefficient * N.of_nat (credit next) <=
      coefficient * N.of_nat (credit st))%N).
  { intros st next Hst Hstep.
    destruct (Hcontinue st next Hst Hstep) as [Hnext Hcredit]. split; [exact Hnext|].
    specialize (Hclock st Hst). apply time_of_nat_le in Hcredit.
    rewrite Nat2N.inj_add in Hcredit.
    apply N.mul_le_mono_l with (p := coefficient) in Hcredit.
    rewrite N.mul_add_distr_l in Hcredit. lia. }
  assert (Hdone : forall st result, Inv st -> step st = inr result ->
    (T_step st + c_loopN + 0 <= coefficient * N.of_nat (credit st))%N).
  { intros st result Hst Hstep. specialize (Hclock st Hst).
    specialize (Hstop st result Hst Hstep). apply time_of_nat_le in Hstop.
    apply N.mul_le_mono_l with (p := coefficient) in Hstop. lia. }
  specialize (Hloop Hgo Hdone Hinitial).
  destruct (loopN step fuel initial); cbn beta in Hloop; lia.
Qed.

(** A positive width and work unit pay the fixed binary-loop callback overhead. *)
Lemma dom_order_callback_overhead (coefficient overhead width work value : N) :
  (1 <= width)%N -> (1 <= work)%N -> (value <= coefficient * width * work)%N ->
  (value + overhead <= (coefficient + overhead) * width * work)%N.
Proof.
  intros Hwidth Hwork Hvalue.
  assert (Hextra : (overhead <= overhead * width * work)%N).
  { replace overhead with (overhead * 1)%N at 1 by ring.
    rewrite <- N.mul_assoc. apply N.mul_le_mono_l. nia. }
  replace ((coefficient + overhead) * width * work)%N with
    (coefficient * width * work + overhead * width * work)%N by ring. lia.
Qed.


(** * Numbering callback and finite-row clocks *)

Definition dom_order_number_work (rows : ptrie (list N)) (st : dom_order_walk) : nat :=
  match order_tasks st with
  | DomOrderEnter vertex :: _ =>
    match trie_get (dom_lt_key vertex) (order_pre st) with
    | None => length (dom_order_row rows vertex) + 1
    | Some _ => 1
    end
  | _ => 1
  end.

(** Every numbering callback has at least one unit of list or administrative work. *)
Lemma dom_order_number_work_positive rows st : 1 <= dom_order_number_work rows st.
Proof.
  destruct st as [[|[vertex|vertex] rest] pre post clock];
    cbn [dom_order_number_work order_tasks order_pre]; try lia.
  destruct (trie_get (dom_lt_key vertex) pre); lia.
Qed.

(** The row and fresh-key credit pays the exact work unit of every continuing callback. *)
Lemma dom_order_number_step_credit keys rows st next :
  NoDup keys -> dom_order_walk_inventory keys st ->
  dom_order_number_step rows st = inl next ->
  dom_order_number_credit keys rows next + dom_order_number_work rows st <=
    dom_order_number_credit keys rows st.
Proof.
  intros Hunique Hinv Hstep. destruct st as [tasks pre post clock].
  destruct Hinv as [Htasks Hrest].
  cbn [order_tasks] in Htasks. destruct tasks as [|[vertex|vertex] tasks].
  - discriminate Hstep.
  - inversion Htasks as [|head tail Hmember Htail]; subst head tail.
    cbn [dom_order_task_vertex] in Hmember.
    cbn [dom_order_number_step order_tasks order_pre order_post order_clock] in Hstep.
    cbn [dom_order_number_work order_tasks order_pre].
    destruct (trie_get (dom_lt_key vertex) pre) as [stored|] eqn:Hget;
      injection Hstep as <-.
    + unfold dom_order_number_credit. cbn [order_tasks order_pre length]. lia.
    + pose proof (dom_order_number_fresh_credit keys rows vertex tasks pre post clock
        Hunique Hmember Hget) as Hcredit. lia.
  - cbn [dom_order_number_step order_tasks order_pre order_post order_clock] in Hstep.
    injection Hstep as <-. unfold dom_order_number_credit, dom_order_number_work.
    cbn [order_tasks order_pre length]. lia.
Qed.

(** Terminal numbering needs only the permanent unit retained in its credit. *)
Lemma dom_order_number_stop_credit keys rows st result :
  dom_order_number_step rows st = inr result ->
  dom_order_number_work rows st <= dom_order_number_credit keys rows st.
Proof.
  destruct st as [tasks pre post clock]. destruct tasks as [|[vertex|vertex] tasks].
  - intro Hstep. unfold dom_order_number_credit, dom_order_number_work.
    cbn [order_tasks order_pre length]. lia.
  - cbn [dom_order_number_step order_tasks order_pre order_post order_clock].
    destruct (trie_get (dom_lt_key vertex) pre); discriminate.
  - discriminate.
Qed.

Local Opaque dom_order_index_build T_dom_order_index_build
  dom_order_index_search T_dom_order_index_search.

(** Pointwise callback domination lifts to the generated clock of the unchanged state fold. *)
Lemma dom_order_fold_clock_mono {A B : Type} (step : A -> B -> A)
    (left_clock right_clock : A -> B -> N) xs st :
  (forall current item, (left_clock current item <= right_clock current item)%N) ->
  (List.T_fold_left step left_clock xs st <= List.T_fold_left step right_clock xs st)%N.
Proof.
  intro Hclock. revert st. induction xs as [|item rest IH]; intro st.
  - change (1 <= 1)%N. reflexivity.
  - change (1 + (left_clock st item +
      List.T_fold_left step left_clock rest (step st item)) <=
      1 + (right_clock st item +
      List.T_fold_left step right_clock rest (step st item)))%N.
    pose proof (Hclock st item) as Hhead. specialize (IH (step st item)).
    clear -Hhead IH. lia.
Qed.

(** Naming the callback changes no callback or fold body and adds only wrapper constants. *)
Lemma dom_order_indexes_overhead order rows pre :
  (T_dom_order_indexes order rows pre <=
    List.T_fold_left (dom_order_index_add rows pre) (T_dom_order_index_add rows pre)
      order Empty + 8)%N.
Proof.
  unfold T_dom_order_indexes. time_simpl.
  eapply N.le_trans with (1 +
    List.T_fold_left (dom_order_index_add rows pre) (T_dom_order_index_add rows pre)
      order Empty)%N.
  - apply N.add_le_mono_l. apply dom_order_fold_clock_mono.
    intros indexes vertex. unfold T_dom_order_index_add. time_simpl. lia.
  - lia.
Qed.

(** Each row and each order entry is charged once by the complete index fold. *)
Lemma dom_order_indexes_clock width height order rows pre :
  Forall (fun vertex => N.size_nat vertex <= width) order ->
  dom_lt_trie_all (Forall (fun child => N.size_nat child <= width)) rows ->
  (forall vertex, In vertex order ->
    N.size_nat (N.of_nat (length (dom_order_row rows vertex))) <= height) ->
  (T_dom_order_indexes order rows pre <=
    2048 * (PTrieT.c_trie + 1) *
      N.of_nat ((dom_lt_row_mass (map dom_lt_key order) rows + length order + 1) *
        (height + 1) * (width + 1)))%N.
Proof.
  intros Horder Hrows Hheight.
  set (unit := (1024 * (PTrieT.c_trie + 1) * N.of_nat ((height + 1) * (width + 1)))%N).
  assert (Hunit : (8 <= unit)%N) by (unfold unit; rewrite Nat2N.inj_mul; nia).
  assert (Hcallback : forall vertex, In vertex order -> forall indexes,
    (T_dom_order_index_add rows pre indexes vertex <=
      unit * N.of_nat (length (dom_order_row rows vertex) + 1))%N).
  { intros vertex Hin indexes.
    pose proof (dom_order_index_add_clock width height rows pre indexes vertex
      (proj1 (Forall_forall _ _) Horder vertex Hin)
      (dom_order_row_forall _ rows vertex Hrows) (Hheight vertex Hin)) as Hclock.
    unfold unit. rewrite !Nat2N.inj_mul in *.
    replace (1024 * (PTrieT.c_trie + 1) *
      (N.of_nat (height + 1) * N.of_nat (width + 1)) *
      N.of_nat (length (dom_order_row rows vertex) + 1))%N with
      (1024 * (PTrieT.c_trie + 1) *
        (N.of_nat (height + 1) * N.of_nat (length (dom_order_row rows vertex) + 1) *
          N.of_nat (width + 1)))%N by ring. exact Hclock. }
  pose proof (dom_order_fold_sum_clock (dom_order_index_add rows pre)
    (T_dom_order_index_add rows pre)
    (fun vertex => unit * N.of_nat (length (dom_order_row rows vertex) + 1))%N
    order Empty Hcallback) as Hfold.
  rewrite dom_order_sum_scaled in Hfold.
  rewrite (dom_order_sum_allowance (fun vertex => length (dom_order_row rows vertex))
    order 1), dom_order_rows_sum, Nat.mul_1_l in Hfold.
  pose proof (dom_order_indexes_overhead order rows pre) as Hsetup.
  rewrite !Nat2N.inj_mul.
  replace (2048 * (PTrieT.c_trie + 1) *
    (N.of_nat (dom_lt_row_mass (map dom_lt_key order) rows + length order + 1) *
      N.of_nat (height + 1) * N.of_nat (width + 1)))%N with
    (2 * unit * N.of_nat (dom_lt_row_mass (map dom_lt_key order) rows + length order + 1))%N
    by (unfold unit; rewrite Nat2N.inj_mul; ring).
  rewrite !Nat2N.inj_add in *.
  clearbody unit. clear -Hunit Hfold Hsetup. nia.
Qed.

(** * Bounded searches for derived sibling sources *)

(** Every stored index inherits the uniform recursion-height bound of its input row. *)
Lemma dom_order_indexes_height order rows pre height :
  (forall vertex, In vertex order ->
    N.size_nat (N.of_nat (length (dom_order_row rows vertex))) <= height) ->
  dom_lt_trie_all (fun index => dom_order_index_height index <= height)
    (dom_order_indexes order rows pre).
Proof.
  intro Hheight. unfold dom_order_indexes.
  eapply dom_lt_fold_forall with
    (Inv := dom_lt_trie_all (fun index => dom_order_index_height index <= height))
    (P := fun vertex => In vertex order).
  - apply Forall_forall. auto.
  - apply dom_lt_trie_all_empty.
  - intros indexes vertex Hindexes Hvertex. apply dom_lt_trie_all_set; [exact Hindexes|].
    eapply Nat.le_trans; [apply dom_order_index_build_height|now apply Hheight].
Qed.


Local Transparent dom_order_index_build T_dom_order_index_build
  dom_order_index_search T_dom_order_index_search.

(** Every numbering callback is linear in the newly visited row, at the common numeric width. *)
Lemma dom_order_number_step_clock width rows st :
  Forall (fun task => N.size_nat (dom_order_task_vertex task) <= width) (order_tasks st) ->
  N.size_nat (order_clock st) <= width ->
  (T_dom_order_number_step rows st <=
    128 * (PTrieT.c_trie + 1) * N.of_nat (width + 1) *
      N.of_nat (dom_order_number_work rows st))%N.
Proof.
  destruct st as [tasks pre post clock]. intros Htasks Hclock.
  cbn [order_tasks order_clock] in Htasks, Hclock.
  destruct tasks as [|[vertex|vertex] tasks].
  - unfold T_dom_order_number_step, dom_order_number_work.
    time_simpl. cbn [order_tasks]. rewrite Nat2N.inj_add. nia.
  - inversion Htasks as [|head tail Hvertex Htail]; subst head tail.
    cbn [dom_order_task_vertex] in Hvertex.
    pose proof (dom_lt_time_key vertex) as Hkey.
    pose proof (dom_lt_key_width vertex) as Hkey_width.
    unfold T_dom_order_number_step, dom_order_number_work.
    time_simpl. cbn [order_tasks order_pre order_post order_clock].
    PTrieT.trie_get_le.
    destruct (trie_get (dom_lt_key vertex) pre) as [stored|] eqn:Hget.
    + time_simpl. rewrite !Nat2N.inj_add in *. nia.
    + pose proof (dom_order_row_clock rows vertex) as Hrow.
      pose proof (ListDef.T_map_le DomOrderEnter (fun _ => 1%N) 1%N
        (dom_order_row rows vertex) ltac:(intro; reflexivity)) as Hmap.
      pose proof (Datatypes.T_app_le (map DomOrderEnter (dom_order_row rows vertex))
        (DomOrderLeave vertex :: tasks)) as Happend.
      rewrite length_map in Happend.
      pose proof (PTrieT.T_set_le N (dom_lt_key vertex) clock pre) as Hset.
      change (PTrieCode.T_set (dom_lt_key vertex) clock pre <=
        PTrieT.c_trie * N.of_nat (Pos.size_nat (dom_lt_key vertex) + 1))%N in Hset.
      pose proof (N.T_succ_le clock) as Hsucc.
      time_simpl. rewrite !Nat2N.inj_add in *.
      change (N.of_nat 1) with 1%N in *.
      eapply N.le_trans with
        (64 * (PTrieT.c_trie + 1) * (N.of_nat width + 1) +
          4 * N.of_nat (length (dom_order_row rows vertex)))%N.
      * clear -Hvertex Hclock Hkey Hkey_width Hrow Hmap Happend Hset Hsucc. PTrieT.trie_get_le. nia.
      * replace (128 * (PTrieT.c_trie + 1) * (N.of_nat width + 1) *
          (N.of_nat (length (dom_order_row rows vertex)) + 1))%N with
          (2 * (64 * (PTrieT.c_trie + 1) * (N.of_nat width + 1)) *
            (N.of_nat (length (dom_order_row rows vertex)) + 1))%N by ring.
        apply dom_order_affine_work_budget; [clear -width; nia|reflexivity].
  - inversion Htasks as [|head tail Hvertex Htail]; subst head tail.
    cbn [dom_order_task_vertex] in Hvertex.
    pose proof (dom_lt_time_key vertex) as Hkey.
    pose proof (dom_lt_key_width vertex) as Hkey_width.
    pose proof (PTrieT.T_set_le N (dom_lt_key vertex) (N.pred clock) post) as Hset.
    change (PTrieCode.T_set (dom_lt_key vertex) (N.pred clock) post <=
      PTrieT.c_trie * N.of_nat (Pos.size_nat (dom_lt_key vertex) + 1))%N in Hset.
    pose proof (N.T_pred_le clock) as Hpred.
    unfold T_dom_order_number_step, dom_order_number_work.
    time_simpl. cbn [order_tasks order_pre order_post order_clock].
    rewrite !Nat2N.inj_add in *. clear -Hvertex Hclock Hkey Hkey_width Hset Hpred.
    PTrieT.trie_get_le. nia.
Qed.



(** Numbering's loop spends its finite row and key inventory once. *)
Lemma dom_order_number_loop_clock keys rows width fuel :
  NoDup keys -> In (dom_lt_key 1%N) keys ->
  dom_lt_trie_all (Forall (fun vertex => In (dom_lt_key vertex) keys)) rows ->
  (forall vertex, In (dom_lt_key vertex) keys -> N.size_nat vertex <= width) ->
  (forall value, (value <= N.of_nat (length keys))%N -> N.size_nat value <= width) ->
  (T_loopN (dom_order_number_step rows) (T_dom_order_number_step rows) fuel
    (DomOrderWalk [DomOrderEnter 1%N] Empty Empty 0%N) <=
    2 * ((128 * (PTrieT.c_trie + 1) + c_loopN) * N.of_nat (width + 1)) *
      N.of_nat (dom_lt_row_mass keys rows + length keys + 1) +
      c_loopN * N.of_nat (N.size_nat fuel + 1))%N.
Proof.
  intros Hunique Hroot Hrows Hkeys Hvalues.
  set (coefficient := ((128 * (PTrieT.c_trie + 1) + c_loopN) * N.of_nat (width + 1))%N).
  assert (Hclock : forall st, dom_order_walk_inventory keys st ->
    (T_dom_order_number_step rows st + c_loopN <=
      coefficient * N.of_nat (dom_order_number_work rows st))%N).
  { intros st Hst.
    assert (Htasks : Forall (fun task => N.size_nat (dom_order_task_vertex task) <= width)
      (order_tasks st)).
    { apply Forall_forall. intros task Hin. apply Hkeys.
      pose proof (proj1 Hst) as Hmembers.
      now apply Forall_forall with (x := task) in Hmembers. }
    assert (Hcounter : N.size_nat (order_clock st) <= width).
    { apply Hvalues. now apply dom_order_walk_inventory_clock. }
    pose proof (dom_order_number_step_clock width rows st Htasks Hcounter) as Hstep.
    pose proof (dom_order_number_work_positive rows st) as Hwork.
    unfold coefficient. apply dom_order_callback_overhead; [lia|lia|exact Hstep]. }
  assert (Hgo : forall st next, dom_order_walk_inventory keys st ->
    dom_order_number_step rows st = inl next ->
    dom_order_walk_inventory keys next /\
      dom_order_number_credit keys rows next + dom_order_number_work rows st <=
        dom_order_number_credit keys rows st).
  { intros st next Hst Hstep. split.
    - pose proof (dom_order_number_step_inventory keys rows st Hunique Hrows Hst) as Hnext.
      now rewrite Hstep in Hnext.
    - eapply dom_order_number_step_credit; eassumption. }
  pose proof (dom_order_work_loop (dom_order_number_step rows) (T_dom_order_number_step rows)
    (dom_order_walk_inventory keys) (dom_order_number_work rows)
    (dom_order_number_credit keys rows) coefficient fuel
    (DomOrderWalk [DomOrderEnter 1%N] Empty Empty 0%N) Hclock Hgo
    ltac:(intros st result Hst Hstep;
      exact (dom_order_number_stop_credit keys rows st result Hstep))
    (dom_order_number_initial_inventory keys Hroot)) as Hloop.
  rewrite dom_order_number_initial_credit, Nat2N.inj_mul in Hloop.
  change (N.of_nat 2) with 2%N in Hloop.
  fold coefficient. replace (2 * coefficient *
    N.of_nat (dom_lt_row_mass keys rows + length keys + 1) +
      c_loopN * N.of_nat (N.size_nat fuel + 1))%N with
    (coefficient * (2 * N.of_nat (dom_lt_row_mass keys rows + length keys + 1)) +
      c_loopN * N.of_nat (N.size_nat fuel + 1))%N by ring. exact Hloop.
Qed.

(** The numbering wrapper adds only arithmetic on the supplied limit to its loop clock. *)
Lemma dom_order_number_tree_overhead limit rows :
  (T_dom_order_number_tree limit rows <=
    T_loopN (dom_order_number_step rows) (T_dom_order_number_step rows)
      (N.double limit + limit + 3)%N (DomOrderWalk [DomOrderEnter 1%N] Empty Empty 0%N) +
      32 * N.of_nat (N.size_nat limit + 1))%N.
Proof.
  pose proof (Search.search_N_double_size limit) as Hdouble.
  pose proof (Search.search_N_add_size (N.double limit) limit) as Hsum.
  pose proof (N.T_add_le (N.double limit) limit) as Hfirst.
  pose proof (N.T_add_le (N.double limit + limit)%N 3%N) as Hsecond.
  unfold T_dom_order_number_tree. time_simpl.
  change (T_loopN (dom_order_number_step rows)
    (fun st => T_dom_order_number_step rows st)
    (N.double limit + limit + 3)%N (DomOrderWalk [DomOrderEnter 1%N] Empty Empty 0%N)) with
    (T_loopN (dom_order_number_step rows) (T_dom_order_number_step rows)
      (N.double limit + limit + 3)%N (DomOrderWalk [DomOrderEnter 1%N] Empty Empty 0%N)).
  time_simpl. cbn [N.size_nat Pos.size_nat] in Hsecond.
  rewrite !Nat2N.inj_add in *. clear -Hdouble Hsum Hfirst Hsecond. lia.
Qed.

(** Binary setup fuel for numbering grows by at most a constant factor in bit width. *)
Lemma dom_order_number_fuel_bits limit :
  N.size_nat (N.double limit + limit + 3)%N <= 2 * N.size_nat limit + 3.
Proof.
  pose proof (Search.search_N_double_size limit) as Hdouble.
  pose proof (Search.search_N_add_size (N.double limit) limit) as Hsum.
  pose proof (Search.search_N_add_size (N.double limit + limit)%N 3%N) as Hfuel.
  cbn [N.size_nat Pos.size_nat] in Hfuel. lia.
Qed.

Definition dom_order_number_coefficient : N :=
  (512 * (PTrieT.c_trie + c_loopN + 1))%N.

(** Numbering is linear in its finite key and child-row inventories at the common numeric width. *)
Lemma dom_order_number_tree_clock keys rows limit width :
  NoDup keys -> In (dom_lt_key 1%N) keys ->
  dom_lt_trie_all (Forall (fun vertex => In (dom_lt_key vertex) keys)) rows ->
  (forall vertex, In (dom_lt_key vertex) keys -> N.size_nat vertex <= width) ->
  (forall value, (value <= N.of_nat (length keys))%N -> N.size_nat value <= width) ->
  N.size_nat limit <= width ->
  (T_dom_order_number_tree limit rows <= dom_order_number_coefficient *
    N.of_nat ((dom_lt_row_mass keys rows + length keys + 1) * (width + 1)))%N.
Proof.
  intros Hunique Hroot Hrows Hkeys Hvalues Hlimit.
  pose proof (dom_order_number_loop_clock keys rows width
    (N.double limit + limit + 3)%N Hunique Hroot Hrows Hkeys Hvalues) as Hloop.
  pose proof (dom_order_number_tree_overhead limit rows) as Hsetup.
  pose proof (dom_order_number_fuel_bits limit) as Hfuel.
  set (mass := N.of_nat (dom_lt_row_mass keys rows + length keys + 1)) in *.
  assert (Hmass : (1 <= mass)%N) by (unfold mass; lia).
  rewrite Nat2N.inj_mul. fold mass.
  set (w := N.of_nat (width + 1)) in *.
  assert (Hw : (1 <= w)%N) by (unfold w; lia).
  assert (Hfuel_cost : (c_loopN * N.of_nat (N.size_nat (N.double limit + limit + 3)%N + 1) <=
    4 * c_loopN * w)%N).
  { assert (Hbits : N.size_nat (N.double limit + limit + 3)%N + 1 <= 4 * (width + 1))
      by lia.
    apply time_of_nat_le in Hbits. rewrite Nat2N.inj_mul in Hbits.
    change (N.of_nat 4) with 4%N in Hbits. fold w in Hbits.
    replace (4 * c_loopN * w)%N with (c_loopN * (4 * w))%N by ring.
    now apply N.mul_le_mono_l. }
  assert (Hsetup_width : (32 * N.of_nat (N.size_nat limit + 1) <= 32 * w)%N).
  { apply N.mul_le_mono_l. unfold w. apply time_of_nat_le. lia. }
  set (budget := (mass * w)%N).
  assert (Hwidth_budget : (w <= budget)%N).
  { unfold budget. replace w with (1 * w)%N at 1 by ring. now apply N.mul_le_mono_r. }
  assert (Hfuel_budget : (c_loopN * N.of_nat (N.size_nat (N.double limit + limit + 3)%N + 1) <=
    4 * c_loopN * budget)%N).
  { eapply N.le_trans; [exact Hfuel_cost|]. now apply N.mul_le_mono_l. }
  assert (Hsetup_budget : (T_dom_order_number_tree limit rows <=
    T_loopN (dom_order_number_step rows) (T_dom_order_number_step rows)
      (N.double limit + limit + 3)%N (DomOrderWalk [DomOrderEnter 1%N] Empty Empty 0%N) +
      32 * budget)%N).
  { eapply N.le_trans; [exact Hsetup|]. apply N.add_le_mono_l.
    eapply N.le_trans; [exact Hsetup_width|]. now apply N.mul_le_mono_l. }
  replace (2 * ((128 * (PTrieT.c_trie + 1) + c_loopN) * w) * mass)%N with
    ((256 * (PTrieT.c_trie + 1) + 2 * c_loopN) * budget)%N in Hloop
      by (unfold budget; ring).
  fold budget. unfold dom_order_number_coefficient.
  clearbody budget. clear -Hloop Hfuel_budget Hsetup_budget. nia.
Qed.

(** A removal callback either preserves its inventory or returns a distinct original sublist. *)
Lemma dom_order_remove_step_inventory parents allowed st :
  dom_order_record_inventory allowed (removal_active st) (removal_records st) ->
  match dom_order_remove_step parents st with
  | inl next =>
    dom_order_record_inventory allowed (removal_active next) (removal_records next)
  | inr records =>
    NoDup (dom_order_record_vertices records) /\ incl (dom_order_record_vertices records) allowed
  end.
Proof.
  destruct st as [blue red active queue remaining records]. intro Hinv.
  unfold dom_order_remove_step.
  cbn [removal_queue removal_blue removal_red removal_active
    removal_fallback removal_records] in *.
  destruct queue as [|v queue].
  - destruct (dom_order_fallback active remaining) as [[vertex rest]|] eqn:Hfallback.
    + cbn [removal_active removal_records]. apply dom_order_record_inventory_add;
        [exact Hinv|].
      exact (proj1 (dom_order_fallback_active active remaining vertex rest Hfallback)).
    + exact (conj (proj1 (proj2 Hinv)) (proj1 (proj2 (proj2 Hinv)))).
  - destruct (dom_order_active active v) eqn:Hactive; [|exact Hinv].
    destruct (N.ltb (N.add (dom_order_number (source_count blue) v)
        (dom_order_number (source_count red) v))
      (if N.eqb (dom_lt_identity (source_parent blue) v)
        (dom_lt_identity (source_parent red) v) then 1%N else 2%N)).
    + cbn [removal_active removal_records].
      now apply dom_order_record_inventory_add.
    + exact Hinv.
Qed.

(** The explicit-fuel removal pass returns distinct vertices from its filtered input. *)
Lemma dom_order_removal_inventory limit parents order sources :
  NoDup (dom_order_record_vertices (dom_order_removal limit parents order sources)) /\
  incl (dom_order_record_vertices (dom_order_removal limit parents order sources)) order.
Proof.
  unfold dom_order_removal.
  set (children := filter (fun v => match trie_get (dom_lt_key v) parents with
    None => false | Some _ => true end) order).
  set (active := fold_left (fun active v => PTrieCode.set (dom_lt_key v) true active)
    children Empty).
  set (initial := DomOrderRemovalState
    (dom_source_initial parents (source_blue sources) children)
    (dom_source_initial parents (source_red sources) children) active children children []).
  assert (Hinitial : dom_order_record_inventory order (removal_active initial)
    (removal_records initial)).
  { unfold initial. cbn [removal_active removal_records].
    unfold dom_order_record_inventory. cbn [dom_order_record_vertices map].
    split.
    - intros v Hv. unfold active in Hv. apply dom_order_active_fold_domain in Hv.
      destruct Hv as [Hin|Hempty].
      + unfold children in Hin. now apply filter_In in Hin as [Hin _].
      + unfold dom_order_active in Hempty. rewrite PTrie.get_empty in Hempty.
        discriminate Hempty.
    - split; [constructor|]. split; intros v Hbad; contradiction. }
  pose proof (dom_lt_loop_invariant (dom_order_remove_step parents)
    (fun st => dom_order_record_inventory order (removal_active st) (removal_records st))
    (fun records => NoDup (dom_order_record_vertices records) /\
      incl (dom_order_record_vertices records) order)
    (N.double (N.double (N.double (N.double limit))) + 3)%N initial) as Hloop.
  specialize (Hloop ltac:(intros st next Hinv Hstep;
    pose proof (dom_order_remove_step_inventory parents order st Hinv) as Hnext;
    rewrite Hstep in Hnext; exact Hnext)).
  specialize (Hloop ltac:(intros st result Hinv Hstep;
    pose proof (dom_order_remove_step_inventory parents order st Hinv) as Hresult;
    rewrite Hstep in Hresult; exact Hresult) Hinitial).
  destruct (loopN (dom_order_remove_step parents)
    (N.double (N.double (N.double (N.double limit))) + 3)%N initial) as [st|result].
  - exact (conj (proj1 (proj2 Hloop)) (proj1 (proj2 (proj2 Hloop)))).
  - exact Hloop.
Qed.

(** At most one removal record is produced for each original order entry. *)
Lemma dom_order_removal_length limit parents order sources :
  length (dom_order_removal limit parents order sources) <= length order.
Proof.
  destruct (dom_order_removal_inventory limit parents order sources) as [Hunique Hlisted].
  pose proof (NoDup_incl_length Hunique Hlisted) as Hlength.
  unfold dom_order_record_vertices in Hlength. now rewrite length_map in Hlength.
Qed.

(** Numeric encoding preserves the distinct removed-vertex inventory. *)
Lemma dom_order_removal_keys_unique limit parents order sources :
  NoDup (map (fun entry => dom_lt_key (fst (fst entry)))
    (dom_order_removal limit parents order sources)).
Proof.
  replace (map (fun entry => dom_lt_key (fst (fst entry)))
    (dom_order_removal limit parents order sources)) with
    (map dom_lt_key (dom_order_record_vertices (dom_order_removal limit parents order sources))).
  - apply dom_lt_key_map_unique.
    exact (proj1 (dom_order_removal_inventory limit parents order sources)).
  - unfold dom_order_record_vertices. now rewrite map_map.
Qed.
(** * Raw source and removal operand ranges *)

(** Every index stores children from the bounded input rows, independently of its positions. *)
Lemma dom_order_indexes_values (P : N -> Prop) order rows pre :
  dom_lt_trie_all (Forall P) rows ->
  dom_lt_trie_all (dom_order_index_values P (fun _ => True))
    (dom_order_indexes order rows pre).
Proof.
  intro Hrows. unfold dom_order_indexes.
  eapply dom_lt_fold_forall with
    (Inv := dom_lt_trie_all (dom_order_index_values P (fun _ => True)))
    (P := fun _ => True).
  - apply Forall_forall. auto.
  - apply dom_lt_trie_all_empty.
  - intros indexes vertex Hindexes Hvertex.
    apply dom_lt_trie_all_set; [exact Hindexes|].
    apply dom_order_index_build_values; [now apply dom_order_row_forall|auto].
Qed.

(** * Numeric universes including empty-traversal sentinels *)

Definition dom_order_key_universe (count : nat) : list positive :=
  map (fun rank => dom_lt_key (N.of_nat rank)) (seq 0 (count + 2)).

(** The numeric key universe contains one distinct key for every rank from zero through count+1. *)
Lemma dom_order_key_universe_unique count : NoDup (dom_order_key_universe count).
Proof.
  unfold dom_order_key_universe. apply dom_lt_map_unique_on.
  - apply seq_NoDup.
  - intros left right Hleft Hright Hkeys.
    apply dom_lt_key_injective in Hkeys. now apply Nat2N.inj in Hkeys.
Qed.

(** Two additional ranks cover zero-default values and the root-one sentinel. *)
Lemma dom_order_key_universe_length count : length (dom_order_key_universe count) = count + 2.
Proof.
  unfold dom_order_key_universe. now rewrite length_map, length_seq.
Qed.

(** Every bounded numeric rank has a key in the chosen universe. *)
Lemma dom_order_key_universe_member count vertex :
  (vertex <= N.of_nat (count + 1))%N -> In (dom_lt_key vertex) (dom_order_key_universe count).
Proof.
  intro Hvertex. unfold dom_order_key_universe. apply in_map_iff.
  exists (N.to_nat vertex). split.
  - now rewrite N2Nat.id.
  - apply in_seq. lia.
Qed.

(** Universe membership bounds the original numeric value. *)
Lemma dom_order_key_universe_bound count vertex :
  In (dom_lt_key vertex) (dom_order_key_universe count) ->
  (vertex <= N.of_nat (count + 1))%N.
Proof.
  unfold dom_order_key_universe. intro Hin.
  apply in_map_iff in Hin as [rank [Hkey Hrank]].
  apply dom_lt_key_injective in Hkey. subst vertex.
  apply in_seq in Hrank. lia.
Qed.

(** The root sentinel remains present even when no graph vertex is discovered. *)
Lemma dom_order_key_universe_root count : In (dom_lt_key 1%N) (dom_order_key_universe count).
Proof.
  apply dom_order_key_universe_member. lia.
Qed.

(** Bounded child-row values are members of the finite counting universe. *)
Lemma dom_order_key_universe_rows count rows :
  dom_lt_trie_all (Forall (fun value => (value <= N.of_nat count)%N)) rows ->
  dom_lt_trie_all (Forall (fun vertex =>
    In (dom_lt_key vertex) (dom_order_key_universe count))) rows.
Proof.
  intros Hrows key row Hget. specialize (Hrows key row Hget).
  apply Forall_forall. intros vertex Hin.
  apply Forall_forall with (x := vertex) in Hrows; [|exact Hin].
  apply dom_order_key_universe_member. lia.
Qed.

(** A derived source is either the supplied parent or a child stored in its index. *)
Lemma dom_order_derived_value (P : N -> Prop) indexes walk parent source :
  P parent -> dom_lt_trie_all (dom_order_index_values P (fun _ => True)) indexes ->
  P (dom_order_derived indexes walk parent source).
Proof.
  intros Hparent Hindexes. unfold dom_order_derived.
  destruct (N.eqb parent source); [exact Hparent|].
  destruct (trie_get (dom_lt_key parent) indexes) as [index|] eqn:Hindex;
    [|exact Hparent].
  destruct (trie_get (dom_lt_key source) (order_pre walk)) as [position|];
    [|exact Hparent].
  destruct (dom_order_index_search position index) as [child|] eqn:Hchild;
    [|exact Hparent].
  destruct (N.leb position (dom_order_number (order_post walk) child)); [|exact Hparent].
  exact (dom_order_index_search_value P (fun _ => True) index position child
    (Hindexes (dom_lt_key parent) index Hindex) Hchild).
Qed.

Definition dom_order_sources_range (bound : N) (sources : dom_order_sources) : Prop :=
  dom_lt_trie_all (fun value => (value <= bound)%N) (source_blue sources) /\
  dom_lt_trie_all (fun value => (value <= bound)%N) (source_red sources).

Local Opaque dom_order_index_search T_dom_order_index_search.
Local Transparent dom_order_derived T_dom_order_derived.

(** Searching a derived source costs one bounded index path and a constant number of key reads. *)
Lemma dom_order_derived_clock width height indexes walk parent source :
  N.size_nat parent <= width -> N.size_nat source <= width ->
  dom_lt_trie_all (dom_order_index_values (fun child => N.size_nat child <= width)
    (fun _ => True)) indexes ->
  dom_lt_trie_all (fun index => dom_order_index_height index <= height) indexes ->
  dom_lt_trie_all (fun position => N.size_nat position <= width) (order_pre walk) ->
  (T_dom_order_derived indexes walk parent source <=
    64 * N.of_nat ((height + 1) * (width + 1)))%N.
Proof.
  intros Hparent Hsource Hchildren Hheights Hpositions.
  set (budget := N.of_nat ((height + 1) * (width + 1))). fold budget.
  assert (Hwidth_budget : (N.of_nat (width + 1) <= budget)%N).
  { unfold budget. apply time_of_nat_le. clear -height width. nia. }
  pose proof (dom_lt_time_key parent) as Hparent_key.
  pose proof (dom_lt_time_key source) as Hsource_key.
  pose proof (dom_lt_key_width parent) as Hparent_bits.
  pose proof (dom_lt_key_width source) as Hsource_bits.
  pose proof (N.T_eqb_le parent source) as Hcompare.
  unfold T_dom_order_derived. time_simpl.
  destruct (N.eqb parent source).
  - time_simpl. rewrite !Nat2N.inj_add in *.
    change (N.of_nat 1) with 1%N in *. clearbody budget.
    clear -Hparent Hcompare Hwidth_budget. lia.
  - PTrieT.trie_get_le.
    destruct (trie_get (dom_lt_key parent) indexes) as [index|] eqn:Hindex.
    + destruct (trie_get (dom_lt_key source) (order_pre walk)) as [position|] eqn:Hposition.
      * pose proof (Hpositions (dom_lt_key source) position Hposition) as Hposition_width.
        change (N.size_nat position <= width) in Hposition_width.
        pose proof (Hheights (dom_lt_key parent) index Hindex) as Hheight.
        change (dom_order_index_height index <= height) in Hheight.
        pose proof (dom_order_index_search_time position index) as Hsearch.
        assert (Hsearch_bound : (T_dom_order_index_search position index <=
          8 * budget)%N).
        { unfold budget. rewrite !Nat2N.inj_mul, !Nat2N.inj_add in *.
          apply time_of_nat_le in Hheight.
          clear -Hposition_width Hheight Hsearch. nia. }
        destruct (dom_order_index_search position index) as [child|] eqn:Hchild.
        -- assert (Hchild_width : N.size_nat child <= width).
           { eapply (dom_order_index_search_value
               (fun value => N.size_nat value <= width) (fun _ => True) index position child).
             - exact (Hchildren (dom_lt_key parent) index Hindex).
             - exact Hchild. }
           pose proof (dom_order_number_clock (order_post walk) child) as Hnumber.
           pose proof (N.T_leb_le position (dom_order_number (order_post walk) child)) as Hwithin.
           time_simpl. destruct (N.leb position (dom_order_number (order_post walk) child));
             time_simpl; rewrite !Nat2N.inj_add in *;
             change (N.of_nat 1) with 1%N in *; clearbody budget;
             clear -Hparent Hsource Hparent_key Hsource_key Hparent_bits Hsource_bits Hcompare
               Hposition_width Hsearch_bound Hchild_width Hnumber Hwithin Hwidth_budget;
             PTrieT.trie_get_le; lia.
        -- time_simpl. rewrite !Nat2N.inj_add in *.
           change (N.of_nat 1) with 1%N in *. clearbody budget.
           clear -Hparent Hsource Hparent_key Hsource_key Hparent_bits Hsource_bits Hcompare
             Hsearch_bound Hwidth_budget. PTrieT.trie_get_le. lia.
      * time_simpl. rewrite !Nat2N.inj_add in *.
        change (N.of_nat 1) with 1%N in *. clearbody budget.
        clear -Hparent Hsource Hparent_key Hsource_key Hparent_bits Hsource_bits Hcompare
          Hwidth_budget. PTrieT.trie_get_le. lia.
    + destruct (trie_get (dom_lt_key source) (order_pre walk)); time_simpl;
        rewrite !Nat2N.inj_add in *;
        change (N.of_nat 1) with 1%N in *; clearbody budget;
        clear -Hparent Hsource Hparent_key Hsource_key Hparent_bits Hsource_bits Hcompare
          Hwidth_budget; PTrieT.trie_get_le; lia.
Qed.

Local Transparent dom_order_index_search T_dom_order_index_search.

(** Colouring writes only a bounded parent or a bounded indexed child to either source map. *)
Lemma dom_order_colour_range bound numeric semis minimizer relative parents indexes walk st v :
  dom_lt_trie_all (fun value => (value <= bound)%N) parents ->
  dom_lt_trie_all (dom_order_index_values (fun value => (value <= bound)%N)
    (fun _ => True)) indexes ->
  dom_order_sources_range bound st ->
  dom_order_sources_range bound
    (dom_order_colour numeric semis minimizer relative parents indexes walk st v).
Proof.
  intros Hparents Hindexes [Hblue Hred].
  unfold dom_order_colour.
  destruct (trie_get (dom_lt_key v) parents) as [parent|] eqn:Hparent;
    [|exact (conj Hblue Hred)].
  pose proof (Hparents (dom_lt_key v) parent Hparent) as Hbound.
  assert (Hderived : forall source, (dom_order_derived indexes walk parent source <= bound)%N).
  { intro source. exact (dom_order_derived_value (fun value => (value <= bound)%N)
      indexes walk parent source Hbound Hindexes). }
  unfold dom_order_sources_range. cbn [source_blue source_red].
  split.
  - apply dom_lt_trie_all_set; [exact Hblue|].
    destruct (existsb (N.eqb parent) (dom_order_row (lt_numeric_pred numeric) v));
      [exact Hbound|apply Hderived].
  - apply dom_lt_trie_all_set; [exact Hred|].
    destruct (existsb (N.eqb parent) (dom_order_row (lt_numeric_pred numeric) v));
      [exact Hbound|apply Hderived].
Qed.

(** Source-map construction retains the raw numeric range without a correctness premise. *)
Lemma dom_order_source_maps_range bound numeric semis minimizer relative parents :
  Forall (fun value => (value <= bound)%N) (lt_numeric_order numeric) ->
  dom_lt_trie_all (fun value => (value <= bound)%N) parents ->
  dom_order_sources_range bound
    (dom_order_source_maps numeric semis minimizer relative parents).
Proof.
  intros Horder Hparents.
  set (rows := fold_left (dom_order_child_add parents) (lt_numeric_order numeric) Empty).
  assert (Hrows : dom_lt_trie_all (Forall (fun value => (value <= bound)%N)) rows).
  { apply dom_order_child_fold_forall; [exact Horder|apply dom_lt_trie_all_empty]. }
  set (walk := dom_order_number_tree (lt_numeric_limit numeric) rows).
  set (indexes := dom_order_indexes (lt_numeric_order numeric) rows (order_pre walk)).
  pose proof (dom_order_indexes_values (fun value => (value <= bound)%N)
    (lt_numeric_order numeric) rows (order_pre walk) Hrows) as Hindexes.
  fold indexes in Hindexes. unfold dom_order_source_maps. fold rows walk indexes.
  eapply dom_lt_fold_forall with (Inv := dom_order_sources_range bound) (P := fun _ => True).
  - apply Forall_forall. auto.
  - split; apply dom_lt_trie_all_empty.
  - intros st v Hst Hv. now apply dom_order_colour_range.
Qed.

Definition dom_source_range (bound : N) (tree : dom_source_tree) : Prop :=
  dom_lt_trie_all (fun value => (value <= bound)%N) (source_parent tree) /\
  dom_lt_trie_all (Forall (fun value => (value <= bound)%N)) (source_children tree).

(** A source insertion preserves both parent payloads and inverse-row members. *)
Lemma dom_source_add_range bound tree vertex source parent :
  dom_source_range bound tree -> (vertex <= bound)%N -> (source <= bound)%N ->
  dom_source_range bound (dom_source_add tree vertex source parent).
Proof.
  intros [Hparents Hchildren] Hvertex Hsource.
  unfold dom_source_add, dom_source_range.
  destruct (N.eqb source parent); cbn [source_parent source_children]; split.
  - now apply dom_lt_trie_all_set.
  - exact Hchildren.
  - now apply dom_lt_trie_all_set.
  - apply dom_lt_trie_all_set; [exact Hchildren|].
    constructor; [exact Hvertex|now apply dom_order_row_forall].
Qed.

(** Source initialization uses only input vertices and bounded source values. *)
Lemma dom_source_initial_range bound parents sources order :
  dom_lt_trie_all (fun value => (value <= bound)%N) sources ->
  Forall (fun value => (value <= bound)%N) order ->
  dom_source_range bound (dom_source_initial parents sources order).
Proof.
  intros Hsources Horder. unfold dom_source_initial.
  eapply dom_lt_fold_forall with (Inv := dom_source_range bound)
    (P := fun value => (value <= bound)%N).
  - exact Horder.
  - split; apply dom_lt_trie_all_empty.
  - intros tree vertex Htree Hvertex.
    destruct (trie_get (dom_lt_key vertex) parents) as [parent|]; [|exact Htree].
    apply dom_source_add_range; try assumption.
    now apply dom_lt_identity_bounded.
Qed.

(** Removing a source only changes its count table. *)
Lemma dom_source_remove_range bound tree vertex parent :
  dom_source_range bound tree ->
  dom_source_range bound (dom_source_remove tree vertex parent).
Proof.
  intro Htree. unfold dom_source_remove.
  destruct (N.eqb (dom_lt_identity (source_parent tree) vertex) parent); exact Htree.
Qed.

(** Redirecting a child combines a count update with one bounded source insertion. *)
Lemma dom_source_redirect_range bound tree vertex source parent :
  dom_source_range bound tree -> (vertex <= bound)%N -> (source <= bound)%N ->
  dom_source_range bound (dom_source_redirect tree vertex source parent).
Proof.
  intros Htree Hvertex Hsource. unfold dom_source_redirect.
  apply dom_source_add_range; try assumption. now apply dom_source_remove_range.
Qed.

(** A successful inverse-row search returns one of that row's original members. *)
Lemma dom_source_child_member sources active source row child :
  dom_source_child sources active source row = Some child -> In child row.
Proof.
  induction row as [|vertex rest IH]; intro Hchild; [discriminate Hchild|].
  cbn [dom_source_child] in Hchild.
  destruct (dom_order_active active vertex && N.eqb (dom_lt_identity sources vertex) source).
  - injection Hchild as <-. now left.
  - right. now apply IH.
Qed.

(** The fallback result and its residual suffix retain all original element predicates. *)
Lemma dom_order_fallback_forall (P : N -> Prop) active remaining vertex rest :
  Forall P remaining -> dom_order_fallback active remaining = Some (vertex, rest) ->
  P vertex /\ Forall P rest.
Proof.
  intro Hall. induction Hall as [|head tail Hhead Htail IH]; intro Hfallback;
    [discriminate Hfallback|].
  cbn [dom_order_fallback] in Hfallback.
  destruct (dom_order_active active head).
  - injection Hfallback as <- <-. auto.
  - now apply IH.
Qed.

Definition dom_order_removal_range (bound : N) (st : dom_order_removal_state) : Prop :=
  dom_source_range bound (removal_blue st) /\
  dom_source_range bound (removal_red st) /\
  Forall (fun value => (value <= bound)%N) (removal_queue st) /\
  Forall (fun value => (value <= bound)%N) (removal_fallback st) /\
  Forall (fun entry => let '(v, a, w) := entry in (v <= bound /\ a <= bound /\ w <= bound)%N)
    (removal_records st).

(** Separate source, queue, suffix and record ranges form the removal invariant. *)
Lemma dom_order_removal_range_make bound blue red active queue remaining records :
  dom_source_range bound blue -> dom_source_range bound red ->
  Forall (fun value => (value <= bound)%N) queue ->
  Forall (fun value => (value <= bound)%N) remaining ->
  Forall (fun entry => let '(v, a, w) := entry in (v <= bound /\ a <= bound /\ w <= bound)%N)
    records ->
  dom_order_removal_range bound (DomOrderRemovalState blue red active queue remaining records).
Proof.
  intros Hblue Hred Hqueue Hremaining Hrecords.
  exact (conj Hblue (conj Hred (conj Hqueue (conj Hremaining Hrecords)))).
Qed.

(** Every successful removal records only bounded vertices, anchors and witnesses. *)
Lemma dom_order_remove_step_range bound parents st :
  dom_lt_trie_all (fun value => (value <= bound)%N) parents ->
  dom_order_removal_range bound st ->
  match dom_order_remove_step parents st with
  | inl next => dom_order_removal_range bound next
  | inr records =>
    Forall (fun entry => let '(v, a, w) := entry in (v <= bound /\ a <= bound /\ w <= bound)%N)
      records
  end.
Proof.
  intros Hparents Hrange. destruct st as [blue red active queue remaining records].
  destruct Hrange as [Hblue [Hred [Hqueue [Hremaining Hrecords]]]].
  cbn [removal_blue removal_red removal_queue removal_fallback removal_records] in *.
  unfold dom_order_remove_step.
  cbn [removal_blue removal_red removal_active removal_queue
    removal_fallback removal_records].
  destruct queue as [|vertex queue].
  - destruct (dom_order_fallback active remaining) as [[vertex rest]|] eqn:Hfallback;
      [|exact Hrecords].
    destruct (dom_order_fallback_forall _ active remaining vertex rest Hremaining Hfallback)
      as [Hvertex Hrest].
    assert (Hparent : (dom_lt_identity parents vertex <= bound)%N).
    { now apply dom_lt_identity_bounded. }
    apply dom_order_removal_range_make.
    + exact Hblue.
    + exact Hred.
    + constructor.
    + exact Hrest.
    + constructor; [exact (conj Hvertex (conj Hparent Hparent))|exact Hrecords].
  - inversion Hqueue as [|head tail Hvertex Htail]; subst head tail.
    destruct (dom_order_active active vertex);
      [|now apply dom_order_removal_range_make].
    assert (Hb : (dom_lt_identity (source_parent blue) vertex <= bound)%N).
    { apply dom_lt_identity_bounded; [exact (proj1 Hblue)|exact Hvertex]. }
    assert (Hr : (dom_lt_identity (source_parent red) vertex <= bound)%N).
    { apply dom_lt_identity_bounded; [exact (proj1 Hred)|exact Hvertex]. }
    destruct (N.ltb
      (N.add (dom_order_number (source_count blue) vertex)
        (dom_order_number (source_count red) vertex))
      (if N.eqb (dom_lt_identity (source_parent blue) vertex)
        (dom_lt_identity (source_parent red) vertex) then 1%N else 2%N));
      [|now apply dom_order_removal_range_make].
    destruct (N.eqb (dom_order_number (source_count red) vertex) 0%N);
      cbn beta iota.
    + destruct (dom_source_child (source_parent blue) active vertex
        (dom_order_row (source_children blue) vertex)) as [child|] eqn:Hchild.
      * assert (Hchild_range : (child <= bound)%N).
        { pose proof (dom_order_row_forall _ (source_children blue) vertex (proj2 Hblue))
            as Hrow. apply Forall_forall with (x := child) in Hrow; [exact Hrow|].
          now apply dom_source_child_member in Hchild. }
        apply dom_order_removal_range_make; try assumption.
        -- apply dom_source_redirect_range; try assumption. now apply dom_source_remove_range.
        -- now apply dom_source_remove_range.
        -- constructor; [exact Hb|]. constructor; [exact Hr|].
           constructor; [exact Hchild_range|exact Htail].
        -- constructor; [exact (conj Hvertex (conj Hb Hr))|exact Hrecords].
      * apply dom_order_removal_range_make; try assumption;
          try now apply dom_source_remove_range.
        -- constructor; [exact Hb|]. constructor; [exact Hr|exact Htail].
        -- constructor; [exact (conj Hvertex (conj Hb Hr))|exact Hrecords].
    + destruct (dom_source_child (source_parent red) active vertex
        (dom_order_row (source_children red) vertex)) as [child|] eqn:Hchild.
      * assert (Hchild_range : (child <= bound)%N).
        { pose proof (dom_order_row_forall _ (source_children red) vertex (proj2 Hred))
            as Hrow. apply Forall_forall with (x := child) in Hrow; [exact Hrow|].
          now apply dom_source_child_member in Hchild. }
        apply dom_order_removal_range_make; try assumption.
        -- now apply dom_source_remove_range.
        -- apply dom_source_redirect_range; try assumption. now apply dom_source_remove_range.
        -- constructor; [exact Hr|]. constructor; [exact Hb|].
           constructor; [exact Hchild_range|exact Htail].
        -- constructor; [exact (conj Hvertex (conj Hr Hb))|exact Hrecords].
      * apply dom_order_removal_range_make; try assumption;
          try now apply dom_source_remove_range.
        -- constructor; [exact Hr|]. constructor; [exact Hb|exact Htail].
        -- constructor; [exact (conj Hvertex (conj Hr Hb))|exact Hrecords].
Qed.

(** * Emission inventories and once-per-row credit *)

Definition dom_order_emit_inventory keys (st : dom_order_emit_state) : Prop :=
  Forall (fun vertex => In (dom_lt_key vertex) keys) (emit_pending st) /\
  dom_lt_trie_all (fun flag => flag = true) (emit_seen st) /\
  length (emit_reverse st) + dom_order_unmarked (fun _ => 1%nat) keys (emit_seen st) <= length keys.

(** Seen maps containing only true flags equate an inactive key with an absent binding. *)
Lemma dom_order_seen_missing seen vertex :
  dom_lt_trie_all (fun flag => flag = true) seen ->
  dom_order_active seen vertex = false -> trie_get (dom_lt_key vertex) seen = None.
Proof.
  intros Hseen Hinactive. unfold dom_order_active in Hinactive.
  destruct (trie_get (dom_lt_key vertex) seen) as [flag|] eqn:Hget; [|reflexivity].
  pose proof (Hseen (dom_lt_key vertex) flag Hget) as Htrue.
  change (flag = true) in Htrue. subst flag. discriminate Hinactive.
Qed.

(** Pending-key membership, true seen flags and output count form the emission invariant. *)
Lemma dom_order_emit_inventory_make keys pending seen reverse :
  Forall (fun vertex => In (dom_lt_key vertex) keys) pending ->
  dom_lt_trie_all (fun flag => flag = true) seen ->
  length reverse + dom_order_unmarked (fun _ => 1%nat) keys seen <= length keys ->
  dom_order_emit_inventory keys (DomOrderEmitState pending seen reverse).
Proof.
  intros Hpending Hseen Hcount. exact (conj Hpending (conj Hseen Hcount)).
Qed.

(** The initial emission root and empty seen/output maps satisfy the finite inventory. *)
Lemma dom_order_emit_initial_inventory keys :
  In (dom_lt_key 1%N) keys ->
  dom_order_emit_inventory keys (DomOrderEmitState [1%N] Empty []).
Proof.
  intro Hroot. apply dom_order_emit_inventory_make.
  - constructor; [exact Hroot|constructor].
  - apply dom_lt_trie_all_empty.
  - rewrite dom_order_unmarked_units_empty. cbn [length]. lia.
Qed.

(** Emission marks each fresh numeric key once and never emits more than that finite domain. *)
Lemma dom_order_emit_step_inventory keys vertices rows st :
  NoDup keys ->
  dom_lt_trie_all (Forall (fun vertex => In (dom_lt_key vertex) keys)) rows ->
  dom_order_emit_inventory keys st ->
  match dom_order_emit_step vertices rows st with
  | inl next => dom_order_emit_inventory keys next
  | inr result => length result <= length keys
  end.
Proof.
  intros Hunique Hrows Hinv. destruct st as [pending seen reverse].
  destruct Hinv as [Hpending [Hseen Hcount]].
  cbn [emit_pending emit_seen emit_reverse] in *.
  destruct pending as [|vertex rest].
  - cbn [dom_order_emit_step emit_pending emit_reverse].
    rewrite rev_append_rev, length_app, length_rev. cbn [length]. lia.
  - inversion Hpending as [|head tail Hmember Hrest]; subst head tail.
    cbn [dom_order_emit_step emit_pending emit_seen emit_reverse].
    destruct (dom_order_active seen vertex) eqn:Hactive.
    + now apply dom_order_emit_inventory_make.
    + pose proof (dom_order_seen_missing seen vertex Hseen Hactive) as Hmissing.
      pose proof (dom_order_unmarked_mark (fun _ => 1%nat) keys seen
        (dom_lt_key vertex) true Hunique Hmember Hmissing) as Hspent.
      apply dom_order_emit_inventory_make.
      * apply Forall_app. split; [now apply dom_order_row_forall|exact Hrest].
      * apply dom_lt_trie_all_set; [exact Hseen|reflexivity].
      * destruct (trie_get (dom_lt_key vertex) vertices);
          cbn [length]; cbn beta in Hspent; lia.
Qed.

(** Any explicit emission fuel retains the finite inventory in a partial state or a final output. *)
Lemma dom_order_emit_run_inventory keys vertices rows fuel :
  NoDup keys -> In (dom_lt_key 1%N) keys ->
  dom_lt_trie_all (Forall (fun vertex => In (dom_lt_key vertex) keys)) rows ->
  match loopN (dom_order_emit_step vertices rows) fuel (DomOrderEmitState [1%N] Empty []) with
  | inl st => dom_order_emit_inventory keys st
  | inr result => length result <= length keys
  end.
Proof.
  intros Hunique Hroot Hrows.
  apply (dom_lt_loop_invariant (dom_order_emit_step vertices rows)
    (dom_order_emit_inventory keys) (fun result => length result <= length keys)
    fuel (DomOrderEmitState [1%N] Empty [])).
  - intros st next Hst Hstep.
    pose proof (dom_order_emit_step_inventory keys vertices rows st Hunique Hrows Hst) as Hnext.
    now rewrite Hstep in Hnext.
  - intros st result Hst Hstep.
    pose proof (dom_order_emit_step_inventory keys vertices rows st Hunique Hrows Hst) as Hresult.
    now rewrite Hstep in Hresult.
  - now apply dom_order_emit_initial_inventory.
Qed.

(** Any explicit emission fuel returns at most one output per original numeric key. *)
Lemma dom_order_emit_length keys numeric rows :
  NoDup keys -> In (dom_lt_key 1%N) keys ->
  dom_lt_trie_all (Forall (fun vertex => In (dom_lt_key vertex) keys)) rows ->
  length (dom_order_emit numeric rows) <= length keys.
Proof.
  intros Hunique Hroot Hrows.
  pose proof (dom_order_emit_run_inventory keys (lt_numeric_vertex numeric) rows
    (N.double (lt_numeric_limit numeric) + 3)%N Hunique Hroot Hrows) as Hloop.
  unfold dom_order_emit.
  destruct (loopN (dom_order_emit_step (lt_numeric_vertex numeric) rows)
    (N.double (lt_numeric_limit numeric) + 3)%N (DomOrderEmitState [1%N] Empty [])) as [st|result].
  - destruct Hloop as [_ [_ Hcount]].
    rewrite rev_append_rev, length_app, length_rev. cbn [length]. lia.
  - exact Hloop.
Qed.

Definition dom_order_emit_credit keys (rows : ptrie (list N)) (st : dom_order_emit_state) : nat :=
  length (emit_pending st) +
  2 * dom_order_unmarked
    (fun key => length (match trie_get key rows with None => [] | Some row => row end))
    keys (emit_seen st) +
  2 * dom_order_unmarked (fun _ => 1%nat) keys (emit_seen st) + length keys + 2.

Definition dom_order_emit_work (rows : ptrie (list N)) (st : dom_order_emit_state) : nat :=
  match emit_pending st with
  | [] => length (emit_reverse st) + 1
  | vertex :: _ =>
    if dom_order_active (emit_seen st) vertex then 1 else length (dom_order_row rows vertex) + 1
  end.

(** Every emission callback includes a permanent administrative work unit. *)
Lemma dom_order_emit_work_positive rows st : 1 <= dom_order_emit_work rows st.
Proof.
  destruct st as [[|vertex rest] seen reverse];
    cbn [dom_order_emit_work emit_pending emit_seen emit_reverse]; [lia|].
  destruct (dom_order_active seen vertex); lia.
Qed.

(** A fresh emission visit consumes its row's credit exactly once. *)
Lemma dom_order_emit_step_credit keys vertices rows st next :
  NoDup keys -> dom_order_emit_inventory keys st ->
  dom_order_emit_step vertices rows st = inl next ->
  dom_order_emit_credit keys rows next + dom_order_emit_work rows st <=
    dom_order_emit_credit keys rows st.
Proof.
  intros Hunique Hinv Hstep. destruct st as [pending seen reverse].
  destruct Hinv as [Hpending [Hseen Hcount]].
  cbn [emit_pending emit_seen emit_reverse] in *.
  destruct pending as [|vertex rest]; [discriminate Hstep|].
  inversion Hpending as [|head tail Hmember Htail]; subst head tail.
  cbn [dom_order_emit_step emit_pending emit_seen emit_reverse] in Hstep.
  cbn [dom_order_emit_work emit_pending emit_seen emit_reverse].
  destruct (dom_order_active seen vertex) eqn:Hactive; injection Hstep as <-.
  - unfold dom_order_emit_credit. cbn [emit_pending emit_seen length]. lia.
  - pose proof (dom_order_seen_missing seen vertex Hseen Hactive) as Hmissing.
    pose proof (dom_order_unmarked_mark
      (fun key => length (match trie_get key rows with None => [] | Some row => row end))
      keys seen (dom_lt_key vertex) true Hunique Hmember Hmissing) as Hrows.
    pose proof (dom_order_unmarked_mark (fun _ => 1%nat)
      keys seen (dom_lt_key vertex) true Hunique Hmember Hmissing) as Hspent.
    cbn beta in Hrows, Hspent. fold (dom_order_row rows vertex) in Hrows.
    unfold dom_order_emit_credit. cbn [emit_pending emit_seen length].
    rewrite length_app. lia.
Qed.

(** The permanent output allowance pays the terminal reverse traversal. *)
Lemma dom_order_emit_stop_credit keys vertices rows st result :
  dom_order_emit_inventory keys st ->
  dom_order_emit_step vertices rows st = inr result ->
  dom_order_emit_work rows st <= dom_order_emit_credit keys rows st.
Proof.
  intros Hinv Hstep. destruct st as [pending seen reverse].
  destruct Hinv as [_ [_ Hcount]]. cbn [emit_reverse emit_seen] in Hcount.
  destruct pending as [|vertex rest].
  - unfold dom_order_emit_work, dom_order_emit_credit.
    cbn [emit_pending emit_reverse emit_seen length]. lia.
  - cbn [dom_order_emit_step emit_pending emit_seen] in Hstep.
    destruct (dom_order_active seen vertex); discriminate Hstep.
Qed.

(** Initial emission credit consists of its root, finite row mass and finite output allowance. *)
Lemma dom_order_emit_initial_credit keys rows :
  dom_order_emit_credit keys rows (DomOrderEmitState [1%N] Empty []) =
    2 * dom_lt_row_mass keys rows + 3 * length keys + 3.
Proof.
  unfold dom_order_emit_credit. cbn [emit_pending emit_seen length].
  rewrite dom_order_unmarked_rows_empty, dom_order_unmarked_units_empty. lia.
Qed.
(** * Emission callback and finite-row clocks *)

(** Emission spends linear work on a fresh row or on its final reverse traversal. *)
Lemma dom_order_emit_step_clock width vertices rows st :
  Forall (fun vertex => N.size_nat vertex <= width) (emit_pending st) ->
  (T_dom_order_emit_step vertices rows st <=
    128 * (PTrieT.c_trie + 1) * N.of_nat (width + 1) *
      N.of_nat (dom_order_emit_work rows st))%N.
Proof.
  destruct st as [pending seen reverse]. intro Hpending.
  cbn [emit_pending] in Hpending. destruct pending as [|vertex rest].
  - pose proof (List.T_rev_append_le reverse []) as Hreverse.
    unfold T_dom_order_emit_step, dom_order_emit_work. time_simpl.
    cbn [emit_pending emit_reverse]. rewrite !Nat2N.inj_add in *.
    change (N.of_nat 1) with 1%N in *.
    eapply N.le_trans with (64 * (PTrieT.c_trie + 1) * (N.of_nat width + 1) +
      4 * N.of_nat (length reverse))%N; [nia|].
    replace (128 * (PTrieT.c_trie + 1) * (N.of_nat width + 1) *
      (N.of_nat (length reverse) + 1))%N with
      (2 * (64 * (PTrieT.c_trie + 1) * (N.of_nat width + 1)) *
        (N.of_nat (length reverse) + 1))%N by ring.
    apply dom_order_affine_work_budget; [clear -width; nia|reflexivity].
  - inversion Hpending as [|head tail Hvertex Hrest]; subst head tail.
    change (N.size_nat vertex <= width) in Hvertex.
    pose proof (dom_order_active_clock seen vertex) as Hactive.
    unfold T_dom_order_emit_step, dom_order_emit_work. time_simpl.
    cbn [emit_pending emit_seen emit_reverse].
    destruct (dom_order_active seen vertex) eqn:Hseen.
    + time_simpl. rewrite !Nat2N.inj_add in *. nia.
    + pose proof (dom_lt_time_key vertex) as Hkey.
      pose proof (dom_lt_key_width vertex) as Hkey_width.
      pose proof (dom_order_row_clock rows vertex) as Hrow.
      pose proof (Datatypes.T_app_le (dom_order_row rows vertex) rest) as Happend.
      pose proof (PTrieT.T_set_le bool (dom_lt_key vertex) true seen) as Hset.
      change (PTrieCode.T_set (dom_lt_key vertex) true seen <=
        PTrieT.c_trie * N.of_nat (Pos.size_nat (dom_lt_key vertex) + 1))%N in Hset.
      PTrieT.trie_get_le.
      destruct (trie_get (dom_lt_key vertex) vertices); time_simpl;
        rewrite !Nat2N.inj_add in *; change (N.of_nat 1) with 1%N in *.
      all: eapply N.le_trans with
        (64 * (PTrieT.c_trie + 1) * (N.of_nat width + 1) +
          4 * N.of_nat (length (dom_order_row rows vertex)))%N;
        [clear -Hvertex Hactive Hkey Hkey_width Hrow Happend Hset; PTrieT.trie_get_le; nia|].
      all: replace (128 * (PTrieT.c_trie + 1) * (N.of_nat width + 1) *
          (N.of_nat (length (dom_order_row rows vertex)) + 1))%N with
          (2 * (64 * (PTrieT.c_trie + 1) * (N.of_nat width + 1)) *
            (N.of_nat (length (dom_order_row rows vertex)) + 1))%N by ring.
      all: apply dom_order_affine_work_budget; [clear -width; nia|reflexivity].
Qed.

(** Emission's loop spends only its finite row, key and output inventories. *)
Lemma dom_order_emit_loop_clock keys vertices rows width fuel :
  NoDup keys -> In (dom_lt_key 1%N) keys ->
  dom_lt_trie_all (Forall (fun vertex => In (dom_lt_key vertex) keys)) rows ->
  (forall vertex, In (dom_lt_key vertex) keys -> N.size_nat vertex <= width) ->
  (T_loopN (dom_order_emit_step vertices rows) (T_dom_order_emit_step vertices rows) fuel
    (DomOrderEmitState [1%N] Empty []) <=
    ((128 * (PTrieT.c_trie + 1) + c_loopN) * N.of_nat (width + 1)) *
      N.of_nat (2 * dom_lt_row_mass keys rows + 3 * length keys + 3) +
      c_loopN * N.of_nat (N.size_nat fuel + 1))%N.
Proof.
  intros Hunique Hroot Hrows Hkeys.
  set (coefficient := ((128 * (PTrieT.c_trie + 1) + c_loopN) * N.of_nat (width + 1))%N).
  assert (Hclock : forall st, dom_order_emit_inventory keys st ->
    (T_dom_order_emit_step vertices rows st + c_loopN <=
      coefficient * N.of_nat (dom_order_emit_work rows st))%N).
  { intros st Hst.
    assert (Hpending : Forall (fun vertex => N.size_nat vertex <= width) (emit_pending st)).
    { apply Forall_forall. intros vertex Hin. apply Hkeys.
      pose proof (proj1 Hst) as Hmembers.
      now apply Forall_forall with (x := vertex) in Hmembers. }
    pose proof (dom_order_emit_step_clock width vertices rows st Hpending) as Hstep.
    pose proof (dom_order_emit_work_positive rows st) as Hwork.
    unfold coefficient. apply dom_order_callback_overhead; [lia|lia|exact Hstep]. }
  assert (Hgo : forall st next, dom_order_emit_inventory keys st ->
    dom_order_emit_step vertices rows st = inl next ->
    dom_order_emit_inventory keys next /\
      dom_order_emit_credit keys rows next + dom_order_emit_work rows st <=
        dom_order_emit_credit keys rows st).
  { intros st next Hst Hstep. split.
    - pose proof (dom_order_emit_step_inventory keys vertices rows st Hunique Hrows Hst) as Hnext.
      now rewrite Hstep in Hnext.
    - eapply dom_order_emit_step_credit; eassumption. }
  pose proof (dom_order_work_loop (dom_order_emit_step vertices rows)
    (T_dom_order_emit_step vertices rows) (dom_order_emit_inventory keys)
    (dom_order_emit_work rows) (dom_order_emit_credit keys rows) coefficient fuel
    (DomOrderEmitState [1%N] Empty []) Hclock Hgo
    ltac:(intros st result Hst Hstep; eapply dom_order_emit_stop_credit; eassumption)
    (dom_order_emit_initial_inventory keys Hroot)) as Hloop.
  now rewrite dom_order_emit_initial_credit in Hloop.
Qed.

(** Binary setup fuel for emission adds at most three bits to its supplied limit. *)
Lemma dom_order_emit_fuel_bits limit :
  N.size_nat (N.double limit + 3)%N <= N.size_nat limit + 3.
Proof.
  pose proof (Search.search_N_double_size limit) as Hdouble.
  pose proof (Search.search_N_add_size (N.double limit) 3%N) as Hfuel.
  cbn [N.size_nat Pos.size_nat] in Hfuel. lia.
Qed.

(** The emission wrapper pays for binary fuel and, if needed, one bounded partial reverse. *)
Lemma dom_order_emit_overhead keys numeric rows :
  NoDup keys -> In (dom_lt_key 1%N) keys ->
  dom_lt_trie_all (Forall (fun vertex => In (dom_lt_key vertex) keys)) rows ->
  (T_dom_order_emit numeric rows <=
    T_loopN (dom_order_emit_step (lt_numeric_vertex numeric) rows)
      (T_dom_order_emit_step (lt_numeric_vertex numeric) rows)
      (N.double (lt_numeric_limit numeric) + 3)%N (DomOrderEmitState [1%N] Empty []) +
    64 * N.of_nat (N.size_nat (lt_numeric_limit numeric) + 1) +
    4 * N.of_nat (length keys + 1))%N.
Proof.
  intros Hunique Hroot Hrows.
  pose proof (dom_order_emit_run_inventory keys (lt_numeric_vertex numeric) rows
    (N.double (lt_numeric_limit numeric) + 3)%N Hunique Hroot Hrows) as Hrun.
  pose proof (Search.search_N_double_size (lt_numeric_limit numeric)) as Hdouble.
  pose proof (N.T_add_le (N.double (lt_numeric_limit numeric)) 3%N) as Hadd.
  unfold T_dom_order_emit. time_simpl.
  change (T_loopN (dom_order_emit_step (lt_numeric_vertex numeric) rows)
    (fun st => T_dom_order_emit_step (lt_numeric_vertex numeric) rows st)
    (N.double (lt_numeric_limit numeric) + 3)%N (DomOrderEmitState [1%N] Empty [])) with
    (T_loopN (dom_order_emit_step (lt_numeric_vertex numeric) rows)
      (T_dom_order_emit_step (lt_numeric_vertex numeric) rows)
      (N.double (lt_numeric_limit numeric) + 3)%N (DomOrderEmitState [1%N] Empty [])).
  destruct (loopN (dom_order_emit_step (lt_numeric_vertex numeric) rows)
    (N.double (lt_numeric_limit numeric) + 3)%N (DomOrderEmitState [1%N] Empty []))
    as [st|result].
  - destruct Hrun as [_ [_ Hcount]].
    pose proof (List.T_rev_append_le (emit_reverse st) []) as Hreverse.
    time_simpl. cbn [N.size_nat Pos.size_nat] in Hadd.
    rewrite !Nat2N.inj_add in *. clear -Hcount Hdouble Hadd Hreverse. lia.
  - time_simpl. cbn [N.size_nat Pos.size_nat] in Hadd.
    rewrite !Nat2N.inj_add in *. clear -Hdouble Hadd. lia.
Qed.

Definition dom_order_emit_coefficient : N :=
  (1024 * (PTrieT.c_trie + c_loopN + 1))%N.

(** Emission is linear in its finite row and key inventories at the common numeric width. *)
Lemma dom_order_emit_clock keys numeric rows width :
  NoDup keys -> In (dom_lt_key 1%N) keys ->
  dom_lt_trie_all (Forall (fun vertex => In (dom_lt_key vertex) keys)) rows ->
  (forall vertex, In (dom_lt_key vertex) keys -> N.size_nat vertex <= width) ->
  N.size_nat (lt_numeric_limit numeric) <= width ->
  (T_dom_order_emit numeric rows <= dom_order_emit_coefficient *
    N.of_nat ((dom_lt_row_mass keys rows + length keys + 1) * (width + 1)))%N.
Proof.
  intros Hunique Hroot Hrows Hkeys Hlimit.
  pose proof (dom_order_emit_loop_clock keys (lt_numeric_vertex numeric) rows width
    (N.double (lt_numeric_limit numeric) + 3)%N Hunique Hroot Hrows Hkeys) as Hloop.
  pose proof (dom_order_emit_overhead keys numeric rows Hunique Hroot Hrows) as Hsetup.
  pose proof (dom_order_emit_fuel_bits (lt_numeric_limit numeric)) as Hfuel.
  set (mass := N.of_nat (dom_lt_row_mass keys rows + length keys + 1)).
  set (w := N.of_nat (width + 1)) in *.
  assert (Hmass : (1 <= mass)%N) by (unfold mass; lia).
  assert (Hw : (1 <= w)%N) by (unfold w; lia).
  assert (Hcredit : (N.of_nat (2 * dom_lt_row_mass keys rows + 3 * length keys + 3) <=
    3 * mass)%N) by (unfold mass; lia).
  assert (Hkeys_mass : (N.of_nat (length keys + 1) <= mass)%N)
    by (unfold mass; lia).
  set (budget := (mass * w)%N).
  assert (Hwidth_budget : (w <= budget)%N).
  { unfold budget. replace w with (1 * w)%N at 1 by ring. now apply N.mul_le_mono_r. }
  assert (Hmass_budget : (mass <= budget)%N).
  { unfold budget. replace mass with (mass * 1)%N at 1 by ring. now apply N.mul_le_mono_l. }
  assert (Hcore : (((128 * (PTrieT.c_trie + 1) + c_loopN) * w) *
    N.of_nat (2 * dom_lt_row_mass keys rows + 3 * length keys + 3) <=
    (384 * (PTrieT.c_trie + 1) + 3 * c_loopN) * budget)%N).
  { replace ((384 * (PTrieT.c_trie + 1) + 3 * c_loopN) * budget)%N with
      (((128 * (PTrieT.c_trie + 1) + c_loopN) * w) * (3 * mass))%N
      by (unfold budget; ring).
    now apply N.mul_le_mono_l. }
  assert (Hfuel_budget : (c_loopN *
    N.of_nat (N.size_nat (N.double (lt_numeric_limit numeric) + 3)%N + 1) <=
    4 * c_loopN * budget)%N).
  { assert (Hbits : N.size_nat (N.double (lt_numeric_limit numeric) + 3)%N + 1 <=
      4 * (width + 1)) by lia.
    apply time_of_nat_le in Hbits. rewrite Nat2N.inj_mul in Hbits.
    change (N.of_nat 4) with 4%N in Hbits. fold w in Hbits.
    eapply N.le_trans with (c_loopN * (4 * w))%N; [now apply N.mul_le_mono_l|].
    replace (c_loopN * (4 * w))%N with ((4 * c_loopN) * w)%N by ring.
    now apply N.mul_le_mono_l. }
  assert (Hsetup_budget : (64 * N.of_nat (N.size_nat (lt_numeric_limit numeric) + 1) +
    4 * N.of_nat (length keys + 1) <= 68 * budget)%N).
  { assert (Hlimit_width : (N.of_nat (N.size_nat (lt_numeric_limit numeric) + 1) <= w)%N)
      by (unfold w; apply time_of_nat_le; lia).
    clearbody budget. clear -Hlimit_width Hwidth_budget Hkeys_mass Hmass_budget. lia. }
  assert (Hloop_paid : (T_loopN (dom_order_emit_step (lt_numeric_vertex numeric) rows)
    (T_dom_order_emit_step (lt_numeric_vertex numeric) rows)
    (N.double (lt_numeric_limit numeric) + 3)%N (DomOrderEmitState [1%N] Empty []) <=
    (384 * (PTrieT.c_trie + 1) + 7 * c_loopN) * budget)%N).
  { eapply N.le_trans; [exact Hloop|].
    replace ((384 * (PTrieT.c_trie + 1) + 7 * c_loopN) * budget)%N with
      ((384 * (PTrieT.c_trie + 1) + 3 * c_loopN) * budget + 4 * c_loopN * budget)%N by ring.
    now apply N.add_le_mono. }
  rewrite Nat2N.inj_mul. fold mass w budget.
  unfold dom_order_emit_coefficient.
  clearbody budget. clear -Hloop_paid Hsetup Hsetup_budget. nia.
Qed.

(** The explicit-fuel pass preserves numeric ranges even if it returns a partial removal list. *)
Lemma dom_order_removal_records_range bound limit parents order sources :
  dom_lt_trie_all (fun value => (value <= bound)%N) parents ->
  Forall (fun value => (value <= bound)%N) order ->
  dom_order_sources_range bound sources ->
  Forall (fun entry => let '(v, a, w) := entry in (v <= bound /\ a <= bound /\ w <= bound)%N)
    (dom_order_removal limit parents order sources).
Proof.
  intros Hparents Horder [Hblue Hred]. unfold dom_order_removal.
  set (children := filter (fun v => match trie_get (dom_lt_key v) parents with
    None => false | Some _ => true end) order).
  assert (Hchildren : Forall (fun value => (value <= bound)%N) children).
  { apply Forall_forall. intros value Hin. unfold children in Hin.
    apply filter_In in Hin as [Hin Hkept].
    now apply Forall_forall with (x := value) in Horder. }
  set (initial := DomOrderRemovalState
    (dom_source_initial parents (source_blue sources) children)
    (dom_source_initial parents (source_red sources) children)
    (fold_left (fun active v => PTrieCode.set (dom_lt_key v) true active) children Empty)
    children children []).
  assert (Hinitial : dom_order_removal_range bound initial).
  { unfold initial. apply dom_order_removal_range_make.
    - exact (dom_source_initial_range bound parents (source_blue sources) children Hblue Hchildren).
    - exact (dom_source_initial_range bound parents (source_red sources) children Hred Hchildren).
    - exact Hchildren.
    - exact Hchildren.
    - constructor. }
  pose proof (dom_lt_loop_invariant (dom_order_remove_step parents)
    (dom_order_removal_range bound)
    (Forall (fun entry => let '(v, a, w) := entry in
      (v <= bound /\ a <= bound /\ w <= bound)%N))
    (N.double (N.double (N.double (N.double limit))) + 3)%N initial) as Hloop.
  specialize (Hloop ltac:(intros st next Hst Hstep;
    pose proof (dom_order_remove_step_range bound parents st Hparents Hst) as Hnext;
    rewrite Hstep in Hnext; exact Hnext)).
  specialize (Hloop ltac:(intros st result Hst Hstep;
    pose proof (dom_order_remove_step_range bound parents st Hparents Hst) as Hresult;
    rewrite Hstep in Hresult; exact Hresult) Hinitial).
  destruct (loopN (dom_order_remove_step parents)
    (N.double (N.double (N.double (N.double limit))) + 3)%N initial) as [st|result].
  - exact (proj2 (proj2 (proj2 (proj2 Hloop)))).
  - exact Hloop.
Qed.

(** * Sorting all child rows *)

(** Pointwise callback bounds remain valid after summing a finite list. *)
Lemma dom_order_sum_cost_le {A : Type} (cost budget : A -> N) items :
  (forall item, (cost item <= budget item)%N) ->
  (fold_right N.add 0 (map cost items) <=
    fold_right N.add 0 (map budget items))%N.
Proof.
  intro Hcost. induction items as [|item rest IH]; cbn [map fold_right].
  - apply N.le_refl.
  - apply N.add_le_mono; [apply Hcost|exact IH].
Qed.

(** The public filter-sum contract can use any upper bound on each map callback. *)
Lemma dom_order_map_time_bound {A B : Type} (f : A -> B) (T_f cost : A -> N) rows :
  (forall item, (T_f item <= cost item)%N) ->
  (PTrieT.T_map f T_f rows <= (PTrieT.k_filter + 1) *
    (N.of_nat (PTrie.nodes rows + 1) +
      N.of_nat (length (PTrieCode.elements rows)) +
      fold_right N.add 0 (map (fun ka => cost (snd ka)) (PTrieCode.elements rows)) + 1))%N.
Proof.
  intro Hcost. eapply N.le_trans; [apply dom_order_map_time_sum|].
  apply N.mul_le_mono_l.
  pose proof (dom_order_sum_cost_le (fun ka => T_f (snd ka))
    (fun ka => cost (snd ka)) (PTrieCode.elements rows)
    (fun ka => Hcost (snd ka))) as Hsum. lia.
Qed.

(** The row map charges its actual inline callback by the named callback's summed bound. *)
Lemma dom_order_sorted_rows_wrapper_clock order parents positions :
  (T_dom_order_sorted_rows order parents positions <=
    4 + List.T_fold_left (dom_order_child_add parents) (T_dom_order_child_add parents)
      order Empty +
    (PTrieT.k_filter + 1) *
      (N.of_nat (PTrie.nodes (fold_left (dom_order_child_add parents) order Empty) + 1) +
        N.of_nat (length (PTrieCode.elements (fold_left (dom_order_child_add parents) order Empty))) +
        fold_right N.add 0 (map (fun ka => T_dom_order_sort_row positions (snd ka))
          (PTrieCode.elements (fold_left (dom_order_child_add parents) order Empty))) + 1))%N.
Proof.
  unfold T_dom_order_sorted_rows. time_simpl.
  lazymatch goal with
  | |- context[@PTrieT.T_map ?A ?B ?f ?T_f ?rows] =>
      pose proof (@dom_order_map_time_bound A B f T_f
        (T_dom_order_sort_row positions) rows) as Hmap
  end.
  specialize (Hmap ltac:(intro row; unfold T_dom_order_sort_row; time_simpl; lia)).
  change (fun (current : ptrie (list N)) (vertex : N) =>
    T_dom_order_child_add parents current vertex) with (T_dom_order_child_add parents).
  lia.
Qed.

(** Every binding of the child map has at most the original number of occurrences. *)
Lemma dom_order_children_binding_length order parents key row :
  trie_get key (fold_left (dom_order_child_add parents) order Empty) = Some row ->
  length row <= length order.
Proof.
  intro Hget.
  pose proof (dom_order_children_mass [key] parents order
    ltac:(constructor; [intro Hbad; contradiction|constructor])) as Hmass.
  unfold dom_lt_row_mass in Hmass. cbn [fold_right] in Hmass. rewrite Hget in Hmass. lia.
Qed.

(** Total row cells occupy at most the original occurrence budget. *)
Lemma dom_order_rows_cell_budget count levels width mass :
  mass <= count ->
  (N.of_nat (levels * width) * N.of_nat mass <=
    N.of_nat ((count + 1) * levels * width))%N.
Proof.
  intro Hmass. rewrite <- Nat2N.inj_mul. apply time_of_nat_le.
  replace ((count + 1) * levels * width) with ((levels * width) * (count + 1)) by ring.
  apply Nat.mul_le_mono_l. lia.
Qed.

(** Skeleton and per-binding costs fit alongside the per-cell sorting cost. *)
Lemma dom_order_sorted_rows_budget filter_unit row_unit child_unit budget nodes bindings cells
    callbacks map_clock child_clock total_clock :
  (1 <= budget)%N -> (nodes <= budget)%N -> (bindings <= nodes)%N -> (cells <= budget)%N ->
  (callbacks <= row_unit * cells + 16 * bindings)%N ->
  (map_clock <= (filter_unit + 1) * ((nodes + 1) + bindings + callbacks + 1))%N ->
  (child_clock <= child_unit * budget)%N ->
  (total_clock <= 4 + child_clock + map_clock)%N ->
  (total_clock <= ((filter_unit + 1) * (row_unit + 20) + child_unit + 4) * budget)%N.
Proof.
  intros Hpositive Hnodes Hbindings Hcells Hcallbacks Hmap Hchild Htotal.
  assert (Hcallback_budget : (callbacks <= row_unit * budget + 16 * budget)%N).
  { eapply N.le_trans; [exact Hcallbacks|]. apply N.add_le_mono.
    - now apply N.mul_le_mono_l.
    - apply N.mul_le_mono_l. lia. }
  assert (Hinside : ((nodes + 1) + bindings + callbacks + 1 <=
    (row_unit + 20) * budget)%N).
  { rewrite N.mul_add_distr_r. lia. }
  assert (Hmap_budget : (map_clock <= (filter_unit + 1) * ((row_unit + 20) * budget))%N).
  { eapply N.le_trans; [exact Hmap|]. now apply N.mul_le_mono_l. }
  replace (((filter_unit + 1) * (row_unit + 20) + child_unit + 4) * budget)%N with
    ((filter_unit + 1) * ((row_unit + 20) * budget) + child_unit * budget + 4 * budget)%N by ring.
  clear -Hpositive Hmap_budget Hchild Htotal. lia.
Qed.

Definition dom_order_sorted_rows_coefficient : N :=
  ((PTrieT.k_filter + 1) * (dom_order_sort_row_coefficient + 20) +
    128 * (PTrieT.c_trie + 1) + 4)%N.

(** Sorting the child forest charges its total cells once per logarithmic recursion level. *)
Lemma dom_order_sorted_rows_time width order parents positions :
  Forall (dom_order_merge_operand width positions) order ->
  dom_lt_trie_all (fun parent => N.size_nat parent <= width) parents ->
  (T_dom_order_sorted_rows order parents positions <= dom_order_sorted_rows_coefficient *
    N.of_nat ((length order + 1) * (Nat.log2 (length order) + 1) * (width + 1)))%N.
Proof.
  intros Horder Hparents.
  set (rows := fold_left (dom_order_child_add parents) order Empty).
  set (levels := Nat.log2 (length order) + 1).
  set (budget := N.of_nat ((length order + 1) * levels * (width + 1))).
  assert (Hvertices : Forall (fun vertex => N.size_nat vertex <= width) order).
  { apply Forall_forall. intros vertex Hin.
    apply Forall_forall with (x := vertex) in Horder; [exact (proj1 Horder)|exact Hin]. }
  pose proof (dom_order_child_fold_clock width parents Empty order Hvertices Hparents) as Hchild.
  pose proof (dom_order_child_fold_nodes parents order Empty (width + 1)) as Hnodes.
  specialize (Hnodes ltac:(intros vertex parent Hin Hget;
    pose proof (Hparents (dom_lt_key vertex) parent Hget) as Hparent;
    change (N.size_nat parent <= width) in Hparent;
    pose proof (dom_lt_key_width parent); lia)).
  change (PTrie.nodes rows <= length order * (width + 1)) in Hnodes.
  pose proof (PTrieT.F4_bindings (list N) rows) as Hbindings.
  change (length (PTrieCode.elements rows) <= PTrie.nodes rows) in Hbindings.
  pose proof (dom_order_children_elements_mass parents order) as Hmass. fold rows in Hmass.
  assert (Hrow_predicate : dom_lt_trie_all (Forall (dom_order_merge_operand width positions)) rows).
  { unfold rows. apply dom_order_child_fold_forall; [exact Horder|apply dom_lt_trie_all_empty]. }
  pose proof (dom_order_sum_cells
    (fun entry : positive * list N => T_dom_order_sort_row positions (snd entry))
    (fun entry : positive * list N => length (snd entry)) (PTrieCode.elements rows)
    (dom_order_sort_row_coefficient * N.of_nat (levels * (width + 1)))%N 16%N) as Hcallbacks.
  specialize (Hcallbacks ltac:(intros [key row] Hin; cbn [snd];
    apply PTrie.elements_spec in Hin;
    apply dom_order_sort_row_time;
    [exact (dom_order_children_binding_length order parents key row Hin)|
     exact (Hrow_predicate key row Hin)])).
  pose proof (dom_order_sorted_rows_wrapper_clock order parents positions) as Hraw.
  fold rows in Hraw.
  assert (Hpositive : (1 <= budget)%N).
  { unfold budget, levels. clear -order width. rewrite !Nat2N.inj_mul.
    change (1 * 1 * 1 <= N.of_nat (length order + 1) *
      N.of_nat (Nat.log2 (length order) + 1) * N.of_nat (width + 1))%N.
    apply N.mul_le_mono; [apply N.mul_le_mono; lia|lia]. }
  assert (Hnodes_budget : (N.of_nat (PTrie.nodes rows) <= budget)%N).
  { unfold budget. apply time_of_nat_le. eapply Nat.le_trans; [exact Hnodes|].
    apply Nat.mul_le_mono_r.
    replace (length order) with (length order * 1) at 1 by lia.
    apply Nat.mul_le_mono; [lia|unfold levels; lia]. }
  assert (Hcells_budget :
    (N.of_nat (levels * (width + 1)) *
      N.of_nat (fold_right (fun entry total => (length (snd entry) + total)%nat) 0%nat
        (PTrieCode.elements rows)) <= budget)%N).
  { unfold budget. now apply dom_order_rows_cell_budget. }
  assert (Hchild_budget :
    (List.T_fold_left (dom_order_child_add parents) (T_dom_order_child_add parents) order Empty <=
      128 * (PTrieT.c_trie + 1) * budget)%N).
  { eapply N.le_trans; [exact Hchild|]. apply N.mul_le_mono_l.
    unfold budget. apply time_of_nat_le. apply Nat.mul_le_mono_r.
    replace (length order + 1) with ((length order + 1) * 1) at 1 by lia.
    apply Nat.mul_le_mono_l. unfold levels. lia. }
  fold levels. fold budget. unfold dom_order_sorted_rows_coefficient.
  eapply dom_order_sorted_rows_budget with
    (nodes := N.of_nat (PTrie.nodes rows))
    (bindings := N.of_nat (length (PTrieCode.elements rows)))
    (cells := (N.of_nat (levels * (width + 1)) *
      N.of_nat (fold_right (fun entry total => (length (snd entry) + total)%nat) 0%nat
        (PTrieCode.elements rows)))%N)
    (map_clock := ((PTrieT.k_filter + 1) *
      (N.of_nat (PTrie.nodes rows + 1) + N.of_nat (length (PTrieCode.elements rows)) +
        fold_right N.add 0 (map (fun entry => T_dom_order_sort_row positions (snd entry))
          (PTrieCode.elements rows)) + 1))%N).
  - exact Hpositive.
  - exact Hnodes_budget.
  - now apply time_of_nat_le.
  - exact Hcells_budget.
  - rewrite N.mul_assoc. exact Hcallbacks.
  - rewrite Nat2N.inj_add. change (N.of_nat 1) with 1%N. apply N.le_refl.
  - exact Hchild_budget.
  - exact Hraw.
Qed.

(** * Raw assembly of the ordering result *)

(** The polynomial operand budget contains all linear counters and the two sentinel ranks. *)
Lemma dom_order_linear_value_polynomial (bound value : N) :
  (value <= 4 * bound + 4)%N -> (value <= 8 * (bound + 1) * (bound + 1))%N.
Proof.
  intro Hvalue. nia.
Qed.

(** A common polynomial width also covers every required linear counter. *)
Lemma dom_order_linear_value_width bound width value :
  (forall n, (n <= 8 * (bound + 1) * (bound + 1))%N -> N.size_nat n <= width) ->
  (value <= 4 * bound + 4)%N -> N.size_nat value <= width.
Proof.
  intros Hwidth Hvalue. apply Hwidth. now apply dom_order_linear_value_polynomial.
Qed.

(** Bounded parent payloads inherit the common polynomial numeric width. *)
Lemma dom_order_table_width bound width (table : ptrie N) :
  (forall n, (n <= 8 * (bound + 1) * (bound + 1))%N -> N.size_nat n <= width) ->
  dom_lt_trie_all (fun value => (value <= bound)%N) table ->
  dom_lt_trie_all (fun value => N.size_nat value <= width) table.
Proof.
  intros Hwidth Htable key value Hget.
  eapply dom_order_linear_value_width; [exact Hwidth|].
  pose proof (Htable key value Hget) as Hbound.
  change (value <= bound)%N in Hbound. lia.
Qed.

(** The result wrapper adds only fixed projections to its five unchanged ordering phases. *)
Lemma dom_order_result_phase_clocks result :
  let numeric := result_numeric result in
  let semi := result_semi result in
  let bucket := result_bucket result in
  let parents := result_parent result in
  let sources := dom_order_source_maps numeric (lt_semis semi) (lt_minimizer semi)
    (lt_relative bucket) parents in
  let removed := dom_order_removal (lt_numeric_limit numeric) parents
    (lt_numeric_order numeric) sources in
  let positions := dom_anchor_order parents removed in
  let rows := dom_order_sorted_rows (lt_numeric_order numeric) parents positions in
  (T_dom_order_of_result result <=
    T_dom_order_source_maps numeric (lt_semis semi) (lt_minimizer semi) (lt_relative bucket) parents +
    T_dom_order_removal (lt_numeric_limit numeric) parents (lt_numeric_order numeric) sources +
    T_dom_anchor_order parents removed +
    T_dom_order_sorted_rows (lt_numeric_order numeric) parents positions +
    T_dom_order_emit numeric rows + 64)%N.
Proof.
  intros numeric semi bucket parents sources removed positions rows.
  unfold T_dom_order_of_result. time_simpl.
  fold numeric semi bucket parents sources removed positions rows. lia.
Qed.

Definition dom_order_body_budget (count predecessors width : nat) : nat :=
  (count + predecessors + 1) * (Nat.log2 count + 1) * (width + 1).

(** Every raw ordering budget reserves a unit for fixed wrapper work, even on empty inputs. *)
Lemma dom_order_body_budget_positive count predecessors width :
  1 <= dom_order_body_budget count predecessors width.
Proof.
  unfold dom_order_body_budget.
  change (1 * 1 * 1 <= (count + predecessors + 1) * (Nat.log2 count + 1) * (width + 1)).
  apply Nat.mul_le_mono; [apply Nat.mul_le_mono; lia|lia].
Qed.

(** A linear pass over the vertex inventory fits the complete raw ordering budget. *)
Lemma dom_order_body_budget_linear count predecessors width :
  (count + 1) * (width + 1) <= dom_order_body_budget count predecessors width.
Proof.
  unfold dom_order_body_budget. apply Nat.mul_le_mono_r.
  replace (count + 1) with ((count + 1) * 1) at 1 by lia.
  apply Nat.mul_le_mono; lia.
Qed.

(** The logarithmic child-sort budget fits after adding the predecessor-row allowance. *)
Lemma dom_order_body_budget_rows count predecessors width :
  (count + 1) * (Nat.log2 count + 1) * (width + 1) <=
    dom_order_body_budget count predecessors width.
Proof.
  unfold dom_order_body_budget. apply Nat.mul_le_mono_r.
  apply Nat.mul_le_mono_r. lia.
Qed.

(** A finite output universe with two sentinels costs at most three vertex allowances. *)
Lemma dom_order_body_budget_emit count predecessors width row_mass :
  row_mass <= count ->
  (row_mass + (count + 2) + 1) * (width + 1) <=
    3 * dom_order_body_budget count predecessors width.
Proof.
  intro Hmass.
  eapply Nat.le_trans with (3 * ((count + 1) * (width + 1))).
  - replace (3 * ((count + 1) * (width + 1))) with
      ((3 * (count + 1)) * (width + 1)) by ring.
    apply Nat.mul_le_mono_r. lia.
  - apply Nat.mul_le_mono_l. apply dom_order_body_budget_linear.
Qed.

(** * Common budgets for the independent ordering passes *)

(** Linear rows, numbering cells and logarithmic index work share one global product. *)
Lemma dom_order_source_product_budgets (count predecessors levels width : N) :
  (1 <= levels)%N -> (1 <= width)%N ->
  let budget := ((count + predecessors + 1) * levels * width)%N in
  ((count + 1) * width <= budget)%N /\
  ((2 * count + 3) * width <= 3 * budget)%N /\
  ((2 * count + 1) * (levels + 1) * width <= 4 * budget)%N /\
  ((predecessors + (levels + 1) * count + 1) * width <= 2 * budget)%N.
Proof.
  intros Hlevels Hwidth budget.
  set (span := (count + predecessors + 1)%N).
  assert (Hspan : (count + 1 <= span)%N) by (unfold span; lia).
  assert (Hspan_levels : (span <= span * levels)%N) by nia.
  assert (Hlinear : ((count + 1) * width <= budget)%N).
  { unfold budget. fold span. apply N.mul_le_mono_r. lia. }
  split; [exact Hlinear|].
  assert (Hnumber_factor : (2 * count + 3 <= 3 * (count + 1))%N) by lia.
  assert (Hnumber : ((2 * count + 3) * width <= 3 * budget)%N).
  { eapply N.le_trans with ((3 * (count + 1)) * width)%N;
      [now apply N.mul_le_mono_r|].
    replace (3 * (count + 1) * width)%N with (3 * ((count + 1) * width))%N by ring.
    now apply N.mul_le_mono_l. }
  split; [exact Hnumber|].
  assert (Hindex_count : (2 * count + 1 <= 2 * span)%N) by lia.
  assert (Hindex_levels : (levels + 1 <= 2 * levels)%N) by lia.
  assert (Hindex_factor : ((2 * count + 1) * (levels + 1) <= 4 * (span * levels))%N).
  { replace (4 * (span * levels))%N with ((2 * span) * (2 * levels))%N by ring.
    now apply N.mul_le_mono. }
  assert (Hindex : ((2 * count + 1) * (levels + 1) * width <= 4 * budget)%N).
  { replace (4 * budget)%N with ((4 * (span * levels)) * width)%N
      by (unfold budget, span; ring).
    now apply N.mul_le_mono_r. }
  split; [exact Hindex|].
  assert (Hplain : (predecessors + 1 <= (predecessors + 1) * levels)%N) by nia.
  assert (Hdouble : ((levels + 1) * count <= 2 * levels * count)%N) by nia.
  assert (Hcolour_factor : (predecessors + (levels + 1) * count + 1 <=
    2 * (span * levels))%N) by (unfold span; nia).
  replace (2 * budget)%N with ((2 * (span * levels)) * width)%N
    by (unfold budget, span; ring).
  now apply N.mul_le_mono_r.
Qed.

(** Adding the five source-construction phases preserves the linear-logarithmic budget. *)
Lemma dom_order_source_maps_budget (trie_coefficient number_coefficient count predecessors
    levels width child_work number_work index_work colour_work setup_work total_work : N) :
  (1 <= levels)%N -> (1 <= width)%N ->
  (child_work <= 128 * (trie_coefficient + 1) * ((count + 1) * width))%N ->
  (number_work <= number_coefficient * ((2 * count + 3) * width))%N ->
  (index_work <= 2048 * (trie_coefficient + 1) *
    ((2 * count + 1) * (levels + 1) * width))%N ->
  (colour_work <= 2048 * (trie_coefficient + 1) *
    ((predecessors + (levels + 1) * count + 1) * width))%N ->
  (setup_work <= 64 * ((count + 1) * width))%N ->
  (total_work <= child_work + number_work + index_work + colour_work + setup_work)%N ->
  (total_work <= (3 * number_coefficient + 16384 * (trie_coefficient + 1) + 64) *
    ((count + predecessors + 1) * levels * width))%N.
Proof.
  intros Hlevels Hwidth Hchild Hnumber Hindex Hcolour Hsetup Htotal.
  pose proof (dom_order_source_product_budgets count predecessors levels width Hlevels Hwidth)
    as [Hlinear [Hnumber_product [Hindex_product Hcolour_product]]].
  set (budget := ((count + predecessors + 1) * levels * width)%N) in *.
  assert (Hchild_paid : (child_work <= 128 * (trie_coefficient + 1) * budget)%N).
  { eapply N.le_trans; [exact Hchild|]. now apply N.mul_le_mono_l. }
  assert (Hnumber_paid : (number_work <= 3 * number_coefficient * budget)%N).
  { eapply N.le_trans; [exact Hnumber|].
    replace (3 * number_coefficient * budget)%N with
      (number_coefficient * (3 * budget))%N by ring. now apply N.mul_le_mono_l. }
  assert (Hindex_paid : (index_work <= 8192 * (trie_coefficient + 1) * budget)%N).
  { eapply N.le_trans; [exact Hindex|].
    replace (8192 * (trie_coefficient + 1) * budget)%N with
      ((2048 * (trie_coefficient + 1)) * (4 * budget))%N by ring.
    now apply N.mul_le_mono_l. }
  assert (Hcolour_paid : (colour_work <= 4096 * (trie_coefficient + 1) * budget)%N).
  { eapply N.le_trans; [exact Hcolour|].
    replace (4096 * (trie_coefficient + 1) * budget)%N with
      ((2048 * (trie_coefficient + 1)) * (2 * budget))%N by ring.
    now apply N.mul_le_mono_l. }
  assert (Hsetup_paid : (setup_work <= 64 * budget)%N).
  { eapply N.le_trans; [exact Hsetup|]. now apply N.mul_le_mono_l. }
  clearbody budget.
  clear -Htotal Hchild_paid Hnumber_paid Hindex_paid Hcolour_paid Hsetup_paid. nia.
Qed.

(** A constant number of projection calls fits any positive common phase budget. *)
Lemma dom_order_phase_sum_budget (budget source_coefficient removal_coefficient anchor_coefficient
    rows_coefficient emit_coefficient source_work removal_work anchor_work rows_work emit_work
    total_work : N) :
  (1 <= budget)%N ->
  (source_work <= source_coefficient * budget)%N ->
  (removal_work <= removal_coefficient * budget)%N ->
  (anchor_work <= anchor_coefficient * budget)%N ->
  (rows_work <= rows_coefficient * budget)%N ->
  (emit_work <= 3 * emit_coefficient * budget)%N ->
  (total_work <= source_work + removal_work + anchor_work + rows_work + emit_work + 64)%N ->
  (total_work <= (source_coefficient + removal_coefficient + anchor_coefficient + rows_coefficient +
    3 * emit_coefficient + 64) * budget)%N.
Proof.
  intros Hbudget Hsource Hremove Hanchor Hrows Hemit Htotal.
  assert (Hsetup : (64 <= 64 * budget)%N) by lia.
  replace ((source_coefficient + removal_coefficient + anchor_coefficient + rows_coefficient +
    3 * emit_coefficient + 64) * budget)%N with
    (source_coefficient * budget + removal_coefficient * budget + anchor_coefficient * budget +
      rows_coefficient * budget + 3 * emit_coefficient * budget + 64 * budget)%N by ring. lia.
Qed.

(** * Final removal initialization and loop clocks *)

(** The child filter uses exactly the existing parent-membership predicate. *)
Definition dom_order_removal_keep (parents : ptrie N) (vertex : N) : bool :=
  match trie_get (dom_lt_key vertex) parents with None => false | Some _ => true end.
TimeFun dom_order_removal_keep.

(** The activation fold writes exactly the existing true flag. *)
Definition dom_order_removal_activate (active : ptrie bool) (vertex : N) : ptrie bool :=
  PTrieCode.set (dom_lt_key vertex) true active.
TimeFun dom_order_removal_activate.

Lemma dom_order_removal_filter_mono {A : Type} (predicate : A -> bool)
    (left right : A -> N) xs :
  (forall value, (left value <= right value)%N) ->
  (List.T_filter predicate left xs <= List.T_filter predicate right xs)%N.
Proof.
  intro Hclock. induction xs as [|vertex rest IH].
  - time_unfold List.T_filter. lia.
  - time_unfold List.T_filter. specialize (Hclock vertex).
    destruct (predicate vertex); lia.
Qed.

(** A filter only needs a callback bound on elements actually present in its input. *)
Lemma dom_order_removal_filter_bound {A : Type} (predicate : A -> bool)
    (clock : A -> N) xs coefficient :
  (forall value, In value xs -> (clock value <= coefficient)%N) ->
  (List.T_filter predicate clock xs <=
    (coefficient + 1) * N.of_nat (length xs) + 1)%N.
Proof.
  revert coefficient. induction xs as [|vertex rest IH]; intros coefficient Hclock.
  - time_unfold List.T_filter. cbn [length]. lia.
  - pose proof (Hclock vertex (or_introl eq_refl)) as Hhead.
    specialize (IH coefficient (fun value Hin => Hclock value (or_intror Hin))).
    time_unfold List.T_filter. cbn [length]. rewrite Nat2N.inj_succ.
    destruct (predicate vertex); lia.
Qed.

Lemma dom_order_removal_keep_clock width parents vertex :
  N.size_nat vertex <= width ->
  (T_dom_order_removal_keep parents vertex <= 8 * N.of_nat (width + 1))%N.
Proof.
  intro Hwidth. pose proof (dom_lt_time_key vertex) as Hkey.
  pose proof (dom_lt_key_width vertex) as Hbits.
  unfold T_dom_order_removal_keep. time_simpl. PTrieT.trie_get_le.
  destruct (trie_get (dom_lt_key vertex) parents); time_simpl;
    rewrite !Nat2N.inj_add in *; lia.
Qed.

(** Parent filtering is linear in the supplied order at the numeric operand width. *)
Lemma dom_order_removal_filter_clock width parents order :
  Forall (fun vertex => N.size_nat vertex <= width) order ->
  (List.T_filter (dom_order_removal_keep parents) (T_dom_order_removal_keep parents) order <=
    32 * N.of_nat ((length order + 1) * (width + 1)))%N.
Proof.
  intro Horder.
  pose proof (dom_order_removal_filter_bound (dom_order_removal_keep parents)
    (T_dom_order_removal_keep parents) order (8 * N.of_nat (width + 1))%N
    ltac:(intros vertex Hin; apply dom_order_removal_keep_clock;
      exact (proj1 (Forall_forall _ _) Horder vertex Hin))) as Hfilter.
  rewrite Nat2N.inj_mul, !Nat2N.inj_add in *. change (N.of_nat 1) with 1%N in *.
  set (count := N.of_nat (length order)) in *. set (w := N.of_nat width) in *.
  clearbody count w. clear -Hfilter. nia.
Qed.

Lemma dom_order_removal_activate_clock width active vertex :
  N.size_nat vertex <= width ->
  (T_dom_order_removal_activate active vertex <=
    32 * (PTrieT.c_trie + 1) * N.of_nat (width + 1))%N.
Proof.
  intro Hwidth. pose proof (dom_lt_time_key vertex) as Hkey.
  pose proof (dom_lt_key_width vertex) as Hbits.
  pose proof (PTrieT.T_set_le bool (dom_lt_key vertex) true active) as Hset.
  change (PTrieCode.T_set (dom_lt_key vertex) true active <=
    PTrieT.c_trie * N.of_nat (Pos.size_nat (dom_lt_key vertex) + 1))%N in Hset.
  unfold T_dom_order_removal_activate. time_simpl.
  rewrite !Nat2N.inj_add in *. clear -Hwidth Hkey Hbits Hset. nia.
Qed.

(** Activating one child uses one bounded trie update. *)
Lemma dom_order_removal_activation_clock width children active :
  Forall (fun vertex => N.size_nat vertex <= width) children ->
  (List.T_fold_left dom_order_removal_activate T_dom_order_removal_activate children active <=
    128 * (PTrieT.c_trie + 1) * N.of_nat ((length children + 1) * (width + 1)))%N.
Proof.
  intro Hchildren.
  set (unit := (32 * (PTrieT.c_trie + 1) * N.of_nat (width + 1))%N).
  pose proof (dom_time_fold_credit dom_order_removal_activate T_dom_order_removal_activate
    (fun _ => 0%N) unit children active
    ltac:(intros vertex Hin state; cbn beta; rewrite !N.add_0_r;
      apply dom_order_removal_activate_clock;
      exact (proj1 (Forall_forall _ _) Hchildren vertex Hin))) as Hfold.
  cbn beta in Hfold. rewrite !N.add_0_r in Hfold.
  assert (Hunit : (1 <= unit)%N).
  { unfold unit. rewrite Nat2N.inj_add. nia. }
  rewrite Nat2N.inj_mul, Nat2N.inj_add.
  change (N.of_nat 1) with 1%N.
  replace (128 * (PTrieT.c_trie + 1) *
      ((N.of_nat (length children) + 1) * N.of_nat (width + 1)))%N with
    (4 * unit * (N.of_nat (length children) + 1))%N by (unfold unit; ring).
  clearbody unit. clear -Hfold Hunit. nia.
Qed.

Local Opaque dom_order_derived T_dom_order_derived.
Local Transparent dom_order_colour T_dom_order_colour.

(** * Source colouring with separate predecessor and search charges *)

(** Identity-default lookup preserves any predicate satisfied by its fallback and stored values. *)
Lemma dom_order_identity_property (P : N -> Prop) table vertex :
  P vertex -> dom_lt_trie_all P table -> P (dom_lt_identity table vertex).
Proof.
  intros Hvertex Htable. unfold dom_lt_identity.
  destruct (trie_get (dom_lt_key vertex) table) as [value|] eqn:Hget;
    [now apply (Htable (dom_lt_key vertex))|exact Hvertex].
Qed.

(** One colouring callback scans one predecessor row and performs at most two supplied searches. *)
Lemma dom_order_colour_base_clock width search_work numeric semis minimizer relative
    parents indexes walk st vertex :
  N.size_nat vertex <= width ->
  N.size_nat (dom_lt_identity relative vertex) <= width ->
  N.size_nat (dom_lt_identity semis vertex) <= width ->
  dom_lt_trie_all (fun parent => N.size_nat parent <= width) parents ->
  (forall parent, trie_get (dom_lt_key vertex) parents = Some parent ->
    (T_dom_order_derived indexes walk parent (dom_lt_identity (lt_numeric_parent numeric) vertex)
      <= search_work)%N /\
    (T_dom_order_derived indexes walk parent (dom_lt_identity minimizer vertex)
      <= search_work)%N) ->
  (T_dom_order_colour numeric semis minimizer relative parents indexes walk st vertex <=
    256 * (PTrieT.c_trie + 1) * N.of_nat (width + 1) + 2 * search_work +
      (N.of_nat (width + 1) + 2) *
        N.of_nat (length (dom_order_row (lt_numeric_pred numeric) vertex)))%N.
Proof.
  intros Hvertex Hrelative Hsemi Hparents Hsearch.
  pose proof (dom_lt_time_key vertex) as Hkey.
  pose proof (dom_lt_key_width vertex) as Hkey_width.
  unfold T_dom_order_colour. time_simpl. PTrieT.trie_get_le.
  destruct (trie_get (dom_lt_key vertex) parents) as [parent|] eqn:Hparent.
  - pose proof (Hparents (dom_lt_key vertex) parent Hparent) as Hparent_width.
    change (N.size_nat parent <= width) in Hparent_width.
    destruct (Hsearch parent eq_refl) as [Hfirst Hsecond].
    pose proof (dom_lt_time_identity relative vertex) as Hrelative_read.
    pose proof (dom_lt_time_identity semis vertex) as Hsemi_read.
    pose proof (dom_lt_time_identity (lt_numeric_parent numeric) vertex) as Hparent_read.
    pose proof (dom_lt_time_identity minimizer vertex) as Hminimizer_read.
    pose proof (dom_lt_time_key (dom_lt_identity relative vertex)) as Hrelative_key.
    pose proof (dom_lt_key_width (dom_lt_identity relative vertex)) as Hrelative_bits.
    pose proof (N.T_eqb_le (dom_lt_identity semis vertex) parent) as Hcompare.
    pose proof (dom_order_row_clock (lt_numeric_pred numeric) vertex) as Hrow.
    pose proof (List.T_existsb_le (N.eqb parent) (N.T_eqb parent)
      (N.of_nat (N.size_nat parent) + 1)%N (dom_order_row (lt_numeric_pred numeric) vertex)
      (fun other => N.T_eqb_le parent other)) as Hscan.
    assert (Hscan_width : (List.T_existsb (N.eqb parent) (N.T_eqb parent)
      (dom_order_row (lt_numeric_pred numeric) vertex) <=
      (N.of_nat (width + 1) + 2) *
        N.of_nat (length (dom_order_row (lt_numeric_pred numeric) vertex)) + 1)%N).
    { eapply N.le_trans; [exact Hscan|]. apply N.add_le_mono_r.
      apply N.mul_le_mono_r. rewrite Nat2N.inj_add. clear -Hparent_width. lia. }
    clear Hscan. rename Hscan_width into Hscan.
    set (is_blue := N.eqb (dom_lt_identity semis vertex) parent ||
      match trie_get (dom_lt_key (dom_lt_identity relative vertex)) (source_colour st) with
      | Some true => true | _ => false end).
    set (direct := existsb (N.eqb parent) (dom_order_row (lt_numeric_pred numeric) vertex)).
    set (blue_value := if direct then parent else dom_order_derived indexes walk parent
      (if is_blue then dom_lt_identity minimizer vertex
       else dom_lt_identity (lt_numeric_parent numeric) vertex)).
    set (red_value := if direct then parent else dom_order_derived indexes walk parent
      (if is_blue then dom_lt_identity (lt_numeric_parent numeric) vertex
       else dom_lt_identity minimizer vertex)).
    pose proof (PTrieT.T_set_le N (dom_lt_key vertex) blue_value (source_blue st)) as Hblue_set.
    pose proof (PTrieT.T_set_le N (dom_lt_key vertex) red_value (source_red st)) as Hred_set.
    pose proof (PTrieT.T_set_le bool (dom_lt_key vertex) (negb is_blue) (source_colour st))
      as Hcolour_set.
    change (PTrieCode.T_set (dom_lt_key vertex) blue_value (source_blue st) <=
      PTrieT.c_trie * N.of_nat (Pos.size_nat (dom_lt_key vertex) + 1))%N in Hblue_set.
    change (PTrieCode.T_set (dom_lt_key vertex) red_value (source_red st) <=
      PTrieT.c_trie * N.of_nat (Pos.size_nat (dom_lt_key vertex) + 1))%N in Hred_set.
    change (PTrieCode.T_set (dom_lt_key vertex) (negb is_blue) (source_colour st) <=
      PTrieT.c_trie * N.of_nat (Pos.size_nat (dom_lt_key vertex) + 1))%N in Hcolour_set.
    assert (Hkey_budget : (N.of_nat (Pos.size_nat (dom_lt_key vertex) + 1) <=
      2 * N.of_nat (width + 1))%N).
    { rewrite !Nat2N.inj_add. clear -Hvertex Hkey_width. lia. }
    assert (Hwrite_budget : (PTrieT.c_trie * N.of_nat (Pos.size_nat (dom_lt_key vertex) + 1) <=
      2 * PTrieT.c_trie * N.of_nat (width + 1))%N).
    { replace (2 * PTrieT.c_trie * N.of_nat (width + 1))%N with
        (PTrieT.c_trie * (2 * N.of_nat (width + 1)))%N by ring.
      now apply N.mul_le_mono_l. }
    assert (Hblue_width : (PTrieCode.T_set (dom_lt_key vertex) blue_value (source_blue st) <=
      2 * PTrieT.c_trie * N.of_nat (width + 1))%N)
      by (eapply N.le_trans; [exact Hblue_set|exact Hwrite_budget]).
    assert (Hred_width : (PTrieCode.T_set (dom_lt_key vertex) red_value (source_red st) <=
      2 * PTrieT.c_trie * N.of_nat (width + 1))%N)
      by (eapply N.le_trans; [exact Hred_set|exact Hwrite_budget]).
    assert (Hcolour_width : (PTrieCode.T_set (dom_lt_key vertex) (negb is_blue) (source_colour st) <=
      2 * PTrieT.c_trie * N.of_nat (width + 1))%N)
      by (eapply N.le_trans; [exact Hcolour_set|exact Hwrite_budget]).
    clear Hblue_set Hred_set Hcolour_set.
    rename Hblue_width into Hblue_set, Hred_width into Hred_set, Hcolour_width into Hcolour_set.
    PTrieT.trie_get_le. fold is_blue direct.
    unfold blue_value, red_value in Hblue_set, Hred_set.
    destruct direct, is_blue;
      destruct (trie_get (dom_lt_key (dom_lt_identity relative vertex)) (source_colour st))
        as [[|]|]; time_simpl;
      unfold blue_value, red_value;
      change (fun other => N.T_eqb parent other) with (N.T_eqb parent);
      rewrite !Nat2N.inj_add in *;
      change (N.of_nat 1) with 1%N in *;
      set (write_budget := (PTrieT.c_trie * (N.of_nat width + 1))%N);
      set (scan_budget := ((N.of_nat width + 1 + 2) *
        N.of_nat (length (dom_order_row (lt_numeric_pred numeric) vertex)))%N) in *;
      replace (2 * PTrieT.c_trie * (N.of_nat width + 1))%N with
        (2 * write_budget)%N in Hblue_set, Hred_set, Hcolour_set by (unfold write_budget; ring);
      replace (256 * (PTrieT.c_trie + 1) * (N.of_nat width + 1))%N with
        (256 * write_budget + 256 * (N.of_nat width + 1))%N by (unfold write_budget; ring);
      clearbody write_budget scan_budget;
      clear -Hvertex Hrelative Hsemi Hkey Hkey_width Hparent_width Hfirst Hsecond
        Hrelative_read Hsemi_read Hparent_read Hminimizer_read Hrelative_key Hrelative_bits
        Hcompare Hrow Hscan Hblue_set Hred_set Hcolour_set;
      PTrieT.trie_get_le.
    all: lia.
  - time_simpl. rewrite !Nat2N.inj_add in *.
    clear -Hvertex Hkey Hkey_width. PTrieT.trie_get_le. nia.
Qed.


Local Transparent dom_order_derived T_dom_order_derived.

(** * Active-source credit for stale inverse rows *)

Definition dom_order_live (weight : positive -> nat) (keys : list positive)
    (active : ptrie bool) : nat :=
  fold_right (fun key total =>
    (match trie_get key active with Some true => weight key | _ => 0 end) + total) 0 keys.

Definition dom_order_live_rows keys active (rows : ptrie (list N)) : nat :=
  dom_order_live
    (fun key => length (match trie_get key rows with None => [] | Some row => row end)) keys active.

(** A flag update outside the finite domain changes no live credit. *)
Lemma dom_order_live_absent weight keys active key flag :
  ~ In key keys ->
  dom_order_live weight keys (PTrieCode.set key flag active) = dom_order_live weight keys active.
Proof.
  induction keys as [|head rest IH]; intro Houtside; [reflexivity|].
  unfold dom_order_live in *. cbn [fold_right].
  rewrite PTrie.get_set_other by (intro Heq; apply Houtside; now left).
  rewrite IH; [reflexivity|]. intro Hin. apply Houtside. now right.
Qed.

(** Retiring a live key consumes exactly its weight from a distinct inventory. *)
Lemma dom_order_live_retire weight keys active key :
  NoDup keys -> In key keys -> trie_get key active = Some true ->
  dom_order_live weight keys (PTrieCode.set key false active) + weight key =
    dom_order_live weight keys active.
Proof.
  intro Hunique. induction Hunique as [|head rest Hfresh Hunique IH];
    intros Hin Hactive; [contradiction|].
  destruct Hin as [<-|Hin].
  - cbn [dom_order_live fold_right]. rewrite PTrie.get_set_same, Hactive.
    change (dom_order_live weight rest (PTrieCode.set head false active) + weight head =
      weight head + dom_order_live weight rest active).
    rewrite dom_order_live_absent by exact Hfresh. lia.
  - assert (Hdifferent : head <> key) by (intro Heq; subst head; contradiction).
    specialize (IH Hin Hactive).
    change ((match trie_get head (PTrieCode.set key false active) with
      | Some true => weight head | _ => 0 end) +
        dom_order_live weight rest (PTrieCode.set key false active) + weight key =
      (match trie_get head active with Some true => weight head | _ => 0 end) +
        dom_order_live weight rest active).
    rewrite PTrie.get_set_other by exact Hdifferent.
    rewrite <- Nat.add_assoc, IH. reflexivity.
Qed.

(** Live unit credit never exceeds the original finite domain. *)
Lemma dom_order_live_count_bound keys active : dom_order_live (fun _ => 1%nat) keys active <= length keys.
Proof.
  induction keys as [|key rest IH]; [reflexivity|].
  unfold dom_order_live in *. cbn [fold_right length].
  destruct (trie_get key active) as [[|]|]; lia.
Qed.

(** Live row credit is bounded by the total row mass of the same finite domain. *)
Lemma dom_order_live_rows_bound keys active rows :
  dom_order_live_rows keys active rows <= dom_lt_row_mass keys rows.
Proof.
  induction keys as [|key rest IH]; [reflexivity|].
  unfold dom_order_live_rows, dom_order_live, dom_lt_row_mass in *.
  cbn [fold_right]. destruct (trie_get key active) as [[|]|]; lia.
Qed.

(** Agreement of weights on the counted keys determines live credit. *)
Lemma dom_order_live_weights weight other keys active :
  (forall key, In key keys -> weight key = other key) ->
  dom_order_live weight keys active = dom_order_live other keys active.
Proof.
  induction keys as [|head rest IH]; intro Hweights; [reflexivity|].
  unfold dom_order_live in *. cbn [fold_right].
  rewrite Hweights by now left.
  rewrite IH; [reflexivity|]. intros key Hin. apply Hweights. now right.
Qed.

(** An inverse-row update outside the counted domain changes no live row credit. *)
Lemma dom_order_live_rows_absent keys active rows key row :
  ~ In key keys -> dom_order_live_rows keys active (PTrieCode.set key row rows) =
    dom_order_live_rows keys active rows.
Proof.
  intro Houtside. unfold dom_order_live_rows. apply dom_order_live_weights.
  intros other Hother. rewrite PTrie.get_set_other; [reflexivity|].
  intro Heq. subst other. contradiction.
Qed.

(** Appending an inverse entry adds at most one live credit, even at an already retired source. *)
Lemma dom_order_live_rows_push keys active rows key value :
  NoDup keys ->
  dom_order_live_rows keys active (PTrieCode.set key
    (value :: match trie_get key rows with None => [] | Some row => row end) rows) <=
    S (dom_order_live_rows keys active rows).
Proof.
  intro Hunique. induction Hunique as [|head rest Hfresh Hunique IH]; [cbn; lia|].
  destruct (Pos.eq_dec head key) as [->|Hdifferent].
  - unfold dom_order_live_rows, dom_order_live. cbn [fold_right].
    rewrite PTrie.get_set_same. cbn [length].
    change ((match trie_get key active with
      | Some true => S (length (match trie_get key rows with None => [] | Some row => row end))
      | _ => 0
      end) + dom_order_live_rows rest active (PTrieCode.set key
        (value :: match trie_get key rows with None => [] | Some row => row end) rows) <=
      S ((match trie_get key active with
      | Some true => length (match trie_get key rows with None => [] | Some row => row end)
      | _ => 0
      end) + dom_order_live_rows rest active rows)).
    rewrite dom_order_live_rows_absent by exact Hfresh.
    destruct (trie_get key active) as [[|]|]; lia.
  - change ((match trie_get head active with
      | Some true => length (match trie_get head (PTrieCode.set key
          (value :: match trie_get key rows with None => [] | Some row => row end) rows) with
          None => [] | Some row => row end)
      | _ => 0 end) + dom_order_live_rows rest active (PTrieCode.set key
        (value :: match trie_get key rows with None => [] | Some row => row end) rows) <=
      S ((match trie_get head active with
        | Some true => length (match trie_get head rows with None => [] | Some row => row end)
        | _ => 0 end) + dom_order_live_rows rest active rows)).
    rewrite PTrie.get_set_other by exact Hdifferent.
    rewrite <- Nat.add_succ_r. now apply Nat.add_le_mono_l.
Qed.

(** One queried row is part of any finite row inventory containing its key. *)
Lemma dom_order_row_mass_member {A : Type} keys (rows : ptrie (list A)) key :
  In key keys ->
  length (match trie_get key rows with None => [] | Some row => row end) <=
    dom_lt_row_mass keys rows.
Proof.
  induction keys as [|head rest IH]; intro Hin; [contradiction|].
  change (length (match trie_get key rows with None => [] | Some row => row end) <=
    length (match trie_get head rows with None => [] | Some row => row end) +
      dom_lt_row_mass rest rows).
  destruct Hin as [<-|Hin]; [lia|]. specialize (IH Hin). lia.
Qed.

(** A true activity observation exposes the exact stored flag needed by retirement accounting. *)
Lemma dom_order_active_get active vertex :
  dom_order_active active vertex = true -> trie_get (dom_lt_key vertex) active = Some true.
Proof.
  unfold dom_order_active. destruct (trie_get (dom_lt_key vertex) active) as [[|]|];
    intro Hactive; try discriminate Hactive; reflexivity.
Qed.

(** Retiring an active source consumes its entire retained inverse row. *)
Lemma dom_order_live_rows_retire keys active rows vertex :
  NoDup keys -> In (dom_lt_key vertex) keys -> dom_order_active active vertex = true ->
  dom_order_live_rows keys (PTrieCode.set (dom_lt_key vertex) false active) rows +
    length (dom_order_row rows vertex) = dom_order_live_rows keys active rows.
Proof.
  intros Hunique Hmember Hactive. unfold dom_order_live_rows, dom_order_row.
  apply dom_order_live_retire; [exact Hunique|exact Hmember|].
  now apply dom_order_active_get.
Qed.

Definition dom_order_removal_credit keys (st : dom_order_removal_state) : nat :=
  length (removal_queue st) + 2 * length (removal_fallback st) +
  5 * dom_order_live (fun _ => 1%nat) keys (removal_active st) +
  2 * (dom_order_live_rows keys (removal_active st) (source_children (removal_blue st)) +
    dom_order_live_rows keys (removal_active st) (source_children (removal_red st))) + 1.
(** * Stale source rows bound all source counts *)

Definition dom_source_counts_fit (tree : dom_source_tree) : Prop :=
  forall vertex, (dom_order_number (source_count tree) vertex <=
    N.of_nat (length (dom_order_row (source_children tree) vertex)))%N.

(** Empty source tables have zero counts and empty inverse rows. *)
Lemma dom_source_empty_counts : dom_source_counts_fit (DomSourceTree Empty Empty Empty).
Proof.
  intro vertex. unfold dom_order_number, dom_order_row.
  cbn [source_count source_children]. now rewrite !PTrie.get_empty.
Qed.

(** Incrementing a source count also retains one new inverse-row occurrence. *)
Lemma dom_source_add_counts tree vertex source parent :
  dom_source_counts_fit tree -> dom_source_counts_fit (dom_source_add tree vertex source parent).
Proof.
  intros Hcounts query. unfold dom_source_add.
  destruct (N.eqb source parent); [exact (Hcounts query)|].
  cbn [source_count source_children].
  destruct (N.eq_dec query source) as [->|Hdifferent].
  - unfold dom_order_number at 1. unfold dom_order_row at 1.
    rewrite !PTrie.get_set_same. cbn [length].
    pose proof (Hcounts source) as Hsource. rewrite Nat2N.inj_succ. lia.
  - unfold dom_order_number, dom_order_row in *.
    rewrite !PTrie.get_set_other by
      (intro Hkey; apply dom_lt_key_injective in Hkey; contradiction).
    exact (Hcounts query).
Qed.

(** Decrementing a source count preserves its upper bound by the retained stale row. *)
Lemma dom_source_remove_counts tree vertex parent :
  dom_source_counts_fit tree -> dom_source_counts_fit (dom_source_remove tree vertex parent).
Proof.
  intros Hcounts query. unfold dom_source_remove.
  destruct (N.eqb (dom_lt_identity (source_parent tree) vertex) parent);
    [exact (Hcounts query)|].
  cbn [source_count source_children].
  destruct (N.eq_dec query (dom_lt_identity (source_parent tree) vertex)) as [->|Hdifferent].
  - unfold dom_order_number at 1. rewrite PTrie.get_set_same.
    eapply N.le_trans; [apply N.le_pred_l|apply Hcounts].
  - unfold dom_order_number at 1. rewrite PTrie.get_set_other;
      [apply Hcounts|].
    intro Hkey. apply dom_lt_key_injective in Hkey. contradiction.
Qed.

(** Redirection preserves the count-to-stale-row inequality through its remove and add steps. *)
Lemma dom_source_redirect_counts tree vertex source parent :
  dom_source_counts_fit tree ->
  dom_source_counts_fit (dom_source_redirect tree vertex source parent).
Proof.
  intro Hcounts. unfold dom_source_redirect.
  apply dom_source_add_counts. now apply dom_source_remove_counts.
Qed.

(** Initial source counts are bounded by the inverse rows created by the same fold. *)
Lemma dom_source_initial_counts parents sources order :
  dom_source_counts_fit (dom_source_initial parents sources order).
Proof.
  unfold dom_source_initial.
  eapply dom_lt_fold_forall with (Inv := dom_source_counts_fit) (P := fun _ => True).
  - apply Forall_forall. auto.
  - apply dom_source_empty_counts.
  - intros tree vertex Htree Hvertex.
    destruct (trie_get (dom_lt_key vertex) parents); [now apply dom_source_add_counts|exact Htree].
Qed.

(** Source insertion adds at most one retained inverse entry over a distinct finite key domain. *)
Lemma dom_source_add_mass keys tree vertex source parent :
  NoDup keys -> dom_lt_row_mass keys (source_children (dom_source_add tree vertex source parent)) <=
    S (dom_lt_row_mass keys (source_children tree)).
Proof.
  intro Hunique. unfold dom_source_add.
  destruct (N.eqb source parent); cbn [source_children]; [lia|].
  unfold dom_order_row. now apply dom_lt_row_mass_push.
Qed.

(** Removing a count retains the complete stale inverse-row table. *)
Lemma dom_source_remove_children tree vertex parent :
  source_children (dom_source_remove tree vertex parent) = source_children tree.
Proof.
  unfold dom_source_remove.
  destruct (N.eqb (dom_lt_identity (source_parent tree) vertex) parent); reflexivity.
Qed.

(** A redirection creates at most one new stale inverse occurrence. *)
Lemma dom_source_redirect_mass keys tree vertex source parent :
  NoDup keys ->
  dom_lt_row_mass keys (source_children (dom_source_redirect tree vertex source parent)) <=
    S (dom_lt_row_mass keys (source_children tree)).
Proof.
  intro Hunique. unfold dom_source_redirect.
  pose proof (dom_source_add_mass keys (dom_source_remove tree vertex parent)
    vertex source parent Hunique) as Hmass.
  now rewrite dom_source_remove_children in Hmass.
Qed.

(** A source insertion creates at most one live inverse occurrence under any activity mask. *)
Lemma dom_source_add_live keys active tree vertex source parent :
  NoDup keys ->
  dom_order_live_rows keys active (source_children (dom_source_add tree vertex source parent)) <=
    S (dom_order_live_rows keys active (source_children tree)).
Proof.
  intro Hunique. unfold dom_source_add.
  destruct (N.eqb source parent); cbn [source_children]; [lia|].
  unfold dom_order_row. now apply dom_order_live_rows_push.
Qed.

(** A redirection creates at most one live inverse occurrence under the new activity mask. *)
Lemma dom_source_redirect_live keys active tree vertex source parent :
  NoDup keys ->
  dom_order_live_rows keys active
    (source_children (dom_source_redirect tree vertex source parent)) <=
    S (dom_order_live_rows keys active (source_children tree)).
Proof.
  intro Hunique. unfold dom_source_redirect.
  pose proof (dom_source_add_live keys active (dom_source_remove tree vertex parent)
    vertex source parent Hunique) as Hmass.
  now rewrite dom_source_remove_children in Hmass.
Qed.
(** * Prefix scans of inverse rows and the shrinking fallback suffix *)

Fixpoint dom_order_fallback_steps active (remaining : list N) : nat :=
  match remaining with
  | [] => 0
  | vertex :: rest =>
    if dom_order_active active vertex then 1 else S (dom_order_fallback_steps active rest)
  end.

(** An exhausted fallback has scanned its entire remaining suffix. *)
Lemma dom_order_fallback_none_steps active remaining :
  dom_order_fallback active remaining = None ->
  dom_order_fallback_steps active remaining = length remaining.
Proof.
  induction remaining as [|vertex rest IH]; intro Hnone; [reflexivity|].
  cbn [dom_order_fallback] in Hnone. cbn [dom_order_fallback_steps length].
  destruct (dom_order_active active vertex); [discriminate Hnone|].
  now rewrite (IH Hnone).
Qed.

(** A successful fallback consumes exactly the prefix before its returned residual suffix. *)
Lemma dom_order_fallback_some_steps active remaining vertex rest :
  dom_order_fallback active remaining = Some (vertex, rest) ->
  dom_order_fallback_steps active remaining + length rest = length remaining.
Proof.
  induction remaining as [|head tail IH]; intro Hsome; [discriminate Hsome|].
  cbn [dom_order_fallback] in Hsome. cbn [dom_order_fallback_steps length].
  destruct (dom_order_active active head).
  - injection Hsome as <- <-. lia.
  - specialize (IH Hsome). lia.
Qed.

(** A successful retirement charges both retained inverse rows, whichever row it actually scans. *)
Definition dom_order_removal_work (st : dom_order_removal_state) : nat :=
  match removal_queue st with
  | [] => dom_order_fallback_steps (removal_active st) (removal_fallback st) + 1
  | vertex :: _ =>
    let blue := removal_blue st in
    let red := removal_red st in
    if dom_order_active (removal_active st) vertex then
      if N.ltb (N.add (dom_order_number (source_count blue) vertex)
          (dom_order_number (source_count red) vertex))
        (if N.eqb (dom_lt_identity (source_parent blue) vertex)
          (dom_lt_identity (source_parent red) vertex) then 1%N else 2%N) then
        length (dom_order_row (source_children blue) vertex) +
          length (dom_order_row (source_children red) vertex) + 1
      else 1
    else 1
  end.

(** Every removal callback carries at least its administrative work unit. *)
Lemma dom_order_removal_work_positive st : 1 <= dom_order_removal_work st.
Proof.
  destruct st as [blue red active queue remaining records].
  unfold dom_order_removal_work. cbn [removal_blue removal_red removal_active
    removal_queue removal_fallback].
  destruct queue as [|vertex rest]; [lia|].
  destruct (dom_order_active active vertex); [|lia].
  destruct (N.ltb
    (N.add (dom_order_number (source_count blue) vertex) (dom_order_number (source_count red) vertex))
    (if N.eqb (dom_lt_identity (source_parent blue) vertex)
      (dom_lt_identity (source_parent red) vertex) then 1%N else 2%N)); lia.
Qed.
(** * Linear stale-row and retirement budgets *)

Definition dom_order_active_domain keys active : Prop :=
  forall vertex, dom_order_active active vertex = true -> In (dom_lt_key vertex) keys.

(** Retiring a key introduces no new active numeric key. *)
Lemma dom_order_active_domain_retire keys active vertex :
  dom_order_active_domain keys active ->
  dom_order_active_domain keys (PTrieCode.set (dom_lt_key vertex) false active).
Proof.
  intros Hdomain query Hquery. rewrite dom_order_active_set in Hquery.
  destruct (N.eqb query vertex); [discriminate Hquery|now apply Hdomain].
Qed.

(** Initial activation uses only the explicitly supplied finite key universe. *)
Lemma dom_order_active_domain_initial keys order :
  Forall (fun vertex => In (dom_lt_key vertex) keys) order ->
  dom_order_active_domain keys
    (fold_left (fun active vertex => PTrieCode.set (dom_lt_key vertex) true active) order Empty).
Proof.
  intros Horder vertex Hactive. apply dom_order_active_fold_domain in Hactive.
  destruct Hactive as [Hin|Hempty].
  - now apply Forall_forall with (x := vertex) in Horder.
  - unfold dom_order_active in Hempty. rewrite PTrie.get_empty in Hempty. discriminate Hempty.
Qed.

Definition dom_order_stale_credit keys (st : dom_order_removal_state) : nat :=
  dom_lt_row_mass keys (source_children (removal_blue st)) +
  dom_lt_row_mass keys (source_children (removal_red st)) +
  dom_order_live (fun _ => 1%nat) keys (removal_active st).

(** Each removal callback keeps its live vertices inside the original finite domain. *)
Lemma dom_order_remove_step_domain keys parents st :
  dom_order_active_domain keys (removal_active st) ->
  match dom_order_remove_step parents st with
  | inl next => dom_order_active_domain keys (removal_active next)
  | inr _ => True
  end.
Proof.
  destruct st as [blue red active queue remaining records]. intro Hdomain.
  cbn [removal_active] in Hdomain.
  unfold dom_order_remove_step.
  cbn [removal_blue removal_red removal_active removal_queue
    removal_fallback removal_records].
  destruct queue as [|vertex queue].
  - destruct (dom_order_fallback active remaining) as [[vertex rest]|]; [|exact I].
    cbn [removal_active]. now apply dom_order_active_domain_retire.
  - destruct (dom_order_active active vertex); [|exact Hdomain].
    destruct (N.ltb
      (N.add (dom_order_number (source_count blue) vertex)
        (dom_order_number (source_count red) vertex))
      (if N.eqb (dom_lt_identity (source_parent blue) vertex)
        (dom_lt_identity (source_parent red) vertex) then 1%N else 2%N)); [|exact Hdomain].
    cbn [removal_active]. now apply dom_order_active_domain_retire.
Qed.

(** Source-count bounds remain valid while removals and redirects retain stale rows. *)
Lemma dom_order_remove_step_counts parents st :
  dom_source_counts_fit (removal_blue st) -> dom_source_counts_fit (removal_red st) ->
  match dom_order_remove_step parents st with
  | inl next => dom_source_counts_fit (removal_blue next) /\ dom_source_counts_fit (removal_red next)
  | inr _ => True
  end.
Proof.
  destruct st as [blue red active queue remaining records]. intros Hblue Hred.
  cbn [removal_blue removal_red] in Hblue, Hred.
  unfold dom_order_remove_step.
  cbn [removal_blue removal_red removal_active removal_queue
    removal_fallback removal_records].
  destruct queue as [|vertex queue].
  - destruct (dom_order_fallback active remaining) as [[vertex rest]|];
      [exact (conj Hblue Hred)|exact I].
  - destruct (dom_order_active active vertex); [|exact (conj Hblue Hred)].
    destruct (N.ltb
      (N.add (dom_order_number (source_count blue) vertex)
        (dom_order_number (source_count red) vertex))
      (if N.eqb (dom_lt_identity (source_parent blue) vertex)
        (dom_lt_identity (source_parent red) vertex) then 1%N else 2%N));
      [|exact (conj Hblue Hred)].
    destruct (N.eqb (dom_order_number (source_count red) vertex) 0%N);
      cbn [removal_blue removal_red].
    + destruct (dom_source_child (source_parent blue) active vertex
        (dom_order_row (source_children blue) vertex)).
      * split.
        -- apply dom_source_redirect_counts. now apply dom_source_remove_counts.
        -- now apply dom_source_remove_counts.
      * split; now apply dom_source_remove_counts.
    + destruct (dom_source_child (source_parent red) active vertex
        (dom_order_row (source_children red) vertex)).
      * split.
        -- now apply dom_source_remove_counts.
        -- apply dom_source_redirect_counts. now apply dom_source_remove_counts.
      * split; now apply dom_source_remove_counts.
Qed.

(** Retiring one source pays for the at most one stale inverse entry created by its redirect. *)
Lemma dom_order_remove_step_stale keys parents st :
  NoDup keys -> dom_order_active_domain keys (removal_active st) ->
  match dom_order_remove_step parents st with
  | inl next => dom_order_stale_credit keys next <= dom_order_stale_credit keys st
  | inr _ => True
  end.
Proof.
  destruct st as [blue red active queue remaining records]. intros Hunique Hdomain.
  cbn [removal_active] in Hdomain.
  unfold dom_order_remove_step.
  cbn [removal_blue removal_red removal_active removal_queue
    removal_fallback removal_records].
  destruct queue as [|vertex queue].
  - destruct (dom_order_fallback active remaining) as [[vertex rest]|] eqn:Hfallback;
      [|exact I].
    pose proof (proj1 (dom_order_fallback_active active remaining vertex rest Hfallback)) as Hactive.
    pose proof (dom_order_live_retire (fun _ => 1%nat) keys active (dom_lt_key vertex)
      Hunique (Hdomain vertex Hactive) (dom_order_active_get active vertex Hactive)) as Hretire.
    unfold dom_order_stale_credit. cbn [removal_blue removal_red removal_active].
    cbn beta in Hretire. lia.
  - destruct (dom_order_active active vertex) eqn:Hactive; [|reflexivity].
    destruct (N.ltb
      (N.add (dom_order_number (source_count blue) vertex)
        (dom_order_number (source_count red) vertex))
      (if N.eqb (dom_lt_identity (source_parent blue) vertex)
        (dom_lt_identity (source_parent red) vertex) then 1%N else 2%N)); [|reflexivity].
    pose proof (dom_order_live_retire (fun _ => 1%nat) keys active (dom_lt_key vertex)
      Hunique (Hdomain vertex Hactive) (dom_order_active_get active vertex Hactive)) as Hretire.
    cbn beta in Hretire.
    destruct (N.eqb (dom_order_number (source_count red) vertex) 0%N).
    + destruct (dom_source_child (source_parent blue) active vertex
        (dom_order_row (source_children blue) vertex)) as [child|].
      * pose proof (dom_source_redirect_mass keys
          (dom_source_remove blue vertex (dom_lt_identity parents vertex)) child
          (dom_lt_identity (source_parent blue) vertex) (dom_lt_identity parents vertex)
          Hunique) as Hredirect.
        rewrite dom_source_remove_children in Hredirect.
        unfold dom_order_stale_credit. cbn [removal_blue removal_red removal_active].
        rewrite dom_source_remove_children. clear -Hretire Hredirect. lia.
      * unfold dom_order_stale_credit. cbn [removal_blue removal_red removal_active].
        rewrite !dom_source_remove_children. lia.
    + destruct (dom_source_child (source_parent red) active vertex
        (dom_order_row (source_children red) vertex)) as [child|].
      * pose proof (dom_source_redirect_mass keys
          (dom_source_remove red vertex (dom_lt_identity parents vertex)) child
          (dom_lt_identity (source_parent red) vertex) (dom_lt_identity parents vertex)
          Hunique) as Hredirect.
        rewrite dom_source_remove_children in Hredirect.
        unfold dom_order_stale_credit. cbn [removal_blue removal_red removal_active].
        rewrite dom_source_remove_children. clear -Hretire Hredirect. lia.
      * unfold dom_order_stale_credit. cbn [removal_blue removal_red removal_active].
        rewrite !dom_source_remove_children. lia.
Qed.

(** Each initial source insertion contributes at most one stale inverse entry. *)
Lemma dom_source_initial_mass keys parents sources order :
  NoDup keys -> dom_lt_row_mass keys (source_children (dom_source_initial parents sources order)) <=
    length order.
Proof.
  intro Hunique.
  assert (Hfold : forall xs tree,
    dom_lt_row_mass keys (source_children (fold_left
      (fun tree vertex => match trie_get (dom_lt_key vertex) parents with
      | None => tree
      | Some parent => dom_source_add tree vertex (dom_lt_identity sources vertex) parent
      end) xs tree)) <= length xs + dom_lt_row_mass keys (source_children tree)).
  { induction xs as [|vertex rest IH]; intro tree; [cbn [fold_left length]; lia|].
    cbn [fold_left length].
    destruct (trie_get (dom_lt_key vertex) parents) as [parent|].
    - pose proof (dom_source_add_mass keys tree vertex (dom_lt_identity sources vertex)
        parent Hunique) as Hhead.
      specialize (IH (dom_source_add tree vertex (dom_lt_identity sources vertex) parent)). lia.
    - specialize (IH tree). lia. }
  unfold dom_source_initial.
  pose proof (Hfold order (DomSourceTree Empty Empty Empty)) as Hmass.
  cbn [source_children] in Hmass. now rewrite dom_lt_row_mass_empty, Nat.add_0_r in Hmass.
Qed.

(** A continuing removal spends enough queue, suffix and live-row credit for its chosen work. *)
Lemma dom_order_remove_step_credit keys parents st next :
  NoDup keys -> dom_order_active_domain keys (removal_active st) ->
  dom_order_remove_step parents st = inl next ->
  dom_order_removal_credit keys next + dom_order_removal_work st <=
    dom_order_removal_credit keys st.
Proof.
  destruct st as [blue red active queue remaining records].
  intros Hunique Hdomain Hstep. cbn [removal_active] in Hdomain.
  unfold dom_order_remove_step in Hstep.
  cbn [removal_blue removal_red removal_active removal_queue
    removal_fallback removal_records] in Hstep.
  unfold dom_order_removal_work.
  cbn [removal_blue removal_red removal_active removal_queue removal_fallback].
  destruct queue as [|vertex queue].
  - destruct (dom_order_fallback active remaining) as [[vertex rest]|] eqn:Hfallback;
      [|discriminate Hstep]. injection Hstep as <-.
    pose proof (proj1 (dom_order_fallback_active active remaining vertex rest Hfallback)) as Hactive.
    pose proof (dom_order_live_retire (fun _ => 1%nat) keys active (dom_lt_key vertex)
      Hunique (Hdomain vertex Hactive) (dom_order_active_get active vertex Hactive)) as Hretire.
    pose proof (dom_order_live_rows_retire keys active (source_children blue) vertex
      Hunique (Hdomain vertex Hactive) Hactive) as Hblue.
    pose proof (dom_order_live_rows_retire keys active (source_children red) vertex
      Hunique (Hdomain vertex Hactive) Hactive) as Hred.
    pose proof (dom_order_fallback_some_steps active remaining vertex rest Hfallback) as Hsuffix.
    unfold dom_order_removal_credit.
    cbn [removal_blue removal_red removal_active removal_queue removal_fallback length].
    cbn beta in Hretire. clear -Hretire Hblue Hred Hsuffix. lia.
  - destruct (dom_order_active active vertex) eqn:Hactive.
    + destruct (N.ltb
        (N.add (dom_order_number (source_count blue) vertex)
          (dom_order_number (source_count red) vertex))
        (if N.eqb (dom_lt_identity (source_parent blue) vertex)
          (dom_lt_identity (source_parent red) vertex) then 1%N else 2%N)).
      * pose proof (dom_order_live_retire (fun _ => 1%nat) keys active (dom_lt_key vertex)
          Hunique (Hdomain vertex Hactive) (dom_order_active_get active vertex Hactive)) as Hretire.
        pose proof (dom_order_live_rows_retire keys active (source_children blue) vertex
          Hunique (Hdomain vertex Hactive) Hactive) as Hblue.
        pose proof (dom_order_live_rows_retire keys active (source_children red) vertex
          Hunique (Hdomain vertex Hactive) Hactive) as Hred.
        cbn beta in Hretire.
        destruct (N.eqb (dom_order_number (source_count red) vertex) 0%N).
        -- destruct (dom_source_child (source_parent blue) active vertex
            (dom_order_row (source_children blue) vertex)) as [child|]; injection Hstep as <-.
           ++ pose proof (dom_source_redirect_live keys
                (PTrieCode.set (dom_lt_key vertex) false active)
                (dom_source_remove blue vertex (dom_lt_identity parents vertex)) child
                (dom_lt_identity (source_parent blue) vertex) (dom_lt_identity parents vertex)
                Hunique) as Hredirect.
              rewrite dom_source_remove_children in Hredirect.
              unfold dom_order_removal_credit.
              cbn [removal_blue removal_red removal_active removal_queue removal_fallback length].
              rewrite dom_source_remove_children.
              clear -Hretire Hblue Hred Hredirect. lia.
           ++ unfold dom_order_removal_credit.
              cbn [removal_blue removal_red removal_active removal_queue removal_fallback length].
              rewrite !dom_source_remove_children. clear -Hretire Hblue Hred. lia.
        -- destruct (dom_source_child (source_parent red) active vertex
            (dom_order_row (source_children red) vertex)) as [child|]; injection Hstep as <-.
           ++ pose proof (dom_source_redirect_live keys
                (PTrieCode.set (dom_lt_key vertex) false active)
                (dom_source_remove red vertex (dom_lt_identity parents vertex)) child
                (dom_lt_identity (source_parent red) vertex) (dom_lt_identity parents vertex)
                Hunique) as Hredirect.
              rewrite dom_source_remove_children in Hredirect.
              unfold dom_order_removal_credit.
              cbn [removal_blue removal_red removal_active removal_queue removal_fallback length].
              rewrite dom_source_remove_children.
              clear -Hretire Hblue Hred Hredirect. lia.
           ++ unfold dom_order_removal_credit.
              cbn [removal_blue removal_red removal_active removal_queue removal_fallback length].
              rewrite !dom_source_remove_children. clear -Hretire Hblue Hred. lia.
      * injection Hstep as <-. unfold dom_order_removal_credit.
        cbn [removal_blue removal_red removal_active removal_queue removal_fallback length]. lia.
    + injection Hstep as <-. unfold dom_order_removal_credit.
      cbn [removal_blue removal_red removal_active removal_queue removal_fallback length]. lia.
Qed.

(** Terminal removal spends the remaining fallback suffix from its permanent credit. *)
Lemma dom_order_remove_stop_credit keys parents st result :
  dom_order_remove_step parents st = inr result ->
  dom_order_removal_work st <= dom_order_removal_credit keys st.
Proof.
  destruct st as [blue red active queue remaining records]. intro Hstep.
  unfold dom_order_remove_step in Hstep.
  cbn [removal_blue removal_red removal_active removal_queue
    removal_fallback removal_records] in Hstep.
  destruct queue as [|vertex queue].
  - destruct (dom_order_fallback active remaining) as [[vertex rest]|] eqn:Hfallback;
      [discriminate Hstep|].
    pose proof (dom_order_fallback_none_steps active remaining Hfallback) as Hsuffix.
    unfold dom_order_removal_credit, dom_order_removal_work.
    cbn [removal_blue removal_red removal_active removal_queue removal_fallback length]. lia.
  - destruct (dom_order_active active vertex); [|discriminate Hstep].
    destruct (N.ltb
      (N.add (dom_order_number (source_count blue) vertex)
        (dom_order_number (source_count red) vertex))
      (if N.eqb (dom_lt_identity (source_parent blue) vertex)
        (dom_lt_identity (source_parent red) vertex) then 1%N else 2%N)); discriminate Hstep.
Qed.
(** A count is bounded by the complete stale-row inventory whenever its query key is included. *)
Lemma dom_source_count_bound keys tree vertex :
  dom_source_counts_fit tree -> In (dom_lt_key vertex) keys ->
  (dom_order_number (source_count tree) vertex <=
    N.of_nat (dom_lt_row_mass keys (source_children tree)))%N.
Proof.
  intros Hcounts Hmember. eapply N.le_trans; [exact (Hcounts vertex)|].
  apply time_of_nat_le. unfold dom_order_row. now apply dom_order_row_mass_member.
Qed.

(** * Numeric bounds for removal clocks *)

(** The enlarged removal fuel adds six bits even for a zero or unit limit. *)
Lemma dom_order_removal_fuel_bits limit :
  N.size_nat (N.double (N.double (N.double (N.double limit))) + 3)%N <=
    N.size_nat limit + 6.
Proof.
  pose proof (dom_lt_double_width limit) as Hfirst.
  pose proof (dom_lt_double_width (N.double limit)) as Hsecond.
  pose proof (dom_lt_double_width (N.double (N.double limit))) as Hthird.
  pose proof (dom_lt_double_width (N.double (N.double (N.double limit)))) as Hfourth.
  pose proof (dom_add_width (N.double (N.double (N.double (N.double limit)))) 3%N) as Hadd.
  change (N.size_nat (N.double (N.double (N.double (N.double limit))) + 3)%N <=
    N.size_nat (N.double (N.double (N.double (N.double limit)))) + 2) in Hadd.
  lia.
Qed.

(** The common polynomial budget includes all source-count sums and numeric operands. *)
Lemma dom_order_removal_linear_bound (bound value : N) :
  (value <= 6 * bound + 4)%N ->
  (value <= 8 * (bound + 1) * (bound + 1))%N.
Proof.
  intro Hvalue. nia.
Qed.

(** Every original numeric operand inherits the polynomial width allowance. *)
Lemma dom_order_removal_base_width count width :
  (forall value, (value <= 8 * (N.of_nat count + 1) * (N.of_nat count + 1))%N ->
    N.size_nat value <= width) ->
  forall value, (value <= N.of_nat count)%N -> N.size_nat value <= width.
Proof.
  intros Hwidth value Hvalue. apply Hwidth. apply dom_order_removal_linear_bound. lia.
Qed.

(** Operand ranges, live-domain membership, counts, and stale mass form the clock invariant. *)
Record dom_order_removal_invariant (count : nat) (st : dom_order_removal_state) : Prop := {
  dom_order_removal_inv_range : dom_order_removal_range (N.of_nat count) st;
  dom_order_removal_inv_domain :
    dom_order_active_domain (dom_order_key_universe count) (removal_active st);
  dom_order_removal_inv_blue_counts : dom_source_counts_fit (removal_blue st);
  dom_order_removal_inv_red_counts : dom_source_counts_fit (removal_red st);
  dom_order_removal_inv_stale :
    dom_order_stale_credit (dom_order_key_universe count) st <= 3 * count + 2
}.

(** A continuing callback preserves every numeric premise needed by its next clock. *)
Lemma dom_order_removal_invariant_step count parents st next :
  dom_lt_trie_all (fun value => (value <= N.of_nat count)%N) parents ->
  dom_order_removal_invariant count st ->
  dom_order_remove_step parents st = inl next -> dom_order_removal_invariant count next.
Proof.
  intros Hparents [Hrange Hdomain Hblue Hred Hstale] Hstep.
  pose proof (dom_order_remove_step_range (N.of_nat count) parents st Hparents Hrange) as Hranges.
  pose proof (dom_order_remove_step_domain (dom_order_key_universe count) parents st Hdomain)
    as Hdomains.
  pose proof (dom_order_remove_step_counts parents st Hblue Hred) as Hcounts.
  pose proof (dom_order_remove_step_stale (dom_order_key_universe count) parents st
    (dom_order_key_universe_unique count) Hdomain) as Hmass.
  rewrite Hstep in Hranges, Hdomains, Hcounts, Hmass.
  destruct Hcounts as [Hblue_next Hred_next]. constructor; try assumption.
  eapply Nat.le_trans; eassumption.
Qed.

Definition dom_source_numeric_bounded (count : nat) (tree : dom_source_tree) : Prop :=
  dom_source_range (N.of_nat count) tree /\ dom_source_counts_fit tree /\
    dom_lt_row_mass (dom_order_key_universe count) (source_children tree) <= 3 * count + 2.

(** Each source tree fits the shared stale-mass ceiling. *)
Lemma dom_order_removal_trees_bounded count st :
  dom_order_removal_invariant count st ->
  dom_source_numeric_bounded count (removal_blue st) /\
    dom_source_numeric_bounded count (removal_red st).
Proof.
  intros [Hrange Hdomain Hblue Hred Hstale].
  destruct Hrange as [Hblue_range [Hred_range Hrest]].
  unfold dom_source_numeric_bounded. unfold dom_order_stale_credit in Hstale.
  split.
  - split; [exact Hblue_range|]. split; [exact Hblue|lia].
  - split; [exact Hred_range|]. split; [exact Hred|lia].
Qed.

(** Initialization allocates at most one inverse entry per input and a linear total credit. *)
Lemma dom_order_removal_initial_invariant count parents sources children :
  length children <= count ->
  Forall (fun value => (value <= N.of_nat count)%N) children ->
  dom_order_sources_range (N.of_nat count) sources ->
  let initial := DomOrderRemovalState
    (dom_source_initial parents (source_blue sources) children)
    (dom_source_initial parents (source_red sources) children)
    (fold_left (fun active vertex => PTrieCode.set (dom_lt_key vertex) true active)
      children Empty) children children [] in
  dom_order_removal_invariant count initial /\
    dom_order_removal_credit (dom_order_key_universe count) initial <= 12 * (count + 1).
Proof.
  intros Hlength Hchildren [Hblue_source Hred_source]. cbn zeta.
  set (blue := dom_source_initial parents (source_blue sources) children).
  set (red := dom_source_initial parents (source_red sources) children).
  set (active := fold_left (fun active vertex => PTrieCode.set (dom_lt_key vertex) true active)
    children Empty).
  pose proof (dom_source_initial_range (N.of_nat count) parents (source_blue sources)
    children Hblue_source Hchildren) as Hblue_range. fold blue in Hblue_range.
  pose proof (dom_source_initial_range (N.of_nat count) parents (source_red sources)
    children Hred_source Hchildren) as Hred_range. fold red in Hred_range.
  pose proof (dom_source_initial_counts parents (source_blue sources) children) as Hblue_counts.
  pose proof (dom_source_initial_counts parents (source_red sources) children) as Hred_counts.
  fold blue in Hblue_counts. fold red in Hred_counts.
  pose proof (dom_source_initial_mass (dom_order_key_universe count) parents
    (source_blue sources) children (dom_order_key_universe_unique count)) as Hblue_mass.
  pose proof (dom_source_initial_mass (dom_order_key_universe count) parents
    (source_red sources) children (dom_order_key_universe_unique count)) as Hred_mass.
  fold blue in Hblue_mass. fold red in Hred_mass.
  assert (Hmembers : Forall (fun vertex =>
      In (dom_lt_key vertex) (dom_order_key_universe count)) children).
  { apply Forall_forall. intros vertex Hin.
    apply Forall_forall with (x := vertex) in Hchildren; [|exact Hin].
    apply dom_order_key_universe_member. eapply N.le_trans; [exact Hchildren|].
    rewrite Nat2N.inj_add. apply N.le_add_r. }
  pose proof (dom_order_active_domain_initial (dom_order_key_universe count) children Hmembers)
    as Hdomain. fold active in Hdomain.
  pose proof (dom_order_live_count_bound (dom_order_key_universe count) active) as Hactive_count.
  rewrite dom_order_key_universe_length in Hactive_count.
  pose proof (dom_order_live_rows_bound (dom_order_key_universe count) active
    (source_children blue)) as Hblue_live.
  pose proof (dom_order_live_rows_bound (dom_order_key_universe count) active
    (source_children red)) as Hred_live.
  split.
  - constructor.
    + apply dom_order_removal_range_make; try assumption. constructor.
    + exact Hdomain.
    + exact Hblue_counts.
    + exact Hred_counts.
    + unfold dom_order_stale_credit. cbn [removal_blue removal_red removal_active].
      clearbody blue red active. clear -Hblue_mass Hred_mass Hactive_count Hlength. lia.
  - unfold dom_order_removal_credit.
    cbn [removal_blue removal_red removal_active removal_queue removal_fallback length].
    clearbody blue red active.
    clear -Hblue_mass Hred_mass Hactive_count Hblue_live Hred_live Hlength. lia.
Qed.

(** Removing one count preserves source ranges, fitted counts, and the stale-mass ceiling. *)
Lemma dom_source_remove_numeric_bounded count tree vertex parent :
  dom_source_numeric_bounded count tree ->
  dom_source_numeric_bounded count (dom_source_remove tree vertex parent).
Proof.
  intros [Hrange [Hcounts Hmass]]. split.
  - now apply dom_source_remove_range.
  - split; [now apply dom_source_remove_counts|].
    now rewrite dom_source_remove_children.
Qed.

(** Every bounded query count is covered by the finite stale-row inventory. *)
Lemma dom_source_numeric_count count tree vertex :
  dom_source_numeric_bounded count tree -> (vertex <= N.of_nat count)%N ->
  (dom_order_number (source_count tree) vertex <= N.of_nat (3 * count + 2))%N.
Proof.
  intros [Hrange [Hcounts Hmass]] Hvertex.
  assert (Hmember : In (dom_lt_key vertex) (dom_order_key_universe count)).
  { apply dom_order_key_universe_member.
    eapply N.le_trans; [exact Hvertex|]. rewrite Nat2N.inj_add. apply N.le_add_r. }
  eapply N.le_trans; [exact (dom_source_count_bound (dom_order_key_universe count)
    tree vertex Hcounts Hmember)|].
  now apply time_of_nat_le.
Qed.

(** Source counts inherit the common width without assumptions about active children. *)
Lemma dom_source_numeric_count_width count width tree vertex :
  (forall value, (value <= 8 * (N.of_nat count + 1) * (N.of_nat count + 1))%N ->
    N.size_nat value <= width) ->
  dom_source_numeric_bounded count tree -> (vertex <= N.of_nat count)%N ->
  N.size_nat (dom_order_number (source_count tree) vertex) <= width.
Proof.
  intros Hwidth Htree Hvertex. apply Hwidth. apply dom_order_removal_linear_bound.
  pose proof (dom_source_numeric_count count tree vertex Htree Hvertex) as Hcount.
  clear -Hcount. rewrite !Nat2N.inj_add, !Nat2N.inj_mul in Hcount. lia.
Qed.

(** Stored or defaulted source values remain in the original numeric range. *)
Lemma dom_source_numeric_value count tree vertex :
  dom_source_numeric_bounded count tree -> (vertex <= N.of_nat count)%N ->
  (dom_lt_identity (source_parent tree) vertex <= N.of_nat count)%N.
Proof.
  intros [[Hparents Hrows] Hrest] Hvertex.
  exact (dom_lt_identity_bounded (N.of_nat count) (source_parent tree) vertex Hparents Hvertex).
Qed.

(** The two count operands and their sum fit the polynomial numeric width. *)
Lemma dom_source_numeric_sum_width count width blue red vertex :
  (forall value, (value <= 8 * (N.of_nat count + 1) * (N.of_nat count + 1))%N ->
    N.size_nat value <= width) ->
  dom_source_numeric_bounded count blue -> dom_source_numeric_bounded count red ->
  (vertex <= N.of_nat count)%N ->
  N.size_nat (dom_order_number (source_count blue) vertex +
    dom_order_number (source_count red) vertex)%N <= width.
Proof.
  intros Hwidth Hblue Hred Hvertex. apply Hwidth. apply dom_order_removal_linear_bound.
  pose proof (dom_source_numeric_count count blue vertex Hblue Hvertex) as Hblue_count.
  pose proof (dom_source_numeric_count count red vertex Hred Hvertex) as Hred_count.
  clear -Hblue_count Hred_count.
  rewrite !Nat2N.inj_add, !Nat2N.inj_mul in Hblue_count, Hred_count. lia.
Qed.

Local Opaque dom_order_derived T_dom_order_derived.

(** Bounded numeric sources and logarithmic indexes supply the two search charges. *)
Lemma dom_order_colour_clock width height numeric semis minimizer relative parents indexes
    walk st vertex :
  N.size_nat vertex <= width ->
  dom_lt_trie_all (fun value => N.size_nat value <= width) semis ->
  dom_lt_trie_all (fun value => N.size_nat value <= width) minimizer ->
  dom_lt_trie_all (fun value => N.size_nat value <= width) relative ->
  dom_lt_trie_all (fun value => N.size_nat value <= width) (lt_numeric_parent numeric) ->
  dom_lt_trie_all (fun value => N.size_nat value <= width) parents ->
  dom_lt_trie_all (dom_order_index_values (fun child => N.size_nat child <= width)
    (fun _ => True)) indexes ->
  dom_lt_trie_all (fun index => dom_order_index_height index <= height) indexes ->
  dom_lt_trie_all (fun position => N.size_nat position <= width) (order_pre walk) ->
  (T_dom_order_colour numeric semis minimizer relative parents indexes walk st vertex <=
    1024 * (PTrieT.c_trie + 1) *
      N.of_nat ((length (dom_order_row (lt_numeric_pred numeric) vertex) + height + 1) *
        (width + 1)))%N.
Proof.
  intros Hvertex Hsemis Hminimizer Hrelative Hnumeric_parent Hparents Hchildren Hheight Hpositions.
  pose proof (dom_order_identity_property _ relative vertex Hvertex Hrelative) as Hrelative_value.
  pose proof (dom_order_identity_property _ semis vertex Hvertex Hsemis) as Hsemi_value.
  pose proof (dom_order_identity_property _ minimizer vertex Hvertex Hminimizer) as Hminimizer_value.
  pose proof (dom_order_identity_property _ (lt_numeric_parent numeric) vertex
    Hvertex Hnumeric_parent) as Hnumeric_value.
  pose proof (dom_order_colour_base_clock width
    (64 * N.of_nat ((height + 1) * (width + 1)))%N numeric semis minimizer relative
    parents indexes walk st vertex Hvertex Hrelative_value Hsemi_value Hparents) as Hclock.
  specialize (Hclock ltac:(intros parent Hparent;
    pose proof (Hparents (dom_lt_key vertex) parent Hparent) as Hparent_width;
    change (N.size_nat parent <= width) in Hparent_width;
    split; apply dom_order_derived_clock; assumption)).
  set (row := dom_order_row (lt_numeric_pred numeric) vertex) in *.
  set (w := N.of_nat (width + 1)).
  set (budget := N.of_nat ((length row + height + 1) * (width + 1))).
  assert (Hw : (1 <= w)%N) by (unfold w; lia).
  assert (Hwidth_budget : (w <= budget)%N).
  { unfold budget. rewrite Nat2N.inj_mul. fold w.
    replace w with (1 * w)%N at 1 by ring.
    apply N.mul_le_mono_r. lia. }
  assert (Hsearch_budget : (N.of_nat ((height + 1) * (width + 1)) <= budget)%N).
  { unfold budget. apply time_of_nat_le. apply Nat.mul_le_mono_r. lia. }
  assert (Hscan_budget : ((w + 2) * N.of_nat (length row) <= 3 * budget)%N).
  { eapply N.le_trans with ((3 * w) * N.of_nat (length row))%N.
    - apply N.mul_le_mono_r. lia.
    - unfold budget. rewrite Nat2N.inj_mul. fold w.
      replace (3 * w * N.of_nat (length row))%N with
        (3 * (N.of_nat (length row) * w))%N by ring.
      apply N.mul_le_mono_l. apply N.mul_le_mono_r. apply time_of_nat_le. lia. }
  fold w in Hclock. fold budget.
  set (trie_budget := ((PTrieT.c_trie + 1) * budget)%N).
  assert (Hbase_paid : (256 * (PTrieT.c_trie + 1) * w <= 256 * trie_budget)%N).
  { unfold trie_budget.
    replace (256 * ((PTrieT.c_trie + 1) * budget))%N with
      ((256 * (PTrieT.c_trie + 1)) * budget)%N by ring.
    now apply N.mul_le_mono_l. }
  assert (Hbudget_paid : (budget <= trie_budget)%N).
  { unfold trie_budget. replace budget with (1 * budget)%N at 1 by ring.
    apply N.mul_le_mono_r. lia. }
  replace (1024 * (PTrieT.c_trie + 1) * budget)%N with (1024 * trie_budget)%N
    by (unfold trie_budget; ring).
  clearbody budget trie_budget.
  clear -Hclock Hbase_paid Hsearch_budget Hscan_budget Hbudget_paid. lia.
Qed.

(** Summing colouring callbacks charges predecessor cells and one index height per input. *)
Lemma dom_order_colour_fold_clock width height numeric semis minimizer relative parents indexes
    walk order st :
  Forall (fun vertex => N.size_nat vertex <= width) order ->
  dom_lt_trie_all (fun value => N.size_nat value <= width) semis ->
  dom_lt_trie_all (fun value => N.size_nat value <= width) minimizer ->
  dom_lt_trie_all (fun value => N.size_nat value <= width) relative ->
  dom_lt_trie_all (fun value => N.size_nat value <= width) (lt_numeric_parent numeric) ->
  dom_lt_trie_all (fun value => N.size_nat value <= width) parents ->
  dom_lt_trie_all (dom_order_index_values (fun child => N.size_nat child <= width)
    (fun _ => True)) indexes ->
  dom_lt_trie_all (fun index => dom_order_index_height index <= height) indexes ->
  dom_lt_trie_all (fun position => N.size_nat position <= width) (order_pre walk) ->
  (List.T_fold_left (dom_order_colour numeric semis minimizer relative parents indexes walk)
    (T_dom_order_colour numeric semis minimizer relative parents indexes walk) order st <=
    2048 * (PTrieT.c_trie + 1) *
      N.of_nat ((dom_lt_row_mass (map dom_lt_key order) (lt_numeric_pred numeric) +
        (height + 1) * length order + 1) * (width + 1)))%N.
Proof.
  intros Horder Hsemis Hminimizer Hrelative Hnumeric_parent Hparents Hchildren Hheight Hpositions.
  set (unit := (1024 * (PTrieT.c_trie + 1) * N.of_nat (width + 1))%N).
  assert (Hunit : (1 <= unit)%N).
  { unfold unit. clear -width. rewrite Nat2N.inj_add. nia. }
  assert (Hcallback : forall vertex, In vertex order -> forall current,
    (T_dom_order_colour numeric semis minimizer relative parents indexes walk current vertex <=
      unit * N.of_nat (length (dom_order_row (lt_numeric_pred numeric) vertex) + (height + 1)))%N).
  { intros vertex Hin current.
    pose proof (dom_order_colour_clock width height numeric semis minimizer relative parents indexes
      walk current vertex (proj1 (Forall_forall _ _) Horder vertex Hin) Hsemis Hminimizer
      Hrelative Hnumeric_parent Hparents Hchildren Hheight Hpositions) as Hclock.
    replace (length (dom_order_row (lt_numeric_pred numeric) vertex) + (height + 1))
      with (length (dom_order_row (lt_numeric_pred numeric) vertex) + height + 1) by lia.
    unfold unit. rewrite Nat2N.inj_mul in Hclock.
    replace (1024 * (PTrieT.c_trie + 1) * N.of_nat (width + 1) *
      N.of_nat (length (dom_order_row (lt_numeric_pred numeric) vertex) + height + 1))%N with
      (1024 * (PTrieT.c_trie + 1) *
        (N.of_nat (length (dom_order_row (lt_numeric_pred numeric) vertex) + height + 1) *
          N.of_nat (width + 1)))%N by ring. exact Hclock. }
  pose proof (dom_order_fold_sum_clock
    (dom_order_colour numeric semis minimizer relative parents indexes walk)
    (T_dom_order_colour numeric semis minimizer relative parents indexes walk)
    (fun vertex => unit *
      N.of_nat (length (dom_order_row (lt_numeric_pred numeric) vertex) + (height + 1)))%N
    order st Hcallback) as Hfold.
  rewrite dom_order_sum_scaled in Hfold.
  rewrite (dom_order_sum_allowance
    (fun vertex => length (dom_order_row (lt_numeric_pred numeric) vertex)) order (height + 1)),
    dom_order_rows_sum in Hfold.
  set (mass := (dom_lt_row_mass (map dom_lt_key order) (lt_numeric_pred numeric) +
    (height + 1) * length order)%nat) in *.
  assert (Hcount : length order <= mass) by (unfold mass; nia).
  apply time_of_nat_le in Hcount.
  rewrite Nat2N.inj_mul.
  replace (2048 * (PTrieT.c_trie + 1) *
    (N.of_nat (mass + 1) * N.of_nat (width + 1)))%N with
    (2 * unit * N.of_nat (mass + 1))%N by (unfold unit; ring).
  rewrite Nat2N.inj_add. change (N.of_nat 1) with 1%N in *.
  clearbody unit mass. clear -Hfold Hunit Hcount. nia.
Qed.

Local Transparent dom_order_derived T_dom_order_derived.

(** Each phase fits the same linear removal budget. *)
Lemma dom_order_removal_final_budget (c loop budget filter_work active blue red run total : N) :
  (filter_work <= 32 * budget)%N ->
  (active <= 128 * (c + 1) * budget)%N ->
  (blue <= 512 * (c + 1) * budget)%N ->
  (red <= 512 * (c + 1) * budget)%N ->
  (run <= (49152 * (c + 1) + 19 * loop) * budget)%N ->
  (total <= filter_work + active + blue + red + run + 64 * budget)%N ->
  (total <= 65536 * (loop + 1) * (c + 1) * budget)%N.
Proof.
  intros Hfilter Hactive Hblue Hred Hrun Htotal.
  assert (Hsum : (total <= (50304 * (c + 1) + 19 * loop + 96) * budget)%N).
  { replace ((50304 * (c + 1) + 19 * loop + 96) * budget)%N with
      (32 * budget + 128 * (c + 1) * budget + 512 * (c + 1) * budget +
        512 * (c + 1) * budget + (49152 * (c + 1) + 19 * loop) * budget +
        64 * budget)%N by ring. lia. }
  eapply N.le_trans; [exact Hsum|]. apply N.mul_le_mono_r. nia.
Qed.

Definition dom_order_removal_coefficient : N :=
  (65536 * (c_loopN + 1) * (PTrieT.c_trie + 1))%N.

(** * Removal callback clocks *)

Local Opaque Argent.Loop.loop T_loopN.

Definition dom_order_removal_unit (width : nat) : N :=
  ((PTrieT.c_trie + 1) * N.of_nat (width + 1))%N.

(** One unit covers the common width and is positive even for empty inputs. *)
Lemma dom_order_removal_unit_width width :
  (N.of_nat (width + 1) <= dom_order_removal_unit width)%N.
Proof.
  unfold dom_order_removal_unit.
  rewrite <- (N.mul_1_l (N.of_nat (width + 1))) at 1.
  apply N.mul_le_mono_r. lia.
Qed.

(** A bounded numeric key makes one write fit two common units. *)
Lemma dom_order_removal_set_clock {A} width (table : ptrie A) vertex value :
  N.size_nat vertex <= width ->
  (PTrieCode.T_set (dom_lt_key vertex) value table <=
    2 * dom_order_removal_unit width)%N.
Proof.
  intro Hwidth. pose proof (dom_lt_key_width vertex) as Hkey.
  pose proof (PTrieT.T_set_le A (dom_lt_key vertex) value table) as Hset.
  change (PTrieCode.T_set (dom_lt_key vertex) value table <=
    PTrieT.c_trie * N.of_nat (Pos.size_nat (dom_lt_key vertex) + 1))%N in Hset.
  eapply N.le_trans; [exact Hset|]. unfold dom_order_removal_unit.
  replace (2 * ((PTrieT.c_trie + 1) * N.of_nat (width + 1)))%N with
    ((PTrieT.c_trie + 1) * (2 * N.of_nat (width + 1)))%N by ring.
  apply N.mul_le_mono; [lia|].
  change (N.of_nat (Pos.size_nat (dom_lt_key vertex) + 1) <=
    N.of_nat 2 * N.of_nat (width + 1))%N.
  rewrite <- Nat2N.inj_mul. apply time_of_nat_le. lia.
Qed.

(** Source insertion performs three bounded-key writes and at most one count increment. *)
Lemma dom_source_add_clock width tree vertex source parent :
  N.size_nat vertex <= width -> N.size_nat source <= width ->
  N.size_nat (dom_order_number (source_count tree) source) <= width ->
  (T_dom_source_add tree vertex source parent <=
    128 * (PTrieT.c_trie + 1) * N.of_nat (width + 1))%N.
Proof.
  intros Hvertex Hsource Hcount.
  pose proof (dom_lt_time_key vertex) as Hvertex_key.
  pose proof (dom_lt_time_key source) as Hsource_key.
  pose proof (dom_lt_key_width vertex) as Hvertex_bits.
  pose proof (dom_lt_key_width source) as Hsource_bits.
  pose proof (N.T_eqb_le source parent) as Hcompare.
  pose proof (dom_order_row_clock (source_children tree) source) as Hrow.
  pose proof (dom_order_number_clock (source_count tree) source) as Hnumber.
  pose proof (N.T_succ_le (dom_order_number (source_count tree) source)) as Hsucc.
  pose proof (dom_order_removal_set_clock width (source_parent tree) vertex source Hvertex)
    as Hparent_set.
  pose proof (dom_order_removal_set_clock width (source_children tree) source
    (vertex :: dom_order_row (source_children tree) source) Hsource) as Hrow_set.
  pose proof (dom_order_removal_set_clock width (source_count tree) source
    (N.succ (dom_order_number (source_count tree) source)) Hsource) as Hcount_set.
  pose proof (dom_order_removal_unit_width width) as Hunit_width.
  set (unit := dom_order_removal_unit width) in *.
  replace (128 * (PTrieT.c_trie + 1) * N.of_nat (width + 1))%N with
    (128 * unit)%N by (unfold unit, dom_order_removal_unit; ring).
  unfold T_dom_source_add. time_simpl.
  destruct (N.eqb source parent); time_simpl; rewrite !Nat2N.inj_add in *;
    change (N.of_nat 1) with 1%N in *; clearbody unit;
    clear -Hvertex Hsource Hcount Hvertex_key Hsource_key Hvertex_bits Hsource_bits
      Hcompare Hrow Hnumber Hsucc Hparent_set Hrow_set Hcount_set Hunit_width; lia.
Qed.

(** Source removal reads one bounded source and decrements its bounded count. *)
Lemma dom_source_remove_clock width tree vertex parent :
  N.size_nat vertex <= width ->
  N.size_nat (dom_lt_identity (source_parent tree) vertex) <= width ->
  N.size_nat (dom_order_number (source_count tree)
    (dom_lt_identity (source_parent tree) vertex)) <= width ->
  (T_dom_source_remove tree vertex parent <=
    128 * (PTrieT.c_trie + 1) * N.of_nat (width + 1))%N.
Proof.
  intros Hvertex Hsource Hcount.
  pose proof (dom_lt_time_identity (source_parent tree) vertex) as Hidentity.
  pose proof (dom_lt_time_key (dom_lt_identity (source_parent tree) vertex)) as Hkey.
  pose proof (dom_lt_key_width (dom_lt_identity (source_parent tree) vertex)) as Hbits.
  pose proof (N.T_eqb_le (dom_lt_identity (source_parent tree) vertex) parent) as Hcompare.
  pose proof (dom_order_number_clock (source_count tree)
    (dom_lt_identity (source_parent tree) vertex)) as Hnumber.
  pose proof (N.T_pred_le (dom_order_number (source_count tree)
    (dom_lt_identity (source_parent tree) vertex))) as Hpred.
  pose proof (dom_order_removal_set_clock width (source_count tree)
    (dom_lt_identity (source_parent tree) vertex)
    (N.pred (dom_order_number (source_count tree)
      (dom_lt_identity (source_parent tree) vertex))) Hsource) as Hset.
  pose proof (dom_order_removal_unit_width width) as Hunit_width.
  set (unit := dom_order_removal_unit width) in *.
  replace (128 * (PTrieT.c_trie + 1) * N.of_nat (width + 1))%N with
    (128 * unit)%N by (unfold unit, dom_order_removal_unit; ring).
  unfold T_dom_source_remove. time_simpl.
  destruct (N.eqb (dom_lt_identity (source_parent tree) vertex) parent); time_simpl;
    rewrite !Nat2N.inj_add in *;
    change (N.of_nat 1) with 1%N in *; clearbody unit;
    clear -Hvertex Hsource Hcount Hidentity Hkey Hbits Hcompare Hnumber Hpred Hset Hunit_width; lia.
Qed.

(** Redirection is one bounded removal followed by one bounded insertion. *)
Lemma dom_source_redirect_clock width tree vertex source parent :
  N.size_nat vertex <= width ->
  N.size_nat (dom_lt_identity (source_parent tree) vertex) <= width ->
  N.size_nat (dom_order_number (source_count tree)
    (dom_lt_identity (source_parent tree) vertex)) <= width ->
  N.size_nat source <= width ->
  N.size_nat (dom_order_number (source_count (dom_source_remove tree vertex parent)) source) <= width ->
  (T_dom_source_redirect tree vertex source parent <=
    512 * (PTrieT.c_trie + 1) * N.of_nat (width + 1))%N.
Proof.
  intros Hvertex Hold Hcount Hsource Hnext.
  pose proof (dom_source_remove_clock width tree vertex parent Hvertex Hold Hcount) as Hremove.
  pose proof (dom_source_add_clock width (dom_source_remove tree vertex parent)
    vertex source parent Hvertex Hsource Hnext) as Hadd.
  unfold T_dom_source_redirect. time_simpl.
  set (remove_work := T_dom_source_remove tree vertex parent) in *.
  set (add_work := T_dom_source_add (dom_source_remove tree vertex parent)
    vertex source parent) in *.
  clearbody remove_work add_work. clear -Hremove Hadd.
  rewrite !Nat2N.inj_add in *. nia.
Qed.

(** * Prefix scans of inverse rows and the shrinking fallback suffix *)

(** Fallback scanning pays only the consumed prefix, at the common numeric-key width. *)
Lemma dom_order_fallback_clock width active remaining :
  Forall (fun vertex => N.size_nat vertex <= width) remaining ->
  (T_dom_order_fallback active remaining <=
    16 * N.of_nat (width + 1) * N.of_nat (dom_order_fallback_steps active remaining + 1))%N.
Proof.
  intro Hremaining. induction Hremaining as [|vertex rest Hvertex Hrest IH].
  - unfold T_dom_order_fallback. time_simpl. cbn [dom_order_fallback_steps].
    rewrite Nat2N.inj_add. nia.
  - pose proof (dom_order_active_clock active vertex) as Hactive.
    time_unfold T_dom_order_fallback. cbn [dom_order_fallback_steps].
    destruct (dom_order_active active vertex); time_simpl;
      rewrite !Nat2N.inj_add, !Nat2N.inj_succ in *; nia.
Qed.

(** Searching a stale inverse row charges each tested vertex at most one bounded lookup chain. *)
Lemma dom_source_child_clock bound width sources active source row :
  dom_lt_trie_all (fun value => (value <= bound)%N) sources ->
  (forall value, (value <= bound)%N -> N.size_nat value <= width) ->
  Forall (fun value => (value <= bound)%N) row ->
  (T_dom_source_child sources active source row <=
    32 * N.of_nat (width + 1) * N.of_nat (length row + 1))%N.
Proof.
  intros Hsources Hwidth Hrow. induction Hrow as [|vertex rest Hvertex Hrest IH].
  - unfold T_dom_source_child. time_simpl. cbn [length]. rewrite Nat2N.inj_add. nia.
  - pose proof (Hwidth vertex Hvertex) as Hvertex_width.
    assert (Hsource_value : (dom_lt_identity sources vertex <= bound)%N)
      by now apply dom_lt_identity_bounded.
    pose proof (Hwidth _ Hsource_value) as Hsource_width.
    pose proof (dom_order_active_clock active vertex) as Hactive.
    pose proof (dom_lt_time_identity sources vertex) as Hidentity.
    pose proof (N.T_eqb_le (dom_lt_identity sources vertex) source) as Hcompare.
    time_unfold T_dom_source_child.
    destruct (dom_order_active active vertex && N.eqb (dom_lt_identity sources vertex) source);
      time_simpl; cbn [length]; rewrite !Nat2N.inj_add, !Nat2N.inj_succ in *;
      clear -Hvertex_width Hsource_width Hactive Hidentity Hcompare IH; nia.
Qed.

(** A named successful continuation exposes exactly the original retirement operations. *)
Definition dom_order_remove_success (parents : ptrie N) (blue red : dom_source_tree)
    (active : ptrie bool) (vertex : N) (queue remaining : list N)
    (records : list (N * N * N)) (b r nr : N) : dom_order_removal_state :=
  let p := dom_lt_identity parents vertex in
  let red_leaf := N.eqb nr 0%N in
  let anchor := if red_leaf then b else r in
  let witness := if red_leaf then r else b in
  let source_tree := if red_leaf then blue else red in
  let child := dom_source_child (source_parent source_tree) active vertex
    (dom_order_row (source_children source_tree) vertex) in
  let blue := dom_source_remove blue vertex p in
  let red := dom_source_remove red vertex p in
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
  DomOrderRemovalState blue red (PTrieCode.set (dom_lt_key vertex) false active)
    queue remaining ((vertex, anchor, witness) :: records).
TimeFun dom_order_remove_success.

(** The retirement continuation has one row search, two removals and at most one redirect. *)
Lemma dom_order_remove_success_overhead parents blue red active vertex queue remaining records b r nr :
  let p := dom_lt_identity parents vertex in
  let red_leaf := N.eqb nr 0%N in
  let tree := if red_leaf then blue else red in
  let child := dom_source_child (source_parent tree) active vertex
    (dom_order_row (source_children tree) vertex) in
  (T_dom_order_remove_success parents blue red active vertex queue remaining records b r nr <=
    T_dom_lt_identity parents vertex + N.T_eqb nr 0%N +
    T_dom_order_row (source_children tree) vertex +
    T_dom_source_child (source_parent tree) active vertex
      (dom_order_row (source_children tree) vertex) +
    T_dom_source_remove blue vertex p + T_dom_source_remove red vertex p +
    (match child with
    | None => 0
    | Some child => if red_leaf then
        T_dom_source_redirect (dom_source_remove blue vertex p) child b p else
        T_dom_source_redirect (dom_source_remove red vertex p) child r p
    end) + T_dom_lt_key vertex + PTrieCode.T_set (dom_lt_key vertex) false active + 64)%N.
Proof.
  cbn zeta. unfold T_dom_order_remove_success.
  destruct (N.eqb nr 0%N); cbn beta iota zeta.
  - destruct (dom_source_child (source_parent blue) active vertex
      (dom_order_row (source_children blue) vertex)); time_simpl; lia.
  - destruct (dom_source_child (source_parent red) active vertex
      (dom_order_row (source_children red) vertex)); time_simpl; lia.
Qed.

(** Queue processing adds only guard clocks around the named successful continuation. *)
Lemma dom_order_remove_queue_overhead parents blue red active vertex queue remaining records :
  let b := dom_lt_identity (source_parent blue) vertex in
  let r := dom_lt_identity (source_parent red) vertex in
  let nb := dom_order_number (source_count blue) vertex in
  let nr := dom_order_number (source_count red) vertex in
  let eligible := N.ltb (N.add nb nr) (if N.eqb b r then 1%N else 2%N) in
  (T_dom_order_remove_step parents
      (DomOrderRemovalState blue red active (vertex :: queue) remaining records) <=
    T_dom_order_active active vertex +
    T_dom_lt_identity (source_parent blue) vertex +
    T_dom_lt_identity (source_parent red) vertex +
    T_dom_order_number (source_count blue) vertex +
    T_dom_order_number (source_count red) vertex +
    N.T_eqb b r + N.T_add nb nr +
    N.T_ltb (N.add nb nr) (if N.eqb b r then 1%N else 2%N) +
    (if dom_order_active active vertex then
      if eligible then
        T_dom_order_remove_success parents blue red active vertex queue remaining records b r nr
      else 0
    else 0) + 64)%N.
Proof.
  cbn zeta. unfold T_dom_order_remove_step.
  cbn [removal_blue removal_red removal_active removal_queue removal_fallback removal_records].
  destruct (dom_order_active active vertex); [|time_simpl; lia].
  destruct (N.ltb
    (N.add (dom_order_number (source_count blue) vertex)
      (dom_order_number (source_count red) vertex))
    (if N.eqb (dom_lt_identity (source_parent blue) vertex)
      (dom_lt_identity (source_parent red) vertex) then 1%N else 2%N));
    [|time_simpl; lia].
  unfold T_dom_order_remove_success.
  destruct (N.eqb (dom_order_number (source_count red) vertex) 0%N); cbn beta iota zeta.
  - destruct (dom_source_child (source_parent blue) active vertex
      (dom_order_row (source_children blue) vertex)); time_simpl; lia.
  - destruct (dom_source_child (source_parent red) active vertex
      (dom_order_row (source_children red) vertex)); time_simpl; lia.
Qed.

(** Naming the two original setup callbacks bounds the generated wrapper without changing it. *)
Lemma dom_order_removal_overhead limit parents order sources :
  let children := filter (dom_order_removal_keep parents) order in
  let initial := DomOrderRemovalState
    (dom_source_initial parents (source_blue sources) children)
    (dom_source_initial parents (source_red sources) children)
    (fold_left dom_order_removal_activate children Empty) children children [] in
  (T_dom_order_removal limit parents order sources <=
    List.T_filter (dom_order_removal_keep parents) (T_dom_order_removal_keep parents) order +
    List.T_fold_left dom_order_removal_activate T_dom_order_removal_activate children Empty +
    T_dom_source_initial parents (source_blue sources) children +
    T_dom_source_initial parents (source_red sources) children +
    T_loopN (dom_order_remove_step parents) (T_dom_order_remove_step parents)
      (N.double (N.double (N.double (N.double limit))) + 3)%N initial +
    64 * N.of_nat (N.size_nat limit + 1))%N.
Proof.
  cbn zeta.
  pose proof (dom_lt_double_width limit) as Hfirst.
  pose proof (dom_lt_double_width (N.double limit)) as Hsecond.
  pose proof (dom_lt_double_width (N.double (N.double limit))) as Hthird.
  pose proof (dom_lt_double_width (N.double (N.double (N.double limit)))) as Hfourth.
  pose proof (N.T_add_le (N.double (N.double (N.double (N.double limit)))) 3%N) as Hadd.
  unfold T_dom_order_removal. time_simpl.
  fold (dom_order_removal_keep parents).
  fold dom_order_removal_activate.
  set (children := filter (dom_order_removal_keep parents) order) in *.
  set (initial := DomOrderRemovalState
    (dom_source_initial parents (source_blue sources) children)
    (dom_source_initial parents (source_red sources) children)
    (fold_left dom_order_removal_activate children Empty) children children []) in *.
  lazymatch goal with
  | |- context [List.T_filter ?predicate ?clock order] =>
      assert (Hfilter : (List.T_filter predicate clock order <=
        List.T_filter (dom_order_removal_keep parents) (T_dom_order_removal_keep parents) order)%N)
        by (apply dom_order_removal_filter_mono; intro vertex;
          unfold T_dom_order_removal_keep; time_simpl; lia)
  end.
  lazymatch goal with
  | |- context [List.T_fold_left ?step ?clock children Empty] =>
      assert (Hactive : (List.T_fold_left step clock children Empty <=
        List.T_fold_left dom_order_removal_activate T_dom_order_removal_activate children Empty)%N)
        by (apply dom_order_fold_clock_mono; intros active vertex;
          unfold T_dom_order_removal_activate; time_simpl; lia)
  end.
  change (fun (active : ptrie bool) (vertex : N) =>
    PTrieCode.set (dom_lt_key vertex) true active) with dom_order_removal_activate in *.
  fold initial.
  lazymatch goal with
  | |- (?lhs <= _)%N => lazymatch lhs with
    | context [T_loopN ?step ?clock ?fuel ?state] =>
        change (T_loopN step clock fuel state) with
          (T_loopN (dom_order_remove_step parents) (T_dom_order_remove_step parents)
            (N.double (N.double (N.double (N.double limit))) + 3)%N initial)
    end
  end.
  clearbody initial children.
  lazymatch goal with
  | |- context [match ?outcome with inl _ => 1%N | inr _ => 0%N end] => destruct outcome
  end;
    time_simpl; cbn [N.size_nat Pos.size_nat] in Hadd;
    rewrite !Nat2N.inj_add in *;
    clear -Hfirst Hsecond Hthird Hfourth Hadd Hfilter Hactive; lia.
Qed.

Local Opaque dom_order_colour T_dom_order_colour dom_order_indexes T_dom_order_indexes dom_order_number_tree T_dom_order_number_tree.

(** * Complete source-map construction clocks

    Finite child rows and numbering counters share the polynomial operand budget.
    The two index-related passes add only one logarithmic factor. *)

(** Reversing the source order preserves the exact predecessor-row mass. *)
Lemma dom_order_rows_mass_reverse order (rows : ptrie (list N)) :
  dom_lt_row_mass (map dom_lt_key (rev_append order [])) rows =
    dom_lt_row_mass (map dom_lt_key order) rows.
Proof.
  rewrite <- !dom_order_rows_sum.
  rewrite rev_append_rev, app_nil_r. apply dom_lt_sum_rev.
Qed.

(** The source-map wrapper adds only projection calls around its four measured passes. *)
Lemma dom_order_source_maps_overhead numeric semis minimizer relative parents :
  let order := lt_numeric_order numeric in
  let rows := fold_left (dom_order_child_add parents) order Empty in
  let walk := dom_order_number_tree (lt_numeric_limit numeric) rows in
  let indexes := dom_order_indexes order rows (order_pre walk) in
  (T_dom_order_source_maps numeric semis minimizer relative parents <=
    List.T_fold_left (dom_order_child_add parents) (T_dom_order_child_add parents) order Empty +
    T_dom_order_number_tree (lt_numeric_limit numeric) rows +
    T_dom_order_indexes order rows (order_pre walk) +
    List.T_fold_left (dom_order_colour numeric semis minimizer relative parents indexes walk)
      (T_dom_order_colour numeric semis minimizer relative parents indexes walk)
      (rev_append order []) (DomOrderSources Empty Empty Empty) +
    (List.T_rev_append order [] + 16))%N.
Proof.
  intros order rows walk indexes.
  unfold T_dom_order_source_maps. time_simpl. fold order rows walk indexes.
  change (fun (current : ptrie (list N)) (vertex : N) =>
    T_dom_order_child_add parents current vertex) with (T_dom_order_child_add parents).
  change (fun (current : dom_order_sources) (vertex : N) =>
    T_dom_order_colour numeric semis minimizer relative parents indexes walk current vertex)
    with (T_dom_order_colour numeric semis minimizer relative parents indexes walk).
  clearbody order rows walk indexes. lia.
Qed.

(** One closed coefficient covers child rows, numbering, indexes and colouring. *)
Definition dom_order_source_maps_coefficient : N :=
  (3 * dom_order_number_coefficient + 16384 * (PTrieT.c_trie + 1) + 64)%N.

(** Source maps cost linear work in order and predecessor cells with one logarithmic factor. *)
Lemma dom_order_source_maps_time width numeric semis minimizer relative parents :
  NoDup (lt_numeric_order numeric) ->
  dom_lt_numeric_ranges (N.of_nat (length (lt_numeric_order numeric))) numeric ->
  (lt_numeric_limit numeric <= N.of_nat (length (lt_numeric_order numeric) + 1))%N ->
  dom_lt_trie_all (fun value => (value <= N.of_nat (length (lt_numeric_order numeric)))%N) semis ->
  dom_lt_trie_all (fun value => (value <= N.of_nat (length (lt_numeric_order numeric)))%N) minimizer ->
  dom_lt_trie_all (fun value => (value <= N.of_nat (length (lt_numeric_order numeric)))%N) relative ->
  dom_lt_trie_all (fun value => (value <= N.of_nat (length (lt_numeric_order numeric)))%N) parents ->
  (forall value, (value <= 8 * (N.of_nat (length (lt_numeric_order numeric)) + 1) *
    (N.of_nat (length (lt_numeric_order numeric)) + 1))%N -> N.size_nat value <= width) ->
  (T_dom_order_source_maps numeric semis minimizer relative parents <=
    dom_order_source_maps_coefficient *
    N.of_nat ((length (lt_numeric_order numeric) +
      dom_lt_row_mass (map dom_lt_key (lt_numeric_order numeric)) (lt_numeric_pred numeric) + 1) *
      (Nat.log2 (length (lt_numeric_order numeric)) + 1) * (width + 1)))%N.
Proof.
  intros Hunique Hranges Hlimit Hsemis Hminimizer Hrelative Hparents Hwidth.
  set (order := lt_numeric_order numeric) in *.
  set (count := length order) in *.
  set (levels := Nat.log2 count + 1).
  set (predecessors := dom_lt_row_mass (map dom_lt_key order) (lt_numeric_pred numeric)).
  fold levels predecessors.
  destruct Hranges as [Horder Hnumeric_parent Hpredecessors]. fold order in Horder.
  assert (Hsmall : (N.of_nat (count + 2) <=
    8 * (N.of_nat count + 1) * (N.of_nat count + 1))%N).
  { rewrite Nat2N.inj_add. change (N.of_nat 2) with 2%N.
    clearbody count. clear -count. nia. }
  assert (Hsmall_width : forall value, (value <= N.of_nat (count + 2))%N ->
    N.size_nat value <= width).
  { intros value Hvalue. apply Hwidth. eapply N.le_trans; eassumption. }
  assert (Hrank_width : forall value, (value <= N.of_nat count)%N ->
    N.size_nat value <= width).
  { intros value Hvalue. apply Hsmall_width.
    eapply N.le_trans; [exact Hvalue|]. apply time_of_nat_le. lia. }
  assert (Htables : forall table,
    dom_lt_trie_all (fun value => (value <= N.of_nat count)%N) table ->
    dom_lt_trie_all (fun value => N.size_nat value <= width) table).
  { intros table Htable key value Hget. apply Hrank_width. exact (Htable _ _ Hget). }
  assert (Horder_width : Forall (fun vertex => N.size_nat vertex <= width) order).
  { apply Forall_forall. intros vertex Hin. apply Hrank_width.
    exact (proj1 (Forall_forall _ _) Horder vertex Hin). }
  set (rows := fold_left (dom_order_child_add parents) order Empty).
  assert (Hrows : dom_lt_trie_all (Forall (fun value => (value <= N.of_nat count)%N)) rows).
  { apply dom_order_child_fold_forall; [exact Horder|apply dom_lt_trie_all_empty]. }
  assert (Hrows_width : dom_lt_trie_all (Forall (fun value => N.size_nat value <= width)) rows).
  { apply dom_order_child_fold_forall; [exact Horder_width|apply dom_lt_trie_all_empty]. }
  set (keys := dom_order_key_universe count).
  assert (Hkeys_unique : NoDup keys) by (apply dom_order_key_universe_unique).
  assert (Hkeys_length : length keys = count + 2) by (apply dom_order_key_universe_length).
  assert (Hroot : In (dom_lt_key 1%N) keys) by (apply dom_order_key_universe_root).
  assert (Hrows_members : dom_lt_trie_all
    (Forall (fun vertex => In (dom_lt_key vertex) keys)) rows).
  { apply dom_order_key_universe_rows. exact Hrows. }
  assert (Hkeys_width : forall vertex, In (dom_lt_key vertex) keys ->
    N.size_nat vertex <= width).
  { intros vertex Hin. apply Hsmall_width.
    pose proof (dom_order_key_universe_bound count vertex Hin) as Hbound.
    eapply N.le_trans; [exact Hbound|]. apply time_of_nat_le. lia. }
  assert (Hcounter_width : forall value, (value <= N.of_nat (length keys))%N ->
    N.size_nat value <= width).
  { intros value Hvalue. apply Hsmall_width. now rewrite Hkeys_length in Hvalue. }
  assert (Hlimit_width : N.size_nat (lt_numeric_limit numeric) <= width).
  { apply Hsmall_width. eapply N.le_trans; [exact Hlimit|]. apply time_of_nat_le. lia. }
  set (walk := dom_order_number_tree (lt_numeric_limit numeric) rows).
  pose proof (dom_order_number_tree_inventory keys (lt_numeric_limit numeric) rows
    Hkeys_unique Hroot Hrows_members) as Hwalk. fold walk in Hwalk.
  destruct Hwalk as [_ [_ [Hpre Hpost]]].
  assert (Hpre_width : dom_lt_trie_all (fun value => N.size_nat value <= width) (order_pre walk)).
  { intros key value Hget. apply Hcounter_width. exact (Hpre _ _ Hget). }
  assert (Hheight : forall vertex, In vertex order ->
    N.size_nat (N.of_nat (length (dom_order_row rows vertex))) <= levels).
  { intros vertex Hin. unfold levels. apply dom_order_value_log_width.
    apply time_of_nat_le. unfold rows, count. apply dom_order_children_row_length. }
  set (indexes := dom_order_indexes order rows (order_pre walk)).
  assert (Hindex_values : dom_lt_trie_all
    (dom_order_index_values (fun value => N.size_nat value <= width) (fun _ => True)) indexes).
  { apply dom_order_indexes_values. exact Hrows_width. }
  assert (Hindex_height : dom_lt_trie_all
    (fun index => dom_order_index_height index <= levels) indexes).
  { apply dom_order_indexes_height. exact Hheight. }
  assert (Hencoded_unique : NoDup (map dom_lt_key order)).
  { apply dom_lt_map_unique_on; [exact Hunique|].
    intros left right Hleft Hright Heq. now apply dom_lt_key_injective in Heq. }
  pose proof (dom_order_children_mass keys parents order Hkeys_unique) as Huniverse_mass.
  pose proof (dom_order_children_mass (map dom_lt_key order) parents order Hencoded_unique)
    as Hindex_mass.
  fold rows count in Huniverse_mass, Hindex_mass.
  pose proof (dom_order_child_fold_clock width parents Empty order Horder_width
    (Htables parents Hparents)) as Hchild_clock. fold count in Hchild_clock.
  pose proof (dom_order_number_tree_clock keys rows (lt_numeric_limit numeric) width
    Hkeys_unique Hroot Hrows_members Hkeys_width Hcounter_width Hlimit_width) as Hnumber_clock.
  assert (Hnumber_paid : (T_dom_order_number_tree (lt_numeric_limit numeric) rows <=
    dom_order_number_coefficient * N.of_nat ((2 * count + 3) * (width + 1)))%N).
  { eapply N.le_trans; [exact Hnumber_clock|]. apply N.mul_le_mono_l.
    apply time_of_nat_le. apply Nat.mul_le_mono_r. rewrite Hkeys_length. lia. }
  pose proof (dom_order_indexes_clock width levels order rows (order_pre walk)
    Horder_width Hrows_width Hheight) as Hindex_clock. fold count in Hindex_clock.
  assert (Hindex_paid : (T_dom_order_indexes order rows (order_pre walk) <=
    2048 * (PTrieT.c_trie + 1) *
      N.of_nat ((2 * count + 1) * (levels + 1) * (width + 1)))%N).
  { eapply N.le_trans; [exact Hindex_clock|]. apply N.mul_le_mono_l.
    apply time_of_nat_le. apply Nat.mul_le_mono_r. apply Nat.mul_le_mono_r. lia. }
  assert (Hreverse_width : Forall (fun vertex => N.size_nat vertex <= width)
    (rev_append order [])).
  { rewrite rev_append_rev, app_nil_r. now apply Forall_rev. }
  pose proof (dom_order_colour_fold_clock width levels numeric semis minimizer relative
    parents indexes walk (rev_append order []) (DomOrderSources Empty Empty Empty)
    Hreverse_width (Htables semis Hsemis) (Htables minimizer Hminimizer)
    (Htables relative Hrelative) (Htables (lt_numeric_parent numeric) Hnumeric_parent)
    (Htables parents Hparents) Hindex_values Hindex_height Hpre_width) as Hcolour_clock.
  rewrite dom_order_rows_mass_reverse in Hcolour_clock.
  replace (length (rev_append order [])) with count in Hcolour_clock
    by (unfold count; rewrite rev_append_rev, app_nil_r, length_rev; reflexivity).
  fold predecessors in Hcolour_clock.
  pose proof (List.T_rev_append_le order []) as Hreverse. fold count in Hreverse.
  assert (Hsetup : (List.T_rev_append order [] + 16 <=
    64 * N.of_nat ((count + 1) * (width + 1)))%N).
  { rewrite !Nat2N.inj_mul, !Nat2N.inj_add in *.
    change (N.of_nat 1) with 1%N in *. clear -Hreverse. nia. }
  pose proof (dom_order_source_maps_overhead numeric semis minimizer relative parents) as Htotal.
  fold order rows walk indexes in Htotal.
  assert (Hlevels : (1 <= N.of_nat levels)%N).
  { unfold levels. rewrite Nat2N.inj_add. change (N.of_nat 1) with 1%N. lia. }
  assert (Hwidth_positive : (1 <= N.of_nat (width + 1))%N)
    by (rewrite Nat2N.inj_add; change (N.of_nat 1) with 1%N; lia).
  repeat first [rewrite Nat2N.inj_mul in Hchild_clock | rewrite Nat2N.inj_add in Hchild_clock].
  repeat first [rewrite Nat2N.inj_mul in Hnumber_paid | rewrite Nat2N.inj_add in Hnumber_paid].
  repeat first [rewrite Nat2N.inj_mul in Hindex_paid | rewrite Nat2N.inj_add in Hindex_paid].
  repeat first [rewrite Nat2N.inj_mul in Hcolour_clock | rewrite Nat2N.inj_add in Hcolour_clock].
  repeat first [rewrite Nat2N.inj_mul in Hsetup | rewrite Nat2N.inj_add in Hsetup].
  pose proof (dom_order_source_maps_budget PTrieT.c_trie dom_order_number_coefficient
    (N.of_nat count) (N.of_nat predecessors) (N.of_nat levels) (N.of_nat (width + 1))
    (List.T_fold_left (dom_order_child_add parents) (T_dom_order_child_add parents) order Empty)
    (T_dom_order_number_tree (lt_numeric_limit numeric) rows)
    (T_dom_order_indexes order rows (order_pre walk))
    (List.T_fold_left (dom_order_colour numeric semis minimizer relative parents indexes walk)
      (T_dom_order_colour numeric semis minimizer relative parents indexes walk)
      (rev_append order []) (DomOrderSources Empty Empty Empty))
    (List.T_rev_append order [] + 16)%N
    (T_dom_order_source_maps numeric semis minimizer relative parents)) as Htime.
  repeat rewrite Nat2N.inj_add in Htime.
  repeat rewrite Nat2N.inj_add in Hwidth_positive.
  specialize (Htime Hlevels Hwidth_positive Hchild_clock Hnumber_paid Hindex_paid
    Hcolour_clock Hsetup Htotal).
  unfold dom_order_source_maps_coefficient.
  repeat first [rewrite Nat2N.inj_mul | rewrite Nat2N.inj_add]. exact Htime.
Qed.

Local Transparent dom_order_colour T_dom_order_colour dom_order_indexes T_dom_order_indexes dom_order_number_tree T_dom_order_number_tree.

Local Opaque Argent.Loop.loop T_loopN.

(** A source insertion inherits all of its primitive width bounds from the stale inventory. *)
Lemma dom_source_add_bounded_clock count width tree vertex source parent :
  (forall value, (value <= 8 * (N.of_nat count + 1) * (N.of_nat count + 1))%N ->
    N.size_nat value <= width) ->
  dom_source_numeric_bounded count tree ->
  (vertex <= N.of_nat count)%N -> (source <= N.of_nat count)%N ->
  (T_dom_source_add tree vertex source parent <=
    128 * (PTrieT.c_trie + 1) * N.of_nat (width + 1))%N.
Proof.
  intros Hwidth Htree Hvertex Hsource.
  apply (dom_source_add_clock width tree vertex source parent).
  - exact (dom_order_removal_base_width count width Hwidth vertex Hvertex).
  - exact (dom_order_removal_base_width count width Hwidth source Hsource).
  - exact (dom_source_numeric_count_width count width tree source Hwidth Htree Hsource).
Qed.

(** A count removal needs no semantic relationship between its vertex and parent argument. *)
Lemma dom_source_remove_bounded_clock count width tree vertex parent :
  (forall value, (value <= 8 * (N.of_nat count + 1) * (N.of_nat count + 1))%N ->
    N.size_nat value <= width) ->
  dom_source_numeric_bounded count tree -> (vertex <= N.of_nat count)%N ->
  (T_dom_source_remove tree vertex parent <=
    128 * (PTrieT.c_trie + 1) * N.of_nat (width + 1))%N.
Proof.
  intros Hwidth Htree Hvertex.
  pose proof (dom_source_numeric_value count tree vertex Htree Hvertex) as Hsource.
  apply (dom_source_remove_clock width tree vertex parent).
  - exact (dom_order_removal_base_width count width Hwidth vertex Hvertex).
  - exact (dom_order_removal_base_width count width Hwidth _ Hsource).
  - exact (dom_source_numeric_count_width count width tree _ Hwidth Htree Hsource).
Qed.

(** Redirection retains bounded counts through its preliminary count removal. *)
Lemma dom_source_redirect_bounded_clock count width tree vertex source parent :
  (forall value, (value <= 8 * (N.of_nat count + 1) * (N.of_nat count + 1))%N ->
    N.size_nat value <= width) ->
  dom_source_numeric_bounded count tree ->
  (vertex <= N.of_nat count)%N -> (source <= N.of_nat count)%N ->
  (T_dom_source_redirect tree vertex source parent <=
    512 * (PTrieT.c_trie + 1) * N.of_nat (width + 1))%N.
Proof.
  intros Hwidth Htree Hvertex Hsource.
  pose proof (dom_source_numeric_value count tree vertex Htree Hvertex) as Hold.
  pose proof (dom_source_remove_numeric_bounded count tree vertex parent Htree) as Hnext.
  apply (dom_source_redirect_clock width tree vertex source parent).
  - exact (dom_order_removal_base_width count width Hwidth vertex Hvertex).
  - exact (dom_order_removal_base_width count width Hwidth _ Hold).
  - exact (dom_source_numeric_count_width count width tree _ Hwidth Htree Hold).
  - exact (dom_order_removal_base_width count width Hwidth source Hsource).
  - exact (dom_source_numeric_count_width count width (dom_source_remove tree vertex parent)
      source Hwidth Hnext Hsource).
Qed.
(** * Source initialization clocks *)

(** Naming the existing initialization callback provides its automatically derived clock. *)
Definition dom_source_initial_step (parents sources : ptrie N)
    (tree : dom_source_tree) (vertex : N) : dom_source_tree :=
  match trie_get (dom_lt_key vertex) parents with
  | None => tree
  | Some parent => dom_source_add tree vertex (dom_lt_identity sources vertex) parent
  end.
TimeFun dom_source_initial_step.

(** Each initialization callback performs one bounded lookup and at most one bounded insertion. *)
Lemma dom_source_initial_step_clock count width parents sources tree vertex :
  (forall value, (value <= 8 * (N.of_nat count + 1) * (N.of_nat count + 1))%N ->
    N.size_nat value <= width) ->
  dom_lt_trie_all (fun value => (value <= N.of_nat count)%N) sources ->
  dom_source_numeric_bounded count tree -> (vertex <= N.of_nat count)%N ->
  (T_dom_source_initial_step parents sources tree vertex <=
    256 * (PTrieT.c_trie + 1) * N.of_nat (width + 1))%N.
Proof.
  intros Hwidth Hsources Htree Hvertex.
  pose proof (dom_order_removal_base_width count width Hwidth vertex Hvertex) as Hvertex_width.
  pose proof (dom_lt_identity_bounded (N.of_nat count) sources vertex Hsources Hvertex)
    as Hsource.
  pose proof (dom_lt_time_key vertex) as Hkey.
  pose proof (dom_lt_key_width vertex) as Hkey_width.
  pose proof (dom_lt_time_identity sources vertex) as Hidentity.
  pose proof (dom_order_removal_unit_width width) as Hunit.
  replace (256 * (PTrieT.c_trie + 1) * N.of_nat (width + 1))%N with
    (256 * dom_order_removal_unit width)%N by (unfold dom_order_removal_unit; ring).
  set (unit := dom_order_removal_unit width) in *.
  unfold T_dom_source_initial_step. time_simpl. PTrieT.trie_get_le.
  destruct (trie_get (dom_lt_key vertex) parents) as [parent|].
  - pose proof (dom_source_add_bounded_clock count width tree vertex
      (dom_lt_identity sources vertex) parent Hwidth Htree Hvertex Hsource) as Hadd.
    rewrite <- N.mul_assoc in Hadd. fold (dom_order_removal_unit width) in Hadd.
    fold unit in Hadd. time_simpl. clearbody unit.
    clear -Hvertex_width Hkey Hkey_width Hidentity Hadd Hunit. PTrieT.trie_get_le.
    rewrite !Nat2N.inj_add in *. lia.
  - time_simpl. clearbody unit. clear -Hvertex_width Hkey Hkey_width Hunit. PTrieT.trie_get_le.
    rewrite !Nat2N.inj_add in *. lia.
Qed.

(** The named callback adds only wrapper calls to the original initialization fold. *)
Lemma dom_source_initial_overhead parents sources order :
  (T_dom_source_initial parents sources order <=
    List.T_fold_left (dom_source_initial_step parents sources)
      (T_dom_source_initial_step parents sources) order (DomSourceTree Empty Empty Empty) + 8)%N.
Proof.
  unfold T_dom_source_initial. time_simpl.
  eapply N.le_trans with (1 +
    List.T_fold_left (dom_source_initial_step parents sources)
      (T_dom_source_initial_step parents sources) order (DomSourceTree Empty Empty Empty))%N.
  - apply N.add_le_mono_l. apply dom_order_fold_clock_mono.
    intros tree vertex. unfold T_dom_source_initial_step. time_simpl. lia.
  - lia.
Qed.

Definition dom_source_initial_invariant (count total : nat) (rest : list N)
    (tree : dom_source_tree) : Prop :=
  dom_source_range (N.of_nat count) tree /\ dom_source_counts_fit tree /\
  dom_lt_row_mass (dom_order_key_universe count) (source_children tree) + length rest <= total /\
  Forall (fun value => (value <= N.of_nat count)%N) rest.

(** An insertion consumes one pending input and adds at most one retained inverse occurrence. *)
Lemma dom_source_initial_invariant_step count total parents sources vertex rest tree :
  dom_lt_trie_all (fun value => (value <= N.of_nat count)%N) sources ->
  dom_source_initial_invariant count total (vertex :: rest) tree ->
  dom_source_initial_invariant count total rest
    (dom_source_initial_step parents sources tree vertex).
Proof.
  intros Hsources [Hrange [Hcounts [Hmass Hrest]]].
  inversion Hrest as [|head tail Hvertex Htail]; subst head tail.
  unfold dom_source_initial_step.
  destruct (trie_get (dom_lt_key vertex) parents) as [parent|].
  - assert (Hsource : (dom_lt_identity sources vertex <= N.of_nat count)%N).
    { exact (dom_lt_identity_bounded (N.of_nat count) sources vertex Hsources Hvertex). }
    pose proof (dom_source_add_mass (dom_order_key_universe count) tree vertex
      (dom_lt_identity sources vertex) parent (dom_order_key_universe_unique count)) as Hnext.
    split; [now apply dom_source_add_range|].
    split; [now apply dom_source_add_counts|]. split; [cbn [length] in Hmass; lia|exact Htail].
  - split; [exact Hrange|]. split; [exact Hcounts|].
    split; [cbn [length] in Hmass; lia|exact Htail].
Qed.

(** Every partial initialization tree fits the callback's numeric count ceiling. *)
Lemma dom_source_initial_numeric_bounded count total rest tree :
  total <= count -> dom_source_initial_invariant count total rest tree ->
  dom_source_numeric_bounded count tree.
Proof.
  intros Htotal [Hrange [Hcounts [Hmass Hrest]]].
  split; [exact Hrange|]. split; [exact Hcounts|]. lia.
Qed.

(** The constant callback allowance pays the fold calls and its outer wrapper. *)
Lemma dom_source_initial_clock_budget (unit count fold_work total_work : N) :
  (8 <= unit)%N -> (fold_work <= (unit + 1) * count + 1)%N ->
  (total_work <= fold_work + 8)%N -> (total_work <= 2 * unit * (count + 1))%N.
Proof.
  intros Hunit Hfold Htotal. nia.
Qed.

(** Source initialization is linear in the supplied input length at the common width. *)
Lemma dom_source_initial_time count width parents sources order :
  (forall value, (value <= 8 * (N.of_nat count + 1) * (N.of_nat count + 1))%N ->
    N.size_nat value <= width) ->
  dom_lt_trie_all (fun value => (value <= N.of_nat count)%N) sources ->
  Forall (fun value => (value <= N.of_nat count)%N) order -> length order <= count ->
  (T_dom_source_initial parents sources order <=
    512 * (PTrieT.c_trie + 1) * N.of_nat ((length order + 1) * (width + 1)))%N.
Proof.
  intros Hwidth Hsources Horder Hlength.
  set (unit := (256 * (PTrieT.c_trie + 1) * N.of_nat (width + 1))%N).
  assert (Hunit : (8 <= unit)%N).
  { unfold unit. change (8 * 1 <= (256 * (PTrieT.c_trie + 1)) * N.of_nat (width + 1))%N.
    apply N.mul_le_mono; [lia|rewrite Nat2N.inj_add; lia]. }
  assert (Hinitial : dom_source_initial_invariant count (length order) order
    (DomSourceTree Empty Empty Empty)).
  { split; [split; apply dom_lt_trie_all_empty|].
    split; [apply dom_source_empty_counts|]. split; [|exact Horder].
    cbn [source_children]. rewrite dom_lt_row_mass_empty. lia. }
  pose proof (dom_lt_fold_credit (dom_source_initial_step parents sources)
    (T_dom_source_initial_step parents sources)
    (dom_source_initial_invariant count (length order)) (fun _ => 0%N) unit order) as Hfold.
  specialize (Hfold ltac:(intros vertex rest tree Htree;
    exact (dom_source_initial_invariant_step count (length order) parents sources
      vertex rest tree Hsources Htree))).
  specialize (Hfold ltac:(intros vertex rest tree Htree; cbn beta; rewrite !N.add_0_r;
    apply (dom_source_initial_step_clock count width parents sources tree vertex);
    [exact Hwidth|exact Hsources|
      exact (dom_source_initial_numeric_bounded count (length order) (vertex :: rest)
        tree Hlength Htree)|];
    destruct Htree as [Hrange [Hcounts [Hmass Hrest]]]; now inversion Hrest)).
  specialize (Hfold (DomSourceTree Empty Empty Empty) Hinitial).
  destruct Hfold as [Hfinal Hclock]. cbn beta in Hclock. rewrite !N.add_0_r in Hclock.
  pose proof (dom_source_initial_overhead parents sources order) as Hwrapper.
  rewrite Nat2N.inj_mul, Nat2N.inj_add.
  change (N.of_nat 1) with 1%N.
  replace (512 * (PTrieT.c_trie + 1) *
    ((N.of_nat (length order) + 1) * N.of_nat (width + 1)))%N with
    (2 * unit * (N.of_nat (length order) + 1))%N by (unfold unit; ring).
  eapply dom_source_initial_clock_budget; [exact Hunit|exact Hclock|exact Hwrapper].
Qed.
(** The eligibility test has a constant allowance at the common operand width. *)
Lemma dom_order_remove_guard_clock count width blue red active vertex :
  (forall value, (value <= 8 * (N.of_nat count + 1) * (N.of_nat count + 1))%N ->
    N.size_nat value <= width) ->
  dom_source_numeric_bounded count blue -> dom_source_numeric_bounded count red ->
  (vertex <= N.of_nat count)%N ->
  (T_dom_order_active active vertex +
    T_dom_lt_identity (source_parent blue) vertex +
    T_dom_lt_identity (source_parent red) vertex +
    T_dom_order_number (source_count blue) vertex +
    T_dom_order_number (source_count red) vertex +
    N.T_eqb (dom_lt_identity (source_parent blue) vertex)
      (dom_lt_identity (source_parent red) vertex) +
    N.T_add (dom_order_number (source_count blue) vertex)
      (dom_order_number (source_count red) vertex) +
    N.T_ltb (N.add (dom_order_number (source_count blue) vertex)
      (dom_order_number (source_count red) vertex))
      (if N.eqb (dom_lt_identity (source_parent blue) vertex)
        (dom_lt_identity (source_parent red) vertex) then 1%N else 2%N) + 64 <=
      256 * dom_order_removal_unit width)%N.
Proof.
  intros Hwidth Hblue Hred Hvertex.
  pose proof (dom_order_removal_base_width count width Hwidth vertex Hvertex) as Hv.
  pose proof (dom_source_numeric_value count blue vertex Hblue Hvertex) as Hb.
  pose proof (dom_order_removal_base_width count width Hwidth _ Hb) as Hbw.
  pose proof (dom_source_numeric_count_width count width blue vertex Hwidth Hblue Hvertex)
    as Hnb.
  pose proof (dom_source_numeric_count_width count width red vertex Hwidth Hred Hvertex)
    as Hnr.
  pose proof (dom_source_numeric_sum_width count width blue red vertex Hwidth Hblue Hred Hvertex)
    as Hsum.
  pose proof (dom_order_active_clock active vertex) as Ha.
  pose proof (dom_lt_time_identity (source_parent blue) vertex) as Hib.
  pose proof (dom_lt_time_identity (source_parent red) vertex) as Hir.
  pose proof (dom_order_number_clock (source_count blue) vertex) as Hcb.
  pose proof (dom_order_number_clock (source_count red) vertex) as Hcr.
  pose proof (N.T_eqb_le (dom_lt_identity (source_parent blue) vertex)
    (dom_lt_identity (source_parent red) vertex)) as Heq.
  pose proof (N.T_add_le (dom_order_number (source_count blue) vertex)
    (dom_order_number (source_count red) vertex)) as Hadd.
  pose proof (dom_lt_time_ltb
    (N.add (dom_order_number (source_count blue) vertex) (dom_order_number (source_count red) vertex))
    (if N.eqb (dom_lt_identity (source_parent blue) vertex)
      (dom_lt_identity (source_parent red) vertex) then 1%N else 2%N)) as Hlt.
  pose proof (dom_order_removal_unit_width width) as Hunit.
  set (unit := dom_order_removal_unit width) in *. clearbody unit.
  clear -Hv Hbw Hnb Hnr Hsum Ha Hib Hir Hcb Hcr Heq Hadd Hlt Hunit.
  rewrite !Nat2N.inj_add in *. lia.
Qed.

(** Fixed retirement work is absorbed by every positive row-work allowance. *)
Lemma dom_order_remove_success_budget (unit work fixed scan redirect total : N) :
  (1 <= unit)%N -> (1 <= work)%N ->
  (fixed <= 512 * unit)%N -> (scan <= 64 * unit * work)%N ->
  (redirect <= 512 * unit)%N -> (total <= fixed + scan + redirect + 64)%N ->
  (total <= 2048 * unit * work)%N.
Proof.
  intros Hunit Hwork Hfixed Hscan Hredirect Htotal.
  assert (Hscale : (unit <= unit * work)%N).
  { rewrite <- (N.mul_1_r unit) at 1. now apply N.mul_le_mono_l. }
  assert (Hpositive : (1 <= unit * work)%N).
  { eapply N.le_trans with unit; [exact Hunit|exact Hscale]. }
  lia.
Qed.

Lemma dom_order_removal_unit_positive width : (1 <= dom_order_removal_unit width)%N.
Proof.
  eapply N.le_trans; [|exact (dom_order_removal_unit_width width)].
  rewrite Nat2N.inj_add. lia.
Qed.

(** A fallback callback adds only one retirement write after its prefix scan. *)
Lemma dom_order_remove_fallback_overhead parents blue red active remaining records :
  (T_dom_order_remove_step parents
      (DomOrderRemovalState blue red active [] remaining records) <=
    T_dom_order_fallback active remaining +
      (match dom_order_fallback active remaining with
      | None => 0
      | Some (vertex, _) => T_dom_lt_identity parents vertex + T_dom_lt_key vertex +
          PTrieCode.T_set (dom_lt_key vertex) false active
      end) + 32)%N.
Proof.
  unfold T_dom_order_remove_step.
  cbn [removal_blue removal_red removal_active removal_queue removal_fallback removal_records].
  destruct (dom_order_fallback active remaining) as [[vertex rest]|]; time_simpl; lia.
Qed.

(** A positive scan allowance absorbs the fixed fallback retirement overhead. *)
Lemma dom_order_remove_fallback_budget (unit work scan extra step_work : N) :
  (1 <= unit)%N -> (1 <= work)%N -> (scan <= 16 * unit * work)%N ->
  (extra <= 64 * unit)%N -> (step_work <= scan + extra + 32)%N ->
  (step_work <= 256 * unit * work)%N.
Proof.
  intros Hunit Hwork Hscan Hextra Hstep.
  assert (Hscale : (unit <= unit * work)%N).
  { rewrite <- (N.mul_1_r unit) at 1. now apply N.mul_le_mono_l. }
  assert (Hpositive : (1 <= unit * work)%N).
  { eapply N.le_trans with unit; [exact Hunit|exact Hscale]. }
  lia.
Qed.

(** Fallback scanning is paid by the consumed-prefix work, uniformly over the source trees. *)
Lemma dom_order_remove_fallback_clock width parents blue red active remaining records :
  Forall (fun vertex => N.size_nat vertex <= width) remaining ->
  (T_dom_order_remove_step parents
      (DomOrderRemovalState blue red active [] remaining records) <=
    256 * dom_order_removal_unit width *
      N.of_nat (dom_order_fallback_steps active remaining + 1))%N.
Proof.
  intro Hremaining.
  pose proof (dom_order_remove_fallback_overhead parents blue red active remaining records)
    as Hstep.
  pose proof (dom_order_fallback_clock width active remaining Hremaining) as Hscan.
  assert (Hscan_scaled : (T_dom_order_fallback active remaining <=
    16 * dom_order_removal_unit width *
      N.of_nat (dom_order_fallback_steps active remaining + 1))%N).
  { eapply N.le_trans; [exact Hscan|].
    apply N.mul_le_mono_r. apply N.mul_le_mono_l. apply dom_order_removal_unit_width. }
  set (extra := match dom_order_fallback active remaining with
    | None => 0%N
    | Some (vertex, _) => (T_dom_lt_identity parents vertex + T_dom_lt_key vertex +
        PTrieCode.T_set (dom_lt_key vertex) false active)%N
    end) in Hstep.
  assert (Hextra : (extra <= 64 * dom_order_removal_unit width)%N).
  { unfold extra. destruct (dom_order_fallback active remaining) as [[vertex rest]|] eqn:Hcase;
      [|apply N.le_0_l].
    pose proof (proj1 (dom_order_fallback_forall (fun vertex => N.size_nat vertex <= width)
      active remaining vertex rest Hremaining Hcase)) as Hvertex.
    pose proof (dom_lt_time_identity parents vertex) as Hidentity.
    pose proof (dom_lt_time_key vertex) as Hkey.
    pose proof (dom_order_removal_set_clock width active vertex false Hvertex) as Hset.
    pose proof (dom_order_removal_unit_width width) as Hunit.
    set (unit := dom_order_removal_unit width) in *. clearbody unit.
    rewrite !Nat2N.inj_add in *.
    clear -Hvertex Hidentity Hkey Hset Hunit. lia. }
  eapply dom_order_remove_fallback_budget with
    (scan := T_dom_order_fallback active remaining) (extra := extra).
  - apply dom_order_removal_unit_positive.
  - rewrite Nat2N.inj_add. lia.
  - exact Hscan_scaled.
  - exact Hextra.
  - exact Hstep.
Qed.
(** * Closing the removal callback clock from its bounded source operations *)

(** One retained row lookup and its scan fit the shared two-row allowance. *)
Lemma dom_order_remove_scan_budget (width unit cells work row scan : N) :
  (width <= unit)%N -> (1 <= work)%N -> (cells + 1 <= work)%N ->
  (row <= 8 * width)%N -> (scan <= 32 * width * (cells + 1))%N ->
  (row + scan <= 64 * unit * work)%N.
Proof.
  intros Hwidth Hwork Hcells Hrow Hscan.
  assert (Hscaled : (width * (cells + 1) <= unit * work)%N)
    by now apply N.mul_le_mono.
  assert (Hbase : (width <= unit * work)%N).
  { eapply N.le_trans; [exact Hwidth|].
    rewrite <- (N.mul_1_r unit) at 1. now apply N.mul_le_mono_l. }
  lia.
Qed.

(** A retirement spends the sum of the two retained inverse-row lengths plus one. *)
Lemma dom_order_remove_success_clock count width parents blue red active vertex
    queue remaining records b r nr :
  (forall value, (value <= 8 * (N.of_nat count + 1) * (N.of_nat count + 1))%N ->
    N.size_nat value <= width) ->
  dom_source_numeric_bounded count blue -> dom_source_numeric_bounded count red ->
  (vertex <= N.of_nat count)%N -> (b <= N.of_nat count)%N -> (r <= N.of_nat count)%N ->
  N.size_nat nr <= width ->
  (T_dom_order_remove_success parents blue red active vertex queue remaining records b r nr <=
    2048 * dom_order_removal_unit width *
      N.of_nat (length (dom_order_row (source_children blue) vertex) +
        length (dom_order_row (source_children red) vertex) + 1))%N.
Proof.
  intros Hwidth Hblue Hred Hvertex Hb Hr Hnr.
  pose proof (dom_order_removal_base_width count width Hwidth vertex Hvertex) as Hv.
  set (unit := dom_order_removal_unit width).
  set (work := N.of_nat (length (dom_order_row (source_children blue) vertex) +
    length (dom_order_row (source_children red) vertex) + 1)).
  set (parent := dom_lt_identity parents vertex).
  set (fixed := (T_dom_lt_identity parents vertex + N.T_eqb nr 0%N +
    T_dom_source_remove blue vertex parent + T_dom_source_remove red vertex parent +
    T_dom_lt_key vertex + PTrieCode.T_set (dom_lt_key vertex) false active)%N).
  assert (Hwork : (1 <= work)%N) by (unfold work; rewrite !Nat2N.inj_add; lia).
  assert (Hfixed : (fixed <= 512 * unit)%N).
  { pose proof (dom_source_remove_bounded_clock count width blue vertex parent
      Hwidth Hblue Hvertex) as Hblue_remove.
    pose proof (dom_source_remove_bounded_clock count width red vertex parent
      Hwidth Hred Hvertex) as Hred_remove.
    rewrite <- N.mul_assoc in Hblue_remove, Hred_remove.
    fold (dom_order_removal_unit width) in Hblue_remove, Hred_remove.
    fold unit in Hblue_remove, Hred_remove.
    pose proof (dom_lt_time_identity parents vertex) as Hidentity.
    pose proof (N.T_eqb_le nr 0%N) as Hcompare.
    pose proof (dom_lt_time_key vertex) as Hkey.
    pose proof (dom_order_removal_set_clock width active vertex false Hv) as Hset.
    pose proof (dom_order_removal_unit_width width) as Hunit. fold unit in Hunit, Hset.
    unfold fixed. clearbody unit.
    clear -Hv Hnr Hblue_remove Hred_remove Hidentity Hcompare Hkey Hset Hunit.
    rewrite !Nat2N.inj_add in *. lia. }
  assert (Hscan : forall tree,
    dom_source_numeric_bounded count tree ->
    length (dom_order_row (source_children tree) vertex) <=
      length (dom_order_row (source_children blue) vertex) +
        length (dom_order_row (source_children red) vertex) ->
    (T_dom_order_row (source_children tree) vertex +
      T_dom_source_child (source_parent tree) active vertex
        (dom_order_row (source_children tree) vertex) <= 64 * unit * work)%N).
  { intros tree [[Hparents Hrows] Hcounts] Hlength.
    pose proof (dom_order_row_forall (fun value => (value <= N.of_nat count)%N)
      (source_children tree) vertex Hrows) as Hrow_range.
    pose proof (dom_source_child_clock (N.of_nat count) width (source_parent tree)
      active vertex (dom_order_row (source_children tree) vertex) Hparents
      (dom_order_removal_base_width count width Hwidth) Hrow_range) as Hchild.
    pose proof (dom_order_row_clock (source_children tree) vertex) as Hrow.
    apply dom_order_remove_scan_budget with (width := N.of_nat (width + 1))
      (cells := N.of_nat (length (dom_order_row (source_children tree) vertex))).
    - exact (dom_order_removal_unit_width width).
    - exact Hwork.
    - unfold work. rewrite !Nat2N.inj_add. apply time_of_nat_le in Hlength.
      rewrite Nat2N.inj_add in Hlength. clear -Hlength. lia.
    - eapply N.le_trans; [exact Hrow|]. apply N.mul_le_mono_l.
      apply time_of_nat_le. clear -Hv. lia.
    - rewrite (Nat2N.inj_add (length (dom_order_row (source_children tree) vertex)) 1)
        in Hchild. exact Hchild. }
  set (tree := if N.eqb nr 0%N then blue else red).
  set (scan := (T_dom_order_row (source_children tree) vertex +
    T_dom_source_child (source_parent tree) active vertex
      (dom_order_row (source_children tree) vertex))%N).
  assert (Hscan_bound : (scan <= 64 * unit * work)%N).
  { unfold scan, tree. destruct (N.eqb nr 0%N).
    - apply Hscan; [exact Hblue|apply Nat.le_add_r].
    - apply Hscan; [exact Hred|apply Nat.le_add_l]. }
  set (redirect := match dom_source_child (source_parent tree) active vertex
    (dom_order_row (source_children tree) vertex) with
    | None => 0%N
    | Some child => if N.eqb nr 0%N then
        T_dom_source_redirect (dom_source_remove blue vertex parent) child b parent else
        T_dom_source_redirect (dom_source_remove red vertex parent) child r parent
    end).
  assert (Hredirect : (redirect <= 512 * unit)%N).
  { assert (Hone : forall source_tree anchor child,
      dom_source_numeric_bounded count source_tree -> (anchor <= N.of_nat count)%N ->
      dom_source_child (source_parent source_tree) active vertex
        (dom_order_row (source_children source_tree) vertex) = Some child ->
      (T_dom_source_redirect (dom_source_remove source_tree vertex parent)
        child anchor parent <= 512 * unit)%N).
    { intros source_tree anchor child Htree Hanchor Hchild.
      assert (Hchild_range : (child <= N.of_nat count)%N).
      { pose proof (dom_order_row_forall (fun value => (value <= N.of_nat count)%N)
          (source_children source_tree) vertex (proj2 (proj1 Htree))) as Hrow.
        apply Forall_forall with (x := child) in Hrow; [exact Hrow|].
        now apply dom_source_child_member in Hchild. }
      pose proof (dom_source_redirect_bounded_clock count width
        (dom_source_remove source_tree vertex parent) child anchor parent Hwidth
        (dom_source_remove_numeric_bounded count source_tree vertex parent Htree)
        Hchild_range Hanchor) as Hclock.
      rewrite <- N.mul_assoc in Hclock. exact Hclock. }
    unfold redirect, tree. destruct (N.eqb nr 0%N).
    - destruct (dom_source_child (source_parent blue) active vertex
        (dom_order_row (source_children blue) vertex)) as [child|] eqn:Hchild;
        [exact (Hone blue b child Hblue Hb Hchild)|apply N.le_0_l].
    - destruct (dom_source_child (source_parent red) active vertex
        (dom_order_row (source_children red) vertex)) as [child|] eqn:Hchild;
        [exact (Hone red r child Hred Hr Hchild)|apply N.le_0_l]. }
  pose proof (dom_order_remove_success_overhead parents blue red active vertex queue
    remaining records b r nr) as Htotal.
  cbn zeta in Htotal. fold parent tree in Htotal. fold redirect in Htotal.
  eapply dom_order_remove_success_budget with (fixed := fixed) (scan := scan)
    (redirect := redirect).
  - exact (dom_order_removal_unit_positive width).
  - exact Hwork.
  - exact Hfixed.
  - exact Hscan_bound.
  - exact Hredirect.
  - unfold fixed, scan. clear -Htotal. lia.
Qed.

(** A constant queue guard is covered by every positive row-work allowance. *)
Lemma dom_order_remove_queue_budget (unit work guard success total : N) :
  (1 <= work)%N -> (guard <= 256 * unit)%N ->
  (success <= 2048 * unit * work)%N -> (total <= guard + success)%N ->
  (total <= 4096 * unit * work)%N.
Proof.
  intros Hwork Hguard Hsuccess Htotal.
  assert (Hscale : (unit <= unit * work)%N).
  { rewrite <- (N.mul_1_r unit) at 1. now apply N.mul_le_mono_l. }
  lia.
Qed.

(** Every removal callback is paid by its explicit prefix or two-row work. *)
Lemma dom_order_remove_step_clock count width parents st :
  (forall value, (value <= 8 * (N.of_nat count + 1) * (N.of_nat count + 1))%N ->
    N.size_nat value <= width) ->
  dom_lt_trie_all (fun value => (value <= N.of_nat count)%N) parents ->
  dom_order_removal_invariant count st ->
  (T_dom_order_remove_step parents st <=
    4096 * (PTrieT.c_trie + 1) * N.of_nat (width + 1) *
      N.of_nat (dom_order_removal_work st))%N.
Proof.
  intros Hwidth Hparents Hst.
  pose proof (dom_order_removal_trees_bounded count st Hst) as [Hblue Hred].
  pose proof (dom_order_removal_inv_range count st Hst) as Hrange.
  destruct st as [blue red active queue remaining records].
  cbn [removal_blue removal_red] in Hblue, Hred.
  destruct Hrange as [Hbr [Hrr [Hqueue [Hremaining Hrecords]]]].
  cbn [removal_queue removal_fallback] in Hqueue, Hremaining.
  replace (4096 * (PTrieT.c_trie + 1) * N.of_nat (width + 1))%N with
    (4096 * dom_order_removal_unit width)%N by (unfold dom_order_removal_unit; ring).
  destruct queue as [|vertex queue].
  - assert (Hremaining_width : Forall (fun value => N.size_nat value <= width) remaining).
    { apply Forall_forall. intros value Hin.
      exact (dom_order_removal_base_width count width Hwidth value
        (proj1 (Forall_forall _ _) Hremaining value Hin)). }
    pose proof (dom_order_remove_fallback_clock width parents blue red active remaining
      records Hremaining_width) as Hclock.
    unfold dom_order_removal_work.
    cbn [removal_blue removal_red removal_active removal_queue removal_fallback].
    eapply N.le_trans; [exact Hclock|]. apply N.mul_le_mono_r.
    apply N.mul_le_mono_r. lia.
  - inversion Hqueue as [|head tail Hvertex Htail]; subst head tail.
    pose proof (dom_order_remove_queue_overhead parents blue red active vertex queue
      remaining records) as Htotal.
    pose proof (dom_order_remove_guard_clock count width blue red active vertex Hwidth
      Hblue Hred Hvertex) as Hguard.
    pose proof (dom_order_remove_success_clock count width parents blue red active vertex
      queue remaining records
      (dom_lt_identity (source_parent blue) vertex)
      (dom_lt_identity (source_parent red) vertex)
      (dom_order_number (source_count red) vertex) Hwidth Hblue Hred Hvertex
      (dom_source_numeric_value count blue vertex Hblue Hvertex)
      (dom_source_numeric_value count red vertex Hred Hvertex)
      (dom_source_numeric_count_width count width red vertex Hwidth Hred Hvertex)) as Hsuccess.
    cbn zeta in Htotal. unfold dom_order_removal_work.
    cbn [removal_blue removal_red removal_active removal_queue removal_fallback].
    destruct (dom_order_active active vertex).
    + destruct (N.ltb
        (N.add (dom_order_number (source_count blue) vertex)
          (dom_order_number (source_count red) vertex))
        (if N.eqb (dom_lt_identity (source_parent blue) vertex)
          (dom_lt_identity (source_parent red) vertex) then 1%N else 2%N)).
      * eapply dom_order_remove_queue_budget with
          (guard := (256 * dom_order_removal_unit width)%N).
        -- rewrite !Nat2N.inj_add. lia.
        -- reflexivity.
        -- exact Hsuccess.
        -- clear -Htotal Hguard. lia.
      * change (N.of_nat 1) with 1%N. clear -Htotal Hguard. lia.
    + change (N.of_nat 1) with 1%N. clear -Htotal Hguard. lia.
Qed.
(** The removal work potential pays every callback and every binary-loop visit. *)
Lemma dom_order_removal_loop_clock count width parents fuel initial :
  (forall value, (value <= 8 * (N.of_nat count + 1) * (N.of_nat count + 1))%N ->
    N.size_nat value <= width) ->
  dom_lt_trie_all (fun value => (value <= N.of_nat count)%N) parents ->
  dom_order_removal_invariant count initial ->
  (T_loopN (dom_order_remove_step parents) (T_dom_order_remove_step parents) fuel initial <=
    ((4096 * (PTrieT.c_trie + 1) + c_loopN) * N.of_nat (width + 1)) *
      N.of_nat (dom_order_removal_credit (dom_order_key_universe count) initial) +
    c_loopN * N.of_nat (N.size_nat fuel + 1))%N.
Proof.
  intros Hwidth Hparents Hinitial.
  eapply (dom_order_work_loop (dom_order_remove_step parents)
    (T_dom_order_remove_step parents) (dom_order_removal_invariant count)
    dom_order_removal_work (dom_order_removal_credit (dom_order_key_universe count))).
  - intros st Hst. eapply dom_order_callback_overhead.
    + rewrite Nat2N.inj_add. lia.
    + exact (time_of_nat_le _ _ (dom_order_removal_work_positive st)).
    + exact (dom_order_remove_step_clock count width parents st Hwidth Hparents Hst).
  - intros st next Hst Hstep. split.
    + exact (dom_order_removal_invariant_step count parents st next Hparents Hst Hstep).
    + exact (dom_order_remove_step_credit (dom_order_key_universe count) parents st next
        (dom_order_key_universe_unique count) (dom_order_removal_inv_domain _ _ Hst) Hstep).
  - intros st result Hst Hstep.
    exact (dom_order_remove_stop_credit (dom_order_key_universe count) parents st result Hstep).
  - exact Hinitial.
Qed.
(** Filtering, initialization and all removal callbacks have a common linear budget. *)
Lemma dom_order_removal_time count width limit parents order sources :
  length order <= count ->
  Forall (fun value => (value <= N.of_nat count)%N) order ->
  dom_lt_trie_all (fun value => (value <= N.of_nat count)%N) parents ->
  dom_order_sources_range (N.of_nat count) sources ->
  (limit <= N.of_nat (count + 1))%N ->
  (forall value, (value <= 8 * (N.of_nat count + 1) * (N.of_nat count + 1))%N ->
    N.size_nat value <= width) ->
  (T_dom_order_removal limit parents order sources <=
    dom_order_removal_coefficient * N.of_nat ((count + 1) * (width + 1)))%N.
Proof.
  intros Hlength Horder Hparents Hsources Hlimit Hwidth.
  set (children := filter (dom_order_removal_keep parents) order).
  assert (Hchildren_length : length children <= count).
  { unfold children. eapply Nat.le_trans; [apply filter_length_le|exact Hlength]. }
  assert (Hchildren : Forall (fun value => (value <= N.of_nat count)%N) children).
  { apply Forall_forall. intros value Hin. unfold children in Hin.
    apply filter_In in Hin. exact (proj1 (Forall_forall _ _) Horder value (proj1 Hin)). }
  assert (Horder_width : Forall (fun value => N.size_nat value <= width) order).
  { apply Forall_forall. intros value Hin. apply (dom_order_removal_base_width count width Hwidth).
    exact (proj1 (Forall_forall _ _) Horder value Hin). }
  assert (Hchildren_width : Forall (fun value => N.size_nat value <= width) children).
  { apply Forall_forall. intros value Hin. apply (dom_order_removal_base_width count width Hwidth).
    exact (proj1 (Forall_forall _ _) Hchildren value Hin). }
  assert (Hlimit_width : N.size_nat limit <= width).
  { apply Hwidth. apply dom_order_removal_linear_bound.
    rewrite Nat2N.inj_add in Hlimit. change (N.of_nat 1) with 1%N in Hlimit.
    clear -Hlimit. lia. }
  set (initial := DomOrderRemovalState
    (dom_source_initial parents (source_blue sources) children)
    (dom_source_initial parents (source_red sources) children)
    (fold_left dom_order_removal_activate children Empty) children children []).
  pose proof (dom_order_removal_initial_invariant count parents sources children
    Hchildren_length Hchildren Hsources) as Hinitial.
  change (dom_order_removal_invariant count initial /\
    dom_order_removal_credit (dom_order_key_universe count) initial <= 12 * (count + 1)) in Hinitial.
  destruct Hinitial as [Hinv Hcredit].
  pose proof (dom_order_removal_loop_clock count width parents
    (N.double (N.double (N.double (N.double limit))) + 3)%N initial Hwidth Hparents Hinv) as Hloop.
  pose proof (dom_order_removal_filter_clock width parents order Horder_width) as Hfilter.
  pose proof (dom_order_removal_activation_clock width children Empty Hchildren_width) as Hactive.
  destruct Hsources as [Hblue_source Hred_source].
  pose proof (dom_source_initial_time count width parents (source_blue sources) children
    Hwidth Hblue_source Hchildren Hchildren_length) as Hblue.
  pose proof (dom_source_initial_time count width parents (source_red sources) children
    Hwidth Hred_source Hchildren Hchildren_length) as Hred.
  pose proof (dom_order_removal_overhead limit parents order sources) as Hsetup.
  fold children initial in Hsetup.
  set (budget := N.of_nat ((count + 1) * (width + 1))).
  assert (Horder_budget : (N.of_nat ((length order + 1) * (width + 1)) <= budget)%N).
  { unfold budget. apply time_of_nat_le. apply Nat.mul_le_mono_r. clear -Hlength. lia. }
  assert (Hchildren_budget : (N.of_nat ((length children + 1) * (width + 1)) <= budget)%N).
  { unfold budget. apply time_of_nat_le. apply Nat.mul_le_mono_r.
    clear -Hchildren_length. lia. }
  assert (Hwidth_budget : (N.of_nat (width + 1) <= budget)%N).
  { unfold budget. apply time_of_nat_le. clear -count width. nia. }
  assert (Hlimit_budget : (N.of_nat (N.size_nat limit + 1) <= budget)%N).
  { eapply N.le_trans with (N.of_nat (width + 1)).
    - apply time_of_nat_le. clear -Hlimit_width. lia.
    - exact Hwidth_budget. }
  assert (Hfilter_paid : (List.T_filter (dom_order_removal_keep parents)
    (T_dom_order_removal_keep parents) order <= 32 * budget)%N).
  { eapply N.le_trans; [exact Hfilter|]. now apply N.mul_le_mono_l. }
  assert (Hactive_paid : (List.T_fold_left dom_order_removal_activate T_dom_order_removal_activate
    children Empty <= 128 * (PTrieT.c_trie + 1) * budget)%N).
  { eapply N.le_trans; [exact Hactive|]. now apply N.mul_le_mono_l. }
  assert (Hblue_paid : (T_dom_source_initial parents (source_blue sources) children <=
    512 * (PTrieT.c_trie + 1) * budget)%N).
  { eapply N.le_trans; [exact Hblue|]. now apply N.mul_le_mono_l. }
  assert (Hred_paid : (T_dom_source_initial parents (source_red sources) children <=
    512 * (PTrieT.c_trie + 1) * budget)%N).
  { eapply N.le_trans; [exact Hred|]. now apply N.mul_le_mono_l. }
  assert (Hfuel_paid : (c_loopN * N.of_nat
    (N.size_nat (N.double (N.double (N.double (N.double limit))) + 3)%N + 1) <=
      7 * c_loopN * budget)%N).
  { pose proof (dom_order_removal_fuel_bits limit) as Hfuel.
    assert (Hbits : N.size_nat (N.double (N.double (N.double (N.double limit))) + 3)%N + 1 <=
      7 * (width + 1)) by (clear -Hfuel Hlimit_width; lia).
    apply time_of_nat_le in Hbits. rewrite Nat2N.inj_mul in Hbits.
    change (N.of_nat 7) with 7%N in Hbits.
    apply N.mul_le_mono_l with (p := c_loopN) in Hbits.
    eapply N.le_trans; [exact Hbits|].
    replace (c_loopN * (7 * N.of_nat (width + 1)))%N with
      (7 * c_loopN * N.of_nat (width + 1))%N by ring.
    apply N.mul_le_mono_l. exact Hwidth_budget. }
  assert (Hcredit_paid : (((4096 * (PTrieT.c_trie + 1) + c_loopN) * N.of_nat (width + 1)) *
    N.of_nat (dom_order_removal_credit (dom_order_key_universe count) initial) <=
      (49152 * (PTrieT.c_trie + 1) + 12 * c_loopN) * budget)%N).
  { apply time_of_nat_le in Hcredit. rewrite Nat2N.inj_mul in Hcredit.
    change (N.of_nat 12) with 12%N in Hcredit.
    eapply N.le_trans.
    - apply N.mul_le_mono_l. exact Hcredit.
    - unfold budget. rewrite Nat2N.inj_mul. ring_simplify. reflexivity. }
  assert (Hloop_paid : (T_loopN (dom_order_remove_step parents) (T_dom_order_remove_step parents)
    (N.double (N.double (N.double (N.double limit))) + 3)%N initial <=
      (49152 * (PTrieT.c_trie + 1) + 19 * c_loopN) * budget)%N).
  { replace ((49152 * (PTrieT.c_trie + 1) + 19 * c_loopN) * budget)%N with
      ((49152 * (PTrieT.c_trie + 1) + 12 * c_loopN) * budget +
        7 * c_loopN * budget)%N by ring.
    clear -Hloop Hcredit_paid Hfuel_paid. lia. }
  assert (Hsetup_paid : (T_dom_order_removal limit parents order sources <=
    List.T_filter (dom_order_removal_keep parents) (T_dom_order_removal_keep parents) order +
    List.T_fold_left dom_order_removal_activate T_dom_order_removal_activate children Empty +
    T_dom_source_initial parents (source_blue sources) children +
    T_dom_source_initial parents (source_red sources) children +
    T_loopN (dom_order_remove_step parents) (T_dom_order_remove_step parents)
      (N.double (N.double (N.double (N.double limit))) + 3)%N initial + 64 * budget)%N).
  { eapply N.le_trans; [exact Hsetup|]. apply N.add_le_mono_l. now apply N.mul_le_mono_l. }
  unfold dom_order_removal_coefficient. fold budget.
  exact (dom_order_removal_final_budget PTrieT.c_trie c_loopN budget _ _ _ _ _ _
    Hfilter_paid Hactive_paid Hblue_paid Hred_paid Hloop_paid Hsetup_paid).
Qed.
