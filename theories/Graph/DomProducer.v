(** * Dominator producer traversal

    The producer records a binary DFS layout before semidominator settlement.
    For example, a discovered child records its active DFS parent.
    Builds on: filtered graph search and dominator operation data. *)

From Stdlib Require Import List Bool PArith NArith.
From Argent Require Import Time Tactics Std.
From Galois.Base Require Import Trie Loop.
From Galois.Graph Require Import Data DigraphSig SearchSig Search Scc DomSig.
Import List.ListNotations.

Record dom_lt_layout := DomLtLayout {
  lt_reverse_order : list positive;
  lt_rank : ptrie N;
  lt_dfs_parent : ptrie positive;
  lt_stack : list positive;
  lt_next : N
}.
TimeFun lt_reverse_order.
TimeFun lt_rank.
TimeFun lt_dfs_parent.
TimeFun lt_stack.
TimeFun lt_next.

Definition dom_lt_event (st : dom_lt_layout) (e : event) : dom_lt_layout :=
  match e with
  | Enter v =>
    let parents := match lt_stack st with
      | [] => lt_dfs_parent st
      | p :: _ => PTrieCode.set v p (lt_dfs_parent st)
      end in
    DomLtLayout (v :: lt_reverse_order st) (PTrieCode.set v (lt_next st) (lt_rank st))
      parents (v :: lt_stack st) (N.succ (lt_next st))
  | Leave _ => DomLtLayout (lt_reverse_order st) (lt_rank st) (lt_dfs_parent st)
      (match lt_stack st with [] => [] | _ :: rest => rest end) (lt_next st)
  | Edge _ _ _ => st
  end.
TimeFun dom_lt_event.

Fixpoint dom_lt_key_fits (width : nat) (v : positive) : bool :=
  match width, v with
  | O, _ => false
  | S _, xH => true
  | S rest, xO tail | S rest, xI tail => dom_lt_key_fits rest tail
  end.
TimeFun dom_lt_key_fits.

(** Unlisted roots are rejected before the filtered traversal can read their rows. *)
Definition dom_lt_trace (g : prepared) (r : positive) : list event :=
  let listed := fold_left (fun acc v => PTrieCode.set v true acc) (nodes g) Empty in
  if dom_lt_key_fits (graph_width (base g)) r then
    match trie_get r listed with
    | None => []
    | Some _ => prepared_search_trace (scc_graph g) [r]
    end
  else [].
TimeFun dom_lt_trace.

Definition dom_lt_layout_of (g : prepared) (r : positive) : dom_lt_layout :=
  fold_left dom_lt_event (dom_lt_trace g r) (DomLtLayout [] Empty Empty [] 1%N).
TimeFun dom_lt_layout_of.

Definition dom_lt_dfs (g : prepared) (r : positive) : list positive :=
  rev_append (lt_reverse_order (dom_lt_layout_of g r)) [].
TimeFun dom_lt_dfs.

Record dom_lt_links := DomLtLinks {
  lt_shortcut : ptrie N;
  lt_label : ptrie N;
  lt_operations : list lt_op
}.
TimeFun lt_shortcut.
TimeFun lt_label.
TimeFun lt_operations.

Definition dom_lt_key (rank : N) : positive := N.succ_pos rank.
TimeFun dom_lt_key.

Definition dom_lt_identity (m : ptrie N) (v : N) : N :=
  match trie_get (dom_lt_key v) m with Some stored => stored | None => v end.
TimeFun dom_lt_identity.

Definition dom_lt_rank_get (ranks : ptrie N) (v : positive) : N :=
  match trie_get v ranks with Some n => n | None => 0%N end.
TimeFun dom_lt_rank_get.

Definition dom_lt_minimum (semis : ptrie N) (u v : N) : N :=
  if N.ltb (dom_lt_identity semis v) (dom_lt_identity semis u) then v else u.
TimeFun dom_lt_minimum.

Inductive dom_lt_walk_phase :=
  | DomLtDescend (current : N) (stack : list N)
  | DomLtUnwind (root : N) (part : option N) (stack : list N).

Record dom_lt_walk := DomLtWalk {
  lt_walk_links : dom_lt_links;
  lt_walk_phase : dom_lt_walk_phase
}.
TimeFun lt_walk_links.
TimeFun lt_walk_phase.

(** Descending saves compression frames and unwinding installs their selected numeric labels. *)
Definition dom_lt_compress_step (semis : ptrie N) (st : dom_lt_walk)
    : dom_lt_walk + (dom_lt_links * N) :=
  let links := lt_walk_links st in
  match lt_walk_phase st with
  | DomLtDescend v stack =>
    match trie_get (dom_lt_key v) (lt_shortcut links) with
    | Some p =>
      if N.ltb p v then inl (DomLtWalk links (DomLtDescend p (v :: stack)))
      else inl (DomLtWalk links (DomLtUnwind v None stack))
    | None => inl (DomLtWalk links (DomLtUnwind v None stack))
    end
  | DomLtUnwind root part [] =>
    inr (links, match part with None => root | Some best => best end)
  | DomLtUnwind root part (v :: stack) =>
    let label := dom_lt_identity (lt_label links) v in
    let best := match part with
      | None => label
      | Some previous => dom_lt_minimum semis label previous
      end in
    let links := DomLtLinks (PTrieCode.set (dom_lt_key v) root (lt_shortcut links))
      (PTrieCode.set (dom_lt_key v) best (lt_label links)) (lt_operations links) in
    inl (DomLtWalk links (DomLtUnwind root (Some best) stack))
  end.
TimeFun dom_lt_compress_step.

Definition dom_lt_eval (fuel : N) (semis : ptrie N) (links : dom_lt_links) (v : N)
    : dom_lt_links * N :=
  let links := DomLtLinks (lt_shortcut links) (lt_label links)
    (LtEval v :: lt_operations links) in
  match loopN (dom_lt_compress_step semis) (N.double fuel + 3)%N
      (DomLtWalk links (DomLtDescend v [])) with
  | inr result => result
  | inl st => (lt_walk_links st, v)
  end.
TimeFun dom_lt_eval.

Definition dom_lt_link (links : dom_lt_links) (v p : N) : dom_lt_links :=
  DomLtLinks (PTrieCode.set (dom_lt_key v) p (lt_shortcut links))
    (PTrieCode.set (dom_lt_key v) v (lt_label links))
    (LtLink v p :: lt_operations links).
TimeFun dom_lt_link.

Record dom_lt_numeric := DomLtNumeric {
  lt_numeric_order : list N;
  lt_numeric_parent : ptrie N;
  lt_numeric_pred : ptrie (list N);
  lt_numeric_vertex : ptrie positive;
  lt_numeric_limit : N
}.
TimeFun lt_numeric_order.
TimeFun lt_numeric_parent.
TimeFun lt_numeric_pred.
TimeFun lt_numeric_vertex.
TimeFun lt_numeric_limit.

Definition dom_lt_ranked_row (ranks : ptrie N) (vs : list positive) : list N :=
  fold_right (fun v rest => match trie_get v ranks with
    | None => rest
    | Some n => n :: rest
    end) [] vs.
TimeFun dom_lt_ranked_row.

Definition dom_lt_numeric_add (g : prepared) (layout : dom_lt_layout)
    (st : dom_lt_numeric) (v : positive) : dom_lt_numeric :=
  let rank := dom_lt_rank_get (lt_rank layout) v in
  let key := dom_lt_key rank in
  let parents := match trie_get v (lt_dfs_parent layout) with
    | None => lt_numeric_parent st
    | Some p => PTrieCode.set key (dom_lt_rank_get (lt_rank layout) p) (lt_numeric_parent st)
    end in
  DomLtNumeric (rank :: lt_numeric_order st) parents
    (PTrieCode.set key (dom_lt_ranked_row (lt_rank layout) (preds g v)) (lt_numeric_pred st))
    (PTrieCode.set key v (lt_numeric_vertex st)) (lt_numeric_limit st).
TimeFun dom_lt_numeric_add.

Definition dom_lt_numeric_of (g : prepared) (r : positive) : dom_lt_numeric :=
  let layout := dom_lt_layout_of g r in
  fold_left (dom_lt_numeric_add g layout) (rev_append (lt_reverse_order layout) [])
    (DomLtNumeric [] Empty Empty Empty (lt_next layout)).
TimeFun dom_lt_numeric_of.

Record dom_lt_semi_state := DomLtSemiState {
  lt_semis : ptrie N;
  lt_minimizer : ptrie N;
  lt_semi_links : dom_lt_links
}.
TimeFun lt_semis.
TimeFun lt_minimizer.
TimeFun lt_semi_links.

Definition dom_lt_predecessor (limit : N) (semis : ptrie N)
    (acc : dom_lt_links * N * N) (source : N) : dom_lt_links * N * N :=
  let '(links, best, witness) := acc in
  let '(links, chosen) := dom_lt_eval limit semis links source in
  let candidate := dom_lt_identity semis chosen in
  if N.ltb candidate best then (links, candidate, source) else (links, best, witness).
TimeFun dom_lt_predecessor.

Definition dom_lt_settle (numeric : dom_lt_numeric) (st : dom_lt_semi_state) (v : N)
    : dom_lt_semi_state :=
  let key := dom_lt_key v in
  match trie_get key (lt_numeric_parent numeric) with
  | None => st
  | Some p =>
    let incoming := match trie_get key (lt_numeric_pred numeric) with
      | None => []
      | Some row => row
      end in
    let '(links, best, witness) := fold_left
      (dom_lt_predecessor (lt_numeric_limit numeric) (lt_semis st)) incoming
      (lt_semi_links st, p, p) in
    DomLtSemiState (PTrieCode.set key best (lt_semis st))
      (PTrieCode.set key witness (lt_minimizer st)) (dom_lt_link links v p)
  end.
TimeFun dom_lt_settle.

Definition dom_lt_semidominators (numeric : dom_lt_numeric) : dom_lt_semi_state :=
  fold_left (dom_lt_settle numeric) (lt_numeric_order numeric)
    (DomLtSemiState Empty Empty (DomLtLinks Empty Empty [])).
TimeFun dom_lt_semidominators.

Definition dom_lt_bucket_add (semis : ptrie N) (buckets : ptrie (list N)) (v : N)
    : ptrie (list N) :=
  match trie_get (dom_lt_key v) semis with
  | None => buckets
  | Some s => let key := dom_lt_key s in
    let row := match trie_get key buckets with None => [] | Some row => row end in
    PTrieCode.set key (v :: row) buckets
  end.
TimeFun dom_lt_bucket_add.

Record dom_lt_bucket_state := DomLtBucketState {
  lt_bucket_links : dom_lt_links;
  lt_relative : ptrie N
}.
TimeFun lt_bucket_links.
TimeFun lt_relative.

Definition dom_lt_bucket_member (limit : N) (semis : ptrie N) (s : N)
    (st : dom_lt_bucket_state) (v : N) : dom_lt_bucket_state :=
  let '(links, u) := dom_lt_eval limit semis (lt_bucket_links st) v in
  let parent := if N.ltb (dom_lt_identity semis u) s then u else s in
  DomLtBucketState links (PTrieCode.set (dom_lt_key v) parent (lt_relative st)).
TimeFun dom_lt_bucket_member.

Definition dom_lt_bucket_step (numeric : dom_lt_numeric) (semis : ptrie N)
    (buckets : ptrie (list N)) (st : dom_lt_bucket_state) (s : N) : dom_lt_bucket_state :=
  let row := match trie_get (dom_lt_key s) buckets with None => [] | Some row => row end in
  let st := fold_left (dom_lt_bucket_member (lt_numeric_limit numeric) semis s) row st in
  match trie_get (dom_lt_key s) (lt_numeric_parent numeric) with
  | None => st
  | Some p => DomLtBucketState (dom_lt_link (lt_bucket_links st) s p) (lt_relative st)
  end.
TimeFun dom_lt_bucket_step.

Definition dom_lt_correct_step (semis relative : ptrie N) (corrected : ptrie N) (v : N)
    : ptrie N :=
  match trie_get (dom_lt_key v) relative with
  | None => corrected
  | Some p =>
    let parent := if N.eqb p (dom_lt_identity semis v) then p
      else dom_lt_identity corrected p in
    PTrieCode.set (dom_lt_key v) parent corrected
  end.
TimeFun dom_lt_correct_step.

Definition dom_lt_buckets (numeric : dom_lt_numeric) (semis : ptrie N)
    : dom_lt_bucket_state :=
  let buckets := fold_left (dom_lt_bucket_add semis)
    (rev_append (lt_numeric_order numeric) []) Empty in
  fold_left (dom_lt_bucket_step numeric semis buckets) (lt_numeric_order numeric)
    (DomLtBucketState (DomLtLinks Empty Empty []) Empty).
TimeFun dom_lt_buckets.

Definition dom_lt_correct (numeric : dom_lt_numeric) (semis relative : ptrie N) : ptrie N :=
  fold_left (dom_lt_correct_step semis relative) (rev_append (lt_numeric_order numeric) []) Empty.
TimeFun dom_lt_correct.

Definition dom_lt_erase (numeric : dom_lt_numeric) (parents : ptrie N) : ptrie positive :=
  fold_left (fun result v =>
    match trie_get (dom_lt_key v) parents, trie_get (dom_lt_key v) (lt_numeric_vertex numeric) with
    | Some p, Some child =>
      match trie_get (dom_lt_key p) (lt_numeric_vertex numeric) with
      | None => result
      | Some parent => PTrieCode.set child parent result
      end
    | _, _ => result
    end) (lt_numeric_order numeric) Empty.
TimeFun dom_lt_erase.

Definition dom_lt_parents (g : prepared) (r : positive) : ptrie positive :=
  let numeric := dom_lt_numeric_of g r in
  let semis := dom_lt_semidominators numeric in
  let buckets := dom_lt_buckets numeric (lt_semis semis) in
  dom_lt_erase numeric (dom_lt_correct numeric (lt_semis semis) (lt_relative buckets)).
TimeFun dom_lt_parents.
