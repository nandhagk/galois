(** * Dominator producer traversal

    The producer records a binary DFS layout before semidominator settlement.
    For example, a discovered child records its active DFS parent.
    Builds on: filtered graph search and dominator operation data. *)

From Stdlib Require Import List Bool PArith NArith Arith Lia.
From Argent Require Import Time Tactics Std Loop.
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

(** The reference traversal builds a separate table for its root membership test. *)
Local Definition dom_lt_trace_spec (g : prepared) (r : positive) : list event :=
  let listed := fold_left (fun acc v => PTrieCode.set v true acc) (nodes g) Empty in
  if dom_lt_key_fits (graph_width (base g)) r then
    match trie_get r listed with
    | None => []
    | Some _ => prepared_search_trace (scc_graph g) [r]
    end
  else [].

(** The filtered graph's rows also supply the root membership test. *)
Definition dom_lt_trace (g : prepared) (r : positive) : list event :=
  if dom_lt_key_fits (vertex_width (nodes g)) r then
    let ready := scc_graph g in
    match trie_get r (succ (base ready)) with
    | None => []
    | Some _ => prepared_search_trace ready [r]
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

(** The reference evaluator retains the original uncached compression loop. *)
Definition dom_lt_eval_spec (fuel : N) (semis : ptrie N) (links : dom_lt_links) (v : N)
    : dom_lt_links * N :=
  let links := DomLtLinks (lt_shortcut links) (lt_label links)
    (LtEval v :: lt_operations links) in
  match loopN (dom_lt_compress_step semis) (N.double fuel + 3)%N
      (DomLtWalk links (DomLtDescend v [])) with
  | inr result => result
  | inl st => (lt_walk_links st, v)
  end.

(** Compression carries the selected label's score through its pending unwind frames. *)
Record dom_cached_walk := DomCachedWalk {
  cached_links : dom_lt_links;
  cached_phase : dom_lt_walk_phase;
  cached_score : N
}.
TimeFun cached_links.
TimeFun cached_phase.
TimeFun cached_score.

(** The cached callback keeps the original frames and avoids repeated score lookups. *)
Definition dom_cached_compress_step (semis : ptrie N) (st : dom_cached_walk)
    : dom_cached_walk + (dom_lt_links * N) :=
  let '(DomCachedWalk links phase previous_score) := st in
  match phase with
  | DomLtDescend v stack =>
    match trie_get (dom_lt_key v) (lt_shortcut links) with
    | Some p =>
      if N.ltb p v then inl (DomCachedWalk links (DomLtDescend p (v :: stack)) 0%N)
      else inl (DomCachedWalk links (DomLtUnwind v None stack) 0%N)
    | None => inl (DomCachedWalk links (DomLtUnwind v None stack) 0%N)
    end
  | DomLtUnwind root part [] =>
    inr (links, match part with None => root | Some best => best end)
  | DomLtUnwind root part (v :: stack) =>
    let label := dom_lt_identity (lt_label links) v in
    let '(best, score) := match part with
      | None =>
        (* No score is needed when this is the last unwind frame. *)
        (label, match stack with [] => 0%N | _ => dom_lt_identity semis label end)
      | Some previous =>
        let fresh := dom_lt_identity semis label in
        let old := previous_score in
        if N.leb fresh old then (label, fresh) else (previous, old)
      end in
    let links := DomLtLinks (PTrieCode.set (dom_lt_key v) root (lt_shortcut links))
      (PTrieCode.set (dom_lt_key v) best (lt_label links)) (lt_operations links) in
    inl (DomCachedWalk links (DomLtUnwind root (Some best) stack) score)
  end.
TimeFun dom_cached_compress_step.

(** Evaluation carries scores while preserving the original binary-fuel budget. *)
Definition dom_lt_eval (fuel : N) (semis : ptrie N) (links : dom_lt_links) (v : N)
    : dom_lt_links * N :=
  let links := DomLtLinks (lt_shortcut links) (lt_label links)
    (LtEval v :: lt_operations links) in
  match loopN (dom_cached_compress_step semis) (N.double fuel + 3)%N
      (DomCachedWalk links (DomLtDescend v []) 0%N) with
  | inr result => result
  | inl st => (cached_links st, v)
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

(** * Producer operation inventories *)

(** The invariant argument is independent of the driver's accessibility proof. *)
Local Lemma dom_lt_loop_acc {S R : Type} (step : S -> S + R)
    (Inv : S -> Prop) (Result : R -> Prop) :
  (forall st next, Inv st -> step st = inl next -> Inv next) ->
  (forall st result, Inv st -> step st = inr result -> Result result) ->
  forall fs (Hacc : Acc loopN_lt fs), Inv (snd fs) ->
  match Argent.Loop.loop loopN_lt (loopN_step step) fs Hacc with
  | inl st => Inv st | inr result => Result result
  end.
Proof.
  intros Hcontinue Hstop fs Hacc.
  induction Hacc as [[remaining st] Hnext IH] using Acc_ind_dep.
  cbn [snd]. intro Hinv. destruct remaining as [|p].
  - cbn [Argent.Loop.loop loopN_step]. exact Hinv.
  - cbn [Argent.Loop.loop loopN_step]. destruct (step st) as [next|result] eqn:Hstep.
    + apply IH. eapply Hcontinue; eassumption.
    + eapply Hstop; eassumption.
Qed.

(** Forgetting the score retains the original compression state. *)
Definition dom_cached_forget (st : dom_cached_walk) : dom_lt_walk :=
  match st with DomCachedWalk links phase _ => DomLtWalk links phase end.

(** Projection retains both partial exhausted states and completed results. *)
Definition dom_cached_result (result : dom_cached_walk + (dom_lt_links * N))
    : dom_lt_walk + (dom_lt_links * N) :=
  match result with
  | inl next => inl (dom_cached_forget next)
  | inr done => inr done
  end.

(** A cached score is required only while another pending frame can read it. *)
Definition dom_cached_valid (semis : ptrie N) (st : dom_cached_walk) : Prop :=
  match st with
  | DomCachedWalk _ (DomLtUnwind _ (Some previous) (_ :: _)) score =>
    score = dom_lt_identity semis previous
  | _ => True
  end.

(** Choosing the fresh label on equal scores preserves the original minimum's tie rule. *)
Local Lemma dom_cached_choice {A : Type} (left right : N) (first second : A) :
  (if N.leb left right then first else second) =
    (if N.ltb right left then second else first).
Proof.
  destruct (N.leb left right) eqn:Hle.
  - apply N.leb_le in Hle.
    assert (Hlt : N.ltb right left = false) by (apply N.ltb_ge; lia).
    now rewrite Hlt.
  - apply N.leb_gt in Hle.
    assert (Hlt : N.ltb right left = true) by (apply N.ltb_lt; lia).
    now rewrite Hlt.
Qed.

(** Every cached transition projects to the original transition and preserves its score. *)
Lemma dom_cached_step_simulates semis st : dom_cached_valid semis st ->
  dom_cached_result (dom_cached_compress_step semis st) =
    dom_lt_compress_step semis (dom_cached_forget st) /\
  match dom_cached_compress_step semis st with
  | inl next => dom_cached_valid semis next
  | inr _ => True
  end.
Proof.
  destruct st as [links [vertex stack|root part stack] score].
  - intros _. cbn [dom_cached_compress_step dom_cached_forget dom_lt_compress_step
      lt_walk_phase lt_walk_links].
    destruct (trie_get (dom_lt_key vertex) (lt_shortcut links)) as [parent|];
      [destruct (N.ltb parent vertex)|]; split; (reflexivity || exact I).
  - destruct stack as [|vertex stack].
    + intros _. cbn [dom_cached_compress_step dom_cached_forget dom_lt_compress_step
        dom_cached_result lt_walk_phase lt_walk_links]. split; [reflexivity|exact I].
    + destruct part as [previous|].
      * cbn [dom_cached_valid]. intro Hscore. subst score.
        cbn [dom_cached_compress_step dom_cached_forget dom_lt_compress_step
          lt_walk_phase lt_walk_links].
        rewrite dom_cached_choice.
        unfold dom_lt_minimum.
        destruct (N.ltb (dom_lt_identity semis previous)
          (dom_lt_identity semis (dom_lt_identity (lt_label links) vertex)));
          cbn [dom_cached_result dom_cached_forget]; split; [reflexivity| |reflexivity|];
          destruct stack; (exact I || reflexivity).
      * intros _. cbn [dom_cached_compress_step dom_cached_forget dom_lt_compress_step
          dom_cached_result lt_walk_phase lt_walk_links].
        destruct stack; split; (reflexivity || exact I).
Qed.

Local Opaque dom_cached_compress_step dom_lt_compress_step.

(** Projection commutes with both loops for arbitrary accessibility proofs. *)
Local Lemma dom_cached_loop_acc semis fs (access : Acc loopN_lt fs) :
  forall old_access : Acc loopN_lt (fst fs, dom_cached_forget (snd fs)),
  dom_cached_valid semis (snd fs) ->
  dom_cached_result
    (Argent.Loop.loop loopN_lt (loopN_step (dom_cached_compress_step semis)) fs access) =
  Argent.Loop.loop loopN_lt (loopN_step (dom_lt_compress_step semis))
    (fst fs, dom_cached_forget (snd fs)) old_access.
Proof.
  induction access as [[fuel st] Hnext IH] using Acc_ind_dep.
  intros [Hspec] Hvalid. cbn [fst snd] in *.
  destruct fuel as [|fuel]; [reflexivity|].
  pose proof (dom_cached_step_simulates semis st Hvalid) as [Hstep Hpreserve].
  cbn [Argent.Loop.loop loopN_step].
  destruct (dom_cached_compress_step semis st) as [next|result] eqn:Hcached.
  - cbn [dom_cached_result] in Hstep. rewrite <- Hstep.
    cbn [Acc_inv]. apply IH. exact Hpreserve.
  - cbn [dom_cached_result] in Hstep. rewrite <- Hstep. reflexivity.
Qed.

(** Projection preserves every binary-fuel prefix, including exhaustion. *)
Local Lemma dom_cached_loop_agrees semis fuel st : dom_cached_valid semis st ->
  dom_cached_result (loopN (dom_cached_compress_step semis) fuel st) =
    loopN (dom_lt_compress_step semis) fuel (dom_cached_forget st).
Proof.
  intro Hvalid. unfold loopN. apply dom_cached_loop_acc. exact Hvalid.
Qed.

(** Cached evaluation preserves the exact links, operation log and selected label for every fuel. *)
Lemma dom_cached_eval_agrees fuel semis links vertex :
  dom_lt_eval fuel semis links vertex = dom_lt_eval_spec fuel semis links vertex.
Proof.
  unfold dom_lt_eval, dom_lt_eval_spec.
  set (recorded := DomLtLinks (lt_shortcut links) (lt_label links)
    (LtEval vertex :: lt_operations links)).
  pose proof (dom_cached_loop_agrees semis (N.double fuel + 3)%N
    (DomCachedWalk recorded (DomLtDescend vertex []) 0%N) I) as Hagree.
  cbn [dom_cached_forget] in Hagree. rewrite <- Hagree.
  destruct (loopN (dom_cached_compress_step semis) (N.double fuel + 3)%N
    (DomCachedWalk recorded (DomLtDescend vertex []) 0%N)) as [st|result]; [|reflexivity].
  destruct st. reflexivity.
Qed.

Local Transparent dom_cached_compress_step dom_lt_compress_step.

Local Opaque Argent.Loop.loop Acc_intro_generator.

(** A binary-fuel loop preserves state invariants even when its fuel is exhausted. *)
Lemma dom_lt_loop_invariant {S R : Type} (step : S -> S + R)
    (Inv : S -> Prop) (Result : R -> Prop) fuel s :
  (forall st next, Inv st -> step st = inl next -> Inv next) ->
  (forall st result, Inv st -> step st = inr result -> Result result) ->
  Inv s ->
  match loopN step fuel s with inl st => Inv st | inr result => Result result end.
Proof.
  intros Hcontinue Hstop Hinitial. unfold loopN.
  match goal with
  | |- context [Argent.Loop.loop _ _ _ ?Hacc] =>
    exact (dom_lt_loop_acc step Inv Result Hcontinue Hstop (fuel, s) Hacc Hinitial)
  end.
Qed.

(** Compression updates shortcuts and labels without changing its operation log. *)
Lemma dom_lt_compress_operations semis st :
  match dom_lt_compress_step semis st with
  | inl next => lt_operations (lt_walk_links next)
  | inr result => lt_operations (fst result)
  end = lt_operations (lt_walk_links st).
Proof.
  destruct st as [links [v stack|root part stack]].
  - cbn [dom_lt_compress_step lt_walk_links lt_walk_phase].
    destruct (trie_get (dom_lt_key v) (lt_shortcut links)) as [p|]; [destruct (N.ltb p v)|];
      reflexivity.
  - destruct stack as [|v stack]; [destruct part; reflexivity|].
    destruct part; reflexivity.
Qed.

(** Every evaluator call records exactly its own query, including fuel exhaustion. *)
Lemma dom_lt_eval_operations fuel semis links v :
  lt_operations (fst (dom_lt_eval fuel semis links v)) = LtEval v :: lt_operations links.
Proof.
  set (recorded := LtEval v :: lt_operations links).
  pose proof (dom_lt_loop_invariant (dom_lt_compress_step semis)
    (fun st => lt_operations (lt_walk_links st) = recorded)
    (fun result => lt_operations (fst result) = recorded)
    (N.double fuel + 3)%N
    (DomLtWalk (DomLtLinks (lt_shortcut links) (lt_label links) recorded)
      (DomLtDescend v []))) as Hrun.
  assert (Hgo : forall st next,
    lt_operations (lt_walk_links st) = recorded ->
    dom_lt_compress_step semis st = inl next ->
    lt_operations (lt_walk_links next) = recorded).
  { intros st next Hinv Hstep. pose proof (dom_lt_compress_operations semis st) as Hlog.
    rewrite Hstep in Hlog. now rewrite Hlog. }
  assert (Hstop : forall st result,
    lt_operations (lt_walk_links st) = recorded ->
    dom_lt_compress_step semis st = inr result ->
    lt_operations (fst result) = recorded).
  { intros st result Hinv Hstep. pose proof (dom_lt_compress_operations semis st) as Hlog.
    rewrite Hstep in Hlog. now rewrite Hlog. }
  specialize (Hrun Hgo Hstop eq_refl).
  rewrite dom_cached_eval_agrees. unfold dom_lt_eval_spec. fold recorded.
  destruct (loopN (dom_lt_compress_step semis) (N.double fuel + 3)
    (DomLtWalk (DomLtLinks (lt_shortcut links) (lt_label links) recorded)
      (DomLtDescend v []))) as [st|[result chosen]]; exact Hrun.
Qed.

Local Opaque dom_lt_eval.

(** A predecessor visit appends one query to the accumulated operation count. *)
Lemma dom_lt_predecessor_operations limit semis links best witness source :
  length (lt_operations (fst (fst
    (dom_lt_predecessor limit semis (links, best, witness) source)))) =
    S (length (lt_operations links)).
Proof.
  pose proof (dom_lt_eval_operations limit semis links source) as Hlog.
  unfold dom_lt_predecessor.
  destruct (dom_lt_eval limit semis links source) as [result chosen].
  cbn [fst] in Hlog. destruct (N.ltb (dom_lt_identity semis chosen) best);
    cbn [fst]; now rewrite Hlog.
Qed.

Local Opaque dom_lt_predecessor.

(** A fold whose callback adds one unit has exactly one unit per list entry. *)
Lemma dom_lt_fold_count {A B : Type} (step : A -> B -> A) (count : A -> nat) :
  (forall st x, count (step st x) = S (count st)) ->
  forall xs st, count (fold_left step xs st) = length xs + count st.
Proof.
  intros Hstep xs. induction xs as [|x rest IH]; intro st; [reflexivity|].
  cbn [fold_left length]. rewrite IH, Hstep, Nat.add_succ_r. reflexivity.
Qed.

(** A fold's accumulated count is bounded by the sum of its callback increments. *)
Lemma dom_lt_fold_count_le {A B : Type} (step : A -> B -> A)
    (count : A -> nat) (weight : B -> nat) :
  (forall st x, count (step st x) <= count st + 1 + weight x) ->
  forall xs st, count (fold_left step xs st) <= count st + length xs +
    fold_right (fun x total => weight x + total) 0 xs.
Proof.
  intros Hstep xs. induction xs as [|x rest IH]; intro st.
  - cbn [fold_left length fold_right]. lia.
  - specialize (IH (step st x)). specialize (Hstep st x).
    cbn [fold_left length fold_right]. lia.
Qed.

(** One optional link fits above the already counted row queries. *)
Lemma dom_lt_count_link recorded row before :
  recorded = row + before -> S recorded <= before + 1 + row.
Proof.
  lia.
Qed.

(** Folding a predecessor row records one query for each occurrence in that row. *)
Lemma dom_lt_predecessors_operations limit semis incoming links best witness :
  length (lt_operations (fst (fst
    (fold_left (dom_lt_predecessor limit semis) incoming (links, best, witness))))) =
    length incoming + length (lt_operations links).
Proof.
  apply (dom_lt_fold_count (dom_lt_predecessor limit semis)
    (fun acc => length (lt_operations (fst (fst acc))))).
  intros [[current current_best] current_witness] source.
  apply dom_lt_predecessor_operations.
Qed.

(** A settlement records at most its predecessor queries and one parent link. *)
Lemma dom_lt_settle_operations numeric st v :
  length (lt_operations (lt_semi_links (dom_lt_settle numeric st v))) <=
    length (lt_operations (lt_semi_links st)) + 1 +
      length (match trie_get (dom_lt_key v) (lt_numeric_pred numeric) with
        None => [] | Some row => row end).
Proof.
  unfold dom_lt_settle.
  destruct (trie_get (dom_lt_key v) (lt_numeric_parent numeric)) as [p|].
  2: { eapply Nat.le_trans; [apply Nat.le_add_r|apply Nat.le_add_r]. }
  set (incoming := match trie_get (dom_lt_key v) (lt_numeric_pred numeric) with
    None => [] | Some row => row end).
  pose proof (dom_lt_predecessors_operations (lt_numeric_limit numeric)
    (lt_semis st) incoming (lt_semi_links st) p p) as Hlog.
  revert Hlog.
  generalize (fold_left (dom_lt_predecessor (lt_numeric_limit numeric) (lt_semis st))
    incoming (lt_semi_links st, p, p)).
  intros [[links best] witness] Hlog.
  cbn [fst] in Hlog. cbn [lt_semi_links dom_lt_link lt_operations length].
  now apply dom_lt_count_link.
Qed.

Local Opaque dom_lt_settle.

(** A semidominator fold has one possible link plus its row queries per numeric vertex. *)
Lemma dom_lt_settlements_operations numeric order st :
  length (lt_operations (lt_semi_links (fold_left (dom_lt_settle numeric) order st))) <=
    length (lt_operations (lt_semi_links st)) + length order +
      fold_right (fun v total =>
        length (match trie_get (dom_lt_key v) (lt_numeric_pred numeric) with
          None => [] | Some row => row end) + total) 0 order.
Proof.
  apply (dom_lt_fold_count_le (dom_lt_settle numeric)
    (fun current => length (lt_operations (lt_semi_links current)))
    (fun v => length (match trie_get (dom_lt_key v) (lt_numeric_pred numeric) with
      None => [] | Some row => row end))).
  apply dom_lt_settle_operations.
Qed.

(** Each bucket member records one evaluator query. *)
Lemma dom_lt_bucket_member_operations limit semis s st v :
  length (lt_operations (lt_bucket_links (dom_lt_bucket_member limit semis s st v))) =
    S (length (lt_operations (lt_bucket_links st))).
Proof.
  pose proof (dom_lt_eval_operations limit semis (lt_bucket_links st) v) as Hlog.
  unfold dom_lt_bucket_member.
  destruct (dom_lt_eval limit semis (lt_bucket_links st) v) as [links chosen].
  cbn [fst] in Hlog. cbn [lt_bucket_links]. now rewrite Hlog.
Qed.

Local Opaque dom_lt_bucket_member.

(** Folding one bucket records exactly as many evaluations as it has members. *)
Lemma dom_lt_bucket_members_operations limit semis s row st :
  length (lt_operations (lt_bucket_links
    (fold_left (dom_lt_bucket_member limit semis s) row st))) =
    length row + length (lt_operations (lt_bucket_links st)).
Proof.
  apply (dom_lt_fold_count (dom_lt_bucket_member limit semis s)
    (fun current => length (lt_operations (lt_bucket_links current)))).
  apply dom_lt_bucket_member_operations.
Qed.

(** A bucket step records its members and at most one link. *)
Lemma dom_lt_bucket_step_operations numeric semis buckets st s :
  length (lt_operations (lt_bucket_links (dom_lt_bucket_step numeric semis buckets st s))) <=
    length (lt_operations (lt_bucket_links st)) + 1 +
      length (match trie_get (dom_lt_key s) buckets with None => [] | Some row => row end).
Proof.
  unfold dom_lt_bucket_step.
  set (row := match trie_get (dom_lt_key s) buckets with None => [] | Some row => row end).
  pose proof (dom_lt_bucket_members_operations (lt_numeric_limit numeric) semis s row st)
    as Hlog.
  destruct (trie_get (dom_lt_key s) (lt_numeric_parent numeric)) as [p|];
    cbn [lt_bucket_links dom_lt_link lt_operations length].
  - now apply dom_lt_count_link.
  - eapply Nat.le_trans; [apply Nat.le_succ_diag_r|]. now apply dom_lt_count_link.
Qed.

Local Opaque dom_lt_bucket_step.

(** A bucket fold charges each listed row once, plus one possible link per entry. *)
Lemma dom_lt_bucket_steps_operations numeric semis buckets order st :
  length (lt_operations (lt_bucket_links
    (fold_left (dom_lt_bucket_step numeric semis buckets) order st))) <=
    length (lt_operations (lt_bucket_links st)) + length order +
      fold_right (fun v total =>
        length (match trie_get (dom_lt_key v) buckets with None => [] | Some row => row end) +
          total) 0 order.
Proof.
  apply (dom_lt_fold_count_le (dom_lt_bucket_step numeric semis buckets)
    (fun current => length (lt_operations (lt_bucket_links current)))
    (fun v => length (match trie_get (dom_lt_key v) buckets with
      None => [] | Some row => row end))).
  apply dom_lt_bucket_step_operations.
Qed.

(** * Graph traversal cost helpers *)

(** A listed key is no wider than its row's maximum key width. *)
Lemma dom_time_width_member vs v : In v vs -> Pos.size_nat v <= vertex_width vs.
Proof.
  unfold vertex_width. induction vs as [|x xs IH]; cbn [In fold_right]; [tauto|].
  change graph_max with Nat.max. intros [Heq|Hin].
  - subst x. apply Nat.le_max_l.
  - eapply Nat.le_trans; [apply IH; exact Hin|apply Nat.le_max_r].
Qed.

(** Listed vertex widths are bounded by the full graph width. *)
Local Lemma dom_lt_vertex_width_le g :
  vertex_width (nodes g) <= graph_width (base g).
Proof.
  destruct g as [[vs rows] predecessors vertices edges]. cbn [nodes base graph_width].
  change graph_max with Nat.max. apply Nat.le_max_l.
Qed.

(** Taking a maximum examines no more than the first unary argument. *)
Lemma dom_time_graph_max a b : (T_graph_max a b <= N.of_nat a + 1)%N.
Proof.
  revert b. induction a as [|a IH]; intros [|b]; time_step.
Qed.

(** Successor lookup pays two observations per key digit and its wrapper. *)
Lemma dom_time_succs g v :
  (T_succs g v <= 2 * N.of_nat (Pos.size_nat v) + 1)%N.
Proof.
  destruct g as [vs adjacency]. unfold T_succs. time_simpl.
  PTrieT.trie_get_le. lia.
Qed.

(** Uniform callback costs need only hold on the list being folded. *)
Lemma dom_time_fold_left {A B} (f : A -> B -> A) (T_f : A -> B -> N)
    k xs acc :
  (forall x, In x xs -> forall acc, (T_f acc x <= k)%N) ->
  (List.T_fold_left f T_f xs acc <= (k + 1) * N.of_nat (length xs) + 1)%N.
Proof.
  revert acc. induction xs as [|x xs IH]; intros acc Hbound.
  - time_unfold @List.T_fold_left. cbn [length]. lia.
  - pose proof (Hbound x (or_introl eq_refl) acc) as Hhead.
    specialize (IH (f acc x) (fun y Hy => Hbound y (or_intror Hy))).
    time_unfold @List.T_fold_left. cbn [length]. rewrite Nat2N.inj_succ. nia.
Qed.

(** Computing a row maximum charges the width of each key in that row. *)
Lemma dom_time_vertex_width vs w : vertex_width vs <= w ->
  (T_vertex_width vs <= 8 * N.of_nat (length vs + 1) * N.of_nat (w + 1))%N.
Proof.
  revert w. induction vs as [|v vs IH]; intros w Hwidth.
  - unfold T_vertex_width. time_unfold @List.T_fold_right. time_simpl.
    cbn [length]. nia.
  - assert (Hhead : Pos.size_nat v <= w).
    { eapply Nat.le_trans; [apply (dom_time_width_member (v :: vs) v); now left|
        exact Hwidth]. }
    assert (Htail : vertex_width vs <= w).
    { unfold vertex_width in Hwidth |- *. cbn [fold_right] in Hwidth.
      change graph_max with Nat.max in Hwidth |- *. lia. }
    specialize (IH w Htail).
    pose proof (Pos.T_size_nat_le v) as Hbits.
    pose proof (dom_time_graph_max (Pos.size_nat v) (vertex_width vs)) as Hmax.
    unfold vertex_width in Hmax.
    unfold T_vertex_width in IH |- *. time_unfold @List.T_fold_right.
    time_simpl. cbn [length]. rewrite Nat2N.inj_add, Nat2N.inj_succ.
    nia.
Qed.

(** Counting outgoing occurrences pays once for each row and each list entry. *)
Lemma dom_time_edge_fold g vs w :
  (forall v, In v vs -> Pos.size_nat v <= w) ->
  (List.T_fold_right (fun v count => (length (succs g v) + count)%nat)
      (fun v count => 1 + (T_succs g v + Datatypes.T_length (succs g v) +
        Nat.T_add (length (succs g v)) count)) 0%nat vs <=
    16 * N.of_nat (length vs +
      fold_right (fun v count => (length (succs g v) + count)%nat) 0%nat vs + 1) *
      N.of_nat (w + 1))%N.
Proof.
  induction vs as [|v vs IH]; intro Hwidth.
  - time_unfold @List.T_fold_right. cbn [length fold_right]. nia.
  - pose proof (Hwidth v (or_introl eq_refl)) as Hhead.
    specialize (IH (fun x Hx => Hwidth x (or_intror Hx))).
    pose proof (dom_time_succs g v) as Hrow.
    pose proof (Datatypes.T_length_le (succs g v)) as Hlength.
    pose proof (Nat.T_add_le (length (succs g v))
      (fold_right (fun v count => length (succs g v) + count) 0 vs)) as Hadd.
    time_unfold @List.T_fold_right. cbn [length fold_right].
    rewrite !Nat2N.inj_add, !Nat2N.inj_succ in *. nia.
Qed.

(** Computing the graph maximum pays for its listed keys and successor entries. *)
Lemma dom_time_width_fold g vs w :
  (forall v, In v vs -> Pos.size_nat v <= w /\ vertex_width (succs g v) <= w) ->
  (List.T_fold_right (fun v width => graph_max (vertex_width (succs g v)) width)
      (fun v width => 1 + (T_succs g v + T_vertex_width (succs g v) +
        T_graph_max (vertex_width (succs g v)) width)) 0%nat vs <=
    32 * N.of_nat (length vs +
      fold_right (fun v count => (length (succs g v) + count)%nat) 0%nat vs + 1) *
      N.of_nat (w + 1))%N.
Proof.
  induction vs as [|v vs IH]; intro Hwidth.
  - time_unfold @List.T_fold_right. cbn [length fold_right]. nia.
  - destruct (Hwidth v (or_introl eq_refl)) as [Hhead Hrow_width].
    specialize (IH (fun x Hx => Hwidth x (or_intror Hx))).
    pose proof (dom_time_succs g v) as Hrow.
    pose proof (dom_time_vertex_width (succs g v) w Hrow_width) as Hbits.
    pose proof (dom_time_graph_max (vertex_width (succs g v))
      (fold_right (fun v width => graph_max (vertex_width (succs g v)) width) 0 vs)) as Hmax.
    time_unfold @List.T_fold_right. cbn [length fold_right].
    rewrite !Nat2N.inj_add, !Nat2N.inj_succ in *. nia.
Qed.

(** The graph maximum bounds every listed key and every listed successor row. *)
Lemma dom_time_graph_width g v : In v (verts g) ->
  Pos.size_nat v <= graph_width g /\ vertex_width (succs g v) <= graph_width g.
Proof.
  destruct g as [vs adjacency]. intro Hin. split.
  - eapply Nat.le_trans; [apply dom_time_width_member; exact Hin|].
    cbn [graph_width]. change graph_max with Nat.max. apply Nat.le_max_l.
  - cbn [verts] in Hin. cbn [graph_width]. change graph_max with Nat.max.
    eapply Nat.le_trans; [|apply Nat.le_max_r].
    induction vs as [|x xs IH]; cbn [In fold_right] in Hin |- *; [tauto|].
    destruct Hin as [Heq|Hin].
    + subst x. apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; exact Hin|apply Nat.le_max_r].
Qed.

(** Graph size and width observations fit the same occurrence-and-width scan budget. *)
Lemma dom_time_graph_observations g :
  (T_graph_n g + T_graph_e g + T_graph_width g <=
    128 * N.of_nat ((graph_n g + graph_e g + 1) * (graph_width g + 1)))%N.
Proof.
  pose proof (dom_time_edge_fold g (verts g) (graph_width g)
    (fun v Hv => proj1 (dom_time_graph_width g v Hv))) as Hedges.
  pose proof (dom_time_width_fold g (verts g) (graph_width g)
    (fun v Hv => dom_time_graph_width g v Hv)) as Hrows.
  assert (Hvertices : vertex_width (verts g) <= graph_width g).
  { destruct g as [vs adjacency]. cbn [verts graph_width].
    change graph_max with Nat.max. apply Nat.le_max_l. }
  pose proof (dom_time_vertex_width (verts g) (graph_width g) Hvertices) as Hkeys.
  pose proof (dom_time_graph_max (vertex_width (verts g))
    (fold_right (fun v w => graph_max (vertex_width (succs g v)) w) 0 (verts g))) as Hmax.
  pose proof (Datatypes.T_length_le (verts g)) as Hlength.
  destruct g as [vs adjacency]. cbn [verts] in *.
  unfold T_graph_n, T_graph_e, T_graph_width. time_simpl.
  cbn [graph_n graph_e] in *. rewrite !Nat2N.inj_mul, !Nat2N.inj_add in *. nia.
Qed.

(** A listed vertex is bounded by the prepared graph's maximum key width. *)
Lemma dom_listed_key_width g v : In v (nodes g) ->
  Pos.size_nat v <= graph_width (base g).
Proof.
  destruct g as [[vs adjacency] predecessors count_v count_e]. intro Hin.
  exact (proj1 (dom_time_graph_width (Digraph vs adjacency) v Hin)).
Qed.

(** * Binary counter cost helpers *)

(** Set bits pay for carries in the reader's binary position counter. *)
Fixpoint dom_positive_credit (p : positive) : N :=
  match p with
  | xH => 1%N
  | xO q => dom_positive_credit q
  | xI q => (1 + dom_positive_credit q)%N
  end.

Definition dom_counter_credit (n : N) : N :=
  match n with N0 => 0%N | Npos p => dom_positive_credit p end.

(** Each positive increment releases the credit attached to its carry chain. *)
Lemma dom_time_positive_succ p :
  (Pos.T_succ p + dom_positive_credit (Pos.succ p) <=
    2 + dom_positive_credit p)%N.
Proof.
  induction p as [p IH|p IH|]; time_unfold Pos.T_succ;
    cbn [Pos.succ dom_positive_credit]; lia.
Qed.

(** The natural-number wrapper costs one further call per increment. *)
Lemma dom_time_counter_succ n :
  (N.T_succ n + dom_counter_credit (N.succ n) <=
    3 + dom_counter_credit n)%N.
Proof.
  destruct n as [|p]; time_unfold N.T_succ; cbn [N.succ dom_counter_credit].
  - cbn [dom_positive_credit]. lia.
  - pose proof (dom_time_positive_succ p). lia.
Qed.

(** Building a positive from unary input amortizes its successive binary carries. *)
Lemma dom_time_of_succ_nat n :
  (Key.Pos.T_of_succ_nat n + dom_positive_credit (Pos.of_succ_nat n) <=
    3 * N.of_nat n + 2)%N.
Proof.
  induction n as [|n IH]; time_unfold Key.Pos.T_of_succ_nat.
  - reflexivity.
  - pose proof (dom_time_positive_succ (Pos.of_succ_nat n)) as Hcarry.
    cbn [Pos.of_succ_nat]. lia.
Qed.

(** Reading the unary count once has linear total conversion cost. *)
Lemma dom_time_of_nat n : (TimeHelpers.N.T_of_nat n <= 3 * N.of_nat n + 2)%N.
Proof.
  destruct n as [|n]; time_unfold TimeHelpers.N.T_of_nat; [lia|].
  pose proof (dom_time_of_succ_nat n). lia.
Qed.

(** A positive's bit count never exceeds its numeric value. *)
Lemma dom_positive_size_value p : (N.of_nat (Pos.size_nat p) <= N.pos p)%N.
Proof.
  induction p as [p IH|p IH|]; cbn [Pos.size_nat].
  - change (N.of_nat (S (Pos.size_nat p)) <= 2 * N.pos p + 1)%N.
    rewrite Nat2N.inj_succ. lia.
  - change (N.of_nat (S (Pos.size_nat p)) <= 2 * N.pos p)%N.
    rewrite Nat2N.inj_succ. lia.
  - reflexivity.
Qed.

(** Natural bit counts are bounded by the values they represent. *)
Lemma dom_size_value n : (N.of_nat (N.size_nat n) <= n)%N.
Proof.
  destruct n as [|p]; [reflexivity|apply dom_positive_size_value].
Qed.
(** Reconstruction credit counts trie nodes and all stored value bits. *)
Fixpoint dom_rebuilt_weight_ne (t : trie_ne positive) : nat :=
  match t with
  | N001 r => 1 + dom_rebuilt_weight_ne r
  | N010 v => 1 + Pos.size_nat v
  | N011 v r => 1 + Pos.size_nat v + dom_rebuilt_weight_ne r
  | N100 l => 1 + dom_rebuilt_weight_ne l
  | N101 l r => 1 + dom_rebuilt_weight_ne l + dom_rebuilt_weight_ne r
  | N110 l v => 1 + dom_rebuilt_weight_ne l + Pos.size_nat v
  | N111 l v r => 1 + dom_rebuilt_weight_ne l + Pos.size_nat v + dom_rebuilt_weight_ne r
  end.

Definition dom_rebuilt_weight (t : ptrie positive) : nat :=
  match t with Empty => 0 | Nodes n => dom_rebuilt_weight_ne n end.

(** A reconstructed node introduces only its node and optional value credit. *)
Lemma dom_rebuilt_weight_node l o r :
  dom_rebuilt_weight (PTrieCode.node l o r) <=
  1 + dom_rebuilt_weight l +
    (match o with None => 0 | Some v => Pos.size_nat v end) + dom_rebuilt_weight r.
Proof.
  destruct l, o, r; cbn [PTrieCode.node dom_rebuilt_weight dom_rebuilt_weight_ne]; lia.
Qed.

(** Children and an existing value spend at most the containing trie's credit. *)
Lemma dom_rebuilt_weight_parts t :
  dom_rebuilt_weight (trie_left t) +
    (match trie_value t with None => 0 | Some v => Pos.size_nat v end) +
    dom_rebuilt_weight (trie_right t) <= dom_rebuilt_weight t.
Proof.
  destruct t as [|t]; [reflexivity|]. destruct t;
    cbn [trie_left trie_value trie_right dom_rebuilt_weight dom_rebuilt_weight_ne]; lia.
Qed.

(** Insertion pays for its key path and the inserted value once. *)
Lemma dom_rebuilt_weight_set p v t :
  dom_rebuilt_weight (PTrieCode.set p v t) <=
    dom_rebuilt_weight t + Pos.size_nat p + Pos.size_nat v.
Proof.
  revert t. induction p as [p IH|p IH|]; intro t;
    cbn [PTrieCode.set PTrieCode.replace Pos.size_nat].
  all: eapply Nat.le_trans; [apply dom_rebuilt_weight_node|].
  all: pose proof (dom_rebuilt_weight_parts t) as Hparts.
  - specialize (IH (trie_right t)). unfold PTrieCode.set in IH.
    unfold PTrieCode.left, PTrieCode.value, PTrieCode.right in *. lia.
  - specialize (IH (trie_left t)). unfold PTrieCode.set in IH.
    unfold PTrieCode.left, PTrieCode.value, PTrieCode.right in *. lia.
  - unfold PTrieCode.left, PTrieCode.right in *. lia.
Qed.
(** A bounded predicate is charged only on elements that the list contains. *)
Lemma dom_time_forallb {A} (f : A -> bool) (T_f : A -> N) k xs :
  (forall x, In x xs -> (T_f x <= k)%N) ->
  (List.T_forallb f T_f xs <= (k + 2) * N.of_nat (length xs) + 1)%N.
Proof.
  induction xs as [|x xs IH]; intro Hbound.
  - time_step.
  - specialize (IH (fun y Hy => Hbound y (or_intror Hy))).
    pose proof (Hbound x (or_introl eq_refl)) as Hx. time_step.
Qed.

(** A state invariant allows callback cost to vary with a nonnegative row weight. *)
Lemma dom_time_fold_left_state {A B} (f : A -> B -> A) (T_f : A -> B -> N)
    (Inv : A -> Prop) (weight : B -> nat) k xs acc :
  Inv acc ->
  (forall x, In x xs -> forall state, Inv state ->
    Inv (f state x) /\ (T_f state x <= k * N.of_nat (weight x + 1))%N) ->
  Inv (fold_left f xs acc) /\
  (List.T_fold_left f T_f xs acc <=
    (k + 1) * N.of_nat
      (fold_right (fun x total => (weight x + total)%nat) 0%nat xs + length xs) + 1)%N.
Proof.
  revert acc. induction xs as [|x xs IH]; intros acc Hacc Hstep.
  - cbn [fold_left fold_right length]. split; [exact Hacc|]. time_step.
  - destruct (Hstep x (or_introl eq_refl) acc Hacc) as [Hnext Hcost].
    destruct (IH (f acc x) Hnext
      (fun y Hy state Hstate => Hstep y (or_intror Hy) state Hstate)) as [Hfinal Htail].
    split; [exact Hfinal|]. time_unfold @List.T_fold_left.
    cbn [fold_right length]. rewrite !Nat2N.inj_add in *. nia.
Qed.
(** A duplicate-free sublist never contributes more nonnegative weight than its containing list. *)
Lemma dom_nodup_sum_incl {A} (weight : A -> nat) xs ys :
  NoDup xs -> incl xs ys ->
  fold_right (fun x total => weight x + total) 0 xs <=
    fold_right (fun x total => weight x + total) 0 ys.
Proof.
  revert ys. induction xs as [|x xs IH]; intros ys Hunique Hincl; [cbn; lia|].
  inversion Hunique as [|head tail Hfresh Htail]; subst head tail.
  destruct (in_split x ys (Hincl x (or_introl eq_refl))) as [left [right Heq]].
  subst ys. assert (Hrest : incl xs (left ++ right)).
  { intros y Hy. specialize (Hincl y (or_intror Hy)).
    apply in_app_iff in Hincl. apply in_app_iff.
    destruct Hincl as [Hleft|[Heq|Hright]].
    - now left.
    - subst y. contradiction.
    - now right. }
  specialize (IH (left ++ right) Htail Hrest).
  rewrite fold_right_app in IH |- *. cbn [fold_right].
  assert (Hshift : forall ns start,
    fold_right (fun y total => weight y + total) start ns =
      fold_right (fun y total => weight y + total) 0 ns + start).
  { intros ns. induction ns as [|a ns IHns]; intro start; cbn [fold_right]; [lia|].
    rewrite IHns. lia. }
  rewrite (Hshift left (fold_right (fun y total => weight y + total) 0 right)) in IH.
  rewrite (Hshift left (weight x + fold_right (fun y total => weight y + total) 0 right)).
  lia.
Qed.

(** Sum widths are bounded by the total widths of their operands. *)
Lemma dom_positive_add_width : forall p q,
  Pos.size_nat (p + q) <= Pos.size_nat p + Pos.size_nat q.
Proof.
  intros p q. apply Pos.size_nat_least. rewrite Pos2Nat.inj_add, Nat.pow_add_r.
  pose proof (Pos.size_nat_upper p) as Hp. pose proof (Pos.size_nat_upper q) as Hq.
  pose proof (Nat.pow_le_mono_r 2 1 (Pos.size_nat p) ltac:(lia) (Pos.size_nat_pos p)) as Hp2.
  pose proof (Nat.pow_le_mono_r 2 1 (Pos.size_nat q) ltac:(lia) (Pos.size_nat_pos q)) as Hq2.
  change (2 <= Nat.pow 2 (Pos.size_nat p)) in Hp2.
  change (2 <= Nat.pow 2 (Pos.size_nat q)) in Hq2. nia.
Qed.

Lemma dom_add_width : forall n m,
  N.size_nat (n + m) <= N.size_nat n + N.size_nat m.
Proof.
  intros [|p] [|q]; cbn [N.add N.size_nat]; try lia. apply dom_positive_add_width.
Qed.
(** Search tasks retain the source row and the discovered vertices that justify them. *)
Definition dom_lt_search_task_ok (g : digraph) (domain seen : list positive)
    (task : search_task) : Prop :=
  match task with
  | SearchRoot v => In v domain
  | SearchRow v row => In v seen /\ incl row (succs g v)
  | SearchLeave v => In v seen
  end.

Definition dom_lt_search_pending (tasks : list search_task) : nat :=
  fold_right (fun task total =>
    match task with
    | SearchRoot _ => 1 + total
    | SearchRow _ row => length row + total
    | SearchLeave _ => total
    end) 0 tasks.

Definition dom_lt_search_marks (seen : list positive) (marks : ptrie bool) : Prop :=
  forall v, trie_get v marks = None <-> ~ In v seen.

Record dom_lt_search_inventory (g : digraph) (domain : list positive)
    (roots : nat) (st : search_state) : Prop := DomLtSearchInventory {
  dom_lt_search_unique : NoDup (entered (search_events st));
  dom_lt_search_listed : incl (entered (search_events st)) domain;
  dom_lt_search_marked : dom_lt_search_marks (entered (search_events st)) (search_colours st);
  dom_lt_search_tasks : Forall
    (dom_lt_search_task_ok g domain (entered (search_events st))) (search_tasks st);
  dom_lt_search_budget :
    length (entered (search_events st)) + dom_lt_search_pending (search_tasks st) <=
      roots + fold_right (fun v total => length (succs g v) + total) 0
        (entered (search_events st))
}.

(** Marking a vertex extends exactly the discovered-key domain. *)
Lemma dom_lt_search_mark seen marks v b :
  dom_lt_search_marks seen marks ->
  dom_lt_search_marks (v :: seen) (PTrieCode.set v b marks).
Proof.
  unfold dom_lt_search_marks.
  intros Hmarks x. destruct (Pos.eq_dec x v) as [->|Hdifferent].
  - rewrite PTrie.get_set_same. cbn [In]. split; [discriminate|tauto].
  - rewrite PTrie.get_set_other by exact Hdifferent.
    rewrite (Hmarks x). cbn [In]. intuition congruence.
Qed.

(** Changing a discovered colour leaves the discovered-key domain unchanged. *)
Lemma dom_lt_search_mark_old seen marks v b :
  dom_lt_search_marks seen marks -> In v seen ->
  dom_lt_search_marks seen (PTrieCode.set v b marks).
Proof.
  intros Hmarks Hseen x. pose proof (dom_lt_search_mark seen marks v b Hmarks x) as Hnew.
  cbn [In] in Hnew. destruct (Pos.eq_dec v x) as [->|Hdifferent]; tauto.
Qed.

(** A task supported by earlier discoveries remains supported after further discovery. *)
Lemma dom_lt_search_tasks_extend g domain seen seen1 tasks :
  incl seen seen1 ->
  Forall (dom_lt_search_task_ok g domain seen) tasks ->
  Forall (dom_lt_search_task_ok g domain seen1) tasks.
Proof.
  intros Hincl Htasks. apply Forall_forall. intros task Htask.
  apply Forall_forall with (x := task) in Htasks; [|exact Htask].
  destruct task; cbn [dom_lt_search_task_ok] in *; intuition.
Qed.

(** Every raw search transition preserves the discovered inventory and occurrence budget. *)
Lemma dom_lt_search_inventory_step g domain roots st next :
  (forall u v, In u domain -> In v (succs g u) -> In v domain) ->
  dom_lt_search_inventory g domain roots st ->
  search_step g st = inl next -> dom_lt_search_inventory g domain roots next.
Proof.
  intros Hclosed Hinv Hstep. destruct st as [tasks marks events].
  destruct Hinv as [Hunique Hlisted Hmarks Htasks Hbudget].
  cbn [search_tasks search_colours search_events] in *.
  destruct tasks as [|task rest]; [discriminate Hstep|].
  inversion Htasks as [|head tail Htask Hrest]; subst head tail.
  destruct task as [v|u row|v]; cbn [dom_lt_search_task_ok] in Htask.
  - cbn [search_step] in Hstep.
    destruct (trie_get v marks) as [colour|] eqn:Hget; injection Hstep as <-.
    + constructor; cbn [search_tasks search_colours search_events]; try assumption.
      unfold dom_lt_search_pending in Hbudget |- *. cbn [fold_right] in Hbudget. lia.
    + constructor; cbn [search_tasks search_colours search_events entered].
      * constructor; [now apply (proj1 (Hmarks v))|exact Hunique].
      * intros x [->|Hx]; [exact Htask|now apply Hlisted].
      * now apply dom_lt_search_mark.
      * constructor.
        -- cbn [dom_lt_search_task_ok]. split; [now left|apply incl_refl].
        -- constructor; [cbn [dom_lt_search_task_ok]; now left|].
           apply (dom_lt_search_tasks_extend g domain (entered events)); [|exact Hrest].
           intros x Hx. now right.
      * unfold dom_lt_search_pending in Hbudget |- *.
        cbn [length fold_right] in Hbudget |- *. lia.
  - destruct Htask as [Hsource Hrow]. destruct row as [|v row].
    + cbn [search_step] in Hstep. injection Hstep as <-.
      constructor; cbn [search_tasks search_colours search_events]; try assumption.
    + assert (Hv : In v domain).
      { apply (Hclosed u v); [now apply Hlisted|apply Hrow; now left]. }
      assert (Htail : incl row (succs g u)).
      { intros x Hx. apply Hrow. now right. }
      cbn [search_step] in Hstep.
      destruct (trie_get v marks) as [colour|] eqn:Hget; injection Hstep as <-.
      * constructor; cbn [search_tasks search_colours search_events entered]; try assumption.
        -- constructor; [cbn [dom_lt_search_task_ok]; now split|exact Hrest].
        -- unfold dom_lt_search_pending in Hbudget |- *.
           cbn [fold_right length] in Hbudget |- *. lia.
      * constructor; cbn [search_tasks search_colours search_events entered]; try assumption.
        -- constructor; [exact Hv|].
           constructor; [cbn [dom_lt_search_task_ok]; now split|exact Hrest].
  - cbn [search_step] in Hstep. injection Hstep as <-.
    constructor; cbn [search_tasks search_colours search_events entered]; try assumption.
    eapply dom_lt_search_mark_old; eassumption.
Qed.

(** The initial root tasks own one pending unit each and no discovered vertices. *)
Lemma dom_lt_search_inventory_initial g domain roots :
  incl roots domain ->
  dom_lt_search_inventory g domain (length roots)
    (SearchState (map SearchRoot roots) Empty []).
Proof.
  intro Hroots. constructor; cbn [search_tasks search_colours search_events entered].
  - constructor.
  - intros v Hv. contradiction.
  - intros v. split; [intros _ Hin; contradiction|intro Hfresh; apply PTrie.get_empty].
  - apply Forall_forall. intros task Htask. apply in_map_iff in Htask.
    destruct Htask as [v [<- Hv]]. now apply Hroots.
  - unfold dom_lt_search_pending. clear Hroots.
    induction roots as [|v rest IH]; cbn [map length fold_right] in *; lia.
Qed.

(** Reversing a trace reverses precisely its enter subsequence. *)
Lemma dom_lt_entered_rev events : entered (rev events) = rev (entered events).
Proof.
  assert (Happ : forall left right,
    entered (left ++ right) = entered left ++ entered right).
  { intro left. induction left as [|event rest IH]; intro right; [reflexivity|].
    destruct event; cbn [app entered]; now rewrite IH. }
  induction events as [|event rest IH]; [reflexivity|].
  cbn [rev]. rewrite Happ, IH. destruct event; cbn [entered rev]; now rewrite ?app_nil_r.
Qed.

(** Every returned prefix is duplicate-free, listed and charged to entered successor rows. *)
Lemma dom_lt_search_trace_inventory g domain roots fuel :
  incl roots domain ->
  (forall u v, In u domain -> In v (succs g u) -> In v domain) ->
  let trace := match loopN (search_step g) fuel
      (SearchState (map SearchRoot roots) Empty []) with
    | inl st => rev_append (search_events st) []
    | inr events => events
    end in
  NoDup (entered trace) /\ incl (entered trace) domain /\
    length (entered trace) <= length roots +
      fold_right (fun v total => length (succs g v) + total) 0 (entered trace).
Proof.
  intros Hroots Hclosed.
  set (Result := fun events => NoDup (entered events) /\ incl (entered events) domain /\
    length (entered events) <= length roots +
      fold_right (fun v total => length (succs g v) + total) 0 (entered events)).
  assert (Houtput : forall st, dom_lt_search_inventory g domain (length roots) st ->
    Result (rev_append (search_events st) [])).
  { intros st [Hunique Hlisted Hmarks Htasks Hbudget].
    unfold Result. rewrite rev_append_rev, app_nil_r, dom_lt_entered_rev, length_rev.
    split; [now apply NoDup_rev|]. split.
    - intros v Hv. apply Hlisted. now apply in_rev in Hv.
    - assert (Hsum : forall xs, fold_right (fun v total => length (succs g v) + total) 0
          (rev xs) = fold_right (fun v total => length (succs g v) + total) 0 xs).
      { intro xs. induction xs as [|v rest IH]; [reflexivity|].
        cbn [rev fold_right]. rewrite fold_right_app.
        assert (Hshift : forall ys n,
          fold_right (fun v total => length (succs g v) + total) n ys =
          fold_right (fun v total => length (succs g v) + total) 0 ys + n).
        { intro ys. induction ys as [|y ys IHys]; intro n; cbn [fold_right]; [lia|].
          rewrite IHys. lia. }
        rewrite Hshift, IH. cbn [fold_right]. lia. }
      rewrite Hsum. lia. }
  pose proof (dom_lt_loop_invariant (search_step g)
    (dom_lt_search_inventory g domain (length roots)) Result fuel
    (SearchState (map SearchRoot roots) Empty [])) as Hrun.
  specialize (Hrun (fun st next =>
    dom_lt_search_inventory_step g domain (length roots) st next Hclosed)).
  assert (Hstop : forall st events,
    dom_lt_search_inventory g domain (length roots) st ->
    search_step g st = inr events -> Result events).
  { intros [tasks colours events] result Hinv Hstep.
    destruct tasks as [|task rest].
    - cbn [search_step] in Hstep. injection Hstep as <-.
      exact (Houtput (SearchState [] colours events) Hinv).
    - destruct task as [v|v row|v]; cbn [search_step] in Hstep;
        try destruct row as [|u row];
        repeat match type of Hstep with
        | context [match trie_get ?v ?m with _ => _ end] => destruct (trie_get v m)
        end; discriminate Hstep. }
  specialize (Hrun Hstop (dom_lt_search_inventory_initial g domain roots Hroots)).
  revert Hrun.
  generalize (loopN (search_step g) fuel (SearchState (map SearchRoot roots) Empty [])).
  intros [st|events] Hrun; [exact (Houtput st Hrun)|exact Hrun].
Qed.
(** Numeric keys retain their natural-number identity. *)
Lemma dom_lt_key_injective u v : dom_lt_key u = dom_lt_key v -> u = v.
Proof.
  intro Hkeys. apply (f_equal N.pos) in Hkeys.
  unfold dom_lt_key in Hkeys. rewrite !N.succ_pos_spec in Hkeys. now apply N.succ_inj.
Qed.

Definition dom_lt_row_mass {A : Type} (keys : list positive) (rows : ptrie (list A)) : nat :=
  fold_right (fun key total =>
    length (match trie_get key rows with None => [] | Some row => row end) + total) 0 keys.

(** An empty bucket map has no members at any queried keys. *)
Lemma dom_lt_row_mass_empty {A : Type} keys :
  dom_lt_row_mass keys (Empty : ptrie (list A)) = 0.
Proof.
  unfold dom_lt_row_mass. induction keys as [|key rest IH]; [reflexivity|].
  cbn [fold_right]. rewrite PTrie.get_empty. cbn [length]. exact IH.
Qed.

(** A row outside the counted domain does not affect its mass. *)
Lemma dom_lt_row_mass_absent {A : Type} keys (rows : ptrie (list A)) key row :
  ~ In key keys -> dom_lt_row_mass keys (PTrieCode.set key row rows) =
    dom_lt_row_mass keys rows.
Proof.
  induction keys as [|head rest IH]; intro Hfresh; [reflexivity|].
  unfold dom_lt_row_mass in *. cbn [fold_right].
  rewrite PTrie.get_set_other by (intro Heq; apply Hfresh; now left).
  rewrite IH by (intro Hin; apply Hfresh; now right). reflexivity.
Qed.

(** Prepending to one bucket increases duplicate-free row mass by at most one. *)
Lemma dom_lt_row_mass_push {A : Type} keys (rows : ptrie (list A)) key value :
  NoDup keys ->
  dom_lt_row_mass keys (PTrieCode.set key
    (value :: match trie_get key rows with None => [] | Some row => row end) rows) <=
    S (dom_lt_row_mass keys rows).
Proof.
  intro Hunique. induction Hunique as [|head rest Hfresh Hunique IH]; [cbn; lia|].
  destruct (Pos.eq_dec head key) as [->|Hdifferent].
  - cbn [dom_lt_row_mass fold_right]. rewrite PTrie.get_set_same.
    change (S (length (match trie_get key rows with None => [] | Some row => row end)) +
      dom_lt_row_mass rest (PTrieCode.set key
        (value :: match trie_get key rows with None => [] | Some row => row end) rows) <=
      S (length (match trie_get key rows with None => [] | Some row => row end) +
        dom_lt_row_mass rest rows)).
    rewrite dom_lt_row_mass_absent by exact Hfresh. reflexivity.
  - unfold dom_lt_row_mass in *. cbn [fold_right].
    rewrite PTrie.get_set_other by exact Hdifferent.
    rewrite <- Nat.add_succ_r. now apply Nat.add_le_mono_l.
Qed.

(** Every bucket insertion contributes at most one member to any distinct counted keys. *)
Lemma dom_lt_bucket_add_mass keys semis buckets v :
  NoDup keys ->
  dom_lt_row_mass keys (dom_lt_bucket_add semis buckets v) <=
    S (dom_lt_row_mass keys buckets).
Proof.
  intro Hunique. unfold dom_lt_bucket_add.
  destruct (trie_get (dom_lt_key v) semis) as [s|];
    [now apply dom_lt_row_mass_push|lia].
Qed.

(** A fold of bucket insertions contributes at most one member per input vertex. *)
Lemma dom_lt_bucket_build_mass keys semis order buckets :
  NoDup keys ->
  dom_lt_row_mass keys (fold_left (dom_lt_bucket_add semis) order buckets) <=
    length order + dom_lt_row_mass keys buckets.
Proof.
  intro Hunique. revert buckets. induction order as [|v rest IH]; intro buckets.
  - cbn [fold_left length]. reflexivity.
  - pose proof (dom_lt_bucket_add_mass keys semis buckets v Hunique) as Hhead.
    specialize (IH (dom_lt_bucket_add semis buckets v)).
    cbn [fold_left length]. clear -Hhead IH. lia.
Qed.

(** Numeric bucket keys are distinct whenever their numeric traversal order is distinct. *)
Lemma dom_lt_key_map_unique order : NoDup order -> NoDup (map dom_lt_key order).
Proof.
  intro Hunique. induction Hunique as [|v rest Hfresh Hunique IH]; cbn [map]; constructor.
  - intro Hin. apply in_map_iff in Hin. destruct Hin as [u [Hkey Hin]].
    apply dom_lt_key_injective in Hkey. subst u. contradiction.
  - exact IH.
Qed.

(** Reading every bucket in a distinct numeric order charges each inserted member at most once. *)
Lemma dom_lt_buckets_operations numeric semis :
  NoDup (lt_numeric_order numeric) ->
  length (lt_operations (lt_bucket_links (dom_lt_buckets numeric semis))) <=
    2 * length (lt_numeric_order numeric).
Proof.
  intro Hunique.
  set (order := lt_numeric_order numeric).
  set (buckets := fold_left (dom_lt_bucket_add semis) (rev_append order []) Empty).
  pose proof (dom_lt_bucket_build_mass (map dom_lt_key order) semis
    (rev_append order []) Empty (dom_lt_key_map_unique order Hunique)) as Hmass.
  fold buckets in Hmass. rewrite rev_append_rev, app_nil_r, length_rev in Hmass.
  rewrite dom_lt_row_mass_empty in Hmass.
  pose proof (dom_lt_bucket_steps_operations numeric semis buckets order
    (DomLtBucketState (DomLtLinks Empty Empty []) Empty)) as Hsteps.
  cbn [lt_bucket_links lt_operations length] in Hsteps.
  assert (Hrows : fold_right (fun v total =>
    length (match trie_get (dom_lt_key v) buckets with None => [] | Some row => row end) + total)
      0 order = dom_lt_row_mass (map dom_lt_key order) buckets).
  { clearbody buckets order. clear -buckets order.
    unfold dom_lt_row_mass. induction order as [|v rest IH];
      cbn [map fold_right]; [reflexivity|now rewrite IH]. }
  rewrite Hrows in Hsteps.
  change (length (lt_operations (lt_bucket_links
    (fold_left (dom_lt_bucket_step numeric semis buckets) order
      (DomLtBucketState (DomLtLinks Empty Empty []) Empty)))) <= 2 * length order).
  clearbody buckets order. clear -Hsteps Hmass. lia.
Qed.
(** Repeated writes of the same key-dependent value retain exactly the listed keys. *)
Lemma dom_lt_fold_set_lookup {A : Type} (value : positive -> A) xs initial key :
  trie_get key (fold_left (fun rows v => PTrieCode.set v (value v) rows) xs initial) =
    if existsb (Pos.eqb key) xs then Some (value key) else trie_get key initial.
Proof.
  revert initial. induction xs as [|v rest IH]; intro initial; [reflexivity|].
  cbn [fold_left existsb]. rewrite IH.
  destruct (Pos.eqb key v) eqn:Hkey.
  - apply Pos.eqb_eq in Hkey. subst v. rewrite PTrie.get_set_same.
    now destruct (existsb (Pos.eqb key) rest).
  - apply Pos.eqb_neq in Hkey. rewrite PTrie.get_set_other by exact Hkey.
    reflexivity.
Qed.

(** The membership test used by the filtering scan agrees with list membership. *)
Lemma dom_lt_existsb_key key xs : existsb (Pos.eqb key) xs = true <-> In key xs.
Proof.
  rewrite existsb_exists. split.
  - intros [v [Hin Heq]]. apply Pos.eqb_eq in Heq. now subst v.
  - intro Hin. exists key. split; [exact Hin|apply Pos.eqb_refl].
Qed.

(** The producer's initial trie records exactly the listed vertex keys. *)
Lemma dom_lt_listed_lookup nodes key :
  trie_get key (fold_left (fun rows v => PTrieCode.set v true rows) nodes Empty) =
    if existsb (Pos.eqb key) nodes then Some true else None.
Proof.
  rewrite (dom_lt_fold_set_lookup (fun _ => true) nodes Empty key), PTrie.get_empty.
  reflexivity.
Qed.

(** A key that fits the width is accepted by the bounded guard. *)
Local Lemma dom_lt_key_fits_complete width v :
  Pos.size_nat v <= width -> dom_lt_key_fits width v = true.
Proof.
  revert v. induction width as [|width IH]; intros [v|v|] Hwidth;
    cbn [dom_lt_key_fits Pos.size_nat] in *; try lia; try reflexivity;
    apply IH; lia.
Qed.

(** The filtered graph has a row exactly at each listed vertex. *)
Local Lemma dom_lt_root_test g r :
  (match trie_get r (succ (base (scc_graph g))) with
  | Some _ => true
  | None => false
  end) = existsb (Pos.eqb r) (nodes g).
Proof.
  unfold scc_graph. cbn [base succ]. rewrite scc_rows_lookup, PTrie.get_empty.
  destruct (existsb (Pos.eqb r) (nodes g)); reflexivity.
Qed.

(** Reusing the filtered rows preserves the original trace for every prepared record. *)
Lemma dom_lt_trace_agrees g r : dom_lt_trace g r = dom_lt_trace_spec g r.
Proof.
  unfold dom_lt_trace, dom_lt_trace_spec. rewrite dom_lt_listed_lookup.
  pose proof (dom_lt_root_test g r) as Hroot.
  destruct (existsb (Pos.eqb r) (nodes g)) eqn:Hlisted.
  - apply dom_lt_existsb_key in Hlisted.
    assert (Hvertices : dom_lt_key_fits (vertex_width (nodes g)) r = true).
    { apply dom_lt_key_fits_complete. now apply dom_time_width_member. }
    assert (Hgraph : dom_lt_key_fits (graph_width (base g)) r = true).
    { apply dom_lt_key_fits_complete. now apply dom_listed_key_width. }
    rewrite Hvertices, Hgraph.
    destruct (trie_get r (succ (base (scc_graph g)))); [reflexivity|discriminate Hroot].
  - destruct (trie_get r (succ (base (scc_graph g)))); [discriminate Hroot|].
    now destruct (dom_lt_key_fits (vertex_width (nodes g)) r);
      destruct (dom_lt_key_fits (graph_width (base g)) r).
Qed.

(** A filtered search row is the listed source row with unlisted targets removed. *)
Lemma dom_lt_filtered_row g u :
  succs (base (scc_graph g)) u =
    if existsb (Pos.eqb u) (nodes g) then
      filter (fun v => existsb (Pos.eqb v) (nodes g)) (succs (base g) u)
    else [].
Proof.
  unfold scc_graph. cbn [base succs]. rewrite dom_lt_fold_set_lookup, PTrie.get_empty.
  destruct (existsb (Pos.eqb u) (nodes g)); [|reflexivity].
  apply filter_ext. intro v. rewrite dom_lt_listed_lookup.
  now destruct (existsb (Pos.eqb v) (nodes g)).
Qed.

(** Every filtered successor stays in the original listed-key domain. *)
Lemma dom_lt_filtered_closed g u v :
  In v (succs (base (scc_graph g)) u) -> In v (nodes g).
Proof.
  rewrite dom_lt_filtered_row.
  destruct (existsb (Pos.eqb u) (nodes g)); [|contradiction].
  intro Hin. apply filter_In in Hin as [_ Hkey]. now apply dom_lt_existsb_key.
Qed.

(** Filtering never increases the number of successor occurrences in a row. *)
Lemma dom_lt_filtered_length g u :
  length (succs (base (scc_graph g)) u) <= length (succs (base g) u).
Proof.
  rewrite dom_lt_filtered_row.
  destruct (existsb (Pos.eqb u) (nodes g)); [apply filter_length_le|cbn; lia].
Qed.

(** Pointwise nonnegative weight bounds lift to a whole finite sum. *)
Lemma dom_lt_sum_le {A : Type} (left right : A -> nat) xs :
  (forall x, In x xs -> left x <= right x) ->
  fold_right (fun x total => left x + total) 0 xs <=
    fold_right (fun x total => right x + total) 0 xs.
Proof.
  induction xs as [|x rest IH]; intro Hbound; [reflexivity|].
  cbn [fold_right]. specialize (IH (fun y Hy => Hbound y (or_intror Hy))).
  pose proof (Hbound x (or_introl eq_refl)). lia.
Qed.

(** Distinct filtered source rows fit the input graph's occurrence count. *)
Lemma dom_lt_filtered_rows g order :
  NoDup order -> incl order (nodes g) ->
  fold_right (fun v total => length (succs (base (scc_graph g)) v) + total) 0 order <=
    graph_e (base g).
Proof.
  intros Hunique Hlisted.
  pose proof (dom_lt_sum_le (fun v => length (succs (base (scc_graph g)) v))
    (fun v => length (succs (base g) v)) order
    (fun v _ => dom_lt_filtered_length g v)) as Hfiltered.
  pose proof (dom_nodup_sum_incl (fun v => length (succs (base g) v))
    order (nodes g) Hunique Hlisted) as Hrows.
  replace (graph_e (base g)) with
    (fold_right (fun v total => length (succs (base g) v) + total) 0 (nodes g)) by
    (destruct g as [[vertices adjacency] predecessors count_v count_e]; reflexivity).
  eapply Nat.le_trans; eassumption.
Qed.

(** The raw producer trace has distinct listed discoveries and at most one root beyond its edges. *)
Lemma dom_lt_trace_inventory g r :
  NoDup (entered (dom_lt_trace g r)) /\
  incl (entered (dom_lt_trace g r)) (nodes g) /\
  length (entered (dom_lt_trace g r)) <= graph_n (base g) /\
  length (entered (dom_lt_trace g r)) <= graph_e (base g) + 1.
Proof.
  rewrite dom_lt_trace_agrees. unfold dom_lt_trace_spec. rewrite dom_lt_listed_lookup.
  destruct (dom_lt_key_fits (graph_width (base g)) r); [|].
  2: { cbn [entered length]. split; [constructor|]. split; [intros v Hv; contradiction|lia]. }
  destruct (existsb (Pos.eqb r) (nodes g)) eqn:Hroot.
  2: { cbn [entered length]. split; [constructor|]. split; [intros v Hv; contradiction|lia]. }
  apply dom_lt_existsb_key in Hroot.
  assert (Hroots : incl [r] (nodes g)).
  { intros v [<-|Hv]; [exact Hroot|contradiction]. }
  pose proof (dom_lt_search_trace_inventory (base (scc_graph g)) (nodes g) [r]
    (search_budget (scc_graph g) [r]) Hroots
    (fun u v _ => dom_lt_filtered_closed g u v)) as Htrace.
  change (NoDup (entered (prepared_search_trace (scc_graph g) [r])) /\
    incl (entered (prepared_search_trace (scc_graph g) [r])) (nodes g) /\
    length (entered (prepared_search_trace (scc_graph g) [r])) <= length [r] +
      fold_right (fun v total => length (succs (base (scc_graph g)) v) + total) 0
        (entered (prepared_search_trace (scc_graph g) [r]))) in Htrace.
  destruct Htrace as [Hunique [Hlisted Hbudget]].
  pose proof (dom_lt_filtered_rows g _ Hunique Hlisted) as Hrows.
  split; [exact Hunique|]. split; [exact Hlisted|]. split.
  - replace (graph_n (base g)) with (length (nodes g)) by
      (destruct g as [[vertices adjacency] predecessors count_v count_e]; reflexivity).
    now apply NoDup_incl_length.
  - cbn [length] in Hbudget. clear -Hbudget Hrows. lia.
Qed.
(** Pointwise equal weights have equal finite sums. *)
Lemma dom_lt_sum_ext {A : Type} (left right : A -> nat) xs :
  (forall x, In x xs -> left x = right x) ->
  fold_right (fun x total => left x + total) 0 xs =
    fold_right (fun x total => right x + total) 0 xs.
Proof.
  induction xs as [|x rest IH]; intro Hequal; [reflexivity|].
  cbn [fold_right]. rewrite (Hequal x (or_introl eq_refl)), IH; [reflexivity|].
  intros y Hy. apply Hequal. now right.
Qed.

(** A sum distributes over addition of its pointwise weights. *)
Lemma dom_lt_sum_add {A : Type} (left right : A -> nat) xs :
  fold_right (fun x total => left x + right x + total) 0 xs =
    fold_right (fun x total => left x + total) 0 xs +
      fold_right (fun x total => right x + total) 0 xs.
Proof.
  induction xs as [|x rest IH]; [reflexivity|]. cbn [fold_right]. rewrite IH. lia.
Qed.

(** The order of two finite nonnegative sums can be exchanged. *)
Lemma dom_lt_sum_swap {A B : Type} (weight : A -> B -> nat) xs ys :
  fold_right (fun x total =>
    fold_right (fun y subtotal => weight x y + subtotal) 0 ys + total) 0 xs =
  fold_right (fun y total =>
    fold_right (fun x subtotal => weight x y + subtotal) 0 xs + total) 0 ys.
Proof.
  induction xs as [|x rest IH].
  - cbn [fold_right]. induction ys; cbn [fold_right]; [reflexivity|assumption].
  - cbn [fold_right]. rewrite IH. symmetry. apply dom_lt_sum_add.
Qed.

(** Concatenated row lengths are the sum of the individual row lengths. *)
Lemma dom_lt_flat_map_length {A B : Type} (rows : A -> list B) xs :
  length (flat_map rows xs) = fold_right (fun x total => length (rows x) + total) 0 xs.
Proof.
  induction xs as [|x rest IH]; [reflexivity|].
  cbn [flat_map fold_right]. now rewrite length_app, IH.
Qed.

(** An extra successor contributes once for each matching target key. *)
Lemma dom_lt_filter_sum_cons targets v row :
  fold_right (fun y total => length (filter (Pos.eqb y) (v :: row)) + total) 0 targets =
    count_occ Pos.eq_dec targets v +
      fold_right (fun y total => length (filter (Pos.eqb y) row) + total) 0 targets.
Proof.
  induction targets as [|y rest IH]; [reflexivity|].
  cbn [fold_right count_occ]. rewrite IH.
  destruct (Pos.eq_dec y v) as [->|Hdifferent]; cbn [filter].
  - rewrite Pos.eqb_refl. cbn [length]. lia.
  - apply Pos.eqb_neq in Hdifferent. rewrite Hdifferent. lia.
Qed.

(** Distinct target keys can count any successor occurrence at most once. *)
Lemma dom_lt_filter_sum_bound targets row :
  NoDup targets ->
  fold_right (fun y total => length (filter (Pos.eqb y) row) + total) 0 targets <= length row.
Proof.
  intro Hunique. induction row as [|v rest IH].
  - clear Hunique. induction targets; cbn [fold_right filter length];
      [reflexivity|assumption].
  - rewrite dom_lt_filter_sum_cons. cbn [length].
    pose proof (proj1 (NoDup_count_occ Pos.eq_dec targets) Hunique v) as Hcount.
    lia.
Qed.

(** Prepared predecessor lengths count the exact original successor multiplicities. *)
Lemma dom_lt_preds_length g y :
  prepared_ok g -> length (preds g y) =
    fold_right (fun x total =>
      length (filter (Pos.eqb y) (succs (base g) x)) + total) 0 (nodes g).
Proof.
  intros [_ [_ Hpreds]]. rewrite (Permutation.Permutation_length (Hpreds y)).
  rewrite dom_lt_flat_map_length. apply dom_lt_sum_ext. intros x Hx. apply length_map.
Qed.

(** Distinct predecessor columns fit the graph occurrence count without graph well-formedness. *)
Lemma dom_lt_predecessor_total g targets :
  prepared_ok g -> NoDup targets ->
  fold_right (fun y total => length (preds g y) + total) 0 targets <= graph_e (base g).
Proof.
  intros Hprepared Hunique.
  rewrite (dom_lt_sum_ext (fun y => length (preds g y))
    (fun y => fold_right (fun x total =>
      length (filter (Pos.eqb y) (succs (base g) x)) + total) 0 (nodes g)) targets)
    by (intros y Hy; now apply dom_lt_preds_length).
  rewrite dom_lt_sum_swap.
  replace (graph_e (base g)) with
    (fold_right (fun x total => length (succs (base g) x) + total) 0 (nodes g)) by
    (destruct g as [[vertices adjacency] predecessors count_v count_e]; reflexivity).
  apply dom_lt_sum_le. intros x Hx. now apply dom_lt_filter_sum_bound.
Qed.

(** * Numeric layout inventories *)

(** A left fold preserves an invariant proved for every callback. *)
Lemma dom_lt_fold_invariant {A B : Type} (step : A -> B -> A) (Inv : A -> Prop) xs st :
  Inv st -> (forall state x, Inv state -> Inv (step state x)) ->
  Inv (fold_left step xs st).
Proof.
  intros Hinitial Hstep. revert st Hinitial.
  induction xs as [|x rest IH]; intros st Hinitial; [exact Hinitial|].
  cbn [fold_left]. apply IH. now apply Hstep.
Qed.

Definition dom_lt_rank_injective (ranks : ptrie N) : Prop :=
  forall u v n, trie_get u ranks = Some n -> trie_get v ranks = Some n -> u = v.

Definition dom_lt_rank_below (ranks : ptrie N) (next : N) : Prop :=
  forall v n, trie_get v ranks = Some n -> (n < next)%N.

(** A fresh rank cannot collide with any earlier stored rank. *)
Lemma dom_lt_rank_set_injective ranks next key :
  dom_lt_rank_injective ranks -> dom_lt_rank_below ranks next ->
  dom_lt_rank_injective (PTrieCode.set key next ranks).
Proof.
  intros Hinjective Hbelow u v n Hu Hv.
  destruct (Pos.eq_dec u key) as [->|Hu_key], (Pos.eq_dec v key) as [->|Hv_key].
  - reflexivity.
  - rewrite PTrie.get_set_same in Hu. injection Hu as <-.
    rewrite PTrie.get_set_other in Hv by exact Hv_key.
    pose proof (Hbelow v next Hv). lia.
  - rewrite PTrie.get_set_same in Hv. injection Hv as <-.
    rewrite PTrie.get_set_other in Hu by exact Hu_key.
    pose proof (Hbelow u next Hu). lia.
  - rewrite PTrie.get_set_other in Hu by exact Hu_key.
    rewrite PTrie.get_set_other in Hv by exact Hv_key.
    eapply Hinjective; eassumption.
Qed.

(** The updated rank map is bounded by the incremented discovery counter. *)
Lemma dom_lt_rank_set_below ranks next key :
  dom_lt_rank_below ranks next ->
  dom_lt_rank_below (PTrieCode.set key next ranks) (N.succ next).
Proof.
  intros Hbelow v n Hget. destruct (Pos.eq_dec v key) as [->|Hdifferent].
  - rewrite PTrie.get_set_same in Hget. injection Hget as <-. lia.
  - rewrite PTrie.get_set_other in Hget by exact Hdifferent.
    specialize (Hbelow v n Hget). lia.
Qed.

(** Assigning a positive discovery rank preserves positivity of every stored rank. *)
Lemma dom_lt_rank_set_positive ranks next key :
  (forall v n, trie_get v ranks = Some n -> (0 < n)%N) -> (0 < next)%N ->
  forall v n, trie_get v (PTrieCode.set key next ranks) = Some n -> (0 < n)%N.
Proof.
  intros Hpositive Hnext v n Hget. destruct (Pos.eq_dec v key) as [->|Hdifferent].
  - rewrite PTrie.get_set_same in Hget. now injection Hget as <-.
  - rewrite PTrie.get_set_other in Hget by exact Hdifferent. now apply (Hpositive v).
Qed.

(** Inserting a rank extends the lookup domain by exactly its key. *)
Lemma dom_lt_rank_set_domain (ranks : ptrie N) key rank v :
  (exists n, trie_get v (PTrieCode.set key rank ranks) = Some n) <->
    v = key \/ exists n, trie_get v ranks = Some n.
Proof.
  destruct (Pos.eq_dec v key) as [->|Hdifferent].
  - rewrite PTrie.get_set_same. split; [now left|]. intros _. now exists rank.
  - rewrite PTrie.get_set_other by exact Hdifferent. tauto.
Qed.

(** Numeric layout fields retain the exact discovered domain and its consecutive counter. *)
Record dom_lt_layout_inventory (st : dom_lt_layout) : Prop := DomLtLayoutInventory {
  dom_lt_layout_injective : dom_lt_rank_injective (lt_rank st);
  dom_lt_layout_bounded : dom_lt_rank_below (lt_rank st) (lt_next st);
  dom_lt_layout_domain : forall v,
    In v (lt_reverse_order st) <-> exists n, trie_get v (lt_rank st) = Some n;
  dom_lt_layout_next : lt_next st = N.of_nat (length (lt_reverse_order st) + 1);
  dom_lt_layout_positive : forall v n, trie_get v (lt_rank st) = Some n -> (0 < n)%N
}.

(** Each trace event preserves rank injectivity, the exact domain and its discovery counter. *)
Lemma dom_lt_layout_event_inventory st event :
  dom_lt_layout_inventory st -> dom_lt_layout_inventory (dom_lt_event st event).
Proof.
  intros [Hinjective Hbounded Hdomain Hnext Hpositive].
  destruct event as [v|v|kind u v];
    cbn [dom_lt_event lt_reverse_order lt_rank lt_next].
  - constructor; cbn [lt_rank lt_next lt_reverse_order].
    + now apply dom_lt_rank_set_injective.
    + now apply dom_lt_rank_set_below.
    + intro x. rewrite dom_lt_rank_set_domain, <- Hdomain. cbn [In]. intuition congruence.
    + cbn [length]. now rewrite Hnext, <- Nat2N.inj_succ.
    + apply dom_lt_rank_set_positive; [exact Hpositive|]. rewrite Hnext. lia.
  - constructor; cbn [lt_rank lt_next lt_reverse_order]; assumption.
  - constructor; assumption.
Qed.

(** The producer layout assigns distinct bounded numeric ranks to precisely its discovered keys. *)
Lemma dom_lt_layout_of_inventory g r : dom_lt_layout_inventory (dom_lt_layout_of g r).
Proof.
  unfold dom_lt_layout_of. apply (dom_lt_fold_invariant dom_lt_event dom_lt_layout_inventory).
  - constructor; cbn [lt_rank lt_next lt_reverse_order length].
    + intros u v n Hget. rewrite PTrie.get_empty in Hget. discriminate Hget.
    + intros v n Hget. rewrite PTrie.get_empty in Hget. discriminate Hget.
    + intro v. split; [intro Hbad; contradiction|].
      intros [n Hget]. rewrite PTrie.get_empty in Hget. discriminate Hget.
    + reflexivity.
    + intros v n Hget. rewrite PTrie.get_empty in Hget. discriminate Hget.
  - intros st event Hinv. now apply dom_lt_layout_event_inventory.
Qed.

(** The layout's reverse order is the reversed enter subsequence of the trace. *)
Lemma dom_lt_layout_reverse events st :
  lt_reverse_order (fold_left dom_lt_event events st) =
    rev (entered events) ++ lt_reverse_order st.
Proof.
  revert st. induction events as [|event rest IH]; intro st; [reflexivity|].
  cbn [fold_left]. rewrite IH.
  destruct event; cbn [dom_lt_event lt_reverse_order entered rev];
    [now rewrite <- app_assoc|reflexivity|reflexivity].
Qed.

(** The public DFS order is exactly the trace's enter subsequence. *)
Lemma dom_lt_dfs_entered g r : dom_lt_dfs g r = entered (dom_lt_trace g r).
Proof.
  unfold dom_lt_dfs, dom_lt_layout_of. rewrite dom_lt_layout_reverse.
  cbn [lt_reverse_order]. rewrite app_nil_r, rev_append_rev, app_nil_r, rev_involutive.
  reflexivity.
Qed.

(** The producer's DFS order is distinct, listed and bounded by vertices and occurrences. *)
Lemma dom_lt_dfs_inventory g r :
  NoDup (dom_lt_dfs g r) /\ incl (dom_lt_dfs g r) (nodes g) /\
  length (dom_lt_dfs g r) <= graph_n (base g) /\
  length (dom_lt_dfs g r) <= graph_e (base g) + 1.
Proof.
  rewrite dom_lt_dfs_entered. apply dom_lt_trace_inventory.
Qed.

(** Rank filtering can only discard predecessor occurrences. *)
Lemma dom_lt_ranked_row_length ranks row :
  length (dom_lt_ranked_row ranks row) <= length row.
Proof.
  induction row as [|v rest IH]; [reflexivity|].
  unfold dom_lt_ranked_row in *. cbn [fold_right].
  destruct (trie_get v ranks); cbn [length]; lia.
Qed.

Local Opaque dom_lt_layout_of.

(** Reversing a list does not change its summed nonnegative weight. *)
Lemma dom_lt_sum_rev {A : Type} (weight : A -> nat) xs :
  fold_right (fun x total => weight x + total) 0 (rev xs) =
    fold_right (fun x total => weight x + total) 0 xs.
Proof.
  assert (Hshift : forall ys initial,
    fold_right (fun x total => weight x + total) initial ys =
      fold_right (fun x total => weight x + total) 0 ys + initial).
  { intro ys. induction ys as [|y rest IH]; intro initial; cbn [fold_right]; [lia|].
    rewrite IH. lia. }
  induction xs as [|x rest IH]; [reflexivity|].
  cbn [rev fold_right]. rewrite fold_right_app, Hshift, IH. cbn [fold_right]. lia.
Qed.

(** Mapping input keys merely composes the weight in a finite sum. *)
Lemma dom_lt_sum_map {A B : Type} (weight : B -> nat) (key : A -> B) xs :
  fold_right (fun x total => weight x + total) 0 (map key xs) =
    fold_right (fun x total => weight (key x) + total) 0 xs.
Proof.
  induction xs as [|x rest IH]; cbn [map fold_right]; [reflexivity|now rewrite IH].
Qed.

(** A key map injective on a distinct input list produces distinct output keys. *)
Lemma dom_lt_map_unique_on {A B : Type} (key : A -> B) xs :
  NoDup xs ->
  (forall u v, In u xs -> In v xs -> key u = key v -> u = v) ->
  NoDup (map key xs).
Proof.
  intro Hunique. induction Hunique as [|v rest Hfresh Hunique IH]; intro Hinjective.
  - constructor.
  - cbn [map]. constructor.
    + intro Hin. apply in_map_iff in Hin. destruct Hin as [u [Heq Hu]].
      assert (u = v) by (apply Hinjective; [now right|now left|exact Heq]).
      now subst u.
    + apply IH. intros u w Hu Hw Heq.
      apply Hinjective; [now right|now right|exact Heq].
Qed.

(** Key-dependent writes preserve a previously installed value when all collisions agree. *)
Lemma dom_lt_fold_keys_preserve {A B : Type} (key : A -> positive) (value : A -> B)
    xs rows p stored :
  trie_get p rows = Some stored ->
  (forall x, In x xs -> key x = p -> value x = stored) ->
  trie_get p (fold_left (fun acc x => PTrieCode.set (key x) (value x) acc) xs rows) =
    Some stored.
Proof.
  revert rows. induction xs as [|x rest IH]; intros rows Hget Hagree; [exact Hget|].
  cbn [fold_left]. apply IH.
  - destruct (Pos.eq_dec p (key x)) as [->|Hdifferent].
    + rewrite PTrie.get_set_same. f_equal. apply Hagree; [now left|reflexivity].
    + now rewrite PTrie.get_set_other.
  - intros y Hy Hkey. apply Hagree; [now right|exact Hkey].
Qed.

(** A keyed fold exposes the assigned value at every input key when collisions agree. *)
Lemma dom_lt_fold_keys_present {A B : Type} (key : A -> positive) (value : A -> B)
    xs rows v :
  In v xs ->
  (forall x, In x xs -> key x = key v -> value x = value v) ->
  trie_get (key v)
    (fold_left (fun acc x => PTrieCode.set (key x) (value x) acc) xs rows) = Some (value v).
Proof.
  revert rows. induction xs as [|x rest IH]; intros rows Hin Hagree; [contradiction|].
  cbn [fold_left]. destruct Hin as [<-|Hin].
  - apply dom_lt_fold_keys_preserve; [apply PTrie.get_set_same|].
    intros y Hy Hkey. apply Hagree; [now right|exact Hkey].
  - apply IH; [exact Hin|]. intros y Hy Hkey. apply Hagree; [now right|exact Hkey].
Qed.

(** DFS membership is exactly membership in the layout's rank map. *)
Lemma dom_lt_dfs_rank_domain g r v :
  In v (dom_lt_dfs g r) <-> exists n, trie_get v (lt_rank (dom_lt_layout_of g r)) = Some n.
Proof.
  pose proof (dom_lt_layout_domain _ (dom_lt_layout_of_inventory g r) v) as Hdomain.
  unfold dom_lt_dfs. rewrite rev_append_rev, app_nil_r, <- in_rev. exact Hdomain.
Qed.

(** Rank lookup is injective on the actual DFS order. *)
Lemma dom_lt_dfs_rank_injective g r u v :
  In u (dom_lt_dfs g r) -> In v (dom_lt_dfs g r) ->
  dom_lt_rank_get (lt_rank (dom_lt_layout_of g r)) u =
    dom_lt_rank_get (lt_rank (dom_lt_layout_of g r)) v -> u = v.
Proof.
  intros Hu Hv Heq.
  destruct (proj1 (dom_lt_dfs_rank_domain g r u) Hu) as [nu Hnu].
  destruct (proj1 (dom_lt_dfs_rank_domain g r v) Hv) as [nv Hnv].
  unfold dom_lt_rank_get in Heq. rewrite Hnu, Hnv in Heq. subst nv.
  exact (dom_lt_layout_injective _ (dom_lt_layout_of_inventory g r) u v nu Hnu Hnv).
Qed.

(** Numeric construction records the input ranks in reverse input order. *)
Lemma dom_lt_numeric_order_fold g layout xs st :
  lt_numeric_order (fold_left (dom_lt_numeric_add g layout) xs st) =
    rev (map (dom_lt_rank_get (lt_rank layout)) xs) ++ lt_numeric_order st.
Proof.
  revert st. induction xs as [|v rest IH]; intro st; [reflexivity|].
  cbn [fold_left]. rewrite IH.
  cbn [dom_lt_numeric_add lt_numeric_order map rev]. now rewrite <- app_assoc.
Qed.

(** Numeric predecessor construction is the corresponding keyed row fold. *)
Lemma dom_lt_numeric_pred_fold g layout xs st :
  lt_numeric_pred (fold_left (dom_lt_numeric_add g layout) xs st) =
    fold_left (fun rows v => PTrieCode.set (dom_lt_key (dom_lt_rank_get (lt_rank layout) v))
      (dom_lt_ranked_row (lt_rank layout) (preds g v)) rows) xs (lt_numeric_pred st).
Proof.
  revert st. induction xs as [|v rest IH]; intro st; [reflexivity|].
  cbn [fold_left]. rewrite IH. reflexivity.
Qed.

(** The numeric order is the reversed rank image of the producer's DFS order. *)
Lemma dom_lt_numeric_order_of g r :
  lt_numeric_order (dom_lt_numeric_of g r) =
    rev (map (dom_lt_rank_get (lt_rank (dom_lt_layout_of g r))) (dom_lt_dfs g r)).
Proof.
  unfold dom_lt_numeric_of, dom_lt_dfs. rewrite dom_lt_numeric_order_fold.
  cbn [lt_numeric_order]. now rewrite app_nil_r.
Qed.

(** The numeric predecessor map is built from exactly the producer's DFS order. *)
Lemma dom_lt_numeric_pred_of g r :
  lt_numeric_pred (dom_lt_numeric_of g r) =
    fold_left (fun rows v =>
      PTrieCode.set (dom_lt_key (dom_lt_rank_get (lt_rank (dom_lt_layout_of g r)) v))
        (dom_lt_ranked_row (lt_rank (dom_lt_layout_of g r)) (preds g v)) rows)
      (dom_lt_dfs g r) Empty.
Proof.
  unfold dom_lt_numeric_of, dom_lt_dfs. rewrite dom_lt_numeric_pred_fold. reflexivity.
Qed.

(** Each numeric predecessor lookup returns the filtered row of its original vertex. *)
Lemma dom_lt_numeric_pred_lookup g r v :
  In v (dom_lt_dfs g r) ->
  trie_get (dom_lt_key (dom_lt_rank_get (lt_rank (dom_lt_layout_of g r)) v))
    (lt_numeric_pred (dom_lt_numeric_of g r)) =
      Some (dom_lt_ranked_row (lt_rank (dom_lt_layout_of g r)) (preds g v)).
Proof.
  intro Hv. rewrite dom_lt_numeric_pred_of.
  apply (dom_lt_fold_keys_present
    (fun u => dom_lt_key (dom_lt_rank_get (lt_rank (dom_lt_layout_of g r)) u))
    (fun u => dom_lt_ranked_row (lt_rank (dom_lt_layout_of g r)) (preds g u))
    (dom_lt_dfs g r) Empty v); [exact Hv|].
  intros u Hu Hkeys. apply dom_lt_key_injective in Hkeys.
  assert (u = v) by (eapply dom_lt_dfs_rank_injective; eassumption). now subst u.
Qed.

(** Actual numeric traversal ranks are distinct. *)
Lemma dom_lt_numeric_order_unique g r : NoDup (lt_numeric_order (dom_lt_numeric_of g r)).
Proof.
  rewrite dom_lt_numeric_order_of. apply NoDup_rev. apply dom_lt_map_unique_on.
  - exact (proj1 (dom_lt_dfs_inventory g r)).
  - intros u v Hu Hv Hkeys. eapply dom_lt_dfs_rank_injective; eassumption.
Qed.

(** Numeric construction preserves the number of discovered vertices. *)
Lemma dom_lt_numeric_order_length g r :
  length (lt_numeric_order (dom_lt_numeric_of g r)) = length (dom_lt_dfs g r).
Proof.
  rewrite dom_lt_numeric_order_of, length_rev, length_map. reflexivity.
Qed.

(** Numeric predecessor occurrences fit the original graph's total occurrence count. *)
Lemma dom_lt_numeric_pred_total g r :
  prepared_ok g ->
  fold_right (fun v total => length
    (match trie_get (dom_lt_key v) (lt_numeric_pred (dom_lt_numeric_of g r)) with
      None => [] | Some row => row end) + total) 0
        (lt_numeric_order (dom_lt_numeric_of g r)) <= graph_e (base g).
Proof.
  intro Hprepared. rewrite dom_lt_numeric_order_of, dom_lt_sum_rev, dom_lt_sum_map.
  eapply Nat.le_trans.
  - apply (dom_lt_sum_le _ (fun v => length (preds g v))).
    intros v Hv. rewrite (dom_lt_numeric_pred_lookup g r v Hv).
    apply dom_lt_ranked_row_length.
  - apply dom_lt_predecessor_total; [exact Hprepared|].
    exact (proj1 (dom_lt_dfs_inventory g r)).
Qed.

(** The semidominator pass records one possible link and one query per predecessor occurrence. *)
Lemma dom_lt_semidominators_operations numeric :
  length (lt_operations (lt_semi_links (dom_lt_semidominators numeric))) <=
    length (lt_numeric_order numeric) +
      fold_right (fun v total => length
        (match trie_get (dom_lt_key v) (lt_numeric_pred numeric) with
          None => [] | Some row => row end) + total) 0 (lt_numeric_order numeric).
Proof.
  unfold dom_lt_semidominators.
  exact (dom_lt_settlements_operations numeric (lt_numeric_order numeric)
    (DomLtSemiState Empty Empty (DomLtLinks Empty Empty []))).
Qed.

(** * Numeric operand ranges *)

(** The reverse layout order and forward DFS order contain the same number of discoveries. *)
Lemma dom_lt_layout_order_length g r :
  length (lt_reverse_order (dom_lt_layout_of g r)) = length (dom_lt_dfs g r).
Proof.
  unfold dom_lt_dfs. rewrite rev_append_rev, length_app, length_rev. cbn [length]. lia.
Qed.

(** Every stored producer rank is positive and no greater than the distinct discovery count. *)
Lemma dom_lt_layout_rank_discovered g r v rank :
  trie_get v (lt_rank (dom_lt_layout_of g r)) = Some rank ->
  (0 < rank <= N.of_nat (length (dom_lt_dfs g r)))%N.
Proof.
  intro Hget. pose proof (dom_lt_layout_of_inventory g r) as Hlayout.
  pose proof (dom_lt_layout_positive _ Hlayout v rank Hget) as Hpositive.
  pose proof (dom_lt_layout_bounded _ Hlayout v rank Hget) as Hbelow.
  pose proof (dom_lt_layout_next _ Hlayout) as Hnext.
  rewrite dom_lt_layout_order_length, Nat2N.inj_add in Hnext.
  split; [exact Hpositive|]. lia.
Qed.

(** The discovery rank bound also fits the original vertex inventory. *)
Lemma dom_lt_layout_rank_bound g r v rank :
  trie_get v (lt_rank (dom_lt_layout_of g r)) = Some rank ->
  (0 < rank <= N.of_nat (graph_n (base g)))%N.
Proof.
  intro Hget. pose proof (dom_lt_layout_rank_discovered g r v rank Hget) as Hrank.
  destruct (dom_lt_dfs_inventory g r) as [_ [_ [Hvertices Hedges]]]. lia.
Qed.

(** Rank lookup stays within the distinct discovery inventory, including its default zero. *)
Lemma dom_lt_rank_get_discovered g r v :
  (dom_lt_rank_get (lt_rank (dom_lt_layout_of g r)) v <=
    N.of_nat (length (dom_lt_dfs g r)))%N.
Proof.
  unfold dom_lt_rank_get.
  destruct (trie_get v (lt_rank (dom_lt_layout_of g r))) as [rank|] eqn:Hget; [|lia].
  exact (proj2 (dom_lt_layout_rank_discovered g r v rank Hget)).
Qed.

(** The rank lookup's default zero obeys the same upper bound as every stored rank. *)
Lemma dom_lt_rank_get_bound g r v :
  (dom_lt_rank_get (lt_rank (dom_lt_layout_of g r)) v <=
    N.of_nat (graph_n (base g)))%N.
Proof.
  unfold dom_lt_rank_get.
  destruct (trie_get v (lt_rank (dom_lt_layout_of g r))) as [rank|] eqn:Hget; [|lia].
  exact (proj2 (dom_lt_layout_rank_bound g r v rank Hget)).
Qed.

(** Numeric construction leaves its discovery-limit field unchanged. *)
Lemma dom_lt_numeric_limit_fold g layout xs st :
  lt_numeric_limit (fold_left (dom_lt_numeric_add g layout) xs st) = lt_numeric_limit st.
Proof.
  revert st. induction xs as [|v rest IH]; intro st; [reflexivity|].
  cbn [fold_left]. rewrite IH. reflexivity.
Qed.

(** Numeric evaluation fuel is the discovery count plus one. *)
Lemma dom_lt_numeric_limit_count g r :
  lt_numeric_limit (dom_lt_numeric_of g r) = N.of_nat (length (dom_lt_dfs g r) + 1).
Proof.
  unfold dom_lt_numeric_of. rewrite dom_lt_numeric_limit_fold. cbn [lt_numeric_limit].
  rewrite (dom_lt_layout_next _ (dom_lt_layout_of_inventory g r)).
  now rewrite dom_lt_layout_order_length.
Qed.

(** Every rank in the numeric traversal order names a positive bounded discovery. *)
Lemma dom_lt_numeric_order_discovered g r rank :
  In rank (lt_numeric_order (dom_lt_numeric_of g r)) ->
  (0 < rank <= N.of_nat (length (dom_lt_dfs g r)))%N.
Proof.
  rewrite dom_lt_numeric_order_of, <- in_rev. intro Hin.
  apply in_map_iff in Hin. destruct Hin as [v [<- Hv]].
  destruct (proj1 (dom_lt_dfs_rank_domain g r v) Hv) as [n Hget].
  unfold dom_lt_rank_get. rewrite Hget. now apply (dom_lt_layout_rank_discovered g r v n).
Qed.

(** Numeric traversal ranks also fit the original vertex inventory. *)
Lemma dom_lt_numeric_order_bound g r rank :
  In rank (lt_numeric_order (dom_lt_numeric_of g r)) ->
  (0 < rank <= N.of_nat (graph_n (base g)))%N.
Proof.
  intro Hin. pose proof (dom_lt_numeric_order_discovered g r rank Hin) as Hrank.
  destruct (dom_lt_dfs_inventory g r) as [_ [_ [Hvertices Hedges]]]. lia.
Qed.

(** A trie payload invariant constrains every successful lookup independently of its key. *)
Definition dom_lt_trie_all {A : Type} (P : A -> Prop) (m : ptrie A) : Prop :=
  forall key value, trie_get key m = Some value -> P value.

(** An empty trie satisfies every payload invariant. *)
Lemma dom_lt_trie_all_empty {A : Type} (P : A -> Prop) : dom_lt_trie_all P Empty.
Proof.
  intros key value Hget. rewrite PTrie.get_empty in Hget. discriminate Hget.
Qed.

(** A trie write preserves a payload invariant when the installed value satisfies it. *)
Lemma dom_lt_trie_all_set {A : Type} (P : A -> Prop) m key value :
  dom_lt_trie_all P m -> P value -> dom_lt_trie_all P (PTrieCode.set key value m).
Proof.
  intros Hbefore Hvalue query stored Hget.
  destruct (Pos.eq_dec query key) as [->|Hdifferent].
  - rewrite PTrie.get_set_same in Hget. now injection Hget as <-.
  - rewrite PTrie.get_set_other in Hget by exact Hdifferent. now apply (Hbefore query).
Qed.

(** Identity-default lookup preserves any upper bound on payloads and its default key. *)
Lemma dom_lt_identity_bounded bound m v :
  dom_lt_trie_all (fun n => (n <= bound)%N) m -> (v <= bound)%N ->
  (dom_lt_identity m v <= bound)%N.
Proof.
  intros Hvalues Hv. unfold dom_lt_identity.
  destruct (trie_get (dom_lt_key v) m) as [stored|] eqn:Hget; [|exact Hv].
  now apply (Hvalues (dom_lt_key v)).
Qed.

(** Filtering a row through bounded ranks produces a row of bounded numeric operands. *)
Lemma dom_lt_ranked_row_bounded bound ranks row :
  dom_lt_trie_all (fun n => (n <= bound)%N) ranks ->
  Forall (fun n => (n <= bound)%N) (dom_lt_ranked_row ranks row).
Proof.
  intro Hvalues. unfold dom_lt_ranked_row. induction row as [|v rest IH]; cbn [fold_right].
  - constructor.
  - destruct (trie_get v ranks) as [stored|] eqn:Hget; [|exact IH].
    constructor; [now apply (Hvalues v)|exact IH].
Qed.

(** Numeric layout order, parents and predecessor rows all stay inside one numeric range. *)
Record dom_lt_numeric_ranges (bound : N) (numeric : dom_lt_numeric) : Prop :=
  DomLtNumericRanges {
    dom_lt_numeric_order_range : Forall (fun n => (n <= bound)%N) (lt_numeric_order numeric);
    dom_lt_numeric_parent_range :
      dom_lt_trie_all (fun n => (n <= bound)%N) (lt_numeric_parent numeric);
    dom_lt_numeric_predecessor_range :
      dom_lt_trie_all (Forall (fun n => (n <= bound)%N)) (lt_numeric_pred numeric)
  }.

(** Adding an original vertex keeps every numeric payload within the distinct discovery bound. *)
Lemma dom_lt_numeric_add_ranges g r st v :
  dom_lt_numeric_ranges (N.of_nat (length (dom_lt_dfs g r))) st ->
  dom_lt_numeric_ranges (N.of_nat (length (dom_lt_dfs g r)))
    (dom_lt_numeric_add g (dom_lt_layout_of g r) st v).
Proof.
  intros [Horder Hparents Hpredecessors]. unfold dom_lt_numeric_add.
  constructor; cbn [lt_numeric_order lt_numeric_parent lt_numeric_pred].
  - constructor; [apply dom_lt_rank_get_discovered|exact Horder].
  - destruct (trie_get v (lt_dfs_parent (dom_lt_layout_of g r))) as [p|];
      [|exact Hparents].
    apply dom_lt_trie_all_set; [exact Hparents|apply dom_lt_rank_get_discovered].
  - apply dom_lt_trie_all_set; [exact Hpredecessors|].
    apply dom_lt_ranked_row_bounded. intros key value Hget.
    exact (proj2 (dom_lt_layout_rank_discovered g r key value Hget)).
Qed.

(** Numeric layout construction bounds every operand by its distinct discovery count. *)
Lemma dom_lt_numeric_of_ranges g r :
  dom_lt_numeric_ranges (N.of_nat (length (dom_lt_dfs g r))) (dom_lt_numeric_of g r).
Proof.
  unfold dom_lt_numeric_of.
  apply (dom_lt_fold_invariant (dom_lt_numeric_add g (dom_lt_layout_of g r))
    (dom_lt_numeric_ranges (N.of_nat (length (dom_lt_dfs g r))))).
  - constructor; cbn [lt_numeric_order lt_numeric_parent lt_numeric_pred].
    + constructor.
    + apply dom_lt_trie_all_empty.
    + apply dom_lt_trie_all_empty.
  - intros st v Hrange. now apply dom_lt_numeric_add_ranges.
Qed.

(** A larger numeric budget preserves all three numeric payload-range invariants. *)
Lemma dom_lt_numeric_ranges_mono smaller larger numeric :
  (smaller <= larger)%N -> dom_lt_numeric_ranges smaller numeric ->
  dom_lt_numeric_ranges larger numeric.
Proof.
  intros Hle [Horder Hparents Hpredecessors]. constructor.
  - apply Forall_forall. intros n Hin.
    pose proof (proj1 (Forall_forall _ _) Horder n Hin) as Hsmall.
    eapply N.le_trans; [exact Hsmall|exact Hle].
  - intros key value Hget. specialize (Hparents key value Hget).
    eapply N.le_trans; [exact Hparents|exact Hle].
  - intros key row Hget. specialize (Hpredecessors key row Hget).
    apply Forall_forall. intros n Hin.
    pose proof (proj1 (Forall_forall _ _) Hpredecessors n Hin) as Hsmall.
    eapply N.le_trans; [exact Hsmall|exact Hle].
Qed.

(** The distinct discovery range weakens to the original vertex-count range for work budgets. *)
Lemma dom_lt_numeric_graph_ranges g r :
  dom_lt_numeric_ranges (N.of_nat (graph_n (base g))) (dom_lt_numeric_of g r).
Proof.
  apply (dom_lt_numeric_ranges_mono (N.of_nat (length (dom_lt_dfs g r)))).
  - pose proof (proj1 (proj2 (proj2 (dom_lt_dfs_inventory g r)))) as Hvertices. lia.
  - apply dom_lt_numeric_of_ranges.
Qed.

(** * Producer traversal clocks *)

(** A fold may spend credit carried by its changing accumulator. *)
Lemma dom_time_fold_credit {A B : Type} (step : A -> B -> A) (T_step : A -> B -> N)
    (credit : A -> N) k xs st :
  (forall x, In x xs -> forall state,
    (T_step state x + credit (step state x) <= k + credit state)%N) ->
  (List.T_fold_left step T_step xs st + credit (fold_left step xs st) <=
    (k + 1) * N.of_nat (length xs) + 1 + credit st)%N.
Proof.
  revert st. induction xs as [|x rest IH]; intros st Hstep.
  - time_unfold @List.T_fold_left. cbn [fold_left length]. lia.
  - specialize (IH (step st x) (fun y Hy => Hstep y (or_intror Hy))).
    pose proof (Hstep x (or_introl eq_refl) st) as Hhead.
    time_unfold @List.T_fold_left. cbn [fold_left length]. rewrite Nat2N.inj_succ.
    clear -IH Hhead. nia.
Qed.

(** The root-width guard stops after at most its supplied unary width. *)
Lemma dom_time_lt_key_fits width v :
  (T_dom_lt_key_fits width v <= N.of_nat width + 1)%N.
Proof.
  revert v. induction width as [|width IH]; intros [v|v|]; time_step.
Qed.

(** Discovery-counter carry credit pays the binary increment in each enter event. *)
Lemma dom_time_lt_event st event width :
  (match event with Enter v => Pos.size_nat v <= width | _ => True end) ->
  (T_dom_lt_event st event + dom_counter_credit (lt_next (dom_lt_event st event)) <=
    (2 * PTrieT.c_trie + 32) * N.of_nat (width + 1) +
      dom_counter_credit (lt_next st))%N.
Proof.
  destruct st as [order ranks parents stack next]. destruct event as [v|v|kind u v].
  - intro Hwidth.
    pose proof (PTrieT.T_set_le N v next ranks) as Hrank.
    change (PTrieCode.T_set v next ranks <=
      PTrieT.c_trie * N.of_nat (Pos.size_nat v + 1))%N in Hrank.
    pose proof (dom_time_counter_succ next) as Hcounter.
    destruct stack as [|parent rest].
    + unfold T_dom_lt_event. time_simpl.
      cbn [dom_lt_event lt_next lt_rank lt_dfs_parent lt_stack lt_reverse_order].
      rewrite !Nat2N.inj_add in *. nia.
    + pose proof (PTrieT.T_set_le positive v parent parents) as Hparent.
      change (PTrieCode.T_set v parent parents <=
        PTrieT.c_trie * N.of_nat (Pos.size_nat v + 1))%N in Hparent.
      unfold T_dom_lt_event. time_simpl.
      cbn [dom_lt_event lt_next lt_rank lt_dfs_parent lt_stack lt_reverse_order].
      rewrite !Nat2N.inj_add in *. nia.
  - intro Htrivial. destruct stack; unfold T_dom_lt_event; time_simpl;
      cbn [dom_lt_event lt_next lt_rank lt_dfs_parent lt_stack lt_reverse_order]; nia.
  - intro Htrivial. unfold T_dom_lt_event. time_simpl.
    cbn [dom_lt_event lt_next lt_rank lt_dfs_parent lt_stack lt_reverse_order]. nia.
Qed.

(** A successful width guard permits lookup of the otherwise arbitrary root key. *)
Lemma dom_lt_key_fits_bound width v :
  dom_lt_key_fits width v = true -> Pos.size_nat v <= width.
Proof.
  revert v. induction width as [|width IH]; intros [v|v|] Hfits;
    cbn [dom_lt_key_fits Pos.size_nat] in Hfits |- *; try discriminate; try lia.
  all: specialize (IH v Hfits); lia.
Qed.

(** Building the listed-key trie charges one bounded insertion per original list entry. *)
Lemma dom_time_lt_listed g :
  (List.T_fold_left (fun acc v => PTrieCode.set v true acc)
    (fun acc v => 1 + PTrieCode.T_set v true acc)%N (nodes g) Empty <=
      (PTrieT.c_trie + 4) *
        N.of_nat ((graph_n (base g) + 1) * (graph_width (base g) + 1)))%N.
Proof.
  pose proof (dom_time_fold_left (fun acc v => PTrieCode.set v true acc)
    (fun acc v => 1 + PTrieCode.T_set v true acc)%N
    ((PTrieT.c_trie + 1) * N.of_nat (graph_width (base g) + 1))%N
    (nodes g) Empty) as Hfold.
  specialize (Hfold ltac:(intros v Hv acc;
    pose proof (PTrieT.T_set_le bool v true acc) as Hset;
    change (PTrieCode.T_set v true acc <=
      PTrieT.c_trie * N.of_nat (Pos.size_nat v + 1))%N in Hset;
    pose proof (dom_listed_key_width g v Hv) as Hwidth;
    rewrite !Nat2N.inj_add in *; nia)).
  replace (length (nodes g)) with (graph_n (base g)) in Hfold by
    (destruct g as [[vs adjacency] predecessors count_v count_e]; reflexivity).
  rewrite !Nat2N.inj_mul, !Nat2N.inj_add in *. nia.
Qed.

(** The producer trace contains at most two events per discovery and one per edge occurrence. *)
Lemma dom_lt_trace_events g r :
  length (dom_lt_trace g r) <= 2 * graph_n (base g) + graph_e (base g).
Proof.
  pose proof (dom_lt_trace_inventory g r) as Htrace.
  rewrite dom_lt_trace_agrees in Htrace |- *.
  unfold dom_lt_trace_spec in Htrace |- *. rewrite dom_lt_listed_lookup in Htrace |- *.
  destruct (dom_lt_key_fits (graph_width (base g)) r); [|cbn; lia].
  destruct (existsb (Pos.eqb r) (nodes g)); [|cbn; lia].
  destruct Htrace as [Hunique [Hlisted [Hvertices Hedges]]].
  pose proof (dom_lt_filtered_rows g _ Hunique Hlisted) as Hrows.
  pose proof (prepared_search_event_bound (scc_graph g) [r]) as Hevents.
  rewrite search_event_supply_entered in Hevents.
  clear -Hevents Hrows Hvertices. lia.
Qed.

(** The trace's component bounds scale to one common graph budget before they are added. *)
Lemma dom_lt_trace_budget vertices edges width trie_coefficient search_coefficient
    listed_work width_scan guard_work root_width filter_work search_work :
  (listed_work <= (trie_coefficient + 4) * ((vertices + 1) * (width + 1)))%N ->
  (width_scan <= 128 * ((vertices + edges + 1) * (width + 1)))%N ->
  (guard_work <= width + 1)%N -> (root_width <= width)%N ->
  (filter_work <= 16384 * ((vertices + edges + 1) * (width + 1)))%N ->
  (search_work <= 2 * search_coefficient * (vertices + edges + 1 + 1) * (width + 1))%N ->
  (1 + (1 + listed_work + (1 + width_scan + guard_work +
    (2 * root_width + (filter_work + search_work)))) <=
    8 * (search_coefficient + trie_coefficient + 4096) *
      ((vertices + edges + 1) * (width + 1)))%N.
Proof.
  intros Hlisted Hscan Hguard Hroot Hfilter Hsearch.
  set (budget := ((vertices + edges + 1) * (width + 1))%N).
  assert (Hfactor : (width + 1 <= budget)%N).
  { unfold budget. replace (width + 1)%N with (1 * (width + 1))%N at 1 by lia.
    apply N.mul_le_mono_r. lia. }
  assert (Hpositive : (1 <= budget)%N) by lia.
  assert (Hlisted_big : (listed_work <= (trie_coefficient + 4) * budget)%N).
  { eapply N.le_trans; [exact Hlisted|]. apply N.mul_le_mono_l.
    unfold budget. apply N.mul_le_mono_r. lia. }
  assert (Hguard_big : (guard_work <= budget)%N) by lia.
  assert (Hroot_big : (root_width <= budget)%N) by lia.
  assert (Htwice : ((vertices + edges + 1 + 1) * (width + 1) <= 2 * budget)%N).
  { rewrite N.mul_add_distr_r, N.mul_1_l. fold budget. lia. }
  assert (Hscaled : (2 * search_coefficient *
    ((vertices + edges + 1 + 1) * (width + 1)) <=
      2 * search_coefficient * (2 * budget))%N).
  { now apply N.mul_le_mono_l. }
  replace (2 * search_coefficient * (2 * budget))%N with
    (4 * search_coefficient * budget)%N in Hscaled by
    (clearbody budget; clear -search_coefficient budget; nia).
  assert (Hsearch_big : (search_work <= 4 * search_coefficient * budget)%N).
  { rewrite <- N.mul_assoc in Hsearch. eapply N.le_trans; eassumption. }
  fold budget in Hscan, Hfilter |- *.
  clearbody budget.
  clear -Hlisted_big Hguard_big Hroot_big Hscan Hfilter Hsearch_big Hpositive.
  nia.
Qed.

(** Missing listed roots pay the guard and lookup without filtered search work. *)
Lemma dom_lt_trace_missing_budget vertices edges width trie_coefficient search_coefficient
    listed_work width_scan guard_work root_width :
  (listed_work <= (trie_coefficient + 4) * ((vertices + 1) * (width + 1)))%N ->
  (width_scan <= 128 * ((vertices + edges + 1) * (width + 1)))%N ->
  (guard_work <= width + 1)%N -> (root_width <= width)%N ->
  (1 + (1 + listed_work + (1 + width_scan + guard_work + 2 * root_width)) <=
    8 * (search_coefficient + trie_coefficient + 4096) *
      ((vertices + edges + 1) * (width + 1)))%N.
Proof.
  intros Hlisted Hscan Hguard Hroot.
  pose proof (dom_lt_trace_budget vertices edges width trie_coefficient search_coefficient
    listed_work width_scan guard_work root_width 0%N 0%N
    Hlisted Hscan Hguard Hroot (N.le_0_l _) (N.le_0_l _)) as Htime.
  clear -Htime. lia.
Qed.

(** Rejected root widths stop before either the listed lookup or the search. *)
Lemma dom_lt_trace_rejected_budget vertices edges width trie_coefficient search_coefficient
    listed_work width_scan guard_work :
  (listed_work <= (trie_coefficient + 4) * ((vertices + 1) * (width + 1)))%N ->
  (width_scan <= 128 * ((vertices + edges + 1) * (width + 1)))%N ->
  (guard_work <= width + 1)%N ->
  (1 + (1 + listed_work + (1 + width_scan + guard_work)) <=
    8 * (search_coefficient + trie_coefficient + 4096) *
      ((vertices + edges + 1) * (width + 1)))%N.
Proof.
  intros Hlisted Hscan Hguard.
  pose proof (dom_lt_trace_missing_budget vertices edges width trie_coefficient
    search_coefficient listed_work width_scan guard_work 0%N
    Hlisted Hscan Hguard (N.le_0_l _)) as Htime.
  clear -Htime. lia.
Qed.

(** Scanning only the listed key widths fits the original graph observation budget. *)
Local Lemma dom_time_lt_trace_width g :
  (T_vertex_width (nodes g) <= 128 *
    N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
      (graph_width (base g) + 1)))%N.
Proof.
  pose proof (dom_time_vertex_width (nodes g) (graph_width (base g))
    (dom_lt_vertex_width_le g)) as Hscan.
  replace (length (nodes g)) with (graph_n (base g)) in Hscan by
    (destruct g as [[vs rows] predecessors vertices edges]; reflexivity).
  rewrite !Nat2N.inj_mul, !Nat2N.inj_add in *. nia.
Qed.

(** The guarded trace pays one filtered graph construction and one listed-width scan. *)
Lemma dom_time_lt_trace g r :
  (T_dom_lt_trace g r <= (8 * (search_trace_coefficient + PTrieT.c_trie + 4096)) *
    N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
      (graph_width (base g) + 1)))%N.
Proof.
  pose proof (dom_time_lt_trace_width g) as Hscan.
  pose proof (dom_time_lt_key_fits (vertex_width (nodes g)) r) as Hguard.
  pose proof (dom_lt_vertex_width_le g) as Hwidth.
  pose proof (scc_graph_time g) as Hfilter.
  assert (Hguard_graph : (T_dom_lt_key_fits (vertex_width (nodes g)) r <=
    N.of_nat (graph_width (base g)) + 1)%N) by lia.
  unfold T_dom_lt_trace. time_simpl.
  destruct (dom_lt_key_fits (vertex_width (nodes g)) r) eqn:Hfits.
  - pose proof (dom_lt_key_fits_bound (vertex_width (nodes g)) r Hfits) as Hroot_width.
    assert (Hroot_bits : (N.of_nat (Pos.size_nat r) <=
      N.of_nat (graph_width (base g)))%N) by lia.
    destruct (trie_get r (succ (base (scc_graph g)))) as [row|] eqn:Hroot.
    + assert (Hr : In r (nodes g)).
      { pose proof (dom_lt_root_test g r) as Hmember. rewrite Hroot in Hmember.
        apply dom_lt_existsb_key. now symmetry. }
      assert (Hroots : forall v, In v [r] -> In v (nodes g)).
      { intros v [<-|Hbad]; [exact Hr|contradiction]. }
      pose proof (scc_search_time g [r] Hroots) as Hsearch.
      cbn [length] in Hsearch.
      time_simpl.
      rewrite !Nat2N.inj_mul, !Nat2N.inj_add in *.
      eapply N.le_trans; [shelve|apply dom_lt_trace_budget with (listed_work := 4%N)].
      * nia.
      * exact Hscan.
      * exact Hguard_graph.
      * exact Hroot_bits.
      * now rewrite <- N.mul_assoc in Hfilter.
      * eapply N.le_trans; [apply N.le_add_l|exact Hsearch].
      Unshelve. PTrieT.trie_get_le. lia.
    + time_simpl. rewrite ?N.add_0_r.
      rewrite !Nat2N.inj_mul, !Nat2N.inj_add in *.
      eapply N.le_trans; [shelve|apply dom_lt_trace_budget with
        (listed_work := 4%N) (search_work := 0%N)].
      * nia.
      * exact Hscan.
      * exact Hguard_graph.
      * exact Hroot_bits.
      * now rewrite <- N.mul_assoc in Hfilter.
      * apply N.le_0_l.
      Unshelve. PTrieT.trie_get_le. lia.
  - time_simpl. rewrite ?N.add_0_r.
    rewrite !Nat2N.inj_mul, !Nat2N.inj_add in *.
    eapply N.le_trans; [shelve|apply dom_lt_trace_rejected_budget with (listed_work := 4%N)].
    + nia.
    + exact Hscan.
    + exact Hguard_graph.
    Unshelve. lia.
Qed.

(** Event count and callback cost scale to one layout-fold budget. *)
Lemma dom_lt_layout_fold_budget vertices edges width trie_coefficient count work credit :
  (count <= 2 * vertices + edges)%N ->
  (work + credit <= ((2 * trie_coefficient + 32) * (width + 1) + 1) * count + 1 + 1)%N ->
  (work <= (4 * trie_coefficient + 128) *
    ((vertices + edges + 1) * (width + 1)))%N.
Proof.
  intros Hcount Hwork.
  set (budget := ((vertices + edges + 1) * (width + 1))%N).
  assert (Hpositive : (1 <= budget)%N).
  { unfold budget. clear -vertices edges width. nia. }
  assert (Hunit : ((2 * trie_coefficient + 32) * (width + 1) + 1 <=
    (2 * trie_coefficient + 33) * (width + 1))%N).
  { clear -trie_coefficient width. nia. }
  assert (Hcount_big : (count <= 2 * (vertices + edges + 1))%N) by lia.
  assert (Hscaled : (((2 * trie_coefficient + 32) * (width + 1) + 1) * count <=
    ((2 * trie_coefficient + 33) * (width + 1)) * (2 * (vertices + edges + 1)))%N).
  { now apply N.mul_le_mono. }
  replace (((2 * trie_coefficient + 33) * (width + 1)) *
    (2 * (vertices + edges + 1)))%N with ((4 * trie_coefficient + 66) * budget)%N
    in Hscaled by (unfold budget; clear -trie_coefficient vertices edges width; nia).
  assert (Hsmall : (work <= (4 * trie_coefficient + 66) * budget + 2)%N).
  { clear -Hwork Hscaled. lia. }
  fold budget. clearbody budget. clear -Hsmall Hpositive. nia.
Qed.

(** The layout fold pays bounded-key updates and amortized binary carries over the trace. *)
Lemma dom_time_lt_layout_fold g r :
  (List.T_fold_left dom_lt_event T_dom_lt_event (dom_lt_trace g r)
    (DomLtLayout [] Empty Empty [] 1%N) <=
    (4 * PTrieT.c_trie + 128) *
      N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
        (graph_width (base g) + 1)))%N.
Proof.
  pose proof (dom_time_fold_credit dom_lt_event T_dom_lt_event
    (fun st => dom_counter_credit (lt_next st))
    ((2 * PTrieT.c_trie + 32) * N.of_nat (graph_width (base g) + 1))%N
    (dom_lt_trace g r) (DomLtLayout [] Empty Empty [] 1%N)) as Hfold.
  destruct (dom_lt_trace_inventory g r) as [Hunique [Hlisted [Hvertices Hedges]]].
  assert (Hcallback : forall event, In event (dom_lt_trace g r) -> forall st,
    (T_dom_lt_event st event + dom_counter_credit (lt_next (dom_lt_event st event)) <=
      (2 * PTrieT.c_trie + 32) * N.of_nat (graph_width (base g) + 1) +
        dom_counter_credit (lt_next st))%N).
  { intros event Hevent st. apply dom_time_lt_event.
    destruct event as [v|v|kind u v]; [|exact I|exact I].
    apply dom_listed_key_width. apply Hlisted.
    now apply search_entered_member. }
  specialize (Hfold Hcallback).
  pose proof (dom_lt_trace_events g r) as Hlength.
  cbn beta in Hfold.
  change (dom_counter_credit (lt_next (DomLtLayout [] Empty Empty [] 1%N))) with 1%N in Hfold.
  apply time_of_nat_le in Hlength.
  rewrite !Nat2N.inj_mul, !Nat2N.inj_add in *.
  rewrite Nat2N.inj_mul in Hlength.
  eapply dom_lt_layout_fold_budget with (count := N.of_nat (length (dom_lt_trace g r)));
    [exact Hlength|exact Hfold].
Qed.

(** The complete layout construction includes the guarded trace and its event fold. *)
Lemma dom_time_lt_layout g r :
  (T_dom_lt_layout_of g r <= (16 * (search_trace_coefficient + PTrieT.c_trie + 4096)) *
    N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
      (graph_width (base g) + 1)))%N.
Proof.
  pose proof (dom_time_lt_trace g r) as Htrace.
  pose proof (dom_time_lt_layout_fold g r) as Hfold.
  set (budget := N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
    (graph_width (base g) + 1))) in *.
  assert (Hpositive : (1 <= budget)%N).
  { unfold budget. clear -g. rewrite Nat2N.inj_mul, !Nat2N.inj_add. nia. }
  unfold T_dom_lt_layout_of. time_simpl.
  change (List.T_fold_left dom_lt_event (fun st event => T_dom_lt_event st event)
    (dom_lt_trace g r) (DomLtLayout [] Empty Empty [] 1%N)) with
    (List.T_fold_left dom_lt_event T_dom_lt_event
      (dom_lt_trace g r) (DomLtLayout [] Empty Empty [] 1%N)).
  set (trace_work := T_dom_lt_trace g r) in *.
  set (fold_work := List.T_fold_left dom_lt_event T_dom_lt_event
    (dom_lt_trace g r) (DomLtLayout [] Empty Empty [] 1%N)) in *.
  set (search_coefficient := search_trace_coefficient) in *.
  set (trie_coefficient := PTrieT.c_trie) in *.
  clearbody trace_work fold_work search_coefficient trie_coefficient budget.
  clear -Htrace Hfold Hpositive. nia.
Qed.

Definition dom_lt_dfs_coefficient : N :=
  (32 * (search_trace_coefficient + PTrieT.c_trie + 4096))%N.

(** The DFS wrapper also reverses the discovered order once and pays its public alias. *)
Lemma dom_time_lt_dfs g r :
  (T_dom_lt_dfs g r + 1 <= dom_lt_dfs_coefficient *
    N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
      (graph_width (base g) + 1)))%N.
Proof.
  pose proof (dom_time_lt_layout g r) as Hlayout.
  pose proof (List.T_rev_append_le (lt_reverse_order (dom_lt_layout_of g r)) []) as Hreverse.
  pose proof (dom_lt_layout_order_length g r) as Hlength.
  destruct (dom_lt_dfs_inventory g r) as [Hunique [Hlisted [Hvertices Hedges]]].
  rewrite Hlength in Hreverse.
  set (budget := N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
    (graph_width (base g) + 1))) in *.
  assert (Hsize : (N.of_nat (length (dom_lt_dfs g r)) + 1 <= budget)%N).
  { assert (Hnatural : length (dom_lt_dfs g r) + 1 <=
      (graph_n (base g) + graph_e (base g) + 1) * (graph_width (base g) + 1)).
    { clear -Hvertices.
      eapply Nat.le_trans with (graph_n (base g) + graph_e (base g) + 1); [lia|].
      replace (graph_n (base g) + graph_e (base g) + 1) with
        ((graph_n (base g) + graph_e (base g) + 1) * 1) at 1 by lia.
      apply Nat.mul_le_mono_l. lia. }
    apply time_of_nat_le in Hnatural. rewrite Nat2N.inj_add in Hnatural.
    exact Hnatural. }
  assert (Hpositive : (1 <= budget)%N) by (clear -Hsize; lia).
  assert (Hreverse_big : (List.T_rev_append
    (lt_reverse_order (dom_lt_layout_of g r)) [] <= budget)%N).
  { eapply N.le_trans; [exact Hreverse|exact Hsize]. }
  unfold T_dom_lt_dfs, dom_lt_dfs_coefficient. time_simpl.
  set (layout_work := T_dom_lt_layout_of g r) in *.
  set (reverse_work := List.T_rev_append (lt_reverse_order (dom_lt_layout_of g r)) []) in *.
  set (search_coefficient := search_trace_coefficient) in *.
  set (trie_coefficient := PTrieT.c_trie) in *.
  clearbody layout_work reverse_work search_coefficient trie_coefficient budget.
  clear -Hlayout Hreverse_big Hpositive. nia.
Qed.
