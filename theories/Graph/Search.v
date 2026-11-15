(** * Depth-first search

    Search visits roots and successor occurrences in their supplied order.
    For example, an edge to an active vertex produces a back-edge event.
    Builds on: graph data, binary-fuel loops and the search signature. *)

From Stdlib Require Import List NArith PArith Lia Arith Sorting.Permutation.
From Argent Require Import Time Tactics Std BigO Loop.
From Galois.Base Require Import Trie Loop.
From Galois.Graph Require Import Data Spec DigraphSig SearchSig.
Import List.ListNotations.

Definition search_step (g : digraph) (s : search_state) : search_state + (list event) :=
  match s with
  | SearchState [] _ es => inr (rev_append es [])
  | SearchState (task :: tasks) colours es =>
    match task with
    | SearchRoot v =>
      match trie_get v colours with
      | Some _ => inl (SearchState tasks colours es)
      | None => inl (SearchState (SearchRow v (succs g v) :: SearchLeave v :: tasks)
          (PTrieCode.set v true colours) (Enter v :: es))
      end
    | SearchRow u [] => inl (SearchState tasks colours es)
    | SearchRow u (v :: vs) =>
      match trie_get v colours with
      | None => inl (SearchState (SearchRoot v :: SearchRow u vs :: tasks) colours
          (Edge Tree u v :: es))
      | Some active => inl (SearchState (SearchRow u vs :: tasks) colours
          (Edge (if active then Back else Done) u v :: es))
      end
    | SearchLeave v => inl (SearchState tasks (PTrieCode.set v false colours) (Leave v :: es))
    end
  end.
TimeFun search_step.

Definition raw_search_budget (g : digraph) (roots : list positive) : N :=
  N.of_nat (4 * (length roots +
    fold_right (fun entry n => length (snd entry) + n) 0 (PTrieCode.elements (succ g)) + 1)).
TimeFun raw_search_budget.

Definition search_trace (g : digraph) (roots : list positive) : list event :=
  match loopN (search_step g) (raw_search_budget g roots)
      (SearchState (map SearchRoot roots) Empty []) with
  | inl s => rev_append (search_events s) []
  | inr es => es
  end.
TimeFun search_trace.

Definition search_budget (g : prepared) (roots : list positive) : N :=
  N.double (N.double (nv g + ne g + N.of_nat (length roots) + 1))%N.
TimeFun search_budget.

Definition prepared_search_trace (g : prepared) (roots : list positive) : list event :=
  match loopN (search_step (base g)) (search_budget g roots)
      (SearchState (map SearchRoot roots) Empty []) with
  | inl s => rev_append (search_events s) []
  | inr es => es
  end.
TimeFun prepared_search_trace.

(** Binary fuel and unary fuel describe the same sequence of task transitions. *)
Lemma search_loopN_fuel {St Out} (step : St -> St + Out) fuel st :
  loopN step fuel st = loop_fuel step (N.to_nat fuel) st.
Proof.
  assert (Hloop : forall fs (Hacc : Acc loopN_lt fs),
      loop loopN_lt (loopN_step step) fs Hacc =
      loop_fuel step (N.to_nat (fst fs)) (snd fs)).
  { intros fs Hacc. induction Hacc as [[n state] Hacc IH] using Acc_ind_dep.
    cbn [fst snd]. destruct n as [|p]; [reflexivity|].
    assert (Hpos : 0 < N.to_nat (N.pos p)) by lia.
    destruct (N.to_nat (N.pos p)) as [|n] eqn:Hn; [lia|].
    cbn [loop loopN_step loop_fuel Acc_inv].
    destruct (step state) as [next|result]; [|reflexivity].
    rewrite IH. cbn [fst snd]. rewrite N2Nat.inj_pred, Hn. reflexivity. }
  unfold loopN. apply Hloop.
Qed.

(** Task validity includes the source and every remaining target of an adjacency row. *)
Definition search_task_valid (domain : positive -> Prop) (task : search_task) : Prop :=
  match task with
  | SearchRoot v | SearchLeave v => domain v
  | SearchRow u vs => domain u /\ Forall domain vs
  end.

(** A successor-closed domain is retained by every continuing task transition. *)
Lemma search_tasks_preserved g domain st next :
  (forall u v, domain u -> edge g u v -> domain v) ->
  Forall (search_task_valid domain) (search_tasks st) ->
  search_step g st = inl next ->
  Forall (search_task_valid domain) (search_tasks next).
Proof.
  intros Hclosed Hvalid Hstep. destruct st as [tasks colours es].
  destruct tasks as [|task tasks]; [discriminate Hstep|].
  inversion Hvalid as [|task0 tasks0 Htask Htail]; subst task0 tasks0.
  destruct task as [v|u vs|v].
  - cbn [search_step] in Hstep. destruct (trie_get v colours).
    + inversion Hstep; subst next. exact Htail.
    + inversion Hstep; subst next. constructor.
      * split; [exact Htask|]. apply Forall_forall. intros w Hin.
        apply (Hclosed v w Htask). exact Hin.
      * constructor; [exact Htask|exact Htail].
  - destruct vs as [|v vs].
    + inversion Hstep; subst next. exact Htail.
    + destruct Htask as [Hu Hvs]. inversion Hvs as [|v0 vs0 Hv Hrest]; subst v0 vs0.
      cbn [search_step] in Hstep. destruct (trie_get v colours).
      * inversion Hstep; subst next. constructor; [split; assumption|exact Htail].
      * inversion Hstep; subst next. constructor; [exact Hv|].
        constructor; [split; assumption|exact Htail].
  - inversion Hstep; subst next. exact Htail.
Qed.

(** Lookup after one colour update distinguishes its key from all other vertices. *)
Local Lemma search_colour_set x y (b : bool) colours :
  trie_get x (PTrieCode.set y b colours) =
    if Pos.eqb x y then Some b else trie_get x colours.
Proof.
  destruct (Pos.eqb_spec x y) as [Heq|Hneq].
  - subst x. apply PTrie.get_set_same.
  - apply PTrie.get_set_other. exact Hneq.
Qed.

Local Lemma search_colour_empty v : trie_get v (@Empty bool) = None.
Proof.
  apply PTrie.get_empty.
Qed.

(** White work counts two vertex tasks and the outgoing row for each listed occurrence. *)
Definition search_white g vertices (colours : ptrie bool) : nat :=
  fold_right (fun v n =>
    match trie_get v colours with
    | None => 2 + length (succs g v) + n
    | Some _ => n
    end) 0 vertices.

(** Updating any colour can only remove white work. *)
Lemma search_white_set_le g vertices colours v b :
  search_white g vertices (PTrieCode.set v b colours) <= search_white g vertices colours.
Proof.
  induction vertices as [|u rest IH]; [reflexivity|].
  unfold search_white in *. cbn [fold_right]. rewrite search_colour_set.
  destruct (Pos.eqb u v); destruct (trie_get u colours); lia.
Qed.

(** Discovering a listed white vertex transfers at least one copy of its row credit. *)
Lemma search_white_discover g vertices colours v b :
  In v vertices -> trie_get v colours = None ->
  search_white g vertices (PTrieCode.set v b colours) + 2 + length (succs g v) <=
    search_white g vertices colours.
Proof.
  intros Hin Hwhite. induction vertices as [|u rest IH]; [contradiction|].
  destruct Hin as [Heq|Hin].
  - subst u. unfold search_white. cbn [fold_right].
    rewrite search_colour_set, Pos.eqb_refl, Hwhite.
    pose proof (search_white_set_le g rest colours v b) as Hle.
    unfold search_white in Hle. lia.
  - specialize (IH Hin). unfold search_white in *. cbn [fold_right].
    rewrite search_colour_set. destruct (Pos.eqb u v); destruct (trie_get u colours); lia.
Qed.

(** Pending rows charge their targets and the administrative empty-row step. *)
Definition search_task_credit tasks : nat :=
  fold_right (fun task n =>
    match task with
    | SearchRoot _ => 1 + n
    | SearchRow _ vs => 2 * length vs + 1 + n
    | SearchLeave _ => 1 + n
    end) 0 tasks.

Definition search_finite_credit g vertices st :=
  2 * search_white g vertices (search_colours st) +
    search_task_credit (search_tasks st).

(** Every continuing task consumes finite-domain credit, including administrative tasks. *)
Lemma search_finite_decreases g vertices st next :
  Forall (search_task_valid (fun v => In v vertices)) (search_tasks st) ->
  search_step g st = inl next ->
  search_finite_credit g vertices next < search_finite_credit g vertices st.
Proof.
  intros Hvalid Hstep. destruct st as [tasks colours es].
  destruct tasks as [|task tasks]; [discriminate Hstep|].
  inversion Hvalid as [|task0 tasks0 Htask Htail]; subst task0 tasks0.
  destruct task as [v|u vs|v].
  - cbn [search_step] in Hstep. destruct (trie_get v colours) eqn:Hcolour.
    + inversion Hstep; subst next. unfold search_finite_credit, search_task_credit.
      cbn [search_colours search_tasks fold_right]. lia.
    + inversion Hstep; subst next.
      pose proof (search_white_discover g vertices colours v true Htask Hcolour) as Hwhite.
      unfold search_finite_credit, search_task_credit.
      cbn [search_colours search_tasks fold_right]. lia.
  - destruct vs as [|v vs]; cbn [search_step] in Hstep.
    + inversion Hstep; subst next. unfold search_finite_credit, search_task_credit.
      cbn [search_colours search_tasks fold_right length]. lia.
    + destruct (trie_get v colours); inversion Hstep; subst next;
        unfold search_finite_credit, search_task_credit;
        cbn [search_colours search_tasks fold_right length]; lia.
  - inversion Hstep; subst next.
    pose proof (search_white_set_le g vertices colours v false) as Hwhite.
    unfold search_finite_credit, search_task_credit.
    cbn [search_colours search_tasks fold_right]. lia.
Qed.

(** Initial credit charges every listed occurrence, allowing duplicate vertices. *)
Lemma search_finite_initial g vertices roots :
  search_finite_credit g vertices (SearchState (map SearchRoot roots) Empty []) =
    4 * length vertices +
    2 * fold_right (fun v n => length (succs g v) + n) 0 vertices + length roots.
Proof.
  unfold search_finite_credit. cbn [search_colours search_tasks].
  assert (Htasks : search_task_credit (map SearchRoot roots) = length roots).
  { induction roots as [|v rest IH].
    - reflexivity.
    - change (1 + search_task_credit (map SearchRoot rest) = S (length rest)).
      rewrite IH. lia. }
  rewrite Htasks. unfold search_white.
  induction vertices as [|v rest IH]; cbn [fold_right length] in *;
    rewrite ?search_colour_empty in *; lia.
Qed.

(** Correct count caches suffice for completion on any successor-closed listed graph. *)
Lemma prepared_search_complete_closed g roots :
  counts_ok g ->
  (forall u v, In u (nodes g) -> edge (base g) u v -> In v (nodes g)) ->
  (forall r, In r roots -> In r (nodes g)) ->
  exists es, loopN (search_step (base g)) (search_budget g roots)
    (SearchState (map SearchRoot roots) Empty []) = inr es.
Proof.
  intros Hcounts Hclosed Hroots.
  eapply (loopN_done search_state (list event) (search_step (base g))
    (fun st => Forall (search_task_valid (fun v => In v (nodes g))) (search_tasks st))
    (search_finite_credit (base g) (nodes g))).
  - intros st next Hvalid Hstep. split.
    + eapply search_tasks_preserved; eassumption.
    + eapply search_finite_decreases; eassumption.
  - cbn [search_tasks]. apply Forall_forall. intros task Hin.
    apply in_map_iff in Hin. destruct Hin as [v [Heq Hin]]. subst task. apply Hroots. exact Hin.
  - rewrite search_finite_initial. unfold search_budget. rewrite !N.double_spec.
    destruct Hcounts as [Hnv Hne]. rewrite Hnv, Hne.
    destruct g as [[vertices adjacency] predecessors n e].
    cbn [nodes base graph_n graph_e]. lia.
Qed.

Module SearchCode (V : VISITOR_OPS) <: SEARCH_OPS V.
  Definition dfs (g : prepared) (roots : list positive) (s : V.state) : V.state :=
    fold_events V.enter V.leave V.edge (prepared_search_trace g roots) s.
End SearchCode.

Opaque search_trace.
Local Opaque prepared_search_trace.
Local Opaque loopN.

Module Search (V : VISITOR) <: SEARCH V.
  Include SearchCode V.

  Definition trace (g : prepared) (roots : list positive) := prepared_search_trace g roots.

  Lemma trace_depth_first : forall g roots,
    counts_ok g -> wf_graph (base g) ->
    (forall r, In r roots -> In r (nodes g)) ->
    exists final, dfs_roots (base g) [] roots (trace g roots) final.
  Proof. Admitted. (* CONVERT: GraphSearch: validity premises require the prepared machine proof. *)

  Lemma dfs_fold : forall g roots s,
    counts_ok g -> wf_graph (base g) ->
    (forall r, In r roots -> In r (nodes g)) ->
    dfs g roots s = fold_events V.enter V.leave V.edge (trace g roots) s.
  Proof.
    intros g roots s Hcounts Hgraph Hroots. unfold dfs, trace.
    reflexivity.
  Qed.

  Lemma trace_reach : forall g roots v,
    counts_ok g -> wf_graph (base g) ->
    (forall r, In r roots -> In r (nodes g)) ->
    In v (entered (trace g roots)) <-> reach (base g) roots v.
  Proof. Admitted. (* CONVERT: GraphSearch: validity premises require the prepared machine proof. *)

  Lemma trace_unique : forall g roots,
    counts_ok g -> wf_graph (base g) ->
    (forall r, In r roots -> In r (nodes g)) -> NoDup (entered (trace g roots)).
  Proof. Admitted. (* CONVERT: GraphSearch: validity premises require the prepared machine proof. *)

  Lemma trace_nested : forall g roots,
    counts_ok g -> wf_graph (base g) ->
    (forall r, In r roots -> In r (nodes g)) -> trace_stack [] (trace g roots) [].
  Proof. Admitted. (* CONVERT: GraphSearch: validity premises require the prepared machine proof. *)

  Lemma trace_edges : forall g roots u,
    counts_ok g -> wf_graph (base g) ->
    (forall r, In r roots -> In r (nodes g)) -> reach (base g) roots u ->
    Permutation (edge_targets u (trace g roots)) (succs (base g) u).
  Proof. Admitted. (* CONVERT: GraphSearch: validity premises require the prepared machine proof. *)

  Lemma trace_edges_sound : forall g roots kind u v,
    counts_ok g -> wf_graph (base g) ->
    (forall r, In r roots -> In r (nodes g)) ->
    In (Edge kind u v) (trace g roots) -> reach (base g) roots u /\ edge (base g) u v.
  Proof. Admitted. (* CONVERT: GraphSearch: validity premises require the prepared machine proof. *)

  Lemma trace_kinds : forall g roots prefix kind u v suffix,
    counts_ok g -> wf_graph (base g) ->
    (forall r, In r roots -> In r (nodes g)) ->
    trace g roots = prefix ++ Edge kind u v :: suffix -> event_kind_correct prefix kind v.
  Proof. Admitted. (* CONVERT: GraphSearch: validity premises require the prepared machine proof. *)
End Search.

Module SearchT (V : VISITOR_T) <: SEARCH_ALL V.
  Include Search V.
  TimeFun dfs.
  Definition c_dfs : N := 1%N. (* STUB *)

  Definition n_reach (g : prepared) (roots : list positive) : nat :=
    length (entered (trace g roots)).
  Definition e_reach (g : prepared) (roots : list positive) : nat :=
    fold_right (fun u n => length (succs (base g) u) + n) 0 (entered (trace g roots)).
  Definition run_width (g : prepared) (roots : list positive) : nat :=
    graph_max (vertex_width roots)
      (fold_right (fun u w => graph_max (vertex_width (succs (base g) u)) w) 0
        (entered (trace g roots))).
  Definition work_bounded (g : prepared) (roots : list positive) (s : V.state) (B : nat) :=
    forall prefix suffix, trace g roots = prefix ++ suffix ->
      V.vwork (fold_events V.enter V.leave V.edge prefix s) <= B.

  Lemma T_dfs_le : forall g roots s B, work_bounded g roots s B ->
    (T_dfs g roots s <=
      c_dfs * (N.of_nat (n_reach g roots + e_reach g roots + length roots + 1) *
      (N.of_nat (run_width g roots) + V.c_vis * N.of_nat (B + 1)) +
        N.of_nat (N.size_nat (nv g) + N.size_nat (ne g) + 1)))%N.
  Proof. Admitted. (* STUB *)

  Lemma dfs_bigO : bigO
    (fun '(g, roots, s, B) => work_bounded g roots s B)
    (fun '(g, roots, _, B) =>
      (N.of_nat (n_reach g roots + e_reach g roots + length roots + 1) *
        (N.of_nat (run_width g roots) + V.c_vis * N.of_nat (B + 1)) +
          N.of_nat (N.size_nat (nv g) + N.size_nat (ne g) + 1))%N)
    (fun '(g, roots, s, _) => T_dfs g roots s).
  Proof. Admitted. (* STUB *)

  Definition search_step := search_step.
  TimeFun search_step.
  Definition search_budget := search_budget.
  TimeFun search_budget.
  Definition search_trace := prepared_search_trace.
  TimeFun search_trace.
  Definition k_step : N := 1%N. (* STUB *)
  Definition k_trace : N := 1%N. (* STUB *)
  Definition k_fold : N := 1%N. (* STUB *)
  Definition k_budget : N := 1%N. (* STUB *)

  Definition initial (roots : list positive) : search_state :=
    SearchState (map SearchRoot roots) Empty [].
  Definition advance (g : digraph) (s : search_state) : search_state :=
    match search_step g s with inl next => next | inr _ => s end.
  Definition machine_reachable (g : prepared) roots st : Prop :=
    exists n, Nat.iter n (advance (base g)) (initial roots) = st.
  Definition support (g : prepared) roots := entered (trace g roots).
  Definition unvisited (g : prepared) roots (st : search_state) : nat :=
    fold_right (fun v n =>
      match trie_get v (search_colours st) with
      | None => 2 + length (succs (base g) v) + n
      | Some _ => n
      end) 0 (support g roots).
  Definition pending (st : search_state) : nat :=
    fold_right (fun task n =>
      match task with
      | SearchRoot _ => 1 + n
      | SearchRow _ vs => 2 * length vs + 1 + n
      | SearchLeave _ => 1 + n
      end) 0 (search_tasks st).
  Definition potential g roots st : N := N.of_nat (2 * unvisited g roots st + pending st).
  Definition planned_fuel (g : prepared) : N := (2 * (nv g + ne g) + 1)%N.
  Definition event_width (w : nat) (e : event) : Prop :=
    match e with
    | Enter v | Leave v => Pos.size_nat v <= w
    | Edge _ u v => Pos.size_nat u <= w /\ Pos.size_nat v <= w
    end.
  Definition representation (st : search_state) : Prop :=
    NoDup (entered (rev (search_events st))) /\
    forall v,
      (trie_get v (search_colours st) = None <->
        ~ In (Enter v) (search_events st)) /\
      (trie_get v (search_colours st) = Some true <->
        In (Enter v) (search_events st) /\ ~ In (Leave v) (search_events st)) /\
      (trie_get v (search_colours st) = Some false <->
        In (Leave v) (search_events st)).
  Definition invariant g roots st : Prop :=
    machine_reachable g roots st /\ representation st /\
    exists suffix, trace g roots = rev (search_events st) ++ suffix.
  Definition all_rows (g : digraph) : nat :=
    fold_right (fun entry n => length (snd entry) + n) 0 (PTrieCode.elements (succ g)).
  Definition driver_credit g roots w st :=
    ((k_step * N.of_nat (w + 1) + 1) * potential g roots st)%N.
  Definition stop_budget g roots := (k_trace * N.of_nat (length (trace g roots) + 1))%N.

  Lemma F1_budget : forall g roots,
    search_budget g roots = (4 * (nv g + ne g + N.of_nat (length roots) + 1))%N.
  Proof.
    intros g roots.
    change (N.double (N.double (nv g + ne g + N.of_nat (length roots) + 1)) =
      4 * (nv g + ne g + N.of_nat (length roots) + 1))%N.
    rewrite !N.double_spec. lia.
  Qed.

  Local Transparent prepared_search_trace.

  Lemma F2_trace : forall g roots,
    trace g roots = search_trace g roots /\
    search_trace g roots =
      match loopN (search_step (base g)) (search_budget g roots) (initial roots) with
      | inl st => rev (search_events st)
      | inr es => es
      end.
  Proof.
    intros g roots. split; [reflexivity|].
    unfold search_trace, prepared_search_trace, initial.
    fold search_step search_budget.
    destruct (loopN (search_step (base g)) (search_budget g roots)
      (SearchState (map SearchRoot roots) Empty [])) as [st|es]; [|reflexivity].
    rewrite rev_append_rev, app_nil_r. reflexivity.
  Qed.

  Local Opaque prepared_search_trace.

  Lemma F3_initial : forall g roots,
    counts_ok g -> wf_graph (base g) ->
    (forall r, In r roots -> In r (nodes g)) ->
    invariant g roots (initial roots) /\
    potential g roots (initial roots) =
      N.of_nat (4 * n_reach g roots + 2 * e_reach g roots + length roots).
  Proof. Admitted. (* STUB *)

  Lemma F4_step : forall g roots st next,
    counts_ok g -> wf_graph (base g) ->
    (forall r, In r roots -> In r (nodes g)) ->
    invariant g roots st -> search_step (base g) st = inl next ->
    invariant g roots next /\ (potential g roots next < potential g roots st)%N.
  Proof. Admitted. (* STUB *)

  Lemma F5_stop : forall g roots st es,
    counts_ok g -> wf_graph (base g) ->
    (forall r, In r roots -> In r (nodes g)) ->
    invariant g roots st -> search_step (base g) st = inr es ->
    search_tasks st = [] /\ es = trace g roots.
  Proof. Admitted. (* STUB *)

  Lemma F6_width : forall g roots st,
    counts_ok g -> wf_graph (base g) ->
    (forall r, In r roots -> In r (nodes g)) ->
    invariant g roots st -> Forall (event_width (run_width g roots)) (search_events st).
  Proof. Admitted. (* STUB *)

  Lemma F7_events : forall g roots,
    counts_ok g -> wf_graph (base g) ->
    (forall r, In r roots -> In r (nodes g)) ->
    length (trace g roots) = 2 * n_reach g roots + e_reach g roots.
  Proof. Admitted. (* STUB *)

  Lemma F8_fuel : forall g roots,
    counts_ok g -> wf_graph (base g) ->
    (forall r, In r roots -> In r (nodes g)) ->
    exists es, loopN (search_step (base g)) (search_budget g roots)
      (initial roots) = inr es.
  Proof.
    intros [[vertices adjacency] predecessors n e] roots Hcounts Hgraph Hroots.
    apply prepared_search_complete_closed; [exact Hcounts| |exact Hroots].
    exact (proj2 Hgraph).
  Qed.

  Lemma T1_step : forall g roots st next w,
    counts_ok g -> wf_graph (base g) ->
    (forall r, In r roots -> In r (nodes g)) ->
    invariant g roots st -> Forall (event_width w) (trace g roots) ->
    vertex_width roots <= w -> search_step (base g) st = inl next ->
    (T_search_step (base g) st <= k_step * N.of_nat (w + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T2_stop : forall g roots st es,
    counts_ok g -> wf_graph (base g) ->
    (forall r, In r roots -> In r (nodes g)) ->
    invariant g roots st -> search_step (base g) st = inr es ->
    (T_search_step (base g) st <= stop_budget g roots)%N.
  Proof. Admitted. (* STUB *)

  Lemma T3_loop : forall g roots w,
    counts_ok g -> wf_graph (base g) ->
    (forall r, In r roots -> In r (nodes g)) ->
    Forall (event_width w) (trace g roots) -> vertex_width roots <= w ->
    (T_loopN (search_step (base g)) (T_search_step (base g))
      (search_budget g roots) (initial roots) <=
    c_loopN * (driver_credit g roots w (initial roots) + stop_budget g roots +
      N.of_nat (N.size_nat (search_budget g roots)) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T4_trace : forall g roots w,
    counts_ok g -> wf_graph (base g) ->
    (forall r, In r roots -> In r (nodes g)) ->
    Forall (event_width w) (trace g roots) -> vertex_width roots <= w ->
    (T_search_trace g roots <= k_trace *
      (T_search_budget g roots + N.of_nat (length roots) +
        T_loopN (search_step (base g)) (T_search_step (base g))
          (search_budget g roots) (initial roots) +
        N.of_nat (length (trace g roots)) + 1))%N.
  Proof. Admitted. (* STUB *)

  (** A continuing step taken within the fuel costs one key width of the run. *)
  Lemma T1_raw_step : forall g roots n st next,
    (N.of_nat n < search_budget g roots)%N ->
    Nat.iter n (advance (base g)) (initial roots) = st ->
    search_step (base g) st = inl next ->
    (T_search_step (base g) st <= k_step * N.of_nat (run_width g roots + 1))%N.
  Proof. Admitted. (* STUB *)

  (** Steps taken within the fuel emit an event, retire a root or finish a row. *)
  Lemma F9_raw_count : forall g roots n,
    (N.of_nat n <= search_budget g roots)%N ->
    (forall i, i < n -> exists next,
      search_step (base g) (Nat.iter i (advance (base g)) (initial roots)) = inl next) ->
    n <= length (trace g roots) + length roots + n_reach g roots.
  Proof. Admitted. (* STUB *)

  (** The truncated loop pays its steps, one stop and the binary fuel width. *)
  Lemma T3_raw_loop : forall g roots,
    (T_loopN (search_step (base g)) (T_search_step (base g))
      (search_budget g roots) (initial roots) <=
    c_loopN * (k_step * N.of_nat (run_width g roots + 1) *
      N.of_nat (length (trace g roots) + length roots + n_reach g roots + 1) +
      stop_budget g roots + N.of_nat (N.size_nat (search_budget g roots)) + 1))%N.
  Proof. Admitted. (* STUB *)

  (** Every step emits an event or retires a root or row task, at the width of the run. *)
  Lemma T4_raw : forall g roots,
    (T_search_trace g roots <= k_trace *
      (N.of_nat (n_reach g roots + e_reach g roots + length roots + 1) *
        N.of_nat (run_width g roots + 1) +
       N.of_nat (N.size_nat (nv g) + N.size_nat (ne g) + 1)))%N.
  Proof. Admitted. (* STUB *)

  Lemma T5_fold : forall g roots s B,
    work_bounded g roots s B ->
    (T_fold_events V.enter V.T_enter V.leave V.T_leave V.edge V.T_edge
      (trace g roots) s <=
    k_fold * N.of_nat (length (trace g roots) + 1) *
      (V.c_vis * N.of_nat (B + 1) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T6_dfs : forall g roots s,
    (T_dfs g roots s <= k_trace * (T_search_trace g roots +
      T_fold_events V.enter V.T_enter V.leave V.T_leave V.edge V.T_edge
        (trace g roots) s + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T7_public : forall g roots s B, work_bounded g roots s B ->
    (T_dfs g roots s <= c_dfs * (N.of_nat (n_reach g roots + e_reach g roots + length roots + 1) *
      (N.of_nat (run_width g roots) + V.c_vis * N.of_nat (B + 1)) +
        N.of_nat (N.size_nat (nv g) + N.size_nat (ne g) + 1)))%N.
  Proof. Admitted. (* STUB *)

  (** Each entered vertex contributes at most two events and its row on every input. *)
  Lemma F7b_events_raw : forall g roots,
      length (trace g roots) <= 2 * n_reach g roots + e_reach g roots.
  Proof. Admitted. (* STUB *)

End SearchT.

Transparent search_trace.
Transparent prepared_search_trace.
Transparent loopN.
