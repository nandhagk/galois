(** * Strongly connected components

    Tarjan's visitor tracks discovery numbers and pending components.
    For example, closing a cycle root emits its pending vertices together.
    Builds on: depth-first search and the SCC signature. *)

From Stdlib Require Import List NArith PArith Sorting.Permutation.
From Argent Require Import Time Tactics Std BigO.
From Galois.Base Require Import Trie.
From Galois.Graph Require Import Data Spec DigraphSig SearchSig Search SccSig.
Import List.ListNotations.

Module Pos.
  TimeFun Pos.min.
End Pos.

Definition tarjan_initial := TarjanState Empty Empty [] Empty [] [] Empty 1%positive 1%positive.
TimeFun tarjan_initial.

Fixpoint tarjan_pop (root index : positive) (pending : list positive)
    (low : ptrie positive) (active : ptrie bool) (owners : ptrie positive)
    : list positive * list positive * ptrie positive * ptrie bool * ptrie positive :=
  match pending with
  | [] => ([], [], low, active, owners)
  | v :: rest =>
    let low' := PTrieCode.remove v low in
    let active' := PTrieCode.remove v active in
    let owners' := PTrieCode.set v index owners in
    if Pos.eqb v root then ([v], rest, low', active', owners') else
    let '(members, tail, low'', active'', owners'') :=
      tarjan_pop root index rest low' active' owners' in
    (v :: members, tail, low'', active'', owners'')
  end.
TimeFun tarjan_pop.

Module TarjanVisitor <: VISITOR_OPS.
  Definition state := tarjan_state.

  Definition enter (v : positive) (s : state) : state :=
    TarjanState (PTrieCode.set v (tarjan_clock s) (tarjan_disc s))
      (PTrieCode.set v (tarjan_clock s) (tarjan_low s)) (v :: tarjan_pending s)
      (PTrieCode.set v true (tarjan_active s)) (v :: tarjan_frames s)
      (tarjan_emitted s) (tarjan_owners s) (Pos.succ (tarjan_clock s)) (tarjan_next s).
  TimeFun enter.

  Definition lower (v n : positive) (s : state) : state :=
    match trie_get v (tarjan_low s) with
    | None => s
    | Some old => TarjanState (tarjan_disc s) (PTrieCode.set v (Pos.min old n) (tarjan_low s))
        (tarjan_pending s) (tarjan_active s) (tarjan_frames s) (tarjan_emitted s)
        (tarjan_owners s) (tarjan_clock s) (tarjan_next s)
    end.
  TimeFun lower.

  Definition edge (kind : edge_kind) (u v : positive) (s : state) : state :=
    match kind with
    | Tree => s
    | _ => match trie_get v (tarjan_active s), trie_get v (tarjan_disc s) with
           | Some true, Some n => lower u n s
           | _, _ => s
           end
    end.
  TimeFun edge.

  Definition leave (v : positive) (s : state) : state :=
    let frames := match tarjan_frames s with [] => [] | _ :: rest => rest end in
    let s' := TarjanState (tarjan_disc s) (tarjan_low s) (tarjan_pending s)
      (tarjan_active s) frames (tarjan_emitted s) (tarjan_owners s)
      (tarjan_clock s) (tarjan_next s) in
    match trie_get v (tarjan_low s), trie_get v (tarjan_disc s) with
    | Some l, Some d =>
      if Pos.eqb l d then
        let '(members, tail, low, active, owners) :=
          tarjan_pop v (tarjan_next s) (tarjan_pending s) (tarjan_low s)
            (tarjan_active s) (tarjan_owners s) in
        TarjanState (tarjan_disc s) low tail active frames
          (members :: tarjan_emitted s) owners (tarjan_clock s) (Pos.succ (tarjan_next s))
      else match frames with [] => s' | parent :: _ => lower parent l s' end
    | _, _ => s'
    end.
  TimeFun leave.
End TarjanVisitor.

Module TarjanSearchCode := SearchCode TarjanVisitor.
Module TarjanSearch.
  Include TarjanSearchCode.
  TimeFun dfs.
End TarjanSearch.

(** Rebuild the search graph from listed rows and exclude every unlisted successor. *)
Definition scc_graph (g : prepared) : prepared :=
  let vs := nodes g in
  let listed := fold_left (fun acc v => PTrieCode.set v true acc) vs Empty in
  let rows := fold_left (fun acc v => PTrieCode.set v
    (filter (fun u => match trie_get u listed with Some _ => true | None => false end)
      (succs (base g) v)) acc) vs Empty in
  let b := Digraph vs rows in
  Prepared b Empty (N.of_nat (graph_n b)) (N.of_nat (graph_e b)).
TimeFun scc_graph.

(** The filtered traversal reads neither predecessor nor count caches of its input. *)
Definition scc_trace (g : prepared) : list event :=
  let ready := scc_graph g in
  prepared_search_trace ready (nodes ready).
TimeFun scc_trace.

Module SccCode <: SCC_OPS.
  Definition run (g : prepared) : scc :=
    let result := fold_events TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge
      (scc_trace g) tarjan_initial in
    Scc (tarjan_owners result) (rev (tarjan_emitted result)).
End SccCode.

Opaque search_trace.

Module Scc <: SCC.
  Include SccCode.
  Include SCC_SPEC.

  Lemma comp_spec : forall g, wf_graph (base g) -> forall u v,
    (exists i, trie_get u (comp (run g)) = Some i /\
      trie_get v (comp (run g)) = Some i) <->
    In u (nodes g) /\ In v (nodes g) /\ mutually_reachable (base g) u v.
  Proof. Admitted. (* CONVERT: GraphTarjan: filtered traversal requires the scoped proof. *)

  Lemma comps_partition : forall g, wf_graph (base g) ->
    NoDup (concat (comps (run g))) /\
    (forall v, In v (concat (comps (run g))) <-> In v (nodes g)).
  Proof. Admitted. (* CONVERT: GraphTarjan: filtered traversal requires the scoped proof. *)

  Lemma comps_nonempty : forall g, wf_graph (base g) ->
    Forall (fun vs => vs <> []) (comps (run g)).
  Proof. Admitted. (* CONVERT: GraphTarjan: filtered traversal requires the scoped proof. *)

  Lemma owners_spec : forall g, wf_graph (base g) -> forall v i,
    trie_get v (comp (run g)) = Some i <->
    exists vs, nth_error (comps (run g)) (Nat.pred (Pos.to_nat i)) = Some vs /\ In v vs.
  Proof. Admitted. (* CONVERT: GraphTarjan: filtered traversal requires the scoped proof. *)

  Lemma comps_order : forall g, wf_graph (base g) -> forall u v i j,
    edge (base g) u v -> trie_get u (comp (run g)) = Some i ->
    trie_get v (comp (run g)) = Some j -> (j <= i)%positive.
  Proof. Admitted. (* CONVERT: GraphTarjan: filtered traversal requires the scoped proof. *)
End Scc.

Transparent search_trace.

Module SccT <: SCC_ALL.
  Include Scc.
  TimeFun run.
  Definition c_scc : N := 1%N. (* STUB *)

  Lemma T_run_le : forall g,
    (T_run g <= c_scc * N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma run_bigO : bigO (fun _ => True)
    (fun g => N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
      (graph_width (base g) + 1))) T_run.
  Proof. Admitted. (* STUB *)

  Definition tarjan_initial := tarjan_initial.
  Definition tarjan_enter := TarjanVisitor.enter.
  TimeFun tarjan_enter.
  Definition tarjan_leave := TarjanVisitor.leave.
  TimeFun tarjan_leave.
  Definition tarjan_edge := TarjanVisitor.edge.
  TimeFun tarjan_edge.
  Definition tarjan_pop := tarjan_pop.
  TimeFun tarjan_pop.
  Definition tarjan_trace := scc_trace.
  TimeFun tarjan_trace.
  Definition k_pop : N := 1%N. (* STUB *)
  Definition k_callback : N := 1%N. (* STUB *)
  Definition k_result : N := 1%N. (* STUB *)
  Definition k_search : N := 1%N. (* STUB *)

  Definition apply_event (s : tarjan_state) (e : event) : tarjan_state :=
    visit_event tarjan_enter tarjan_leave tarjan_edge s e.
  Definition callback_cost (e : event) (s : tarjan_state) : N :=
    match e with
    | Enter v => T_tarjan_enter v s
    | Leave v => T_tarjan_leave v s
    | Edge kind u v => T_tarjan_edge kind u v s
    end.
  Definition prefix_state (es : list event) : tarjan_state :=
    fold_events tarjan_enter tarjan_leave tarjan_edge es tarjan_initial.
  Definition pop_unit (w : nat) := (k_pop * N.of_nat (w + 1))%N.
  Definition potential (w : nat) (s : tarjan_state) : N :=
    (pop_unit w * N.of_nat (length (tarjan_pending s)) +
      k_result * N.of_nat (length (tarjan_emitted s)))%N.
  Definition event_domain (w : nat) (e : event) : Prop :=
    match e with
    | Enter v | Leave v => Pos.size_nat v <= w
    | Edge _ u v => Pos.size_nat u <= w /\ Pos.size_nat v <= w
    end.
  Definition width_domain (w : nat) (s : tarjan_state) : Prop :=
    Forall (fun v => Pos.size_nat v <= w) (tarjan_pending s) /\
    Forall (fun v => Pos.size_nat v <= w) (tarjan_frames s) /\
    Pos.size_nat (tarjan_clock s) <= w + 1 /\
    Pos.size_nat (tarjan_next s) <= w + 1 /\
    (forall v i, trie_get v (tarjan_disc s) = Some i -> Pos.size_nat i <= w + 1) /\
    (forall v i, trie_get v (tarjan_low s) = Some i -> Pos.size_nat i <= w + 1).
  Definition inventory (prefix : list event) (s : tarjan_state) : Prop :=
    NoDup (tarjan_pending s ++ concat (tarjan_emitted s)) /\
    Permutation (tarjan_pending s ++ concat (tarjan_emitted s)) (entered prefix) /\
    incl (tarjan_frames s) (tarjan_pending s) /\
    tarjan_clock s = Pos.of_succ_nat (length (entered prefix)) /\
    tarjan_next s = Pos.of_succ_nat (length (tarjan_emitted s)) /\
    (forall v, trie_get v (tarjan_active s) = Some true <-> In v (tarjan_pending s)) /\
    (forall v, (exists i, trie_get v (tarjan_low s) = Some i) <->
      In v (tarjan_pending s)) /\
    (forall v i, trie_get v (tarjan_disc s) = Some i <->
      exists n, nth_error (entered prefix) n = Some v /\ i = Pos.of_succ_nat n).
  Definition emitted_closed (g : digraph) (s : tarjan_state) : Prop :=
    Forall (fun block => block <> [] /\
      (forall u v, In u block -> In v block -> mutually_reachable g u v) /\
      (forall u v, In u block -> edge g u v -> In v (concat (tarjan_emitted s))))
      (tarjan_emitted s).
  Definition invariant g prefix s : Prop :=
    s = prefix_state prefix /\ inventory prefix s /\
    width_domain (graph_width (base g)) s /\ emitted_closed (base g) s.

  Lemma F1_trace : forall g, wf_graph (base g) ->
    NoDup (entered (tarjan_trace g)) /\
    (forall v, In v (entered (tarjan_trace g)) <-> In v (nodes g)) /\
    trace_stack [] (tarjan_trace g) [] /\
    length (tarjan_trace g) = 2 * graph_n (base g) + graph_e (base g).
  Proof. Admitted. (* STUB *)

  (** The filtered traversal is nested, duplicate-free and graph-sized on every input. *)
  Lemma F1b_trace_size : forall g,
    NoDup (entered (tarjan_trace g)) /\
    (forall v, In v (entered (tarjan_trace g)) -> In v (nodes g)) /\
    trace_stack [] (tarjan_trace g) [] /\
    length (tarjan_trace g) <= 2 * graph_n (base g) + graph_e (base g).
  Proof. Admitted. (* STUB *)

  Lemma F2_run : forall g,
    run g = let result := prefix_state (tarjan_trace g) in
      Scc (tarjan_owners result) (rev (tarjan_emitted result)).
  Proof. Admitted. (* STUB *)

  Lemma F3_initial : forall g,
    invariant g [] tarjan_initial /\
    potential (graph_width (base g)) tarjan_initial = 0%N.
  Proof. Admitted. (* STUB *)

  Lemma F4_prefix : forall g prefix suffix,
    wf_graph (base g) -> tarjan_trace g = prefix ++ suffix ->
    invariant g prefix (prefix_state prefix).
  Proof. Admitted. (* STUB *)

  (** Actual prefixes keep the inventory and widths that the cost proof reads. *)
  Lemma F4b_prefix_cost : forall g prefix suffix,
    tarjan_trace g = prefix ++ suffix ->
    inventory prefix (prefix_state prefix) /\
    width_domain (graph_width (base g)) (prefix_state prefix).
  Proof. Admitted. (* STUB *)

  Lemma F5_pop : forall root index pending low active owners members tail low' active' owners',
    tarjan_pop root index pending low active owners =
      (members, tail, low', active', owners') ->
    pending = members ++ tail /\
    (forall v, In v members -> trie_get v low' = None /\
      trie_get v active' = None /\ trie_get v owners' = Some index).
  Proof. Admitted. (* STUB *)

  Lemma F6_final : forall g, wf_graph (base g) ->
    let result := prefix_state (tarjan_trace g) in
    tarjan_pending result = [] /\ tarjan_frames result = [] /\
    forall v i, trie_get v (tarjan_owners result) = Some i <->
      exists block, nth_error (rev (tarjan_emitted result))
        (Nat.pred (Pos.to_nat i)) = Some block /\ In v block.
  Proof. Admitted. (* STUB *)

  Lemma F7_components : forall g, wf_graph (base g) -> forall u v,
    (exists i, trie_get u (comp (run g)) = Some i /\ trie_get v (comp (run g)) = Some i) <->
    In u (nodes g) /\ In v (nodes g) /\ mutually_reachable (base g) u v.
  Proof. Admitted. (* STUB *)

  Lemma T1_pop : forall w root index pending low active owners members tail low' active' owners',
    Forall (fun v => Pos.size_nat v <= w) pending ->
    Pos.size_nat root <= w -> Pos.size_nat index <= w + 1 ->
    tarjan_pop root index pending low active owners = (members, tail, low', active', owners') ->
    (T_tarjan_pop root index pending low active owners + pop_unit w * N.of_nat (length tail) <=
      pop_unit w * N.of_nat (length pending) + k_pop * N.of_nat (w + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T2_callback : forall g prefix e suffix,
    tarjan_trace g = prefix ++ e :: suffix ->
    let w := graph_width (base g) in
    let s := prefix_state prefix in
    (callback_cost e s + potential w (apply_event s e) <=
      k_callback * N.of_nat (w + 1) + potential w s)%N.
  Proof. Admitted. (* STUB *)

  Lemma T3_fold : forall g,
    (T_fold_events tarjan_enter T_tarjan_enter tarjan_leave T_tarjan_leave
      tarjan_edge T_tarjan_edge (tarjan_trace g) tarjan_initial +
      potential (graph_width (base g)) (prefix_state (tarjan_trace g)) <=
    k_callback * N.of_nat (length (tarjan_trace g) + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T4_trace : forall g,
    (T_tarjan_trace g <= k_search * N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T5_wrapper : forall g,
    (T_run g <= k_result * (T_tarjan_trace g +
      T_fold_events tarjan_enter T_tarjan_enter tarjan_leave T_tarjan_leave
        tarjan_edge T_tarjan_edge (tarjan_trace g) tarjan_initial +
      N.of_nat (length (tarjan_emitted (prefix_state (tarjan_trace g)))) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T6_public : forall g,
    (T_run g <= c_scc * N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
  Proof. Admitted. (* STUB *)
End SccT.
