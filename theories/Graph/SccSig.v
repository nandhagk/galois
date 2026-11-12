(** * Strongly connected component signatures

    Components partition the listed graph vertices in reverse topological order.
    For example, two vertices joined in both directions have the same present owner.
    Builds on: graph semantics, trie data and preparation measures. *)

From Stdlib Require Import PArith NArith List Sorting.Permutation.
From Argent Require Import Time BigO.
From Galois.Base Require Import Trie.
From Galois.Graph Require Import Data Spec DigraphSig SearchSig.
Import List.ListNotations.

(** Mutual reachability permits zero-edge paths at each endpoint. *)
Definition mutually_reachable (g : digraph) (u v : positive) : Prop :=
  (exists vs, path g u vs v) /\ (exists vs, path g v vs u).

Record tarjan_state := TarjanState {
  tarjan_disc : ptrie positive;
  tarjan_low : ptrie positive;
  tarjan_pending : list positive;
  tarjan_active : ptrie bool;
  tarjan_frames : list positive;
  tarjan_emitted : list (list positive);
  tarjan_owners : ptrie positive;
  tarjan_clock : positive;
  tarjan_next : positive
}.

TimeFun tarjan_disc.
TimeFun tarjan_low.
TimeFun tarjan_pending.
TimeFun tarjan_active.
TimeFun tarjan_frames.
TimeFun tarjan_emitted.
TimeFun tarjan_owners.
TimeFun tarjan_clock.
TimeFun tarjan_next.

Module Type SCC_OPS.
  Parameter run : prepared -> scc.
End SCC_OPS.

Module Type SCC_SPEC (Import S : SCC_OPS).
  (** A shared component requires a present owner for both endpoints. *)
  Definition same_component (g : prepared) (u v : positive) : Prop :=
    exists i, trie_get u (comp (run g)) = Some i /\ trie_get v (comp (run g)) = Some i.
End SCC_SPEC.

Module Type SCC_LAWS (Import S : SCC_OPS).
  (** Equal present owners characterize mutual reachability of listed vertices. *)
  Parameter comp_spec : forall g, wf_graph (base g) -> forall u v,
    (exists i, trie_get u (comp (run g)) = Some i /\
      trie_get v (comp (run g)) = Some i) <->
    In u (nodes g) /\ In v (nodes g) /\ mutually_reachable (base g) u v.
  (** Component lists contain each listed vertex once. *)
  Parameter comps_partition : forall g, wf_graph (base g) ->
    NoDup (concat (comps (run g))) /\
    (forall v, In v (concat (comps (run g))) <-> In v (nodes g)).
  (** Every emitted component has a member. *)
  Parameter comps_nonempty : forall g, wf_graph (base g) ->
    Forall (fun vs => vs <> []) (comps (run g)).
  (** Owner indices are one-based positions in the component list. *)
  Parameter owners_spec : forall g, wf_graph (base g) -> forall v i,
    trie_get v (comp (run g)) = Some i <->
    exists vs, nth_error (comps (run g)) (Nat.pred (Pos.to_nat i)) = Some vs /\ In v vs.
  (** Every edge stays in its component or targets an earlier component. *)
  Parameter comps_order : forall g, wf_graph (base g) -> forall u v i j,
    edge (base g) u v -> trie_get u (comp (run g)) = Some i ->
    trie_get v (comp (run g)) = Some j -> (j <= i)%positive.
End SCC_LAWS.

Module Type SCC := SCC_OPS <+ SCC_SPEC <+ SCC_LAWS.

Module Type SCC_TIME (Import S : SCC).
  Parameter T_run : prepared -> N.
  Parameter c_scc : N.
  (** SCC computation charges graph vertices, successor occurrences and identifier bits. *)
  Parameter T_run_le : forall g,
    (T_run g <= c_scc * N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
  (** SCC computation has the published linear bit-cost bound. *)
  Parameter run_bigO : bigO (fun _ => True)
    (fun g => N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
      (graph_width (base g) + 1))) T_run.
End SCC_TIME.

Module Type SCC_T := SCC <+ SCC_TIME.

(** * Tarjan proof plan

    [GraphTarjanCost] at [87192fe] pays pops from pending-cell credit and pays
    final reversal from emitted-component credit. The current callback also
    propagates through [tarjan_frames], so its domain includes frame keys.
    The amortised chain uses actual event prefixes and does not require a
    constant worst-case cost for a component-closing callback. *)

Module Type SCC_PLAN (Import S : SCC_T).
  Parameter tarjan_initial : tarjan_state.
  Parameter tarjan_enter tarjan_leave : positive -> tarjan_state -> tarjan_state.
  Parameter tarjan_edge : edge_kind -> positive -> positive -> tarjan_state -> tarjan_state.
  Parameter tarjan_pop : positive -> positive -> list positive -> ptrie positive ->
    ptrie bool -> ptrie positive ->
    list positive * list positive * ptrie positive * ptrie bool * ptrie positive.
  Parameter tarjan_trace : prepared -> list event.
  Parameter T_tarjan_enter T_tarjan_leave : positive -> tarjan_state -> N.
  Parameter T_tarjan_edge : edge_kind -> positive -> positive -> tarjan_state -> N.
  Parameter T_tarjan_pop : positive -> positive -> list positive -> ptrie positive ->
    ptrie bool -> ptrie positive -> N.
  Parameter T_tarjan_trace : prepared -> N.
  Parameter k_pop k_callback k_result k_search : N.

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

  (** Pending cells reserve removal, owner insertion and equality work for a future pop. *)
  Definition potential (w : nat) (s : tarjan_state) : N :=
    (pop_unit w * N.of_nat (length (tarjan_pending s)) +
      k_result * N.of_nat (length (tarjan_emitted s)))%N.

  Definition event_domain (w : nat) (e : event) : Prop :=
    match e with
    | Enter v | Leave v => Pos.size_nat v <= w
    | Edge _ u v => Pos.size_nat u <= w /\ Pos.size_nat v <= w
    end.

  (** Counter widths include the next unused discovery and owner indices. *)
  Definition width_domain (w : nat) (s : tarjan_state) : Prop :=
    Forall (fun v => Pos.size_nat v <= w) (tarjan_pending s) /\
    Forall (fun v => Pos.size_nat v <= w) (tarjan_frames s) /\
    Pos.size_nat (tarjan_clock s) <= w + 1 /\
    Pos.size_nat (tarjan_next s) <= w + 1 /\
    (forall v i, trie_get v (tarjan_disc s) = Some i -> Pos.size_nat i <= w + 1) /\
    (forall v i, trie_get v (tarjan_low s) = Some i -> Pos.size_nat i <= w + 1).

  (** The pending stack and emitted blocks partition the discovered vertices. *)
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

  (** Emitted blocks contain mutually reachable vertices and cannot point to pending vertices. *)
  Definition emitted_closed (g : digraph) (s : tarjan_state) : Prop :=
    Forall (fun block => block <> [] /\
      (forall u v, In u block -> In v block -> mutually_reachable g u v) /\
      (forall u v, In u block -> edge g u v ->
        In v (concat (tarjan_emitted s)))) (tarjan_emitted s).

  (** Actual prefix states carry inventory, finite-width and emitted-block facts. *)
  Definition invariant g prefix s : Prop :=
    s = prefix_state prefix /\ inventory prefix s /\
    width_domain (graph_width (base g)) s /\ emitted_closed (base g) s.

  (** The actual search trace visits the listed vertices and all their successor occurrences. *)
  Parameter F1_trace : forall g, wf_graph (base g) ->
    NoDup (entered (tarjan_trace g)) /\
    (forall v, In v (entered (tarjan_trace g)) <-> In v (nodes g)) /\
    trace_stack [] (tarjan_trace g) [] /\
    length (tarjan_trace g) = 2 * graph_n (base g) + graph_e (base g).

  (** The wrapper returns the owner map and reverses emitted blocks from the final state. *)
  Parameter F2_run : forall g,
    run g = let result := prefix_state (tarjan_trace g) in
      Scc (tarjan_owners result) (rev (tarjan_emitted result)).

  (** Empty maps and stacks start the prefix induction without reserved work. *)
  Parameter F3_initial : forall g,
    invariant g [] tarjan_initial /\ potential (graph_width (base g)) tarjan_initial = 0%N.

  (** Each actual event maintains the inventory and width facts used by the cost proof. *)
  Parameter F4_prefix : forall g prefix suffix,
    wf_graph (base g) -> tarjan_trace g = prefix ++ suffix ->
    invariant g prefix (prefix_state prefix).

  (** Popping consumes an ordered prefix and updates every consumed owner once. *)
  Parameter F5_pop : forall root index pending low active owners members tail low' active' owners',
    tarjan_pop root index pending low active owners = (members, tail, low', active', owners') ->
    pending = members ++ tail /\
    (forall v, In v members -> trie_get v low' = None /\
      trie_get v active' = None /\ trie_get v owners' = Some index).

  (** Completed traversal leaves no pending vertex and assigns every emitted owner index. *)
  Parameter F6_final : forall g, wf_graph (base g) ->
    let result := prefix_state (tarjan_trace g) in
    tarjan_pending result = [] /\ tarjan_frames result = [] /\
    forall v i, trie_get v (tarjan_owners result) = Some i <->
      exists block, nth_error (rev (tarjan_emitted result))
        (Nat.pred (Pos.to_nat i)) = Some block /\ In v block.

  (** Distinct closed emitted blocks are maximal mutual-reachability classes. *)
  Parameter F7_components : forall g, wf_graph (base g) -> forall u v,
    (exists i, trie_get u (comp (run g)) = Some i /\
      trie_get v (comp (run g)) = Some i) <->
    In u (nodes g) /\ In v (nodes g) /\ mutually_reachable (base g) u v.

  (** Pop credit pays the consumed cells and retains the tail's credit. *)
  Parameter T1_pop : forall w root index pending low active owners
      members tail low' active' owners',
    Forall (fun v => Pos.size_nat v <= w) pending ->
    Pos.size_nat root <= w -> Pos.size_nat index <= w + 1 ->
    tarjan_pop root index pending low active owners = (members, tail, low', active', owners') ->
    (T_tarjan_pop root index pending low active owners + pop_unit w * N.of_nat (length tail) <=
      pop_unit w * N.of_nat (length pending) + k_pop * N.of_nat (w + 1))%N.

  (** Actual callbacks transfer pending-cell credit and emitted-reversal credit. *)
  Parameter T2_callback : forall g prefix e suffix,
    wf_graph (base g) -> tarjan_trace g = prefix ++ e :: suffix ->
    let w := graph_width (base g) in
    let s := prefix_state prefix in
    (callback_cost e s + potential w (apply_event s e) <=
      k_callback * N.of_nat (w + 1) + potential w s)%N.

  (** Folding telescopes actual callback credits across the complete search trace. *)
  Parameter T3_fold : forall g, wf_graph (base g) ->
    (T_fold_events tarjan_enter T_tarjan_enter tarjan_leave T_tarjan_leave
      tarjan_edge T_tarjan_edge (tarjan_trace g) tarjan_initial +
      potential (graph_width (base g)) (prefix_state (tarjan_trace g)) <=
    k_callback * N.of_nat (length (tarjan_trace g) + 1) * N.of_nat (graph_width (base g) + 1))%N.

  (** Trace construction retains the concrete Search driver's cost. *)
  Parameter T4_trace : forall g,
    (T_tarjan_trace g <= k_search * N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
      N.of_nat (graph_width (base g) + 1))%N.

  (** The wrapper pays final reversal from the retained emitted-block potential. *)
  Parameter T5_wrapper : forall g,
    (T_run g <= k_result * (T_tarjan_trace g +
      T_fold_events tarjan_enter T_tarjan_enter tarjan_leave T_tarjan_leave
        tarjan_edge T_tarjan_edge (tarjan_trace g) tarjan_initial +
      N.of_nat (length (tarjan_emitted (prefix_state (tarjan_trace g)))) + 1))%N.

  (** The unrestricted target needs raw-graph accounting beyond well-formed runs. *)
  Parameter T6_public : forall g,
    (T_run g <= c_scc * N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
End SCC_PLAN.

Module Type SCC_ALL := SCC_T <+ SCC_PLAN.
