(** * Costed explicit-stack search

    Search examines prepared adjacency in order and dispatches scoped DFS events to a visitor.
    For example, a second labelled edge to a finished child produces a forward event.
    Builds on: GraphPrepared, GraphVisitor, GraphSearchSpec and CostLoop. *)

From Stdlib Require Import List Bool PArith NArith Lia.
From Galois.Cost Require Import CostMonad CostList CostLoop.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor GraphSearchSpec.
Import List.ListNotations Cost.Notations.

Module SearchRun.

(** Orders accumulate backwards and clocks are the next one-based ranks. *)
Record core (E : Type) := Core {
  pre_rev : list positive;
  post_rev : list positive;
  parents : Map.t positive (E * positive);
  pre_index : Map.t positive positive;
  post_index : Map.t positive positive;
  seen : FinSet.t positive;
  pre_clock : positive;
  post_clock : positive
}.
Arguments Core {E}.
Arguments pre_rev {E}.
Arguments post_rev {E}.
Arguments parents {E}.
Arguments pre_index {E}.
Arguments post_index {E}.
Arguments seen {E}.
Arguments pre_clock {E}.
Arguments post_clock {E}.

Definition initial {E} : core E :=
  Core [] [] Map.empty Map.empty Map.empty FinSet.empty 1%positive 1%positive.

(** A frame stores the current ID and its unread labelled successor pairs. *)
Definition frame E := (positive * list (E * positive))%type.
Definition work E := (list (frame E) * core E)%type.

Definition discover_c {E} v (via : option (E * positive)) (c : core E) :=
  Cost.step ;;
  let* parent :=
    match via with
    | None => Cost.ret (parents c)
    | Some edge => Map.set_c positive_encoding v edge (parents c)
    end in
  let* pre := Map.set_c positive_encoding v (pre_clock c) (pre_index c) in
  let* visited := FinSet.add_c positive_encoding v (seen c) in
  Cost.ret (Core (v :: pre_rev c) (post_rev c) parent pre (post_index c) visited
    (Pos.succ (pre_clock c)) (post_clock c)).

Definition discover {E} v via (c : core E) := Cost.value (discover_c v via c).

Definition finish_c {E} v (c : core E) :=
  Cost.step ;;
  let* post := Map.set_c positive_encoding v (post_clock c) (post_index c) in
  Cost.ret (Core (pre_rev c) (v :: post_rev c) (parents c) (pre_index c) post (seen c)
    (pre_clock c) (Pos.succ (post_clock c))).

Definition finish {E} v (c : core E) := Cost.value (finish_c v c).

(** Discovery retains the selected labelled parent and increments only the entry clock. *)
Theorem discover_equation {E} v via (c : core E) :
  discover v via c =
    Core (v :: pre_rev c) (post_rev c)
      (match via with
      | None => parents c
      | Some edge => Map.set positive_encoding v edge (parents c)
      end)
      (Map.set positive_encoding v (pre_clock c) (pre_index c)) (post_index c)
      (FinSet.add positive_encoding v (seen c)) (Pos.succ (pre_clock c)) (post_clock c).
Proof.
  destruct via; reflexivity.
Qed.

(** Finishing records the next exit rank and leaves discovery data unchanged. *)
Theorem finish_equation {E} v (c : core E) :
  finish v c =
    Core (pre_rev c) (v :: post_rev c) (parents c) (pre_index c)
      (Map.set positive_encoding v (post_clock c) (post_index c)) (seen c)
      (pre_clock c) (Pos.succ (post_clock c)).
Proof.
  reflexivity.
Qed.

(** Runtime classification observes current colors and ranks, never parent endpoints. *)
Definition edge_kind_c {E} (c : core E) u v :=
  let* visited := FinSet.mem_c positive_encoding v (seen c) in
  if visited then
    let* post := Map.get_c positive_encoding v (post_index c) in
    match post with
    | None => Cost.ret Search.Back
    | Some _ =>
      let* a := Map.get_c positive_encoding u (pre_index c) in
      let* b := Map.get_c positive_encoding v (pre_index c) in
      Cost.ret
        (match a, b with
        | Some a, Some b => if Pos.ltb a b then Search.Forward else Search.Cross
        | _, _ => Search.Cross
        end)
    end
  else Cost.ret Search.Tree.

Definition edge_kind {E} (c : core E) u v := Cost.value (edge_kind_c c u v).

(** Each transition returns at most an edge and its immediately following entry event. *)
Definition transition_c {V E} (p : Prepared.t V E) scope (w : work E)
    : Cost.t ((work E + work E) * list (Search.event E)) :=
  Cost.step ;;
  let '(stack, c) := w in
  match stack with
  | [] => Cost.ret (inr w, [])
  | (u, []) :: rest =>
    let* c' := finish_c u c in
    Cost.ret (inl (rest, c'),
      [Search.Exit u (match rest with [] => None | (v, _) :: _ => Some v end)])
  | (u, (e, v) :: pending) :: rest =>
    let tail := (u, pending) :: rest in
    let* admitted := Scope.admits_c scope v in
    if admitted then
      let* name := Prepared.name_of_c p v in
      match name with
      | None => Cost.ret (inl (tail, c), [])
      | Some _ =>
      let* k := edge_kind_c c u v in
      match k with
      | Search.Tree =>
        let* c' := discover_c v (Some (e, u)) c in
        let* es := Prepared.succ_edges_c p v in
        Cost.ret (inl ((v, es) :: tail, c'), [Search.Edge e u v k; Search.Enter v (Some (e, u))])
      | _ => Cost.ret (inl (tail, c), [Search.Edge e u v k])
      end
      end
    else Cost.ret (inl (tail, c), [])
  end.

Definition transition {V E} (p : Prepared.t V E) scope w :=
  Cost.value (transition_c p scope w).

(** Rejected targets consume admission work and emit no scoped edge event. *)
Theorem step_equation {V E} (p : Prepared.t V E) scope stack (c : core E) :
  transition p scope (stack, c) =
    match stack with
    | [] => (inr (stack, c), [])
    | (u, []) :: rest =>
      (inl (rest, finish u c),
        [Search.Exit u (match rest with [] => None | (v, _) :: _ => Some v end)])
    | (u, (e, v) :: pending) :: rest =>
      let tail := (u, pending) :: rest in
      if Scope.admits scope v then
        match Prepared.name_of p v with
        | None => (inl (tail, c), [])
        | Some _ =>
        let k := edge_kind c u v in
        match k with
        | Search.Tree =>
          (inl ((v, Prepared.succ_edges p v) :: tail, discover v (Some (e, u)) c),
            [Search.Edge e u v k; Search.Enter v (Some (e, u))])
        | _ => (inl (tail, c), [Search.Edge e u v k])
        end
        end
      else (inl (tail, c), [])
    end.
Proof.
  destruct stack as [|[u [|[e v] pending]] rest]; [reflexivity|reflexivity|].
  unfold transition, transition_c. autorewrite with galois_cost.
  fold (Scope.admits scope v). destruct (Scope.admits scope v); [|reflexivity].
  autorewrite with galois_cost.
  fold (Prepared.name_of p v). destruct (Prepared.name_of p v); [|reflexivity].
  autorewrite with galois_cost.
  fold (edge_kind c u v). destruct (edge_kind c u v); reflexivity.
Qed.

Definition apply_events_c {E S} (vis : Visitor.t E S) evs s :=
  fold_left_c (fun s ev => Visitor.apply_c vis ev s) evs s.

Definition apply_events {E S} (vis : Visitor.t E S) evs s :=
  fold_left (fun s ev => Visitor.apply vis ev s) evs s.

(** Event dispatch retains the complete callback cost and the list traversal charge. *)
Theorem apply_events_value {E S} (vis : Visitor.t E S) evs s :
  Cost.value (apply_events_c vis evs s) = apply_events vis evs s.
Proof.
  apply value_fold_left_c.
Qed.

Definition step_c {V E S} (p : Prepared.t V E) (vis : Visitor.t E S) scope
    (state : work E * S) : Cost.t ((work E * S) + (work E * S)) :=
  let '(w, s) := state in
  let* next := transition_c p scope w in
  let* s' := apply_events_c vis (snd next) s in
  Cost.ret
    (match fst next with
    | inl w' => inl (w', s')
    | inr w' => inr (w', s')
    end).

(** Erasing a step preserves the transition and folds precisely its emitted events. *)
Theorem step_erases {V E S} (p : Prepared.t V E) (vis : Visitor.t E S) scope w s :
  Cost.value (step_c p vis scope (w, s)) =
    let '(next, evs) := transition p scope w in
    match next with
    | inl w' => inl (w', apply_events vis evs s)
    | inr w' => inr (w', apply_events vis evs s)
    end.
Proof.
  unfold step_c. autorewrite with galois_cost. rewrite apply_events_value.
  fold (transition p scope w). destruct (transition p scope w) as [[w'|w'] evs];
    reflexivity.
Qed.

(** The reference loop counts actual transitions using ordinary natural-number recursion. *)
Fixpoint reference_loop {V E} (p : Prepared.t V E) scope n (w : work E)
    : work E * list (Search.event E) :=
  match n with
  | O => (w, [])
  | Datatypes.S n =>
    let '(next, here) := transition p scope w in
    match next with
    | inr w' => (w', here)
    | inl w' =>
      let '(final, later) := reference_loop p scope n w' in
      (final, here ++ later)
    end
  end.

Definition unwrap {A} (x : A + A) := match x with inl a | inr a => a end.

(** Core reconstruction uses the same entry and exit updates and ignores edge notifications. *)
Definition core_event {E} (c : core E) (ev : Search.event E) :=
  match ev with
  | Search.Enter v via => discover v via c
  | Search.Exit v _ => finish v c
  | Search.Edge _ _ _ _ => c
  end.

(** A transition's events reconstruct precisely its resulting core, including its selected label. *)
Theorem transition_core {V E} (p : Prepared.t V E) scope (w : work E) :
  snd (unwrap (fst (transition p scope w))) =
    fold_left core_event (snd (transition p scope w)) (snd w).
Proof.
  destruct w as [stack c]. rewrite step_equation.
  destruct stack as [|[u [|[e v] pending]] rest]; [reflexivity|reflexivity|].
  destruct (Scope.admits scope v); [|reflexivity].
  destruct (Prepared.name_of p v); [|reflexivity].
  destruct (edge_kind c u v); reflexivity.
Qed.

(** Natural-budget reference runs reconstruct their core from their complete event list. *)
Theorem reference_loop_core {V E} (p : Prepared.t V E) scope n w :
  snd (fst (reference_loop p scope n w)) =
    fold_left core_event (snd (reference_loop p scope n w)) (snd w).
Proof.
  revert w. induction n as [|n IH]; intro w; [reflexivity|].
  pose proof (transition_core p scope w) as Hcore.
  cbn [reference_loop].
  destruct (transition p scope w) as [[w'|w'] here]; cbn [fst snd unwrap] in Hcore.
  - pose proof (IH w') as Htail.
    destruct (reference_loop p scope n w') as [final later].
    cbn [fst snd] in Htail |- *. rewrite fold_left_app, <- Hcore. exact Htail.
  - exact Hcore.
Qed.

(** Reference event blocks compose in their original order for every visitor. *)
Theorem apply_events_app {E S} (vis : Visitor.t E S) xs ys s :
  apply_events vis (xs ++ ys) s = apply_events vis ys (apply_events vis xs s).
Proof.
  apply fold_left_app.
Qed.

(** Any driver run erases to the same natural-budget reference and visitor fold. *)
Theorem runs_erases {V E S} (p : Prepared.t V E) (vis : Visitor.t E S) scope
    n state answer :
  runs (step_c p vis scope) n state answer ->
  let '(w, s) := state in
  let '(final, evs) := reference_loop p scope n w in
  unwrap answer = (final, apply_events vis evs s).
Proof.
  intro Hrun. induction Hrun as [state|n state answer Hstop|n state next answer Hnext Hrun IH].
  - destruct state. reflexivity.
  - destruct state as [w s]. rewrite step_erases in Hstop.
    cbn [reference_loop]. destruct (transition p scope w) as [[w'|w'] evs];
      inversion Hstop; subst. reflexivity.
  - destruct state as [w s]. rewrite step_erases in Hnext.
    cbn [reference_loop]. destruct (transition p scope w) as [[w'|w'] evs];
      inversion Hnext; subst.
    destruct (reference_loop p scope n w') as [final later].
    rewrite apply_events_app. exact IH.
Qed.

(** The binary loop retains the same visitor-independent work and exact reference events. *)
Theorem loop_erases {V E S} (p : Prepared.t V E) (vis : Visitor.t E S) scope fuel w s :
  unwrap (Cost.value (iterate (step_c p vis scope) fuel (w, s))) =
    let '(final, evs) := reference_loop p scope (Pos.to_nat fuel) w in
    (final, apply_events vis evs s).
Proof.
  pose proof (runs_erases p vis scope _ _ _ (iterate_value (step_c p vis scope) fuel (w, s)))
    as Herase.
  cbn beta iota zeta in Herase.
  destruct (reference_loop p scope (Pos.to_nat fuel) w) as [final evs] eqn:Hreference.
  exact Herase.
Qed.

Definition launch_c {V E S} (p : Prepared.t V E) (vis : Visitor.t E S) scope
    (c : core E) v s : Cost.t (core E * S) :=
  let* c' := discover_c v None c in
  let* s' := Visitor.apply_c vis (Search.Enter v None) s in
  let* es := Prepared.succ_edges_c p v in
  let* answer := iterate (step_c p vis scope) (Prepared.fuel p) (([(v, es)], c'), s') in
  let '(w, s'') := unwrap answer in Cost.ret (snd w, s'').

Definition root_c {V E S} (p : Prepared.t V E) (vis : Visitor.t E S) scope
    (state : core E * S) v : Cost.t (core E * S) :=
  let '(c, s) := state in
  let* admitted := Scope.admits_c scope v in
  if admitted then
    let* visited := FinSet.mem_c positive_encoding v (seen c) in
    if visited then Cost.ret state else
      let* name := Prepared.name_of_c p v in
      match name with
      | None => Cost.ret state
      | Some _ => launch_c p vis scope c v s
      end
  else Cost.ret state.

(** Reference roots reject unknown IDs and retain root occurrences and order. *)
Definition reference_root {V E} (p : Prepared.t V E) scope (c : core E) v
    : core E * list (Search.event E) :=
  if Scope.admits scope v then
    if FinSet.mem positive_encoding v (seen c) then (c, []) else
      match Prepared.name_of p v with
      | None => (c, [])
      | Some _ =>
        let '(w, evs) := reference_loop p scope (Pos.to_nat (Prepared.fuel p))
          ([(v, Prepared.succ_edges p v)], discover v None c) in
        (snd w, Search.Enter v None :: evs)
      end
  else (c, []).

(** Every reference root's entry and loop events reconstruct the actual root result. *)
Theorem reference_root_core {V E} (p : Prepared.t V E) scope (c : core E) v :
  fst (reference_root p scope c v) =
    fold_left core_event (snd (reference_root p scope c v)) c.
Proof.
  unfold reference_root.
  destruct (Scope.admits scope v); [|reflexivity].
  destruct (FinSet.mem positive_encoding v (seen c)); [reflexivity|].
  destruct (Prepared.name_of p v); [|reflexivity].
  pose proof (reference_loop_core p scope (Pos.to_nat (Prepared.fuel p))
    ([(v, Prepared.succ_edges p v)], discover v None c)) as Hcore.
  destruct (reference_loop p scope (Pos.to_nat (Prepared.fuel p))
    ([(v, Prepared.succ_edges p v)], discover v None c)) as [w evs].
  exact Hcore.
Qed.

(** Skipping or starting a root produces exactly the reference root's visitor effects. *)
Theorem root_erases {V E S} (p : Prepared.t V E) (vis : Visitor.t E S) scope c s v :
  Cost.value (root_c p vis scope (c, s) v) =
    let '(c', evs) := reference_root p scope c v in (c', apply_events vis evs s).
Proof.
  unfold root_c, reference_root, launch_c. autorewrite with galois_cost.
  fold (Scope.admits scope v). destruct (Scope.admits scope v); [|reflexivity].
  autorewrite with galois_cost.
  fold (FinSet.mem positive_encoding v (seen c)).
  destruct (FinSet.mem positive_encoding v (seen c)); [reflexivity|].
  autorewrite with galois_cost.
  fold (Prepared.name_of p v). destruct (Prepared.name_of p v); [|reflexivity].
  autorewrite with galois_cost.
  fold (discover v None c).
  fold (Visitor.apply vis (Search.Enter v None) s).
  fold (Prepared.succ_edges p v).
  pose proof (loop_erases p vis scope (Prepared.fuel p)
    ([(v, Prepared.succ_edges p v)], discover v None c)
    (Visitor.apply vis (Search.Enter v None) s)) as Hloop.
  destruct (reference_loop p scope (Pos.to_nat (Prepared.fuel p))
    ([(v, Prepared.succ_edges p v)], discover v None c)) as [[stack c'] evs] eqn:Hreference.
  match goal with
  | |- context [unwrap ?answer] => destruct (unwrap answer) as [w' s'] eqn:Hanswer
  end.
  unfold work, frame in Hloop, Hanswer.
  assert (Heq : (w', s') =
    ((stack, c'), apply_events vis evs (Visitor.apply vis (Search.Enter v None) s))).
  { transitivity (unwrap (Cost.value (iterate (step_c p vis scope) (Prepared.fuel p)
      (([(v, Prepared.succ_edges p v)], discover v None c),
        Visitor.apply vis (Search.Enter v None) s)))).
    - symmetry. exact Hanswer.
    - exact Hloop. }
  inversion Heq. reflexivity.
Qed.

Fixpoint reference_roots {V E} (p : Prepared.t V E) scope roots (c : core E)
    : core E * list (Search.event E) :=
  match roots with
  | [] => (c, [])
  | v :: rest =>
    let '(c', here) := reference_root p scope c v in
    let '(final, later) := reference_roots p scope rest c' in
    (final, here ++ later)
  end.

(** Root event concatenation reconstructs the actual final core without reselecting parents. *)
Theorem reference_roots_core {V E} (p : Prepared.t V E) scope roots c :
  fst (reference_roots p scope roots c) =
    fold_left core_event (snd (reference_roots p scope roots c)) c.
Proof.
  revert c. induction roots as [|v rest IH]; intro c; [reflexivity|].
  pose proof (reference_root_core p scope c v) as Hroot.
  cbn [reference_roots].
  destruct (reference_root p scope c v) as [c' here]. cbn [fst snd] in Hroot.
  pose proof (IH c') as Htail.
  destruct (reference_roots p scope rest c') as [final later].
  cbn [fst snd] in Htail |- *. rewrite fold_left_app, <- Hroot. exact Htail.
Qed.

(** The costed root fold preserves the complete reference event sequence. *)
Theorem roots_erases {V E S} (p : Prepared.t V E) (vis : Visitor.t E S) scope roots c s :
  Cost.value (fold_left_c (root_c p vis scope) roots (c, s)) =
    let '(final, evs) := reference_roots p scope roots c in
    (final, apply_events vis evs s).
Proof.
  rewrite value_fold_left_c.
  revert c s. induction roots as [|v rest IH]; intros c s; [reflexivity|].
  cbn [fold_left reference_roots].
  rewrite root_erases.
  destruct (reference_root p scope c v) as [c' here].
  rewrite IH. destruct (reference_roots p scope rest c') as [final later].
  rewrite apply_events_app. reflexivity.
Qed.

Definition result_c {E} (c : core E) : Cost.t (Search.result E) :=
  let* pre := rev_c (pre_rev c) in
  let* post := rev_c (post_rev c) in
  Cost.ret (Search.Result pre post (parents c) (pre_index c) (post_index c) (seen c)).

Definition result {E} (c : core E) := Cost.value (result_c c).

(** Finalization reverses both accumulated orders without changing maps or visited IDs. *)
Theorem result_equation {E} (c : core E) :
  result c = Search.Result (rev (pre_rev c)) (rev (post_rev c))
    (parents c) (pre_index c) (post_index c) (seen c).
Proof.
  unfold result, result_c. autorewrite with galois_cost. reflexivity.
Qed.

Definition run_c {V E S} (p : Prepared.t V E) (vis : Visitor.t E S) scope roots s0 :=
  let* state := fold_left_c (root_c p vis scope) roots (initial, s0) in
  let* r := result_c (fst state) in Cost.ret (r, snd state).

Definition events {V E} (p : Prepared.t V E) scope roots :=
  snd (reference_roots p scope roots initial).

Definition result_of {E} (evs : list (Search.event E)) :=
  result (fold_left core_event evs initial).

Definition dfs {V E} (p : Prepared.t V E) scope roots :=
  fst (Cost.value (run_c p (@Visitor.noop E unit) scope roots tt)).

(** Search returns the reference core's ordered result and folds precisely the reference events. *)
Theorem run_equation {V E S} (p : Prepared.t V E) (vis : Visitor.t E S) scope roots s0 :
  Cost.value (run_c p vis scope roots s0) =
    let '(c, evs) := reference_roots p scope roots initial in
    (result c, apply_events vis evs s0).
Proof.
  unfold run_c. rewrite Cost.value_bind, roots_erases.
  destruct (reference_roots p scope roots initial) as [c evs]. reflexivity.
Qed.

(** Arbitrary visitors change only their own state and agree with the complete reference trace. *)
Theorem run_events {V E S} (p : Prepared.t V E) (vis : Visitor.t E S) scope roots s0 :
  Cost.value (run_c p vis scope roots s0) =
    (result_of (events p scope roots), apply_events vis (events p scope roots) s0).
Proof.
  unfold events, result_of. rewrite run_equation.
  pose proof (reference_roots_core p scope roots initial) as Hcore.
  destruct (reference_roots p scope roots initial) as [c evs].
  cbn [fst snd] in Hcore |- *. now rewrite <- Hcore.
Qed.

(** A visitor cannot alter the search result. *)
Theorem run_result {V E S} (p : Prepared.t V E) (vis : Visitor.t E S) scope roots s0 :
  fst (Cost.value (run_c p vis scope roots s0)) = dfs p scope roots.
Proof.
  unfold dfs. rewrite !run_equation.
  destruct (reference_roots p scope roots initial) as [c evs]. reflexivity.
Qed.

(** Temporal edge colors inspect current discovery and finishing observations independently of labels. *)
Inductive edge_color {E} (c : core E) u v : Search.kind -> Prop :=
  | color_tree :
      FinSet.mem positive_encoding v (seen c) = false -> edge_color c u v Search.Tree
  | color_back :
      FinSet.mem positive_encoding v (seen c) = true ->
      Map.get positive_encoding v (post_index c) = None -> edge_color c u v Search.Back
  | color_forward : forall finished a b,
      FinSet.mem positive_encoding v (seen c) = true ->
      Map.get positive_encoding v (post_index c) = Some finished ->
      Map.get positive_encoding u (pre_index c) = Some a ->
      Map.get positive_encoding v (pre_index c) = Some b ->
      Pos.ltb a b = true -> edge_color c u v Search.Forward
  | color_cross : forall finished,
      FinSet.mem positive_encoding v (seen c) = true ->
      Map.get positive_encoding v (post_index c) = Some finished ->
      (match Map.get positive_encoding u (pre_index c),
        Map.get positive_encoding v (pre_index c) with
      | Some a, Some b => Pos.ltb a b = false
      | _, _ => True
      end) -> edge_color c u v Search.Cross.

(** Runtime edge colors satisfy the temporal observation rules on arbitrary cores. *)
Theorem edge_kind_color {E} (c : core E) u v : edge_color c u v (edge_kind c u v).
Proof.
  unfold edge_kind, edge_kind_c. rewrite Cost.value_bind.
  fold (FinSet.mem positive_encoding v (seen c)).
  destruct (FinSet.mem positive_encoding v (seen c)) eqn:Hseen; [|now apply color_tree].
  rewrite Cost.value_bind. fold (Map.get positive_encoding v (post_index c)).
  destruct (Map.get positive_encoding v (post_index c)) as [finished|] eqn:Hpost;
    [|now apply color_back].
  rewrite !Cost.value_bind. fold (Map.get positive_encoding u (pre_index c)).
  fold (Map.get positive_encoding v (pre_index c)).
  destruct (Map.get positive_encoding u (pre_index c)) as [a|] eqn:Ha;
    destruct (Map.get positive_encoding v (pre_index c)) as [b|] eqn:Hb;
    rewrite Cost.value_ret.
  - destruct (Pos.ltb a b) eqn:Hlt.
    + eapply color_forward; eassumption.
    + eapply color_cross; [exact Hseen|exact Hpost|now rewrite ?Ha, ?Hb].
  - eapply color_cross; [exact Hseen|exact Hpost|now rewrite ?Ha, ?Hb].
  - eapply color_cross; [exact Hseen|exact Hpost|now rewrite ?Ha, ?Hb].
  - eapply color_cross; [exact Hseen|exact Hpost|now rewrite ?Ha, ?Hb].
Qed.

(** Each temporal color rule determines the runtime classifier without consulting a label. *)
Theorem color_edge_kind {E} (c : core E) u v k :
  edge_color c u v k -> edge_kind c u v = k.
Proof.
  intro Hcolor.
  destruct Hcolor as [Hseen|Hseen Hpost|finished a b Hseen Hpost Ha Hb Hlt|
    finished Hseen Hpost Hcross]; unfold edge_kind, edge_kind_c;
    rewrite Cost.value_bind; fold (FinSet.mem positive_encoding v (seen c));
    rewrite Hseen;
    try reflexivity; rewrite Cost.value_bind;
    fold (Map.get positive_encoding v (post_index c));
    rewrite Hpost;
    try reflexivity; rewrite !Cost.value_bind;
    fold (Map.get positive_encoding u (pre_index c));
    fold (Map.get positive_encoding v (pre_index c)).
  - rewrite Ha, Hb, Cost.value_ret, Hlt. reflexivity.
  - destruct (Map.get positive_encoding u (pre_index c)) as [a|] eqn:Ha;
      destruct (Map.get positive_encoding v (pre_index c)) as [b|] eqn:Hb;
      rewrite Cost.value_ret; try reflexivity.
    now rewrite Hcross.
Qed.

(** DFS trace blocks inspect labelled occurrences, enter white targets and pop completed frames. *)
Inductive trace_step {V E} (p : Prepared.t V E) scope :
    work E -> list (Search.event E) -> work E -> Prop :=
  | trace_exit : forall u rest c,
      trace_step p scope ((u, []) :: rest, c)
        [Search.Exit u (match rest with [] => None | (parent, _) :: _ => Some parent end)]
        (rest, finish u c)
  | trace_scope_skip : forall u e v pending rest c,
      Scope.admits scope v = false ->
      trace_step p scope ((u, (e, v) :: pending) :: rest, c) [] ((u, pending) :: rest, c)
  | trace_unknown_skip : forall u e v pending rest c,
      Scope.admits scope v = true -> Prepared.name_of p v = None ->
      trace_step p scope ((u, (e, v) :: pending) :: rest, c) [] ((u, pending) :: rest, c)
  | trace_tree : forall u e v pending rest c name,
      Scope.admits scope v = true -> Prepared.name_of p v = Some name ->
      edge_color c u v Search.Tree ->
      trace_step p scope ((u, (e, v) :: pending) :: rest, c)
        [Search.Edge e u v Search.Tree; Search.Enter v (Some (e, u))]
        ((v, Prepared.succ_edges p v) :: (u, pending) :: rest, discover v (Some (e, u)) c)
  | trace_seen : forall u e v pending rest c name k,
      Scope.admits scope v = true -> Prepared.name_of p v = Some name ->
      edge_color c u v k -> k <> Search.Tree ->
      trace_step p scope ((u, (e, v) :: pending) :: rest, c)
        [Search.Edge e u v k] ((u, pending) :: rest, c).

(** A trace segment preserves ordered blocks and their exact intermediate frame/core states. *)
Inductive trace_segment {V E} (p : Prepared.t V E) scope :
    work E -> list (Search.event E) -> work E -> Prop :=
  | trace_segment_nil : forall w, trace_segment p scope w [] w
  | trace_segment_next : forall w here next later final,
      trace_step p scope w here next -> trace_segment p scope next later final ->
      trace_segment p scope w (here ++ later) final.

(** Every continuing transition is one independently specified DFS trace block. *)
Theorem transition_trace {V E} (p : Prepared.t V E) scope w next evs :
  transition p scope w = (inl next, evs) -> trace_step p scope w evs next.
Proof.
  destruct w as [stack c]. rewrite step_equation.
  destruct stack as [|[u [|[e v] pending]] rest]; [discriminate| |].
  - intro H. inversion H; subst. apply trace_exit.
  - destruct (Scope.admits scope v) eqn:Hscope.
    + destruct (Prepared.name_of p v) as [name|] eqn:Hname.
      * pose proof (edge_kind_color c u v) as Hcolor.
        destruct (edge_kind c u v); intro H; inversion H; subst.
        -- eapply trace_tree; eassumption.
        -- eapply trace_seen; try eassumption; discriminate.
        -- eapply trace_seen; try eassumption; discriminate.
        -- eapply trace_seen; try eassumption; discriminate.
      * intro H. inversion H; subst. now apply trace_unknown_skip.
    + intro H. inversion H; subst. now apply trace_scope_skip.
Qed.

(** Reference segments keep every labelled event occurrence and exact intermediate state. *)
Theorem reference_loop_trace {V E} (p : Prepared.t V E) scope n w :
  trace_segment p scope w (snd (reference_loop p scope n w))
    (fst (reference_loop p scope n w)).
Proof.
  revert w. induction n as [|n IH]; intro w; [apply trace_segment_nil|].
  cbn [reference_loop].
  destruct (transition p scope w) as [[next|final] here] eqn:Htransition.
  - pose proof (IH next) as Htail.
    destruct (reference_loop p scope n next) as [last later].
    eapply trace_segment_next; [exact (transition_trace p scope w next here Htransition)|].
    exact Htail.
  - destruct w as [stack c]. rewrite step_equation in Htransition.
    destruct stack as [|[u [|[e v] pending]] rest].
    + inversion Htransition; subst. apply trace_segment_nil.
    + discriminate.
    + destruct (Scope.admits scope v); [|discriminate].
      destruct (Prepared.name_of p v); [|discriminate].
      destruct (edge_kind c u v); discriminate.
Qed.

(** Root traces either skip one rejected/seen occurrence or drain a fresh DFS tree completely. *)
Inductive trace_root {V E} (p : Prepared.t V E) scope :
    core E -> positive -> list (Search.event E) -> core E -> Prop :=
  | trace_root_scope : forall c v,
      Scope.admits scope v = false -> trace_root p scope c v [] c
  | trace_root_seen : forall c v,
      Scope.admits scope v = true -> FinSet.mem positive_encoding v (seen c) = true ->
      trace_root p scope c v [] c
  | trace_root_unknown : forall c v,
      Scope.admits scope v = true -> FinSet.mem positive_encoding v (seen c) = false ->
      Prepared.name_of p v = None -> trace_root p scope c v [] c
  | trace_root_fresh : forall c v name evs final,
      Scope.admits scope v = true -> FinSet.mem positive_encoding v (seen c) = false ->
      Prepared.name_of p v = Some name ->
      trace_segment p scope ([(v, Prepared.succ_edges p v)], discover v None c) evs ([], final) ->
      trace_root p scope c v (Search.Enter v None :: evs) final.

(** Root-sequence traces preserve duplicate roots, skip decisions and tree order. *)
Inductive trace_roots {V E} (p : Prepared.t V E) scope :
    list positive -> core E -> list (Search.event E) -> core E -> Prop :=
  | trace_roots_nil : forall c, trace_roots p scope [] c [] c
  | trace_roots_cons : forall v rest c here next later final,
      trace_root p scope c v here next -> trace_roots p scope rest next later final ->
      trace_roots p scope (v :: rest) c (here ++ later) final.

End SearchRun.
