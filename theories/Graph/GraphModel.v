(** * Graphs and constructive paths

    Graph callbacks retain their charges and paths describe their pure observations.
    For example, an empty path connects a node to itself.
    Builds on: CostMonad and BaseEncoding. *)

From Stdlib Require Import List Bool Arith NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding.
Import List.ListNotations Cost.Notations.

Module Graph.

(** Graph data can be used without well-formedness or termination evidence. *)
Record t (V E : Type) := Make {
  entries : list V;
  nodes : list V;
  out_c : V -> Cost.t (list E);
  source_c : E -> Cost.t V;
  target_c : E -> Cost.t V
}.
Arguments Make {V E}.
Arguments entries {V E}.
Arguments nodes {V E}.
Arguments out_c {V E}.
Arguments source_c {V E}.
Arguments target_c {V E}.

Definition out {V E} (g : t V E) v := Cost.value (out_c g v).
Definition source {V E} (g : t V E) e := Cost.value (source_c g e).
Definition target {V E} (g : t V E) e := Cost.value (target_c g e).

(** Outgoing observation of a constructed graph is the value of its supplied callback. *)
Theorem make_out {V E} roots nodes (out_c : V -> Cost.t (list E)) source_c target_c v :
  out (Make roots nodes out_c source_c target_c) v = Cost.value (out_c v).
Proof.
  reflexivity.
Qed.

(** Source observation of a constructed graph is the value of its supplied callback. *)
Theorem make_source {V E} roots nodes (out_c : V -> Cost.t (list E)) source_c target_c e :
  source (Make roots nodes out_c source_c target_c) e = Cost.value (source_c e).
Proof.
  reflexivity.
Qed.

(** Target observation of a constructed graph is the value of its supplied callback. *)
Theorem make_target {V E} roots nodes (out_c : V -> Cost.t (list E)) source_c target_c e :
  target (Make roots nodes out_c source_c target_c) e = Cost.value (target_c e).
Proof.
  reflexivity.
Qed.

(** Pure client primitives charge one tick on each accessor call. *)
Definition of_pure {V E} entries nodes (out : V -> list E) (source target : E -> V) :=
  @Make V E entries nodes (Cost.lift (fun _ => 1%N) out)
    (Cost.lift (fun _ => 1%N) source) (Cost.lift (fun _ => 1%N) target).

(** Reversal retains the incoming callback's charges and swaps endpoint callbacks. *)
Definition reverse_with {V E} (g : t V E) exits incoming : t V E :=
  Make exits (nodes g) incoming (target_c g) (source_c g).

(** Pure adapters preserve outgoing values. *)
Theorem of_pure_out {V E} roots vs (f : V -> list E) s t v :
  out (of_pure roots vs f s t) v = f v.
Proof.
  apply Cost.value_lift.
Qed.

(** Pure adapters preserve source endpoints. *)
Theorem of_pure_source {V E} roots vs (f : V -> list E) s t e :
  source (of_pure roots vs f s t) e = s e.
Proof.
  apply Cost.value_lift.
Qed.

(** Pure adapters preserve target endpoints. *)
Theorem of_pure_target {V E} roots vs (f : V -> list E) s t e :
  target (of_pure roots vs f s t) e = t e.
Proof.
  apply Cost.value_lift.
Qed.

(** Pure adapters charge one outgoing primitive call. *)
Theorem of_pure_out_cost {V E} roots vs (f : V -> list E) s t v :
  Cost.ticks (out_c (of_pure roots vs f s t) v) = 1%N.
Proof.
  change (Cost.ticks (Cost.lift (fun _ : V => 1%N) f v) = 1%N).
  rewrite Cost.ticks_lift. reflexivity.
Qed.

(** Pure endpoint primitives use the same unit-charge convention as outgoing access. *)
Theorem of_pure_endpoint_cost {V E} roots vs (f : V -> list E) s t e :
  Cost.ticks (source_c (of_pure roots vs f s t) e) = 1%N /\
  Cost.ticks (target_c (of_pure roots vs f s t) e) = 1%N.
Proof.
  change (Cost.ticks (Cost.lift (fun _ : E => 1%N) s e) = 1%N /\
    Cost.ticks (Cost.lift (fun _ : E => 1%N) t e) = 1%N).
  rewrite !Cost.ticks_lift. split; reflexivity.
Qed.

Arguments of_pure {V E} entries nodes out source target : simpl never.
Arguments reverse_with {V E} g exits incoming : simpl never.

End Graph.

(** Reachability starts at any entry and follows listed outgoing edges. *)
Inductive reachable {V E} (g : Graph.t V E) : V -> Prop :=
  | reachable_entry : forall v, In v (Graph.entries g) -> reachable g v
  | reachable_step : forall e, reachable g (Graph.source g e) ->
      In e (Graph.out g (Graph.source g e)) -> reachable g (Graph.target g e).
Arguments reachable_entry {V E g} v _.
Arguments reachable_step {V E g} e _ _.

(** Well-formed graphs have distinct nodes and closed, correctly sourced edges. *)
Record graph_wf {V E} (g : Graph.t V E) : Prop := {
  nodes_nodup : NoDup (Graph.nodes g);
  entries_in : forall v, In v (Graph.entries g) -> In v (Graph.nodes g);
  out_source : forall v e, In e (Graph.out g v) -> Graph.source g e = v;
  out_target_in : forall v e, In v (Graph.nodes g) -> In e (Graph.out g v) ->
    In (Graph.target g e) (Graph.nodes g)
}.
Arguments nodes_nodup {V E g} _.
Arguments entries_in {V E g} _ v _.
Arguments out_source {V E g} _ v e _.
Arguments out_target_in {V E g} _ v e _ _.

(** A path records edges in traversal order, including an empty traversal. *)
Inductive path {V E} (g : Graph.t V E) : V -> list E -> V -> Prop :=
  | path_nil : forall v, path g v [] v
  | path_cons : forall e es w, In e (Graph.out g (Graph.source g e)) ->
      path g (Graph.target g e) es w -> path g (Graph.source g e) (e :: es) w.
Arguments path_nil {V E g} v.
Arguments path_cons {V E g} e es w _ _.

(** Two nodes are related when an edge-labelled path connects them. *)
Definition reaches {V E} (g : Graph.t V E) u v := exists es, path g u es v.

(** Mutual reachability requires paths in both directions. *)
Definition mutual {V E} (g : Graph.t V E) u v := reaches g u v /\ reaches g v u.

(** Acyclicity rules out every nonempty cycle starting at a listed node. *)
Definition acyclic {V E} (g : Graph.t V E) :=
  forall v es, In v (Graph.nodes g) -> path g v es v -> es = [].

(** Strict textual precedence distinguishes two occurrences in a list. *)
Definition before {A} (xs : list A) u v :=
  exists a b c, xs = a ++ u :: b ++ v :: c.

(** Every listed cycle must meet the supplied cut predicate. *)
Definition cycles_cut {V E} (g : Graph.t V E) (cut : V -> Prop) :=
  forall v es, In v (Graph.nodes g) -> path g v es v -> es <> [] ->
    cut v \/ exists e, In e es /\ cut (Graph.target g e).

(** Entry replacement leaves every callback unchanged. *)
Definition set_entries {V E} (g : Graph.t V E) roots :=
  Graph.Make roots (Graph.nodes g) (Graph.out_c g) (Graph.source_c g) (Graph.target_c g).

(** Count edges once at their listed source in the mathematical reference model. *)
Definition edge_count {V E} (g : Graph.t V E) :=
  fold_right (fun v n => length (Graph.out g v) + n) 0 (Graph.nodes g).

(** Filtering retains every predicate callback charge and charges every visited cell. *)
Fixpoint graph_filter_c {A} (keep_c : A -> Cost.t bool) (xs : list A) : Cost.t (list A) :=
  match xs with
  | [] => Cost.ret []
  | x :: rest =>
    Cost.step ;;
    Cost.step ;;
    let* keep := keep_c x in
    let* ys := graph_filter_c keep_c rest in
    Cost.ret (if keep then x :: ys else ys)
  end.

Local Lemma graph_filter_value {A} (keep_c : A -> Cost.t bool) xs :
  Cost.value (graph_filter_c keep_c xs) =
    filter (fun x => Cost.value (keep_c x)) xs.
Proof.
  induction xs as [|x rest IH]; [reflexivity|].
  cbn [graph_filter_c]. autorewrite with galois_cost.
  rewrite IH. reflexivity.
Qed.

Definition without_out_c {V E} (eq_c : V -> V -> Cost.t bool) d (g : Graph.t V E) v :=
  Cost.step ;;
  let* es := Graph.out_c g v in
  graph_filter_c (fun e =>
    Cost.step ;;
    let* target := Graph.target_c g e in
    Cost.step ;;
    let* deleted := eq_c target d in Cost.ret (negb deleted)) es.

(** Deletion keeps a reference node domain and honestly costed outgoing callbacks. *)
Definition without {V E} (eq_c : V -> V -> Cost.t bool) (d : V) (g : Graph.t V E) :=
  Graph.Make (filter (fun v => negb (Cost.value (eq_c v d))) (Graph.entries g))
    (filter (fun v => negb (Cost.value (eq_c v d))) (Graph.nodes g))
    (without_out_c eq_c d g) (Graph.source_c g) (Graph.target_c g).

(** Deleted outgoing lists contain exactly the edges whose targets survive deletion. *)
Theorem without_out {V E} eq_c d (g : Graph.t V E) v :
  Graph.out (without eq_c d g) v =
    filter (fun e => negb (Cost.value (eq_c (Graph.target g e) d))) (Graph.out g v).
Proof.
  change (Cost.value (without_out_c eq_c d g v) =
    filter (fun e => negb (Cost.value (eq_c (Graph.target g e) d))) (Graph.out g v)).
  unfold without_out_c. autorewrite with galois_cost.
  rewrite graph_filter_value. reflexivity.
Qed.

Local Lemma path_snoc {V E} (g : Graph.t V E) u es v e :
  path g u es v -> v = Graph.source g e -> In e (Graph.out g v) ->
  path g u (es ++ [e]) (Graph.target g e).
Proof.
  intros Hpath. induction Hpath as [v|a es w Hedge Hpath IH]; intros Heq Hin.
  - subst v. cbn. constructor; [exact Hin|constructor].
  - cbn. constructor; [exact Hedge|]. apply IH; assumption.
Qed.

(** Reachability holds exactly at endpoints of paths starting at an entry. *)
Theorem reachable_iff_path {V E} (g : Graph.t V E) v :
  reachable g v <-> exists s es, In s (Graph.entries g) /\ path g s es v.
Proof.
  split.
  - intro Hreach. induction Hreach as [v Hin|e Hreach IH Hedge].
    + exists v, []. split; [exact Hin|constructor].
    + destruct IH as [s [es [Hin Hpath]]].
      exists s, (es ++ [e]). split; [exact Hin|]. eapply path_snoc; eauto.
  - intros [s [es [Hin Hpath]]].
    assert (Hstart : reachable g s) by (constructor; exact Hin).
    clear Hin. induction Hpath as [v|e es w Hedge Hpath IH]; [exact Hstart|].
    apply IH. eapply reachable_step; eauto.
Qed.

(** Every reachable node belongs to a well-formed graph's node domain. *)
Theorem reachable_in_nodes {V E} (g : Graph.t V E) v :
  graph_wf g -> reachable g v -> In v (Graph.nodes g).
Proof.
  intros Hwf Hreach. induction Hreach as [v Hin|e Hreach IH Hedge].
  - eapply entries_in; eauto.
  - eapply out_target_in; eauto.
Qed.
