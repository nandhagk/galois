(** * Semantic links to control-flow and variable presentations

    Links classify steps without being needed to run an analysis.
    For example, an administrative step can keep its control point unchanged.
    Builds on: ProgramSteps and ProgramCfg. *)

From Stdlib Require Import List.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramSemantics ProgramSteps ProgramCfg.

Module Link.

(** A link assigns points and classifies taken edges and stationary transitions. *)
Record t (S O N E : Type) := Make {
  point : S -> N;
  taken : S -> list O -> S -> E -> Prop;
  stays : S -> list O -> S -> Prop
}.
Arguments Make {S O N E}.
Arguments point {S O N E}.
Arguments taken {S O N E}.
Arguments stays {S O N E}.

End Link.

(** Every reachable transition either stays or follows a correctly sourced graph edge. *)
Record link_laws {S O N E} (m : semantics S O) (g : Graph.t N E)
    (lk : Link.t S O N E) : Prop := {
  cfg_wf : graph_wf g;
  entry_points : forall s, initial m s -> In (Link.point lk s) (Graph.entries g);
  edge_covers : on_steps m (fun s l s' =>
    Link.stays lk s l s' \/ exists e, Link.taken lk s l s' e);
  taken_edge : forall e, on_steps m (fun s l s' => Link.taken lk s l s' e ->
    In e (Graph.out g (Link.point lk s)) /\ Graph.target g e = Link.point lk s');
  stays_point : on_steps m (fun s l s' =>
    Link.stays lk s l s' -> Link.point lk s' = Link.point lk s)
}.
Arguments cfg_wf {S O N E m g lk}.
Arguments entry_points {S O N E m g lk}.
Arguments edge_covers {S O N E m g lk}.
Arguments taken_edge {S O N E m g lk}.
Arguments stays_point {S O N E m g lk}.

(** Variable laws preserve unwritten values and determine steps and endings from their inputs.
    Edge and variable quantifiers precede [on_steps], commuting the legacy quantifiers.
    [no_stays] and [exits_determine] retain their original domains because they are not
    restricted to transitions in the legacy contract. *)
Record var_laws {S O N E X C} (m : semantics S O) (en : endings S)
    (p : Vars.t N E X) (lk : Link.t S O N E) (get : S -> X -> C) : Prop := {
  view_laws : link_laws m (Cfg.graph (Vars.cfg p)) lk;
  no_stays : forall s l s', ~ Link.stays lk s l s';
  defs_frame : forall e x, on_steps m (fun s l s' =>
    Link.taken lk s l s' e -> ~ In x (Vars.defs p e) -> get s' x = get s x);
  uses_determine : forall t e, on_steps m (fun s l s' =>
    reachable_state m t -> Link.point lk t = Link.point lk s ->
    Link.taken lk s l s' e ->
    (forall x, In x (Vars.uses p e) -> get s x = get t x) ->
    exists t', step m t l t' /\ Link.taken lk t l t' e /\
      forall x, In x (Vars.defs p e) -> get s' x = get t' x);
  exits_determine : forall s t, reachable_state m s -> reachable_state m t ->
    Link.point lk t = Link.point lk s ->
    (forall x, In x (Vars.exits p (Link.point lk s)) -> get s x = get t x) ->
    (final en s <-> final en t) /\ (trapped en s <-> trapped en t) /\
    (stopped en s <-> stopped en t)
}.
Arguments view_laws {S O N E X C m en p lk get}.
Arguments no_stays {S O N E X C m en p lk get}.
Arguments defs_frame {S O N E X C m en p lk get}.
Arguments uses_determine {S O N E X C m en p lk get}.
Arguments exits_determine {S O N E X C m en p lk get}.
