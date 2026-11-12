(** * Function calls and resolver graphs

    Call inventories retain site and target order while graph vertices use encoded function keys.
    For example, a recursive call contributes a successor equal to its caller.
    Builds on: Program.SemanticsSig and first-order graph data. *)

From Stdlib Require Import List NArith.
From Argent Require Import Time Std BigO.
From Galois.Base Require Import KeySig.
From Galois.Graph Require Import Data Spec.
From Galois.Program Require Import SemanticsSig.

Record call_edge (F S : Type) := CallEdge {
  edge_site : S;
  edge_callee : F
}.

Arguments CallEdge {F S}.
Arguments edge_site {F S}.
Arguments edge_callee {F S}.

(** Each site contributes its targets in resolver order, including repeated occurrences. *)
Definition call_edges {F S} (resolve : S -> list F) (sites : list S) : list (call_edge F S) :=
  flat_map (fun site => map (CallEdge site) (resolve site)) sites.

TimeFun call_edges.

(** Suspended frames are linked from the current callee toward the outermost caller. *)
Fixpoint frames_linked {F S} (sites : F -> list S) (caller : S -> F)
    (resolve : S -> list F) (callee : F) (stack : list (F * S)) : Prop :=
  match stack with
  | nil => True
  | (f, site) :: rest =>
    caller site = f /\ In site (sites f) /\ In callee (resolve site) /\
      frames_linked sites caller resolve f rest
  end.

Module Type CALLS_OPS (P : TYPE) (F S : KEY_OPS).
  Parameter functions roots : P.t -> list F.t.
  Parameter sites_of : P.t -> F.t -> list S.t.
  Parameter caller_of : P.t -> S.t -> F.t.
  Parameter resolve : P.t -> S.t -> list F.t.
  Parameter call_graph : P.t -> digraph.
End CALLS_OPS.

Module Type CALLS_SPEC (P : TYPE) (F S : KEY_OPS) (Import C : CALLS_OPS P F S).
  Definition out_edges p f := call_edges (resolve p) (sites_of p f).
  Definition sites p := flat_map (sites_of p) (functions p).
  Definition targets p := flat_map (resolve p) (sites p).
  Definition graph_roots p := map F.encode (roots p).
  Definition function_width p :=
    fold_right Nat.max 0%nat (map (fun f => Pos.size_nat (F.encode f))
      (functions p ++ targets p)).
End CALLS_SPEC.

Module Type CALLS_LAWS (P : TYPE) (F S : KEY) (Import C : CALLS_OPS P F S).
  (* spec: wf *)
  Parameter wf : P.t -> Prop.
  (** A well-formed inventory lists each function once. *)
  Parameter functions_nodup : forall p, wf p -> NoDup (functions p).
  (** Every root belongs to the function inventory. *)
  Parameter roots_listed : forall p, wf p -> incl (roots p) (functions p).
  (** A listed site's declared caller is its inventory owner. *)
  Parameter sites_caller : forall p f site, wf p -> In site (sites_of p f) ->
    caller_of p site = f /\ In f (functions p).
  (** Every resolver target belongs to the function inventory. *)
  Parameter resolve_listed : forall p site f, wf p -> In f (resolve p site) ->
    In f (functions p).
  (** Graph vertices retain function inventory order. *)
  Parameter call_graph_nodes : forall p, verts (call_graph p) = map F.encode (functions p).
  (** Graph successors retain each site's target order and multiplicity. *)
  Parameter call_graph_out : forall p f, wf p -> In f (functions p) ->
    succs (call_graph p) (F.encode f) =
      map (fun e => F.encode (edge_callee e)) (call_edges (resolve p) (sites_of p f)).
  (** A closed inventory produces a well-formed encoded graph. *)
  Parameter call_graph_wf : forall p, wf p -> wf_graph (call_graph p).
End CALLS_LAWS.

Module Type CALLS (P : TYPE) (F S : KEY) :=
  CALLS_OPS P F S <+ CALLS_SPEC P F S <+ CALLS_LAWS P F S.

Module Type CALLS_TIME (P : TYPE) (F S : KEY_T) (Import C : CALLS P F S).
  Parameter T_functions T_roots : P.t -> N.
  Parameter T_sites_of : P.t -> F.t -> N.
  Parameter T_caller_of : P.t -> S.t -> N.
  Parameter T_resolve : P.t -> S.t -> N.
  Parameter T_call_graph : P.t -> N.
  Parameter c_calls : N.
  Definition call_graph_work p :=
    (T_functions p +
      fold_right N.add 0%N (map (fun f => T_sites_of p f + F.T_encode f)%N (functions p)) +
      fold_right N.add 0%N (map (T_resolve p) (sites p)) +
      fold_right N.add 0%N (map F.T_encode (targets p)) +
      N.of_nat (length (functions p) + length (sites p) + length (targets p) + 1) *
        N.of_nat (function_width p + 1))%N.
  (** Graph construction charges inventory readers, target encodings and adjacency insertion. *)
  Parameter T_call_graph_le : forall p,
    (T_call_graph p <= c_calls * call_graph_work p)%N.
  (** Call graphs have the aggregate inventory and bit-width bound. *)
  Parameter call_graph_bigO : bigO (fun _ : P.t => True) call_graph_work T_call_graph.
End CALLS_TIME.

Module Type CALLS_T (P : TYPE) (F S : KEY_T) := CALLS P F S <+ CALLS_TIME P F S.

Module Type CALLS_PLAN (P : TYPE) (F S : KEY_T) (Import C : CALLS_T P F S).
  (** A site contributes exactly its tagged resolver targets to the outgoing list. *)
  Parameter F1_call_edge : forall p f site target,
    In site (sites_of p f) -> In target (resolve p site) ->
    In (CallEdge site target) (out_edges p f).
End CALLS_PLAN.

Module Type CALLS_ALL (P : TYPE) (F S : KEY_T) := CALLS_T P F S <+ CALLS_PLAN P F S.

Module Type CALLS_LINK (P : TYPE) (F S : KEY) (C : CALLS P F S) (M : SEMANTICS P).
  Parameter here : M.state -> F.t.
  Parameter frames : M.state -> list (F.t * S.t).
  Definition active s := here s :: map fst (frames s).
  (** Initial states start in a root function with an empty frame stack. *)
  Parameter initial_roots : forall p s, M.initial p s ->
    In (here s) (C.roots p) /\ frames s = nil.
  (** Every active function in a reachable state is listed. *)
  Parameter frames_listed : forall p s,
    reachable (M.initial p) (M.step p) s -> incl (active s) (C.functions p).
  (** A step stays in its frame, pushes a resolved call, or pops its matching caller. *)
  Parameter step_shape : forall p s t,
    reachable (M.initial p) (M.step p) s -> M.step p s t ->
    (here t = here s /\ frames t = frames s) \/
    (exists site, In site (C.sites_of p (here s)) /\ In (here t) (C.resolve p site) /\
      frames t = (here s, site) :: frames s) \/
    (exists f site, frames s = (f, site) :: frames t /\ here t = f).
End CALLS_LINK.

Module Type CALLS_SOUND (P : TYPE) (F S : KEY) (C : CALLS P F S)
    (M : SEMANTICS P) (L : CALLS_LINK P F S C M).
  (** Every reachable stack retains the resolver links of its pushes. *)
  Parameter reachable_frames_linked : forall p s, C.wf p ->
    reachable (M.initial p) (M.step p) s ->
    frames_linked (C.sites_of p) (C.caller_of p) (C.resolve p) (L.here s) (L.frames s).
  (** Each active function is reachable from a root in the encoded call graph. *)
  Parameter active_reachable : forall p s f, C.wf p ->
    reachable (M.initial p) (M.step p) s -> In f (L.active s) ->
    reach (C.call_graph p) (C.graph_roots p) (F.encode f).
End CALLS_SOUND.
