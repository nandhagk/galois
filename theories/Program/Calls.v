(** * Function calls and resolver graphs

    Inventories and resolver tables retain site and target order.
    For example, repeated targets produce repeated graph successors.
    Builds on: Program.CallsSig and Base.Trie. *)

From Stdlib Require Import List NArith.
From Argent Require Import Time Tactics Std BigO.
From Galois.Base Require Import KeySig Trie.
From Galois.Graph Require Import Data Spec.
From Galois.Program Require Import SemanticsSig CallsSig.

Definition call_edge_target {F S} (edge : call_edge F S) : F :=
  match edge with
  | CallEdge _ target => target
  end.

TimeFun call_edge_target.

Record calls_tables (F S : Type) := CallsTables {
  call_functions : list F;
  call_roots : list F;
  call_sites : ptrie (list S);
  call_callers : ptrie F;
  call_default_caller : F;
  call_targets : ptrie (list F)
}.

Arguments CallsTables {F S}.
Arguments call_functions {F S}.
Arguments call_roots {F S}.
Arguments call_sites {F S}.
Arguments call_callers {F S}.
Arguments call_default_caller {F S}.
Arguments call_targets {F S}.

TimeFun call_functions.
TimeFun call_roots.
TimeFun call_sites.
TimeFun call_callers.
TimeFun call_default_caller.
TimeFun call_targets.

Module Type CALLS_DATA (P : TYPE) (F S : KEY_OPS).
  Parameter tables : P.t -> calls_tables F.t S.t.
End CALLS_DATA.

Module Type CALLS_DATA_TIME (P : TYPE) (F S : KEY_T)
    (Import D : CALLS_DATA P F S).
  Parameter T_tables : P.t -> N.
End CALLS_DATA_TIME.

Module Type CALLS_DATA_T (P : TYPE) (F S : KEY_T) :=
  CALLS_DATA P F S <+ CALLS_DATA_TIME P F S.

Module CallsCode (P : TYPE) (F S : KEY_OPS) (D : CALLS_DATA P F S)
    <: CALLS_OPS P F S.
  Definition functions p := call_functions (D.tables p).
  Definition roots p := call_roots (D.tables p).
  Definition sites_of p f :=
    match trie_get (F.encode f) (call_sites (D.tables p)) with
    | Some sites => sites
    | None => nil
    end.
  Definition caller_of p site :=
    match trie_get (S.encode site) (call_callers (D.tables p)) with
    | Some f => f
    | None => call_default_caller (D.tables p)
    end.
  Definition resolve p site :=
    match trie_get (S.encode site) (call_targets (D.tables p)) with
    | Some fs => fs
    | None => nil
    end.
  Definition call_graph p :=
    Digraph (map F.encode (functions p))
      (fold_left (fun adj f => PTrieCode.set (F.encode f)
        (map (fun e => F.encode (call_edge_target e))
          (call_edges (resolve p) (sites_of p f))) adj)
        (functions p) PTrieCode.empty).
End CallsCode.

Module Calls (P : TYPE) (F S : KEY) (D : CALLS_DATA P F S) <: CALLS P F S.
  Include CallsCode P F S D.
  Include CALLS_SPEC P F S.

  Definition wf p :=
    NoDup (functions p) /\ incl (roots p) (functions p) /\
    (forall f site, In site (sites_of p f) ->
      caller_of p site = f /\ In f (functions p)) /\
    (forall site f, In f (resolve p site) -> In f (functions p)).

  Lemma functions_nodup : forall p, wf p -> NoDup (functions p).
  Proof. Admitted.
  Lemma roots_listed : forall p, wf p -> incl (roots p) (functions p).
  Proof. Admitted.
  Lemma sites_caller : forall p f site, wf p -> In site (sites_of p f) ->
    caller_of p site = f /\ In f (functions p).
  Proof. Admitted.
  Lemma resolve_listed : forall p site f, wf p -> In f (resolve p site) ->
    In f (functions p).
  Proof. Admitted.
  Lemma call_graph_nodes : forall p, verts (call_graph p) = map F.encode (functions p).
  Proof.
    reflexivity.
  Qed.
  Lemma call_graph_out : forall p f, wf p -> In f (functions p) ->
    succs (call_graph p) (F.encode f) =
      map (fun e => F.encode (edge_callee e)) (call_edges (resolve p) (sites_of p f)).
  Proof. Admitted. (* CONVERT: graph_out: The reference Graph.out was not found. *)
  Lemma call_graph_wf : forall p, wf p -> wf_graph (call_graph p).
  Proof. Admitted. (* CONVERT: call_graph_wf: Hnodes has type NoDup (functions p). *)
End Calls.

Module CallsSound (P : TYPE) (F S : KEY) (C : CALLS P F S)
    (M : SEMANTICS P) (L : CALLS_LINK P F S C M) <: CALLS_SOUND P F S C M L.
  Lemma reachable_frames_linked : forall p s, C.wf p ->
    reachable (M.initial p) (M.step p) s ->
    frames_linked (C.sites_of p) (C.caller_of p) (C.resolve p) (L.here s) (L.frames s).
  Proof. Admitted. (* CONVERT: reachable_frames_linked: Unable to unify the induction goal. *)

  Lemma active_reachable : forall p s f, C.wf p ->
    reachable (M.initial p) (M.step p) s -> In f (L.active s) ->
    reach (C.call_graph p) (C.graph_roots p) (F.encode f).
  Proof. Admitted. (* CONVERT: active_reachable_in_call_graph: Unable to unify the induction goal. *)
End CallsSound.

Module CallsT (P : TYPE) (F S : KEY_T) (D : CALLS_DATA_T P F S)
    <: CALLS_ALL P F S.
  Include Calls P F S D.
  TimeFun functions.
  TimeFun roots.
  TimeFun sites_of.
  TimeFun caller_of.
  TimeFun resolve.
  TimeFun call_graph.

  Definition call_graph_work p :=
    (T_functions p +
      fold_right N.add 0%N (map (fun f => T_sites_of p f + F.T_encode f)%N (functions p)) +
      fold_right N.add 0%N (map (T_resolve p) (sites p)) +
      fold_right N.add 0%N (map F.T_encode (targets p)) +
      N.of_nat (length (functions p) + length (sites p) + length (targets p) + 1) *
        N.of_nat (function_width p + 1))%N.

  Definition c_calls : N := 1%N. (* STUB *)

  (** Graph construction charges the inventory readers and encoded adjacency work. *)
  Lemma T_call_graph_le : forall p,
    (T_call_graph p <= c_calls * call_graph_work p)%N.
  Proof. Admitted. (* STUB *)

  (** Call graph construction has the aggregate reader and bit-width bound. *)
  Lemma call_graph_bigO : bigO (fun _ : P.t => True) call_graph_work T_call_graph.
  Proof. Admitted. (* STUB *)

  (** A site contributes exactly its resolver targets to its outgoing list. *)
  Lemma F1_call_edge : forall p f site target,
    In site (sites_of p f) -> In target (resolve p site) ->
    In (CallEdge site target) (out_edges p f).
  Proof. Admitted. (* STUB *)
End CallsT.
