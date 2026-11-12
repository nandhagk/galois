(** * Function calls and resolver graphs

    Inventories and resolver tables retain site and target order.
    For example, repeated targets produce repeated graph successors.
    Builds on: Program.CallsSig and Base.Trie. *)

From Stdlib Require Import List.
From Galois.Base Require Import KeySig Trie.
From Galois.Graph Require Import Data Spec.
From Galois.Program Require Import SemanticsSig CallsSig.

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

Module Type CALLS_DATA (P : TYPE) (F S : KEY_OPS).
  Parameter tables : P.t -> calls_tables F.t S.t.
End CALLS_DATA.

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
        (map (fun e => F.encode (edge_callee e)) (call_edges (resolve p) (sites_of p f))) adj)
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
