(** * Control-flow and variable presentations

    Presentations carry the encodings and costed callbacks used by analyses.
    For example, an empty graph has no edges or variable occurrences.
    Builds on: CostList, BaseSet and GraphModel. *)

From Stdlib Require Import List NArith.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseEq BaseSet.
From Galois.Graph Require Import GraphModel.
Import List.ListNotations Cost.Notations.

Module Cfg.

(** A CFG packages a graph and its node and edge dictionaries without laws. *)
Record t (N E : Type) := Make {
  graph : Graph.t N E;
  node_enc : encoding N;
  edge_enc : encoding E
}.
Arguments Make {N E}.
Arguments graph {N E}.
Arguments node_enc {N E}.
Arguments edge_enc {N E}.

(** Edges occur in node order followed by each node's outgoing order. *)
Definition edges {N E} (c : t N E) : list E :=
  flat_map (Graph.out (graph c)) (Graph.nodes (graph c)).

(** Edge membership is membership in an outgoing list of a listed node. *)
Theorem edges_spec {N E} (c : t N E) e :
  In e (edges c) <->
  exists n, In n (Graph.nodes (graph c)) /\ In e (Graph.out (graph c) n).
Proof.
  apply in_flat_map.
Qed.

Arguments edges {N E} c : simpl never.

End Cfg.

Module Vars.

(** Edge uses precede definitions and exits expose observations without a step. *)
Record t (N E X : Type) := Make {
  cfg : Cfg.t N E;
  var_enc : encoding X;
  uses_c : E -> Cost.t (list X);
  defs_c : E -> Cost.t (list X);
  exits_c : N -> Cost.t (list X)
}.
Arguments Make {N E X}.
Arguments cfg {N E X}.
Arguments var_enc {N E X}.
Arguments uses_c {N E X}.
Arguments defs_c {N E X}.
Arguments exits_c {N E X}.

Definition uses {N E X} (p : t N E X) e := Cost.value (uses_c p e).
Definition defs {N E X} (p : t N E X) e := Cost.value (defs_c p e).
Definition exits {N E X} (p : t N E X) n := Cost.value (exits_c p n).

(** Pure callbacks are client primitives charged one tick per call. *)
Definition of_pure {N E X} cfg enc (uses defs : E -> list X) (exits : N -> list X) :=
  @Make N E X cfg enc (Cost.lift (fun _ => 1%N) uses)
    (Cost.lift (fun _ => 1%N) defs) (Cost.lift (fun _ => 1%N) exits).

(** The variable universe is prepared once and deduplicated in canonical key order. *)
Definition universe {N E X} (p : t N E X) : list X :=
  FinSet.elements (FinSet.of_list (var_enc p)
    (flat_map (fun e => uses p e ++ defs p e) (Cfg.edges (cfg p)) ++
      flat_map (exits p) (Graph.nodes (Cfg.graph (cfg p))))).

(** With an injective dictionary, the universe contains exactly the syntactic occurrences. *)
Theorem universe_spec {N E X} (p : t N E X) x :
  encoding_laws (var_enc p) ->
  (In x (universe p) <->
    (exists e, In e (Cfg.edges (cfg p)) /\ (In x (uses p e) \/ In x (defs p e))) \/
    (exists n, In n (Graph.nodes (Cfg.graph (cfg p))) /\ In x (exits p n))).
Proof.
  intro HE; unfold universe.
  rewrite (FinSet.elements_spec _ HE) by apply FinSet.wf_of_list.
  rewrite FinSet.mem_of_list, existsb_exists.
  split.
  - intros [y [Hin Heq]].
    apply (eqb_true_iff _ HE) in Heq; subst y.
    apply in_app_iff in Hin; destruct Hin as [Hin|Hin]; [left|right].
    + apply in_flat_map in Hin; destruct Hin as [e [Hedge Hin]].
      exists e; split; [exact Hedge|apply in_app_iff; exact Hin].
    + apply in_flat_map in Hin; exact Hin.
  - intro Hin; exists x; split; [|apply (eqb_true_iff _ HE); reflexivity].
    apply in_app_iff; destruct Hin as [[e [Hedge Hin]]|Hin]; [left|right].
    + apply in_flat_map; exists e; split; [exact Hedge|apply in_app_iff; exact Hin].
    + apply in_flat_map; exact Hin.
Qed.

Arguments universe {N E X} p : simpl never.

End Vars.
