(** * Interference and colouring contracts

    Colouring decides each interference vertex by assigning a register or spilling it.
    For example, adjacent assigned vertices must receive different colours.
    Builds on: BaseMap and BaseSet. *)

From Stdlib Require Import List Arith PArith.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.

Module Interference.

Record t := Make {
  vertices : FinSet.t positive;
  adjacent : Map.t positive (FinSet.t positive)
}.

(** Adjacency is observed through the declared neighbour set at the source ID. *)
Definition interferes ig u v :=
  exists neighbours, Map.get positive_encoding u (adjacent ig) = Some neighbours /\
    FinSet.mem positive_encoding v neighbours = true.

(** Interference is a finite undirected irreflexive graph on the declared vertices. *)
Record laws (ig : t) : Prop := {
  vertices_wf : FinSet.wf positive_encoding (vertices ig);
  adjacent_wf : Map.wf positive_encoding (adjacent ig);
  neighbours_wf : forall u ns, Map.get positive_encoding u (adjacent ig) = Some ns ->
    FinSet.wf positive_encoding ns;
  endpoints : forall u v, interferes ig u v ->
    FinSet.mem positive_encoding u (vertices ig) = true /\
    FinSet.mem positive_encoding v (vertices ig) = true;
  symmetric : forall u v, interferes ig u v -> interferes ig v u;
  irreflexive : forall v, ~ interferes ig v v
}.

End Interference.

Module Colour.

Record problem := Problem {
  interference : Interference.t;
  k : nat;
  precolours : Map.t positive nat;
  moves : list (positive * positive)
}.

Record result := Result {
  colours : Map.t positive nat;
  spilled : list positive
}.

(** Proper colouring covers vertices, respects interference and retains every precolour. *)
Record proper (p : problem) (r : result) : Prop := {
  colour_below_k : forall v c, Map.get positive_encoding v (colours r) = Some c -> c < k p;
  vertex_decided : forall v,
    FinSet.mem positive_encoding v (Interference.vertices (interference p)) = true ->
    (exists c, Map.get positive_encoding v (colours r) = Some c) \/ In v (spilled r);
  spilled_uncoloured : forall v, In v (spilled r) ->
    Map.get positive_encoding v (colours r) = None;
  adjacent_differ : forall u v cu cv, Interference.interferes (interference p) u v ->
    Map.get positive_encoding u (colours r) = Some cu ->
    Map.get positive_encoding v (colours r) = Some cv -> cu <> cv;
  precoloured_kept : forall v c, Map.get positive_encoding v (precolours p) = Some c ->
    Map.get positive_encoding v (colours r) = Some c
}.

End Colour.
