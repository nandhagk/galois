(** * Control-flow graph observations

    Preparation retains edge occurrences and their adjacency order.
    For example, a repeated edge receives distinct occurrence numbers.

    Groups:
    - [OccurrenceTests] Repeated edges are numbered from 0 in their order.
    - [EdgeTests] A prepared program lists its edges, and an unprepared one has none.
    - [AdjacencyTests] Outgoing and incoming lists keep the order of the edges.

    Builds on: Program.Cfg. *)

From Stdlib Require Import List Bool.
From Galois.Base Require Import KeySig Key.
From Galois.Program Require Import CfgSig Cfg.
Import List.ListNotations.

(** * Fixtures *)

Module Prog <: TYPE. Definition t := bool. End Prog.
Module Edge <: TYPE. Definition t := nat. End Edge.

(** A program with edges 0, 1 and 2 when it is true: edge 0 runs from node 0 to node 1, edge 1 is a self-loop at node 1, and edge 2 runs from node 1 to node 2. *)
Module Three <: CFG_OPS Prog NatKeyCode Edge.
  Definition entries (p : bool) := if p then [0] else [].
  Definition edges (p : bool) := if p then [0; 1; 2] else [].
  Definition src (_ : bool) e := match e with 0 => 0 | _ => 1 end.
  Definition dst (_ : bool) e := match e with 0 => 1 | 1 => 1 | _ => 2 end.
End Three.

Module Prep := CfgCode Prog NatKeyCode Edge Three.
Module View := PreparedCfg Prog NatKeyCode Edge Three.

(** * Occurrences *)

Module OccurrenceTests.

  (** Three copies of the edge 7 are numbered 0, 1 and 2. *)
  Example repeats_numbered_from_zero :
    occurrences [7; 7; 7] 0 = [(7, 0); (7, 1); (7, 2)].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Two copies of the edge 7 are numbered 0 and 1. *)
  Example two_copies_numbered :
    occurrences [7; 7] 0 = [(7, 0); (7, 1)].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** An empty list of edges has no occurrences. *)
  Example empty_list_no_occurrences :
    occurrences (@nil nat) 0 = [].
  Proof.
    vm_compute; reflexivity.
  Qed.

End OccurrenceTests.

(** * Edges *)

Module EdgeTests.

  (** A prepared program with three edges lists them in order 0, 1 and 2. *)
  Example prepared_edges_in_order :
    View.Ops.edges (Prep.prepare true) = [0; 1; 2].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** An unprepared program has no edges. *)
  Example unprepared_program_no_edges :
    View.Ops.edges (Prep.prepare false) = [].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Edge 1 starts and ends at node 1. *)
  Example self_loop_endpoints :
    (Three.src true 1, Three.dst true 1) = (1, 1).
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A node that the program does not have has no outgoing edges. *)
  Example missing_node_no_outgoing :
    View.Adj.out (Prep.prepare true) 9 = [].
  Proof.
    vm_compute; reflexivity.
  Qed.

End EdgeTests.

(** * Adjacency *)

Module AdjacencyTests.

  (** The outgoing edges of node 1 are edges 1 and 2, in that order. *)
  Example outgoing_in_order :
    View.Adj.out (Prep.prepare true) 1 = [1; 2].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The incoming edges of node 1 are edges 0 and 1, in that order. *)
  Example incoming_in_order :
    View.Adj.inc (Prep.prepare true) 1 = [0; 1].
  Proof.
    vm_compute; reflexivity.
  Qed.

End AdjacencyTests.
