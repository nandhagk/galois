(** * Control-flow graph presentations

    Presentations expose entries, edges and optional adjacency indexes.
    For example, incoming adjacency lists the edges whose destination is the requested node.
    Builds on: Base.KeySig and Program.SemanticsSig. *)

From Stdlib Require Import List.
From Galois.Base Require Import KeySig.
From Galois.Program Require Import SemanticsSig.

Module Type CFG_OPS (P : TYPE) (N : KEY_OPS) (E : TYPE).
  Parameter entries : P.t -> list N.t.
  Parameter edges : P.t -> list E.t.
  Parameter src : P.t -> E.t -> N.t.
  Parameter dst : P.t -> E.t -> N.t.
End CFG_OPS.

Module Type CFG_ADJ_OPS (P : TYPE) (N : KEY_OPS) (E : TYPE)
    (Import C : CFG_OPS P N E).
  Parameter nodes : P.t -> list N.t.
  Parameter out : P.t -> N.t -> list E.t.
  Parameter inc : P.t -> N.t -> list E.t.
End CFG_ADJ_OPS.

Module Type CFG_INDEXED_OPS (P : TYPE) (N : KEY_OPS) (E : TYPE) :=
  CFG_OPS P N E <+ CFG_ADJ_OPS P N E.

Module Type CFG_LAWS (P : TYPE) (N : KEY) (E : TYPE)
    (Import C : CFG_INDEXED_OPS P N E).
  (* spec: wf *)
  Parameter wf : P.t -> Prop.
  (** Entries belong to the node domain. *)
  Parameter entries_nodes : forall p n, wf p -> In n (entries p) -> In n (nodes p).
  (** Listed edges have both endpoints in the node domain. *)
  Parameter edges_nodes : forall p e, wf p -> In e (edges p) ->
    In (src p e) (nodes p) /\ In (dst p e) (nodes p).
  (** Outgoing adjacency lists exactly the edges with the requested source. *)
  Parameter out_spec : forall p n e, wf p ->
    (In e (out p n) <-> In e (edges p) /\ src p e = n).
  (** Incoming adjacency lists exactly the edges with the requested destination. *)
  Parameter inc_spec : forall p n e, wf p ->
    (In e (inc p n) <-> In e (edges p) /\ dst p e = n).
End CFG_LAWS.

Module Type CFG (P : TYPE) (N : KEY) (E : TYPE) :=
  CFG_INDEXED_OPS P N E <+ CFG_LAWS P N E.

Module Type CFG_TIME (P : TYPE) (N : KEY_T) (E : TYPE)
    (Import C : CFG_INDEXED_OPS P N E).
  Parameter T_entries T_edges T_nodes : P.t -> nat.
  Parameter T_src T_dst : P.t -> E.t -> nat.
  Parameter T_out T_inc : P.t -> N.t -> nat.
  Parameter c_cfg : nat.
  (** Entry enumeration pays for its output. *)
  Parameter T_entries_le : forall p, T_entries p <= c_cfg * (length (entries p) + 1).
  (** Edge enumeration pays for its output. *)
  Parameter T_edges_le : forall p, T_edges p <= c_cfg * (length (edges p) + 1).
  (** Node enumeration pays for its output. *)
  Parameter T_nodes_le : forall p, T_nodes p <= c_cfg * (length (nodes p) + 1).
  (** Source projection has bounded cost. *)
  Parameter T_src_le : forall p e, T_src p e <= c_cfg.
  (** Destination projection has bounded cost. *)
  Parameter T_dst_le : forall p e, T_dst p e <= c_cfg.
  (** Outgoing lookup pays for the key and its output. *)
  Parameter T_out_le : forall p n, T_out p n <= c_cfg * (N.bits n + length (out p n) + 1).
  (** Incoming lookup pays for the key and its output. *)
  Parameter T_inc_le : forall p n, T_inc p n <= c_cfg * (N.bits n + length (inc p n) + 1).
End CFG_TIME.

Module Type CFG_T (P : TYPE) (N : KEY_T) (E : TYPE) :=
  CFG P N E <+ CFG_TIME P N E.

Module Type CFG_LINK (P : TYPE) (N : KEY) (E : TYPE)
    (C : CFG_OPS P N E) (M : SEMANTICS P).
  Parameter point : M.state -> N.t.
  Parameter taken : P.t -> M.state -> M.state -> E.t -> Prop.
  (** Initial states occur at entries. *)
  Parameter init_entry : forall p s, M.initial p s -> In (point s) (C.entries p).
  (** Every reachable transition follows a listed edge between its actual endpoints. *)
  Parameter step_edge : forall p s s1,
    reachable (M.initial p) (M.step p) s -> M.step p s s1 ->
    exists e, taken p s s1 e /\ In e (C.edges p) /\
      C.src p e = point s /\ C.dst p e = point s1.
End CFG_LINK.
