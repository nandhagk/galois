(** * Matched call-site stacks

    Exploded edges preserve, push or pop the top call site.
    For example, a return at site p cannot pop a different site q.
    Builds on: FrameworkIfds and ProgramCfg. *)

From Stdlib Require Import List Arith Lia.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramCfg ProgramIcfg.
From Galois.Framework Require Import FrameworkIfds.
Import List.ListNotations.

Module Stack.

(** Configurations retain the point, optional fact and innermost-first stack. *)
Definition config N D P := (N * option D * list P)%type.

(** Steps require a listed graph edge and an actual exploded flow alternative. *)
Inductive step {N E P D} (I : Ifds.t N E P D) :
    config N D P -> E -> config N D P -> Prop :=
  | internal e x y st :
      In e (Cfg.edges (Icfg.cfg (Ifds.icfg I))) ->
      Icfg.edge_kind (Ifds.icfg I) e = Icfg.Internal ->
      In y (Ifds.flow I e x) ->
      step I (Graph.source (Cfg.graph (Icfg.cfg (Ifds.icfg I))) e, x, st) e
        (Graph.target (Cfg.graph (Icfg.cfg (Ifds.icfg I))) e, y, st)
  | call e p x y st :
      In e (Cfg.edges (Icfg.cfg (Ifds.icfg I))) ->
      Icfg.edge_kind (Ifds.icfg I) e = Icfg.Call p ->
      In y (Ifds.flow I e x) ->
      step I (Graph.source (Cfg.graph (Icfg.cfg (Ifds.icfg I))) e, x, st) e
        (Graph.target (Cfg.graph (Icfg.cfg (Ifds.icfg I))) e, y, p :: st)
  | return_ e p x y st :
      In e (Cfg.edges (Icfg.cfg (Ifds.icfg I))) ->
      Icfg.edge_kind (Ifds.icfg I) e = Icfg.Return p ->
      In y (Ifds.flow I e x) ->
      step I (Graph.source (Cfg.graph (Icfg.cfg (Ifds.icfg I))) e, x, p :: st) e
        (Graph.target (Cfg.graph (Icfg.cfg (Ifds.icfg I))) e, y, st).

(** Finite paths retain all intermediate stack matches. *)
Inductive path {N E P D} (I : Ifds.t N E P D) :
    config N D P -> config N D P -> Prop :=
  | refl c : path I c c
  | next c e c' c'' : step I c e c' -> path I c' c'' -> path I c c''.

(** Balanced paths begin and end with an empty stack. *)
Definition balanced {N E P D} (I : Ifds.t N E P D) a d b d' :=
  path I (a, d, []) (b, d', []).

(** Concatenating paths retains the same intermediate configuration. *)
Theorem path_trans {N E P D} (I : Ifds.t N E P D) c d e :
  path I c d -> path I d e -> path I c e.
Proof.
  intros Hpath Htail; induction Hpath as [c|c edge d z Hstep Hpath IH].
  - exact Htail.
  - eapply next; [exact Hstep|apply IH; exact Htail].
Qed.

(** Bounded contexts retain the innermost k sites. *)
Definition truncate {P} k (st : list P) := firstn k st.

(** Truncation has length min k length, including the zero bound. *)
Theorem truncate_length {P} k (st : list P) :
  length (truncate k st) = Nat.min k (length st).
Proof.
  apply length_firstn.
Qed.

End Stack.
