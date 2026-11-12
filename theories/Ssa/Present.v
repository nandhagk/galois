(** * Language control-flow occurrences

    Edges retain the source block and the selected exit arm.
    For example, two arms aimed at the same block remain distinct.
    Builds on: Ssa.Lang. *)

From Stdlib Require Import List PArith.
From Argent Require Import Time Std.
From Galois.Base Require Import Code.
From Galois.Ssa Require Import Lang.
Import List.ListNotations.

Inductive exit_arm :=
  | Jump_arm
  | True_arm
  | False_arm.

Record block_edge := BlockEdge {
  edge_source : positive;
  edge_arm : exit_arm;
  edge_target : positive;
  edge_arguments : list positive
}.

Definition exit_edges {G} (source : positive) (e : exit positive G) : list block_edge :=
  match e with
  | Jump target args => [BlockEdge source Jump_arm target args]
  | Branch _ _ yes yes_args no no_args =>
      [BlockEdge source True_arm yes yes_args; BlockEdge source False_arm no no_args]
  | Return _ => []
  end.
TimeFun exit_edges.

Definition language_edges {K G} (p : func positive K G) : list block_edge :=
  flat_map (fun item => exit_edges (fst item) (term _ _ _ (snd item))) (blocks _ _ _ p).
TimeFun language_edges.
