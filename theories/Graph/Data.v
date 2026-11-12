(** * First-order graph data

    Graphs store successor lists and prepared graphs cache predecessor lists and sizes.
    For example, a missing adjacency binding denotes an empty list.
    Builds on: Base tries and Argent time derivation. *)

From Stdlib Require Import PArith NArith List.
From Argent Require Import Time Std.
From Galois.Base Require Import Key Trie.

Module TimeHelpers.
  Module N.
    TimeFun BinNat.N.of_nat.
  End N.
End TimeHelpers.

Record digraph := Digraph {
  verts : list positive;
  succ : ptrie (list positive)
}.

TimeFun verts.
TimeFun succ.

Record prepared := Prepared {
  base : digraph;
  pred : ptrie (list positive);
  nv : N;
  ne : N
}.

TimeFun base.

Definition succs (g : digraph) (v : positive) : list positive :=
  match g with
  | Digraph _ adjacency =>
    match trie_get v adjacency with
    | Some l => l
    | None => nil
    end
  end.

TimeFun succs.

Definition preds (g : prepared) (v : positive) : list positive :=
  match g with
  | Prepared _ adjacency _ _ =>
    match trie_get v adjacency with
    | Some l => l
    | None => nil
    end
  end.

TimeFun preds.

Definition nodes (g : prepared) : list positive :=
  match g with
  | Prepared (Digraph vertices _) _ _ _ => vertices
  end.

TimeFun nodes.

Inductive wto :=
  | WNil
  | WVertex (v : positive) (rest : wto)
  | WLoop (head : positive) (body rest : wto).

Record scc := Scc {
  comp : ptrie positive;
  comps : list (list positive)
}.

Record domtree := DomTree {
  idom : ptrie positive;
  kids : ptrie (list positive);
  pre : ptrie N;
  post : ptrie N
}.

Record loops := Loops {
  header : ptrie positive;
  parent : ptrie positive;
  body : ptrie (list positive)
}.

Inductive edge_kind :=
  | Tree
  | Back
  | Done.
