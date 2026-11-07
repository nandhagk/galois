(** * E-graph state and class operations

    Each allocated identifier owns a node, and a union-find records class equivalence.
    For example, a union rejects an identifier that has no allocated node.
    Builds on: EgraphSyntax and BaseUnionFind. *)

From Stdlib Require Import List BinPos.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseUnionFind.
From Galois.Egraph Require Import EgraphSyntax.
Import Cost.Notations.

Module Egraph.

Definition id := positive.

Inductive enode (K Sort V : Type) : Type :=
  | NVar (s : Sort) (v : V)
  | NApp (s : Sort) (op : K) (children : list id).

Arguments NVar {K Sort V}.
Arguments NApp {K Sort V}.

Record t (K Sort V : Type) : Type := Make {
  uf : UnionFind.t id;
  nodes : Map.t id (enode K Sort V);
  memo : Map.t positive id;
  next : positive
}.

Arguments uf {K Sort V} _.
Arguments nodes {K Sort V} _.
Arguments memo {K Sort V} _.
Arguments next {K Sort V} _.

Definition id_encoding : encoding id := codec_enc positive_codec.

Definition empty_c {K Sort V} : Cost.t (t K Sort V) :=
  let* forest := UnionFind.make_c in
  let* ns := Map.empty_c in
  let* table := Map.empty_c in
  Cost.ret (Make K Sort V forest ns table 1%positive).

Definition empty {K Sort V} : t K Sort V := Cost.value empty_c.

Definition find_c {K Sort V} (a : EggAlg.t K Sort V) (g : t K Sort V) (c : id) : Cost.t id :=
  Cost.map fst (UnionFind.find_c id_encoding c (uf g)).

Definition find {K Sort V} (a : EggAlg.t K Sort V) (g : t K Sort V) (c : id) :=
  Cost.value (find_c a g c).

Definition node_sort {K Sort V} (n : enode K Sort V) : Sort :=
  match n with
  | NVar s _ => s
  | NApp s _ _ => s
  end.

Definition sort_of_c {K Sort V} (a : EggAlg.t K Sort V) (g : t K Sort V) (c : id) :
    Cost.t (option Sort) :=
  Cost.map (option_map node_sort) (Map.get_c id_encoding c (nodes g)).

Definition sort_of {K Sort V} (a : EggAlg.t K Sort V) (g : t K Sort V) (c : id) :=
  Cost.value (sort_of_c a g c).

Definition union_c {K Sort V} (a : EggAlg.t K Sort V) (g : t K Sort V) (c d : id) :
    Cost.t (option (t K Sort V)) :=
  let* sc := sort_of_c a g c in
  let* sd := sort_of_c a g d in
  match sc, sd with
  | Some sc, Some sd =>
    Cost.step ;;
    let* pc := encode_c (EggAlg.sort_enc K Sort V a) sc in
    Cost.step ;;
    let* pd := encode_c (EggAlg.sort_enc K Sort V a) sd in
    let* cmp := Map.code_compare_c pc pd in
    match cmp with
    | Eq =>
      let* forest := UnionFind.union_c id_encoding c d (uf g) in
      Cost.ret (Some (Make K Sort V forest (nodes g) (memo g) (next g)))
    | _ => Cost.ret None
    end
  | _, _ => Cost.ret None
  end.

Definition union {K Sort V} (a : EggAlg.t K Sort V) (g : t K Sort V) (c d : id) :=
  Cost.value (union_c a g c d).

Arguments empty {K Sort V} : simpl never.
Arguments find {K Sort V} _ _ _ : simpl never.
Arguments sort_of {K Sort V} _ _ _ : simpl never.
Arguments union {K Sort V} _ _ _ _ : simpl never.

End Egraph.
