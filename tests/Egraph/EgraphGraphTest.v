(** * Empty e-graph boundaries

    Class operations reject identifiers that have no allocated node.
    For example, even a self-union of an unknown identifier is rejected.
    Builds on: EgraphGraph. *)

From Stdlib Require Import List BinPos.
From Galois.Base Require Import BaseEncoding.
From Galois.Egraph Require Import EgraphSyntax EgraphGraph.
Import List.ListNotations.

Definition sample_alg : EggAlg.t nat bool nat :=
  EggAlg.of_pure (codec_enc nat_codec) (codec_enc bool_codec) (codec_enc nat_codec)
    (fun _ => Some true) (fun _ _ _ => true).

Example empty_unknown_sort :
  Egraph.sort_of sample_alg Egraph.empty 1%positive = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example empty_unknown_self_union :
  Egraph.union sample_alg Egraph.empty 1%positive 1%positive = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example empty_unknown_find :
  Egraph.find sample_alg Egraph.empty 1%positive = 1%positive.
Proof.
  vm_compute. reflexivity.
Qed.
