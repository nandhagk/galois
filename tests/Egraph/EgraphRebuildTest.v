(** * Raw leaf coverage for deferred rebuilding

    The reference WF domain includes duplicate leaf classes and an empty memo.
    For example, the reference rebuild merges those classes without any child incidence.
    Builds on: EgraphCoreDomain and EgraphSpec. *)

From Stdlib Require Import List BinPos.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Egraph Require Import EgraphSyntax EgraphGraph EgraphSpec EgraphCoreDomain.
Import List.ListNotations.

Module EggRebuildDomainTest.

Definition alg : EggAlg.t nat bool nat :=
  EggAlg.of_pure (codec_enc nat_codec) (codec_enc bool_codec) (codec_enc nat_codec)
    (fun _ => Some true) (fun _ _ _ => true).

Definition raw : Egraph.t nat bool nat := EggCoreDomain.duplicate_leaves true 1.

Example raw_has_no_memo_entries : Map.elements (Egraph.memo raw) = [].
Proof.
  vm_compute. reflexivity.
Qed.

Example raw_contains_only_duplicate_leaf_productions :
  Map.elements (Egraph.nodes raw) =
    [(2%positive, Egraph.NVar true 1); (1%positive, Egraph.NVar true 1)].
Proof.
  vm_compute. reflexivity.
Qed.

Example raw_classes_start_distinct :
  (Egraph.find alg raw 1%positive, Egraph.find alg raw 2%positive) =
    (1%positive, 2%positive).
Proof.
  vm_compute. reflexivity.
Qed.

Example raw_has_no_dirty_class :
  Egraph.dirty raw = [].
Proof.
  vm_compute. reflexivity.
Qed.

(** Finite witnesses and structural WF hold for the duplicate leaf graph. *)
Theorem raw_structural_wf : EggSpec.structural_wf alg raw.
Proof.
  apply EggCoreDomain.duplicate_leaves_structural_wf; reflexivity.
Qed.

(** The raw graph is outside the maintained kernel domain. *)
Theorem raw_not_kernel_inv : ~ Egraph.kernel_inv alg raw.
Proof.
  apply EggCoreDomain.duplicate_leaves_not_kernel_inv.
Qed.

(** The structurally valid graph fails congruence closure before rebuilding. *)
Theorem raw_not_clean : ~ EggSpec.clean alg raw.
Proof.
  apply EggCoreDomain.duplicate_leaves_not_clean.
Qed.

End EggRebuildDomainTest.
