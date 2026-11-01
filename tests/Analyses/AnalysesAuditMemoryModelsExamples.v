(** * Memory model computations

    These examples exercise counted distinctness and footprint disjointness.
    For example, a duplicate key is probed again but appears only once in the output.
    Builds on: the memory distinctness and disjointness observers. *)

From Stdlib Require Import List PArith ZArith.
From Galois.Domains Require Import DomainsFootprint.
From Galois.Analyses Require Import AnalysesAuditMemoryDistinct AnalysesAuditMemoryDisjoint.
Import List.ListNotations.

Definition example_encode (p : positive) : positive * list unit := (p, []).

Example duplicate_keys_keep_first_order :
  fst (audit_memory_distinct example_encode [2%positive; 1%positive; 2%positive]) =
    [2%positive; 1%positive].
Proof.
  reflexivity.
Qed.

Example overlapping_pair_is_not_disjoint :
  fst (audit_disjoint_pair example_encode (Footprint 1%positive 0 3)
    (Footprint 1%positive 2 4)) = false.
Proof.
  reflexivity.
Qed.

Example adjacent_pair_is_disjoint :
  fst (audit_disjoint_pair example_encode (Footprint 1%positive 0 2)
    (Footprint 1%positive 2 4)) = true.
Proof.
  reflexivity.
Qed.

Example disjoint_pair_count_includes_later_pairs :
  audit_disjoint_pairs
    (snd (audit_footprints_disjoint example_encode [Footprint 1%positive 0 3]
      [Footprint 1%positive 2 4; Footprint 1%positive 3 4])) = 2.
Proof.
  reflexivity.
Qed.
