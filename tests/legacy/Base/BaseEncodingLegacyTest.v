(** * Differential encoding fixtures

    The new tagged tree grammar is compared with the legacy flat grammar.
    For example, the list fixtures include empty, singleton and two-element lists.
    Builds on: BaseCode and the legacy CollectionsEncoding. *)

From Stdlib Require Import Bool List NArith.
From Galois.Base Require Import BaseEncoding BaseCode.
From GaloisLegacy.Collections Require CollectionsEncoding.
Import List.ListNotations.
Local Open Scope positive_scope.

Definition list_fixtures : list (list positive) := [[]; [1]; [1; 2]].
Definition pair_fixtures : list (positive * positive) := [(1, 2); (2, 1)].
Definition option_fixtures : list (option positive) := [None; Some 3].

Definition new_lists :=
  map (encode (codec_enc (list_codec positive_codec))) list_fixtures.
Definition old_lists :=
  map (CollectionsEncoding.encode
    (CollectionsEncoding.list_encoding CollectionsEncoding.positive_encoding)) list_fixtures.

Definition new_pairs :=
  map (encode (codec_enc (pair_codec positive_codec positive_codec))) pair_fixtures.
Definition old_pairs :=
  map (CollectionsEncoding.encode
    (CollectionsEncoding.pair_encoding
      CollectionsEncoding.positive_encoding CollectionsEncoding.positive_encoding)) pair_fixtures.

Definition new_options :=
  map (encode (codec_enc (option_codec positive_codec))) option_fixtures.
Definition old_options :=
  map (CollectionsEncoding.encode
    (CollectionsEncoding.option_encoding CollectionsEncoding.positive_encoding)) option_fixtures.

Fixpoint distinct (ps : list positive) : bool :=
  match ps with
  | [] => true
  | p :: ps => negb (existsb (Pos.eqb p) ps) && distinct ps
  end.

Example differential_no_collisions :
  map distinct [new_lists; old_lists; new_pairs; old_pairs; new_options; old_options] =
    [true; true; true; true; true; true].
Proof.
  vm_compute. reflexivity.
Qed.

Definition bit_count (p : positive) : N := N.pos (Pos.size p).

(** Each fixture increases by at most six bits under the tagged tree grammar. *)
Definition fixture_overhead : N := 6.

Definition fixture_bounds (new old : list positive) : bool :=
  forallb (fun ps => N.leb (bit_count (fst ps)) (bit_count (snd ps) + fixture_overhead))
    (combine new old).

Example differential_size_bounds :
  (fixture_bounds new_lists old_lists,
    fixture_bounds new_pairs old_pairs,
    fixture_bounds new_options old_options) = (true, true, true).
Proof.
  vm_compute. reflexivity.
Qed.

Example differential_fixture_bits :
  (map bit_count (new_lists ++ [encode (codec_enc (pair_codec positive_codec positive_codec))
      (1, 2)] ++ new_options),
    map bit_count (old_lists ++ [CollectionsEncoding.encode
      (CollectionsEncoding.pair_encoding
        CollectionsEncoding.positive_encoding CollectionsEncoding.positive_encoding)
      (1, 2)] ++ old_options)) =
  ([3; 7; 13; 13; 3; 9]%N, [1; 3; 7; 7; 1; 3]%N).
Proof.
  vm_compute. reflexivity.
Qed.

Example differential_layout_changes :
  map (fun ps => Pos.eqb (fst ps) (snd ps)) (combine new_lists old_lists) =
    [false; false; false].
Proof.
  vm_compute. reflexivity.
Qed.
