(** * Exact legacy and deferred-kernel class comparisons

    The same unary terms and leaf union induce identical partitions in both implementations.
    For example, the first two applications become equal and every later application stays separate.
    Builds on: EgraphGraph and GaloisLegacy.Rewrite. *)

From Stdlib Require Import List PArith NArith.
From Galois.Base Require Import BaseEncoding.
From Galois.Egraph Require Import EgraphSyntax EgraphGraph.
From GaloisLegacy.Collections Require Import CollectionsEncoding.
From GaloisLegacy.Rewrite Require Import RewriteSyntax RewriteEgraph RewriteIndex RewriteRebuild.
Import List.ListNotations.
Local Open Scope nat_scope.

Module EggRebuildLegacyTest.

Definition alg : EggAlg.t nat bool nat :=
  EggAlg.of_pure (codec_enc nat_codec) (codec_enc bool_codec) (codec_enc nat_codec)
    (fun _ => Some true) (fun _ _ _ => true).

Definition legacy_fixture m :=
  fold_left (fun g i =>
    fst (rw_add nat_encoding bool_encoding nat_encoding g
      (RWApp true 4 [RWVar true (S i)]))) (seq 0 m) (@rw_empty nat bool nat).

Definition new_fixture m :=
  Egraph.add_terms alg Egraph.empty
    (map (fun i => EggTerm.App true 4 [EggTerm.Var true (S i)]) (seq 0 m)).

Definition legacy_result m :=
  option_map (rw_rebuild nat_encoding bool_encoding nat_encoding)
    (rw_union bool_encoding (legacy_fixture m) 2%positive 4%positive).

Definition new_result m :=
  match new_fixture m with
  | None => None
  | Some (_, g) => option_map (Egraph.rebuild alg)
      (Egraph.union alg g 1%positive 3%positive)
  end.

Definition ids m := map Pos.of_succ_nat (seq 0 (2 * m)).

Definition new_classes m :=
  option_map (fun g => map (Egraph.find alg g) (ids m)) (new_result m).

(** Legacy starts at two whereas the new next pointer starts at one. *)
Definition legacy_classes m :=
  option_map (fun g => map (fun i => option_map Pos.pred (rw_find g (Pos.succ i)))
    (ids m)) (legacy_result m).

Example new_fixture_exact_classes :
  (new_classes 4, new_classes 8, new_classes 16) =
    (Some [1; 4; 1; 4; 5; 6; 7; 8]%positive,
      Some [1; 4; 1; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16]%positive,
      Some [1; 4; 1; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16;
        17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31; 32]%positive).
Proof.
  vm_compute. reflexivity.
Qed.

(** Legacy's chosen representatives are recorded independently of the new rank tie-breaking. *)
Example legacy_fixture_exact_classes :
  (legacy_classes 4, legacy_classes 8, legacy_classes 16) =
    (Some (map (@Some positive) [1; 4; 1; 4; 5; 6; 7; 8]%positive),
      Some (map (@Some positive) [1; 4; 1; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16]%positive),
      Some (map (@Some positive) [1; 4; 1; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16;
        17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31; 32]%positive)).
Proof.
  vm_compute. reflexivity.
Qed.

Definition new_partition m :=
  option_map (fun classes => flat_map (fun c => map (Pos.eqb c) classes) classes)
    (new_classes m).

Definition legacy_partition m :=
  option_map (fun classes => flat_map (fun c => map (fun d =>
    match c, d with Some c, Some d => Pos.eqb c d | _, _ => false end) classes) classes)
    (legacy_classes m).

(** All ordered pairs of allocated identifiers have the same class relation in every fixture. *)
Example legacy_fixture_exact_class_mapping :
  (legacy_partition 4, legacy_partition 8, legacy_partition 16) =
    (new_partition 4, new_partition 8, new_partition 16).
Proof.
  vm_compute. reflexivity.
Qed.

Definition legacy_prepared_pairs m :=
  let g := legacy_fixture m in
  let encoding := rw_node_encoding nat_encoding bool_encoding nat_encoding in
  length (rw_pair_universe nat_encoding encoding g (rw_build_index nat_encoding g)
    (rw_build_table positive_encoding g (rw_variable_keys encoding))).

(** This is the legacy preparation's exact obligation count, not a fabricated Cost tick count. *)
Example legacy_quadratic_pair_preparation :
  (legacy_prepared_pairs 4, legacy_prepared_pairs 8, legacy_prepared_pairs 16) =
    (20, 72, 272).
Proof.
  vm_compute. reflexivity.
Qed.

End EggRebuildLegacyTest.
