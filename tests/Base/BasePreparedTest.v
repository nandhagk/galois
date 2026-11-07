(** * Prepared-key fixtures

    Validity distinguishes locally prepared keys from mismatched cached codes.
    For example, the empty list has the landed list codec's three-bit code.
    Builds on: BasePrepared. *)

From Stdlib Require Import List NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseCode BaseMap BasePrepared.
Import List.ListNotations.

Example prepared_valid : PreparedKey.valid nat_encoding (PreparedKey.prepare nat_encoding 3).
Proof.
  vm_compute. reflexivity.
Qed.

Example prepared_invalid : ~ PreparedKey.valid nat_encoding (PreparedKey.Key 3 1%positive).
Proof.
  vm_compute. discriminate.
Qed.

Example prepared_unequal_codes :
  PreparedKey.code (PreparedKey.prepare nat_encoding 2) <>
    PreparedKey.code (PreparedKey.prepare nat_encoding 3).
Proof.
  vm_compute. discriminate.
Qed.

Example prepared_injection_client {K} (E : encoding K) (HE : encoding_laws E)
    (p q : PreparedKey.t K) :
  PreparedKey.valid E p -> PreparedKey.valid E q -> PreparedKey.key p <> PreparedKey.key q ->
  PreparedKey.code p <> PreparedKey.code q.
Proof.
  intros Hp Hq Hne Heq. apply Hne. exact (PreparedKey.prepared_code_injective E HE p q Hp Hq Heq).
Qed.

Example prepared_empty_list :
  (PreparedKey.key (PreparedKey.prepare (codec_enc (list_codec nat_codec)) []),
    N.pos (Pos.size (PreparedKey.code
      (PreparedKey.prepare (codec_enc (list_codec nat_codec)) [])))) = ([], 3%N).
Proof.
  vm_compute. reflexivity.
Qed.

Example prepared_lookup_and_cost :
  let p := PreparedKey.prepare nat_encoding 2 in
  let m := PreparedKey.set p 7 Map.empty in
  (PreparedKey.get p m, PreparedKey.mem p m, Cost.ticks (PreparedKey.get_c p m)) =
    (Some 7, true, 2%N).
Proof.
  vm_compute. reflexivity.
Qed.

Example prepared_remove :
  let p := PreparedKey.prepare nat_encoding 2 in
  PreparedKey.get p (PreparedKey.remove p (PreparedKey.set p 7 Map.empty)) = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example prepared_pair_width :
  N.pos (Pos.size (PreparedKey.code
    (PreparedKey.prepare (codec_enc (pair_codec nat_codec bool_codec)) (1, true)))) = 15%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example prepared_encoder_is_not_repeated :
  let E := Encoding (fun p : positive => Cost.lift (fun _ => 100%N) (fun p => p) p) in
  let p := PreparedKey.prepare E 4%positive in
  (Cost.ticks (PreparedKey.prepare_c E 4%positive),
    Cost.ticks (PreparedKey.get_c p (@Map.empty positive nat))) = (101, 3)%N.
Proof.
  vm_compute. reflexivity.
Qed.
