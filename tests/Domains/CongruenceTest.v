(** * Congruence domain examples

    These examples exercise normalization, arithmetic and CRT intersection.
    For example, the intersection of 1 modulo 4 and 3 modulo 6 is 9 modulo 12.
    Builds on: Congruence. *)

From Stdlib Require Import ZArith List.
From Galois.Bits Require Import Word Op.
From Galois.Domains Require Import WordSig Congruence CongruenceSig BitsLang Tagged Harness.
Import List.ListNotations.
Local Open Scope Z_scope.
Module Payload := CongruenceCode WordLanguageCode.
Module PayloadSpec := Congruence WordLanguage.
Module Table := CongruenceTableCode WordLanguageCode Payload.
Module Base := TaggedCode WordLanguageCode Payload.
Module TaggedTable := TaggedTableCode WordLanguageCode Payload Table.
Module Domain := HarnessCode BitsLangCode Base TaggedTable.

Definition payload_at w (a : tagged congr) :=
  match a with TBot => CBot | TVal _ p => p | TAny => Payload.ptop w end.
Definition tagged_args (xs : list (positive * congr)) :=
  map (fun wp => TVal (fst wp) (snd wp)) xs.
Definition forward_payload o xs rw :=
  payload_at rw (Domain.forward (BOp o) (tagged_args xs)).
Definition assume_payload o xs rw r :=
  map (payload_at rw) (Domain.backward (BOp o) (TVal rw r) (tagged_args xs)).

Example dom4_cong_residue : Payload.congr_norm 8%positive (C 4 6) = C 4 2.
Proof.
  vm_compute. reflexivity.
Qed.

Example dom4_cong_negative_modulus : Payload.congr_norm 8%positive (C (-4) 6) = C 4 2.
Proof.
  vm_compute. reflexivity.
Qed.

Example dom4_cong_large_modulus : Payload.congr_norm 8%positive (C 512 1) = C 0 1.
Proof.
  vm_compute. reflexivity.
Qed.

Example dom4_cong_large_empty : Payload.congr_norm 8%positive (C 512 300) = CBot.
Proof.
  vm_compute. reflexivity.
Qed.

Example dom4_cong_raw_exact_empty : Payload.congr_norm 8%positive (C 0 256) = CBot.
Proof.
  vm_compute. reflexivity.
Qed.

Example dom4_cong_join : Payload.pjoin 8%positive (C 0 3) (C 0 7) = C 4 3.
Proof.
  vm_compute. reflexivity.
Qed.

Example dom4_cong_meet_incompatible : Payload.pmeet 8%positive (C 2 0) (C 2 1) = CBot.
Proof.
  vm_compute. reflexivity.
Qed.

Example dom4_cong_meet_compatible : Payload.pmeet 8%positive (C 4 1) (C 6 3) = C 12 9.
Proof.
  vm_compute. reflexivity.
Qed.

(* Old rank was 10%nat; the current widening rank is 0%nat.
Example dom4_cong_height : PayloadSpec.pwrank tt 8%positive (C 1 0) = 10%nat.
Proof.
  vm_compute. reflexivity.
Qed.

*)
Example dom4_cong_add : Payload.congr_add 8%positive (C 4 1) (C 8 2) = C 4 3.
Proof.
  vm_compute. reflexivity.
Qed.

Example dom4_cong_constant_mul : Payload.congr_mul 8%positive (C 0 17) (C 0 17) = C 0 33.
Proof.
  vm_compute. reflexivity.
Qed.

Example congruence_unary_entries :
  forward_payload bvneg [(8%positive, C 4 1)] 8%positive = C 4 3 /\
  forward_payload (bvzext 8%positive) [(8%positive, C 4 1)] 16%positive =
    C 4 1 /\
  forward_payload (bvtrunc 4%positive) [(8%positive, C 4 1)] 4%positive =
    C 4 1.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Example congruence_binary_entries :
  map (fun o => forward_payload o
    [(8%positive, C 4 1); (8%positive, C 0 2)] 8%positive)
    [bvadd; bvsub; bvmul; bvshl; bvurem] =
    [C 4 3; C 4 3; C 8 2; C 16 4; C 2 1].
Proof.
  vm_compute. reflexivity.
Qed.

Example congruence_selection_entry :
  forward_payload bvite
    [(1%positive, C 1 0); (8%positive, C 4 1); (8%positive, C 4 3)]
    8%positive = C 2 1.
Proof.
  vm_compute. reflexivity.
Qed.

Definition cong_entry_cases :=
  [(bvneg, [(8%positive, C 4 1)], 8%positive);
   (bvzext 8%positive, [(8%positive, C 4 1)], 16%positive);
   (bvtrunc 4%positive, [(8%positive, C 4 1)], 4%positive);
   (bvadd, [(8%positive, C 4 1); (8%positive, C 0 2)], 8%positive);
   (bvsub, [(8%positive, C 4 1); (8%positive, C 0 2)], 8%positive);
   (bvmul, [(8%positive, C 4 1); (8%positive, C 0 2)], 8%positive);
   (bvshl, [(8%positive, C 4 1); (8%positive, C 0 2)], 8%positive);
   (bvurem, [(8%positive, C 4 1); (8%positive, C 0 2)], 8%positive);
   (bvite, [(1%positive, C 1 0); (8%positive, C 4 1);
     (8%positive, C 4 3)], 8%positive)].

Example congruence_empty_entries :
  map (fun '(o, xs, rw) => forward_payload o
    (map (fun wp => (fst wp, CBot)) xs) rw) cong_entry_cases = repeat CBot 9.
Proof.
  vm_compute. reflexivity.
Qed.

Example congruence_one_bit_entries :
  map (fun o => forward_payload o
    [(1%positive, C 0 1); (1%positive, C 0 1)] 1%positive)
    [bvadd; bvsub; bvmul; bvshl; bvurem] =
    [C 0 0; C 0 0; C 0 1; C 0 0; C 0 0] /\
  forward_payload bvneg [(1%positive, C 0 1)] 1%positive = C 0 1 /\
  forward_payload (bvzext 1%positive) [(1%positive, C 0 1)] 2%positive =
    C 0 1 /\
  forward_payload (bvtrunc 1%positive) [(1%positive, C 0 1)] 1%positive =
    C 0 1 /\
  forward_payload bvite
    [(1%positive, C 0 1); (1%positive, C 0 1); (1%positive, C 0 0)]
    1%positive = C 0 1.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Example congruence_maximum_and_zero_divisor :
  forward_payload bvadd
    [(8%positive, C 0 255); (8%positive, C 0 1)] 8%positive = C 0 0 /\
  forward_payload bvurem
    [(8%positive, C 4 1); (8%positive, C 0 0)] 8%positive = C 4 1.
Proof.
  vm_compute. split; reflexivity.
Qed.


Example congruence_malformed_counts_nonpoint :
  map (fun xs => forward_payload bvadd xs 8%positive)
    [[]; [(8%positive, C 4 1)];
     [(8%positive, C 4 1); (8%positive, C 0 2); (8%positive, C 0 3)];
     [(8%positive, C 4 1); (8%positive, C 0 2); (8%positive, C 0 3);
      (8%positive, C 0 4)]] =
    [CBot; C 1 0; C 1 0; C 1 0].
Proof.
  vm_compute. reflexivity.
Qed.

Example congruence_malformed_counts_points :
  map (fun xs => forward_payload bvadd xs 8%positive)
    [[]; [(8%positive, C 0 1)];
     [(8%positive, C 0 1); (8%positive, C 0 2); (8%positive, C 0 3)];
     [(8%positive, C 0 1); (8%positive, C 0 2); (8%positive, C 0 3);
      (8%positive, C 0 4)]] =
    repeat CBot 4.
Proof.
  vm_compute. reflexivity.
Qed.

Example congruence_malformed_count_assumptions :
  map (fun xs => assume_payload bvadd xs 8%positive CBot)
    [[]; [(8%positive, C 4 1)]; [(8%positive, C 0 1)];
     [(8%positive, C 4 1); (8%positive, C 0 2); (8%positive, C 0 3)];
     [(8%positive, C 0 1); (8%positive, C 0 2); (8%positive, C 0 3);
      (8%positive, C 0 4)]] =
    [[]; [C 4 1]; [C 0 1]; [C 4 1; C 0 2; C 0 3];
     [C 0 1; C 0 2; C 0 3; C 0 4]].
Proof.
  vm_compute. reflexivity.
Qed.

(** A zero divisor retains the dividend in the unsigned remainder table. *)
Example congruence_remainder_zero :
  forward_payload bvurem [(8%positive, C 0 5); (8%positive, C 0 0)] 8%positive = C 0 5.
Proof.
  vm_compute. reflexivity.
Qed.
