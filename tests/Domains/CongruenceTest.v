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

(** The normal-residue path agrees with reduction at the width boundary. *)
Example p1_cong_norm_width_one :
  map (Payload.congr_norm 1%positive) [C 4 1; C 8 3; C 0 5; C 3 1; C 6 2; CBot] =
    [C 0 1; CBot; CBot; C 0 1; CBot; CBot].
Proof.
  vm_compute. reflexivity.
Qed.

(** Normal residues are unchanged at the two larger test widths. *)
Example p1_cong_norm_normal :
  map (fun w => map (Payload.congr_norm w)
    [C 4 1; C 8 3; C 0 5; C 3 1; C 6 2; CBot]) [8%positive; 64%positive] =
    [[C 4 1; C 8 3; C 0 5; C 3 1; C 6 2; CBot];
     [C 4 1; C 8 3; C 0 5; C 3 1; C 6 2; CBot]].
Proof.
  vm_compute. reflexivity.
Qed.

Definition p1_cong_inputs := [C 4 1; C 8 3; C 0 5; C 3 1; C 6 2; CBot].

(** At width one, out-of-range constants normalize to bottom before transfer. *)
Example p1_cong_transfers_width_one :
  map (Payload.congr_neg 1%positive) p1_cong_inputs =
    [C 0 1; CBot; CBot; C 0 1; CBot; CBot] /\
  map (fun a => Payload.congr_add 1%positive a (C 8 3)) p1_cong_inputs =
    repeat CBot 6 /\
  map (fun a => Payload.congr_sub 1%positive a (C 8 3)) p1_cong_inputs =
    repeat CBot 6 /\
  map (fun a => Payload.congr_mul 1%positive a (C 8 3)) p1_cong_inputs =
    repeat CBot 6 /\
  map (fun a => Payload.congr_shl 1%positive a (C 0 5)) p1_cong_inputs =
    repeat CBot 6 /\
  map (Payload.congr_project 1%positive 1%positive) p1_cong_inputs =
    [C 0 1; CBot; CBot; C 0 1; CBot; CBot].
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

(** Eight-bit negation reduces residues modulo the gcd with 256. *)
Example p1_cong_neg_width_eight :
  map (Payload.congr_neg 8%positive) p1_cong_inputs =
    [C 4 3; C 8 5; C 0 251; C 1 0; C 2 0; CBot].
Proof.
  vm_compute. reflexivity.
Qed.

(** Sixty-four-bit negation wraps the exact constant at its word modulus. *)
Example p1_cong_neg_width_sixty_four :
  map (Payload.congr_neg 64%positive) p1_cong_inputs =
    [C 4 3; C 8 5; C 0 (2 ^ 64 - 5); C 1 0; C 2 0; CBot].
Proof.
  vm_compute. reflexivity.
Qed.

(** Addition and subtraction keep only common power-of-two factors of the moduli. *)
Example p1_cong_add_sub_widths :
  map (fun w => map (fun a => Payload.congr_add w a (C 8 3)) p1_cong_inputs)
    [8%positive; 64%positive] =
    repeat [C 4 0; C 8 6; C 8 0; C 1 0; C 2 1; CBot] 2 /\
  map (fun w => map (fun a => Payload.congr_sub w a (C 8 3)) p1_cong_inputs)
    [8%positive; 64%positive] =
    repeat [C 4 2; C 8 0; C 8 2; C 1 0; C 2 1; CBot] 2.
Proof.
  vm_compute. split; reflexivity.
Qed.

(** The product class uses the gcd of all three coefficient products. *)
Example p1_cong_mul_widths :
  map (fun w => map (fun a => Payload.congr_mul w a (C 8 3)) p1_cong_inputs)
    [8%positive; 64%positive] =
    repeat [C 4 3; C 8 1; C 8 7; C 1 0; C 2 0; CBot] 2.
Proof.
  vm_compute. reflexivity.
Qed.

(** A shifted modulus can collapse to an exact value at the smaller width. *)
Example p1_cong_shl_widths :
  map (fun a => Payload.congr_shl 8%positive a (C 0 5)) p1_cong_inputs =
    [C 128 32; C 0 96; C 0 160; C 32 0; C 64 0; CBot] /\
  map (fun a => Payload.congr_shl 64%positive a (C 0 5)) p1_cong_inputs =
    [C 128 32; C 256 96; C 0 160; C 32 0; C 64 0; CBot].
Proof.
  vm_compute. split; reflexivity.
Qed.

(** Projection folds arbitrary moduli into divisors of the target word modulus. *)
Example p1_cong_project_widths :
  map (Payload.congr_project 8%positive 8%positive) p1_cong_inputs =
    [C 4 1; C 8 3; C 0 5; C 1 0; C 2 0; CBot] /\
  map (Payload.congr_project 64%positive 32%positive) p1_cong_inputs =
    [C 4 1; C 8 3; C 0 5; C 1 0; C 2 0; CBot].
Proof.
  vm_compute. split; reflexivity.
Qed.

(** Stable widening returns its original operand, including raw payloads. *)
Example p1_cong_widen_widths :
  map (fun a => Payload.pwiden tt 1%positive a (C 8 5)) p1_cong_inputs =
    p1_cong_inputs /\
  map (fun w => map (fun a => Payload.pwiden tt w a (C 8 5)) p1_cong_inputs)
    [8%positive; 64%positive] =
    repeat [C 4 1; C 2 1; C 8 5; C 1 0; C 1 0; C 8 5] 2.
Proof.
  vm_compute. split; reflexivity.
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

(** Negative residues take the original Euclidean remainder branch. *)
Example congruence_negative_residue_normalization :
  Payload.congr_norm 8%positive (C (-6) (-1)) = C 6 5.
Proof.
  vm_compute. reflexivity.
Qed.

(** Shifting a normalized negative raw residue agrees with gcd and remainder. *)
Example congruence_negative_residue_shift :
  Payload.congr_shl 8%positive (C (-6) (-1)) (C 0 1) = C 4 2.
Proof.
  vm_compute. reflexivity.
Qed.

(** A zero shift preserves this already word-folded class. *)
Example congruence_zero_shift :
  Payload.congr_shl 8%positive (C 4 1) (C 0 0) = C 4 1.
Proof.
  vm_compute. reflexivity.
Qed.

(** A shift equal to the word width yields the exact zero class. *)
Example congruence_width_shift :
  Payload.congr_shl 8%positive (C 4 1) (C 0 8) = C 0 0.
Proof.
  vm_compute. reflexivity.
Qed.
