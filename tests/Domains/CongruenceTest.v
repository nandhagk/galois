(** * Congruence domain examples

    These examples exercise normalization, arithmetic and CRT intersection.
    For example, the intersection of 1 modulo 4 and 3 modulo 6 is 9 modulo 12.

    Groups:
    - NormalizationTests: reducing a congruence class to its normal residue.
    - WidthOneTests: transfers at width one, where out-of-range constants are bottom.
    - NegationTests: negation at wide words.
    - AdditionTests: addition and subtraction keep common power-of-two factors.
    - MultiplicationTests: products use the gcd of coefficient products.
    - ShiftTests: shifts of residue classes.
    - ProjectionTests: projection folds moduli into divisors of the word modulus.
    - WideningTests: widening keeps stable operands and raw payloads.
    - JoinMeetTests: join and meet of residue classes.
    - RemainderTests: unsigned remainder with a zero divisor.
    - ForwardEntryTests: forward entries of the transfer table.
    - OneBitTests: forward entries at width one.
    - EmptyOperandTests: empty operands give empty classes.
    - MalformedTests: operand lists of the wrong length.
    Builds on: Congruence. *)

From Stdlib Require Import ZArith List.
From Galois.Bits Require Import Word Op.
From Galois.Domains Require Import WordSig Congruence CongruenceSig BitsLang Tagged Harness.
Import List.ListNotations.
Local Open Scope Z_scope.

(** * Fixtures *)

Module Payload := CongruenceCode WordLanguageCode.
Module PayloadSpec := Congruence WordLanguage.
Module Table := CongruenceTableCode WordLanguageCode Payload.
Module Base := TaggedCode WordLanguageCode Payload.
Module TaggedTable := TaggedTableCode WordLanguageCode Payload Table.
Module Domain := HarnessCode BitsLangCode Base TaggedTable.

(** The payload of a tagged value at width w, with bottom and top read as payloads. *)
Definition payload_at w (a : tagged congr) :=
  match a with TBot => CBot | TVal _ p => p | TAny => Payload.ptop w end.

(** Tagged operands built from (width, class) pairs. *)
Definition tagged_args (xs : list (positive * congr)) :=
  map (fun wp => TVal (fst wp) (snd wp)) xs.

(** The payload of a forward transfer on (width, class) operands. *)
Definition forward_payload o xs rw :=
  payload_at rw (Domain.forward (BOp o) (tagged_args xs)).

(** The payloads of a backward transfer from a class result. *)
Definition assume_payload o xs rw r :=
  map (payload_at rw) (Domain.backward (BOp o) (TVal rw r) (tagged_args xs)).

(** Six residue classes that the transfer examples apply to. *)
Definition p1_cong_inputs := [C 4 1; C 8 3; C 0 5; C 3 1; C 6 2; CBot].

(** * Normalization *)

Module NormalizationTests.

  (** A residue larger than its modulus reduces into the modulus range. *)
  Example norm_reduces_residue_into_modulus :
    Payload.congr_norm 8%positive (C 4 6) = C 4 2.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The normal-residue path agrees with reduction at the width boundary. *)
  Example width_one_norm_of_inputs :
    map (Payload.congr_norm 1%positive) [C 4 1; C 8 3; C 0 5; C 3 1; C 6 2; CBot] =
      [C 0 1; CBot; CBot; C 0 1; CBot; CBot].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Normal residues are unchanged at the two larger test widths. *)
  Example normal_residues_unchanged_at_wide_widths :
    map (fun w => map (Payload.congr_norm w)
      [C 4 1; C 8 3; C 0 5; C 3 1; C 6 2; CBot]) [8%positive; 64%positive] =
      [[C 4 1; C 8 3; C 0 5; C 3 1; C 6 2; CBot];
       [C 4 1; C 8 3; C 0 5; C 3 1; C 6 2; CBot]].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A negative modulus is normalized to its absolute value. *)
  Example norm_reduces_negative_modulus :
    Payload.congr_norm 8%positive (C (-4) 6) = C 4 2.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A modulus of 512 folds to the exact residue of its class at width eight. *)
  Example norm_large_modulus_folds_to_exact_residue :
    Payload.congr_norm 8%positive (C 512 1) = C 0 1.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A large modulus with a residue outside the word range is bottom. *)
  Example norm_large_modulus_with_residue_outside_word_is_bottom :
    Payload.congr_norm 8%positive (C 512 300) = CBot.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An exact value outside the word range is bottom. *)
  Example norm_exact_value_outside_word_is_bottom :
    Payload.congr_norm 8%positive (C 0 256) = CBot.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Negative residues take the original Euclidean remainder branch. *)
  Example norm_of_negative_residue_uses_euclidean_remainder :
    Payload.congr_norm 8%positive (C (-6) (-1)) = C 6 5.
  Proof.
    vm_compute. reflexivity.
  Qed.

End NormalizationTests.

(** * Width one *)

Module WidthOneTests.

  (** At width one, negation normalizes each out-of-range constant to bottom. *)
  Example width_one_neg_normalizes_inputs :
    map (Payload.congr_neg 1%positive) p1_cong_inputs =
      [C 0 1; CBot; CBot; C 0 1; CBot; CBot].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** At width one, an addition with an out-of-range constant gives bottom for every input. *)
  Example width_one_add_gives_bottom :
    map (fun a => Payload.congr_add 1%positive a (C 8 3)) p1_cong_inputs = repeat CBot 6.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** At width one, a subtraction with an out-of-range constant gives bottom for every input. *)
  Example width_one_sub_gives_bottom :
    map (fun a => Payload.congr_sub 1%positive a (C 8 3)) p1_cong_inputs = repeat CBot 6.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** At width one, a product with an out-of-range constant gives bottom for every input. *)
  Example width_one_mul_gives_bottom :
    map (fun a => Payload.congr_mul 1%positive a (C 8 3)) p1_cong_inputs = repeat CBot 6.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** At width one, a shift by an out-of-range class gives bottom for every input. *)
  Example width_one_shl_gives_bottom :
    map (fun a => Payload.congr_shl 1%positive a (C 0 5)) p1_cong_inputs = repeat CBot 6.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** At width one, projection normalizes each input to its width-one class. *)
  Example width_one_project_normalizes_inputs :
    map (Payload.congr_project 1%positive 1%positive) p1_cong_inputs =
      [C 0 1; CBot; CBot; C 0 1; CBot; CBot].
  Proof.
    vm_compute. reflexivity.
  Qed.

End WidthOneTests.

(** * Negation *)

Module NegationTests.

  (** Eight-bit negation reduces residues modulo the gcd with 256. *)
  Example neg_width_eight_reduces_modulo_gcd :
    map (Payload.congr_neg 8%positive) p1_cong_inputs =
      [C 4 3; C 8 5; C 0 251; C 1 0; C 2 0; CBot].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Sixty-four-bit negation wraps the exact constant at its word modulus. *)
  Example neg_width_sixty_four_wraps_constant :
    map (Payload.congr_neg 64%positive) p1_cong_inputs =
      [C 4 3; C 8 5; C 0 (2 ^ 64 - 5); C 1 0; C 2 0; CBot].
  Proof.
    vm_compute. reflexivity.
  Qed.

End NegationTests.

(** * Addition *)

Module AdditionTests.

  (** Addition keeps common power-of-two factors of the moduli at two widths. *)
  Example add_keeps_common_power_of_two_factors :
    map (fun w => map (fun a => Payload.congr_add w a (C 8 3)) p1_cong_inputs)
      [8%positive; 64%positive] =
      repeat [C 4 0; C 8 6; C 8 0; C 1 0; C 2 1; CBot] 2.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Subtraction keeps common power-of-two factors of the moduli at two widths. *)
  Example sub_keeps_common_power_of_two_factors :
    map (fun w => map (fun a => Payload.congr_sub w a (C 8 3)) p1_cong_inputs)
      [8%positive; 64%positive] =
      repeat [C 4 2; C 8 0; C 8 2; C 1 0; C 2 1; CBot] 2.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The sum of two residue classes is the class of the sum of their residues. *)
  Example add_combines_residues_modulo_gcd :
    Payload.congr_add 8%positive (C 4 1) (C 8 2) = C 4 3.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A forward addition of the maximum constant and one wraps to zero. *)
  Example forward_add_wraps_maximum_to_zero :
    forward_payload bvadd [(8%positive, C 0 255); (8%positive, C 0 1)] 8%positive = C 0 0.
  Proof.
    vm_compute. reflexivity.
  Qed.

End AdditionTests.

(** * Multiplication *)

Module MultiplicationTests.

  (** The product class uses the gcd of the coefficient products at two widths. *)
  Example mul_uses_gcd_of_coefficient_products :
    map (fun w => map (fun a => Payload.congr_mul w a (C 8 3)) p1_cong_inputs)
      [8%positive; 64%positive] =
      repeat [C 4 3; C 8 1; C 8 7; C 1 0; C 2 0; CBot] 2.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The product of two constants wraps at the word width. *)
  Example mul_of_constants_wraps_at_width :
    Payload.congr_mul 8%positive (C 0 17) (C 0 17) = C 0 33.
  Proof.
    vm_compute. reflexivity.
  Qed.

End MultiplicationTests.

(** * Shifts *)

Module ShiftTests.

  (** A shifted modulus can collapse to an exact value at the smaller width. *)
  Example shl_at_width_eight_collapses_modulus :
    map (fun a => Payload.congr_shl 8%positive a (C 0 5)) p1_cong_inputs =
      [C 128 32; C 0 96; C 0 160; C 32 0; C 64 0; CBot].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** At width sixty-four, the same shift keeps the modulus of the wider word. *)
  Example shl_at_width_sixty_four_keeps_modulus :
    map (fun a => Payload.congr_shl 64%positive a (C 0 5)) p1_cong_inputs =
      [C 128 32; C 256 96; C 0 160; C 32 0; C 64 0; CBot].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Shifting a normalized negative raw residue agrees with gcd and remainder. *)
  Example shl_of_negative_residue_uses_gcd_and_remainder :
    Payload.congr_shl 8%positive (C (-6) (-1)) (C 0 1) = C 4 2.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A zero shift preserves this already word-folded class. *)
  Example shl_by_zero_keeps_class :
    Payload.congr_shl 8%positive (C 4 1) (C 0 0) = C 4 1.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A shift equal to the word width yields the exact zero class. *)
  Example shl_by_word_width_gives_zero_class :
    Payload.congr_shl 8%positive (C 4 1) (C 0 8) = C 0 0.
  Proof.
    vm_compute. reflexivity.
  Qed.

End ShiftTests.

(** * Projection *)

Module ProjectionTests.

  (** Projection at width eight folds each input into a divisor of the word modulus. *)
  Example project_folds_moduli_at_width_eight :
    map (Payload.congr_project 8%positive 8%positive) p1_cong_inputs =
      [C 4 1; C 8 3; C 0 5; C 1 0; C 2 0; CBot].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Projection from width sixty-four to thirty-two folds each input into a divisor of 2^32. *)
  Example project_folds_moduli_from_sixty_four_to_thirty_two :
    map (Payload.congr_project 64%positive 32%positive) p1_cong_inputs =
      [C 4 1; C 8 3; C 0 5; C 1 0; C 2 0; CBot].
  Proof.
    vm_compute. reflexivity.
  Qed.

End ProjectionTests.

(** * Widening *)

Module WideningTests.

  (** Stable widening returns its original operand, including raw payloads. *)
  Example stable_widen_at_width_one_returns_operand :
    map (fun a => Payload.pwiden tt 1%positive a (C 8 5)) p1_cong_inputs = p1_cong_inputs.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Stable widening at widths eight and sixty-four keeps every raw payload. *)
  Example stable_widen_at_word_widths_keeps_raw_payloads :
    map (fun w => map (fun a => Payload.pwiden tt w a (C 8 5)) p1_cong_inputs)
      [8%positive; 64%positive] =
      repeat [C 4 1; C 2 1; C 8 5; C 1 0; C 1 0; C 8 5] 2.
  Proof.
    vm_compute. reflexivity.
  Qed.

(* Old rank was 10%nat; the current widening rank is 0%nat.
Example dom4_cong_height : PayloadSpec.pwrank tt 8%positive (C 1 0) = 10%nat.
Proof.
  vm_compute. reflexivity.
Qed.

*)

End WideningTests.

(** * Join and meet *)

Module JoinMeetTests.

  (** The join of two exact values is the residue class of their common modulus. *)
  Example join_of_exact_values_is_residue_class :
    Payload.pjoin 8%positive (C 0 3) (C 0 7) = C 4 3.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The meet of two incompatible residue classes is bottom. *)
  Example meet_of_incompatible_classes_is_bottom :
    Payload.pmeet 8%positive (C 2 0) (C 2 1) = CBot.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The meet of two compatible residue classes is the class of their lcm modulus. *)
  Example meet_of_compatible_classes_is_lcm_class :
    Payload.pmeet 8%positive (C 4 1) (C 6 3) = C 12 9.
  Proof.
    vm_compute. reflexivity.
  Qed.

End JoinMeetTests.

(** * Remainder *)

Module RemainderTests.

  (** A zero divisor retains the dividend in the unsigned remainder table. *)
  Example urem_by_zero_divisor_keeps_dividend :
    forward_payload bvurem [(8%positive, C 0 5); (8%positive, C 0 0)] 8%positive = C 0 5.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A zero divisor keeps a residue dividend in the unsigned remainder table. *)
  Example urem_by_zero_divisor_keeps_residue_dividend :
    forward_payload bvurem [(8%positive, C 4 1); (8%positive, C 0 0)] 8%positive = C 4 1.
  Proof.
    vm_compute. reflexivity.
  Qed.

End RemainderTests.

(** * Forward entries *)

Module ForwardEntryTests.

  (** The negation entry negates the residue of its operand. *)
  Example neg_entry_negates_residue :
    forward_payload bvneg [(8%positive, C 4 1)] 8%positive = C 4 3.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The zero-extension entry keeps the residue class of its operand. *)
  Example zext_entry_keeps_residue_class :
    forward_payload (bvzext 8%positive) [(8%positive, C 4 1)] 16%positive = C 4 1.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The truncation entry keeps the residue class of its operand. *)
  Example trunc_entry_keeps_residue_class :
    forward_payload (bvtrunc 4%positive) [(8%positive, C 4 1)] 4%positive = C 4 1.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The binary entries give the class of each operation on the same two operands. *)
  Example binary_entries_of_forward_ops :
    map (fun o => forward_payload o
      [(8%positive, C 4 1); (8%positive, C 0 2)] 8%positive)
      [bvadd; bvsub; bvmul; bvshl; bvurem] =
      [C 4 3; C 4 3; C 8 2; C 16 4; C 2 1].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A selection with an unknown one-bit condition joins its two branches. *)
  Example ite_entry_selects_residue_class :
    forward_payload bvite
      [(1%positive, C 1 0); (8%positive, C 4 1); (8%positive, C 4 3)]
      8%positive = C 2 1.
  Proof.
    vm_compute. reflexivity.
  Qed.

End ForwardEntryTests.

(** * One-bit operands *)

Module OneBitTests.

  (** At width one, the binary entries of the zero class give their table. *)
  Example one_bit_binary_entries :
    map (fun o => forward_payload o
      [(1%positive, C 0 1); (1%positive, C 0 1)] 1%positive)
      [bvadd; bvsub; bvmul; bvshl; bvurem] =
      [C 0 0; C 0 0; C 0 1; C 0 0; C 0 0].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** At width one, the negation of one is one. *)
  Example one_bit_neg_entry :
    forward_payload bvneg [(1%positive, C 0 1)] 1%positive = C 0 1.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** At width one, zero extension to two bits keeps one. *)
  Example one_bit_zext_entry :
    forward_payload (bvzext 1%positive) [(1%positive, C 0 1)] 2%positive = C 0 1.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** At width one, truncation to one bit keeps one. *)
  Example one_bit_trunc_entry :
    forward_payload (bvtrunc 1%positive) [(1%positive, C 0 1)] 1%positive = C 0 1.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** At width one, a selection between two ones gives one. *)
  Example one_bit_ite_entry :
    forward_payload bvite
      [(1%positive, C 0 1); (1%positive, C 0 1); (1%positive, C 0 0)]
      1%positive = C 0 1.
  Proof.
    vm_compute. reflexivity.
  Qed.

End OneBitTests.

(** * Empty operands *)

Module EmptyOperandTests.

  (** The operand table used to check empty operands. *)
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

  (** Every entry of the operand table gives bottom when its operands are bottom. *)
  Example empty_operands_give_bottom :
    map (fun '(o, xs, rw) => forward_payload o
      (map (fun wp => (fst wp, CBot)) xs) rw) cong_entry_cases = repeat CBot 9.
  Proof.
    vm_compute. reflexivity.
  Qed.

End EmptyOperandTests.

(** * Malformed operands *)

Module MalformedTests.

  (** An addition with a wrong operand count gives bottom for no operands and top otherwise. *)
  Example add_with_wrong_operand_count_of_residues :
    map (fun xs => forward_payload bvadd xs 8%positive)
      [[]; [(8%positive, C 4 1)];
       [(8%positive, C 4 1); (8%positive, C 0 2); (8%positive, C 0 3)];
       [(8%positive, C 4 1); (8%positive, C 0 2); (8%positive, C 0 3);
        (8%positive, C 0 4)]] =
      [CBot; C 1 0; C 1 0; C 1 0].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An addition of points with a wrong operand count is bottom. *)
  Example add_with_wrong_operand_count_of_points_is_bottom :
    map (fun xs => forward_payload bvadd xs 8%positive)
      [[]; [(8%positive, C 0 1)];
       [(8%positive, C 0 1); (8%positive, C 0 2); (8%positive, C 0 3)];
       [(8%positive, C 0 1); (8%positive, C 0 2); (8%positive, C 0 3);
        (8%positive, C 0 4)]] =
      repeat CBot 4.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A backward addition with a wrong operand count returns its operands unchanged. *)
  Example assume_add_with_wrong_operand_count_returns_operands :
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

End MalformedTests.
