(** * Key tactic clients

    Symbolic examples exercise tests in goals and hypotheses and structural round trips.
    For example, the raw positive equality form uses the same law as [eqb].
    Builds on: BaseKeyTactics and BaseCode. *)

From Stdlib Require Import Bool List NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseCode BaseEq BaseKeyTactics.
Import List.ListNotations.

Local Open Scope positive_scope.

Example case_key_goal {K} (E : encoding K) (HE : encoding_laws E) a b :
  (if eqb E a b then a = b else a <> b).
Proof.
  case_key; assumption.
Qed.

Example case_key_hypothesis {K} (E : encoding K) (HE : encoding_laws E) a b :
  eqb E a b = true -> a = b.
Proof.
  intro Htest. case_key; congruence.
Qed.

Example case_key_raw {K} (E : encoding K) (HE : encoding_laws E) a b :
  (if Pos.eqb (encode E a) (encode E b) then a = b else a <> b).
Proof.
  case_key; assumption.
Qed.

Example case_key_raw_hypothesis {K} (E : encoding K) (HE : encoding_laws E) a b :
  Pos.eqb (encode E a) (encode E b) = false -> a <> b.
Proof.
  intro Htest. case_key; congruence.
Qed.

Example case_key_mixed {K} (E : encoding K) (HE : encoding_laws E) a b :
  Pos.eqb (encode E a) (encode E b) = eqb E a b.
Proof.
  case_key; reflexivity.
Qed.

Example solve_pair {A B} (CA : codec A) (CB : codec B)
    (HA : codec_laws CA) (HB : codec_laws CB) :
  forall xy, pair_of_code CA CB (Cost.value (pair_to_code_c CA CB xy)) = Some xy.
Proof.
  solve_roundtrip.
Qed.

Example solve_list {A} (CA : codec A) (HA : codec_laws CA) :
  forall xs, list_of_atoms CA (Cost.value (list_atoms_c CA xs)) = Some xs.
Proof.
  solve_roundtrip.
Qed.

Example solve_option {A} (CA : codec A) (HA : codec_laws CA) :
  forall x, option_of_code CA (Cost.value (option_to_code_c CA x)) = Some x.
Proof.
  solve_roundtrip.
Qed.

Example key_positive : eqb positive_encoding 1 1 = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example key_negative : eqb positive_encoding 1 2 = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example key_boundary :
  option_of_code positive_codec (Cost.value (option_to_code_c positive_codec None)) = Some None.
Proof.
  vm_compute. reflexivity.
Qed.
