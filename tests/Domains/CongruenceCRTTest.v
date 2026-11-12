(** * Exact CRT observations

    These fixtures compare the first-order CRT loop with the standard library.
    For example, signed inputs keep the same ordered Bezout coefficients.
    Builds on: Congruence and BitsLang. *)

From Stdlib Require Import ZArith List Bool.
From Galois.Domains Require Import Congruence CongruenceSig BitsLang.
Import List.ListNotations.
Local Open Scope Z_scope.

Module Payload := CongruenceCode WordLanguageCode.

Definition triple_eqb (a b : Z * Z * Z) : bool :=
  let '(u, v, d) := a in
  let '(u', v', d') := b in
  (u =? u') && (v =? v') && (d =? d').

Definition signed_samples : list Z := [-8; -3; -1; 0; 1; 2; 6; 9].

Example extgcd_signed_reference :
  forallb (fun a => forallb (fun b =>
    triple_eqb (CongruenceCRT.extgcd a b) (Z.extgcd a b)) signed_samples)
    signed_samples = true.
Proof. vm_compute. reflexivity. Qed.

Example crt_signed_reference :
  forallb (fun m => forallb (fun n =>
    forallb (fun r => forallb (fun s =>
      CongruenceCRT.combinecong m n r s =? Z.combinecong m n r s)
      signed_samples) signed_samples) signed_samples) signed_samples = true.
Proof. vm_compute. reflexivity. Qed.

Example extgcd_long_reference :
  CongruenceCRT.extgcd 17167680177565 27777890035288 =
    Z.extgcd 17167680177565 27777890035288.
Proof. vm_compute. reflexivity. Qed.

Definition reference_pmeet w a b :=
  match Payload.congr_norm w a, Payload.congr_norm w b with
  | CBot, _ | _, CBot => CBot
  | C m r, C n s =>
    if r mod Z.gcd m n =? s mod Z.gcd m n then
      Payload.congr_norm w (C (Z.lcm m n) (Z.combinecong m n r s))
    else CBot
  end.

Definition payload_samples : list congr :=
  [CBot; C 0 0; C 0 3; C 0 (-1); C 0 300; C (-6) (-7); C 4 3; C 9 5].

Definition congr_eqb (a b : congr) : bool :=
  match a, b with
  | CBot, CBot => true
  | C m r, C n s => (m =? n) && (r =? s)
  | _, _ => false
  end.

Example meet_long_reference :
  Payload.pmeet 46%positive (C 17167680177565 0) (C 27777890035288 0) =
    reference_pmeet 46%positive (C 17167680177565 0) (C 27777890035288 0).
Proof. vm_compute. reflexivity. Qed.

Example meet_reference :
  forallb (fun w => forallb (fun a => forallb (fun b =>
    congr_eqb (Payload.pmeet w a b) (reference_pmeet w a b) &&
    congr_eqb (Payload.pnarrow w a b) (reference_pmeet w a b))
    payload_samples) payload_samples) [1%positive; 4%positive; 8%positive] = true.
Proof. vm_compute. reflexivity. Qed.

Definition div_pair_eqb (a b : Z * Z) : bool :=
  (fst a =? fst b) && (snd a =? snd b).

Example aligned_division_reference :
  forallb (fun a => forallb (fun b =>
    div_pair_eqb (CongruenceCRT.div_aligned (Z.of_nat a) (Z.of_nat b))
      (Z.div_eucl (Z.of_nat a) (Z.of_nat b))) (seq 1 32)) (seq 0 128) = true.
Proof. vm_compute. reflexivity. Qed.

Example aligned_division_small_dividend :
  CongruenceCRT.div_aligned 1 (2 ^ 128) = (0, 1).
Proof. vm_compute. reflexivity. Qed.

Example aligned_division_large_quotient :
  CongruenceCRT.div_aligned (2 ^ 128 + 7) 3 = Z.div_eucl (2 ^ 128 + 7) 3.
Proof. vm_compute. reflexivity. Qed.
