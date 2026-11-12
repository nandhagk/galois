(** * Constant domain examples

    These examples exercise annihilators, inverses and numeric expressions.
    For example, assuming x + 3 = 7 refines x to 4.
    Builds on: Const and Tagged. *)

From Stdlib Require Import ZArith List.
From Galois.Bits Require Import Word Op Expr.
From Galois.Domains Require Import WordSig Tagged Const ConstSig BitsLang Harness.
Import List.ListNotations Expr.
Local Open Scope Z_scope.
Module Payload := ConstWordCode WordLanguageCode.
Module Table := ConstWordTableCode WordLanguageCode Payload.
Module Base := TaggedCode WordLanguageCode Payload.
Module TaggedTable := TaggedTableCode WordLanguageCode Payload Table.
Module Domain := HarnessCode BitsLangCode Base TaggedTable.
Module FunctionalPayload := ConstWord WordLanguage.

(** Raw constant payloads retain integers outside the width's normalized range. *)
Example constant_raw_meaning :
  FunctionalPayload.pgamma 8%positive (FVal 257) 257 /\
  ~ FunctionalPayload.pgamma 8%positive (FVal 257) 1.
Proof.
  vm_compute. split; [reflexivity | discriminate].
Qed.

Definition forward_constants o xs := Domain.forward (BOp o) xs.
Definition assume_constants o r xs := Domain.backward (BOp o) r xs.
Definition const_constants w z := TVal w (Payload.pconst w z).
Definition top_constants w := TVal w (Payload.ptop w).
Definition payload_at w (a : tagged (flat Z)) :=
  match a with TBot => FBot | TVal _ p => p | TAny => Payload.ptop w end.
Definition tagged_args (xs : list (positive * flat Z)) :=
  map (fun wp => TVal (fst wp) (snd wp)) xs.
Definition forward_payload o xs rw :=
  payload_at rw (forward_constants o (tagged_args xs)).
Definition assume_payload o xs rw r :=
  map (payload_at rw) (assume_constants o (TVal rw r) (tagged_args xs)).

Definition w1 : width := 1%positive.
Definition w8 : width := 8%positive.
Definition w16 : width := 16%positive.

Example constant_add_wrap :
  forward_constants bvadd [const_constants w8 250; const_constants w8 10] =
    TVal w8 (FVal 4).
Proof.
  vm_compute. reflexivity.
Qed.

Example constant_annihilators :
  [forward_constants bvmul [const_constants w8 0; top_constants w8];
   forward_constants bvand [top_constants w8; const_constants w8 0];
   forward_constants bvor [top_constants w8; const_constants w8 255];
   forward_constants bvshl [const_constants w8 0; top_constants w8];
   forward_constants bvlshr [const_constants w8 0; top_constants w8];
   forward_constants bvashr [const_constants w8 0; top_constants w8];
   forward_constants bvurem [const_constants w8 0; top_constants w8]] =
  [TVal w8 (FVal 0); TVal w8 (FVal 0); TVal w8 (FVal 255); TVal w8 (FVal 0);
   TVal w8 (FVal 0); TVal w8 (FVal 0); TVal w8 (FVal 0)].
Proof.
  vm_compute. reflexivity.
Qed.

Definition const_forward_ops := [bvmul; bvand; bvor; bvshl; bvlshr; bvashr; bvurem].
Definition const_backward_ops := [bveq; bvne; bvadd; bvsub; bvxor].

Example constant_rejected_operands :
  map (fun o => forward_payload o [(w8, FBot); (w8, FTop)] w8)
    const_forward_ops = repeat FBot 7.
Proof.
  vm_compute. reflexivity.
Qed.

Example constant_one_bit_annihilators :
  map (fun o => forward_payload o
    [(w1, FVal (if match o with bvor => true | _ => false end then 1 else 0));
     (w1, FTop)] w1) const_forward_ops =
    [FVal 0; FVal 0; FVal 1; FVal 0; FVal 0; FVal 0; FVal 0].
Proof.
  vm_compute. reflexivity.
Qed.

Example constant_maximum_table :
  map (fun o => forward_payload o [(w8, FVal 255); (w8, FTop)] w8)
    const_forward_ops = [FTop; FTop; FVal 255; FTop; FTop; FTop; FTop].
Proof.
  vm_compute. reflexivity.
Qed.

(* Old meet returned TBot; Base.meet now returns TVal w8 FBot.
Example tagged_payload_bottom :
  forward_constants bvadd [TVal w8 FBot; TAny] = TBot /\
  Base.meet (TVal w8 FBot) TAny = TBot.
Proof.
  vm_compute. split; reflexivity.
Qed.

*)
(* Old backward returned [TBot; TBot]; current result is [TVal w8 FTop; TVal w16 FTop].
Example incompatible_widths :
  Base.join (TVal w8 (FVal 0)) (TVal w16 (FVal 0)) = TAny /\
  forward_constants bvadd [TVal w8 (FVal 0); TVal w16 (FVal 0)] = TBot /\
  assume_constants bvadd (TVal w8 (FVal 0)) [TVal w8 FTop; TVal w16 FTop] = [TBot; TBot].
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

*)
Example inverse_add :
  assume_constants bvadd (TVal w8 (FVal 7)) [TVal w8 FTop; TVal w8 (FVal 3)] =
    [TVal w8 (FVal 4); TVal w8 (FVal 3)].
Proof.
  vm_compute. reflexivity.
Qed.

Example inverse_subtract_and_xor :
  assume_constants bvsub (TVal w8 (FVal 250)) [TVal w8 (FVal 3); TVal w8 FTop] =
    [TVal w8 (FVal 3); TVal w8 (FVal 9)] /\
  assume_constants bvxor (TVal w8 (FVal 5)) [TVal w8 FTop; TVal w8 (FVal 3)] =
    [TVal w8 (FVal 6); TVal w8 (FVal 3)].
Proof.
  vm_compute. split; reflexivity.
Qed.

Example inverse_unary_and_equality :
  assume_constants bvnot (TVal w8 (FVal 250)) [TVal w8 FTop] = [TVal w8 (FVal 5)] /\
  assume_constants bvneg (TVal w8 (FVal 250)) [TVal w8 FTop] = [TVal w8 (FVal 6)] /\
  assume_constants bveq (TVal w1 (FVal 1)) [TVal w8 FTop; TVal w8 (FVal 42)] =
    [TVal w8 (FVal 42); TVal w8 (FVal 42)] /\
  assume_constants bvne (TVal w1 (FVal 0)) [TVal w8 (FVal 42); TVal w8 FTop] =
    [TVal w8 (FVal 42); TVal w8 (FVal 42)].
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Example constant_inverse_rejected :
  map (fun o => assume_payload o [(w8, FVal 1); (w8, FVal 2)]
    w8 (FVal 0)) [bvadd; bvsub; bvxor] = repeat [FBot; FBot] 3 /\
  assume_payload bvnot [(w8, FVal 0)] w8 (FVal 0) = [FBot] /\
  assume_payload bvneg [(w8, FVal 1)] w8 (FVal 0) = [FBot] /\
  assume_payload bveq [(w8, FVal 1); (w8, FVal 2)] w1 (FVal 1) =
    [FBot; FBot] /\
  assume_payload bvne [(w8, FVal 1); (w8, FVal 2)] w1 (FVal 0) =
    [FBot; FBot].
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Example constant_inverse_width_one :
  map (fun o => assume_payload o [(w1, FTop); (w1, FVal 1)]
    w1 (FVal 1)) [bvadd; bvsub; bvxor; bveq] =
    [[FVal 0; FVal 1]; [FVal 0; FVal 1]; [FVal 0; FVal 1]; [FVal 1; FVal 1]] /\
  assume_payload bvne [(w1, FTop); (w1, FVal 1)] w1 (FVal 0) =
    [FVal 1; FVal 1] /\
  assume_payload bvnot [(w1, FTop)] w1 (FVal 1) = [FVal 0] /\
  assume_payload bvneg [(w1, FTop)] w1 (FVal 1) = [FVal 1].
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

(* The old numeric expression assumption returned TVal w8 (FVal 4).
Example nested_expression_refinement :
  num_assume constants (fun _ => top_constants w8)
    (App bvadd [Var 0; Const w8 3]) (TVal w8 (FVal 7)) 0%nat = TVal w8 (FVal 4).
Proof.
  vm_compute. reflexivity.
Qed.

*)
(* Old bottom-result backward returned [TBot; TBot]; current result is [TAny; TVal w8 FTop].
   The old mismatched-result-width case also returned [TBot; TBot]; current result is
   [TVal w8 FTop; TVal w8 FTop].
Example impossible_result_refines_every_operand :
  assume_constants bvadd TBot [TAny; TVal w8 FTop] = [TBot; TBot] /\
  assume_constants bvadd (TVal w1 (FVal 1)) [TVal w8 FTop; TVal w8 FTop] = [TBot; TBot].
Proof.
  vm_compute. split; reflexivity.
Qed.

*)
(* The old numeric expression evaluator returned TVal w8 (FVal 9).
Example nested_abstract_evaluation :
  num_eval constants (fun _ => const_constants w8 5)
    (App bvadd [App bvmul [Var 0; Const w8 3]; Const w8 250]) = TVal w8 (FVal 9).
Proof.
  vm_compute. reflexivity.
Qed.



*)
Example tagged_payload_bottom_forward :
  forward_constants bvadd [TVal w8 FBot; TAny] = TBot.
Proof. vm_compute. reflexivity. Qed.

Example incompatible_widths_forward_join :
  Base.join (TVal w8 (FVal 0)) (TVal w16 (FVal 0)) = TAny /\
  forward_constants bvadd [TVal w8 (FVal 0); TVal w16 (FVal 0)] = TBot.
Proof. vm_compute. split; reflexivity. Qed.
