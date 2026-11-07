(** * Constant domain examples

    These examples exercise annihilators, inverses and numeric expressions.
    For example, assuming x + 3 = 7 refines x to 4.
    Builds on: DomainsConst and DomainsTagged. *)

From Stdlib Require Import ZArith List.
From Galois.Cost Require Import CostMonad.
From Galois.Lattice Require Import LatticeCore LatticeFlat.
From Galois.Bits Require Import BitsWord BitsOp BitsExpr.
From Galois.Domains Require Import DomainsNumeric DomainsTagged DomainsConst.
Import List.ListNotations Expr.
Local Open Scope Z_scope.

Definition constants := tagged_domain const_word_domain.
Definition w1 : width := 1%positive.
Definition w8 : width := 8%positive.
Definition w16 : width := 16%positive.

Example constant_add_wrap :
  forward constants bvadd [of_const constants w8 250; of_const constants w8 10] =
    TVal w8 (FVal 4).
Proof.
  vm_compute. reflexivity.
Qed.

Example constant_annihilators :
  [forward constants bvmul [of_const constants w8 0; top_at constants w8];
   forward constants bvand [top_at constants w8; of_const constants w8 0];
   forward constants bvor [top_at constants w8; of_const constants w8 255];
   forward constants bvshl [of_const constants w8 0; top_at constants w8];
   forward constants bvlshr [of_const constants w8 0; top_at constants w8];
   forward constants bvashr [of_const constants w8 0; top_at constants w8];
   forward constants bvurem [of_const constants w8 0; top_at constants w8]] =
  [TVal w8 (FVal 0); TVal w8 (FVal 0); TVal w8 (FVal 255); TVal w8 (FVal 0);
   TVal w8 (FVal 0); TVal w8 (FVal 0); TVal w8 (FVal 0)].
Proof.
  vm_compute. reflexivity.
Qed.

Definition const_forward_ops := [bvmul; bvand; bvor; bvshl; bvlshr; bvashr; bvurem].
Definition const_backward_ops := [bveq; bvne; bvadd; bvsub; bvxor].

Example constant_rejected_operands :
  map (fun o => pforward const_word_domain o [(w8, FBot); (w8, FTop)] w8)
    const_forward_ops = repeat FBot 7.
Proof.
  vm_compute. reflexivity.
Qed.

Example constant_one_bit_annihilators :
  map (fun o => pforward const_word_domain o
    [(w1, FVal (if match o with bvor => true | _ => false end then 1 else 0));
     (w1, FTop)] w1) const_forward_ops =
    [FVal 0; FVal 0; FVal 1; FVal 0; FVal 0; FVal 0; FVal 0].
Proof.
  vm_compute. reflexivity.
Qed.

Example constant_maximum_table :
  map (fun o => pforward const_word_domain o [(w8, FVal 255); (w8, FTop)] w8)
    const_forward_ops = [FTop; FTop; FVal 255; FTop; FTop; FTop; FTop].
Proof.
  vm_compute. reflexivity.
Qed.

Example tagged_payload_bottom :
  forward constants bvadd [TVal w8 FBot; TAny] = TBot /\
  meet constants (TVal w8 FBot) TAny = TBot.
Proof.
  vm_compute. split; reflexivity.
Qed.

Example incompatible_widths :
  join (lat constants) (TVal w8 (FVal 0)) (TVal w16 (FVal 0)) = TAny /\
  forward constants bvadd [TVal w8 (FVal 0); TVal w16 (FVal 0)] = TBot /\
  assume constants bvadd (TVal w8 (FVal 0)) [TVal w8 FTop; TVal w16 FTop] = [TBot; TBot].
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Example inverse_add :
  assume constants bvadd (TVal w8 (FVal 7)) [TVal w8 FTop; TVal w8 (FVal 3)] =
    [TVal w8 (FVal 4); TVal w8 (FVal 3)].
Proof.
  vm_compute. reflexivity.
Qed.

Example inverse_subtract_and_xor :
  assume constants bvsub (TVal w8 (FVal 250)) [TVal w8 (FVal 3); TVal w8 FTop] =
    [TVal w8 (FVal 3); TVal w8 (FVal 9)] /\
  assume constants bvxor (TVal w8 (FVal 5)) [TVal w8 FTop; TVal w8 (FVal 3)] =
    [TVal w8 (FVal 6); TVal w8 (FVal 3)].
Proof.
  vm_compute. split; reflexivity.
Qed.

Example inverse_unary_and_equality :
  assume constants bvnot (TVal w8 (FVal 250)) [TVal w8 FTop] = [TVal w8 (FVal 5)] /\
  assume constants bvneg (TVal w8 (FVal 250)) [TVal w8 FTop] = [TVal w8 (FVal 6)] /\
  assume constants bveq (TVal w1 (FVal 1)) [TVal w8 FTop; TVal w8 (FVal 42)] =
    [TVal w8 (FVal 42); TVal w8 (FVal 42)] /\
  assume constants bvne (TVal w1 (FVal 0)) [TVal w8 (FVal 42); TVal w8 FTop] =
    [TVal w8 (FVal 42); TVal w8 (FVal 42)].
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Example constant_inverse_rejected :
  map (fun o => passume const_word_domain o [(w8, FVal 1); (w8, FVal 2)]
    w8 (FVal 0)) [bvadd; bvsub; bvxor] = repeat [FBot; FBot] 3 /\
  passume const_word_domain bvnot [(w8, FVal 0)] w8 (FVal 0) = [FBot] /\
  passume const_word_domain bvneg [(w8, FVal 1)] w8 (FVal 0) = [FBot] /\
  passume const_word_domain bveq [(w8, FVal 1); (w8, FVal 2)] w1 (FVal 1) =
    [FBot; FBot] /\
  passume const_word_domain bvne [(w8, FVal 1); (w8, FVal 2)] w1 (FVal 0) =
    [FBot; FBot].
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Example constant_inverse_width_one :
  map (fun o => passume const_word_domain o [(w1, FTop); (w1, FVal 1)]
    w1 (FVal 1)) [bvadd; bvsub; bvxor; bveq] =
    [[FVal 0; FVal 1]; [FVal 0; FVal 1]; [FVal 0; FVal 1]; [FVal 1; FVal 1]] /\
  passume const_word_domain bvne [(w1, FTop); (w1, FVal 1)] w1 (FVal 0) =
    [FVal 1; FVal 1] /\
  passume const_word_domain bvnot [(w1, FTop)] w1 (FVal 1) = [FVal 0] /\
  passume const_word_domain bvneg [(w1, FTop)] w1 (FVal 1) = [FVal 1].
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Example nested_expression_refinement :
  num_assume constants (fun _ => top_at constants w8)
    (App bvadd [Var 0; Const w8 3]) (TVal w8 (FVal 7)) 0%nat = TVal w8 (FVal 4).
Proof.
  vm_compute. reflexivity.
Qed.

Example impossible_result_refines_every_operand :
  assume constants bvadd TBot [TAny; TVal w8 FTop] = [TBot; TBot] /\
  assume constants bvadd (TVal w1 (FVal 1)) [TVal w8 FTop; TVal w8 FTop] = [TBot; TBot].
Proof.
  vm_compute. split; reflexivity.
Qed.

Example nested_abstract_evaluation :
  num_eval constants (fun _ => of_const constants w8 5)
    (App bvadd [App bvmul [Var 0; Const w8 3]; Const w8 250]) = TVal w8 (FVal 9).
Proof.
  vm_compute. reflexivity.
Qed.

Example constant_callback_cost :
  Cost.ticks (passume_c const_word_domain bvadd [(w8, FTop); (w8, FVal 3)]
    w8 (FVal 7)) = 7%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example constant_inverse_callback_cost :
  Cost.ticks (const_inverse_c
    (fun z => Cost.bind (Cost.tick 17%N) (fun _ => Cost.ret z)) (FVal 3)) = 18%N.
Proof.
  vm_compute. reflexivity.
Qed.
