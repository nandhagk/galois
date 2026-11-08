(** * Congruence domain examples

    These examples exercise normalization, arithmetic and CRT intersection.
    For example, the intersection of 1 modulo 4 and 3 modulo 6 is 9 modulo 12.
    Builds on: DomainsCongruence. *)

From Stdlib Require Import ZArith List.
From Galois.Cost Require Import CostMonad.
From Galois.Lattice Require Import LatticeCore LatticeHeight.
From Galois.Bits Require Import BitsWord BitsOp.
From Galois.Domains Require Import DomainsNumeric DomainsCongruence.
Import List.ListNotations.
Local Open Scope Z_scope.

Example dom4_cong_residue : cong_norm 8%positive (Cong 4 6) = Cong 4 2.
Proof.
  vm_compute. reflexivity.
Qed.

Example dom4_cong_negative_modulus : cong_norm 8%positive (Cong (-4) 6) = Cong 4 2.
Proof.
  vm_compute. reflexivity.
Qed.

Example dom4_cong_large_modulus : cong_norm 8%positive (Cong 512 1) = Cong 0 1.
Proof.
  vm_compute. reflexivity.
Qed.

Example dom4_cong_large_empty : cong_norm 8%positive (Cong 512 300) = CBot.
Proof.
  vm_compute. reflexivity.
Qed.

Example dom4_cong_raw_exact_empty : cong_norm 8%positive (Cong 0 256) = CBot.
Proof.
  vm_compute. reflexivity.
Qed.

Example dom4_cong_join : join (cong_lattice 8%positive) (Cong 0 3) (Cong 0 7) = Cong 4 3.
Proof.
  vm_compute. reflexivity.
Qed.

Example dom4_cong_meet_incompatible : cong_meet 8%positive (Cong 2 0) (Cong 2 1) = CBot.
Proof.
  vm_compute. reflexivity.
Qed.

Example dom4_cong_meet_compatible : cong_meet 8%positive (Cong 4 1) (Cong 6 3) = Cong 12 9.
Proof.
  vm_compute. reflexivity.
Qed.

Example dom4_cong_height : rank (cong_height_on 8%positive) (Cong 1 0) = 10%nat.
Proof.
  vm_compute. reflexivity.
Qed.

Example dom4_cong_add : cong_add 8%positive (Cong 4 1) (Cong 8 2) = Cong 4 3.
Proof.
  vm_compute. reflexivity.
Qed.

Example dom4_cong_constant_mul : cong_mul 8%positive (Cong 0 17) (Cong 0 17) = Cong 0 33.
Proof.
  vm_compute. reflexivity.
Qed.

Example congruence_unary_entries :
  pforward cong_word_domain bvneg [(8%positive, Cong 4 1)] 8%positive = Cong 4 3 /\
  pforward cong_word_domain (bvzext 8%positive) [(8%positive, Cong 4 1)] 16%positive =
    Cong 4 1 /\
  pforward cong_word_domain (bvtrunc 4%positive) [(8%positive, Cong 4 1)] 4%positive =
    Cong 4 1.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Example congruence_binary_entries :
  map (fun o => pforward cong_word_domain o
    [(8%positive, Cong 4 1); (8%positive, Cong 0 2)] 8%positive)
    [bvadd; bvsub; bvmul; bvshl; bvurem] =
    [Cong 4 3; Cong 4 3; Cong 8 2; Cong 16 4; Cong 2 1].
Proof.
  vm_compute. reflexivity.
Qed.

Example congruence_selection_entry :
  pforward cong_word_domain bvite
    [(1%positive, Cong 1 0); (8%positive, Cong 4 1); (8%positive, Cong 4 3)]
    8%positive = Cong 2 1.
Proof.
  vm_compute. reflexivity.
Qed.

Definition cong_entry_cases :=
  [(bvneg, [(8%positive, Cong 4 1)], 8%positive);
   (bvzext 8%positive, [(8%positive, Cong 4 1)], 16%positive);
   (bvtrunc 4%positive, [(8%positive, Cong 4 1)], 4%positive);
   (bvadd, [(8%positive, Cong 4 1); (8%positive, Cong 0 2)], 8%positive);
   (bvsub, [(8%positive, Cong 4 1); (8%positive, Cong 0 2)], 8%positive);
   (bvmul, [(8%positive, Cong 4 1); (8%positive, Cong 0 2)], 8%positive);
   (bvshl, [(8%positive, Cong 4 1); (8%positive, Cong 0 2)], 8%positive);
   (bvurem, [(8%positive, Cong 4 1); (8%positive, Cong 0 2)], 8%positive);
   (bvite, [(1%positive, Cong 1 0); (8%positive, Cong 4 1);
     (8%positive, Cong 4 3)], 8%positive)].

Example congruence_empty_entries :
  map (fun '(o, xs, rw) => pforward cong_word_domain o
    (map (fun wp => (fst wp, CBot)) xs) rw) cong_entry_cases = repeat CBot 9.
Proof.
  vm_compute. reflexivity.
Qed.

Example congruence_one_bit_entries :
  map (fun o => pforward cong_word_domain o
    [(1%positive, Cong 0 1); (1%positive, Cong 0 1)] 1%positive)
    [bvadd; bvsub; bvmul; bvshl; bvurem] =
    [Cong 0 0; Cong 0 0; Cong 0 1; Cong 0 0; Cong 0 0] /\
  pforward cong_word_domain bvneg [(1%positive, Cong 0 1)] 1%positive = Cong 0 1 /\
  pforward cong_word_domain (bvzext 1%positive) [(1%positive, Cong 0 1)] 2%positive =
    Cong 0 1 /\
  pforward cong_word_domain (bvtrunc 1%positive) [(1%positive, Cong 0 1)] 1%positive =
    Cong 0 1 /\
  pforward cong_word_domain bvite
    [(1%positive, Cong 0 1); (1%positive, Cong 0 1); (1%positive, Cong 0 0)]
    1%positive = Cong 0 1.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Example congruence_maximum_and_zero_divisor :
  pforward cong_word_domain bvadd
    [(8%positive, Cong 0 255); (8%positive, Cong 0 1)] 8%positive = Cong 0 0 /\
  pforward cong_word_domain bvurem
    [(8%positive, Cong 4 1); (8%positive, Cong 0 0)] 8%positive = Cong 4 1.
Proof.
  vm_compute. split; reflexivity.
Qed.

Example congruence_callback_cost :
  Cost.ticks (cong_binary
    (fun _ a _ => Cost.bind (Cost.tick 17%N) (fun _ => Cost.ret a))
    8%positive [(8%positive, Cong 4 1); (8%positive, Cong 0 2)]) = 18%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example congruence_malformed_counts_nonpoint :
  map (fun xs => pforward cong_word_domain bvadd xs 8%positive)
    [[]; [(8%positive, Cong 4 1)];
     [(8%positive, Cong 4 1); (8%positive, Cong 0 2); (8%positive, Cong 0 3)];
     [(8%positive, Cong 4 1); (8%positive, Cong 0 2); (8%positive, Cong 0 3);
      (8%positive, Cong 0 4)]] =
    [CBot; Cong 1 0; Cong 1 0; Cong 1 0].
Proof.
  vm_compute. reflexivity.
Qed.

Example congruence_malformed_counts_points :
  map (fun xs => pforward cong_word_domain bvadd xs 8%positive)
    [[]; [(8%positive, Cong 0 1)];
     [(8%positive, Cong 0 1); (8%positive, Cong 0 2); (8%positive, Cong 0 3)];
     [(8%positive, Cong 0 1); (8%positive, Cong 0 2); (8%positive, Cong 0 3);
      (8%positive, Cong 0 4)]] =
    repeat CBot 4.
Proof.
  vm_compute. reflexivity.
Qed.

Example congruence_malformed_count_assumptions :
  map (fun xs => passume cong_word_domain bvadd xs 8%positive CBot)
    [[]; [(8%positive, Cong 4 1)]; [(8%positive, Cong 0 1)];
     [(8%positive, Cong 4 1); (8%positive, Cong 0 2); (8%positive, Cong 0 3)];
     [(8%positive, Cong 0 1); (8%positive, Cong 0 2); (8%positive, Cong 0 3);
      (8%positive, Cong 0 4)]] =
    [[]; [Cong 4 1]; [Cong 0 1]; [Cong 4 1; Cong 0 2; Cong 0 3];
     [Cong 0 1; Cong 0 2; Cong 0 3; Cong 0 4]].
Proof.
  vm_compute. reflexivity.
Qed.
