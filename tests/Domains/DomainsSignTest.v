(** * Sign domain examples

    These examples exercise transfers, numeric refinement, intersection and finite height.
    For example, incompatible sign classes intersect to bottom.
    Builds on: DomainsSign. *)

From Stdlib Require Import ZArith List.
From Galois.Cost Require Import CostMonad.
From Galois.Lattice Require Import LatticeCore LatticeHeight.
From Galois.Bits Require Import BitsWord BitsOp BitsExpr.
From Galois.Domains Require Import DomainsNumeric DomainsTagged DomainsSign.
Import List.ListNotations Expr.
Local Open Scope Z_scope.

Example sign_intersection_zero :
  sign_meet (Sign true true false) (Sign false true true) = Sign false true false.
Proof.
  vm_compute. reflexivity.
Qed.

Example sign_intersection_disjoint :
  sign_meet (Sign true false false) (Sign false false true) = bot sign_lattice.
Proof.
  vm_compute. reflexivity.
Qed.

Example sign_height_bound : bound sign_height_on = 3%nat.
Proof.
  vm_compute. reflexivity.
Qed.

Definition signs := tagged_domain sign_word_domain.
Definition w1 : width := 1%positive.
Definition w8 : width := 8%positive.
Definition w16 : width := 16%positive.

Example one_bit_signed_boolean :
  of_const signs w1 1 = TVal w1 (Sign true false false) /\
  forward signs bveq [of_const signs w1 1; of_const signs w1 1] =
    TVal w1 (Sign true false false).
Proof.
  vm_compute. split; reflexivity.
Qed.

Example signed_comparison_decisions :
  forward signs bvslt [TVal w8 (Sign true false false); TVal w8 (Sign false false true)] =
    TVal w1 (Sign true false false) /\
  forward signs bvult [TVal w8 (Sign true false false); TVal w8 (Sign false true true)] =
    TVal w1 (Sign false true false) /\
  forward signs bveq [TVal w8 (Sign true false false); TVal w8 (Sign false false true)] =
    TVal w1 (Sign false true false).
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Example sign_transfer_table :
  forward signs bvand [TVal w8 (Sign true false false); TVal w8 (Sign false false true)] =
    TVal w8 (Sign false true true) /\
  forward signs bvor [TVal w8 (Sign true false false); TVal w8 (Sign false false true)] =
    TVal w8 (Sign true false false) /\
  forward signs bvxor [TVal w8 (Sign true false false); TVal w8 (Sign true false false)] =
    TVal w8 (Sign false true true) /\
  forward signs bvnot [TVal w8 (Sign true false false)] = TVal w8 (Sign false true true) /\
  forward signs bvneg [of_const signs w8 128] = TVal w8 (Sign true false true).
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Example sign_refinement :
  num_assume signs (fun _ => TVal w8 (Sign false true true)) (Var 0)
    (TVal w8 (Sign true true false)) 0%nat = TVal w8 (Sign false true false).
Proof.
  vm_compute. reflexivity.
Qed.

Example sign_extensions :
  forward signs (bvzext w8) [TVal w8 (Sign true false false)] =
    TVal w16 (Sign false true true) /\
  forward signs (bvsext w8) [TVal w8 (Sign true false false)] =
    TVal w16 (Sign true false false) /\
  forward signs bvite [top_at signs w1; TVal w8 (Sign true false false);
    TVal w8 (Sign false false true)] = TVal w8 (Sign true false true).
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Example sign_all_comparisons :
  map (fun o => forward signs o
    [TVal w8 (Sign true false false); TVal w8 (Sign false false true)])
    [bveq; bvne; bvult; bvule; bvslt; bvsle] =
    [TVal w1 (Sign false true false); TVal w1 (Sign true false false);
     TVal w1 (Sign false true false); TVal w1 (Sign false true false);
     TVal w1 (Sign true false false); TVal w1 (Sign true false false)].
Proof.
  vm_compute. reflexivity.
Qed.

Definition sign_entry_cases :=
  [(bvnot, [(w8, sign_top)], w8); (bvneg, [(w8, sign_top)], w8);
   (bvzext w8, [(w8, sign_top)], w16); (bvsext w8, [(w8, sign_top)], w16);
   (bvand, [(w8, sign_top); (w8, sign_top)], w8);
   (bvor, [(w8, sign_top); (w8, sign_top)], w8);
   (bvxor, [(w8, sign_top); (w8, sign_top)], w8);
   (bveq, [(w8, sign_top); (w8, sign_top)], w1);
   (bvne, [(w8, sign_top); (w8, sign_top)], w1);
   (bvult, [(w8, sign_top); (w8, sign_top)], w1);
   (bvule, [(w8, sign_top); (w8, sign_top)], w1);
   (bvslt, [(w8, sign_top); (w8, sign_top)], w1);
   (bvsle, [(w8, sign_top); (w8, sign_top)], w1);
   (bvite, [(w1, sign_top); (w8, sign_top); (w8, sign_top)], w8)].

Example sign_empty_entries :
  map (fun '(o, xs, rw) => pforward sign_word_domain o
    (map (fun wp => (fst wp, Sign false false false)) xs) rw) sign_entry_cases =
    repeat (Sign false false false) 14.
Proof.
  vm_compute. reflexivity.
Qed.

Example sign_one_bit_entries :
  map (fun o => pforward sign_word_domain o
    [(w1, Sign true false false); (w1, Sign true false false)] w1)
    [bvand; bvor; bvxor; bveq; bvne; bvult; bvule; bvslt; bvsle] =
    [Sign true false false; Sign true false false; Sign false true true;
     Sign true false false; Sign false true false; Sign false true false;
     Sign true false false; Sign false true false; Sign true false false] /\
  pforward sign_word_domain bvnot [(w1, Sign true false false)] w1 =
    Sign false true true /\
  pforward sign_word_domain bvneg [(w1, Sign true false false)] w1 =
    Sign true false true /\
  pforward sign_word_domain (bvzext 1%positive) [(w1, Sign true false false)] 2%positive =
    Sign false true true /\
  pforward sign_word_domain (bvsext 1%positive) [(w1, Sign true false false)] 2%positive =
    Sign true false false /\
  pforward sign_word_domain bvite
    [(w1, sign_top); (w1, Sign true false false); (w1, Sign false true false)] w1 =
    Sign true true false.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Example sign_callback_cost :
  Cost.ticks (sign_unary
    (fun a => Cost.bind (Cost.tick 17%N) (fun _ => Cost.ret a))
    w8 [(w8, sign_top)]) = 18%N.
Proof.
  vm_compute. reflexivity.
Qed.
