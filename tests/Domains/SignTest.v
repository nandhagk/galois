(** * Sign domain examples

    These examples exercise transfers, numeric refinement, intersection and finite height.
    For example, incompatible sign classes intersect to bottom.
    Builds on: Sign. *)

From Stdlib Require Import ZArith List.
From Galois.Bits Require Import Word Op Expr.
From Galois.Domains Require Import WordSig Tagged Sign SignSig BitsLang Harness.
Import List.ListNotations Expr.
Local Open Scope Z_scope.
Module Payload := SignCode WordLanguageCode.
Module Table := SignTableCode WordLanguageCode Payload.
Module Base := TaggedCode WordLanguageCode Payload.
Module TaggedTable := TaggedTableCode WordLanguageCode Payload Table.
Module Domain := HarnessCode BitsLangCode Base TaggedTable.

Definition forward_signs o xs := Domain.forward (BOp o) xs.
Definition const_signs w z := TVal w (Payload.pconst w z).
Definition top_signs w := TVal w (Payload.ptop w).
Definition payload_at w (a : tagged sgn) :=
  match a with TBot => Payload.pbot w | TVal _ p => p | TAny => Payload.ptop w end.
Definition forward_payload o xs rw :=
  payload_at rw (forward_signs o (map (fun wp => TVal (fst wp) (snd wp)) xs)).

Example sign_intersection_zero :
  Payload.pmeet 8%positive (Sgn true true false) (Sgn false true true) = Sgn false true false.
Proof.
  vm_compute. reflexivity.
Qed.

Example sign_intersection_disjoint :
  Payload.pmeet 8%positive (Sgn true false false) (Sgn false false true) = Payload.pbot 8%positive.
Proof.
  vm_compute. reflexivity.
Qed.

(* The former height bound was 3%nat; the current interface exposes a widening rank.
Example sign_height_bound : bound sign_height_on = 3%nat.
Proof.
  vm_compute. reflexivity.
Qed.

*)
Definition w1 : width := 1%positive.
Definition w8 : width := 8%positive.
Definition w16 : width := 16%positive.

Example one_bit_signed_boolean :
  const_signs w1 1 = TVal w1 (Sgn true false false) /\
  forward_signs bveq [const_signs w1 1; const_signs w1 1] =
    TVal w1 (Sgn true false false).
Proof.
  vm_compute. split; reflexivity.
Qed.

Example signed_comparison_decisions :
  forward_signs bvslt [TVal w8 (Sgn true false false); TVal w8 (Sgn false false true)] =
    TVal w1 (Sgn true false false) /\
  forward_signs bvult [TVal w8 (Sgn true false false); TVal w8 (Sgn false true true)] =
    TVal w1 (Sgn false true false) /\
  forward_signs bveq [TVal w8 (Sgn true false false); TVal w8 (Sgn false false true)] =
    TVal w1 (Sgn false true false).
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Example sign_transfer_table :
  forward_signs bvand [TVal w8 (Sgn true false false); TVal w8 (Sgn false false true)] =
    TVal w8 (Sgn false true true) /\
  forward_signs bvor [TVal w8 (Sgn true false false); TVal w8 (Sgn false false true)] =
    TVal w8 (Sgn true false false) /\
  forward_signs bvxor [TVal w8 (Sgn true false false); TVal w8 (Sgn true false false)] =
    TVal w8 (Sgn false true true) /\
  forward_signs bvnot [TVal w8 (Sgn true false false)] = TVal w8 (Sgn false true true) /\
  forward_signs bvneg [const_signs w8 128] = TVal w8 (Sgn true false true).
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Example sign_refinement :
  Base.meet (TVal w8 (Sgn false true true))
    (TVal w8 (Sgn true true false)) = TVal w8 (Sgn false true false).
Proof.
  vm_compute. reflexivity.
Qed.

Example sign_extensions :
  forward_signs (bvzext w8) [TVal w8 (Sgn true false false)] =
    TVal w16 (Sgn false true true) /\
  forward_signs (bvsext w8) [TVal w8 (Sgn true false false)] =
    TVal w16 (Sgn true false false) /\
  forward_signs bvite [top_signs w1; TVal w8 (Sgn true false false);
    TVal w8 (Sgn false false true)] = TVal w8 (Sgn true false true).
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Example sign_all_comparisons :
  map (fun o => forward_signs o
    [TVal w8 (Sgn true false false); TVal w8 (Sgn false false true)])
    [bveq; bvne; bvult; bvule; bvslt; bvsle] =
    [TVal w1 (Sgn false true false); TVal w1 (Sgn true false false);
     TVal w1 (Sgn false true false); TVal w1 (Sgn false true false);
     TVal w1 (Sgn true false false); TVal w1 (Sgn true false false)].
Proof.
  vm_compute. reflexivity.
Qed.

Definition sign_entry_cases :=
  [(bvnot, [(w8, (Payload.ptop w8))], w8); (bvneg, [(w8, (Payload.ptop w8))], w8);
   (bvzext w8, [(w8, (Payload.ptop w8))], w16); (bvsext w8, [(w8, (Payload.ptop w8))], w16);
   (bvand, [(w8, (Payload.ptop w8)); (w8, (Payload.ptop w8))], w8);
   (bvor, [(w8, (Payload.ptop w8)); (w8, (Payload.ptop w8))], w8);
   (bvxor, [(w8, (Payload.ptop w8)); (w8, (Payload.ptop w8))], w8);
   (bveq, [(w8, (Payload.ptop w8)); (w8, (Payload.ptop w8))], w1);
   (bvne, [(w8, (Payload.ptop w8)); (w8, (Payload.ptop w8))], w1);
   (bvult, [(w8, (Payload.ptop w8)); (w8, (Payload.ptop w8))], w1);
   (bvule, [(w8, (Payload.ptop w8)); (w8, (Payload.ptop w8))], w1);
   (bvslt, [(w8, (Payload.ptop w8)); (w8, (Payload.ptop w8))], w1);
   (bvsle, [(w8, (Payload.ptop w8)); (w8, (Payload.ptop w8))], w1);
   (bvite, [(w1, (Payload.ptop w8)); (w8, (Payload.ptop w8)); (w8, (Payload.ptop w8))], w8)].

Example sign_empty_entries :
  map (fun '(o, xs, rw) => forward_payload o
    (map (fun wp => (fst wp, Sgn false false false)) xs) rw) sign_entry_cases =
    repeat (Sgn false false false) 14.
Proof.
  vm_compute. reflexivity.
Qed.

Example sign_one_bit_entries :
  map (fun o => forward_payload o
    [(w1, Sgn true false false); (w1, Sgn true false false)] w1)
    [bvand; bvor; bvxor; bveq; bvne; bvult; bvule; bvslt; bvsle] =
    [Sgn true false false; Sgn true false false; Sgn false true true;
     Sgn true false false; Sgn false true false; Sgn false true false;
     Sgn true false false; Sgn false true false; Sgn true false false] /\
  forward_payload bvnot [(w1, Sgn true false false)] w1 =
    Sgn false true true /\
  forward_payload bvneg [(w1, Sgn true false false)] w1 =
    Sgn true false true /\
  forward_payload (bvzext 1%positive) [(w1, Sgn true false false)] 2%positive =
    Sgn false true true /\
  forward_payload (bvsext 1%positive) [(w1, Sgn true false false)] 2%positive =
    Sgn true false false /\
  forward_payload bvite
    [(w1, (Payload.ptop w8)); (w1, Sgn true false false); (w1, Sgn false true false)] w1 =
    Sgn true true false.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

