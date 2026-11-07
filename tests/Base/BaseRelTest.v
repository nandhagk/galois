(** * Labelled path tests

    These examples distinguish valid paths, impossible paths and empty paths.
    For example, two successor edges form a labelled path from zero to two.
    Builds on: BaseRel. *)

From Stdlib Require Import List Arith.
From Galois.Base Require Import BaseRel.
Import List.ListNotations.

Definition next (x : nat) (_ : unit) (y : nat) : Prop := y = S x.

Example path_accepts : Rel.lpath next 0 [tt; tt] 2.
Proof.
  apply (Rel.lpath_cons next 0 tt 1 [tt] 2).
  - vm_compute. reflexivity.
  - apply (Rel.lpath_cons next 1 tt 2 [] 2).
    + vm_compute. reflexivity.
    + constructor.
Qed.

Example path_rejects : ~ Rel.lpath next 0 [tt] 0.
Proof.
  intro Hpath.
  inversion Hpath as [|x l y ls z Hstep Hsuffix]; subst.
  inversion Hsuffix; subst.
  discriminate Hstep.
Qed.

Example path_empty_boundary : Rel.lpath next 0 [] 0.
Proof.
  constructor.
Qed.

Example closure_nonempty : Rel.plus (fun x y : nat => y = S x) 0 2.
Proof.
  exists 1. split.
  - vm_compute. reflexivity.
  - apply (Rel.star_cons _ 1 2 2).
    + vm_compute. reflexivity.
    + constructor.
Qed.

Example closure_empty_boundary : Rel.star (fun _ _ : nat => False) 0 0.
Proof.
  constructor.
Qed.

Example closure_rejects : ~ Rel.star (fun _ _ : nat => False) 0 1.
Proof.
  intro Hstar. inversion Hstar; contradiction.
Qed.
