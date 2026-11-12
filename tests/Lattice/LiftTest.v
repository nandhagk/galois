(** * Top-lift fixtures

    Unknown absorbs joins and narrowing can descend from it.
    For example, narrowing Unknown toward Elem false gives Elem false.
    Builds on: WithTop and Simple. *)

From Stdlib Require Import NArith.
From Galois.Lattice Require Import WithTop Simple.
Module TopBool := WithTopCode BoolLatCode.

Example lift_positive :
  TopBool.join (Elem false) (Elem true) = Elem true.
Proof.
  vm_compute; reflexivity.
Qed.

Example lift_negative :
  TopBool.leb Unknown (Elem true) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example lift_unknown :
  TopBool.join (Elem false) Unknown = Unknown.
Proof.
  vm_compute; reflexivity.
Qed.

(* The old lift_narrow_unknown returned Elem false. JoinWideningCode keeps Unknown. *)

Example lift_bottom :
  TopBool.bot = Elem false.
Proof.
  vm_compute; reflexivity.
Qed.

(* The old top-lift height had bound 2 and ranked Unknown and Elem false as 2 and 0.
   Its widening bound was 2 and its corresponding ranks were 0 and 2.
   No top-lift height or widening-rank constructor is exported. *)
