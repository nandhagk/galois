(** * Known-bit word operations

    These operations connect known-bit masks to word transfers.
    For example, evaluating a zero-preserving operator keeps known zero bits.
    Builds on: KnownBits and the bit-vector operations. *)

From Stdlib Require Import ZArith List Bool.
From Galois.Bits Require Import Word Op Fun.
From Galois.Domains Require Import WordSig KnownBitsSig KnownBits.
Import List.ListNotations.
Local Open Scope Z_scope.

Module KnownBitsOpsCode (L : WORD_LANGUAGE_OPS) (C : TNUM_CONFIG)
    (K : KNOWN_BITS_OPS L C).
  Definition tnum_forward_raw (o : op) (wps : list (width * tnum)) (rw : width) : tnum :=
    match o, wps with
    | bvnot, [(_, a)] => K.tnum_not rw a
    | bvneg, [(_, a)] => K.tnum_neg rw a
    | (bvclz | bvctz | bvpopcnt), [_] => tnum_count rw
    | bvadd, [(_, a); (_, b)] => K.tnum_add rw a b
    | bvsub, [(_, a); (_, b)] => K.tnum_sub rw a b
    | bvmul, [(w, a); (v, b)] =>
      if Pos.eqb w rw && Pos.eqb v rw then K.tnum_mul rw a b
      else tnum_mul rw a b
    | bvudiv, [(_, a); (_, b)] => tnum_udiv rw a b
    | bvurem, [(_, a); _] => tnum_urem rw a
    | bvsrem, [(_, a); _] => tnum_srem rw a
    | bvand, [(_, a); (_, b)] => K.tnum_and rw a b
    | bvor, [(_, a); (_, b)] => K.tnum_or rw a b
    | bvxor, [(_, a); (_, b)] => K.tnum_xor rw a b
    | (bvshl | bvlshr | bvashr | bvrotl | bvrotr), [(_, a); (_, b)] =>
      K.tnum_variable o rw a b
    | (bveq | bvne | bvult | bvule | bvslt | bvsle), [(w, a); (_, b)] =>
      tnum_compare o w a b
    | bvite, [(_, c); (_, a); (_, b)] => tnum_ite rw c a b
    | (bvzext _ | bvtrunc _), [(w, a)] => tnum_map w rw (wrap rw) a
    | bvsext _, [(w, a)] => tnum_map w rw (fun x => wrap rw (signed w x)) a
    | bvextract _ lo, [(w, a)] => tnum_map w rw (fun x => wrap rw (x / 2 ^ Z.of_nat lo)) a
    | bvconcat, [(w, a); (v, b)] => tnum_concat w v a b
    | _, _ => tnum_top
    end.
End KnownBitsOpsCode.

Definition tnum_payload_sound (wp : width * tnum) (y : word) : Prop :=
  fst wp = fst y /\ is_word (fst y) (snd y) /\ tnum_gamma (fst wp) (snd wp) (snd y).

Module KnownBitsForwardProof (L : WORD_LANGUAGE_OPS) (C : TNUM_CONFIG).
  Module P := KnownBitsCode L C.
  Module F := KnownBitsOpsCode L C P.

  Theorem tnum_forward_raw_sound : forall o wps ys rw z,
    Forall2 tnum_payload_sound wps ys -> eval_op o ys = Some (rw, z) ->
    tnum_gamma rw (F.tnum_forward_raw o wps rw) z.
  Proof. Admitted. (* CONVERT: tnum_forward_raw_sound: The variable tnum_forward_one_sound was not found in the current environment. *)
End KnownBitsForwardProof.
