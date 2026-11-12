(** * Congruence payload code

    Congruences describe residues of normalized words.
    For example, modulus two and residue zero describe even words.
    Builds on: CongruenceSig and the fixed-width word operations. *)

From Stdlib Require Import ZArith List Bool.
From Galois.Bits Require Import Word Op.
From Galois.Domains Require Import CongruenceSig WordSig.
Import List.ListNotations.
Local Open Scope Z_scope.

Module CongruenceCode (L : WORD_LANGUAGE_OPS) <: CONGRUENCE_OPS L.
  Definition p := congr.
  Definition wordb w z := (0 <=? z) && (z <? modulus w).
  Definition congr_norm w c :=
    match c with
    | CBot => CBot
    | C m r =>
      let m' := Z.abs m in
      if m' =? 0 then if wordb w r then C 0 r else CBot else
        let r' := r mod m' in
        if modulus w <=? m' then if wordb w r' then C 0 r' else CBot
        else C m' r'
    end.
  Definition raw_leb a b :=
    match a, b with
    | CBot, _ => true
    | _, CBot => false
    | C m r, C n s => (m mod n =? 0) && ((r - s) mod n =? 0)
    end.
  Definition pleb w a b := raw_leb (congr_norm w a) (congr_norm w b).
  Definition pjoin w a b :=
    match congr_norm w a, congr_norm w b with
    | CBot, c => c
    | c, CBot => c
    | C m r, C n s => congr_norm w (C (Z.gcd (Z.gcd m n) (r - s)) r)
    end.
  Definition pmeet w a b :=
    match congr_norm w a, congr_norm w b with
    | CBot, _ | _, CBot => CBot
    | C m r, C n s =>
      if r mod Z.gcd m n =? s mod Z.gcd m n then
        congr_norm w (C (Z.lcm m n) (Z.combinecong m n r s))
      else CBot
    end.
  Definition pbot (_ : positive) := CBot.
  Definition ptop (_ : positive) := C 1 0.
  Definition pis_bot w a := match congr_norm w a with CBot => true | _ => false end.
  Definition pconst w z := C 0 (L.wrap w z).
  Definition ppoint w a :=
    match congr_norm w a with C 0 r => Some r | _ => None end.
  Definition pwparam := unit.
  Definition pwiden (_ : pwparam) w a b :=
    if pleb w b a then a else pjoin w a b.
  Definition pnarrow w a b := pmeet w a b.
  Definition wrap_class w m r := congr_norm w (C (Z.gcd m (modulus w)) r).
  Definition congr_neg w a :=
    match congr_norm w a with CBot => CBot | C m r => wrap_class w m (-r) end.
  Definition congr_add w a b :=
    match congr_norm w a, congr_norm w b with
    | C m r, C n s => wrap_class w (Z.gcd m n) (r + s)
    | _, _ => CBot
    end.
  Definition congr_sub w a b :=
    match congr_norm w a, congr_norm w b with
    | C m r, C n s => wrap_class w (Z.gcd m n) (r - s)
    | _, _ => CBot
    end.
  Definition congr_mul w a b :=
    match congr_norm w a, congr_norm w b with
    | C m r, C n s => wrap_class w (Z.gcd (m * n) (Z.gcd (m * s) (n * r))) (r * s)
    | _, _ => CBot
    end.
  Definition congr_project source target a :=
    match congr_norm source a with CBot => CBot | C m r => wrap_class target m r end.
  Definition congr_shl w a b :=
    match congr_norm w a, congr_norm w b with
    | CBot, _ | _, CBot => CBot
    | C m r, C 0 k =>
      if Zpos w <=? k then C 0 0 else wrap_class w (m * 2 ^ k) (r * 2 ^ k)
    | _, _ => C 1 0
    end.
  Definition congr_urem w a b :=
    match congr_norm w a, congr_norm w b with
    | CBot, _ | _, CBot => CBot
    | C m r, C 0 c => congr_norm w (C (Z.gcd m c) r)
    | _, _ => C 1 0
    end.
End CongruenceCode.

Module CongruenceTableCode (L : WORD_LANGUAGE_OPS) (D : CONGRUENCE_OPS L)
    <: WORD_TABLE_OPS L D.
  Definition wfwd o rw (xs : list (positive * D.p)) : option D.p :=
    match o, xs with
    | bvneg, [(w, a)] =>
      Some (if Pos.eqb w rw then D.congr_neg rw a else D.ptop rw)
    | bvzext _, [(w, a)] =>
      Some (if Pos.leb w rw then D.congr_norm rw a else D.ptop rw)
    | bvtrunc _, [(w, a)] => Some (D.congr_project w rw a)
    | (bvadd | bvsub | bvmul | bvshl | bvurem), [(wa, a); (wb, b)] =>
      Some (if Pos.eqb wa rw && Pos.eqb wb rw then
        match o with
        | bvadd => D.congr_add rw a b
        | bvsub => D.congr_sub rw a b
        | bvmul => D.congr_mul rw a b
        | bvshl => D.congr_shl rw a b
        | _ => D.congr_urem rw a b
        end else D.ptop rw)
    | bvite, [_; (wa, a); (wb, b)] =>
      Some (if Pos.eqb wa rw && Pos.eqb wb rw then D.pjoin rw a b else D.ptop rw)
    | _, _ => None
    end.
  Definition wbwd (_ : L.op) (_ : positive) (_ : D.p)
      (_ : list (positive * D.p)) : option (list D.p) := None.
End CongruenceTableCode.
