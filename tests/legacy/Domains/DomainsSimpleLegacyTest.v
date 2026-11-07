(** * Differential matrices for simple word domains

    Matrices compare forward and backward payload transfers against the legacy domains.
    For example, exact congruence operands now use concrete evaluation for bitwise operations.
    Builds on: DomainsConst, DomainsSign, DomainsCongruence and their legacy counterparts. *)

From Stdlib Require Import ZArith List Bool.
From Galois.Cost Require Import CostMonad.
From Galois.Lattice Require Import LatticeCore LatticeFlat.
From Galois.Bits Require Import BitsWord BitsOp.
From Galois.Domains Require Import
  DomainsNumeric DomainsTransfer DomainsConst DomainsSign DomainsCongruence.
From GaloisLegacy.Order Require OrderFlat.
From GaloisLegacy.Bits Require BitsOp.
From GaloisLegacy.Domains Require DomainsNumeric DomainsConst DomainsSign DomainsCongruence.
Import List.ListNotations.
Local Open Scope Z_scope.

Module OldNumeric := GaloisLegacy.Domains.DomainsNumeric.
Module OldConst := GaloisLegacy.Domains.DomainsConst.
Module OldSign := GaloisLegacy.Domains.DomainsSign.
Module OldCong := GaloisLegacy.Domains.DomainsCongruence.
Module OldFlat := GaloisLegacy.Order.OrderFlat.
Module OldOp := GaloisLegacy.Bits.BitsOp.

Definition legacy_op o :=
  match o with
  | bvnot => OldOp.bvnot
  | bvneg => OldOp.bvneg
  | bvclz => OldOp.bvclz
  | bvctz => OldOp.bvctz
  | bvpopcnt => OldOp.bvpopcnt
  | bvadd => OldOp.bvadd
  | bvsub => OldOp.bvsub
  | bvmul => OldOp.bvmul
  | bvudiv => OldOp.bvudiv
  | bvurem => OldOp.bvurem
  | bvsdiv => OldOp.bvsdiv
  | bvsrem => OldOp.bvsrem
  | bvsmod => OldOp.bvsmod
  | bvand => OldOp.bvand
  | bvor => OldOp.bvor
  | bvxor => OldOp.bvxor
  | bvshl => OldOp.bvshl
  | bvlshr => OldOp.bvlshr
  | bvashr => OldOp.bvashr
  | bvrotl => OldOp.bvrotl
  | bvrotr => OldOp.bvrotr
  | bveq => OldOp.bveq
  | bvne => OldOp.bvne
  | bvult => OldOp.bvult
  | bvule => OldOp.bvule
  | bvslt => OldOp.bvslt
  | bvsle => OldOp.bvsle
  | bvite => OldOp.bvite
  | bvzext n => OldOp.bvzext n
  | bvsext n => OldOp.bvsext n
  | bvtrunc t => OldOp.bvtrunc t
  | bvextract hi lo => OldOp.bvextract hi lo
  | bvconcat => OldOp.bvconcat
  end.

Definition matrix_ops w :=
  [bvnot; bvneg; bvclz; bvctz; bvpopcnt; bvadd; bvsub; bvmul; bvudiv; bvurem;
   bvsdiv; bvsrem; bvsmod; bvand; bvor; bvxor; bvshl; bvlshr; bvashr; bvrotl; bvrotr;
   bveq; bvne; bvult; bvule; bvslt; bvsle; bvite; bvzext 1%positive;
   bvsext 1%positive; bvtrunc 1%positive; bvtrunc w; bvextract 0 0; bvconcat].

Fixpoint vectors {A} (n : nat) (xs : list A) : list (list A) :=
  match n with
  | O => [[]]
  | S n => flat_map (fun x => map (cons x) (vectors n xs)) xs
  end.

Definition matrix_inputs {A} o (w : width) (xs : list A) :=
  map (fun args =>
    match o, args with
    | bvite, [a; b; c] => [(1%positive, a); (w, b); (w, c)]
    | _, _ => map (fun x => (w, x)) args
    end) (vectors (arity o) xs).

Definition matrix_width {A} o w (xs : list (width * A)) :=
  match result_width o (map fst xs) with Some rw => rw | None => w end.

Definition old_const (p : flat Z) :=
  match p with
  | FBot => OldFlat.FBot
  | FVal z => OldFlat.FVal z
  | FTop => OldFlat.FTop
  end.
Definition new_const (p : OldFlat.flat Z) :=
  match p with
  | OldFlat.FBot => FBot
  | OldFlat.FVal z => FVal z
  | OldFlat.FTop => FTop
  end.
Definition const_equal (a b : flat Z) :=
  match a, b with
  | FBot, FBot | FTop, FTop => true
  | FVal x, FVal y => Z.eqb x y
  | _, _ => false
  end.
Definition old_sign s := OldSign.Sign (neg s) (zero s) (pos s).
Definition new_sign s := Sign (OldSign.neg s) (OldSign.zero s) (OldSign.pos s).
Definition sign_equal a b :=
  Bool.eqb (neg a) (neg b) && Bool.eqb (zero a) (zero b) && Bool.eqb (pos a) (pos b).
Definition old_cong c := match c with CBot => OldCong.CBot | Cong m r => OldCong.Cong m r end.
Definition new_cong c := match c with OldCong.CBot => CBot | OldCong.Cong m r => Cong m r end.
Definition cong_equal a b :=
  match a, b with
  | CBot, CBot => true
  | Cong m r, Cong n s => Z.eqb m n && Z.eqb r s
  | _, _ => false
  end.

Fixpoint lists_equal {A} (eqb : A -> A -> bool) xs ys :=
  match xs, ys with
  | [], [] => true
  | x :: xs, y :: ys => eqb x y && lists_equal eqb xs ys
  | _, _ => false
  end.

(** Differences require strict refinement and detected emptiness or exact point evaluation. *)
Definition forward_compatible {A}
    (D : word_domain A) (S : Transfer.shape (width * A) A op width word)
    (eqb : A -> A -> bool) o xs rw old :=
  let fresh := pforward D o xs rw in
  if eqb fresh old then true else
  leb (plat D rw) fresh old && negb (leb (plat D rw) old fresh) &&
    (if existsb (fun wp => Cost.value (Transfer.is_empty_c S wp)) xs
     then eqb fresh (Transfer.bot_out S rw)
     else
       match Cost.value (Transfer.points_c S xs) with
       | Some cs =>
         match eval_op o cs with
         | Some c => eqb fresh (Cost.value (Transfer.inj_c S rw c))
         | None => eqb fresh (Transfer.bot_out S rw)
         end
       | None => false
       end).

Definition constant_grid w : list (flat Z) :=
  [FBot; FTop; FVal 0; FVal 1; FVal (modulus w - 1); FVal (half w)].
Definition sign_grid :=
  [Sign false false false; Sign false true false; Sign false false true;
   Sign true false false; Sign false true true; Sign true true false;
   Sign true false true; Sign true true true].
Definition congruence_grid w :=
  [CBot; Cong 1 0; Cong 0 0; Cong 0 (modulus w - 1); Cong 2 0;
   Cong 4 1; Cong (-4) 6; Cong 512 300].

Definition constant_matrix w :=
  forallb (fun o => forallb (fun xs =>
    let rw := matrix_width o w xs in
    const_equal (pforward const_word_domain o xs rw)
      (new_const (OldNumeric.pforward OldConst.const_domain (legacy_op o)
        (map (fun wp => (fst wp, old_const (snd wp))) xs) rw)) &&
    forallb (fun q => lists_equal const_equal
      (passume const_word_domain o xs rw q)
      (map new_const (OldNumeric.passume OldConst.const_domain (legacy_op o)
        (map (fun wp => (fst wp, old_const (snd wp))) xs) rw (old_const q))))
      (constant_grid w)) (matrix_inputs o w (constant_grid w))) (matrix_ops w).

Definition sign_matrix w :=
  forallb (fun o => forallb (fun xs =>
    let rw := matrix_width o w xs in
    forward_compatible sign_word_domain sign_shape sign_equal o xs rw
      (new_sign (OldNumeric.pforward OldSign.sign_domain (legacy_op o)
        (map (fun wp => (fst wp, old_sign (snd wp))) xs) rw)) &&
    forallb (fun q => lists_equal sign_equal
      (passume sign_word_domain o xs rw q)
      (map new_sign (OldNumeric.passume OldSign.sign_domain (legacy_op o)
        (map (fun wp => (fst wp, old_sign (snd wp))) xs) rw (old_sign q))))
      sign_grid) (matrix_inputs o w sign_grid)) (matrix_ops w).

Definition congruence_matrix w :=
  forallb (fun o => forallb (fun xs =>
    let rw := matrix_width o w xs in
    forward_compatible cong_word_domain cong_shape cong_equal o xs rw
      (new_cong (OldNumeric.pforward OldCong.cong_domain (legacy_op o)
        (map (fun wp => (fst wp, old_cong (snd wp))) xs) rw)) &&
    forallb (fun q => lists_equal cong_equal
      (passume cong_word_domain o xs rw q)
      (map new_cong (OldNumeric.passume OldCong.cong_domain (legacy_op o)
        (map (fun wp => (fst wp, old_cong (snd wp))) xs) rw (old_cong q))))
      (congruence_grid w)) (matrix_inputs o w (congruence_grid w))) (matrix_ops w).

Example constant_width1_matrix : constant_matrix 1%positive = true.
Proof.
  vm_compute. reflexivity.
Qed.
Example constant_width4_matrix : constant_matrix 4%positive = true.
Proof.
  vm_compute. reflexivity.
Qed.
Example constant_width8_matrix : constant_matrix 8%positive = true.
Proof.
  vm_compute. reflexivity.
Qed.
Example sign_width1_matrix : sign_matrix 1%positive = true.
Proof.
  vm_compute. reflexivity.
Qed.
Example sign_width4_matrix : sign_matrix 4%positive = true.
Proof.
  vm_compute. reflexivity.
Qed.
Example sign_width8_matrix : sign_matrix 8%positive = true.
Proof.
  vm_compute. reflexivity.
Qed.
Example congruence_width1_matrix : congruence_matrix 1%positive = true.
Proof.
  vm_compute. reflexivity.
Qed.
Example congruence_width4_matrix : congruence_matrix 4%positive = true.
Proof.
  vm_compute. reflexivity.
Qed.
Example congruence_width8_matrix : congruence_matrix 8%positive = true.
Proof.
  vm_compute. reflexivity.
Qed.

(** The zero-only sign point path is more precise than the legacy default for addition. *)
Example sign_zero_point_precision :
  eval_op bvadd [(8%positive, 0); (8%positive, 0)] = Some (8%positive, 0) /\
  pforward sign_word_domain bvadd
    [(8%positive, Sign false true false); (8%positive, Sign false true false)] 8%positive =
    Sign false true false /\
  forward_compatible sign_word_domain sign_shape sign_equal bvadd
    [(8%positive, Sign false true false); (8%positive, Sign false true false)] 8%positive
    sign_top = true.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

(** Congruence exact points evaluate bitwise operations that the legacy domain leaves at top. *)
Example congruence_exact_point_precision :
  eval_op bvand [(4%positive, 3); (4%positive, 5)] = Some (4%positive, 1) /\
  pforward cong_word_domain bvand [(4%positive, Cong 0 3); (4%positive, Cong 0 5)]
    4%positive = Cong 0 1 /\
  forward_compatible cong_word_domain cong_shape cong_equal bvand
    [(4%positive, Cong 0 3); (4%positive, Cong 0 5)] 4%positive (Cong 1 0) = true.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

(** Empty selection conditions now force bottom even when both branches are inhabited. *)
Example empty_condition_precision :
  pforward sign_word_domain bvite
    [(1%positive, Sign false false false); (8%positive, sign_top); (8%positive, sign_top)]
    8%positive = Sign false false false /\
  pforward cong_word_domain bvite
    [(1%positive, CBot); (8%positive, Cong 1 0); (8%positive, Cong 1 0)]
    8%positive = CBot.
Proof.
  vm_compute. split; reflexivity.
Qed.

Definition old_sign_forward o xs rw :=
  new_sign (OldNumeric.pforward OldSign.sign_domain (legacy_op o)
    (map (fun wp => (fst wp, old_sign (snd wp))) xs) rw).
Definition old_cong_forward o xs rw :=
  new_cong (OldNumeric.pforward OldCong.cong_domain (legacy_op o)
    (map (fun wp => (fst wp, old_cong (snd wp))) xs) rw).

Definition difference_tags {A} (D : word_domain A)
    (S : Transfer.shape (width * A) A op width word)
    (eqb : A -> A -> bool) (grid : width -> list A)
    (old : op -> list (width * A) -> width -> A) (empty : bool) :=
  nodup Nat.eq_dec (flat_map (fun w =>
    map (fun o => fst (op_code o)) (filter (fun o =>
      existsb (fun xs =>
        let rw := matrix_width o w xs in
        negb (eqb (pforward D o xs rw) (old o xs rw)) &&
        Bool.eqb empty (existsb
          (fun wp => Cost.value (Transfer.is_empty_c S wp)) xs))
        (matrix_inputs o w (grid w))) (matrix_ops w)))
    [1%positive; 4%positive; 8%positive]).

(** The sign empty-operand exception has this complete operator-code inventory on the matrices. *)
Example sign_empty_difference_inventory :
  difference_tags sign_word_domain sign_shape sign_equal (fun _ => sign_grid)
    old_sign_forward true =
    [2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 16; 17; 18; 19; 20;
     21; 22; 23; 24; 25; 26; 27; 28; 30; 31; 32]%nat.
Proof.
  vm_compute. reflexivity.
Qed.

(** The sign zero-point exception has this complete operator-code inventory on the matrices. *)
Example sign_zero_difference_inventory :
  difference_tags sign_word_domain sign_shape sign_equal (fun _ => sign_grid)
    old_sign_forward false =
    [2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20;
     28; 30; 31; 32]%nat.
Proof.
  vm_compute. reflexivity.
Qed.

(** The congruence empty-operand exception has this complete operator-code inventory. *)
Example congruence_empty_difference_inventory :
  difference_tags cong_word_domain cong_shape cong_equal congruence_grid
    old_cong_forward true =
    [0; 2; 3; 4; 8; 10; 11; 12; 13; 14; 15; 17; 18; 19; 20; 21; 22; 23; 24;
     25; 26; 27; 28; 29; 31; 32]%nat.
Proof.
  vm_compute. reflexivity.
Qed.

(** The congruence exact-point exception has this complete operator-code inventory. *)
Example congruence_point_difference_inventory :
  difference_tags cong_word_domain cong_shape cong_equal congruence_grid
    old_cong_forward false =
    [28; 0; 2; 3; 4; 8; 9; 10; 11; 12; 13; 14; 15; 17; 18; 19; 20; 21; 22; 23; 24;
     25; 26; 27; 29; 31; 32]%nat.
Proof.
  vm_compute. reflexivity.
Qed.
