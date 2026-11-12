(** * Known-bit backward operations

    Backward transfers refine operand masks from a known result mask.
    For example, a known sum can refine the first operand when the second is fixed.
    Builds on: KnownBitsSig and the bit-vector operations. *)

From Stdlib Require Import ZArith List Bool.
From Galois.Bits Require Import Word Op Fun.
From Galois.Domains Require Import WordSig KnownBitsSig KnownBits KnownBitsOps.
Import List.ListNotations.
Local Open Scope Z_scope.

Definition tnum_project (sw rw : width) (g : Z -> Z) (q : tnum) : tnum :=
  Tnum (wrap sw (g (wrap rw (zeros q)))) (wrap sw (g (wrap rw (ones q)))).

Definition tnum_inverse_shift (o : op) : op :=
  match o with
  | bvshl => bvlshr
  | bvlshr | bvashr => bvshl
  | bvrotl => bvrotr
  | bvrotr => bvrotl
  | _ => o
  end.

Definition tnum_and_back (w : width) (q b : tnum) : tnum :=
  Tnum (wand w (zeros q) (ones b)) (wrap w (ones q)).

Definition tnum_or_back (w : width) (q b : tnum) : tnum :=
  Tnum (wrap w (zeros q)) (wand w (ones q) (zeros b)).

Definition tnum_sign_project (sw rw : width) (n : Z) (q : tnum) : tnum :=
  Tnum (if Z.shiftr (wrap rw (zeros q)) n =? 0 then 0 else half sw)
    (if Z.shiftr (wrap rw (ones q)) n =? 0 then 0 else half sw).

Definition tnum_back_shift (o : op) (w : width) (k : Z) (q : tnum) : tnum :=
  let copied := tnum_project w w (tnum_scalar_value (tnum_inverse_shift o) w k) q in
  match o with
  | bvashr => tnum_meet w copied (tnum_sign_project w w (Z.max 0 (Zpos w - 1 - k)) q)
  | _ => copied
  end.

Definition tnum_back_sext (sw rw : width) (q : tnum) : tnum :=
  tnum_meet sw (tnum_project sw rw (fun m => m) q)
    (tnum_sign_project sw rw (Zpos sw - 1) q).

Definition tnum_lower (w : width) (l : Z) : tnum :=
  tnum_not w (tnum_upper w (wnot w l)).

Definition tnum_order_back (strict : bool) (w : width) (q a b : tnum) : tnum * tnum :=
  let d := if strict then 1 else 0 in
  if Z.testbit (ones q) 0 then
    (tnum_upper w (tnum_max w b - d), tnum_lower w (tnum_min w a + d))
  else if Z.testbit (zeros q) 0 then
    (tnum_lower w (tnum_min w b + (1 - d)), tnum_upper w (tnum_max w a - (1 - d)))
  else (tnum_top, tnum_top).

Definition tnum_project_variable (o : op) (w : width) (b q : tnum) : tnum :=
  let inv := tnum_inverse_shift o in
  let zero := tnum_variable_raw inv w (Tnum 0 (zeros q)) b in
  let one := tnum_variable_raw inv w (Tnum 0 (ones q)) b in
  Tnum (ones zero) (ones one).

Definition tnum_back_variable_shift (o : op) (w : width) (b q : tnum) : tnum :=
  let copied := tnum_project_variable o w b q in
  match o with
  | bvashr => tnum_meet w copied
      (tnum_sign_project w w (Z.max 0 (Zpos w - 1 - tnum_min w b)) q)
  | _ => copied
  end.

Definition tnum_backward_raw (o : op) (wps : list (width * tnum))
    (rw : width) (q : tnum) : list tnum :=
  match o, wps with
  | bvnot, [(w, _)] => [tnum_not w q]
  | (bvzext _ | bvtrunc _), [(w, _)] => [tnum_project w rw (fun m => m) q]
  | bvsext _, [(w, _)] => [tnum_back_sext w rw q]
  | bvextract _ lo, [(w, _)] => [tnum_project w rw (fun m => Z.shiftl m (Z.of_nat lo)) q]
  | bvand, [(w, a); (v, b)] => [tnum_and_back w q b; tnum_and_back v q a]
  | bvor, [(w, a); (v, b)] => [tnum_or_back w q b; tnum_or_back v q a]
  | bvxor, [(w, a); (v, b)] => [tnum_xor w q b; tnum_xor v q a]
  | bvadd, [(w, a); (v, b)] => [tnum_sub w q b; tnum_sub v q a]
  | bvsub, [(w, a); (v, b)] => [tnum_add w q b; tnum_sub v a q]
  | (bvshl | bvlshr | bvashr | bvrotl | bvrotr), [(w, _); (v, b)] =>
    match tnum_constant v b with
    | Some k => [tnum_back_shift o w k q; b]
    | None => [tnum_back_variable_shift o w b q; b]
    end
  | bveq, [(_, a); (_, b)] => if Z.testbit (ones q) 0 then [b; a] else [a; b]
  | bvult, [(w, a); (_, b)] =>
    let p := tnum_order_back true w q a b in [fst p; snd p]
  | bvule, [(w, a); (_, b)] =>
    let p := tnum_order_back false w q a b in [fst p; snd p]
  | bvconcat, [(w, _); (v, _)] =>
    [tnum_project w rw (fun m => Z.shiftr m (Zpos v)) q;
      tnum_project v rw (fun m => m) q]
  | _, _ => map snd wps
  end.

Fixpoint tnum_refine (wps : list (width * tnum)) (qs : list tnum) : list tnum :=
  match wps, qs with
  | [], _ => []
  | (w, a) :: rest, q :: tail => tnum_meet w a q :: tnum_refine rest tail
  | (_, a) :: rest, [] => a :: tnum_refine rest []
  end.

Module KnownBitsTableCode (L : WORD_LANGUAGE_OPS) (C : TNUM_CONFIG)
    (K : KNOWN_BITS_OPS L C) <: WORD_TABLE_OPS L K.
  Module Ops := KnownBitsOpsCode L C K.
  Definition wfwd (o : L.op) (rw : positive) (xs : list (positive * K.p)) : option K.p :=
    if Nat.eqb (length xs) (arity o) then Some (Ops.tnum_forward_raw o xs rw) else None.
  Definition wbwd (o : L.op) (rw : positive) (q : K.p)
      (xs : list (positive * K.p)) : option (list K.p) :=
    if Nat.eqb (length xs) (arity o) then Some (tnum_refine xs (tnum_backward_raw o xs rw q))
    else None.
End KnownBitsTableCode.

Module KnownBitsTable (L : WORD_LANGUAGE) (C : TNUM_CONFIG) (K : KNOWN_BITS L C)
    <: KNOWN_BITS_TABLE L C K.
  Include KnownBitsTableCode L C K.
  Lemma wfwd_sound : forall o rw wps cs z r, wfwd o rw wps = Some r ->
    Forall2 (fun wp c => fst wp = fst c /\ L.is_word (fst c) (snd c) /\
      K.pgamma (fst wp) (snd wp) (snd c)) wps cs ->
    L.eval_op o cs = Some (rw, z) -> K.pgamma rw r z.
  Proof. Admitted. (* SIG-QUESTION: K arithmetic has no soundness or implementation pin. *)
  Lemma wbwd_sound : forall o rw q wps ys cs z, wbwd o rw q wps = Some ys ->
    Forall2 (fun wp c => fst wp = fst c /\ L.is_word (fst c) (snd c) /\
      K.pgamma (fst wp) (snd wp) (snd c)) wps cs ->
    L.eval_op o cs = Some (rw, z) -> K.pgamma rw q z ->
    Forall2 (fun wp c => K.pgamma (fst wp) (snd wp) (snd c))
      (combine (map fst wps) ys) cs.
  Proof. Admitted. (* STUB *)
End KnownBitsTable.
Theorem tnum_refine_equation : forall wps qs,
  tnum_refine wps qs =
  match wps, qs with
  | [], _ => []
  | (w, a) :: rest, q :: tail => tnum_meet w a q :: tnum_refine rest tail
  | (_, a) :: rest, [] => a :: tnum_refine rest []
  end.
Proof. Admitted. (* CONVERT: tnum_refine_equation: The reference tnum_refine_c was not found in the current environment. *)
Theorem tnum_refine_length : forall wps qs, length (tnum_refine wps qs) = length wps.
Proof.
  intro wps. induction wps as [|[w a] rest IH]; intros [|q tail];
    rewrite tnum_refine_equation; cbn [length]; [reflexivity|reflexivity| |];
    f_equal; apply IH.
Qed.

Theorem tnum_refine_refines : forall wps qs,
  Forall2 (fun wp q => tnum_leb (fst wp) q (snd wp) = true)
    wps (tnum_refine wps qs).
Proof. Admitted. (* CONVERT: tnum_refine_refines: Unable to unify the Forall2 constructor with the empty case. *)

Definition kb_payload_sound (wp : width * tnum) (y : word) : Prop :=
  fst wp = fst y /\ is_word (fst y) (snd y) /\ tnum_gamma (fst wp) (snd wp) (snd y).

Theorem tnum_backward_raw_sound : forall o wps ys rw z q,
  Forall2 kb_payload_sound wps ys -> eval_op o ys = Some (rw, z) ->
  tnum_gamma rw q z ->
  Forall2 (fun wp_y p => tnum_gamma (fst (fst wp_y)) p (snd (snd wp_y)))
    (combine wps ys) (tnum_backward_raw o wps rw q).
Proof. Admitted. (* CONVERT: tnum_backward_raw_sound: The variable tnum_backward_one_sound was not found in the current environment. *)
Theorem tnum_refine_sound : forall wps ys qs,
  Forall2 kb_payload_sound wps ys ->
  Forall2 (fun wp_y q => tnum_gamma (fst (fst wp_y)) q (snd (snd wp_y)))
    (combine wps ys) qs ->
  Forall2 (fun p y => tnum_gamma (fst p) (snd p) (snd y))
    (combine (map fst wps) (tnum_refine wps qs)) ys.
Proof.
  intros wps ys qs Hgamma. revert qs.
  induction Hgamma as [|[w a] [v x] rest tail Hhead Htail IH]; intros qs Hqs.
  - destruct qs; constructor.
  - inversion Hqs as [|wp_y q rest' qs' Hq Hrest]; subst qs.
    destruct Hhead as [Hwv [Hx Ha]]. cbn in Hwv, Hx, Ha, Hq. subst v.
    rewrite tnum_refine_equation. cbn [combine map fst snd]. constructor.
    + now apply tnum_meet_sound.
    + now apply IH.
Qed.
