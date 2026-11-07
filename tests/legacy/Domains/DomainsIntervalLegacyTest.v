(** * Interval and circular differential fixtures

    Finite matrices compare both transfer directions at widths one, four and eight.
    Explicit fixtures record the mandatory singleton population-count and conditional improvements.
    For example, a one-bit singleton zero population count now returns the singleton zero.
    Builds on: the new and legacy interval and circular word domains. *)

From Stdlib Require Import ZArith List Bool.
From Galois.Bits Require Import BitsWord BitsOp.
From Galois.Domains Require Import DomainsBound DomainsThreshold DomainsInterval
  DomainsIntervalBack DomainsNumeric DomainsWrapped DomainsWrappedBack.
From GaloisLegacy.Bits Require BitsOp.
From GaloisLegacy.Domains Require DomainsNumeric DomainsInterval DomainsWrapped.
Import List.ListNotations.

Module OldOp := GaloisLegacy.Bits.BitsOp.
Module OldNumeric := GaloisLegacy.Domains.DomainsNumeric.
Module OldInterval := GaloisLegacy.Domains.DomainsInterval.
Module OldWrapped := GaloisLegacy.Domains.DomainsWrapped.

Local Open Scope Z_scope.

Definition old_op (o : op) : OldOp.op :=
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
  | bvzext extra => OldOp.bvzext extra
  | bvsext extra => OldOp.bvsext extra
  | bvtrunc target => OldOp.bvtrunc target
  | bvextract hi lo => OldOp.bvextract hi lo
  | bvconcat => OldOp.bvconcat
  end.

Definition old_bound b :=
  match b with
  | NegInf => OldInterval.NegInf
  | Fin z => OldInterval.Fin z
  | PosInf => OldInterval.PosInf
  end.

Definition new_bound b :=
  match b with
  | OldInterval.NegInf => NegInf
  | OldInterval.Fin z => Fin z
  | OldInterval.PosInf => PosInf
  end.

Definition old_interval a :=
  match a with
  | IBot => OldInterval.IBot
  | Itv lo hi => OldInterval.Itv (old_bound lo) (old_bound hi)
  end.

Definition new_interval a :=
  match a with
  | OldInterval.IBot => IBot
  | OldInterval.Itv lo hi => Itv (new_bound lo) (new_bound hi)
  end.

Definition old_wrapped a :=
  match a with
  | WBot => OldWrapped.WBot
  | WFull => OldWrapped.WFull
  | WItv lo hi => OldWrapped.WItv lo hi
  end.

Definition new_wrapped a :=
  match a with
  | OldWrapped.WBot => WBot
  | OldWrapped.WFull => WFull
  | OldWrapped.WItv lo hi => WItv lo hi
  end.

Definition bound_same a b :=
  match a, b with
  | NegInf, NegInf | PosInf, PosInf => true
  | Fin x, Fin y => Z.eqb x y
  | _, _ => false
  end.

Definition interval_same a b :=
  match a, b with
  | IBot, IBot => true
  | Itv l h, Itv l' h' => bound_same l l' && bound_same h h'
  | _, _ => false
  end.

Definition wrapped_same a b :=
  match a, b with
  | WBot, WBot | WFull, WFull => true
  | WItv l h, WItv l' h' => Z.eqb l l' && Z.eqb h h'
  | _, _ => false
  end.

Fixpoint list_same {A} (same : A -> A -> bool) (xs ys : list A) :=
  match xs, ys with
  | [], [] => true
  | x :: xs, y :: ys => same x y && list_same same xs ys
  | _, _ => false
  end.

Definition interval_samples w :=
  [IBot; Itv NegInf PosInf; Itv (Fin 0) (Fin 0);
   Itv (Fin 0) (Fin (Z.min 3 (modulus w - 1)));
   Itv (Fin (half w)) (Fin (modulus w - 1))].

Definition wrapped_samples w :=
  [WBot; WFull; WItv 0 0; WItv (modulus w - 1) (modulus w - 1);
   WItv (modulus w - 1) 0; WItv 0 (Z.min 3 (modulus w - 1))].

Definition binary_ops :=
  [bvadd; bvsub; bvmul; bvudiv; bvurem; bvsdiv; bvsrem; bvsmod;
   bvand; bvor; bvxor; bvshl; bvlshr; bvashr; bvrotl; bvrotr;
   bveq; bvne; bvult; bvule; bvslt; bvsle; bvconcat].

Definition unary_ops w :=
  [bvnot; bvneg; bvclz; bvctz; bvpopcnt; bvzext 1%positive; bvsext 1%positive; bvtrunc 1%positive;
   bvextract (Pos.to_nat w - 1)%nat 0%nat].

Definition interval_forward_agrees o rw xs :=
  interval_same (interval_forward ThresholdEmpty o xs rw)
    (new_interval (OldInterval.interval_forward (old_op o)
      (map (fun wp => (fst wp, old_interval (snd wp))) xs) rw)).

Definition wrapped_forward_agrees o rw xs :=
  wrapped_same (pforward wrapped_word_domain o xs rw)
    (new_wrapped (OldWrapped.wrapped_forward (old_op o)
      (map (fun wp => (fst wp, old_wrapped (snd wp))) xs) rw)).

Definition wrapped_point_exception o xs :=
  match o, xs with
  | bvsrem, [(wa, WItv la ha); (wb, WItv lb hb)] =>
    Pos.eqb wa wb && Z.eqb la (modulus wa - 1) && Z.eqb ha (modulus wa - 1) &&
    Z.eqb lb 0 && Z.eqb hb 0
  | _, _ => false
  end.

Definition wrapped_forward_point_refines o rw xs :=
  let new := pforward wrapped_word_domain o xs rw in
  let old := new_wrapped (OldWrapped.wrapped_forward (old_op o)
    (map (fun wp => (fst wp, old_wrapped (snd wp))) xs) rw) in
  if wrapped_point_exception o xs then
    match xs with
    | [(wa, WItv la _); (wb, WItv lb _)] =>
      match eval_op o [(wa, la); (wb, lb)] with
      | Some (_, z) => wrapped_same new (WItv z z) && wrapped_leb rw new old
      | None => false
      end
    | _ => false
    end
  else wrapped_same new old.

Definition interval_backward_agrees o rw q xs :=
  list_same interval_same (interval_assume ThresholdEmpty o xs rw q)
    (map new_interval (OldInterval.interval_assume (old_op o)
      (map (fun wp => (fst wp, old_interval (snd wp))) xs) rw (old_interval q))).

Definition wrapped_backward_agrees o rw q xs :=
  list_same wrapped_same (passume wrapped_word_domain o xs rw q)
    (map new_wrapped (OldWrapped.wrapped_assume (old_op o)
      (map (fun wp => (fst wp, old_wrapped (snd wp))) xs) rw (old_wrapped q))).

Definition interval_unary_point_agrees o rw w a :=
  match o, interval_singleton (interval_clip w a) with
  | bvpopcnt, Some x =>
    let new := interval_forward ThresholdEmpty o [(w, a)] rw in
    let old := new_interval (OldInterval.interval_forward (old_op o) [(w, old_interval a)] rw) in
    match eval_op o [(w, x)] with
    | Some (_, z) => interval_same new (Itv (Fin z) (Fin z)) && interval_leb new old
    | None => false
    end
  | _, _ => interval_forward_agrees o rw [(w, a)]
  end.

Definition wrapped_unary_point_agrees o rw w a :=
  match o, wrapped_point w a with
  | bvpopcnt, Some x =>
    let new := pforward wrapped_word_domain o [(w, a)] rw in
    let old := new_wrapped (OldWrapped.wrapped_forward (old_op o) [(w, old_wrapped a)] rw) in
    match eval_op o [(w, x)] with
    | Some (_, z) => wrapped_same new (WItv z z) && wrapped_leb rw new old
    | None => false
    end
  | _, _ => wrapped_forward_agrees o rw [(w, a)]
  end.

Definition interval_unary_matrix w :=
  forallb (fun o =>
    match result_width o [w] with
    | Some rw => forallb (interval_unary_point_agrees o rw w) (interval_samples w)
    | None => true
    end) (unary_ops w).

Definition wrapped_unary_matrix w :=
  forallb (fun o =>
    match result_width o [w] with
    | Some rw => forallb (wrapped_unary_point_agrees o rw w) (wrapped_samples w)
    | None => true
    end) (unary_ops w).

Definition interval_binary_row w o :=
  match result_width o [w; w] with
  | Some rw => forallb (fun a => forallb (fun b =>
      interval_forward_agrees o rw [(w, a); (w, b)]) (interval_samples w)) (interval_samples w)
  | None => true
  end.

Definition interval_binary_matrix w := forallb (interval_binary_row w) binary_ops.

Definition wrapped_binary_row w o :=
  match result_width o [w; w] with
  | Some rw => forallb (fun a => forallb (fun b =>
      wrapped_forward_agrees o rw [(w, a); (w, b)]) (wrapped_samples w)) (wrapped_samples w)
  | None => true
  end.

Definition wrapped_binary_matrix w := forallb (wrapped_binary_row w) binary_ops.

Definition wrapped_point_refinement_matrix w :=
  forallb (fun o =>
    match result_width o [w; w] with
    | Some rw => forallb (fun a => forallb (fun b =>
        wrapped_forward_point_refines o rw [(w, a); (w, b)])
        (wrapped_samples w)) (wrapped_samples w)
    | None => true
    end) binary_ops.

Definition backward_ops := [bveq; bvne; bvult; bvule; bvslt; bvsle; bvadd; bvsub].

Definition interval_unary_exceptions w :=
  flat_map (fun o =>
    match result_width o [w] with
    | Some rw => flat_map (fun a =>
        if interval_forward_agrees o rw [(w, a)] then [] else [(o, a)]) (interval_samples w)
    | None => []
    end) (unary_ops w).

Definition wrapped_unary_exceptions w :=
  flat_map (fun o =>
    match result_width o [w] with
    | Some rw => flat_map (fun a =>
        if wrapped_forward_agrees o rw [(w, a)] then [] else [(o, a)]) (wrapped_samples w)
    | None => []
    end) (unary_ops w).

Definition wrapped_binary_exceptions w :=
  flat_map (fun o =>
    match result_width o [w; w] with
    | Some rw => flat_map (fun a => flat_map (fun b =>
        if wrapped_forward_agrees o rw [(w, a); (w, b)] then [] else [(o, a, b)])
        (wrapped_samples w)) (wrapped_samples w)
    | None => []
    end) binary_ops.

Definition wrapped_ite_nonpoint_compatible w a b :=
  let xs := [(1%positive, WFull); (w, a); (w, b)] in
  let new := pforward wrapped_word_domain bvite xs w in
  let old := new_wrapped (OldWrapped.wrapped_forward OldOp.bvite
    [(1%positive, OldWrapped.WFull); (w, old_wrapped a); (w, old_wrapped b)] w) in
  match a, b with
  | WBot, _ | _, WBot => wrapped_same new WBot && wrapped_leb w new old
  | _, _ => wrapped_same new old
  end.

Definition interval_backward_matrix w :=
  forallb (fun o =>
    match result_width o [w; w] with
    | Some rw =>
      forallb (fun q => forallb (fun a => forallb (fun b =>
        interval_backward_agrees o rw q [(w, a); (w, b)])
        (interval_samples w)) (interval_samples w))
        [Itv (Fin 0) (Fin 0); Itv (Fin 1) (Fin 1)]
    | None => true
    end) backward_ops.

Definition wrapped_backward_matrix w :=
  forallb (fun o =>
    match result_width o [w; w] with
    | Some rw =>
      forallb (fun q => forallb (fun a => forallb (fun b =>
        wrapped_backward_agrees o rw q [(w, a); (w, b)])
        (wrapped_samples w)) (wrapped_samples w))
        [WItv 0 0; WItv 1 1]
    | None => true
    end) backward_ops.

Example interval_binary_rows :
  filter (fun o => negb (interval_binary_row 1%positive o)) binary_ops = [].
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_unary_exception_inventory :
  map interval_unary_exceptions [1%positive; 4%positive; 8%positive] =
  [[(bvpopcnt, Itv (Fin 0) (Fin 0)); (bvpopcnt, Itv (Fin 1) (Fin 1))];
   [(bvpopcnt, Itv (Fin 0) (Fin 0))];
   [(bvpopcnt, Itv (Fin 0) (Fin 0))]].
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_unary_exception_inventory :
  map wrapped_unary_exceptions [1%positive; 4%positive; 8%positive] =
  [[(bvpopcnt, WItv 0 0); (bvpopcnt, WItv 1 1)];
   [(bvpopcnt, WItv 0 0); (bvpopcnt, WItv 15 15)];
   [(bvpopcnt, WItv 0 0); (bvpopcnt, WItv 255 255)]].
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_differential_widths_1_4_8 :
  map (fun w => (interval_unary_matrix w, interval_binary_matrix w, interval_backward_matrix w))
    [1%positive; 4%positive; 8%positive] = repeat (true, true, true) 3.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_binary_rows :
  map (fun w => filter (fun o => negb (wrapped_binary_row w o)) binary_ops)
    [1%positive; 4%positive; 8%positive] = repeat [bvsrem] 3.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_binary_exception_inventory :
  map wrapped_binary_exceptions [1%positive; 4%positive; 8%positive] =
  [[(bvsrem, WItv 1 1, WItv 0 0)];
   [(bvsrem, WItv 15 15, WItv 0 0)];
   [(bvsrem, WItv 255 255, WItv 0 0)]].
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_differential_widths_1_4_8 :
  map (fun w =>
    (wrapped_unary_matrix w, wrapped_point_refinement_matrix w, wrapped_backward_matrix w))
    [1%positive; 4%positive; 8%positive] = repeat (true, true, true) 3.
Proof.
  vm_compute. reflexivity.
Qed.

Example ite_nonpoint_differential_widths_1_4_8 :
  forallb (fun w =>
    forallb (fun a => forallb (fun b =>
      interval_forward_agrees bvite w
        [(1%positive, Itv (Fin 0) (Fin 1)); (w, a); (w, b)])
      (interval_samples w)) (interval_samples w) &&
    forallb (fun a => forallb (fun b =>
      wrapped_ite_nonpoint_compatible w a b)
      (wrapped_samples w)) (wrapped_samples w))
    [1%positive; 4%positive; 8%positive] = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_mandated_popcnt_precision :
  (interval_forward ThresholdEmpty bvpopcnt [(1%positive, Itv (Fin 0) (Fin 0))] 1%positive,
    new_interval (OldInterval.interval_forward OldOp.bvpopcnt
      [(1%positive, OldInterval.Itv (OldInterval.Fin 0) (OldInterval.Fin 0))] 1%positive)) =
  (Itv (Fin 0) (Fin 0), Itv (Fin 0) (Fin 1)).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_popcnt_point_exact_and_refines :
  (eval_op bvpopcnt [(1%positive, 0)],
    interval_leb
      (interval_forward ThresholdEmpty bvpopcnt [(1%positive, Itv (Fin 0) (Fin 0))] 1%positive)
      (new_interval (OldInterval.interval_forward OldOp.bvpopcnt
        [(1%positive, OldInterval.Itv (OldInterval.Fin 0) (OldInterval.Fin 0))] 1%positive))) =
  (Some (1%positive, 0), true).
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_mandated_signed_remainder_point_precision :
  map (fun w =>
    (pforward wrapped_word_domain bvsrem
      [(w, WItv (modulus w - 1) (modulus w - 1)); (w, WItv 0 0)] w,
     new_wrapped (OldWrapped.wrapped_forward OldOp.bvsrem
      [(w, OldWrapped.WItv (modulus w - 1) (modulus w - 1));
       (w, OldWrapped.WItv 0 0)] w)))
    [1%positive; 4%positive; 8%positive] =
  [(WItv 1 1, WFull); (WItv 15 15, WItv 15 0); (WItv 255 255, WItv 255 0)].
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_ite_point_precision :
  (pforward wrapped_word_domain bvite
    [(1%positive, WItv 1 1); (4%positive, WItv 2 2); (4%positive, WItv 5 5)] 4%positive,
    new_wrapped (OldWrapped.wrapped_forward OldOp.bvite
      [(1%positive, OldWrapped.WItv 1 1); (4%positive, OldWrapped.WItv 2 2);
       (4%positive, OldWrapped.WItv 5 5)] 4%positive)) = (WItv 2 2, WItv 2 5).
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_ite_point_exact_and_refines :
  (eval_op bvite [(1%positive, 1); (4%positive, 2); (4%positive, 5)],
    wrapped_leb 4%positive
      (pforward wrapped_word_domain bvite
        [(1%positive, WItv 1 1); (4%positive, WItv 2 2); (4%positive, WItv 5 5)] 4%positive)
      (new_wrapped (OldWrapped.wrapped_forward OldOp.bvite
        [(1%positive, OldWrapped.WItv 1 1); (4%positive, OldWrapped.WItv 2 2);
         (4%positive, OldWrapped.WItv 5 5)] 4%positive))) = (Some (4%positive, 2), true).
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_ite_point_precision_widths_1_4_8 :
  map (fun w =>
    let xs := [(1%positive, WItv 1 1); (w, WItv 1 1); (w, WItv 0 0)] in
    let new := pforward wrapped_word_domain bvite xs w in
    let old := new_wrapped (OldWrapped.wrapped_forward OldOp.bvite
      [(1%positive, OldWrapped.WItv 1 1); (w, OldWrapped.WItv 1 1);
       (w, OldWrapped.WItv 0 0)] w) in
    (new, old, eval_op bvite [(1%positive, 1); (w, 1); (w, 0)], wrapped_leb w new old))
    [1%positive; 4%positive; 8%positive] =
  [(WItv 1 1, WFull, Some (1%positive, 1), true);
   (WItv 1 1, WItv 0 1, Some (4%positive, 1), true);
   (WItv 1 1, WItv 0 1, Some (8%positive, 1), true)].
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_ite_empty_condition_precision :
  (pforward wrapped_word_domain bvite
    [(1%positive, WBot); (4%positive, WItv 2 2); (4%positive, WItv 5 5)] 4%positive,
    new_wrapped (OldWrapped.wrapped_forward OldOp.bvite
      [(1%positive, OldWrapped.WBot); (4%positive, OldWrapped.WItv 2 2);
       (4%positive, OldWrapped.WItv 5 5)] 4%positive)) = (WBot, WItv 2 5).
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_ite_empty_arm_precision :
  (pforward wrapped_word_domain bvite
    [(1%positive, WFull); (4%positive, WBot); (4%positive, WItv 5 5)] 4%positive,
    new_wrapped (OldWrapped.wrapped_forward OldOp.bvite
      [(1%positive, OldWrapped.WFull); (4%positive, OldWrapped.WBot);
       (4%positive, OldWrapped.WItv 5 5)] 4%positive)) = (WBot, WItv 5 5).
Proof.
  vm_compute. reflexivity.
Qed.

Example resize_backward_operand_widths :
  forallb (fun w =>
    interval_backward_agrees (bvzext 1%positive) (w + 1)%positive (Itv (Fin 0) (Fin 1))
      [(w, Itv (Fin 0) (Fin (Z.min 3 (modulus w - 1))))] &&
    interval_backward_agrees (bvtrunc 1%positive) 1%positive (Itv (Fin 0) (Fin 0))
      [(w, Itv (Fin 0) (Fin 1))] &&
    wrapped_backward_agrees (bvzext 1%positive) (w + 1)%positive (WItv 0 1)
      [(w, WItv 0 (Z.min 3 (modulus w - 1)))] &&
    wrapped_backward_agrees (bvsext 1%positive) (w + 1)%positive (WItv 0 1)
      [(w, WItv 0 (Z.min 3 (modulus w - 1)))] &&
    wrapped_backward_agrees (bvtrunc 1%positive) 1%positive (WItv 0 0)
      [(w, WItv 0 1)])
    [1%positive; 4%positive; 8%positive] = true.
Proof.
  vm_compute. reflexivity.
Qed.
