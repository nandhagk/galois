(** * Circular word interval operations

    Transfers refine and evaluate circular intervals through linear pieces.
    For example, a binary operation checks each piece at the signed pole.
    Builds on: Wrapped, IntervalBack and WordSig. *)

From Stdlib Require Import ZArith List Bool.
From Galois.Bits Require Import Word Op.
From Galois.Domains Require Import ValueSig WordSig WrappedSig Wrapped IntervalSig IntervalBack
  Thresholds.
Import List.ListNotations.
Local Open Scope Z_scope.

Module WrappedIntervalBack := IntervalBackCode ThresholdsCode WrappedScalar.

Definition wrapped_project (target source : width) (q : wrapped) : wrapped :=
  let pieces := wrapped_parts source q in
  wrapped_join target
    (wrapped_of_interval target (fst pieces)) (wrapped_of_interval target (snd pieces)).

Definition wrapped_signed_piece (division : bool) (w : width) (a b : itv) : wrapped :=
  match a, b with
  | IBot, _ | _, IBot => WBot
  | _, _ =>
    match WrappedIntervalBack.interval_sign w a, WrappedIntervalBack.interval_sign w b with
    | Some sa, Some sb =>
      let aa := if sa then WrappedIntervalBack.interval_neg w a else a in
      let bb := if sb then WrappedIntervalBack.interval_neg w b else b in
      let magnitude := wrapped_of_interval w
        (if division then WrappedIntervalBack.interval_udiv w aa bb
         else WrappedIntervalBack.interval_urem w aa bb) in
      if (if division then xorb sa sb else sa) then wrapped_neg w magnitude else magnitude
    | _, _ => WFull
    end
  end.

Definition wrapped_pair_join (wa wb : width) (a b : wrapped * wrapped) : wrapped * wrapped :=
  (wrapped_join wa (fst a) (fst b), wrapped_join wb (snd a) (snd b)).

Module WrappedOpsCode (L : WORD_LANGUAGE_OPS) (W : WRAPPED_OPS L).
  Module IP := IntervalPayloadCode L ThresholdsCode WrappedScalar.
  Module IT := IntervalWordTableCode L ThresholdsCode WrappedScalar IP.

  Definition piece_forward (o : op) (xs : list (width * itv)) (rw : width) : wrapped :=
    if existsb (fun x => match snd x with IBot => true | _ => false end) xs then WBot else
    match IT.wfwd o rw xs with
    | Some result => wrapped_of_interval rw result
    | None => WFull
    end.

  Definition forward_unary (o : op) (w : width) (a : wrapped) (rw : width) : wrapped :=
    let pieces := wrapped_parts w a in
    wrapped_join rw (piece_forward o [(w, fst pieces)] rw)
      (piece_forward o [(w, snd pieces)] rw).

  Definition piece_binary (o : op) (wa wb : width) (a b : itv) (rw : width) : wrapped :=
    match o with
    | bvsdiv => wrapped_signed_piece true rw a b
    | bvsrem => wrapped_signed_piece false rw a b
    | _ => piece_forward o [(wa, a); (wb, b)] rw
    end.

  Definition piece_cut (o : op) (wa wb : width) (a b : itv) (rw : width) : wrapped :=
    let pa := wrapped_pole_cut wa a in
    let pb := wrapped_pole_cut wb b in
    wrapped_join_four rw
      (piece_binary o wa wb (fst pa) (fst pb) rw)
      (piece_binary o wa wb (fst pa) (snd pb) rw)
      (piece_binary o wa wb (snd pa) (fst pb) rw)
      (piece_binary o wa wb (snd pa) (snd pb) rw).

  Definition forward_binary (o : op) (wa wb : width) (a b : wrapped) (rw : width) : wrapped :=
    let pa := wrapped_parts wa a in
    let pb := wrapped_parts wb b in
    wrapped_join_four rw
      (piece_cut o wa wb (fst pa) (fst pb) rw)
      (piece_cut o wa wb (fst pa) (snd pb) rw)
      (piece_cut o wa wb (snd pa) (fst pb) rw)
      (piece_cut o wa wb (snd pa) (snd pb) rw).

  Definition forward_raw (o : op) (rw : width) (xs : list (width * wrapped)) : option wrapped :=
    match xs with
    | [(w, a)] => Some (match o with
      | bvneg => W.wrapped_neg rw a
      | bvzext _ | bvtrunc _ => wrapped_project rw w a
      | _ => forward_unary o w a rw
      end)
    | [(wa, a); (wb, b)] => Some (match o with
      | bvadd => W.wrapped_add rw a b
      | bvsub => W.wrapped_sub rw a b
      | bvmul => W.wrapped_mul rw a b
      | _ => forward_binary o wa wb a b rw
      end)
    | [_; (_, a); (_, b)] => match o with bvite => Some (W.pjoin rw a b) | _ => None end
    | _ => None
    end.

  Definition assume_consistent (o : op) (wa wb : width) (a b q : itv) : bool :=
    match result_width o [wa; wb] with
    | Some rw =>
      let result := match IT.wfwd o rw [(wa, a); (wb, b)] with
        | Some r => r | None => WrappedIntervalBack.interval_top rw end in
      match WrappedScalar.interval_meet result q with IBot => false | _ => true end
    | None => false
    end.

  Definition assume_piece_raw (o : op) (wa wb : width) (a b q : itv) : wrapped * wrapped :=
    match a, b, q with
    | IBot, _, _ | _, IBot, _ | _, _, IBot => (WBot, WBot)
    | _, _, _ =>
      if assume_consistent o wa wb a b q then
        let refined := WrappedIntervalBack.interval_assume_pair o wa a b q in
        (wrapped_of_interval wa (fst refined), wrapped_of_interval wb (snd refined))
      else (WBot, WBot)
    end.

  Definition assume_piece (o : op) (wa wb : width) (a b q : itv) : wrapped * wrapped :=
    let pa := wrapped_pole_cut wa a in
    let pb := wrapped_pole_cut wb b in
    wrapped_pair_join wa wb
      (wrapped_pair_join wa wb (assume_piece_raw o wa wb (fst pa) (fst pb) q)
        (assume_piece_raw o wa wb (fst pa) (snd pb) q))
      (wrapped_pair_join wa wb (assume_piece_raw o wa wb (snd pa) (fst pb) q)
        (assume_piece_raw o wa wb (snd pa) (snd pb) q)).

  Definition assume_result (o : op) (wa wb : width) (a b : itv) (rw : width) (q : wrapped)
      : wrapped * wrapped :=
    let results := wrapped_parts rw q in
    wrapped_pair_join wa wb (assume_piece o wa wb a b (fst results))
      (assume_piece o wa wb a b (snd results)).

  Definition assume_binary_base (o : op) (wa wb : width) (a b : wrapped) (rw : width)
      (q : wrapped) : wrapped * wrapped :=
    let pa := wrapped_parts wa a in
    let pb := wrapped_parts wb b in
    let candidates := wrapped_pair_join wa wb
      (wrapped_pair_join wa wb (assume_result o wa wb (fst pa) (fst pb) rw q)
        (assume_result o wa wb (fst pa) (snd pb) rw q))
      (wrapped_pair_join wa wb (assume_result o wa wb (snd pa) (fst pb) rw q)
        (assume_result o wa wb (snd pa) (snd pb) rw q)) in
    (wrapped_meet wa a (fst candidates), wrapped_meet wb b (snd candidates)).

  Definition assume_binary (o : op) (wa wb : width) (a b : wrapped) (rw : width)
      (q : wrapped) : wrapped * wrapped :=
    match o with
    | bvadd => (wrapped_meet wa a (wrapped_sub wa q b), wrapped_meet wb b (wrapped_sub wb q a))
    | bvsub => (wrapped_meet wa a (wrapped_add wa q b), wrapped_meet wb b (wrapped_sub wb a q))
    | _ => assume_binary_base o wa wb a b rw q
    end.

  Definition assume_trunc (w : width) (a : wrapped) (rw : width) (q : wrapped) : wrapped :=
    let pa := wrapped_parts w a in
    let pq := wrapped_parts rw q in
    wrapped_meet w a (wrapped_join_four w
      (wrapped_of_interval w (WrappedIntervalBack.interval_assume_rewrap rw (fst pa) (fst pq)))
      (wrapped_of_interval w (WrappedIntervalBack.interval_assume_rewrap rw (fst pa) (snd pq)))
      (wrapped_of_interval w (WrappedIntervalBack.interval_assume_rewrap rw (snd pa) (fst pq)))
      (wrapped_of_interval w (WrappedIntervalBack.interval_assume_rewrap rw (snd pa) (snd pq)))).

  Definition assume_unary (o : op) (w : width) (a : wrapped) (rw : width) (q : wrapped)
      : wrapped :=
    match o with
    | bvzext _ | bvsext _ => wrapped_meet w a (wrapped_project w rw q)
    | bvtrunc _ => assume_trunc w a rw q
    | _ => wrapped_norm w a
    end.

  Definition backward_raw (o : op) (rw : width) (q : wrapped)
      (xs : list (width * wrapped)) : option (list wrapped) :=
    match xs with
    | [(w, a)] => Some [assume_unary o w a rw q]
    | [(wa, a); (wb, b)] => let p := assume_binary o wa wb a b rw q in Some [fst p; snd p]
    | _ => None
    end.
  Definition backward (o : op) (rw : width) (q : wrapped)
      (xs : list (width * wrapped)) : list wrapped :=
    match backward_raw o rw q xs with
    | Some ys => ys
    | None => map (fun wp => wrapped_norm (fst wp) (snd wp)) xs
    end.
End WrappedOpsCode.

Module WrappedTableCode (L : WORD_LANGUAGE_OPS) (W : WRAPPED_OPS L) <: WORD_TABLE_OPS L W.
  Module Ops := WrappedOpsCode L W.
  Definition wfwd := Ops.forward_raw.
  Definition wbwd := Ops.backward_raw.
End WrappedTableCode.

Module WrappedTable (L : WORD_LANGUAGE) (W : WRAPPED L) <: WRAPPED_TABLE L W.
  Include WrappedTableCode L W.
  Lemma wfwd_sound : forall o rw wps cs z r, wfwd o rw wps = Some r ->
    Forall2 (fun wp c => fst wp = fst c /\ L.is_word (fst c) (snd c) /\
      W.pgamma (fst wp) (snd wp) (snd c)) wps cs ->
    L.eval_op o cs = Some (rw, z) -> W.pgamma rw r z.
  Proof. Admitted. (* SIG-QUESTION: W arithmetic has no soundness or implementation pin. *)
  Lemma wbwd_sound : forall o rw q wps ys cs z, wbwd o rw q wps = Some ys ->
    Forall2 (fun wp c => fst wp = fst c /\ L.is_word (fst c) (snd c) /\
      W.pgamma (fst wp) (snd wp) (snd c)) wps cs ->
    L.eval_op o cs = Some (rw, z) -> W.pgamma rw q z ->
    Forall2 (fun wp c => W.pgamma (fst wp) (snd wp) (snd c))
      (combine (map fst wps) ys) cs.
  Proof. Admitted. (* SIG-QUESTION: W.pgamma is not linked to arc_gamma in WRAPPED. *)
End WrappedTable.
