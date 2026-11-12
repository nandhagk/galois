(** * Transfer harness

    The harness combines concrete singleton evaluation with abstract transfer tables.
    For example, an unmodeled forward operation returns top.
    Builds on: HarnessSig. *)

From Stdlib Require Import List.
From Galois.Domains Require Import LangSig HarnessSig.

Module HarnessCode (L : LANG_OPS) (B : HARNESS_BASE_OPS L) (T : TABLE_OPS L B)
    <: HARNESS_OPS L B T.
  Definition t := B.t.
  Definition leb := B.leb.
  Definition bot := B.bot.
  Definition is_bot := B.is_bot.
  Definition join := B.join.
  Definition top := B.top.
  Definition meet := B.meet.
  Definition wparam := B.wparam.
  Definition widen := B.widen.
  Definition narrow := B.narrow.

  Fixpoint points (xs : list B.t) : option (list L.val) :=
    match xs with
    | nil => Some nil
    | x :: rest =>
      match B.point x, points rest with
      | Some c, Some cs => Some (c :: cs)
      | _, _ => None
      end
    end.

  Definition forward (o : L.op) (xs : list B.t) : B.t :=
    if existsb B.is_bot xs then B.bot else
    match points xs with
    | Some cs => match L.eval o cs with Some c => B.abst c | None => B.bot end
    | None => match T.fwd o xs with Some r => r | None => B.top end
    end.

  Fixpoint meet_all (xs ys : list B.t) : list B.t :=
    match xs, ys with
    | x :: rest, y :: tail => B.meet x y :: meet_all rest tail
    | _, _ => xs
    end.

  Definition backward (o : L.op) (r : B.t) (xs : list B.t) : list B.t :=
    match T.bwd o r xs with
    | Some ys => if Nat.eqb (length ys) (length xs) then meet_all xs ys else xs
    | None => xs
    end.

  Definition guard (g : L.guard) (xs : list B.t) : list B.t :=
    match T.grd g xs with
    | Some ys => if Nat.eqb (length ys) (length xs) then meet_all xs ys else xs
    | None => xs
    end.
End HarnessCode.

Module Harness (L : LANG) (B : HARNESS_BASE L) (T : TABLE L B) <: HARNESS L B T.
  Include HarnessCode L B T.
  Definition leb_refl := B.leb_refl.
  Definition leb_trans := B.leb_trans.
  Definition bot_least := B.bot_least.
  Definition is_bot_bot := B.is_bot_bot.
  Definition is_bot_least := B.is_bot_least.
  Definition join_ub_l := B.join_ub_l.
  Definition join_ub_r := B.join_ub_r.
  Definition top_greatest := B.top_greatest.
  Definition meet_lb_l := B.meet_lb_l.
  Definition meet_lb_r := B.meet_lb_r.
  Definition wrank := B.wrank.
  Definition widen_ub_l := B.widen_ub_l.
  Definition widen_ub_r := B.widen_ub_r.
  Definition widen_stable := B.widen_stable.
  Definition wrank_widen := B.wrank_widen.
  Definition wrank_widen_le := B.wrank_widen_le.
  Definition narrow_between := B.narrow_between.
  Definition gamma := B.gamma.
  Definition gamma_mono := B.gamma_mono.
  Definition gamma_bot := B.gamma_bot.
  Definition gamma_top := B.gamma_top.
  Definition gamma_meet := B.gamma_meet.
  Definition is_bot_sound := B.is_bot_sound.
  Definition is_bot_below := B.is_bot_below.

  Lemma forward_sound : forall o xs cs c,
    Forall2 gamma xs cs -> L.eval o cs = Some c -> gamma (forward o xs) c.
  Proof. Admitted.

  Lemma backward_sound : forall o r xs cs c,
    Forall2 gamma xs cs -> L.eval o cs = Some c -> gamma r c ->
    Forall2 gamma (backward o r xs) cs.
  Proof. Admitted.

  Lemma backward_refines : forall o r xs,
    Forall2 (fun y x => leb y x = true) (backward o r xs) xs.
  Proof. Admitted.

  Lemma guard_sound : forall g xs cs,
    Forall2 gamma xs cs -> L.holds g cs -> Forall2 gamma (guard g xs) cs.
  Proof. Admitted.

  Lemma guard_refines : forall g xs,
    Forall2 (fun y x => leb y x = true) (guard g xs) xs.
  Proof. Admitted.
End Harness.
