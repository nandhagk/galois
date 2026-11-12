(** * Value domain translation

    Translation reuses a value domain under operator and guard mappings.
    For example, a source operator can dispatch to a target operator before transfer.
    Builds on: LangSig and ValueSig. *)

From Stdlib Require Import List NArith.
From Argent Require Import Time.
From Galois.Domains Require Import LangSig ValueSig.

Module Type LANG_MORPHISM_OPS := LangSig.LANG_MORPHISM_OPS.

Module TranslateCode (L1 L2 : LANG_OPS) (F : LANG_MORPHISM_OPS L1 L2)
    (D : VALUE_DOMAIN_OPS L2) <: VALUE_DOMAIN_OPS L1.
  Definition t := D.t.
  Definition leb := D.leb.
  Definition bot := D.bot.
  Definition is_bot := D.is_bot.
  Definition join := D.join.
  Definition top := D.top.
  Definition meet := D.meet.
  Definition wparam := D.wparam.
  Definition widen := D.widen.
  Definition narrow := D.narrow.
  Definition forward (o : L1.op) (xs : list t) := D.forward (F.op o) xs.
  Definition backward (o : L1.op) (r : t) (xs : list t) := D.backward (F.op o) r xs.
  Definition guard (g : L1.guard) (xs : list t) := D.guard (F.guard g) xs.
End TranslateCode.

Module Translate (L1 L2 : LANG) (F : LANG_MORPHISM L1 L2)
    (D : VALUE_DOMAIN L2) <: VALUE_DOMAIN L1.
  Include TranslateCode L1 L2 F D.
  Definition wrank := D.wrank.
  Definition gamma (a : t) (c : L1.val) := D.gamma a (F.value c).
  Definition leb_refl := D.leb_refl.
  Definition leb_trans := D.leb_trans.
  Definition bot_least := D.bot_least.
  Definition is_bot_bot := D.is_bot_bot.
  Definition is_bot_least := D.is_bot_least.
  Definition join_ub_l := D.join_ub_l.
  Definition join_ub_r := D.join_ub_r.
  Definition top_greatest := D.top_greatest.
  Definition meet_lb_l := D.meet_lb_l.
  Definition meet_lb_r := D.meet_lb_r.
  Definition widen_ub_l := D.widen_ub_l.
  Definition widen_ub_r := D.widen_ub_r.
  Definition widen_stable := D.widen_stable.
  Definition wrank_widen := D.wrank_widen.
  Definition wrank_widen_le := D.wrank_widen_le.
  Definition narrow_between := D.narrow_between.
  Definition gamma_mono a b c := D.gamma_mono a b (F.value c).
  Definition gamma_bot c := D.gamma_bot (F.value c).
  Definition gamma_top c := D.gamma_top (F.value c).
  Definition gamma_meet a b c := D.gamma_meet a b (F.value c).
  Definition is_bot_sound a c := D.is_bot_sound a (F.value c).
  Definition is_bot_below := D.is_bot_below.
  Lemma forward_sound : forall o xs cs c,
    Forall2 gamma xs cs -> L1.eval o cs = Some c -> gamma (forward o xs) c.
  Proof. Admitted. (* CONVERT: rename_laws: The term "cs" has type "list L1.val" while it is expected to have type *)
  Lemma backward_sound : forall o r xs cs c,
    Forall2 gamma xs cs -> L1.eval o cs = Some c -> gamma r c ->
    Forall2 gamma (backward o r xs) cs.
  Proof. Admitted. (* CONVERT: rename_laws: The term "cs" has type "list L1.val" while it is expected to have type *)
  Definition backward_refines o := D.backward_refines (F.op o).
  Lemma guard_sound : forall g xs cs,
    Forall2 gamma xs cs -> L1.holds g cs -> Forall2 gamma (guard g xs) cs.
  Proof. Admitted. (* CONVERT: rename_laws: The term "cs" has type "list L1.val" while it is expected to have type *)
  Definition guard_refines g := D.guard_refines (F.guard g).
End Translate.

Module TranslateT (L1 L2 : LANG_T) (F : LANG_MORPHISM_T L1 L2)
    (D : VALUE_DOMAIN_T L2) <: VALUE_DOMAIN_T L1.
  Include Translate L1 L2 F D.
  TimeFun leb.
  TimeFun bot.
  TimeFun is_bot.
  TimeFun join.
  TimeFun top.
  TimeFun meet.
  TimeFun widen.
  TimeFun narrow.
  TimeFun forward.
  TimeFun backward.
  TimeFun guard.

  Definition size (a : t) : nat := D.size a.
  Definition work (o : L1.op) (xs : list t) : nat :=
    F.op_work o + D.work (F.op o) xs + 1.
  Definition gwork (g : L1.guard) (xs : list t) : nat :=
    F.guard_work g + D.gwork (F.guard g) xs + 1.
  Definition wsize (p : wparam) : nat := D.wsize p.
  Definition wunits (a : t) : nat := D.wunits a.
  Definition c_val : N := D.c_val + F.c_morphism + 1%N. (* STUB *)
  Definition c_lat : N := c_val.
  Lemma c_lat_pos : (1 <= c_lat)%N.
  Proof. Admitted. (* STUB *)
  Lemma T_leb_le : forall a b,
    (T_leb a b <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_join_le : forall a b,
    (T_join a b <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_meet_le : forall a b,
    (T_meet a b <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_is_bot_le : forall a,
    (T_is_bot a <= c_val * N.of_nat (size a + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_widen_le : forall p a b,
    (T_widen p a b <= c_val * N.of_nat (size a + size b + wsize p + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_narrow_le : forall a b,
    (T_narrow a b <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_forward_le : forall o xs,
    (T_forward o xs <= c_val * N.of_nat (work o xs + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_backward_le : forall o r xs,
    (T_backward o r xs <= c_val * N.of_nat (work o xs + size r + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_guard_le : forall g xs,
    (T_guard g xs <= c_val * N.of_nat (gwork g xs + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma forward_size : forall o xs,
    (N.of_nat (size (forward o xs)) <= c_val * N.of_nat (work o xs + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma meet_size : forall a b,
    (N.of_nat (size (meet a b)) <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma join_size : forall a b,
    (N.of_nat (size (join a b)) <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma widen_size : forall p a b,
    (N.of_nat (size (widen p a b)) <=
      c_val * N.of_nat (size a + size b + wsize p + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma backward_size : forall o r xs,
    (N.of_nat (fold_right Nat.add 0%nat (map size (backward o r xs))) <=
      c_val * N.of_nat (work o xs + size r + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma guard_size : forall g xs,
    (N.of_nat (fold_right Nat.add 0%nat (map size (guard g xs))) <=
      c_val * N.of_nat (gwork g xs + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma work_sizes : forall o xs,
    fold_right Nat.add 0%nat (map size xs) <= work o xs.
  Proof. Admitted. (* STUB *)
  Lemma gwork_sizes : forall g xs,
    fold_right Nat.add 0%nat (map size xs) <= gwork g xs.
  Proof. Admitted. (* STUB *)
End TranslateT.
