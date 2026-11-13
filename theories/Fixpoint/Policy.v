(** * Widening policy updates

    Policy updates select joins or widening at configured heads.
    For example, a stable contribution keeps the counter unchanged.
    Builds on: Fixpoint.PolicySig. *)

From Stdlib Require Import List PArith Arith NArith Lia.
From Argent Require Import Time Tactics Std.
From Galois.Base Require Import Trie.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import PolicySig.

Module PolicyCode (L : WLATTICE_OPS) <: POLICY_OPS L.
  Definition update (p : policy L.wparam) x cnt old new :=
    if L.leb new old then (old, cnt) else
    match trie_get x (heads p) with
    | None => (L.join old new, cnt)
    | Some h =>
      if N.ltb cnt (delay h) then (L.join old new, N.succ cnt)
      else (L.widen (wp p) old new, N.succ cnt)
    end.
End PolicyCode.

Module Policy (L : WLATTICE) <: POLICY L.
  Include PolicyCode L.
  Include POLICY_SPEC L.

  (** An update covers both its previous value and its contribution. *)
  Lemma update_ub : forall p x cnt old new,
    L.leb old (fst (update p x cnt old new)) = true /\
    L.leb new (fst (update p x cnt old new)) = true.
  Proof.
    intros p x cnt old new; unfold update.
    destruct (L.leb new old) eqn:Hcovered.
    - split; [apply L.leb_refl | exact Hcovered].
    - destruct (trie_get x (heads p)) as [h |].
      + destruct (N.ltb cnt (delay h)); split;
          apply L.join_ub_l || apply L.join_ub_r ||
          apply L.widen_ub_l || apply L.widen_ub_r.
      + split; [apply L.join_ub_l | apply L.join_ub_r].
  Qed.

  (** A covered contribution preserves both the stored value and its counter. *)
  Lemma update_stable : forall p x cnt old new, L.leb new old = true ->
    update p x cnt old new = (old, cnt).
  Proof.
    intros p x cnt old new Hcovered; unfold update; now rewrite Hcovered.
  Qed.

  (** Policy data selects the unchanged, joined or widened result. *)
  Lemma update_spec : forall p x cnt old new,
    update p x cnt old new =
      if L.leb new old then (old, cnt) else
      match trie_get x (heads p) with
      | None => (L.join old new, cnt)
      | Some h =>
        if N.ltb cnt (delay h) then (L.join old new, N.succ cnt)
        else (L.widen (wp p) old new, N.succ cnt)
      end.
  Proof.
    reflexivity.
  Qed.

  (** A strict contribution cannot be covered by a recognized bottom. *)
  Local Lemma update_nonbottom : forall p x cnt a new,
    L.leb new a = false -> L.is_bot (fst (update p x cnt a new)) = false.
  Proof.
    intros p x cnt a new Hstrict.
    destruct (L.is_bot (fst (update p x cnt a new))) eqn:Hbottom; [|reflexivity].
    pose proof (proj2 (update_ub p x cnt a new)) as Hnew.
    pose proof (L.is_bot_least (fst (update p x cnt a new)) a Hbottom) as Hleast.
    pose proof (L.leb_trans new (fst (update p x cnt a new)) a Hnew Hleast) as Hcovered.
    congruence.
  Qed.

  (** After the delay, a strict update from a nonbottom consumes widening rank. *)
  Lemma head_strict_steps : forall p x h cnt a new,
    trie_get x (heads p) = Some h -> L.leb new a = false ->
    N.leb (delay h) cnt = true -> L.is_bot a = false ->
    let '(a', cnt') := update p x cnt a new in
    head_pot h (wp p) cnt' a' < head_pot h (wp p) cnt a.
  Proof.
    intros p x h cnt a new Hhead Hstrict Hdelay Hbottom.
    apply N.leb_le in Hdelay.
    assert (Htest : N.ltb cnt (delay h) = false) by (apply N.ltb_ge; lia).
    assert (Hnext_test : N.ltb (N.succ cnt) (delay h) = false)
      by (apply N.ltb_ge; lia).
    pose proof (update_nonbottom p x cnt a new Hstrict) as Hnext_bottom.
    unfold update in Hnext_bottom; rewrite Hstrict, Hhead, Htest in Hnext_bottom.
    unfold update; rewrite Hstrict, Hhead, Htest.
    unfold head_pot; rewrite Htest, Hnext_test, Hbottom.
    cbn [fst] in Hnext_bottom; rewrite Hnext_bottom.
    assert (Hspent : (delay h - cnt = 0)%N) by lia.
    assert (Hnext_spent : (delay h - N.succ cnt = 0)%N) by lia.
    rewrite Hspent, Hnext_spent; cbn [N.to_nat].
    apply L.wrank_widen; assumption.
  Qed.

  (** Processing one contribution exposes the same counter and value to the remaining fold. *)
  Local Lemma run_updates_cons : forall p x cnt a new news,
    run_updates p x cnt a (new :: news) =
      run_updates p x (snd (update p x cnt a new)) (fst (update p x cnt a new)) news.
  Proof.
    intros p x cnt a new news; unfold run_updates; cbn [fold_left fst snd].
    destruct (update p x cnt a new); reflexivity.
  Qed.

  (** Once widening has begun from a nonbottom, its rank bounds every later strict update. *)
  Local Lemma updates_after_delay : forall p x h news cnt a,
    trie_get x (heads p) = Some h -> (delay h <= cnt)%N -> L.is_bot a = false ->
    strict_count (run_updates p x cnt a news) <= N.to_nat cnt + L.wrank (wp p) a.
  Proof.
    intros p x h news; induction news as [|new news IH];
      intros cnt a Hhead Hdelay Hbottom.
    - change (N.to_nat cnt <= N.to_nat cnt + L.wrank (wp p) a); lia.
    - rewrite run_updates_cons.
      destruct (L.leb new a) eqn:Hstrict.
      + rewrite (update_stable p x cnt a new Hstrict); cbn [fst snd].
        apply IH; assumption.
      + assert (Htest : N.ltb cnt (delay h) = false) by (apply N.ltb_ge; lia).
        pose proof (update_nonbottom p x cnt a new Hstrict) as Hnext_bottom.
        unfold update in Hnext_bottom; rewrite Hstrict, Hhead, Htest in Hnext_bottom.
        unfold update; rewrite Hstrict, Hhead, Htest; cbn [fst snd].
        specialize (IH (N.succ cnt) (L.widen (wp p) a new) Hhead ltac:(lia) Hnext_bottom).
        pose proof (L.wrank_widen (wp p) a new Hbottom Hstrict) as Hrank.
        rewrite N2Nat.inj_succ in IH; lia.
  Qed.

  (** The boundary observer returns the current value once its counter has reached the limit. *)
  Local Lemma value_at_counter_stop : forall p x limit cnt a news,
    (limit <= cnt)%N -> value_at_counter update p x limit cnt a news = a.
  Proof.
    intros p x limit cnt a news Hlimit.
    assert (Hstop : N.leb limit cnt = true) by (apply N.leb_le; exact Hlimit).
    destruct news; cbn [value_at_counter]; now rewrite Hstop.
  Qed.

  (** The delayed prefix spends at most the delay and one update before rank accounting. *)
  Local Lemma updates_through_delay : forall p x h news cnt a,
    trie_get x (heads p) = Some h -> (cnt <= delay h)%N ->
    strict_count (run_updates p x cnt a news) <=
      N.to_nat (N.succ (delay h)) +
      L.wrank (wp p) (value_at_counter update p x (N.succ (delay h)) cnt a news).
  Proof.
    intros p x h news; induction news as [|new news IH]; intros cnt a Hhead Hdelay.
    - unfold strict_count, run_updates; cbn [fold_left snd].
      rewrite N2Nat.inj_succ; lia.
    - assert (Hstop : N.leb (N.succ (delay h)) cnt = false)
        by (apply N.leb_gt; lia).
      rewrite run_updates_cons; cbn [value_at_counter]; rewrite Hstop.
      destruct (L.leb new a) eqn:Hstrict.
      + rewrite (update_stable p x cnt a new Hstrict); cbn [fst snd].
        apply IH; assumption.
      + unfold update; rewrite Hstrict, Hhead.
        destruct (N.ltb cnt (delay h)) eqn:Htest; cbn [fst snd].
        * apply IH; [exact Hhead | apply N.ltb_lt in Htest; lia].
        * apply N.ltb_ge in Htest.
          assert (Hcnt : cnt = delay h) by lia; subst cnt.
          rewrite value_at_counter_stop by lia.
          eapply updates_after_delay; [exact Hhead | lia |].
          pose proof (update_nonbottom p x (delay h) a new Hstrict) as Hnext_bottom.
          unfold update in Hnext_bottom.
          rewrite Hstrict, Hhead, N.ltb_irrefl in Hnext_bottom.
          exact Hnext_bottom.
  Qed.

  (** The delay, its boundary update and the remaining rank bound all strict head updates. *)
  Lemma head_updates_le : forall p x h news a0,
    trie_get x (heads p) = Some h ->
    strict_count (run_updates p x 0%N a0 news) <=
      N.to_nat (delay h) + 1 + L.wrank (wp p) (value_after_delay p x h a0 news).
  Proof.
    intros p x h news a0 Hhead.
    pose proof (updates_through_delay p x h news 0%N a0 Hhead ltac:(lia)) as Hupdates.
    unfold value_after_delay; rewrite N2Nat.inj_succ in Hupdates; lia.
  Qed.

  (** Strict updates leave bottom. *)
  Lemma update_leaves_bot : forall p x cnt a new, L.leb new a = false ->
    L.is_bot (fst (update p x cnt a new)) = false.
  Proof.
    exact update_nonbottom.
  Qed.
End Policy.

Module PolicyT (L : WLATTICE_T) <: POLICY_T L.
  Include Policy L.
  TimeFun update.

  Definition c_pol : N := (16 * (PTrieT.c_trie + 1))%N.

  (** Counter comparison costs at most one traversal of its first argument. *)
  Local Lemma T_counter_ltb_le : forall n m,
    (N.T_ltb n m <= N.of_nat (N.size_nat n) + 3)%N.
  Proof.
    intros n m; pose proof (N.T_compare_le n m); time_step.
  Qed.

  (** Updating pays for the selected lattice operation, lookup and counter operations. *)
  Lemma T_update_le : forall pol x cnt a b,
    (T_update pol x cnt a b <= c_pol *
      (N.of_nat (Pos.size_nat x) + L.c_lat * N.of_nat (L.size a + L.size b + 1) +
       (if L.leb b a then 0 else
          match trie_get x (heads pol) with
          | Some _ => N.of_nat (N.size_nat cnt) + L.c_lat *
              N.of_nat ((L.wunits a + L.wunits b + 1) * L.wsize (wp pol))
          | None => 0
          end) + 1))%N.
  Proof.
    intros pol x cnt a b.
    pose proof (L.T_leb_le b a) as Hleb.
    replace (L.size b + L.size a + 1) with (L.size a + L.size b + 1) in Hleb by lia.
    pose proof (L.T_join_le a b) as Hjoin.
    pose proof (L.T_widen_le (wp pol) a b) as Hwiden.
    replace ((L.wunits a + L.wunits b) * L.wsize (wp pol) +
      (L.size a + L.size b + L.wsize (wp pol) + 1)) with
      ((L.size a + L.size b + 1) +
        (L.wunits a + L.wunits b + 1) * L.wsize (wp pol)) in Hwiden by nia.
    rewrite Nat2N.inj_add, N.mul_add_distr_l in Hwiden.
    pose proof (PTrieT.T_get_le head_cfg x (heads pol)) as Hget.
    unfold PTrieT.T_get in Hget; rewrite Nat2N.inj_add in Hget.
    pose proof (N.T_succ_le cnt) as Hsucc.
    remember (L.c_lat * N.of_nat (L.size a + L.size b + 1))%N
      as value_work eqn:Hvalue_work in *.
    remember (L.c_lat *
      N.of_nat ((L.wunits a + L.wunits b + 1) * L.wsize (wp pol)))%N
      as widen_work eqn:Hwiden_work in *.
    clear Hvalue_work Hwiden_work.
    unfold T_update, c_pol, T_heads, T_delay, T_wp.
    destruct (L.leb b a) eqn:Hcovered.
    - clear -Hleb; time_cbn_all; nia.
    - destruct (trie_get x (heads pol)) as [h |] eqn:Hhead.
      + pose proof (T_counter_ltb_le cnt (delay h)) as Htest.
        destruct (N.ltb cnt (delay h)).
        * clear -Hleb Hjoin Hget Hsucc Htest; time_cbn_all; nia.
        * clear -Hleb Hwiden Hget Hsucc Htest; time_cbn_all; nia.
      + clear -Hleb Hjoin Hget; time_cbn_all; nia.
  Qed.
End PolicyT.
