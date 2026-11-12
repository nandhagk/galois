(** * Widening policy updates

    Policy updates select joins or widening at configured heads.
    For example, a stable contribution keeps the counter unchanged.
    Builds on: Fixpoint.PolicySig. *)

From Stdlib Require Import List PArith Arith NArith.
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
      if Nat.ltb cnt (delay h) then (L.join old new, S cnt)
      else (L.widen (wp p) old new, S cnt)
    end.
End PolicyCode.

Module Policy (L : WLATTICE) <: POLICY L.
  Include PolicyCode L.
  Include POLICY_SPEC L.

  Lemma update_ub : forall p x cnt old new,
    L.leb old (fst (update p x cnt old new)) = true /\
    L.leb new (fst (update p x cnt old new)) = true.
  Proof. Admitted.
  Lemma update_stable : forall p x cnt old new, L.leb new old = true ->
    update p x cnt old new = (old, cnt).
  Proof. Admitted.
  Lemma update_spec : forall p x cnt old new,
    update p x cnt old new =
      if L.leb new old then (old, cnt) else
      match trie_get x (heads p) with
      | None => (L.join old new, cnt)
      | Some h =>
        if Nat.ltb cnt (delay h) then (L.join old new, S cnt)
        else (L.widen (wp p) old new, S cnt)
      end.
  Proof. Admitted.
  Definition head_pot (h : head_cfg) (w : L.wparam) (cnt : nat) (a : L.t) : nat :=
    (delay h - cnt) + (if L.is_bot a then 1 else 0) +
      (if Nat.ltb cnt (delay h) then 0 else L.wrank w a).
  Lemma head_strict_steps : forall p x h cnt a new,
    trie_get x (heads p) = Some h -> L.leb new a = false ->
    Nat.leb (delay h) cnt = true ->
    let '(a', cnt') := update p x cnt a new in
    head_pot h (wp p) cnt' a' < head_pot h (wp p) cnt a.
  Proof. Admitted. (* SIG-QUESTION: rank can rise on the first widening. *)
  Lemma head_updates_le : forall p x h news a0,
    trie_get x (heads p) = Some h ->
    strict_count (run_updates p x 0 a0 news) <=
      delay h + 1 + L.wrank (wp p) (value_after_delay p x h a0 news).
  Proof. Admitted. (* SIG-QUESTION: the rank after the delay need not bound all updates. *)
End Policy.

Module PolicyT (L : WLATTICE_T) <: POLICY_T L.
  Include Policy L.
  TimeFun update.

  Definition c_pol : N := 1%N. (* STUB *)

  Lemma T_update_le : forall pol x cnt a b,
    (T_update pol x cnt a b <= c_pol *
      (N.of_nat (Pos.size_nat x) +
        L.c_lat * N.of_nat (L.size a + L.size b + L.wsize (wp pol) + 1) + 1))%N.
  Proof. Admitted. (* STUB *)
End PolicyT.
