(** * Code-keyed widening policies

    Policies store priorities and widening heads as data.
    For example, a head with zero delay widens at its first strict update.
    Builds on: Base.Trie and Lattice.LatticeSig. *)

From Stdlib Require Import PArith List Arith NArith.
From Argent Require Import Time Tactics Std.
From Galois.Base Require Import Trie.
From Galois.Lattice Require Import LatticeSig.

Record head_cfg := HeadCfg {
  delay : N;
  narrow_passes : nat
}.

Record policy (W : Type) := Policy {
  prio : PTrieCode.t positive;
  heads : PTrieCode.t head_cfg;
  wp : W;
  passes : nat
}.

Arguments prio {W} _.
Arguments heads {W} _.
Arguments wp {W} _.
Arguments passes {W} _.

TimeFun prio.
TimeFun heads.
TimeFun wp.
TimeFun passes.
TimeFun delay.
TimeFun narrow_passes.

(** The delay boundary counts strict updates and skips stable contributions. *)
Fixpoint value_at_counter {A W : Type}
    (update : policy W -> positive -> N -> A -> A -> A * N)
    (pol : policy W) (x : positive) (limit cnt : N) (a : A) (news : list A) : A :=
  if N.leb limit cnt then a else
  match news with
  | nil => a
  | new :: rest =>
    let ac := update pol x cnt a new in
    value_at_counter update pol x limit (snd ac) (fst ac) rest
  end.
TimeFun value_at_counter.

Module Type POLICY_OPS (L : WLATTICE_OPS).
  Parameter update : policy L.wparam -> positive -> N -> L.t -> L.t -> L.t * N.
End POLICY_OPS.

Module Type POLICY_SPEC (L : WLATTICE) (Import P : POLICY_OPS L).
  Definition run_updates (pol : policy L.wparam) (x : positive)
      (cnt : N) (a : L.t) (news : list L.t) : L.t * N :=
    fold_left (fun ac new => update pol x (snd ac) (fst ac) new) news (a, cnt).
  Definition strict_count (ac : L.t * N) : nat := N.to_nat (snd ac).
  Definition value_after_delay (pol : policy L.wparam) (x : positive)
      (h : head_cfg) (a : L.t) (news : list L.t) : L.t :=
    value_at_counter update pol x (N.succ (delay h)) 0%N a news.
  (** Head potential combines delay credit, bottom credit and widening rank. *)
  Definition head_pot (h : head_cfg) (w : L.wparam) (cnt : N) (a : L.t) : nat :=
    N.to_nat (delay h - cnt) + (if L.is_bot a then 1 else 0) +
      (if N.ltb cnt (delay h) then 0 else L.wrank w a).
End POLICY_SPEC.

Module Type POLICY_LAWS (L : WLATTICE) (Import P : POLICY_OPS L)
    (Import PS : POLICY_SPEC L P).
  (** An update covers both its previous value and its contribution. *)
  Parameter update_ub : forall p x cnt old new,
    L.leb old (fst (update p x cnt old new)) = true /\
    L.leb new (fst (update p x cnt old new)) = true.
  (** A covered contribution leaves the value and counter unchanged. *)
  Parameter update_stable : forall p x cnt old new, L.leb new old = true ->
    update p x cnt old new = (old, cnt).
  (** Updates follow the policy's delay and widening head. *)
  Parameter update_spec : forall p x cnt old new,
    update p x cnt old new =
      if L.leb new old then (old, cnt) else
      match trie_get x (heads p) with
      | None => (L.join old new, cnt)
      | Some h =>
        if N.ltb cnt (delay h) then (L.join old new, N.succ cnt)
        else (L.widen (wp p) old new, N.succ cnt)
      end.
  (** Every strict update after the delay lowers head potential. *)
  Parameter head_strict_steps : forall p x h cnt a new,
    trie_get x (heads p) = Some h -> L.leb new a = false ->
    N.leb (delay h) cnt = true -> L.is_bot a = false ->
    let '(a', cnt') := update p x cnt a new in
    head_pot h (wp p) cnt' a' < head_pot h (wp p) cnt a.
  (** Strict head updates are bounded by delay and the rank after the delay. *)
  Parameter head_updates_le : forall p x h news a0,
    trie_get x (heads p) = Some h ->
    strict_count (run_updates p x 0%N a0 news) <=
      N.to_nat (delay h) + 1 + L.wrank (wp p) (value_after_delay p x h a0 news).
  (** Strict updates leave bottom. *)
  Parameter update_leaves_bot : forall p x cnt a new, L.leb new a = false ->
    L.is_bot (fst (update p x cnt a new)) = false.
End POLICY_LAWS.

Module Type POLICY (L : WLATTICE) :=
  POLICY_OPS L <+ POLICY_SPEC L <+ POLICY_LAWS L.

Module Type POLICY_TIME (L : WLATTICE_T) (Import P : POLICY L).
  Parameter T_update : policy L.wparam -> positive -> N -> L.t -> L.t -> N.
  Parameter c_pol : N.
  (** Updating accounts for key lookup, both values and widening parameters. *)
  Parameter T_update_le : forall pol x cnt a b,
    (T_update pol x cnt a b <= c_pol *
      (N.of_nat (Pos.size_nat x) + L.c_lat * N.of_nat (L.size a + L.size b + 1) +
       (if L.leb b a then 0 else
          match trie_get x (heads pol) with
          | Some _ => N.of_nat (N.size_nat cnt) + L.c_lat *
              N.of_nat ((L.wunits a + L.wunits b + 1) * L.wsize (wp pol))
          | None => 0
          end) + 1))%N.
End POLICY_TIME.

Module Type POLICY_T (L : WLATTICE_T) := POLICY L <+ POLICY_TIME L.
