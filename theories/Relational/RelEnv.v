(** * Relational and value-state composition

    Relational environments combine a numeric state with a value state.
    For example, a numeric range query can refine an interval value.
    Builds on: RelEnvSig, NumStateSig, StateSig and ValueSig. *)

From Stdlib Require Import NArith List.
From Argent Require Import Time Tactics Std.
From Argent Require Import Time.
From Galois.Base Require Import KeySig.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import LangSig ValueSig Product.
From Galois.States Require Import StateSig.
From Galois.Relational Require Import LinearizeSig NumStateSig RelEnvSig.

Module RelEnvCode (X : KEY_OPS) (L : LANG_OPS) (V : VALUE_DOMAIN_OPS L)
    (F : LINEARIZE_OPS X L) (R : NUM_STATE_OPS X L F) (E : STATE_DOMAIN_OPS X L V)
    (RR : REL_RANGE_REFINE_OPS L V)
    (P : LATTICE_OPS with Definition t := (R.t * E.t)%type)
    <: REL_ENV_OPS X L V F R E RR P.
  Definition t := (R.t * E.t)%type.
  Definition leb := P.leb.
  Definition bot := P.bot.
  Definition is_bot := P.is_bot.
  Definition join := P.join.
  Definition top : t := (R.top, E.top).
  Definition meet (a b : t) : t := (R.meet (fst a) (fst b), E.meet (snd a) (snd b)).
  Definition wparam := (R.wparam * E.wparam)%type.
  Definition widen (p : wparam) (a b : t) : t :=
    if is_bot b then a
    else (R.widen (fst p) (fst a) (fst b), E.widen (snd p) (snd a) (snd b)).
  Definition narrow := product_narrow R.is_bot E.is_bot R.narrow E.narrow.
  Definition assign x e (s : t) : t := (R.assign x e (fst s), E.assign x e (snd s)).
  Definition havoc x (s : t) : t := (R.havoc x (fst s), E.havoc x (snd s)).
  Definition assume g es (s : t) : t := (R.assume g es (fst s), E.assume g es (snd s)).
  Definition eval e (s : t) : V.t :=
    let bounds := R.range e (fst s) in
    RR.refine_range (fst bounds) (snd bounds) (E.eval e (snd s)).
End RelEnvCode.

Module RelEnv (X : KEY) (L : LANG) (N : NUM_VIEW L) (V : VALUE_DOMAIN L)
    (F : LINEARIZE X L N) (R : NUM_STATE X L N F) (E : STATE_DOMAIN X L V)
    (RR : RANGE_REFINE L N V)
    (P : LATTICE with Definition t := (R.t * E.t)%type)
    (PL : REL_PAIR_LINK X L N V F R E P) <: REL_ENV X L N V F R E RR P PL.
  Include RelEnvCode X L V F R E RR P.
  Definition wrank (p : wparam) (s : t) : nat :=
    R.wrank (fst p) (fst s) + E.wrank (snd p) (snd s).
  Definition gamma (s : t) (st : X.t -> L.val) : Prop :=
    R.ngamma (fst s) (fun x => N.num (st x)) /\ E.gamma (snd s) st.
  Lemma leb_refl : forall a, leb a a = true.
  Proof. Admitted. (* STUB *)
  (** The order composes through an intermediate value. *)
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof. Admitted. (* STUB *)
  (** Bottom is below every value. *)
  Lemma bot_least : forall a, leb bot a = true.
  Proof. Admitted. (* STUB *)
  (** The bottom test recognizes bottom. *)
  Lemma is_bot_bot : is_bot bot = true.
  Proof. Admitted. (* STUB *)
  (** Every recognized bottom is below every value. *)
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof. Admitted. (* STUB *)
  (** Join is above its left operand. *)
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof. Admitted. (* STUB *)
  (** Join is above its right operand. *)
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof. Admitted. (* STUB *)

  Lemma top_greatest : forall a, leb a top = true.
  Proof. Admitted. (* STUB *)

  (** Widening is above its previous value. *)
  Lemma widen_ub_l : forall p a b, leb a (widen p a b) = true.
  Proof. Admitted. (* STUB *)
  (** Widening is above its candidate value. *)
  Lemma widen_ub_r : forall p a b, leb b (widen p a b) = true.
  Proof. Admitted. (* STUB *)
  (** A candidate below the previous value leaves widening unchanged. *)
  Lemma widen_stable : forall p a b, leb b a = true -> widen p a b = a.
  Proof. Admitted. (* STUB *)
  (** An unstable widening from a nonbottom strictly decreases rank. *)
  Lemma wrank_widen : forall p a b, is_bot a = false -> leb b a = false ->
    wrank p (widen p a b) < wrank p a.
  Proof. Admitted. (* STUB *)
  (** Widening from a nonbottom does not increase rank. *)
  Lemma wrank_widen_le : forall p a b, is_bot a = false -> wrank p (widen p a b) <= wrank p a.
  Proof. Admitted. (* STUB *)
  (** Narrowing stays between an ordered candidate and previous value. *)
  Lemma narrow_between : forall a b, leb b a = true ->
    leb b (narrow a b) = true /\ leb (narrow a b) a = true.
  Proof. Admitted. (* STUB *)

  (** Abstract inclusion entails inclusion of concrete environments. *)
  Lemma gamma_mono : forall a b st, leb a b = true -> gamma a st -> gamma b st.
  Proof. Admitted. (* STUB *)
  (** Bottom describes no concrete environment. *)
  Lemma gamma_bot : forall st, ~ gamma bot st.
  Proof. Admitted. (* STUB *)
  (** Top describes every concrete environment. *)
  Lemma gamma_top : forall st, gamma top st.
  Proof. Admitted. (* STUB *)
  (** Assignment contains each successful concrete update. *)
  Lemma assign_sound : forall x e s st c,
    gamma s st -> eval_term L.eval st e = Some c ->
    gamma (assign x e s) (upd X.eqb st x c).
  Proof. Admitted. (* STUB *)
  (** Havoc contains every concrete update of the selected variable. *)
  Lemma havoc_sound : forall x s st c,
    gamma s st -> gamma (havoc x s) (upd X.eqb st x c).
  Proof. Admitted. (* STUB *)
  (** Assuming a true guard retains its concrete environment. *)
  Lemma assume_sound : forall g es s st cs,
    gamma s st -> eval_terms L.eval st es = Some cs -> L.holds g cs ->
    gamma (assume g es s) st.
  Proof. Admitted. (* STUB *)
  (** Abstract evaluation describes every successful concrete result. *)
  Lemma eval_sound : forall e s st c,
    gamma s st -> eval_term L.eval st e = Some c -> V.gamma (eval e s) c.
  Proof. Admitted. (* STUB *)

End RelEnv.

Module RelEnvT (X : KEY_T) (L : LANG_T) (N : NUM_VIEW L) (V : VALUE_DOMAIN_T L)
    (F : LINEARIZE_T X L N) (R : NUM_STATE_T X L N F) (E : STATE_DOMAIN_T X L V)
    (RR : REL_RANGE_REFINE_T L N V)
    (P : LATTICE_T with Definition t := (R.t * E.t)%type
      with Definition size := fun a => R.size (fst a) + E.size (snd a))
    (PL : REL_PAIR_LINK X L N V F R E P)
    <: REL_ENV_ALL X L N V F R E RR P PL.
  Include RelEnv X L N V F R E RR P PL.
  Definition size (a : t) : nat := R.size (fst a) + E.size (snd a).
  Definition wsize (p : wparam) : nat := R.wsize (fst p) + E.wsize (snd p).
  Definition wunits (a : t) : nat := R.wunits (fst a) + E.wunits (snd a).
  Definition assign_work (x : X.t) (e : term L.op X.t) (s : t) : nat :=
    R.assign_work x e (fst s) + E.assign_work x e (snd s).
  Definition havoc_work (x : X.t) (s : t) : nat :=
    R.havoc_work x (fst s) + E.havoc_work x (snd s).
  Definition assume_work (g : L.guard) (es : list (term L.op X.t)) (s : t) : nat :=
    R.assume_work g es (fst s) + E.assume_work g es (snd s).
  Definition eval_work (e : term L.op X.t) (s : t) : nat :=
    R.range_work e (fst s) + R.range_bits e (fst s) + E.eval_work e (snd s) +
      V.size (E.eval e (snd s)) + 1.
  TimeFun leb.
  TimeFun bot.
  TimeFun is_bot.
  TimeFun join.
  TimeFun top.
  TimeFun widen.
  TimeFun narrow.
  TimeFun assign.
  TimeFun havoc.
  TimeFun assume.
  TimeFun eval.
  Definition c_rel_env : N := 1. (* STUB *)
  Definition c_lat : N := 1. (* STUB *)
  Definition c_state : N := 1. (* STUB *)
  Lemma c_lat_pos : (1 <= c_lat)%N.
  Proof. Admitted. (* STUB *)
  Lemma T_leb_le : forall a b,
    (T_leb a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_join_le : forall a b,
    (T_join a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_is_bot_le : forall a,
    (T_is_bot a <= c_lat * N.of_nat (size a + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_widen_le : forall p a b,
    (T_widen p a b <= c_lat * N.of_nat
      ((wunits a + wunits b) * wsize p + (size a + size b + wsize p + 1)))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_narrow_le : forall a b,
    (T_narrow a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_assign_le : forall x e s,
    (T_assign x e s <= c_state * N.of_nat (assign_work x e s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_havoc_le : forall x s,
    (T_havoc x s <= c_state * N.of_nat (havoc_work x s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_assume_le : forall g es s,
    (T_assume g es s <= c_state * N.of_nat (assume_work g es s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_eval_le : forall e s,
    (T_eval e s <= c_state * N.of_nat (eval_work e s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_eval_components : forall e r s, (T_eval e (r, s) <= c_rel_env *
    (R.T_range e r + E.T_eval e s +
      RR.T_refine_range (fst (R.range e r)) (snd (R.range e r)) (E.eval e s) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_assign_components : forall x e r s, (T_assign x e (r, s) <=
    c_rel_env * (R.T_assign x e r + E.T_assign x e s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_havoc_components : forall x r s, (T_havoc x (r, s) <=
    c_rel_env * (R.T_havoc x r + E.T_havoc x s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_assume_components : forall g es r s, (T_assume g es (r, s) <=
    c_rel_env * (R.T_assume g es r + E.T_assume g es s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma eval_work_components : forall e r s, eval_work e (r, s) =
    R.range_work e r + R.range_bits e r + E.eval_work e s + V.size (E.eval e s) + 1.
  Proof. reflexivity. Qed.
  (** Assignment work adds the work of both components. *)
  Lemma assign_work_components : forall x e r s,
    assign_work x e (r, s) = R.assign_work x e r + E.assign_work x e s.
  Proof. Admitted. (* STUB *)
  (** Havoc work adds the work of both components. *)
  Lemma havoc_work_components : forall x r s,
    havoc_work x (r, s) = R.havoc_work x r + E.havoc_work x s.
  Proof. Admitted. (* STUB *)
  (** Assumption work adds the work of both components. *)
  Lemma assume_work_components : forall g es r s,
    assume_work g es (r, s) = R.assume_work g es r + E.assume_work g es s.
  Proof. Admitted. (* STUB *)
  (** Widening visits the units of both components. *)
  Lemma wunits_components : forall r s, wunits (r, s) = R.wunits r + E.wunits s.
  Proof. Admitted. (* STUB *)
  (** The widening parameter is measured by its two component parameters. *)
  Lemma wsize_components : forall p, wsize p = R.wsize (fst p) + E.wsize (snd p).
  Proof. Admitted. (* STUB *)
  Lemma c_lat_pair : (P.c_lat <= c_lat)%N.
  Proof. Admitted. (* STUB *)
  Lemma size_pair : forall a, P.size a = R.size (fst a) + E.size (snd a).
  Proof. reflexivity. Qed.
  Lemma F1_gamma : forall r s st,
    gamma (r, s) st <-> R.ngamma r (fun x => N.num (st x)) /\ E.gamma s st.
  Proof. Admitted. (* STUB *)
  Lemma F2_eval : forall e r s, eval e (r, s) =
    RR.refine_range (fst (R.range e r)) (snd (R.range e r)) (E.eval e s).
  Proof. Admitted. (* STUB *)
  Lemma F3_assign : forall x e r s, assign x e (r, s) =
    (R.assign x e r, E.assign x e s).
  Proof. Admitted. (* STUB *)
  Lemma F4_havoc : forall x r s, havoc x (r, s) = (R.havoc x r, E.havoc x s).
  Proof. Admitted. (* STUB *)
  Lemma F5_assume : forall g es r s,
    assume g es (r, s) = (R.assume g es r, E.assume g es s).
  Proof. Admitted. (* STUB *)
  Lemma F6_widen : forall p r s r' s', widen p (r, s) (r', s') =
    if is_bot (r', s') then (r, s)
    else (R.widen (fst p) r r', E.widen (snd p) s s').
  Proof. Admitted. (* STUB *)
  Lemma F6a_narrow : forall a b, narrow a b =
    if is_bot b then b else (R.narrow (fst a) (fst b), E.narrow (snd a) (snd b)).
  Proof. Admitted. (* STUB *)
  Lemma F7_rank : forall p r s,
    wrank p (r, s) = R.wrank (fst p) r + E.wrank (snd p) s.
  Proof. Admitted. (* STUB *)
  Lemma F8_size : forall r s, size (r, s) = R.size r + E.size s.
  Proof. reflexivity. Qed.
End RelEnvT.
