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

Module RelEnvClock (X : KEY_T) (L : LANG_T) (N : NUM_VIEW L) (V : VALUE_DOMAIN_T L)
    (F : LINEARIZE_T X L N) (R : NUM_STATE_T X L N F) (E : STATE_DOMAIN_T X L V)
    (RR : REL_RANGE_REFINE_T L N V)
    (P : LATTICE_T with Definition t := (R.t * E.t)%type)
    (PL : REL_PAIR_LINK X L N V F R E P).
  Include RelEnv X L N V F R E RR P PL.
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
End RelEnvClock.
