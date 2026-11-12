(** * Numeric state domains

    Numeric states describe integer views of concrete stores.
    For example, a zone can describe a bound on the difference of two variables.
    Builds on: LatticeSig, LinearizeSig and ValueSig. *)

From Stdlib Require Import List ZArith.
From Galois.Base Require Import KeySig.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import LangSig ValueSig.
From Galois.Relational Require Import LinearizeSig.

Module Type NUM_STATE_OPS (X : KEY_OPS) (L : LANG_OPS) (F : LINEARIZE_OPS X L).
  Include ALATTICE_OPS.
  Parameter assign : X.t -> term L.op X.t -> t -> t.
  Parameter havoc : X.t -> t -> t.
  Parameter assume : L.guard -> list (term L.op X.t) -> t -> t.
  Parameter range : term L.op X.t -> t -> bnd * bnd.
End NUM_STATE_OPS.

Module Type NUM_STATE_LAWS (X : KEY) (L : LANG) (N : NUM_VIEW L)
    (F : LINEARIZE X L N) (Import D : NUM_STATE_OPS X L F).
  (* spec: ngamma *)
  Parameter ngamma : t -> (X.t -> Z) -> Prop.
  (** Inclusion retains every numeric store. *)
  Parameter ngamma_mono : forall a b v, leb a b = true -> ngamma a v -> ngamma b v.
  (** Bottom describes no numeric store. *)
  Parameter ngamma_bot : forall v, ~ ngamma bot v.
  (** Top describes every numeric store. *)
  Parameter ngamma_top : forall v, ngamma top v.
  (** Assignment retains every successful concrete numeric update. *)
  Parameter assign_sound : forall x e s st c,
    ngamma s (fun y => N.num (st y)) -> eval_term L.eval st e = Some c ->
    ngamma (assign x e s) (fun y => N.num (upd X.eqb st x c y)).
  (** Havoc admits any concrete value for its variable. *)
  Parameter havoc_sound : forall x s st c, ngamma s (fun y => N.num (st y)) ->
    ngamma (havoc x s) (fun y => N.num (upd X.eqb st x c y)).
  (** Assuming a satisfied guard retains the numeric store. *)
  Parameter assume_sound : forall g es s st cs,
    ngamma s (fun y => N.num (st y)) -> eval_terms L.eval st es = Some cs ->
    L.holds g cs -> ngamma (assume g es s) (fun y => N.num (st y)).
  (** Queried ranges cover successful concrete results. *)
  Parameter range_sound : forall e s st c,
    ngamma s (fun y => N.num (st y)) -> eval_term L.eval st e = Some c ->
    in_bnd (fst (range e s)) (snd (range e s)) (N.num c).
End NUM_STATE_LAWS.

Module Type NUM_STATE (X : KEY) (L : LANG) (N : NUM_VIEW L) (F : LINEARIZE X L N) :=
  NUM_STATE_OPS X L F <+ LATTICE_LAWS <+ HAS_TOP_LAWS <+ WIDENING_LAWS <+
  NUM_STATE_LAWS X L N F.

Module Type NUM_STATE_TIME (X : KEY_T) (L : LANG_T) (N : NUM_VIEW L)
    (F : LINEARIZE_T X L N) (Import D : NUM_STATE X L N F).
  (* spec: size wsize transfer_work range_work *)
  Parameter size : t -> nat.
  Parameter wsize : wparam -> nat.
  Parameter transfer_work : t -> nat.
  Parameter range_work : term L.op X.t -> t -> nat.
  Parameter T_leb T_join T_narrow : t -> t -> N.
  Parameter T_is_bot : t -> N.
  Parameter T_widen : wparam -> t -> t -> N.
  Parameter T_assign : X.t -> term L.op X.t -> t -> N.
  Parameter T_havoc : X.t -> t -> N.
  Parameter T_assume : L.guard -> list (term L.op X.t) -> t -> N.
  Parameter T_range : term L.op X.t -> t -> N.
  Parameter c_num : N.
  (** Range queries charge their stated numeric work. *)
  Parameter T_range_le : forall e s, (T_range e s <= c_num * N.of_nat ((range_work e s + 1)%nat))%N.
End NUM_STATE_TIME.

Module Type NUM_STATE_T (X : KEY_T) (L : LANG_T) (N : NUM_VIEW L)
    (F : LINEARIZE_T X L N) := NUM_STATE X L N F <+ NUM_STATE_TIME X L N F.
