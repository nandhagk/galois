(** * Numeric state domains

    Numeric states describe integer views of concrete stores.
    For example, a zone can describe a bound on the difference of two variables.
    Builds on: LatticeSig, LinearizeSig and ValueSig. *)

From Stdlib Require Import List ZArith.
From Argent Require Import Std.
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
  Include LATTICE_TIME D.
  (* spec: wsize wunits assign_work havoc_work assume_work range_work range_bits *)
  Parameter wsize : wparam -> nat.
  Parameter wunits : t -> nat.
  Parameter assign_work : X.t -> term L.op X.t -> t -> nat.
  Parameter havoc_work : X.t -> t -> nat.
  Parameter assume_work : L.guard -> list (term L.op X.t) -> t -> nat.
  Parameter range_work : term L.op X.t -> t -> nat.
  Parameter range_bits : term L.op X.t -> t -> nat.
  Parameter T_narrow : t -> t -> N.
  Parameter T_widen : wparam -> t -> t -> N.
  Parameter T_assign : X.t -> term L.op X.t -> t -> N.
  Parameter T_havoc : X.t -> t -> N.
  Parameter T_assume : L.guard -> list (term L.op X.t) -> t -> N.
  Parameter T_range : term L.op X.t -> t -> N.
  Parameter c_num : N.
  (** Widening charges both states and its parameter. *)
  Parameter T_widen_le : forall p a b,
    (T_widen p a b <= c_lat * N.of_nat
      ((wunits a + wunits b) * wsize p + (size a + size b + wsize p + 1)))%N.
  (** Narrowing charges both states. *)
  Parameter T_narrow_le : forall a b,
    (T_narrow a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  (** Assignment charges its stated numeric work. *)
  Parameter T_assign_le : forall x e s,
    (T_assign x e s <= c_num * N.of_nat (assign_work x e s + 1))%N.
  (** Havoc charges its stated numeric work. *)
  Parameter T_havoc_le : forall x s,
    (T_havoc x s <= c_num * N.of_nat (havoc_work x s + 1))%N.
  (** Assumption charges its stated numeric work. *)
  Parameter T_assume_le : forall g es s,
    (T_assume g es s <= c_num * N.of_nat (assume_work g es s + 1))%N.
  (** Range queries charge their stated numeric work. *)
  Parameter T_range_le : forall e s,
    (T_range e s <= c_num * N.of_nat (range_work e s + 1))%N.
  (** The endpoints of a range fit the declared bits. *)
  Parameter range_size : forall e s,
    (N.of_nat
      (match fst (range e s) with Fin z => Z.size_nat z | _ => 0 end +
       match snd (range e s) with Fin z => Z.size_nat z | _ => 0 end) <=
     c_num * N.of_nat (range_bits e s + 1))%N.
End NUM_STATE_TIME.

Module Type NUM_STATE_T (X : KEY_T) (L : LANG_T) (N : NUM_VIEW L)
    (F : LINEARIZE_T X L N) := NUM_STATE X L N F <+ NUM_STATE_TIME X L N F.
