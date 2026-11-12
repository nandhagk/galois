(** * Integer octagons

    Octagons bound differences of signed variable literals.
    For example, a bound from minus x to plus x bounds twice x.
    Builds on: MapSig, EnvSig and NumStateSig. *)

From Stdlib Require Import List ZArith.
From Argent Require Import Std.
From Galois.Base Require Import KeySig MapSig.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import LangSig ValueSig.
From Galois.States Require Import EnvSig.
From Galois.Relational Require Import LinearizeSig NumStateSig.

Local Open Scope nat_scope.

Module Type OCTAGON_OPS (X : KEY_OPS)
    (K : KEY_OPS with Definition t := (X.t * bool)%type) (M : MAP_OPS K)
    (L : LANG_OPS) (F : LINEARIZE_OPS X L).
  Definition dbm := M.t (M.t Z).
  Include NUM_STATE_OPS X L F with Definition t := reach dbm.
  Parameter entry : dbm -> K.t -> K.t -> option Z.
  Parameter fw strengthen tighten close : dbm -> dbm.
  Parameter tclose : dbm -> t.
  Parameter add_cons : K.t -> K.t -> Z -> dbm -> dbm.
  Parameter incr_close : K.t -> K.t -> Z -> dbm -> t.
End OCTAGON_OPS.

Module Type OCTAGON_BASE (X : KEY) (K : KEY with Definition t := (X.t * bool)%type)
    (M : MAP K) (L : LANG) (N : NUM_VIEW L) (F : LINEARIZE X L N) :=
  OCTAGON_OPS X K M L F <+ LATTICE_LAWS <+ HAS_TOP_LAWS <+ WIDENING_LAWS <+
  NUM_STATE_LAWS X L N F.

Module Type OCTAGON_LAWS (X : KEY) (K : KEY with Definition t := (X.t * bool)%type)
    (M : MAP K) (L : LANG) (N : NUM_VIEW L) (F : LINEARIZE X L N)
    (Import D : OCTAGON_BASE X K M L N F).
  Definition bar (i : K.t) : K.t := (fst i, negb (snd i)).
  Definition vl (v : X.t -> Z) (i : K.t) : Z :=
    if snd i then v (fst i) else (- v (fst i))%Z.
  Definition models (m : dbm) (v : X.t -> Z) : Prop :=
    forall i j d, entry m i j = Some d -> (vl v j - vl v i <= d)%Z.
  (** Entries use the shared literal-key map twice. *)
  Parameter entry_spec : forall m i j,
    entry m i j = match M.get i m with Some row => M.get j row | None => None end.
  (** Reached octagons denote their signed difference constraints. *)
  Parameter ngamma_reached : forall m v, ngamma (Reached m) v <-> models m v.
  (** Unreachable octagons have no model. *)
  Parameter ngamma_unreached : forall v, ~ ngamma Unreached v.
End OCTAGON_LAWS.

Module Type OCTAGON (X : KEY) (K : KEY with Definition t := (X.t * bool)%type)
    (M : MAP K) (L : LANG) (N : NUM_VIEW L) (F : LINEARIZE X L N) :=
  OCTAGON_BASE X K M L N F <+ OCTAGON_LAWS X K M L N F.

Module Type OCTAGON_TIME (X : KEY_T) (K : KEY_T with Definition t := (X.t * bool)%type)
    (M : MAP_T K) (L : LANG_T) (N : NUM_VIEW L) (F : LINEARIZE_T X L N)
    (Import D : OCTAGON X K M L N F).
  Include NUM_STATE_TIME X L N F D.
  (* spec: supp b ell ns bs ells *)
  Parameter supp b ell : dbm -> nat.
  Parameter ns bs ells : t -> nat.
  Parameter T_entry : dbm -> K.t -> K.t -> nat.
  Parameter T_fw T_strengthen T_tighten T_close T_tclose : dbm -> nat.
  Parameter T_add_cons : K.t -> K.t -> Z -> dbm -> nat.
  Parameter T_incr_close : K.t -> K.t -> Z -> dbm -> nat.
  Parameter c_octagon : nat.
  Definition binary_work (a z : t) : nat :=
    (ns a + ns z)^2 * (bs a + bs z + ells a + ells z + 1).
  (** Tight closure charges cubic updates and logarithmic entry growth. *)
  Parameter T_tclose_le : forall m, T_tclose m <= c_octagon * (supp m)^3 *
    (b m + ell m + Nat.log2 (supp m) + 1).
  (** Incremental closure charges quadratic updates. *)
  Parameter T_incr_close_le : forall i j d m, T_incr_close i j d m <=
    c_octagon * (supp m)^2 * (b m + ell m + Z.size_nat d + 1).
  (** Join charges both input supports and entry sizes. *)
  Parameter T_join_octagon_le : forall a z, T_join a z <= c_octagon * binary_work a z.
  (** Inclusion charges both input supports and entry sizes. *)
  Parameter T_leb_octagon_le : forall a z, T_leb a z <= c_octagon * binary_work a z.
  (** Widening charges both input supports and entry sizes. *)
  Parameter T_widen_octagon_le : forall p a z, T_widen p a z <= c_octagon * binary_work a z.
End OCTAGON_TIME.

Module Type OCTAGON_T (X : KEY_T) (K : KEY_T with Definition t := (X.t * bool)%type)
    (M : MAP_T K) (L : LANG_T) (N : NUM_VIEW L) (F : LINEARIZE_T X L N) :=
  OCTAGON X K M L N F <+ OCTAGON_TIME X K M L N F.

Module Type OCTAGON_PLAN (X : KEY_T) (K : KEY_T with Definition t := (X.t * bool)%type)
    (M : MAP_T K) (L : LANG_T) (N : NUM_VIEW L) (F : LINEARIZE_T X L N)
    (Import D : OCTAGON_T X K M L N F).
  Definition coherent (m : dbm) : Prop :=
    forall i j, entry m i j = entry m (bar j) (bar i).
  (* spec: strongly_closed tightly_closed *)
  Parameter strongly_closed tightly_closed : dbm -> Prop.
  (** Floyd-Warshall adds only implied constraints. *)
  Parameter fw_implied : forall m v, models m v -> models (fw m) v.
  (** Strengthening adds only integer-implied constraints. *)
  Parameter strengthen_implied : forall m v, models m v -> models (strengthen m) v.
  (** Even rounding retains integer models. *)
  Parameter tighten_implied : forall m v, models m v -> models (tighten m) v.
  (** Tight closure retains all integer models. *)
  Parameter tclose_sound : forall m v, models m v -> ngamma (tclose m) v.
  (** A failed tight closure certifies inconsistency. *)
  Parameter tclose_bot : forall m, tclose m = Unreached -> forall v, ~ models m v.
  (** Incremental closure retains models satisfying its new bound. *)
  Parameter incr_close_sound : forall i j d m v,
    models m v -> (vl v j - vl v i <= d)%Z -> ngamma (incr_close i j d m) v.
  (** Full rational closure strengthens one Floyd-Warshall result. *)
  Parameter close_spec : forall m, close m = strengthen (fw m).
  (** Coherent rational closure is strongly closed. *)
  Parameter close_strong : forall m, coherent m -> strongly_closed (close m).
  (** Successful coherent integer closure is tightly closed. *)
  Parameter tclose_tight : forall m m', coherent m ->
    tclose m = Reached m' -> tightly_closed m'.
  (** Incremental closure agrees with tight closure on tightly closed input. *)
  Parameter incr_close_eq : forall m i j d, tightly_closed m ->
    incr_close i j d m = tclose (add_cons i j d m).
  (** Successful tight closure bounds finite entry growth. *)
  Parameter bits_tclose_le : forall m m', tclose m = Reached m' ->
    ell m' <= ell m + Nat.log2 (supp m) + 1.
End OCTAGON_PLAN.

Module Type OCTAGON_ALL (X : KEY_T) (K : KEY_T with Definition t := (X.t * bool)%type)
    (M : MAP_T K) (L : LANG_T) (N : NUM_VIEW L) (F : LINEARIZE_T X L N) :=
  OCTAGON_T X K M L N F <+ OCTAGON_PLAN X K M L N F.
