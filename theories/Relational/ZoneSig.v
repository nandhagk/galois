(** * Difference-bound matrices

    Zones bound differences of variables and a distinguished zero node.
    For example, an entry from zero to x bounds x from above.
    Builds on: MapSig, EnvSig and NumStateSig. *)

From Stdlib Require Import List ZArith.
From Argent Require Import Std.
From Galois.Base Require Import KeySig MapSig.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import LangSig ValueSig.
From Galois.States Require Import EnvSig.
From Galois.Relational Require Import LinearizeSig NumStateSig.

Local Open Scope nat_scope.

Module Type ZONE_OPS (X : KEY_OPS) (K : KEY_OPS with Definition t := option X.t)
    (M : MAP_OPS K) (L : LANG_OPS) (F : LINEARIZE_OPS X L).
  Definition dbm := M.t (M.t Z).
  Include NUM_STATE_OPS X L F with Definition t := reach dbm.
  Parameter entry : dbm -> K.t -> K.t -> option Z.
  Parameter fw_round : K.t -> dbm -> dbm.
  Parameter close : dbm -> t.
  Parameter add_cons : K.t -> K.t -> Z -> dbm -> dbm.
  Parameter incr_close : K.t -> K.t -> Z -> dbm -> t.
End ZONE_OPS.

Module Type ZONE_BASE (X : KEY) (K : KEY with Definition t := option X.t)
    (M : MAP K) (L : LANG) (N : NUM_VIEW L) (F : LINEARIZE X L N) :=
  ZONE_OPS X K M L F <+ LATTICE_LAWS <+ HAS_TOP_LAWS <+ WIDENING_LAWS <+
  NUM_STATE_LAWS X L N F.

Module Type ZONE_LAWS (X : KEY) (K : KEY with Definition t := option X.t)
    (M : MAP K) (L : LANG) (N : NUM_VIEW L) (F : LINEARIZE X L N)
    (Import D : ZONE_BASE X K M L N F).
  Definition vz (v : X.t -> Z) (i : K.t) : Z :=
    match i with None => 0%Z | Some x => v x end.
  Definition models (m : dbm) (v : X.t -> Z) : Prop :=
    forall i j d, entry m i j = Some d -> (vz v j - vz v i <= d)%Z.
  (** Matrix entries use row lookup followed by column lookup. *)
  Parameter entry_spec : forall m i j,
    entry m i j = match M.get i m with Some row => M.get j row | None => None end.
  (** Reached matrices denote exactly their difference constraints. *)
  Parameter ngamma_reached : forall m v, ngamma (Reached m) v <-> models m v.
  (** Unreachable matrices have no model. *)
  Parameter ngamma_unreached : forall v, ~ ngamma Unreached v.
End ZONE_LAWS.

Module Type ZONE (X : KEY) (K : KEY with Definition t := option X.t)
    (M : MAP K) (L : LANG) (N : NUM_VIEW L) (F : LINEARIZE X L N) :=
  ZONE_BASE X K M L N F <+ ZONE_LAWS X K M L N F.

Module Type ZONE_TIME (X : KEY_T) (K : KEY_T with Definition t := option X.t)
    (M : MAP_T K) (L : LANG_T) (N : NUM_VIEW L) (F : LINEARIZE_T X L N)
    (Import D : ZONE X K M L N F).
  Include NUM_STATE_TIME X L N F D.
  (* spec: supp b ell ns bs ells *)
  Parameter supp b ell : dbm -> nat.
  Parameter ns bs ells : t -> nat.
  Parameter T_entry : dbm -> K.t -> K.t -> nat.
  Parameter T_fw_round : K.t -> dbm -> nat.
  Parameter T_close : dbm -> nat.
  Parameter T_add_cons : K.t -> K.t -> Z -> dbm -> nat.
  Parameter T_incr_close : K.t -> K.t -> Z -> dbm -> nat.
  Parameter c_zone : nat.
  Definition binary_work (a z : t) : nat :=
    (ns a + ns z)^2 * (bs a + bs z + ells a + ells z + 1).
  (** Closure charges cubic updates and the logarithmic entry-growth allowance. *)
  Parameter T_close_le : forall m, T_close m <= c_zone * (supp m)^3 *
    (b m + ell m + Nat.log2 (supp m) + 1).
  (** Incremental closure charges quadratic updates. *)
  Parameter T_incr_close_le : forall i j d m, T_incr_close i j d m <=
    c_zone * (supp m)^2 * (b m + ell m + Z.size_nat d + 1).
  (** Join charges the combined matrix support and entry sizes. *)
  Parameter T_join_zone_le : forall a z, T_join a z <= c_zone * binary_work a z.
  (** Inclusion charges the combined matrix support and entry sizes. *)
  Parameter T_leb_zone_le : forall a z, T_leb a z <= c_zone * binary_work a z.
  (** Widening charges the combined matrix support and entry sizes. *)
  Parameter T_widen_zone_le : forall p a z, T_widen p a z <= c_zone * binary_work a z.
End ZONE_TIME.

Module Type ZONE_T (X : KEY_T) (K : KEY_T with Definition t := option X.t)
    (M : MAP_T K) (L : LANG_T) (N : NUM_VIEW L) (F : LINEARIZE_T X L N) :=
  ZONE X K M L N F <+ ZONE_TIME X K M L N F.

Module Type ZONE_PLAN (X : KEY_T) (K : KEY_T with Definition t := option X.t)
    (M : MAP_T K) (L : LANG_T) (N : NUM_VIEW L) (F : LINEARIZE_T X L N)
    (Import D : ZONE_T X K M L N F).
  (* spec: closed min_path_weight *)
  Parameter closed : dbm -> Prop.
  Parameter min_path_weight : dbm -> K.t -> K.t -> option Z.
  (** A Floyd-Warshall round adds only implied constraints. *)
  Parameter fw_round_implied : forall k m v, models m v -> models (fw_round k m) v.
  (** Closure retains all models of its input. *)
  Parameter close_sound : forall m v, models m v -> ngamma (close m) v.
  (** A negative diagonal certifies inconsistency. *)
  Parameter close_bot : forall m, close m = Unreached -> forall v, ~ models m v.
  (** Incremental closure retains models satisfying the added edge. *)
  Parameter incr_close_sound : forall i j d m v,
    models m v -> (vz v j - vz v i <= d)%Z -> ngamma (incr_close i j d m) v.
  (** Successful closure computes shortest path weights. *)
  Parameter close_shortest : forall m m', close m = Reached m' ->
    forall i j, entry m' i j = min_path_weight m i j.
  (** Incremental closure agrees with full closure on closed input. *)
  Parameter incr_close_eq : forall m i j d, closed m ->
    incr_close i j d m = close (add_cons i j d m).
  (** Early negative-diagonal exit limits finite entry growth. *)
  Parameter bits_close_le : forall m m', close m = Reached m' ->
    ell m' <= ell m + Nat.log2 (supp m) + 1.
End ZONE_PLAN.

Module Type ZONE_ALL (X : KEY_T) (K : KEY_T with Definition t := option X.t)
    (M : MAP_T K) (L : LANG_T) (N : NUM_VIEW L) (F : LINEARIZE_T X L N) :=
  ZONE_T X K M L N F <+ ZONE_PLAN X K M L N F.
