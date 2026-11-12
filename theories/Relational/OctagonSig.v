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
  Definition support (m : dbm) : list K.t :=
    fold_left (fun acc x => if existsb (K.eqb x) acc then acc else x :: acc)
      (map fst (M.elements m) ++
       flat_map (fun kv => map fst (M.elements (snd kv))) (M.elements m)) nil.
  Definition supp (m : dbm) : nat := length (support m).
  Definition b (m : dbm) : nat := fold_right Nat.max 0 (map K.bits (support m)).
  Definition ell (m : dbm) : nat := fold_right Nat.max 0
    (flat_map (fun kv => map (fun p => Z.size_nat (snd p))
      (M.elements (snd kv))) (M.elements m)).
  Definition ns (s : t) := match s with Unreached => 0 | Reached m => supp m end.
  Definition bs (s : t) := match s with Unreached => 0 | Reached m => b m end.
  Definition ells (s : t) := match s with Unreached => 0 | Reached m => ell m end.
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
  Definition strongly_closed (m : dbm) : Prop :=
    coherent m /\
    (forall i, In i (support m) -> entry m i i = Some 0%Z) /\
    (forall i j k a z, entry m i k = Some a -> entry m k j = Some z ->
      exists d, entry m i j = Some d /\ (d <= a + z)%Z) /\
    (forall i j a z, entry m i (bar i) = Some a -> entry m (bar j) j = Some z ->
      exists d, entry m i j = Some d /\ (2 * d <= a + z)%Z).
  Definition tightly_closed (m : dbm) : Prop := strongly_closed m /\
    (forall i d, entry m i (bar i) = Some d -> (d mod 2 = 0)%Z).
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
  (** Rational closure is strongly closed. *)
  Parameter close_strong : forall m, strongly_closed (close m).
  (** Successful integer closure is tightly closed. *)
  Parameter tclose_tight : forall m m',
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
