(** * Difference-bound matrices

    Zones bound differences of variables and a distinguished zero node.
    For example, an entry from zero to x bounds x from above.
    Builds on: MapSig, EnvSig and NumStateSig. *)

From Stdlib Require Import List ZArith.
From Argent Require Import Time Std.
From Galois.Base Require Import KeySig MapSig Code.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import LangSig ValueSig.
From Galois.States Require Import EnvSig.
From Galois.Relational Require Import LinForm LinearizeSig NumStateSig.

Local Open Scope nat_scope.

Module Type ZONE_OPS (X : KEY_OPS) (K : KEY_OPS with Definition t := option X.t
      with Definition encode := option_code X.encode)
    (M : MAP_OPS K) (L : LANG_OPS) (F : LINEARIZE_OPS X L).
  Definition dbm := M.t (M.t Z).
  Include NUM_STATE_OPS X L F with Definition t := reach dbm.
  Parameter entry : dbm -> K.t -> K.t -> option Z.
  Parameter fw_round : K.t -> dbm -> dbm.
  Parameter close : dbm -> t.
  Parameter add_cons : K.t -> K.t -> Z -> dbm -> dbm.
  Parameter incr_close : K.t -> K.t -> Z -> dbm -> t.
End ZONE_OPS.

Module Type ZONE_BASE (X : KEY) (K : KEY with Definition t := option X.t
      with Definition encode := option_code X.encode)
    (M : MAP K) (L : LANG) (N : NUM_VIEW L) (F : LINEARIZE X L N) :=
  ZONE_OPS X K M L F <+ LATTICE_LAWS <+ HAS_TOP_LAWS <+ WIDENING_LAWS <+
  NUM_STATE_LAWS X L N F.

Module Type ZONE_LAWS (X : KEY) (K : KEY with Definition t := option X.t
      with Definition encode := option_code X.encode)
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

Module Type ZONE (X : KEY) (K : KEY with Definition t := option X.t
      with Definition encode := option_code X.encode)
    (M : MAP K) (L : LANG) (N : NUM_VIEW L) (F : LINEARIZE X L N) :=
  ZONE_BASE X K M L N F <+ ZONE_LAWS X K M L N F.

Module Type ZONE_TIME (X : KEY_T) (K : KEY_T with Definition t := option X.t
      with Definition encode := option_code X.encode)
    (M : MAP_T K) (L : LANG_T) (N : NUM_VIEW L) (F : LINEARIZE_T X L N)
    (Import D : ZONE X K M L N F).
  Include NUM_STATE_TIME X L N F D.
  Definition rows (m : dbm) : list (M.t Z) :=
    flat_map (fun p => match M.find p m with Some r => r :: nil | None => nil end) (M.codes m).
  Definition support (m : dbm) : list positive :=
    fold_left (fun acc p => if existsb (Pos.eqb p) acc then acc else p :: acc)
      (M.codes m ++ flat_map M.codes (rows m)) nil.
  Definition supp (m : dbm) : nat := length (support m).
  Definition b (m : dbm) : nat := fold_right Nat.max 0 (map Pos.size_nat (support m)).
  Definition ell (m : dbm) : nat := fold_right Nat.max 0 (flat_map (fun r =>
    map (fun q => match M.find q r with Some z => Z.size_nat z | None => 0 end) (M.codes r))
    (rows m)).
  Definition skel (m : dbm) : nat := M.nodes m + fold_right Nat.add 0 (map M.nodes (rows m)).
  Definition skels (s : t) : nat := match s with Unreached => 0 | Reached m => skel m end.
  Definition keys (m : dbm) : list K.t :=
    fold_left (fun acc x => if existsb (K.eqb x) acc then acc else x :: acc)
      (map fst (M.elements m) ++
       flat_map (fun kv => map fst (M.elements (snd kv))) (M.elements m)) nil.
  TimeFun keys.
  Definition dbm_wf (m : dbm) : Prop :=
    M.wf m /\ forall p r, M.find p m = Some r -> M.wf r.
  Definition ns (s : t) := match s with Unreached => 0 | Reached m => supp m end.
  Definition bs (s : t) := match s with Unreached => 0 | Reached m => b m end.
  Definition ells (s : t) := match s with Unreached => 0 | Reached m => ell m end.
  Parameter T_entry : dbm -> K.t -> K.t -> N.
  Parameter T_fw_round : K.t -> dbm -> N.
  Parameter T_close : dbm -> N.
  Parameter T_add_cons : K.t -> K.t -> Z -> dbm -> N.
  Parameter T_incr_close : K.t -> K.t -> Z -> dbm -> N.
  Parameter c_zone : N.
  Definition binary_work (a z : t) : nat :=
    (ns a + ns z + 1)^2 * (bs a + bs z + ells a + ells z + 1) + skels a + skels z.
  (** Closure charges cubic updates and the logarithmic entry-growth allowance. *)
  Parameter T_close_le : forall m, dbm_wf m ->
    (T_close m <= c_zone * N.of_nat (((supp m + 1)^3)%nat) *
      N.of_nat ((b m + ell m + Nat.log2 (supp m) + 1)%nat))%N.
  (** Incremental closure charges quadratic updates and one row merge per row. *)
  Parameter T_incr_close_le : forall i j d m, (T_incr_close i j d m <=
    c_zone * N.of_nat (((supp m + 1)^2)%nat) *
      N.of_nat ((b m + K.bits i + K.bits j + ell m + Z.size_nat d + 1)%nat) +
    c_zone * N.of_nat ((supp m + 1) * skel m))%N.
  (** Join charges the combined matrix support and entry sizes. *)
  Parameter T_join_zone_le : forall a z, (T_join a z <= c_zone * N.of_nat (binary_work a z))%N.
  (** Inclusion charges the combined matrix support and entry sizes. *)
  Parameter T_leb_zone_le : forall a z, (T_leb a z <= c_zone * N.of_nat ((binary_work a z)%nat))%N.
  (** Widening charges the combined matrix support and entry sizes. *)
  Parameter T_widen_zone_le : forall p a z,
    (T_widen p a z <= c_zone * N.of_nat (binary_work a z + (ns a + ns z + 1)^2 * wsize p))%N.
End ZONE_TIME.

Module Type ZONE_T (X : KEY_T) (K : KEY_T with Definition t := option X.t
      with Definition encode := option_code X.encode)
    (M : MAP_T K) (L : LANG_T) (N : NUM_VIEW L) (F : LINEARIZE_T X L N) :=
  ZONE X K M L N F <+ ZONE_TIME X K M L N F.

Module Type ZONE_PLAN (X : KEY_T) (K : KEY_T with Definition t := option X.t
      with Definition encode := option_code X.encode)
    (M : MAP_T K) (L : LANG_T) (N : NUM_VIEW L) (F : LINEARIZE_T X L N)
    (Import D : ZONE_T X K M L N F).
  Definition closed (m : dbm) : Prop :=
    (forall i, In (K.encode i) (support m) -> entry m i i = Some 0%Z) /\
    (forall i j k a z, entry m i k = Some a -> entry m k j = Some z ->
      exists d, entry m i j = Some d /\ (d <= a + z)%Z).
  Fixpoint chain_weight (m : dbm) (i : K.t) (ks : list K.t) (j : K.t) : option Z :=
    match ks with
    | nil => entry m i j
    | k :: ks =>
      match entry m i k, chain_weight m k ks j with
      | Some a, Some z => Some (a + z)%Z
      | _, _ => None
      end
    end.
  Definition same_entries (a b : t) : Prop :=
    match a, b with
    | Reached ma, Reached mb => forall i j, entry ma i j = entry mb i j
    | Unreached, Unreached => True
    | _, _ => False
    end.
  Parameter k_zone : N.
  Parameter F_swf : forall s,
    swf s <-> match s with Unreached => True | Reached m => dbm_wf m end.
  (** Linear-form size charges coefficients, the constant and wrap bounds. *)
  Definition lin_bits (e : term L.op X.t) : nat :=
    match F.lin_of e with
    | Some (f, r) =>
      fold_right Nat.max (Z.size_nat (cst f))
        (map (fun p => Z.size_nat (snd p)) (coef f)) +
      match r with NoWrap => 0 | WrapTo lo hi => Z.size_nat lo + Z.size_nat hi end
    | None => 0
    end.
  (** Widening units cover the squared support size. *)
  Parameter F_wunits : forall s, wunits s = (ns s + 1) ^ 2.
  (** Assumption work charges incremental closure for every emitted atom. *)
  Parameter F_assume_work : forall g es s,
    (N.of_nat (assume_work g es s) =
      N.of_nat (length (F.atoms_of g es) *
        (ns s + 2 * length (F.atoms_of g es) + 1)^2 *
        (bs s + ells s + F.bits_es g es + 2 * length (F.atoms_of g es) + 1) +
        length (F.atoms_of g es) *
          (ns s + 2 * length (F.atoms_of g es) + 1) * skels s) +
      F.T_atoms_of g es)%N.
  (** Assignment work pays for linearization and quadratic matrix updates. *)
  Parameter F_assign_work : forall x e s,
    (N.of_nat (assign_work x e s) =
      N.of_nat ((ns s + 1)^2 *
        (bs s + ells s + X.bits x + F.bits_e e + lin_bits e + 1) + skels s) + F.T_lin_of e)%N.
  (** Havoc visits the affected row and column. *)
  Parameter F_havoc_work : forall x s,
    havoc_work x s = (ns s + 1)^2 * (bs s + X.bits x + ells s + 1) + skels s.
  (** Join takes entrywise maxima without closing its arguments. *)
  Parameter F_join_entry : forall ma mb i j,
    match join (Reached ma) (Reached mb) with
    | Reached mj => entry mj i j =
        match entry ma i j, entry mb i j with
        | Some x, Some y => Some (Z.max x y)
        | _, _ => None
        end
    | Unreached => False
    end.
  (** A Floyd-Warshall round adds only implied constraints. *)
  Parameter fw_round_implied : forall k m v, models m v -> models (fw_round k m) v.
  (** A round keeps consistent matrices consistent. *)
  Parameter wf_fw_round : forall k m, dbm_wf m -> dbm_wf (fw_round k m).
  (** Inserting a constraint keeps a well-formed matrix well formed. *)
  Parameter wf_add_cons : forall i j d m, dbm_wf m -> dbm_wf (add_cons i j d m).
  (** Incremental closure keeps a well-formed matrix well formed. *)
  Parameter wf_incr_close : forall i j d m, dbm_wf m ->
    match incr_close i j d m with Unreached => True | Reached m' => dbm_wf m' end.
  (** Closure retains all models of its input. *)
  Parameter close_sound : forall m v, models m v -> ngamma (close m) v.
  (** A negative diagonal certifies inconsistency. *)
  Parameter close_bot : forall m, close m = Unreached -> forall v, ~ models m v.
  (** Incremental closure retains models satisfying the added edge. *)
  Parameter incr_close_sound : forall i j d m v,
    models m v -> (vz v j - vz v i <= d)%Z -> ngamma (incr_close i j d m) v.
  (** Successful closure computes shortest path weights. *)
  Parameter close_shortest : forall m m' i j, dbm_wf m -> close m = Reached m' -> i <> j ->
    (forall d, entry m' i j = Some d -> exists ks, chain_weight m i ks j = Some d) /\
    (forall ks d, chain_weight m i ks j = Some d ->
       exists d', entry m' i j = Some d' /\ (d' <= d)%Z).
  (** Incremental closure agrees with full closure on closed input. *)
  Parameter incr_close_eq : forall m i j d, dbm_wf m -> closed m ->
    same_entries (incr_close i j d m) (close (add_cons i j d m)).
  (** Nonnegative diagonal checks limit intermediate Floyd-Warshall entry growth. *)
  Parameter bits_fw_round_le : forall ks m,
    (forall k, In k ks -> forall d,
      entry (fold_left (fun a k => fw_round k a) ks m) k k = Some d -> (0 <= d)%Z) ->
    ell (fold_left (fun a k => fw_round k a) ks m) <= ell m + Nat.log2 (supp m) + 1.
  (** Each Floyd-Warshall round charges quadratic entry updates. *)
  Parameter T1_fw_round : forall k m, dbm_wf m ->
    (T_fw_round k m <= k_zone * N.of_nat
      ((supp m + 1)^2 * (b m + K.bits k + ell m + 1)))%N.
  (** Early negative-diagonal exit limits finite entry growth. *)
  Parameter bits_close_le : forall m m', close m = Reached m' ->
    ell m' <= ell m + Nat.log2 (supp m) + 1.
  (** State size charges all stored numeric data. *)
  Parameter F_size : forall s, size s = (ns s + 1)^2 * (bs s + ells s + 1) + skels s.
  (** Range work charges the numeric query and its linearization. *)
  Parameter F_range_work : forall e s, (N.of_nat (range_work e s) =
    N.of_nat ((tsize e + 1) * (bs s + ells s + F.bits_e e + 1)^2) + F.T_lin_of e)%N.
  Fixpoint fw_trace (ks : list K.t) (m : dbm) : list (K.t * dbm) :=
    match ks with
    | nil => nil
    | k :: ks =>
      let m' := fw_round k m in
      (k, m) ::
        match entry m' k k with
        | Some d => if (d <? 0)%Z then nil else fw_trace ks m'
        | None => fw_trace ks m'
        end
    end.
  TimeFun fw_trace.
  (** A round keeps the support and its key bits. *)
  Parameter supp_fw_round : forall k m,
    supp (fw_round k m) = supp m /\ b (fw_round k m) = b m.
  (** A consistent matrix has no more pivot keys than codes in its support. *)
  Parameter keys_le : forall m, dbm_wf m -> length (keys m) <= supp m.
  (** Closure pays its pivot list, the performed rounds and the final diagonal. *)
  Parameter T2_close : forall m, dbm_wf m ->
    (T_close m <= k_zone * (N.of_nat ((supp m + 1)^2 * (b m + ell m + 1)) +
      fold_right N.add 0%N (map (fun km => T_fw_round (fst km) (snd km))
        (fw_trace (keys m) m))))%N.
End ZONE_PLAN.

Module Type ZONE_ALL (X : KEY_T) (K : KEY_T with Definition t := option X.t
      with Definition encode := option_code X.encode)
    (M : MAP_T K) (L : LANG_T) (N : NUM_VIEW L) (F : LINEARIZE_T X L N) :=
  ZONE_T X K M L N F <+ ZONE_PLAN X K M L N F.
