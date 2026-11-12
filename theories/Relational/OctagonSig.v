(** * Integer octagons

    Octagons bound differences of signed variable literals.
    For example, a bound from minus x to plus x bounds twice x.
    Builds on: MapSig, EnvSig and NumStateSig. *)

From Stdlib Require Import List ZArith.
From Argent Require Import Time Std.
From Galois.Base Require Import KeySig MapSig Code Key.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import LangSig ValueSig.
From Galois.States Require Import EnvSig.
From Galois.Relational Require Import LinForm LinearizeSig NumStateSig.

Local Open Scope nat_scope.

Module Type OCTAGON_OPS (X : KEY_OPS)
    (K : KEY_OPS with Definition t := (X.t * bool)%type
      with Definition encode := pair_code X.encode BoolKeyCode.encode) (M : MAP_OPS K)
    (L : LANG_OPS) (F : LINEARIZE_OPS X L).
  Definition dbm := M.t (M.t Z).
  Include NUM_STATE_OPS X L F with Definition t := reach dbm.
  Parameter entry : dbm -> K.t -> K.t -> option Z.
  Parameter fw strengthen tighten : dbm -> dbm.
  Parameter tclose : dbm -> t.
  Parameter add_cons : K.t -> K.t -> Z -> dbm -> dbm.
  Parameter incr_close : K.t -> K.t -> Z -> dbm -> t.
End OCTAGON_OPS.

Module Type OCTAGON_BASE (X : KEY) (K : KEY with Definition t := (X.t * bool)%type
      with Definition encode := pair_code X.encode BoolKeyCode.encode)
    (M : MAP K) (L : LANG) (N : NUM_VIEW L) (F : LINEARIZE X L N) :=
  OCTAGON_OPS X K M L F <+ LATTICE_LAWS <+ HAS_TOP_LAWS <+ WIDENING_LAWS <+
  NUM_STATE_LAWS X L N F.

Module Type OCTAGON_LAWS (X : KEY) (K : KEY with Definition t := (X.t * bool)%type
      with Definition encode := pair_code X.encode BoolKeyCode.encode)
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

Module Type OCTAGON (X : KEY) (K : KEY with Definition t := (X.t * bool)%type
      with Definition encode := pair_code X.encode BoolKeyCode.encode)
    (M : MAP K) (L : LANG) (N : NUM_VIEW L) (F : LINEARIZE X L N) :=
  OCTAGON_BASE X K M L N F <+ OCTAGON_LAWS X K M L N F.

Module Type OCTAGON_TIME (X : KEY_T) (K : KEY_T with Definition t := (X.t * bool)%type
      with Definition encode := pair_code X.encode BoolKeyCode.encode)
    (M : MAP_T K) (L : LANG_T) (N : NUM_VIEW L) (F : LINEARIZE_T X L N)
    (Import D : OCTAGON X K M L N F).
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
  Parameter T_fw T_strengthen T_tighten T_tclose : dbm -> N.
  Parameter T_add_cons : K.t -> K.t -> Z -> dbm -> N.
  Parameter T_incr_close : K.t -> K.t -> Z -> dbm -> N.
  Parameter c_octagon : N.
  Definition labs (s : t) : nat :=
    match s with Unreached => 0 | Reached m => M.weight m end.
  (** Entry lookup charges both keys. *)
  Parameter T_entry_le : forall m i j,
    (T_entry m i j <= c_octagon * N.of_nat (K.bits i + K.bits j + 1))%N.
  (** Inserting a constraint charges both key traversals and the bound. *)
  Parameter T_add_cons_le : forall i j d m,
    (T_add_cons i j d m <= c_octagon * N.of_nat
      (K.bits i + K.bits j + Z.size_nat d + 1))%N.
  (** Tight closure charges cubic updates and logarithmic entry growth. *)
  Parameter T_tclose_le : forall m, dbm_wf m ->
    (T_tclose m <= c_octagon * N.of_nat (((supp m + 1)^3)%nat) *
    N.of_nat ((b m + ell m + Nat.log2 (supp m) + 1)%nat))%N.
  (** Incremental closure charges quadratic updates and one row merge per row. *)
  Parameter T_incr_close_le : forall i j d m, (T_incr_close i j d m <=
    c_octagon * N.of_nat (((supp m + 1)^2)%nat) *
      N.of_nat ((b m + K.bits i + K.bits j + ell m + Z.size_nat d + 1)%nat) +
    c_octagon * N.of_nat (M.weight m))%N.
End OCTAGON_TIME.

Module Type OCTAGON_T (X : KEY_T) (K : KEY_T with Definition t := (X.t * bool)%type
      with Definition encode := pair_code X.encode BoolKeyCode.encode)
    (M : MAP_T K) (L : LANG_T) (N : NUM_VIEW L) (F : LINEARIZE_T X L N) :=
  OCTAGON X K M L N F <+ OCTAGON_TIME X K M L N F.

Module Type OCTAGON_PLAN (X : KEY_T) (K : KEY_T with Definition t := (X.t * bool)%type
      with Definition encode := pair_code X.encode BoolKeyCode.encode)
    (M : MAP_T K) (L : LANG_T) (N : NUM_VIEW L) (F : LINEARIZE_T X L N)
    (Import D : OCTAGON_T X K M L N F).
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
  Definition coherent (m : dbm) : Prop :=
    forall i j, entry m i j = entry m (bar j) (bar i).
  Definition coh (s : t) : Prop :=
    match s with Unreached => True | Reached m => coherent m end.
  Definition same_entries (a b : t) : Prop :=
    match a, b with
    | Reached ma, Reached mb => forall i j, entry ma i j = entry mb i j
    | Unreached, Unreached => True
    | _, _ => False
    end.
  Parameter fw_round : K.t -> dbm -> dbm.
  Parameter T_fw_round : K.t -> dbm -> N.
  Parameter k_octagon : N.
  (** The codes of a matrix cover its skeleton. *)
  Parameter skel_le : forall m, skel m <= (supp m + 1)^2 * (b m + 1).
  (** The row labels of a consistent matrix are keys of its support. *)
  Parameter weight_le : forall m, dbm_wf m -> M.weight m <= supp m * (b m + 1).
  (** Incremental closure adds four keys, bits and labels. *)
  Parameter grow_incr_close : forall i j d m m', incr_close i j d m = Reached m' ->
    supp m' <= supp m + 4 /\
    b m' <= Nat.max (b m) (Nat.max (K.bits i) (K.bits j) + 1) /\
    ell m' <= Nat.max (ell m) (Z.size_nat d) + 4 /\
    M.weight m' <= M.weight m + 4 * (Nat.max (K.bits i) (K.bits j) + 2).
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
        length (F.atoms_of g es) * labs s) +
      F.T_atoms_of g es)%N.
  (** Assignment work pays for linearization and quadratic matrix updates. *)
  Parameter F_assign_work : forall x e s,
    (N.of_nat (assign_work x e s) =
      N.of_nat ((ns s + 1)^2 *
        (bs s + ells s + X.bits x + F.bits_e e + lin_bits e + 1) + skels s + labs s +
        (tsize e + 1) * (bs s + ells s + F.bits_e e + Nat.log2 (tsize e) + 1)^2) + F.T_lin_of e)%N.
  (** Havoc visits the affected signed rows and columns. *)
  Parameter F_havoc_work : forall x s,
    havoc_work x s = (ns s + 1)^2 * (bs s + X.bits x + ells s + 1) + skels s.
  (** Top starts coherent. *)
  Parameter coh_top : coh top.
  (** Join keeps coherent matrices coherent. *)
  Parameter coh_join : forall a b, coh a -> coh b -> coh (join a b).
  (** Widening keeps coherent matrices coherent. *)
  Parameter coh_widen : forall p a b, coh a -> coh b -> coh (widen p a b).
  (** Assignment keeps coherence. *)
  Parameter coh_assign : forall x e s, coh s -> coh (assign x e s).
  (** Havoc keeps coherence. *)
  Parameter coh_havoc : forall x s, coh s -> coh (havoc x s).
  (** Assumption keeps coherence. *)
  Parameter coh_assume : forall g es s, coh s -> coh (assume g es s).
  (** Tight closure keeps coherence. *)
  Parameter coh_tclose : forall m, coherent m -> coh (tclose m).
  (** Incremental closure writes both twins and keeps coherence. *)
  Parameter coh_incr_close : forall i j d m, coherent m -> coh (incr_close i j d m).
  (** Constraint insertion writes both signed twins. *)
  Parameter F_add_cons_twins : forall i j d m,
    entry (add_cons i j d m) i j = entry (add_cons i j d m) (bar j) (bar i).
  (** Inserting both signed twins keeps a well-formed matrix well formed. *)
  Parameter wf_add_cons : forall i j d m, dbm_wf m -> dbm_wf (add_cons i j d m).
  (** Incremental closure keeps a well-formed matrix well formed. *)
  Parameter wf_incr_close : forall i j d m, dbm_wf m ->
    match incr_close i j d m with Unreached => True | Reached m' => dbm_wf m' end.
  (** A round keeps a well-formed matrix well formed. *)
  Parameter wf_fw_round : forall k m, dbm_wf m -> dbm_wf (fw_round k m).
  (** Floyd-Warshall charges cubic entry updates. *)
  Parameter T1_fw : forall m, dbm_wf m ->
    (T_fw m <= k_octagon * N.of_nat
      ((supp m + 1)^3 * (b m + ell m + Nat.log2 (supp m) + 1)))%N.
  (** Each round charges quadratic entry updates. *)
  Parameter T0_fw_round : forall k m, dbm_wf m ->
    (T_fw_round k m <= k_octagon * N.of_nat
      ((supp m + 1)^2 * (b m + K.bits k + ell m + 1)))%N.
  (** Even rounding adds at most one bit. *)
  Parameter bits_tighten_le : forall m, ell (tighten m) <= ell m + 1.
  (** Tightening charges quadratic entry updates. *)
  Parameter T2_tighten : forall m, dbm_wf m ->
    (T_tighten m <= k_octagon * N.of_nat ((supp m + 1)^2 * (b m + ell m + 1)))%N.
  (** Strengthening charges quadratic entry updates. *)
  Parameter T3_strengthen : forall m, dbm_wf m ->
    (T_strengthen m <= k_octagon * N.of_nat ((supp m + 1)^2 * (b m + ell m + 1)))%N.
  Definition strongly_closed (m : dbm) : Prop :=
    coherent m /\
    (forall i, In (K.encode i) (support m) -> entry m i i = Some 0%Z) /\
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
  (** Floyd-Warshall keeps consistent matrices consistent. *)
  Parameter wf_fw : forall m, dbm_wf m -> dbm_wf (fw m).
  (** Tightening keeps consistent matrices consistent. *)
  Parameter wf_tighten : forall m, dbm_wf m -> dbm_wf (tighten m).
  (** Strengthening keeps a well-formed matrix well formed. *)
  Parameter wf_strengthen : forall m, dbm_wf m -> dbm_wf (strengthen m).
  (** Tight closure retains all integer models. *)
  Parameter tclose_sound : forall m v, models m v -> ngamma (tclose m) v.
  (** A failed tight closure certifies inconsistency. *)
  Parameter tclose_bot : forall m, tclose m = Unreached -> forall v, ~ models m v.
  (** Incremental closure retains models satisfying its new bound. *)
  Parameter incr_close_sound : forall i j d m v,
    models m v -> (vl v j - vl v i <= d)%Z -> ngamma (incr_close i j d m) v.
  (** Successful integer closure is tightly closed. *)
  Parameter tclose_tight : forall m m', dbm_wf m -> coherent m ->
    tclose m = Reached m' -> tightly_closed m'.
  (** Incremental closure agrees with tight closure on tightly closed input. *)
  Parameter incr_close_eq : forall m i j d, dbm_wf m -> tightly_closed m ->
    same_entries (incr_close i j d m) (tclose (add_cons i j d m)).
  (** Successful tight closure bounds finite entry growth. *)
  Parameter bits_tclose_le : forall m m', tclose m = Reached m' ->
    ell m' <= ell m + Nat.log2 (supp m) + 1.
  (** State size charges all stored numeric data. *)
  Parameter F_size : forall s, size s = (ns s + 1)^2 * (bs s + ells s + 1) + skels s.
  (** Range work charges the numeric query and its linearization. *)
  Parameter F_range_work : forall e s, (N.of_nat (range_work e s) =
    N.of_nat ((tsize e + 1) *
      (bs s + ells s + F.bits_e e + Nat.log2 (tsize e) + 1)^2) + F.T_lin_of e)%N.
  (** A range endpoint is a sum of coefficient-entry products. *)
  Parameter F_range_bits : forall e s,
    range_bits e s = ells s + F.bits_e e + Nat.log2 (tsize e) + 2.
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
  (** A pivot key of a consistent matrix has its code in the support. *)
  Parameter keys_support : forall m k, dbm_wf m -> In k (keys m) ->
    In (K.encode k) (support m).
  (** One round adds at most one bit. *)
  Parameter bits_fw_round_step : forall k m, ell (fw_round k m) <= ell m + 1.
  (** Every traced round reads a matrix within the entry-growth bound. *)
  Parameter bits_fw_trace_le : forall ks m k a, dbm_wf m ->
    In (k, a) (fw_trace ks m) ->
    ell a <= ell m + Nat.log2 (supp m) + 1.
  (** Floyd-Warshall pays its pivots and performed rounds. *)
  Parameter T0_fw : forall m, dbm_wf m ->
    (T_fw m <= k_octagon * (N.of_nat ((supp m + 1)^2 * (b m + ell m + 1)) +
      fold_right N.add 0%N (map (fun km => T_fw_round (fst km) (snd km))
        (fw_trace (keys m) m))))%N.
  (** A round keeps the support and its key bits. *)
  Parameter supp_fw_round : forall k m,
    supp (fw_round k m) = supp m /\ b (fw_round k m) = b m.
  (** A consistent matrix has no more pivot keys than codes in its support. *)
  Parameter keys_le : forall m, dbm_wf m -> length (keys m) <= supp m.
  (** Floyd-Warshall runs the traced rounds over the pivot keys. *)
  Parameter F_fw : forall m, fw m =
    fold_left (fun a km => fw_round (fst km) a) (fw_trace (keys m) m) m.
  Definition diag_ok (m : dbm) : bool :=
    forallb (fun k => match entry m k k with Some d => (0 <=? d)%Z | None => true end) (keys m).
  TimeFun diag_ok.
  (** Tight closure tightens and strengthens only a consistent closed matrix. *)
  Parameter T4_tclose : forall m, dbm_wf m ->
    (T_tclose m <= T_fw m + k_octagon * N.of_nat ((supp m + 1)^2 * (b m + ell m + 1)) +
      if diag_ok (fw m) then T_tighten (fw m) + T_strengthen (tighten (fw m)) else 0)%N.
  (** Tightening and strengthening keep the support. *)
  Parameter supp_tighten_strengthen : forall m,
    supp (tighten m) = supp m /\ b (tighten m) = b m /\
    supp (strengthen m) = supp m /\ b (strengthen m) = b m.
End OCTAGON_PLAN.

Module Type OCTAGON_ALL (X : KEY_T) (K : KEY_T with Definition t := (X.t * bool)%type
      with Definition encode := pair_code X.encode BoolKeyCode.encode)
    (M : MAP_T K) (L : LANG_T) (N : NUM_VIEW L) (F : LINEARIZE_T X L N) :=
  OCTAGON_T X K M L N F <+ OCTAGON_PLAN X K M L N F.
