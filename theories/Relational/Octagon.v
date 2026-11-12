(** * Octagon placeholders

    These modules provide the octagon state interface.
    For example, closure returns an unreachable placeholder state.
    Builds on: OctagonSig. *)
From Stdlib Require Import List ZArith.
From Argent Require Import Time Std.
From Galois.Base Require Import KeySig MapSig Code Key.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import LangSig ValueSig.
From Galois.States Require Import EnvSig.
From Galois.Relational Require Import LinForm LinearizeSig NumStateSig OctagonSig.
Local Open Scope nat_scope.

Module OctagonCode (X : KEY_OPS) (K : KEY_OPS with Definition t := (X.t * bool)%type
      with Definition encode := pair_code X.encode BoolKeyCode.encode)
    (M : MAP_OPS K) (L : LANG_OPS) (F : LINEARIZE_OPS X L) <: OCTAGON_OPS X K M L F.
  Definition dbm := M.t (M.t Z).
  Definition t := reach dbm.
  Definition wparam := nat.
  (* STUB-CODE *)
  Definition leb (_ _ : t) := false.
  (* STUB-CODE *)
  Definition bot : t := Unreached.
  (* STUB-CODE *)
  Definition is_bot (_ : t) := false.
  (* STUB-CODE *)
  Definition join (_ _ : t) : t := Unreached.
  (* STUB-CODE *)
  Definition top : t := Reached M.empty.
  (* STUB-CODE *)
  Definition meet (_ _ : t) : t := Unreached.
  (* STUB-CODE *)
  Definition widen (_ : wparam) (_ _ : t) : t := Unreached.
  (* STUB-CODE *)
  Definition narrow (_ _ : t) : t := Unreached.
  (* STUB-CODE *)
  Definition assign (_ : X.t) (_ : term L.op X.t) (_ : t) : t := Unreached.
  (* STUB-CODE *)
  Definition havoc (_ : X.t) (_ : t) : t := Unreached.
  (* STUB-CODE *)
  Definition assume (_ : L.guard) (_ : list (term L.op X.t)) (_ : t) : t := Unreached.
  (* STUB-CODE *)
  Definition range (_ : term L.op X.t) (_ : t) : bnd * bnd := (NegInf, PosInf).
  (* STUB-CODE *)
  Definition entry (_ : dbm) (_ _ : K.t) : option Z := None.
  (* STUB-CODE *)
  Definition fw (m : dbm) : dbm := m.
  (* STUB-CODE *)
  Definition strengthen (m : dbm) : dbm := m.
  (* STUB-CODE *)
  Definition tighten (m : dbm) : dbm := m.
  (* STUB-CODE *)
  Definition tclose (_ : dbm) : t := Unreached.
  (* STUB-CODE *)
  Definition add_cons (_ _ : K.t) (_ : Z) (m : dbm) : dbm := m.
  (* STUB-CODE *)
  Definition incr_close (_ _ : K.t) (_ : Z) (_ : dbm) : t := Unreached.
End OctagonCode.

Module Octagon (X : KEY) (K : KEY with Definition t := (X.t * bool)%type
      with Definition encode := pair_code X.encode BoolKeyCode.encode)
    (M : MAP K) (L : LANG) (N : NUM_VIEW L) (F : LINEARIZE X L N) <: OCTAGON X K M L N F.
  Include OctagonCode X K M L F.
  (* STUB-CODE *)
  Definition wrank (_ : wparam) (s : t) : nat :=
    match s with
    | Unreached => 0
    | Reached m => fold_right Nat.add 0 (map (fun p =>
        match M.find p m with Some row => length (M.codes row) | None => 0 end) (M.codes m))
    end.
  Definition bar (i : K.t) : K.t := (fst i, negb (snd i)).
  Definition vl (v : X.t -> Z) (i : K.t) : Z :=
    if snd i then v (fst i) else (- v (fst i))%Z.
  Definition models (m : dbm) (v : X.t -> Z) : Prop :=
    forall i j d, entry m i j = Some d -> (vl v j - vl v i <= d)%Z.
  Definition ngamma (s : t) (v : X.t -> Z) : Prop :=
    match s with Unreached => False | Reached m => models m v end.
  Lemma leb_refl  : forall a, leb a a = true.
  Proof. Admitted. (* STUB *)
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof. Admitted. (* STUB *)
  Lemma bot_least : forall a, leb bot a = true.
  Proof. Admitted. (* STUB *)
  Lemma is_bot_bot : is_bot bot = true.
  Proof. Admitted. (* STUB *)
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof. Admitted. (* STUB *)
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof. Admitted. (* STUB *)
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof. Admitted. (* STUB *)
  Lemma top_greatest : forall a, leb a top = true.
  Proof. Admitted. (* STUB *)
  Lemma widen_ub_l : forall p a b, leb a (widen p a b) = true.
  Proof. Admitted. (* STUB *)
  Lemma widen_ub_r : forall p a b, leb b (widen p a b) = true.
  Proof. Admitted. (* STUB *)
  Lemma widen_stable : forall p a b, leb b a = true -> widen p a b = a.
  Proof. Admitted. (* STUB *)
  Lemma wrank_widen : forall p a b, is_bot a = false -> leb b a = false ->
    wrank p (widen p a b) < wrank p a.
  Proof. Admitted. (* STUB *)
  Lemma wrank_widen_le : forall p a b, is_bot a = false -> wrank p (widen p a b) <= wrank p a.
  Proof. Admitted. (* STUB *)
  Lemma narrow_between : forall a b, leb b a = true ->
    leb b (narrow a b) = true /\ leb (narrow a b) a = true.
  Proof. Admitted. (* STUB *)
  Lemma ngamma_mono : forall a b v, leb a b = true -> ngamma a v -> ngamma b v.
  Proof. Admitted. (* STUB *)
  Lemma ngamma_bot : forall v, ~ ngamma bot v.
  Proof. Admitted. (* STUB *)
  Lemma ngamma_top : forall v, ngamma top v.
  Proof. Admitted. (* STUB *)
  Lemma assign_sound : forall x e s st c,
    ngamma s (fun y => N.num (st y)) -> eval_term L.eval st e = Some c ->
    ngamma (assign x e s) (fun y => N.num (upd X.eqb st x c y)).
  Proof. Admitted. (* STUB *)
  Lemma havoc_sound : forall x s st c, ngamma s (fun y => N.num (st y)) ->
    ngamma (havoc x s) (fun y => N.num (upd X.eqb st x c y)).
  Proof. Admitted. (* STUB *)
  Lemma assume_sound : forall g es s st cs,
    ngamma s (fun y => N.num (st y)) -> eval_terms L.eval st es = Some cs ->
    L.holds g cs -> ngamma (assume g es s) (fun y => N.num (st y)).
  Proof. Admitted. (* STUB *)
  Lemma range_sound : forall e s st c,
    ngamma s (fun y => N.num (st y)) -> eval_term L.eval st e = Some c ->
    in_bnd (fst (range e s)) (snd (range e s)) (N.num c).
  Proof. Admitted. (* STUB *)
  Lemma entry_spec : forall m i j,
    entry m i j = match M.get i m with Some row => M.get j row | None => None end.
  Proof. Admitted. (* STUB *)
  Lemma ngamma_reached : forall m v, ngamma (Reached m) v <-> models m v.
  Proof. Admitted. (* STUB *)
  Lemma ngamma_unreached : forall v, ~ ngamma Unreached v.
  Proof. Admitted. (* STUB *)
End Octagon.

Module OctagonT (X : KEY_T) (K : KEY_T with Definition t := (X.t * bool)%type
      with Definition encode := pair_code X.encode BoolKeyCode.encode)
    (M : MAP_T K) (L : LANG_T) (N : NUM_VIEW L) (F : LINEARIZE_T X L N)
    <: OCTAGON_ALL X K M L N F.
  Include Octagon X K M L N F.
  Definition wsize (_ : wparam) : nat := 0.
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
  Definition swf (s : t) : Prop :=
    match s with Unreached => True | Reached m => dbm_wf m end.
  Definition ns (s : t) := match s with Unreached => 0 | Reached m => supp m end.
  Definition bs (s : t) := match s with Unreached => 0 | Reached m => b m end.
  Definition ells (s : t) := match s with Unreached => 0 | Reached m => ell m end.
  Definition size (s : t) : nat :=
    (ns s + 1)^2 * (bs s + ells s + 1) + skels s.
  Definition lin_bits (e : term L.op X.t) : nat :=
    match F.lin_of e with
    | Some (f, r) =>
      fold_right Nat.max (Z.size_nat (cst f))
        (map (fun p => Z.size_nat (snd p)) (coef f)) +
      match r with NoWrap => 0 | WrapTo lo hi => Z.size_nat lo + Z.size_nat hi end
    | None => 0
    end.
  Definition wunits (s : t) : nat := (ns s + 1) ^ 2.
  Definition assign_work (x : X.t) (e : term L.op X.t) (s : t) : nat :=
    (ns s + 1)^2 * (bs s + ells s + X.bits x + F.bits_e e + lin_bits e + 1) + skels s +
      N.to_nat (F.T_lin_of e).
  Definition havoc_work (x : X.t) (s : t) : nat :=
    (ns s + 1)^2 * (bs s + X.bits x + ells s + 1) + skels s.
  Definition assume_work (g : L.guard) (es : list (term L.op X.t)) (s : t) : nat :=
    length (F.atoms_of g es) * (ns s + 2 * length (F.atoms_of g es) + 1)^2 *
      (bs s + ells s + F.bits_es g es + 2 * length (F.atoms_of g es) + 1) +
      length (F.atoms_of g es) *
        (ns s + 2 * length (F.atoms_of g es) + 1) * skels s +
      N.to_nat (F.T_atoms_of g es).
  Definition range_work (e : term L.op X.t) (s : t) : nat :=
    (tsize e + 1) * (bs s + ells s + F.bits_e e + 1)^2 + N.to_nat (F.T_lin_of e).
  TimeFun bot.
  TimeFun top.
  TimeFun meet.
  TimeFun leb.
  TimeFun join.
  TimeFun is_bot.
  TimeFun widen.
  TimeFun narrow.
  TimeFun assign.
  TimeFun havoc.
  TimeFun assume.
  TimeFun range.
  TimeFun entry.
  TimeFun fw.
  TimeFun strengthen.
  TimeFun tighten.
  TimeFun tclose.
  TimeFun add_cons.
  TimeFun incr_close.
  Definition c_num : N := 1. (* STUB *)
  Lemma swf_top : swf top.
  Proof. Admitted. (* STUB *)
  Lemma swf_join : forall a b, swf a -> swf b -> swf (join a b).
  Proof. Admitted. (* STUB *)
  Lemma swf_widen : forall p a b, swf a -> swf b -> swf (widen p a b).
  Proof. Admitted. (* STUB *)
  Lemma swf_narrow : forall a b, swf a -> swf b -> swf (narrow a b).
  Proof. Admitted. (* STUB *)
  Lemma swf_assign : forall x e s, swf s -> swf (assign x e s).
  Proof. Admitted. (* STUB *)
  Lemma swf_havoc : forall x s, swf s -> swf (havoc x s).
  Proof. Admitted. (* STUB *)
  Lemma swf_assume : forall g es s, swf s -> swf (assume g es s).
  Proof. Admitted. (* STUB *)
  Lemma T_assign_le : forall x e s,
    (T_assign x e s <= c_num * N.of_nat (assign_work x e s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_havoc_le : forall x s,
    (T_havoc x s <= c_num * N.of_nat (havoc_work x s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_assume_le : forall g es s, swf s ->
    (T_assume g es s <= c_num * N.of_nat (assume_work g es s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_is_bot_le : forall s,
    (T_is_bot s <= c_num * N.of_nat (size s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_narrow_le : forall a b,
    (T_narrow a b <= c_num * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_range_le : forall e s, (T_range e s <= c_num * N.of_nat ((range_work e s + 1)%nat))%N.
  Proof. Admitted. (* STUB *)
  Definition c_octagon : N := 1. (* STUB *)
  Lemma T_add_cons_le : forall i j d m,
    (T_add_cons i j d m <= c_octagon * N.of_nat
      (K.bits i + K.bits j + Z.size_nat d + 1))%N.
  Proof. Admitted. (* STUB *)
  Definition binary_work (a z : t) : nat :=
    (ns a + ns z + 1)^2 * (bs a + bs z + ells a + ells z + 1) + skels a + skels z.
  Lemma T_tclose_le : forall m, dbm_wf m ->
    (T_tclose m <= c_octagon * N.of_nat (((supp m + 1)^3)%nat) *
    N.of_nat ((b m + ell m + Nat.log2 (supp m) + 1)%nat))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_incr_close_le : forall i j d m, (T_incr_close i j d m <=
    c_octagon * N.of_nat (((supp m + 1)^2)%nat) *
      N.of_nat ((b m + K.bits i + K.bits j + ell m + Z.size_nat d + 1)%nat) +
    c_octagon * N.of_nat ((supp m + 1) * skel m))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_join_octagon_le : forall a z,
    (T_join a z <= c_octagon * N.of_nat (binary_work a z))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_leb_octagon_le : forall a z,
    (T_leb a z <= c_octagon * N.of_nat (binary_work a z))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_widen_octagon_le : forall p a z,
    (T_widen p a z <= c_octagon * N.of_nat (binary_work a z + (ns a + ns z + 1)^2 * wsize p))%N.
  Proof. Admitted. (* STUB *)
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
  (* STUB-CODE *)
  Definition fw_round (_ : K.t) (m : dbm) : dbm := m.
  TimeFun fw_round.
  Definition k_octagon : N := 1. (* STUB *)
  Lemma F_swf : forall s,
    swf s <-> match s with Unreached => True | Reached m => dbm_wf m end.
  Proof. Admitted. (* STUB *)
  (** Assignment work pays for linearization and quadratic matrix updates. *)
  (** Widening units cover the squared support size. *)
  Lemma F_wunits : forall s, wunits s = (ns s + 1) ^ 2.
  Proof. Admitted. (* STUB *)
  (** Assumption work charges incremental closure for every emitted atom. *)
  Lemma F_assume_work : forall g es s,
    (N.of_nat (assume_work g es s) =
      N.of_nat (length (F.atoms_of g es) *
        (ns s + 2 * length (F.atoms_of g es) + 1)^2 *
        (bs s + ells s + F.bits_es g es + 2 * length (F.atoms_of g es) + 1) +
        length (F.atoms_of g es) *
          (ns s + 2 * length (F.atoms_of g es) + 1) * skels s) +
      F.T_atoms_of g es)%N.
  Proof. Admitted. (* STUB *)
  (** Assignment work pays for linearization and quadratic matrix updates. *)
  Lemma F_assign_work : forall x e s,
    (N.of_nat (assign_work x e s) =
      N.of_nat ((ns s + 1)^2 *
        (bs s + ells s + X.bits x + F.bits_e e + lin_bits e + 1) + skels s) + F.T_lin_of e)%N.
  Proof. Admitted. (* STUB *)
  Lemma F_havoc_work : forall x s,
    havoc_work x s = (ns s + 1)^2 * (bs s + X.bits x + ells s + 1) + skels s.
  Proof. Admitted. (* STUB *)
  Lemma coh_top : coh top.
  Proof. Admitted. (* STUB *)
  Lemma coh_join : forall a b, coh a -> coh b -> coh (join a b).
  Proof. Admitted. (* STUB *)
  Lemma coh_widen : forall p a b, coh a -> coh b -> coh (widen p a b).
  Proof. Admitted. (* STUB *)
  Lemma coh_assign : forall x e s, coh s -> coh (assign x e s).
  Proof. Admitted. (* STUB *)
  Lemma coh_havoc : forall x s, coh s -> coh (havoc x s).
  Proof. Admitted. (* STUB *)
  Lemma coh_assume : forall g es s, coh s -> coh (assume g es s).
  Proof. Admitted. (* STUB *)
  Lemma coh_tclose : forall m, coherent m -> coh (tclose m).
  Proof. Admitted. (* STUB *)
  Lemma coh_incr_close : forall i j d m, coherent m -> coh (incr_close i j d m).
  Proof. Admitted. (* STUB *)
  Lemma F_add_cons_twins : forall i j d m,
    entry (add_cons i j d m) i j = entry (add_cons i j d m) (bar j) (bar i).
  Proof. Admitted. (* STUB *)
  Lemma wf_add_cons : forall i j d m, dbm_wf m -> dbm_wf (add_cons i j d m).
  Proof. Admitted. (* STUB *)
  Lemma wf_incr_close : forall i j d m, dbm_wf m ->
    match incr_close i j d m with Unreached => True | Reached m' => dbm_wf m' end.
  Proof. Admitted. (* STUB *)
  Lemma wf_fw_round : forall k m, dbm_wf m -> dbm_wf (fw_round k m).
  Proof. Admitted. (* STUB *)
  Lemma T1_fw : forall m, dbm_wf m ->
    (T_fw m <= k_octagon * N.of_nat
      ((supp m + 1)^3 * (b m + ell m + Nat.log2 (supp m) + 1)))%N.
  Proof. Admitted. (* STUB *)
  Lemma T2_tighten : forall m, dbm_wf m ->
    (T_tighten m <= k_octagon * N.of_nat ((supp m + 1)^2 * (b m + ell m + 1)))%N.
  Proof. Admitted. (* STUB *)
  Lemma T3_strengthen : forall m, dbm_wf m ->
    (T_strengthen m <= k_octagon * N.of_nat ((supp m + 1)^2 * (b m + ell m + 1)))%N.
  Proof. Admitted. (* STUB *)
  Lemma bits_fw_round_le : forall ks m,
    (forall k, In k ks -> forall d,
      entry (fold_left (fun a k => fw_round k a) ks m) k k = Some d -> (0 <= d)%Z) ->
    ell (fold_left (fun a k => fw_round k a) ks m) <= ell m + Nat.log2 (supp m) + 1.
  Proof. Admitted. (* STUB *)
  Definition strongly_closed (m : dbm) : Prop :=
    coherent m /\
    (forall i, In (K.encode i) (support m) -> entry m i i = Some 0%Z) /\
    (forall i j k a z, entry m i k = Some a -> entry m k j = Some z ->
      exists d, entry m i j = Some d /\ (d <= a + z)%Z) /\
    (forall i j a z, entry m i (bar i) = Some a -> entry m (bar j) j = Some z ->
      exists d, entry m i j = Some d /\ (2 * d <= a + z)%Z).
  Definition tightly_closed (m : dbm) : Prop := strongly_closed m /\
    (forall i d, entry m i (bar i) = Some d -> (d mod 2 = 0)%Z).
  Lemma fw_implied : forall m v, models m v -> models (fw m) v.
  Proof. Admitted. (* STUB *)
  Lemma strengthen_implied : forall m v, models m v -> models (strengthen m) v.
  Proof. Admitted. (* STUB *)
  Lemma tighten_implied : forall m v, models m v -> models (tighten m) v.
  Proof. Admitted. (* STUB *)
  Lemma wf_fw : forall m, dbm_wf m -> dbm_wf (fw m).
  Proof. Admitted. (* STUB *)
  Lemma wf_tighten : forall m, dbm_wf m -> dbm_wf (tighten m).
  Proof. Admitted. (* STUB *)
  Lemma wf_strengthen : forall m, dbm_wf m -> dbm_wf (strengthen m).
  Proof. Admitted. (* STUB *)
  Lemma tclose_sound : forall m v, models m v -> ngamma (tclose m) v.
  Proof. Admitted. (* STUB *)
  Lemma tclose_bot : forall m, tclose m = Unreached -> forall v, ~ models m v.
  Proof. Admitted. (* STUB *)
  Lemma incr_close_sound : forall i j d m v,
    models m v -> (vl v j - vl v i <= d)%Z -> ngamma (incr_close i j d m) v.
  Proof. Admitted. (* STUB *)
  Lemma tclose_tight : forall m m', dbm_wf m -> coherent m ->
    tclose m = Reached m' -> tightly_closed m'.
  Proof. Admitted. (* STUB *)
  Lemma incr_close_eq : forall m i j d, dbm_wf m -> tightly_closed m ->
    same_entries (incr_close i j d m) (tclose (add_cons i j d m)).
  Proof. Admitted. (* STUB *)
  Lemma bits_tclose_le : forall m m', tclose m = Reached m' ->
    ell m' <= ell m + Nat.log2 (supp m) + 1.
  Proof. Admitted. (* STUB *)
  (** State size charges all stored numeric data. *)
  Lemma F_size : forall s, size s = (ns s + 1)^2 * (bs s + ells s + 1) + skels s.
  Proof. Admitted. (* STUB *)
  (** Range work charges the numeric query and its linearization. *)
  Lemma F_range_work : forall e s, (N.of_nat (range_work e s) =
    N.of_nat ((tsize e + 1) * (bs s + ells s + F.bits_e e + 1)^2) + F.T_lin_of e)%N.
  Proof. Admitted. (* STUB *)
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
  Lemma supp_fw_round : forall k m,
    supp (fw_round k m) = supp m /\ b (fw_round k m) = b m.
  Proof. Admitted. (* STUB *)
  (** A consistent matrix has no more pivot keys than codes in its support. *)
  Lemma keys_le : forall m, dbm_wf m -> length (keys m) <= supp m.
  Proof. Admitted. (* STUB *)
  (** Floyd-Warshall runs the traced rounds over the pivot keys. *)
  Lemma F_fw : forall m, fw m =
    fold_left (fun a km => fw_round (fst km) a) (fw_trace (keys m) m) m.
  Proof. Admitted. (* STUB *)
  Definition diag_ok (m : dbm) : bool :=
    forallb (fun k => match entry m k k with Some d => (0 <=? d)%Z | None => true end) (keys m).
  TimeFun diag_ok.
  (** Tight closure tightens and strengthens only a consistent closed matrix. *)
  Lemma T4_tclose : forall m, dbm_wf m ->
    (T_tclose m <= T_fw m + k_octagon * N.of_nat ((supp m + 1)^2 * (b m + ell m + 1)) +
      if diag_ok (fw m) then T_tighten (fw m) + T_strengthen (tighten (fw m)) else 0)%N.
  Proof. Admitted. (* STUB *)
  (** Tightening and strengthening keep the support. *)
  Lemma supp_tighten_strengthen : forall m,
    supp (tighten m) = supp m /\ b (tighten m) = b m /\
    supp (strengthen m) = supp m /\ b (strengthen m) = b m.
  Proof. Admitted. (* STUB *)
End OctagonT.
