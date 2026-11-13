(** * Difference-bound matrices

    Sparse matrices store finite bounds and interpret missing entries as infinity.
    For example, a zero-to-variable entry bounds that variable from above.
    Builds on: ZoneSig and keyed map operations. *)

From Stdlib Require Import List ZArith Lia.
From Argent Require Import Time Tactics Std.
From Galois.Base Require Import KeySig MapSig Code.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import LangSig ValueSig.
From Galois.States Require Import EnvSig.
From Galois.Relational Require Import LinForm LinearizeSig NumStateSig ZoneSig.
Local Open Scope nat_scope.

Module ZoneCode (X : KEY_OPS) (K : KEY_OPS with Definition t := option X.t
      with Definition encode := option_code X.encode)
    (M : MAP_OPS K) (L : LANG_OPS) (F : LINEARIZE_OPS X L) <: ZONE_OPS X K M L F.
  Definition dbm := M.t (M.t Z).
  Definition t := reach dbm.
  Definition wparam := nat.

  Definition row_of (r : option (M.t Z)) : M.t Z :=
    match r with Some row => row | None => M.empty end.

  Definition bound_leb (a b : option Z) : bool :=
    match a, b with
    | _, None => true
    | Some x, Some y => (x <=? y)%Z
    | None, Some _ => false
    end.

  Definition row_leb (a b : option (M.t Z)) : bool :=
    M.forall2b bound_leb (row_of a) (row_of b).

  Definition leb (a b : t) : bool :=
    match a, b with
    | Unreached, _ => true
    | Reached _, Unreached => false
    | Reached ma, Reached mb => M.forall2b row_leb ma mb
    end.

  Definition bot : t := Unreached.

  Definition is_bot (s : t) : bool :=
    match s with Unreached => true | Reached _ => false end.

  Definition bound_join (a b : option Z) : option Z :=
    match a, b with Some x, Some y => Some (Z.max x y) | _, _ => None end.

  Definition row_join (a b : option (M.t Z)) : option (M.t Z) :=
    match a, b with
    | Some x, Some y => Some (M.merge bound_join x y)
    | _, _ => None
    end.

  Definition join (a b : t) : t :=
    match a, b with
    | Unreached, _ => b
    | _, Unreached => a
    | Reached ma, Reached mb => Reached (M.merge row_join ma mb)
    end.

  Definition top : t := Reached M.empty.

  Definition bound_meet (a b : option Z) : option Z :=
    match a, b with
    | Some x, Some y => Some (Z.min x y)
    | None, _ => b
    | _, None => a
    end.

  Definition row_meet (a b : option (M.t Z)) : option (M.t Z) :=
    match a, b with
    | Some x, Some y => Some (M.merge bound_meet x y)
    | None, _ => b
    | _, None => a
    end.

  Definition meet (a b : t) : t :=
    match a, b with
    | Reached ma, Reached mb => Reached (M.merge row_meet ma mb)
    | _, _ => Unreached
    end.

  Definition bound_widen (a b : option Z) : option Z :=
    match a, b with
    | Some x, Some y => if (y <=? x)%Z then Some x else None
    | _, _ => None
    end.

  Definition row_widen (a b : option (M.t Z)) : option (M.t Z) :=
    match a with
    | Some x => Some (M.merge bound_widen x (row_of b))
    | None => None
    end.

  Definition widen (_ : wparam) (a b : t) : t :=
    if leb b a then a else
      match a, b with
      | Unreached, _ => b
      | _, Unreached => a
      | Reached ma, Reached mb => Reached (M.merge row_widen ma mb)
      end.

  Definition narrow (a b : t) : t := meet a b.

  Definition forget_row (x : X.t) (r : option (M.t Z))
      (_ : option (M.t Z)) : option (M.t Z) :=
    match r with
    | Some row => Some (M.remove (Some x) row)
    | None => None
    end.

  Definition havoc (x : X.t) (s : t) : t :=
    match s with
    | Unreached => Unreached
    | Reached m => Reached (M.merge (forget_row x) (M.remove (Some x) m) M.empty)
    end.

  (* STUB-CODE *)
  Definition assign (_ : X.t) (_ : term L.op X.t) (_ : t) : t := Unreached.
  (* STUB-CODE *)
  Definition assume (_ : L.guard) (_ : list (term L.op X.t)) (_ : t) : t := Unreached.
  (* STUB-CODE *)
  Definition range (_ : term L.op X.t) (_ : t) : bnd * bnd := (NegInf, PosInf).
  Definition entry (m : dbm) (i j : K.t) : option Z :=
    match M.get i m with Some row => M.get j row | None => None end.

  Definition lower_bound (d : Z) (old : option Z) : Z :=
    match old with Some z => Z.min d z | None => d end.

  Definition add_cons (i j : K.t) (d : Z) (m : dbm) : dbm :=
    let row := row_of (M.get i m) in
    M.set i (M.set j (lower_bound d (M.get j row)) row) m.

  Definition via_bound (a : Z) (old next : option Z) : option Z :=
    match next with
    | Some z => Some (lower_bound (a + z)%Z old)
    | None => old
    end.

  Definition round_row (k : K.t) (pivot : M.t Z) (r : option (M.t Z))
      (_ : option (M.t Z)) : option (M.t Z) :=
    match r with
    | Some row =>
      Some (match M.get k row with
        | Some a => M.merge (via_bound a) row pivot
        | None => row
        end)
    | None => None
    end.

  Definition fw_round (k : K.t) (m : dbm) : dbm :=
    M.merge (round_row k (row_of (M.get k m))) m M.empty.

  (* STUB-CODE *)
  Definition close (_ : dbm) : t := Unreached.
  (* STUB-CODE *)
  Definition incr_close (_ _ : K.t) (_ : Z) (_ : dbm) : t := Unreached.
End ZoneCode.

Module Zone (X : KEY) (K : KEY with Definition t := option X.t
      with Definition encode := option_code X.encode)
    (M : MAP K) (L : LANG) (N : NUM_VIEW L) (F : LINEARIZE X L N) <: ZONE X K M L N F.
  Include ZoneCode X K M L F.
  (* STUB-CODE *)
  Definition wrank (_ : wparam) (s : t) : nat :=
    match s with
    | Unreached => 0
    | Reached m => fold_right Nat.add 0 (map (fun p =>
        match M.find p m with Some row => length (M.codes row) | None => 0 end) (M.codes m))
    end.
  Definition vz (v : X.t -> Z) (i : K.t) : Z :=
    match i with None => 0%Z | Some x => v x end.
  Definition models (m : dbm) (v : X.t -> Z) : Prop :=
    forall i j d, entry m i j = Some d -> (vz v j - vz v i <= d)%Z.
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
End Zone.

Module ZoneT (X : KEY_T) (K : KEY_T with Definition t := option X.t
      with Definition encode := option_code X.encode)
    (M : MAP_T K) (L : LANG_T) (N : NUM_VIEW L) (F : LINEARIZE_T X L N)
    <: ZONE_ALL X K M L N F.
  Include Zone X K M L N F.
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
    (ns s + 1)^2 * (bs s + ells s + X.bits x + F.bits_e e + lin_bits e + 1) +
      skels s +
      (tsize e + 1) * (bs s + ells s + F.bits_e e + Nat.log2 (tsize e) + 1)^2 +
      N.to_nat (F.T_lin_of e).
  Definition havoc_work (x : X.t) (s : t) : nat :=
    (ns s + 1)^2 * (bs s + X.bits x + ells s + 1) + skels s.
  Definition assume_work (g : L.guard) (es : list (term L.op X.t)) (s : t) : nat :=
    length (F.atoms_of g es) * (ns s + 2 * length (F.atoms_of g es) + 1)^2 *
      (bs s + ells s + F.bits_es g es + 2 * length (F.atoms_of g es) + 1) +
      N.to_nat (F.T_atoms_of g es).
  Definition range_work (e : term L.op X.t) (s : t) : nat :=
    (tsize e + 1) * (bs s + ells s + F.bits_e e + Nat.log2 (tsize e) + 1)^2 +
      N.to_nat (F.T_lin_of e).
  Definition range_bits (e : term L.op X.t) (s : t) : nat :=
    ells s + F.bits_e e + Nat.log2 (tsize e) + 2.
  TimeFun row_of.
  TimeFun bound_leb.
  TimeFun row_leb.
  TimeFun bound_join.
  TimeFun row_join.
  TimeFun bound_meet.
  TimeFun row_meet.
  TimeFun bound_widen.
  TimeFun row_widen.
  TimeFun forget_row.
  TimeFun lower_bound.
  TimeFun via_bound.
  TimeFun round_row.
  TimeFun bot.
  TimeFun top.
  TimeFun meet.
  TimeFun leb.
  TimeFun join.
  TimeFun is_bot.
  TimeFun widen.
  TimeFun narrow.
  TimeFun havoc.
  TimeFun assign.
  TimeFun assume.
  TimeFun range.
  TimeFun entry.
  TimeFun fw_round.
  TimeFun close.
  TimeFun add_cons.
  TimeFun incr_close.
  Definition c_lat : N := 1. (* STUB *)
  Lemma c_lat_pos : (1 <= c_lat)%N.
  Proof. Admitted. (* STUB *)
  Lemma T_leb_le : forall a b,
    (T_leb a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_join_le : forall a b,
    (T_join a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_is_bot_le : forall s,
    (T_is_bot s <= c_lat * N.of_nat (size s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_widen_le : forall p a b,
    (T_widen p a b <= c_lat * N.of_nat
      ((wunits a + wunits b) * wsize p + (size a + size b + wsize p + 1)))%N.
  Proof. Admitted. (* STUB *)
  Definition c_num : N := 1. (* STUB *)
  Lemma T_assign_le : forall x e s,
    (T_assign x e s <= c_num * N.of_nat (assign_work x e s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_havoc_le : forall x s,
    (T_havoc x s <= c_num * N.of_nat (havoc_work x s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_assume_le : forall g es s,
    (T_assume g es s <= c_num * N.of_nat (assume_work g es s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_narrow_le : forall a b,
    (T_narrow a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_range_le : forall e s, (T_range e s <= c_num * N.of_nat (range_work e s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma range_size : forall e s,
    (N.of_nat
      (match fst (range e s) with Fin z => Z.size_nat z | _ => 0 end +
       match snd (range e s) with Fin z => Z.size_nat z | _ => 0 end) <=
     c_num * N.of_nat (range_bits e s + 1))%N.
  Proof. Admitted. (* STUB *)
  Definition c_zone : N := 1. (* STUB *)
  Lemma T_entry_le : forall m i j,
    (T_entry m i j <= c_zone * N.of_nat (K.bits i + K.bits j + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_add_cons_le : forall i j d m,
    (T_add_cons i j d m <= c_zone * N.of_nat
      (K.bits i + K.bits j + Z.size_nat d + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_close_le : forall m, dbm_wf m ->
    (T_close m <= c_zone * N.of_nat (((supp m + 1)^3)%nat) *
      N.of_nat ((b m + ell m + Nat.log2 (supp m) + 1)%nat))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_incr_close_le : forall i j d m, (T_incr_close i j d m <=
    c_zone * N.of_nat (((supp m + 1)^2)%nat) *
      N.of_nat ((b m + K.bits i + K.bits j + ell m + Z.size_nat d + 1)%nat))%N.
  Proof. Admitted. (* STUB *)
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
  Definition k_zone : N := 1. (* STUB *)

  (** Deduplication retains exactly the input and accumulator members. *)
  Lemma dedup_membership : forall (A : Type) (eqb : A -> A -> bool),
    (forall x y, eqb x y = true <-> x = y) -> forall xs acc x,
    In x (fold_left (fun seen y => if existsb (eqb y) seen then seen else y :: seen)
      xs acc) <-> In x xs \/ In x acc.
  Proof.
    intros A eqb Heq xs. induction xs as [|a xs IH]; intros acc x.
    - cbn. tauto.
    - cbn [fold_left]. destruct (existsb (eqb a) acc) eqn:Hseen.
      + assert (Ha : In a acc).
        { apply existsb_exists in Hseen. destruct Hseen as [y [Hy Hay]].
          apply Heq in Hay. now subst y. }
        rewrite IH. cbn [In]. split.
        * tauto.
        * intros [[Hax | Hin] | Hin].
          -- subst x. now right.
          -- now left.
          -- now right.
      + rewrite IH. cbn [In]. tauto.
  Qed.

  (** Deduplication preserves a duplicate-free accumulator. *)
  Lemma dedup_nodup : forall (A : Type) (eqb : A -> A -> bool),
    (forall x y, eqb x y = true <-> x = y) -> forall xs acc,
    NoDup acc ->
    NoDup (fold_left (fun seen y => if existsb (eqb y) seen then seen else y :: seen)
      xs acc).
  Proof.
    intros A eqb Heq xs. induction xs as [|a xs IH]; intros acc Hacc.
    - exact Hacc.
    - cbn [fold_left]. destruct (existsb (eqb a) acc) eqn:Hseen; apply IH.
      + exact Hacc.
      + constructor; [|exact Hacc]. intro Ha.
        assert (Hfound : existsb (eqb a) acc = true).
        { apply existsb_exists. exists a. split; [exact Ha|apply Heq; reflexivity]. }
        congruence.
  Qed.

  (** Support contains every outer code and every code of a stored row. *)
  Lemma support_spec : forall m p,
    In p (support m) <-> In p (M.codes m) \/ In p (flat_map M.codes (rows m)).
  Proof.
    intros m p. unfold support.
    rewrite (dedup_membership positive Pos.eqb Pos.eqb_eq), in_app_iff.
    cbn. tauto.
  Qed.

  (** A list maximum bounds each selected member. *)
  Lemma maximum_member : forall (A : Type) (f : A -> nat) xs x,
    In x xs -> f x <= fold_right Nat.max 0 (map f xs).
  Proof.
    intros A f xs. induction xs as [|a xs IH]; intros x Hin.
    - contradiction.
    - cbn in Hin |- *. destruct Hin as [Hax | Hin].
      + subst x. apply Nat.le_max_l.
      + eapply Nat.le_trans; [exact (IH x Hin)|apply Nat.le_max_r].
  Qed.

  (** A uniform bound on summands bounds their sum by length times that bound. *)
  Lemma sum_members_bound : forall (A : Type) (f : A -> nat) xs upper,
    (forall x, In x xs -> f x <= upper) ->
    fold_right Nat.add 0 (map f xs) <= length xs * upper.
  Proof.
    intros A f xs. induction xs as [|a xs IH]; intros upper Hbound.
    - cbn. lia.
    - cbn. assert (Ha : f a <= upper) by (apply Hbound; now left).
      assert (Htail : fold_right Nat.add 0 (map f xs) <= length xs * upper).
      { apply IH. intros x Hin. apply Hbound. now right. }
      lia.
  Qed.

  (** Every supported code fits the matrix key-bit bound. *)
  Lemma support_bits : forall m p, In p (support m) -> Pos.size_nat p <= b m.
  Proof.
    intros m p Hin. unfold b. now apply maximum_member.
  Qed.

  (** Distinct stored codes inject into any support containing them. *)
  Lemma codes_support_length : forall A (r : M.t A) m,
    (forall p, In p (M.codes r) -> In p (support m)) -> length (M.codes r) <= supp m.
  Proof.
    intros A r m Hin. unfold supp. apply NoDup_incl_length.
    - apply M.codes_nodup.
    - exact Hin.
  Qed.

  (** A map whose codes lie in the support has a bounded skeleton. *)
  Lemma nodes_support : forall A (r : M.t A) m,
    (forall p, In p (M.codes r) -> In p (support m)) ->
    M.nodes r <= supp m * (b m + 1).
  Proof.
    intros A r m Hin.
    pose proof (M.nodes_le_codes A r) as Hnodes.
    pose proof (codes_support_length A r m Hin) as Hlength.
    assert (Hsum : fold_right Nat.add 0
      (map (fun p => Pos.size_nat p + 1) (M.codes r)) <=
      length (M.codes r) * (b m + 1)).
    { apply sum_members_bound. intros p Hp.
      pose proof (support_bits m p (Hin p Hp)). lia. }
    nia.
  Qed.

  (** Row collection retains at most one row for each outer code. *)
  Lemma rows_length : forall m, length (rows m) <= length (M.codes m).
  Proof.
    intro m. unfold rows. induction (M.codes m) as [|p ps IH].
    - reflexivity.
    - cbn. destruct (M.find p m); cbn; lia.
  Qed.

  (** Every successful raw row lookup is present in the row collection. *)
  Lemma row_in_rows : forall m p row, M.find p m = Some row -> In row (rows m).
  Proof.
    intros m p row Hrow. unfold rows. apply in_flat_map. exists p. split.
    - apply M.codes_spec. rewrite Hrow. discriminate.
    - rewrite Hrow. now left.
  Qed.

  (** The stored codes cover the skeleton even when labels do not match their codes. *)
  Lemma skel_le : forall m, skel m <= (supp m + 1)^2 * (b m + 1).
  Proof.
    intro m.
    assert (Houter : forall p, In p (M.codes m) -> In p (support m)).
    { intros p Hp. apply support_spec. now left. }
    pose proof (nodes_support (M.t Z) m m Houter) as Hnodes.
    pose proof (codes_support_length (M.t Z) m m Houter) as Hlength.
    pose proof (rows_length m) as Hrows.
    assert (Hsum : fold_right Nat.add 0 (map M.nodes (rows m)) <=
      length (rows m) * (supp m * (b m + 1))).
    { apply sum_members_bound. intros row Hrow. apply nodes_support.
      intros p Hp. apply support_spec. right. apply in_flat_map.
      exists row. now split. }
    unfold skel. cbn [Nat.pow]. nia.
  Qed.
  Lemma grow_incr_close : forall i j d m m', incr_close i j d m = Reached m' ->
    supp m' <= supp m + 2 /\
    b m' <= Nat.max (b m) (Nat.max (K.bits i) (K.bits j)) /\
    ell m' <= Nat.max (ell m) (Z.size_nat d) + 2.
  Proof. Admitted. (* STUB *)

  (** Widening units cover the squared support size. *)
  Lemma F_wunits : forall s, wunits s = (ns s + 1) ^ 2.
  Proof. Admitted. (* STUB *)
  (** Assumption work charges incremental closure for every emitted atom. *)
  Lemma F_assume_work : forall g es s,
    (N.of_nat (assume_work g es s) =
      N.of_nat (length (F.atoms_of g es) *
        (ns s + 2 * length (F.atoms_of g es) + 1)^2 *
        (bs s + ells s + F.bits_es g es + 2 * length (F.atoms_of g es) + 1)) +
      F.T_atoms_of g es)%N.
  Proof. Admitted. (* STUB *)
  (** Assignment work pays for linearization and quadratic matrix updates. *)
  Lemma F_assign_work : forall x e s,
    (N.of_nat (assign_work x e s) =
      N.of_nat ((ns s + 1)^2 *
        (bs s + ells s + X.bits x + F.bits_e e + lin_bits e + 1) + skels s +
        (tsize e + 1) * (bs s + ells s + F.bits_e e + Nat.log2 (tsize e) + 1)^2) +
      F.T_lin_of e)%N.
  Proof. Admitted. (* STUB *)
  Lemma F_havoc_work : forall x s,
    havoc_work x s = (ns s + 1)^2 * (bs s + X.bits x + ells s + 1) + skels s.
  Proof. Admitted. (* STUB *)
  Lemma F_join_entry : forall ma mb i j,
    match join (Reached ma) (Reached mb) with
    | Reached mj => entry mj i j =
        match entry ma i j, entry mb i j with
        | Some x, Some y => Some (Z.max x y)
        | _, _ => None
        end
    | Unreached => False
    end.
  Proof. Admitted. (* STUB *)
  Lemma fw_round_implied : forall k m v, models m v -> models (fw_round k m) v.
  Proof. Admitted. (* STUB *)
  Lemma wf_fw_round : forall k m, dbm_wf m -> dbm_wf (fw_round k m).
  Proof. Admitted. (* STUB *)
  Lemma wf_add_cons : forall i j d m, dbm_wf m -> dbm_wf (add_cons i j d m).
  Proof. Admitted. (* STUB *)
  Lemma wf_incr_close : forall i j d m, dbm_wf m ->
    match incr_close i j d m with Unreached => True | Reached m' => dbm_wf m' end.
  Proof. Admitted. (* STUB *)
  Lemma close_sound : forall m v, models m v -> ngamma (close m) v.
  Proof. Admitted. (* STUB *)
  Lemma close_bot : forall m, close m = Unreached -> forall v, ~ models m v.
  Proof. Admitted. (* STUB *)
  Lemma incr_close_sound : forall i j d m v,
    models m v -> (vz v j - vz v i <= d)%Z -> ngamma (incr_close i j d m) v.
  Proof. Admitted. (* STUB *)
  Lemma close_shortest : forall m m' i j, dbm_wf m -> close m = Reached m' -> i <> j ->
    (forall d, entry m' i j = Some d -> exists ks, chain_weight m i ks j = Some d) /\
    (forall ks d, chain_weight m i ks j = Some d ->
       exists d', entry m' i j = Some d' /\ (d' <= d)%Z).
  Proof. Admitted. (* STUB *)
  Lemma incr_close_eq : forall m i j d, dbm_wf m -> closed m ->
    same_entries (incr_close i j d m) (close (add_cons i j d m)).
  Proof. Admitted. (* STUB *)
  Lemma T1_fw_round : forall k m, dbm_wf m ->
    (T_fw_round k m <= k_zone * N.of_nat
      ((supp m + 1)^2 * (b m + K.bits k + ell m + 1)))%N.
  Proof. Admitted. (* STUB *)
  Lemma bits_close_le : forall m m', close m = Reached m' ->
    ell m' <= ell m + Nat.log2 (supp m) + 1.
  Proof. Admitted. (* STUB *)
  (** State size charges all stored numeric data. *)
  Lemma F_size : forall s, size s = (ns s + 1)^2 * (bs s + ells s + 1) + skels s.
  Proof. Admitted. (* STUB *)
  (** Range work charges the numeric query and its linearization. *)
  Lemma F_range_work : forall e s, (N.of_nat (range_work e s) =
    N.of_nat ((tsize e + 1) *
      (bs s + ells s + F.bits_e e + Nat.log2 (tsize e) + 1)^2) + F.T_lin_of e)%N.
  Proof. Admitted. (* STUB *)
  Lemma F_range_bits : forall e s,
    range_bits e s = ells s + F.bits_e e + Nat.log2 (tsize e) + 2.
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
  Lemma keys_support : forall m k, dbm_wf m -> In k (keys m) ->
    In (K.encode k) (support m).
  Proof. Admitted. (* STUB *)
  Lemma bits_fw_round_step : forall k m, ell (fw_round k m) <= ell m + 1.
  Proof. Admitted. (* STUB *)
  Lemma bits_fw_trace_le : forall ks m k a, dbm_wf m ->
    In (k, a) (fw_trace ks m) ->
    ell a <= ell m + Nat.log2 (supp m) + 1.
  Proof. Admitted. (* STUB *)
  Lemma supp_fw_round : forall k m,
    supp (fw_round k m) = supp m /\ b (fw_round k m) = b m.
  Proof. Admitted. (* STUB *)
  (** A consistent matrix has no more pivot keys than codes in its support. *)
  Lemma keys_le : forall m, dbm_wf m -> length (keys m) <= supp m.
  Proof. Admitted. (* STUB *)
  (** Closure pays its pivot list, the performed rounds and the final diagonal. *)
  Lemma T2_close : forall m, dbm_wf m ->
    (T_close m <= k_zone * (N.of_nat ((supp m + 1)^2 * (b m + ell m + 1)) +
      fold_right N.add 0%N (map (fun km => T_fw_round (fst km) (snd km))
        (fw_trace (keys m) m))))%N.
  Proof. Admitted. (* STUB *)
End ZoneT.
