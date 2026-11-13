(** * Difference-bound matrices

    Sparse matrices store finite bounds and interpret missing entries as infinity.
    For example, a zero-to-variable entry bounds that variable from above.
    Builds on: ZoneSig and keyed map operations. *)

From Stdlib Require Import List Bool NArith ZArith Lia.
From Argent Require Import Time Tactics Std.
From Galois.Base Require Import KeySig MapSig Code.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import LangSig ValueSig.
From Galois.States Require Import EnvSig.
From Galois.Relational Require Import LinForm LinearizeSig NumStateSig ZoneSig.
Local Open Scope nat_scope.

(** Finite interval endpoints add; an absent endpoint remains unbounded. *)
Definition rel_add_bounds (a b : bnd * bnd) : bnd * bnd :=
  (match fst a, fst b with Fin x, Fin y => Fin (x + y)%Z | _, _ => NegInf end,
   match snd a, snd b with Fin x, Fin y => Fin (x + y)%Z | _, _ => PosInf end).
TimeFun rel_add_bounds.

(** Scaling reverses endpoints exactly when the coefficient is negative. *)
Definition rel_scale_bounds (c : Z) (a : bnd * bnd) : bnd * bnd :=
  if (c =? 0)%Z then (Fin 0%Z, Fin 0%Z) else
  let lo := if (0 <=? c)%Z then fst a else snd a in
  let hi := if (0 <=? c)%Z then snd a else fst a in
  (match lo with Fin x => Fin (c * x)%Z | _ => NegInf end,
   match hi with Fin x => Fin (c * x)%Z | _ => PosInf end).
TimeFun rel_scale_bounds.

(** Each coefficient is queried once, and the constant starts the sum. *)
Definition rel_form_bounds {X : Type} (ranges : X -> bnd * bnd)
    (f : lin X) : bnd * bnd :=
  fold_right (fun p acc => rel_add_bounds (rel_scale_bounds (snd p) (ranges (fst p))) acc)
    (Fin (cst f), Fin (cst f)) (coef f).
TimeFun rel_form_bounds.

(** A valid wrapping interval bounds every modular result. *)
Definition rel_wrap_bounds (r : wrapr) (a : bnd * bnd) : bnd * bnd :=
  match r with
  | NoWrap => a
  | WrapTo lo hi => if (lo <=? hi)%Z then (Fin lo, Fin hi) else (NegInf, PosInf)
  end.
TimeFun rel_wrap_bounds.

(** An affine result may be used without wrapping when both endpoints fit. *)
Definition rel_wrap_exact (r : wrapr) (a : bnd * bnd) : bool :=
  match r with
  | NoWrap => true
  | WrapTo lo hi =>
    match a with
    | (Fin l, Fin h) => andb (lo <=? l)%Z (h <=? hi)%Z
    | _ => false
    end
  end.
TimeFun rel_wrap_exact.

Lemma rel_add_bounds_sound : forall a b x y,
  in_bnd (fst a) (snd a) x -> in_bnd (fst b) (snd b) y ->
  in_bnd (fst (rel_add_bounds a b)) (snd (rel_add_bounds a b)) (x + y)%Z.
Proof.
  intros [al ah] [bl bh] x y Ha Hb.
  unfold rel_add_bounds, in_bnd in *.
  destruct al, ah, bl, bh; cbn in *; intuition lia.
Qed.

Lemma rel_scale_bounds_sound : forall c a x,
  in_bnd (fst a) (snd a) x ->
  in_bnd (fst (rel_scale_bounds c a)) (snd (rel_scale_bounds c a)) (c * x)%Z.
Proof.
  intros c [lo hi] x Hx. unfold rel_scale_bounds.
  destruct (c =? 0)%Z eqn:Hc.
  - apply Z.eqb_eq in Hc. subst c. unfold in_bnd. cbn. lia.
  - destruct (0 <=? c)%Z eqn:Hsign;
      [apply Z.leb_le in Hsign|apply Z.leb_gt in Hsign];
      unfold in_bnd in *; destruct lo, hi; cbn in *; intuition nia.
Qed.

Lemma rel_form_bounds_sound : forall (X : Type) ranges (f : lin X) v,
  (forall x, in_bnd (fst (ranges x)) (snd (ranges x)) (v x)) ->
  in_bnd (fst (rel_form_bounds ranges f)) (snd (rel_form_bounds ranges f)) (eval_lin v f).
Proof.
  intros X ranges [cs c] v Hr. unfold rel_form_bounds, eval_lin. cbn [coef cst].
  induction cs as [|[x a] cs IH].
  - change (in_bnd (Fin c) (Fin c) c). unfold in_bnd. lia.
  - change (in_bnd
      (fst (rel_add_bounds (rel_scale_bounds a (ranges x))
        (rel_form_bounds ranges (Lin X cs c))))
      (snd (rel_add_bounds (rel_scale_bounds a (ranges x))
        (rel_form_bounds ranges (Lin X cs c))))
      (a * v x + eval_coef v cs + c)%Z).
    replace (a * v x + eval_coef v cs + c)%Z with (a * v x + (eval_coef v cs + c))%Z by ring.
    apply rel_add_bounds_sound; [apply rel_scale_bounds_sound, Hr|exact IH].
Qed.

Lemma rel_wrap_bounds_sound : forall r a z,
  in_bnd (fst a) (snd a) z ->
  in_bnd (fst (rel_wrap_bounds r a)) (snd (rel_wrap_bounds r a)) (wrap_into r z).
Proof.
  intros [|lo hi] a z Hz; [exact Hz|].
  unfold rel_wrap_bounds. destruct (lo <=? hi)%Z eqn:Hbounds.
  - apply Z.leb_le in Hbounds. unfold wrap_into, in_bnd. cbn.
    pose proof (Z.mod_pos_bound (z - lo) (hi - lo + 1) ltac:(lia)). lia.
  - unfold in_bnd. cbn. tauto.
Qed.

Lemma rel_wrap_exact_sound : forall r a z,
  in_bnd (fst a) (snd a) z -> rel_wrap_exact r a = true -> wrap_into r z = z.
Proof.
  intros [|lo hi] [l h] z Hz Hexact; [reflexivity|].
  unfold rel_wrap_exact in Hexact.
  destruct l, h; cbn in Hexact; try discriminate Hexact.
  apply andb_true_iff in Hexact. destruct Hexact as [Hl Hh].
  apply Z.leb_le in Hl. apply Z.leb_le in Hh. unfold in_bnd in Hz. cbn in Hz.
  unfold wrap_into. rewrite Z.mod_small by lia. lia.
Qed.

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
  Definition entry (m : dbm) (i j : K.t) : option Z :=
    match M.get i m with Some row => M.get j row | None => None end.

  Definition variable_bounds (m : dbm) (x : X.t) : bnd * bnd :=
    (match entry m (Some x) None with Some d => Fin (-d)%Z | None => NegInf end,
     match entry m None (Some x) with Some d => Fin d | None => PosInf end).

  Definition form_bounds (m : dbm) (f : lin X.t) : bnd * bnd :=
    rel_form_bounds (variable_bounds m) f.

  Definition range (e : term L.op X.t) (s : t) : bnd * bnd :=
    match s with
    | Unreached => (NegInf, PosInf)
    | Reached m =>
      match F.lin_of e with
      | Some (f, r) => rel_wrap_bounds r (form_bounds m f)
      | None => (NegInf, PosInf)
      end
    end.

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

  Definition relax_round (k : K.t) (m : dbm) : dbm :=
    M.merge (round_row k (row_of (M.get k m))) m M.empty.

  Definition column_present (k : K.t) (row : M.t Z) : bool :=
    match M.get k row with Some _ => true | None => false end.

  Definition pivot_present (k : K.t) (m : dbm) : bool :=
    match M.get k m with
    | Some _ => true
    | None => M.existsb (column_present k) m
    end.

  (** Materialize the zero walk only when its code already belongs to the matrix. *)
  Definition fw_round (k : K.t) (m : dbm) : dbm :=
    let seed := if pivot_present k m then add_cons k k 0%Z m else m in
    relax_round k seed.

  Definition remember_key (acc : M.t unit * list K.t) (k : K.t)
      : M.t unit * list K.t :=
    match M.get k (fst acc) with
    | Some _ => acc
    | None => (M.set k tt (fst acc), k :: snd acc)
    end.

  (** A map-backed set preserves the signature's reverse first-occurrence order. *)
  Definition pivot_keys (m : dbm) : list K.t :=
    let es := M.elements m in
    snd (fold_left remember_key
      (map fst es ++ flat_map (fun kv => map fst (M.elements (snd kv))) es)
      (M.empty, nil)).

  Definition nonnegative (k : K.t) (m : dbm) : bool :=
    match entry m k k with Some d => (0 <=? d)%Z | None => true end.

  Fixpoint close_pivots (ks : list K.t) (m : dbm) : t :=
    match ks with
    | nil => Reached m
    | k :: ks =>
      let next := fw_round k m in
      if nonnegative k next then close_pivots ks next else Unreached
    end.

  Definition close (m : dbm) : t :=
    let ks := pivot_keys m in
    match close_pivots ks m with
    | Unreached => Unreached
    | Reached next =>
      if forallb (fun k => nonnegative k next) ks then Reached next else Unreached
    end.

  Definition increment_row (i : K.t) (d : Z) (exit : M.t Z)
      (r : option (M.t Z)) (_ : option (M.t Z)) : option (M.t Z) :=
    match r with
    | Some row =>
      Some (match M.get i row with
        | Some a => M.merge (via_bound (a + d)%Z) row exit
        | None => row
        end)
    | None => None
    end.

  (** Each new path uses the inserted edge between its old prefix and suffix. *)
  Definition incr_close (i j : K.t) (d : Z) (m : dbm) : t :=
    let seed := add_cons i j d (add_cons j j 0%Z (add_cons i i 0%Z m)) in
    let next := M.merge (increment_row i d (row_of (M.get j seed))) seed M.empty in
    if andb (nonnegative i next) (nonnegative j next) then Reached next else Unreached.

  (** A difference has at most one positive and one negative unit coefficient. *)
  Definition difference_pair (cs : list (X.t * Z)) : option (K.t * K.t) :=
    match cs with
    | nil => Some (None, None)
    | (x, a) :: nil =>
      if (a =? 1)%Z then Some (None, Some x) else
      if (a =? -1)%Z then Some (Some x, None) else None
    | (x, a) :: (y, b) :: nil =>
      if andb (a =? 1)%Z (b =? -1)%Z then Some (Some y, Some x) else
      if andb (a =? -1)%Z (b =? 1)%Z then Some (Some x, Some y) else None
    | _ => None
    end.

  (** Recognizing bounded coefficient patterns avoids traversing unsupported forms. *)
  Definition difference_forms (l r : lin X.t) : option (K.t * K.t) :=
    match coef l, coef r with
    | nil, rs =>
      match difference_pair rs with Some (i, j) => Some (j, i) | None => None end
    | ls, nil => difference_pair ls
    | (x, a) :: nil, (y, b) :: nil =>
      if andb (a =? 1)%Z (b =? 1)%Z then Some (Some y, Some x) else
      if andb (a =? -1)%Z (b =? -1)%Z then Some (Some x, Some y) else None
    | _, _ => None
    end.

  Definition form_exact (m : dbm) (f : lin X.t) (r : wrapr) : bool :=
    match r with
    | NoWrap => true
    | _ => rel_wrap_exact r (form_bounds m f)
    end.

  Definition refine (i j : K.t) (d : Z) (s : t) : t :=
    match s with Unreached => Unreached | Reached m => incr_close i j d m end.

  Definition assume_cmp (c : cmp) (i j : K.t) (d : Z) (s : t) : t :=
    match c with
    | CLe => refine i j d s
    | CLt => refine i j (d - 1)%Z s
    | CEq => refine j i (-d)%Z (refine i j d s)
    end.

  Definition assume_atom (s : t) (a : atom X.t) : t :=
    match s with
    | Unreached => Unreached
    | Reached m =>
      match difference_forms (al a) (ar a) with
      | None => s
      | Some (i, j) =>
        if andb (form_exact m (al a) (alw a)) (form_exact m (ar a) (arw a)) then
          assume_cmp (acmp a) i j (cst (ar a) - cst (al a))%Z s
        else s
      end
    end.

  Definition assume (g : L.guard) (es : list (term L.op X.t)) (s : t) : t :=
    match s with
    | Unreached => Unreached
    | Reached _ => fold_left assume_atom (F.atoms_of g es) s
    end.
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

  (** An absent row supplies no finite bound. *)
  Lemma get_row_of : forall r k,
    M.get k (row_of r) = match r with Some row => M.get k row | None => None end.
  Proof.
    intros [row|] k; [reflexivity|apply M.get_empty].
  Qed.

  (** Insertion changes only the selected entry, taking its minimum with the new bound. *)
  Lemma entry_add_cons : forall i j d m a b,
    entry (add_cons i j d m) a b =
    if K.eqb a i then
      if K.eqb b j then Some (lower_bound d (entry m i j)) else entry m a b
    else entry m a b.
  Proof.
    intros i j d m a b. unfold entry, add_cons.
    destruct (K.eqb_spec a i) as [Ha | Ha].
    - subst a. rewrite M.get_set_same.
      destruct (K.eqb_spec b j) as [Hb | Hb].
      + subst b. rewrite M.get_set_same, get_row_of. reflexivity.
      + rewrite M.get_set_other by exact Hb. apply get_row_of.
    - rewrite M.get_set_other by exact Ha. reflexivity.
  Qed.

  (** A minimum retains every value below both its finite operands. *)
  Lemma lower_bound_holds : forall value d old,
    (value <= d)%Z -> (forall z, old = Some z -> (value <= z)%Z) ->
    (value <= lower_bound d old)%Z.
  Proof.
    intros value d [z|] Hnew Hold; cbn [lower_bound].
    - apply Z.min_glb; [exact Hnew|apply Hold; reflexivity].
    - exact Hnew.
  Qed.

  (** Adding a satisfied constraint preserves the numeric store. *)
  Lemma models_add_cons : forall i j d m v,
    models m v -> (vz v j - vz v i <= d)%Z -> models (add_cons i j d m) v.
  Proof.
    intros i j d m v Hmodel Hnew a b z Hentry.
    rewrite entry_add_cons in Hentry.
    destruct (K.eqb_spec a i) as [Ha | Ha].
    - subst a. destruct (K.eqb_spec b j) as [Hb | Hb].
      + subst b. inversion Hentry; subst z.
        apply lower_bound_holds; [exact Hnew|]. intros old Hold. now apply Hmodel.
      + now apply Hmodel.
    - now apply Hmodel.
  Qed.

  (** A row relaxation selects the old bound or the two-edge path through its pivot. *)
  Lemma entry_relax_round : forall k m i j,
    entry (relax_round k m) i j =
    match entry m i k with
    | Some a => via_bound a (entry m i j) (entry m k j)
    | None => entry m i j
    end.
  Proof.
    intros k m i j. unfold relax_round, entry.
    rewrite M.get_merge by reflexivity. rewrite M.get_empty.
    destruct (M.get i m) as [row|]; cbn [round_row].
    - destruct (M.get k row) as [a|]; [|reflexivity].
      rewrite M.get_merge by reflexivity. rewrite get_row_of. reflexivity.
    - reflexivity.
  Qed.

  (** Relaxation retains values below the old bound and the proposed path bound. *)
  Lemma via_bound_holds : forall value a old next,
    (forall d, old = Some d -> (value <= d)%Z) ->
    (forall z, next = Some z -> (value <= a + z)%Z) ->
    forall d, via_bound a old next = Some d -> (value <= d)%Z.
  Proof.
    intros value a old [z|] Hold Hnext d Hentry; cbn [via_bound] in Hentry.
    - inversion Hentry; subst d. apply lower_bound_holds.
      + apply Hnext. reflexivity.
      + exact Hold.
    - now apply Hold.
  Qed.

  (** Every path added by one sparse round follows from two existing edges. *)
  Lemma relax_round_models : forall k m v, models m v -> models (relax_round k m) v.
  Proof.
    intros k m v Hmodel i j d Hentry. rewrite entry_relax_round in Hentry.
    destruct (entry m i k) as [a|] eqn:Hik.
    - eapply via_bound_holds; [| |exact Hentry].
      + intros old Hold. now apply Hmodel.
      + intros z Hkj. pose proof (Hmodel i k a Hik).
        pose proof (Hmodel k j z Hkj). lia.
    - now apply Hmodel.
  Qed.

  (** Adding a zero walk and relaxing through it preserves every model. *)
  Lemma fw_round_models : forall k m v, models m v -> models (fw_round k m) v.
  Proof.
    intros k m v Hmodel. unfold fw_round. apply relax_round_models.
    destruct (pivot_present k m); [|exact Hmodel].
    apply models_add_cons; [exact Hmodel|lia].
  Qed.

  (** A matrix with a model cannot have a negative diagonal. *)
  Lemma nonnegative_models : forall k m v, models m v -> nonnegative k m = true.
  Proof.
    intros k m v Hmodel. unfold nonnegative.
    destruct (entry m k k) as [d|] eqn:Hentry; [|reflexivity].
    apply Z.leb_le. specialize (Hmodel k k d Hentry). lia.
  Qed.

  (** Every completed prefix of the pivot loop preserves the original model. *)
  Lemma close_pivots_models : forall ks m v,
    models m v -> ngamma (close_pivots ks m) v.
  Proof.
    intro ks. induction ks as [|k ks IH]; intros m v Hmodel; cbn [close_pivots].
    - exact Hmodel.
    - pose proof (fw_round_models k m v Hmodel) as Hnext.
      rewrite (nonnegative_models k (fw_round k m) v Hnext). now apply IH.
  Qed.

  (** The full closure loop and its final diagonal check preserve every model. *)
  Lemma close_models : forall m v, models m v -> ngamma (close m) v.
  Proof.
    intros m v Hmodel. unfold close.
    pose proof (close_pivots_models (pivot_keys m) m v Hmodel) as Hnext.
    destruct (close_pivots (pivot_keys m) m) as [|next]; [exact Hnext|].
    assert (Hdiag : forallb (fun k => nonnegative k next) (pivot_keys m) = true).
    { apply forallb_forall. intros k Hkey. now apply (nonnegative_models k next v). }
    rewrite Hdiag. exact Hnext.
  Qed.

  (** An incremental update combines an incoming prefix, the new edge and an outgoing suffix. *)
  Lemma entry_increment : forall i j d m a b,
    entry (M.merge (increment_row i d (row_of (M.get j m))) m M.empty) a b =
    match entry m a i with
    | Some prefix => via_bound (prefix + d)%Z (entry m a b) (entry m j b)
    | None => entry m a b
    end.
  Proof.
    intros i j d m a b. unfold entry.
    rewrite M.get_merge by reflexivity. rewrite M.get_empty.
    destruct (M.get a m) as [row|]; cbn [increment_row].
    - destruct (M.get i row) as [prefix|]; [|reflexivity].
      rewrite M.get_merge by reflexivity. rewrite get_row_of. reflexivity.
    - reflexivity.
  Qed.

  (** Every incremental path follows from the matrix and the added constraint. *)
  Lemma increment_models : forall i j d m v,
    models m v -> (vz v j - vz v i <= d)%Z ->
    models (M.merge (increment_row i d (row_of (M.get j m))) m M.empty) v.
  Proof.
    intros i j d m v Hmodel Hnew a b bound Hentry. rewrite entry_increment in Hentry.
    destruct (entry m a i) as [prefix|] eqn:Hai.
    - eapply via_bound_holds; [| |exact Hentry].
      + intros old Hold. now apply Hmodel.
      + intros z Hjb. pose proof (Hmodel a i prefix Hai).
        pose proof (Hmodel j b z Hjb). lia.
    - now apply Hmodel.
  Qed.

  (** Incremental closure and its diagonal checks preserve each model of the new constraint. *)
  Lemma incr_close_models : forall i j d m v,
    models m v -> (vz v j - vz v i <= d)%Z -> ngamma (incr_close i j d m) v.
  Proof.
    intros i j d m v Hmodel Hnew.
    assert (Hseed : models (add_cons i j d (add_cons j j 0%Z (add_cons i i 0%Z m))) v).
    { apply models_add_cons; [|exact Hnew].
      apply models_add_cons; [|lia]. apply models_add_cons; [exact Hmodel|lia]. }
    pose proof (increment_models i j d _ v Hseed Hnew) as Hnext.
    unfold incr_close.
    rewrite (nonnegative_models i _ v Hnext), (nonnegative_models j _ v Hnext).
    exact Hnext.
  Qed.

  (** Forgetting removes exactly the row and column of the chosen variable. *)
  Lemma entry_havoc : forall x m i j,
    entry (M.merge (forget_row x) (M.remove (Some x) m) M.empty) i j =
    if K.eqb i (Some x) then None else
      if K.eqb j (Some x) then None else entry m i j.
  Proof.
    intros x m i j. unfold entry. rewrite M.get_merge by reflexivity.
    rewrite M.get_empty. destruct (K.eqb_spec i (Some x)) as [Hi | Hi].
    - subst i. rewrite M.get_remove_same. reflexivity.
    - rewrite M.get_remove_other by exact Hi.
      destruct (M.get i m) as [row|]; cbn [forget_row].
      + destruct (K.eqb_spec j (Some x)) as [Hj | Hj].
        * subst j. apply M.get_remove_same.
        * apply M.get_remove_other. exact Hj.
      + destruct (K.eqb j (Some x)); reflexivity.
  Qed.

  (** A variable update leaves every other zone coordinate unchanged. *)
  Lemma vz_update_other : forall x st c i,
    i <> Some x ->
    vz (fun y => N.num (upd X.eqb st x c y)) i = vz (fun y => N.num (st y)) i.
  Proof.
    intros x st c [y|] Hne; [|reflexivity].
    change (N.num (if X.eqb y x then c else st y) = N.num (st y)).
    destruct (X.eqb_spec y x) as [Heq | Heq]; [subst y; contradiction Hne; reflexivity|].
    reflexivity.
  Qed.

  (** Raw entry lookup ignores labels and also treats an absent row as empty. *)
  Definition raw_entry (m : dbm) (p q : positive) : option Z :=
    M.find q (row_of (M.find p m)).

  Lemma row_leb_spec : forall a b,
    row_leb a b = true <->
    forall q, bound_leb (M.find q (row_of a)) (M.find q (row_of b)) = true.
  Proof.
    intros a b. unfold row_leb. apply M.forall2b_spec. reflexivity.
  Qed.

  Lemma row_leb_empty : row_leb None None = true.
  Proof.
    apply row_leb_spec. intros q. cbn [row_of]. rewrite M.find_empty. reflexivity.
  Qed.

  (** Entrywise comparison visits actual codes, including codes with inconsistent labels. *)
  Lemma leb_entries : forall ma mb,
    leb (Reached ma) (Reached mb) = true <->
    forall p q, bound_leb (raw_entry ma p q) (raw_entry mb p q) = true.
  Proof.
    intros ma mb. cbn [leb].
    rewrite (M.forall2b_spec _ _ row_leb ma mb row_leb_empty).
    split; intros H p; apply row_leb_spec; apply H.
  Qed.

  Lemma raw_entry_empty : forall p q, raw_entry M.empty p q = None.
  Proof.
    intros p q. unfold raw_entry. rewrite M.find_empty. apply M.find_empty.
  Qed.

  Lemma raw_entry_get : forall m i j,
    raw_entry m (K.encode i) (K.encode j) = entry m i j.
  Proof.
    intros m i j. unfold raw_entry, entry.
    rewrite <- (M.get_find _ i m). destruct (M.get i m) as [row|]; cbn [row_of].
    - symmetry. apply M.get_find.
    - apply M.find_empty.
  Qed.

  Lemma bound_leb_refl : forall a, bound_leb a a = true.
  Proof.
    intros [z|]; cbn [bound_leb]; [apply Z.leb_refl|reflexivity].
  Qed.

  Lemma bound_leb_trans : forall a b c,
    bound_leb a b = true -> bound_leb b c = true -> bound_leb a c = true.
  Proof.
    intros [a|] [b|] [c|]; cbn [bound_leb]; try congruence.
    repeat rewrite Z.leb_le. lia.
  Qed.

  Lemma raw_entry_join : forall ma mb p q,
    raw_entry (M.merge row_join ma mb) p q =
    bound_join (raw_entry ma p q) (raw_entry mb p q).
  Proof.
    intros ma mb p q. unfold raw_entry.
    rewrite M.find_merge by reflexivity.
    destruct (M.find p ma) as [ra|], (M.find p mb) as [rb|]; cbn [row_join row_of].
    - apply M.find_merge. reflexivity.
    - rewrite M.find_empty. destruct (M.find q ra); reflexivity.
    - rewrite M.find_empty. reflexivity.
    - rewrite M.find_empty. reflexivity.
  Qed.

  Lemma raw_entry_meet : forall ma mb p q,
    raw_entry (M.merge row_meet ma mb) p q =
    bound_meet (raw_entry ma p q) (raw_entry mb p q).
  Proof.
    intros ma mb p q. unfold raw_entry.
    rewrite M.find_merge by reflexivity.
    destruct (M.find p ma) as [ra|], (M.find p mb) as [rb|]; cbn [row_meet row_of].
    - apply M.find_merge. reflexivity.
    - rewrite M.find_empty. destruct (M.find q ra); reflexivity.
    - rewrite M.find_empty. reflexivity.
    - rewrite M.find_empty. reflexivity.
  Qed.

  Lemma raw_entry_widen : forall ma mb p q,
    raw_entry (M.merge row_widen ma mb) p q =
    bound_widen (raw_entry ma p q) (raw_entry mb p q).
  Proof.
    intros ma mb p q. unfold raw_entry.
    rewrite M.find_merge by reflexivity.
    destruct (M.find p ma) as [ra|], (M.find p mb) as [rb|]; cbn [row_widen row_of].
    - apply M.find_merge. reflexivity.
    - rewrite M.find_merge by reflexivity. reflexivity.
    - rewrite M.find_empty. reflexivity.
    - rewrite M.find_empty. reflexivity.
  Qed.

  Lemma bound_join_ub_l : forall a b, bound_leb a (bound_join a b) = true.
  Proof.
    intros [a|] [b|]; cbn [bound_leb bound_join]; try reflexivity.
    apply Z.leb_le, Z.le_max_l.
  Qed.

  Lemma bound_join_ub_r : forall a b, bound_leb b (bound_join a b) = true.
  Proof.
    intros [a|] [b|]; cbn [bound_leb bound_join]; try reflexivity.
    apply Z.leb_le, Z.le_max_r.
  Qed.

  Lemma bound_meet_lb_l : forall a b, bound_leb (bound_meet a b) a = true.
  Proof.
    intros [a|] [b|]; cbn [bound_leb bound_meet]; try reflexivity.
    - apply Z.leb_le, Z.le_min_l.
    - apply Z.leb_refl.
  Qed.

  Lemma bound_meet_greatest : forall a b c,
    bound_leb c a = true -> bound_leb c b = true ->
    bound_leb c (bound_meet a b) = true.
  Proof.
    intros [a|] [b|] [c|]; cbn [bound_leb bound_meet]; try congruence.
    repeat rewrite Z.leb_le. intros Ha Hb. apply Z.min_glb; assumption.
  Qed.

  Lemma bound_widen_ub_l : forall a b, bound_leb a (bound_widen a b) = true.
  Proof.
    intros [a|] [b|]; cbn [bound_widen bound_leb]; try reflexivity.
    destruct (b <=? a)%Z; cbn [bound_leb]; [apply Z.leb_refl|reflexivity].
  Qed.

  Lemma bound_widen_ub_r : forall a b, bound_leb b (bound_widen a b) = true.
  Proof.
    intros [a|] [b|]; cbn [bound_widen bound_leb]; try reflexivity.
    destruct (b <=? a)%Z eqn:Hle; cbn [bound_leb]; [exact Hle|reflexivity].
  Qed.

  (** Every sparse matrix compares below itself, even when labels are inconsistent. *)
  Lemma leb_refl  : forall a, leb a a = true.
  Proof.
    intros [|m]; [reflexivity|]. apply leb_entries. intros p q. apply bound_leb_refl.
  Qed.

  (** Entrywise comparison is transitive. *)
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof.
    intros [|ma] [|mb] [|mc]; cbn [leb]; try congruence.
    change (leb (Reached ma) (Reached mb) = true ->
      leb (Reached mb) (Reached mc) = true -> leb (Reached ma) (Reached mc) = true).
    rewrite !leb_entries. intros Hab Hbc p q. eapply bound_leb_trans; [apply Hab|apply Hbc].
  Qed.

  (** The unreachable state is below every state. *)
  Lemma bot_least : forall a, leb bot a = true.
  Proof.
    intros a. reflexivity.
  Qed.

  (** The bottom predicate recognizes the unreachable constructor. *)
  Lemma is_bot_bot : is_bot bot = true.
  Proof.
    reflexivity.
  Qed.

  (** Every state recognized as bottom is least. *)
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof.
    intros [|ma] b Hbot; [reflexivity|discriminate Hbot].
  Qed.

  (** Joining weakens every bound supplied by the left state. *)
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof.
    intros [|ma] [|mb]; try apply leb_refl; try reflexivity.
    apply leb_entries. intros p q. rewrite raw_entry_join. apply bound_join_ub_l.
  Qed.

  (** Joining weakens every bound supplied by the right state. *)
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof.
    intros [|ma] [|mb]; try apply leb_refl; try reflexivity.
    apply leb_entries. intros p q. rewrite raw_entry_join. apply bound_join_ub_r.
  Qed.

  (** The empty matrix imposes no upper bounds. *)
  Lemma top_greatest : forall a, leb a top = true.
  Proof.
    intros [|m]; [reflexivity|]. apply leb_entries. intros p q.
    rewrite raw_entry_empty. destruct (raw_entry m p q); reflexivity.
  Qed.

  (** Widening keeps or discards each old finite bound. *)
  Lemma widen_ub_l : forall p a b, leb a (widen p a b) = true.
  Proof.
    intros p a b. unfold widen. destruct (leb b a) eqn:Hle; [apply leb_refl|].
    destruct a as [|ma], b as [|mb]; try apply leb_refl; try reflexivity.
    apply leb_entries. intros i j. rewrite raw_entry_widen. apply bound_widen_ub_l.
  Qed.

  (** A retained old bound is also an upper bound for the candidate. *)
  Lemma widen_ub_r : forall p a b, leb b (widen p a b) = true.
  Proof.
    intros p a b. unfold widen. destruct (leb b a) eqn:Hle; [exact Hle|].
    destruct a as [|ma], b as [|mb]; try apply leb_refl; try reflexivity.
    apply leb_entries. intros i j. rewrite raw_entry_widen. apply bound_widen_ub_r.
  Qed.

  (** A stable candidate returns the exact old representation. *)
  Lemma widen_stable : forall p a b, leb b a = true -> widen p a b = a.
  Proof.
    intros p a b Hle. unfold widen. now rewrite Hle.
  Qed.
  (** A row contributes the distinct pairs formed from its actual stored codes. *)
  Definition row_entry_codes (m : dbm) (p : positive) : list (positive * positive) :=
    match M.find p m with
    | Some row => map (pair p) (M.codes row)
    | None => nil
    end.

  (** Finite-entry counting ignores stored labels at both map levels. *)
  Definition entry_codes (m : dbm) : list (positive * positive) :=
    flat_map (row_entry_codes m) (M.codes m).

  (** The first coordinate of every row entry is its outer stored code. *)
  Lemma row_entry_first : forall m p pq, In pq (row_entry_codes m p) -> fst pq = p.
  Proof.
    intros m p pq Hin. unfold row_entry_codes in Hin.
    destruct (M.find p m) as [row|]; [|contradiction].
    apply in_map_iff in Hin. destruct Hin as [q [Heq Hin]]. now subst pq.
  Qed.

  (** Pairing distinct column codes with one row code preserves distinctness. *)
  Lemma paired_codes_nodup : forall (p : positive) (qs : list positive),
    NoDup qs -> NoDup (map (pair p) qs).
  Proof.
    intros p qs Hcodes. induction Hcodes as [|q qs Hfresh Hcodes IH].
    - constructor.
    - cbn. constructor; [|exact IH]. intro Hin. apply in_map_iff in Hin.
      destruct Hin as [r [Heq Hr]]. injection Heq as Heq. subst r. exact (Hfresh Hr).
  Qed.

  (** Distinct outer codes yield disjoint lists of finite-entry coordinates. *)
  Lemma rows_entry_nodup : forall m ps, NoDup ps ->
    NoDup (flat_map (row_entry_codes m) ps).
  Proof.
    intros m ps Hcodes. induction Hcodes as [|p ps Hfresh Hcodes IH].
    - constructor.
    - cbn [flat_map]. apply NoDup_app; [|exact IH|].
      + unfold row_entry_codes. destruct (M.find p m) as [row|].
        * apply paired_codes_nodup, M.codes_nodup.
        * constructor.
      + intros pq Hfirst Htail. apply in_flat_map in Htail.
        destruct Htail as [q [Hq Hentry]].
        pose proof (row_entry_first m p pq Hfirst) as Hp.
        pose proof (row_entry_first m q pq Hentry) as Hsame.
        apply Hfresh. rewrite <- Hp, Hsame. exact Hq.
  Qed.

  (** No finite raw-code coordinate is counted twice. *)
  Lemma entry_codes_nodup : forall m, NoDup (entry_codes m).
  Proof.
    intro m. unfold entry_codes. apply rows_entry_nodup, M.codes_nodup.
  Qed.

  (** A coordinate occurs exactly when its raw entry is finite. *)
  Lemma entry_codes_spec : forall m p q,
    In (p, q) (entry_codes m) <-> raw_entry m p q <> None.
  Proof.
    intros m p q. split.
    - intro Hin. unfold entry_codes in Hin. apply in_flat_map in Hin.
      destruct Hin as [i [Hi Hin]]. unfold row_entry_codes in Hin.
      destruct (M.find i m) as [row|] eqn:Hrow; [|contradiction].
      apply in_map_iff in Hin. destruct Hin as [j [Heq Hj]].
      injection Heq as Hip Hjq. subst i j.
      unfold raw_entry. rewrite Hrow. cbn [row_of]. now apply M.codes_spec.
    - intro Hentry. unfold raw_entry in Hentry.
      destruct (M.find p m) as [row|] eqn:Hrow; cbn [row_of] in Hentry.
      + unfold entry_codes. apply in_flat_map. exists p. split.
        * apply M.codes_spec. rewrite Hrow. discriminate.
        * unfold row_entry_codes. rewrite Hrow. apply in_map_iff. exists q.
          split; [reflexivity|now apply M.codes_spec].
      + rewrite M.find_empty in Hentry. contradiction.
  Qed.

  (** The flattened coordinate count is the released widening rank. *)
  Lemma entry_codes_rank : forall p m, length (entry_codes m) = wrank p (Reached m).
  Proof.
    intros p m. unfold entry_codes, wrank.
    induction (M.codes m) as [|q qs IH].
    - reflexivity.
    - cbn [flat_map map fold_right]. rewrite length_app, IH.
      unfold row_entry_codes. destruct (M.find q m); cbn; rewrite ?length_map; reflexivity.
  Qed.

  (** Every finite entry retained by widening was already finite in the old matrix. *)
  Lemma widen_codes_incl : forall ma mb,
    incl (entry_codes (M.merge row_widen ma mb)) (entry_codes ma).
  Proof.
    intros ma mb [p q] Hin. apply entry_codes_spec in Hin. apply entry_codes_spec.
    rewrite raw_entry_widen in Hin.
    destruct (raw_entry ma p q) as [d|]; [discriminate|].
    cbn [bound_widen] in Hin. contradiction.
  Qed.

  (** A failed finite Boolean scan provides a member on which its predicate fails. *)
  Lemma forallb_failure : forall (A : Type) (test : A -> bool) xs,
    forallb test xs = false -> exists x, In x xs /\ test x = false.
  Proof.
    intros A test xs. induction xs as [|x xs IH]; intro Hfalse.
    - discriminate Hfalse.
    - cbn in Hfalse. destruct (test x) eqn:Hx.
      + destruct (IH Hfalse) as [y [Hy Htest]]. exists y. split; [now right|exact Htest].
      + exists x. split; [now left|exact Hx].
  Qed.

  (** Failure of entrywise inclusion identifies an old finite bound that widening discards. *)
  Lemma leb_failure_entry : forall ma mb,
    leb (Reached mb) (Reached ma) = false ->
    exists p q, raw_entry ma p q <> None /\
      bound_leb (raw_entry mb p q) (raw_entry ma p q) = false.
  Proof.
    intros ma mb Hfalse.
    destruct (forallb (fun pq =>
      bound_leb (raw_entry mb (fst pq) (snd pq)) (raw_entry ma (fst pq) (snd pq)))
      (entry_codes ma)) eqn:Hscan.
    - assert (Htrue : leb (Reached mb) (Reached ma) = true).
      { apply leb_entries. intros p q.
        destruct (raw_entry ma p q) as [d|] eqn:Hentry.
        - rewrite forallb_forall in Hscan.
          assert (Hin : In (p, q) (entry_codes ma)).
          { apply entry_codes_spec. rewrite Hentry. discriminate. }
          specialize (Hscan (p, q) Hin). cbn in Hscan. now rewrite Hentry in Hscan.
        - destruct (raw_entry mb p q); reflexivity. }
      congruence.
    - apply forallb_failure in Hscan. destruct Hscan as [[p q] [Hin Hfailed]].
      exists p, q. split; [now apply entry_codes_spec|exact Hfailed].
  Qed.

  (** An unstable finite old bound is dropped by the widening callback. *)
  Lemma bound_widen_drops : forall a b,
    bound_leb b a = false -> bound_widen a b = None.
  Proof.
    intros [a|] [b|]; cbn [bound_leb bound_widen]; try congruence.
    intro Hle. now rewrite Hle.
  Qed.

  (** Every unstable widening removes at least one distinct stored coordinate. *)
  Lemma wrank_widen : forall p a b, is_bot a = false -> leb b a = false ->
    wrank p (widen p a b) < wrank p a.
  Proof.
    intros p [|ma] [|mb] Hbot Hunstable; try discriminate.
    unfold widen. rewrite Hunstable.
    change (wrank p (Reached (M.merge row_widen ma mb)) < wrank p (Reached ma)).
    destruct (leb_failure_entry ma mb Hunstable) as [i [j [Hfinite Hfailed]]].
    assert (Hmissing : ~ In (i, j) (entry_codes (M.merge row_widen ma mb))).
    { intro Hin. apply entry_codes_spec in Hin. rewrite raw_entry_widen in Hin.
      rewrite (bound_widen_drops _ _ Hfailed) in Hin. contradiction. }
    assert (Hlength : length ((i, j) :: entry_codes (M.merge row_widen ma mb)) <=
      length (entry_codes ma)).
    { apply NoDup_incl_length.
      - constructor; [exact Hmissing|apply entry_codes_nodup].
      - intros pq [Hpq | Hin].
        + subst pq. now apply entry_codes_spec.
        + exact (widen_codes_incl ma mb pq Hin). }
    change (S (length (entry_codes (M.merge row_widen ma mb))) <=
      length (entry_codes ma)) in Hlength.
    rewrite (entry_codes_rank p (M.merge row_widen ma mb)) in Hlength.
    rewrite (entry_codes_rank p ma) in Hlength. exact Hlength.
  Qed.

  (** Stable widening preserves rank and unstable widening strictly lowers it. *)
  Lemma wrank_widen_le : forall p a b, is_bot a = false -> wrank p (widen p a b) <= wrank p a.
  Proof.
    intros p a b Hbot. destruct (leb b a) eqn:Hstable.
    - rewrite (widen_stable p a b Hstable). reflexivity.
    - apply Nat.lt_le_incl. now apply wrank_widen.
  Qed.
  Lemma narrow_between : forall a b, leb b a = true ->
    leb b (narrow a b) = true /\ leb (narrow a b) a = true.
  Proof.
    intros [|ma] [|mb] Hle; try (split; reflexivity); try discriminate Hle.
    pose proof (proj1 (leb_entries mb ma) Hle) as Hentries.
    split; apply leb_entries; intros p q; cbn [narrow meet].
    - rewrite raw_entry_meet. apply bound_meet_greatest; [apply Hentries|apply bound_leb_refl].
    - rewrite raw_entry_meet. apply bound_meet_lb_l.
  Qed.

  (** Every bound accepted by comparison follows from a source bound. *)
  Lemma ngamma_mono : forall a b v, leb a b = true -> ngamma a v -> ngamma b v.
  Proof.
    intros [|ma] [|mb] v Hle Hmodel; try contradiction; try discriminate Hle.
    pose proof (proj1 (leb_entries ma mb) Hle) as Hentries. intros i j d Hentry.
    specialize (Hentries (K.encode i) (K.encode j)).
    rewrite !raw_entry_get, Hentry in Hentries.
    destruct (entry ma i j) as [c|] eqn:Hsource; [|discriminate Hentries].
    cbn [bound_leb] in Hentries. apply Z.leb_le in Hentries.
    specialize (Hmodel i j c Hsource). lia.
  Qed.

  (** The unreachable constructor has no numeric models. *)
  Lemma ngamma_bot : forall v, ~ ngamma bot v.
  Proof.
    intros v Hmodel. exact Hmodel.
  Qed.

  (** Every numeric store satisfies an empty matrix. *)
  Lemma ngamma_top : forall v, ngamma top v.
  Proof.
    intros v i j d Hentry. unfold entry in Hentry.
    rewrite M.get_empty in Hentry. discriminate Hentry.
  Qed.
  Lemma assign_sound : forall x e s st c,
    ngamma s (fun y => N.num (st y)) -> eval_term L.eval st e = Some c ->
    ngamma (assign x e s) (fun y => N.num (upd X.eqb st x c y)).
  Proof. Admitted. (* STUB *)
  Lemma havoc_sound : forall x s st c, ngamma s (fun y => N.num (st y)) ->
    ngamma (havoc x s) (fun y => N.num (upd X.eqb st x c y)).
  Proof.
    intros x [|m] st c Hmodel; [exact Hmodel|].
    intros i j d Hentry. rewrite entry_havoc in Hentry.
    destruct (K.eqb_spec i (Some x)) as [Hi | Hi]; [discriminate Hentry|].
    destruct (K.eqb_spec j (Some x)) as [Hj | Hj]; [discriminate Hentry|].
    rewrite !vz_update_other by assumption. now apply Hmodel.
  Qed.
  (** Unary entries supply lower and upper bounds for each variable. *)
  Lemma variable_bounds_sound : forall m v x, models m v ->
    in_bnd (fst (variable_bounds m x)) (snd (variable_bounds m x)) (v x).
  Proof.
    intros m v x Hmodel. unfold variable_bounds.
    destruct (entry m (Some x) None) as [lo|] eqn:Hlo;
      destruct (entry m None (Some x)) as [hi|] eqn:Hhi;
      cbn [fst snd in_bnd]; split; try exact I.
    - pose proof (Hmodel (Some x) None lo Hlo). cbn [vz] in *. lia.
    - pose proof (Hmodel None (Some x) hi Hhi). cbn [vz] in *. lia.
    - pose proof (Hmodel (Some x) None lo Hlo). cbn [vz] in *. lia.
    - pose proof (Hmodel None (Some x) hi Hhi). cbn [vz] in *. lia.
  Qed.

  Lemma form_bounds_sound : forall m v f, models m v ->
    in_bnd (fst (form_bounds m f)) (snd (form_bounds m f)) (eval_lin v f).
  Proof.
    intros m v f Hmodel. apply rel_form_bounds_sound.
    intro x. now apply variable_bounds_sound.
  Qed.

  (** Recognized coefficient lists denote exactly their selected difference. *)
  Lemma difference_pair_sound : forall cs v i j,
    difference_pair cs = Some (i, j) -> eval_coef v cs = (vz v j - vz v i)%Z.
  Proof.
    intros cs v i j Hpair.
    destruct cs as [|[x a] cs].
    - inversion Hpair; subst. unfold eval_coef, vz. cbn -[Z.add Z.sub Z.mul Z.opp]. ring.
    - destruct cs as [|[y b] cs].
      + unfold difference_pair in Hpair.
        destruct (a =? 1)%Z eqn:Ha.
        * apply Z.eqb_eq in Ha. subst a. inversion Hpair; subst.
          unfold eval_coef, vz. cbn -[Z.add Z.sub Z.mul Z.opp]. ring.
        * destruct (a =? -1)%Z eqn:Hneg; [|discriminate Hpair].
          apply Z.eqb_eq in Hneg. subst a. inversion Hpair; subst.
          unfold eval_coef, vz. cbn -[Z.add Z.sub Z.mul Z.opp]. ring.
      + destruct cs as [|p cs]; [|discriminate Hpair].
        unfold difference_pair in Hpair.
        destruct (andb (a =? 1)%Z (b =? -1)%Z) eqn:Hsigns.
        * apply andb_true_iff in Hsigns. destruct Hsigns as [Ha Hb].
          apply Z.eqb_eq in Ha. apply Z.eqb_eq in Hb. subst a b.
          inversion Hpair; subst. unfold eval_coef, vz. cbn -[Z.add Z.sub Z.mul Z.opp]. ring.
        * destruct (andb (a =? -1)%Z (b =? 1)%Z) eqn:Hother;
            [|discriminate Hpair].
          apply andb_true_iff in Hother. destruct Hother as [Ha Hb].
          apply Z.eqb_eq in Ha. apply Z.eqb_eq in Hb. subst a b.
          inversion Hpair; subst. unfold eval_coef, vz. cbn -[Z.add Z.sub Z.mul Z.opp]. ring.
  Qed.

  (** Recognition subtracts the two coefficient sums without changing their meaning. *)
  Lemma difference_forms_sound : forall l r v i j,
    difference_forms l r = Some (i, j) ->
    (eval_coef v (coef l) - eval_coef v (coef r) = vz v j - vz v i)%Z.
  Proof.
    intros [ls lc] [rs rc] v i j Hpair. unfold difference_forms in Hpair.
    cbn [coef] in Hpair |- *. destruct ls as [|[x a] xs].
    - destruct (difference_pair rs) as [[u w]|] eqn:Hrecognized;
        [|discriminate Hpair].
      pose proof (difference_pair_sound rs v u w Hrecognized) as Hvalue.
      inversion Hpair; subst. unfold eval_coef in *. cbn in *. lia.
    - destruct rs as [|[y b] ys].
      + pose proof (difference_pair_sound ((x, a) :: xs) v i j Hpair) as Hvalue.
        unfold eval_coef in *. cbn in *. lia.
      + destruct xs as [|p xs], ys as [|q ys]; try discriminate Hpair.
        destruct (andb (a =? 1)%Z (b =? 1)%Z) eqn:Hsigns.
        * apply andb_true_iff in Hsigns. destruct Hsigns as [Ha Hb].
          apply Z.eqb_eq in Ha. apply Z.eqb_eq in Hb. subst a b.
          inversion Hpair; subst. unfold eval_coef, vz. cbn -[Z.add Z.sub Z.mul Z.opp]. ring.
        * destruct (andb (a =? -1)%Z (b =? -1)%Z) eqn:Hother;
            [|discriminate Hpair].
          apply andb_true_iff in Hother. destruct Hother as [Ha Hb].
          apply Z.eqb_eq in Ha. apply Z.eqb_eq in Hb. subst a b.
          inversion Hpair; subst. unfold eval_coef, vz. cbn -[Z.add Z.sub Z.mul Z.opp]. ring.
  Qed.

  (** An accepted range check justifies interpreting a wrapped form as an integer form. *)
  Lemma form_exact_sound : forall m f r v, models m v -> form_exact m f r = true ->
    wrap_into r (eval_lin v f) = eval_lin v f.
  Proof.
    intros m f [|lo hi] v Hmodel Hexact; [reflexivity|].
    apply (rel_wrap_exact_sound (WrapTo lo hi) (form_bounds m f)).
    - now apply form_bounds_sound.
    - exact Hexact.
  Qed.

  (** A refinement retains every current model satisfying the new difference bound. *)
  Lemma refine_sound : forall i j d s v, ngamma s v ->
    (vz v j - vz v i <= d)%Z -> ngamma (refine i j d s) v.
  Proof.
    intros i j d [|m] v Hmodel Hbound; [exact Hmodel|].
    now apply incr_close_models.
  Qed.

  Lemma assume_cmp_sound : forall c i j d s v, ngamma s v ->
    (match c with
     | CLe => (vz v j - vz v i <= d)%Z
     | CLt => (vz v j - vz v i < d)%Z
     | CEq => (vz v j - vz v i = d)%Z
     end) -> ngamma (assume_cmp c i j d s) v.
  Proof.
    intros [| |] i j d s v Hmodel Hbound; unfold assume_cmp.
    - now apply refine_sound.
    - apply refine_sound; [exact Hmodel|lia].
    - apply refine_sound; [apply refine_sound; [exact Hmodel|lia]|lia].
  Qed.

  (** Each supported atom contributes only difference constraints implied by that atom. *)
  Lemma assume_atom_sound : forall s a v, ngamma s v -> atom_holds v a ->
    ngamma (assume_atom s a) v.
  Proof.
    intros [|m] a v Hmodel Hatom; [exact Hmodel|].
    unfold assume_atom. destruct (difference_forms (al a) (ar a))
      as [[i j]|] eqn:Hpair; [|exact Hmodel].
    destruct (andb (form_exact m (al a) (alw a))
      (form_exact m (ar a) (arw a))) eqn:Hexact; [|exact Hmodel].
    apply andb_true_iff in Hexact. destruct Hexact as [Hl Hr].
    unfold atom_holds in Hatom.
    rewrite (form_exact_sound m (al a) (alw a) v Hmodel Hl),
      (form_exact_sound m (ar a) (arw a) v Hmodel Hr) in Hatom.
    pose proof (difference_forms_sound (al a) (ar a) v i j Hpair) as Hdiff.
    apply assume_cmp_sound; [exact Hmodel|].
    unfold eval_lin in Hatom. destruct (acmp a); lia.
  Qed.

  (** A sequence of satisfied atoms retains the same concrete model. *)
  Lemma assume_atoms_sound : forall atoms s v, ngamma s v ->
    Forall (atom_holds v) atoms -> ngamma (fold_left assume_atom atoms s) v.
  Proof.
    induction atoms as [|a atoms IH]; intros s v Hmodel Hatoms.
    - exact Hmodel.
    - inversion Hatoms as [|a' atoms' Ha Htail]; subst.
      apply IH; [now apply assume_atom_sound|exact Htail].
  Qed.

  Lemma assume_sound : forall g es s st cs,
    ngamma s (fun y => N.num (st y)) -> eval_terms L.eval st es = Some cs ->
    L.holds g cs -> ngamma (assume g es s) (fun y => N.num (st y)).
  Proof.
    intros g es [|m] st cs Hmodel Heval Hholds; [exact Hmodel|].
    apply assume_atoms_sound; [exact Hmodel|].
    now apply (F.atoms_sound g es st cs).
  Qed.

  Lemma range_sound : forall e s st c,
    ngamma s (fun y => N.num (st y)) -> eval_term L.eval st e = Some c ->
    in_bnd (fst (range e s)) (snd (range e s)) (N.num c).
  Proof.
    intros e [|m] st c Hmodel Heval; [contradiction|].
    unfold range. destruct (F.lin_of e) as [[f r]|] eqn:Hlinear.
    - rewrite (F.lin_sound st e c f r Heval Hlinear).
      apply rel_wrap_bounds_sound. now apply form_bounds_sound.
    - unfold in_bnd. cbn. tauto.
  Qed.
  Lemma entry_spec : forall m i j,
    entry m i j = match M.get i m with Some row => M.get j row | None => None end.
  Proof.
    reflexivity.
  Qed.

  (** Reached matrices use the difference semantics. *)
  Lemma ngamma_reached : forall m v, ngamma (Reached m) v <-> models m v.
  Proof.
    reflexivity.
  Qed.

  (** Unreachable matrices have no numeric models. *)
  Lemma ngamma_unreached : forall v, ~ ngamma Unreached v.
  Proof.
    intros v Hmodel. exact Hmodel.
  Qed.
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
  TimeFun column_present.
  TimeFun pivot_present.
  TimeFun remember_key.
  TimeFun pivot_keys.
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
  TimeFun entry.
  TimeFun variable_bounds.
  TimeFun form_bounds.
  TimeFun range.
  TimeFun add_cons.
  TimeFun relax_round.
  TimeFun fw_round.
  TimeFun nonnegative.
  TimeFun close_pivots.
  TimeFun close.
  TimeFun increment_row.
  TimeFun incr_close.
  TimeFun difference_pair.
  TimeFun difference_forms.
  TimeFun form_exact.
  TimeFun refine.
  TimeFun assume_cmp.
  TimeFun assume_atom.
  TimeFun assume.
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
  (** A collected row is witnessed by a successful lookup at an outer stored code. *)
  Lemma rows_find : forall m row,
    In row (rows m) <-> exists p, M.find p m = Some row.
  Proof.
    intros m row. split.
    - intro Hin. unfold rows in Hin. apply in_flat_map in Hin.
      destruct Hin as [p [Hp Hin]]. destruct (M.find p m) as [r|] eqn:Hrow.
      + cbn in Hin. destruct Hin as [Heq | Hempty]; [subst r|contradiction].
        now exists p.
      + contradiction.
    - intros [p Hrow]. exact (row_in_rows m p row Hrow).
  Qed.

  (** Support records row codes and column codes independently of their stored labels. *)
  Lemma support_find : forall m p, In p (support m) <->
    M.find p m <> None \/ exists q, raw_entry m q p <> None.
  Proof.
    intros m p. rewrite support_spec. split.
    - intros [Houter | Hinner].
      + left. now apply M.codes_spec.
      + right. apply in_flat_map in Hinner. destruct Hinner as [row [Hrow Hp]].
        apply rows_find in Hrow. destruct Hrow as [q Hrow]. exists q.
        unfold raw_entry. rewrite Hrow. cbn [row_of]. now apply M.codes_spec.
    - intros [Houter | [q Hinner]].
      + left. now apply M.codes_spec.
      + right. unfold raw_entry in Hinner.
        destruct (M.find q m) as [row|] eqn:Hrow; cbn [row_of] in Hinner.
        * apply in_flat_map. exists row. split.
          -- exact (row_in_rows m q row Hrow).
          -- now apply M.codes_spec.
        * rewrite M.find_empty in Hinner. contradiction.
  Qed.

  (** The deduplicated support contains each stored code once. *)
  Lemma support_nodup : forall m, NoDup (support m).
  Proof.
    intro m. unfold support. apply (dedup_nodup positive Pos.eqb Pos.eqb_eq).
    constructor.
  Qed.

  (** A common upper bound for list members bounds their maximum. *)
  Lemma maximum_bound : forall (A : Type) (f : A -> nat) xs upper,
    (forall x, In x xs -> f x <= upper) -> fold_right Nat.max 0 (map f xs) <= upper.
  Proof.
    intros A f xs. induction xs as [|x xs IH]; intros upper Hbound.
    - cbn. lia.
    - cbn. apply Nat.max_lub.
      + apply Hbound. now left.
      + apply IH. intros y Hin. apply Hbound. now right.
  Qed.

  (** Equal support membership gives equal support size and key-bit bounds. *)
  Lemma support_sizes : forall ma mb,
    (forall p, In p (support ma) <-> In p (support mb)) ->
    supp ma = supp mb /\ b ma = b mb.
  Proof.
    intros ma mb Hsame. split.
    - unfold supp. apply Nat.le_antisymm; apply NoDup_incl_length;
        try apply support_nodup.
      + intros p Hin. now apply Hsame.
      + intros p Hin. now apply Hsame.
    - apply Nat.le_antisymm.
      + unfold b at 1. apply maximum_bound. intros p Hin.
        apply support_bits. now apply Hsame.
      + unfold b at 1. apply maximum_bound. intros p Hin.
        apply support_bits. now apply Hsame.
  Qed.

  (** Constraint insertion preserves all outer codes and adds its source code. *)
  Lemma find_add_cons_presence : forall i j d m p,
    M.find p (add_cons i j d m) <> None <-> p = K.encode i \/ M.find p m <> None.
  Proof.
    intros i j d m p. unfold add_cons. rewrite M.find_set.
    destruct (Pos.eqb p (K.encode i)) eqn:Hkey.
    - apply Pos.eqb_eq in Hkey. subst p. split; [intros; now left|intros; discriminate].
    - apply Pos.eqb_neq in Hkey. tauto.
  Qed.

  (** Constraint insertion changes finite-entry presence only at its supplied coordinates. *)
  Lemma raw_add_cons_presence : forall i j d m p q,
    raw_entry (add_cons i j d m) p q <> None <->
    (p = K.encode i /\ q = K.encode j) \/ raw_entry m p q <> None.
  Proof.
    intros i j d m p q. unfold raw_entry, add_cons. rewrite M.find_set.
    destruct (Pos.eqb p (K.encode i)) eqn:Hrow.
    - apply Pos.eqb_eq in Hrow. subst p. cbn [row_of]. rewrite M.find_set.
      destruct (Pos.eqb q (K.encode j)) eqn:Hcol.
      + apply Pos.eqb_eq in Hcol. subst q. split.
        * intros. left. now split.
        * intros. discriminate.
      + apply Pos.eqb_neq in Hcol. rewrite M.get_find. tauto.
    - apply Pos.eqb_neq in Hrow. tauto.
  Qed.

  (** Insertion adds only its two endpoint codes to the support. *)
  Lemma support_add_cons : forall i j d m p,
    In p (support (add_cons i j d m)) <->
    p = K.encode i \/ p = K.encode j \/ In p (support m).
  Proof.
    intros i j d m p. split.
    - intro Hin. apply support_find in Hin. destruct Hin as [Hrow | [q Hentry]].
      + apply find_add_cons_presence in Hrow. destruct Hrow as [Heq | Hrow].
        * now left.
        * right. right. apply support_find. now left.
      + apply raw_add_cons_presence in Hentry. destruct Hentry as [[Hq Hp] | Hentry].
        * right. now left.
        * right. right. apply support_find. right. now exists q.
    - intros [Hrow | [Hcol | Hin]]; apply support_find.
      + left. apply find_add_cons_presence. now left.
      + right. exists (K.encode i). apply raw_add_cons_presence. left. now split.
      + apply support_find in Hin. destruct Hin as [Hrow | [q Hentry]].
        * left. apply find_add_cons_presence. now right.
        * right. exists q. apply raw_add_cons_presence. now right.
  Qed.

  (** The pivot test recognizes precisely the supplied key's membership in raw support. *)
  Lemma pivot_present_support : forall k m,
    pivot_present k m = true <-> In (K.encode k) (support m).
  Proof.
    intros k m. unfold pivot_present. rewrite M.get_find.
    destruct (M.find (K.encode k) m) as [row|] eqn:Hrow.
    - split; [intros|reflexivity]. apply support_find. left. rewrite Hrow. discriminate.
    - rewrite (M.existsb_spec (M.t Z) (column_present k) m). split.
      + intros [p [row [Hp Hcol]]]. apply support_find. right. exists p.
        unfold raw_entry. rewrite Hp. cbn [row_of].
        unfold column_present in Hcol. rewrite M.get_find in Hcol.
        destruct (M.find (K.encode k) row); congruence.
      + intro Hin. apply support_find in Hin. destruct Hin as [Hfound | [p Hentry]].
        * rewrite Hrow in Hfound. contradiction.
        * unfold raw_entry in Hentry. destruct (M.find p m) as [r|] eqn:Hp.
          -- exists p, r. split; [exact Hp|]. unfold column_present. rewrite M.get_find.
             cbn [row_of] in Hentry. destruct (M.find (K.encode k) r); congruence.
          -- cbn [row_of] in Hentry. rewrite M.find_empty in Hentry. contradiction.
  Qed.

  (** Relaxation retains precisely the existing outer rows. *)
  Lemma find_relax_presence : forall k m p,
    M.find p (relax_round k m) <> None <-> M.find p m <> None.
  Proof.
    intros k m p. unfold relax_round. rewrite M.find_merge by reflexivity.
    rewrite M.find_empty. destruct (M.find p m); cbn [round_row]; split; congruence.
  Qed.

  (** A relaxed coordinate is old or joins an incoming and an outgoing pivot edge. *)
  Lemma raw_relax_presence : forall k m p q,
    raw_entry (relax_round k m) p q <> None <->
    raw_entry m p q <> None \/
      (raw_entry m p (K.encode k) <> None /\ raw_entry m (K.encode k) q <> None).
  Proof.
    intros k m p q. unfold raw_entry, relax_round.
    rewrite M.find_merge by reflexivity. rewrite M.find_empty.
    destruct (M.find p m) as [row|] eqn:Hrow; cbn [round_row row_of].
    - rewrite !M.get_find. destruct (M.find (K.encode k) row) as [a|] eqn:Hentry.
      + rewrite M.find_merge by reflexivity.
        destruct (M.find q row), (M.find q (row_of (M.find (K.encode k) m)));
          cbn [via_bound]; intuition congruence.
      + tauto.
    - rewrite !M.find_empty. tauto.
  Qed.

  (** Relaxing through a pivot adds no code and deletes no supported code. *)
  Lemma support_relax : forall k m p,
    In p (support (relax_round k m)) <-> In p (support m).
  Proof.
    intros k m p. rewrite !support_find. split.
    - intros [Hrow | [q Hentry]].
      + left. now apply find_relax_presence in Hrow.
      + apply raw_relax_presence in Hentry. right.
        destruct Hentry as [Hentry | [Hprefix Hsuffix]].
        * now exists q.
        * now exists (K.encode k).
    - intros [Hrow | [q Hentry]].
      + left. now apply find_relax_presence.
      + right. exists q. apply raw_relax_presence. now left.
  Qed.

  (** Materializing an already-supported pivot diagonal leaves support unchanged. *)
  Lemma support_round : forall k m p,
    In p (support (fw_round k m)) <-> In p (support m).
  Proof.
    intros k m p. unfold fw_round. rewrite support_relax.
    destruct (pivot_present k m) eqn:Hpresent; [|reflexivity].
    apply pivot_present_support in Hpresent. rewrite support_add_cons.
    split.
    - intros [Heq | [Heq | Hin]]; subst; assumption.
    - intro Hin. right. now right.
  Qed.

  (** Every member of a list is bounded by its maximum. *)
  Lemma maximum_raw_member : forall xs n,
    In n xs -> n <= fold_right Nat.max 0 xs.
  Proof.
    intros xs. induction xs as [|x xs IH]; intros n Hin.
    - contradiction.
    - cbn in Hin. cbn. destruct Hin as [Heq | Hin].
      + subst n. apply Nat.le_max_l.
      + eapply Nat.le_trans; [exact (IH n Hin)|apply Nat.le_max_r].
  Qed.

  (** A uniform upper bound for a list bounds its maximum. *)
  Lemma maximum_raw_bound : forall xs upper,
    (forall n, In n xs -> n <= upper) -> fold_right Nat.max 0 xs <= upper.
  Proof.
    intros xs. induction xs as [|x xs IH]; intros upper Hbound.
    - cbn. lia.
    - cbn. apply Nat.max_lub.
      + apply Hbound. now left.
      + apply IH. intros n Hin. apply Hbound. now right.
  Qed.

  (** Every finite raw entry satisfies the matrix's integer-bit bound. *)
  Lemma ell_entry : forall m p q z,
    raw_entry m p q = Some z -> Z.size_nat z <= ell m.
  Proof.
    intros m p q z Hentry. unfold raw_entry in Hentry.
    destruct (M.find p m) as [row|] eqn:Hrow; cbn [row_of] in Hentry.
    - unfold ell. apply maximum_raw_member. apply in_flat_map.
      exists row. split; [exact (row_in_rows m p row Hrow)|].
      apply in_map_iff. exists q. split.
      + now rewrite Hentry.
      + apply M.codes_spec. rewrite Hentry. discriminate.
    - rewrite M.find_empty in Hentry. discriminate.
  Qed.

  (** Bounding every finite raw entry bounds the matrix's integer-bit maximum. *)
  Lemma ell_bound : forall m upper,
    (forall p q z, raw_entry m p q = Some z -> Z.size_nat z <= upper) ->
    ell m <= upper.
  Proof.
    intros m upper Hbound. unfold ell. apply maximum_raw_bound.
    intros n Hin. apply in_flat_map in Hin. destruct Hin as [row [Hrow Hin]].
    apply in_map_iff in Hin. destruct Hin as [q [Heq Hq]].
    apply rows_find in Hrow. destruct Hrow as [p Hrow].
    destruct (M.find q row) as [z|] eqn:Hentry.
    - subst n. apply (Hbound p q z). unfold raw_entry. rewrite Hrow. exact Hentry.
    - cbn in Heq. lia.
  Qed.

  (** An integer's absolute value fits strictly below its bit-length power of two. *)
  Lemma zbits_upper : forall z, Z.abs_nat z < 2 ^ Z.size_nat z.
  Proof.
    intros [|p|p]; cbn [Z.abs_nat Z.size_nat].
    - change (0 < 1). lia.
    - apply Pos.size_nat_upper.
    - apply Pos.size_nat_upper.
  Qed.

  (** Any strict power-of-two bound also bounds the integer's bit length. *)
  Lemma zbits_least : forall z n,
    Z.abs_nat z < 2 ^ n -> Z.size_nat z <= n.
  Proof.
    intros [|p|p] n Hbound; cbn [Z.abs_nat Z.size_nat] in *.
    - lia.
    - now apply Pos.size_nat_least.
    - now apply Pos.size_nat_least.
  Qed.

  (** Adding two integers with a common bit bound needs at most one further bit. *)
  Lemma zbits_add_bound : forall x y upper,
    Z.size_nat x <= upper -> Z.size_nat y <= upper ->
    Z.size_nat (x + y)%Z <= upper + 1.
  Proof.
    intros x y upper Hx Hy.
    pose proof (zbits_upper x) as Hxabs. pose proof (zbits_upper y) as Hyabs.
    assert (Hxp : 2 ^ Z.size_nat x <= 2 ^ upper).
    { apply Nat.pow_le_mono_r; lia. }
    assert (Hyp : 2 ^ Z.size_nat y <= 2 ^ upper).
    { apply Nat.pow_le_mono_r; lia. }
    assert (Htriangle : Z.abs_nat (x + y)%Z <= Z.abs_nat x + Z.abs_nat y).
    { apply (proj2 (Nat2Z.inj_le _ _)).
      rewrite Nat2Z.inj_add, !Zabs2Nat.id_abs. apply Z.abs_triangle. }
    apply zbits_least. replace (upper + 1) with (S upper) by lia.
    cbn [Nat.pow]. lia.
  Qed.

  (** Tightening a bound selects one of its inputs and preserves their common bit bound. *)
  Lemma lower_bound_size : forall d old upper,
    Z.size_nat d <= upper ->
    (forall z, old = Some z -> Z.size_nat z <= upper) ->
    Z.size_nat (lower_bound d old) <= upper.
  Proof.
    intros d [z|] upper Hd Hold; cbn [lower_bound].
    - destruct (Z.leb_spec0 d z) as [Hle | Hgt].
      + now rewrite Z.min_l by exact Hle.
      + rewrite Z.min_r by lia. apply Hold. reflexivity.
    - exact Hd.
  Qed.

  (** Insertion changes only the supplied raw coordinate, retaining its tighter bound. *)
  Lemma raw_entry_add_cons : forall i j d m p q,
    raw_entry (add_cons i j d m) p q =
    if Pos.eqb p (K.encode i) then
      if Pos.eqb q (K.encode j) then Some (lower_bound d (raw_entry m p q))
      else raw_entry m p q
    else raw_entry m p q.
  Proof.
    intros i j d m p q. unfold raw_entry, add_cons. rewrite M.find_set.
    destruct (Pos.eqb p (K.encode i)) eqn:Hrow; [|reflexivity].
    apply Pos.eqb_eq in Hrow. subst p. cbn [row_of]. rewrite M.find_set.
    destruct (Pos.eqb q (K.encode j)) eqn:Hcol.
    - apply Pos.eqb_eq in Hcol. subst q. now rewrite !M.get_find.
    - now rewrite M.get_find.
  Qed.

  (** Inserting one constraint preserves a common bit bound for old and new entries. *)
  Lemma ell_add_cons : forall i j d m upper,
    ell m <= upper -> Z.size_nat d <= upper -> ell (add_cons i j d m) <= upper.
  Proof.
    intros i j d m upper Hm Hd. apply ell_bound. intros p q z Hentry.
    rewrite raw_entry_add_cons in Hentry.
    destruct (Pos.eqb p (K.encode i)).
    - destruct (Pos.eqb q (K.encode j)).
      + injection Hentry as <-. apply lower_bound_size; [exact Hd|].
        intros old Hold. eapply Nat.le_trans; [eapply ell_entry; exact Hold|exact Hm].
      + eapply Nat.le_trans; [eapply ell_entry; exact Hentry|exact Hm].
    - eapply Nat.le_trans; [eapply ell_entry; exact Hentry|exact Hm].
  Qed.

  (** Raw relaxation considers the old edge and the two edges through the pivot. *)
  Lemma raw_entry_relax : forall k m p q,
    raw_entry (relax_round k m) p q =
    match raw_entry m p (K.encode k) with
    | Some a => via_bound a (raw_entry m p q) (raw_entry m (K.encode k) q)
    | None => raw_entry m p q
    end.
  Proof.
    intros k m p q. unfold raw_entry, relax_round.
    rewrite M.find_merge by reflexivity. rewrite M.find_empty.
    destruct (M.find p m) as [row|]; cbn [round_row row_of].
    - rewrite !M.get_find. destruct (M.find (K.encode k) row).
      + now rewrite M.find_merge by reflexivity.
      + reflexivity.
    - now rewrite !M.find_empty.
  Qed.

  (** One sparse relaxation adds at most one bit to the maximum stored bound. *)
  Lemma ell_relax : forall k m, ell (relax_round k m) <= ell m + 1.
  Proof.
    intros k m. apply ell_bound. intros p q z Hentry.
    rewrite raw_entry_relax in Hentry.
    destruct (raw_entry m p (K.encode k)) as [a|] eqn:Ha.
    - unfold via_bound in Hentry.
      destruct (raw_entry m (K.encode k) q) as [c|] eqn:Hc.
      + injection Hentry as <-. apply lower_bound_size.
        * apply zbits_add_bound; [exact (ell_entry m p (K.encode k) a Ha)|
            exact (ell_entry m (K.encode k) q c Hc)].
        * intros old Hold. pose proof (ell_entry m p q old Hold). lia.
      + pose proof (ell_entry m p q z Hentry). lia.
    - pose proof (ell_entry m p q z Hentry). lia.
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
  Proof.
    exact fw_round_models.
  Qed.
  Lemma wf_fw_round : forall k m, dbm_wf m -> dbm_wf (fw_round k m).
  Proof. Admitted. (* STUB *)
  Lemma wf_add_cons : forall i j d m, dbm_wf m -> dbm_wf (add_cons i j d m).
  Proof. Admitted. (* STUB *)
  Lemma wf_incr_close : forall i j d m, dbm_wf m ->
    match incr_close i j d m with Unreached => True | Reached m' => dbm_wf m' end.
  Proof. Admitted. (* STUB *)
  Lemma close_sound : forall m v, models m v -> ngamma (close m) v.
  Proof.
    exact close_models.
  Qed.
  Lemma close_bot : forall m, close m = Unreached -> forall v, ~ models m v.
  Proof.
    intros m Hclose v Hmodel. pose proof (close_sound m v Hmodel) as Hnext.
    rewrite Hclose in Hnext. exact Hnext.
  Qed.
  Lemma incr_close_sound : forall i j d m v,
    models m v -> (vz v j - vz v i <= d)%Z -> ngamma (incr_close i j d m) v.
  Proof.
    exact incr_close_models.
  Qed.
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
  (** Reflected key equality supplies the Boolean test used by deduplication. *)
  Lemma key_eqb_true : forall x y, K.eqb x y = true <-> x = y.
  Proof.
    intros x y. destruct (K.eqb_spec x y); split; congruence.
  Qed.

  (** Consistent stored labels name codes actually present in their map. *)
  Lemma elements_code : forall A (m : M.t A) k, M.wf m ->
    In k (map fst (M.elements m)) -> In (K.encode k) (M.codes m).
  Proof.
    intros A m k Hwf Hin. apply in_map_iff in Hin.
    destruct Hin as [[q value] [Hq Hin]]. cbn in Hq. subst q.
    apply M.codes_spec. rewrite <- (M.get_find A k m).
    pose proof (proj1 (M.elements_spec A m k value Hwf) Hin) as Hget.
    rewrite Hget. discriminate.
  Qed.

  (** Pivot collection keeps each key once. *)
  Lemma keys_nodup : forall m, NoDup (keys m).
  Proof.
    intro m. unfold keys. apply (dedup_nodup K.t K.eqb key_eqb_true).
    constructor.
  Qed.

  (** Injective encoding preserves distinct pivot keys. *)
  Lemma encoded_keys_nodup : forall ks, NoDup ks -> NoDup (map K.encode ks).
  Proof.
    intros ks Hkeys. induction Hkeys as [|k ks Hfresh Hkeys IH].
    - constructor.
    - cbn. constructor; [|exact IH]. intro Hin. apply in_map_iff in Hin.
      destruct Hin as [q [Hcode Hq]]. apply K.encode_inj in Hcode.
      subst q. exact (Hfresh Hq).
  Qed.

  (** Each consistent pivot label names a code in the matrix support. *)
  Lemma keys_support : forall m k, dbm_wf m -> In k (keys m) ->
    In (K.encode k) (support m).
  Proof.
    intros m k [Houter Hrows] Hkey. unfold keys in Hkey.
    rewrite (dedup_membership K.t K.eqb key_eqb_true) in Hkey.
    destruct Hkey as [Hkey | Hempty]; [|contradiction].
    apply in_app_iff in Hkey. apply support_spec. destruct Hkey as [Hkey | Hkey].
    - left. now apply elements_code.
    - right. apply in_flat_map in Hkey.
      destruct Hkey as [[i row] [Hrow Hkey]]. cbn in Hkey.
      pose proof (proj1 (M.elements_spec (M.t Z) m i row Houter) Hrow) as Hget.
      rewrite M.get_find in Hget.
      apply in_flat_map. exists row. split.
      + exact (row_in_rows m (K.encode i) row Hget).
      + apply elements_code; [exact (Hrows (K.encode i) row Hget)|exact Hkey].
  Qed.
  Lemma bits_fw_round_step : forall k m, ell (fw_round k m) <= ell m + 1.
  Proof.
    intros k m. unfold fw_round. destruct (pivot_present k m).
    - eapply Nat.le_trans; [apply ell_relax|].
      assert (Hseed : ell (add_cons k k 0%Z m) <= ell m).
      { apply ell_add_cons; [lia|cbn [Z.size_nat]; lia]. }
      lia.
    - apply ell_relax.
  Qed.
  Lemma bits_fw_trace_le : forall ks m k a, dbm_wf m ->
    In (k, a) (fw_trace ks m) ->
    ell a <= ell m + Nat.log2 (supp m) + 1.
  Proof. Admitted. (* STUB *)
  Lemma supp_fw_round : forall k m,
    supp (fw_round k m) = supp m /\ b (fw_round k m) = b m.
  Proof.
    intros k m. apply support_sizes, support_round.
  Qed.
  (** A consistent matrix has no more pivot keys than codes in its support. *)
  Lemma keys_le : forall m, dbm_wf m -> length (keys m) <= supp m.
  Proof.
    intros m Hwf. unfold supp.
    rewrite <- (length_map K.encode (keys m)). apply NoDup_incl_length.
    - apply encoded_keys_nodup, keys_nodup.
    - intros p Hin. apply in_map_iff in Hin. destruct Hin as [k [Hcode Hkey]].
      subst p. now apply keys_support.
  Qed.
  (** Closure pays its pivot list, the performed rounds and the final diagonal. *)
  Lemma T2_close : forall m, dbm_wf m ->
    (T_close m <= k_zone * (N.of_nat ((supp m + 1)^2 * (b m + ell m + 1)) +
      fold_right N.add 0%N (map (fun km => T_fw_round (fst km) (snd km))
        (fw_trace (keys m) m))))%N.
  Proof. Admitted. (* STUB *)
End ZoneT.
