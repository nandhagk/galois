(** * Map lattices

    Sparse environments use explicit defaults for absent keys.
    For example, joining top-default maps drops a binding present on one side.
    Builds on: LatticeSig and MapSig. *)

From Stdlib Require Import Bool List Arith NArith Lia.
From Argent Require Import Time Tactics Std BigO.
From Galois.Base Require Import KeySig MapSig.
From Galois.Lattice Require Import LatticeSig.

Module MapLatticeCode (K : KEY_OPS) (M : MAP_OPS K) (L : LATTICE_OPS)
    <: LATTICE_OPS.
  Definition t := M.t L.t.
  Definition default (x : option L.t) : L.t :=
    match x with Some a => a | None => L.bot end.
  Definition leb (x y : t) : bool :=
    M.forall2b (fun a b =>
      L.leb (match a with Some v => v | None => L.bot end)
        (match b with Some v => v | None => L.bot end)) x y.
  Definition bot : t := M.empty.
  Definition is_bot (x : t) : bool := negb (M.existsb (fun a => negb (L.is_bot a)) x).
  Definition join (x y : t) : t :=
    M.merge (fun a b =>
      match a, b with
      | None, None => None
      | Some a, None => Some a
      | None, Some b => Some b
      | Some a, Some b => Some (L.join a b)
      end) x y.
End MapLatticeCode.

Module MapLattice (K : KEY) (M : MAP K) (L : LATTICE) <: LATTICE.
  Include MapLatticeCode K M L.
  Definition read (m : t) (k : positive) := default (M.find k m).
  Lemma leb_read : forall a b, leb a b = true <-> forall k, L.leb (read a k) (read b k) = true.
  Proof.
    intros a b; unfold leb, read.
    apply M.forall2b_spec; cbn [default]; apply L.leb_refl.
  Qed.
  Lemma leb_refl : forall a, leb a a = true.
  Proof. intro a; apply leb_read; intro k; apply L.leb_refl. Qed.
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof.
    intros a b c Hab Hbc; apply leb_read; intro k.
    eapply L.leb_trans; [apply (proj1 (leb_read a b) Hab)|apply (proj1 (leb_read b c) Hbc)].
  Qed.
  Lemma bot_least : forall a, leb bot a = true.
  Proof.
    intro a; apply leb_read; intro k; unfold read, bot; rewrite M.find_empty; apply L.bot_least.
  Qed.
  Lemma is_bot_bot : is_bot bot = true.
  Proof.
    unfold is_bot, bot. apply Bool.negb_true_iff.
    destruct (M.existsb (fun a => negb (L.is_bot a)) M.empty) eqn:Hex; auto.
    apply M.existsb_spec in Hex. destruct Hex as [k [a [Hfind _]]].
    rewrite M.find_empty in Hfind. discriminate.
  Qed.
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof.
    intros a b Hbot. apply leb_read; intro k. unfold read.
    destruct (M.find k a) as [v|] eqn:Hfind; cbn [default].
    - apply L.is_bot_least. destruct (L.is_bot v) eqn:Hv; auto.
      unfold is_bot in Hbot. apply Bool.negb_true_iff in Hbot.
      assert (Hex : M.existsb (fun x => negb (L.is_bot x)) a = true).
      { apply M.existsb_spec. exists k, v. rewrite Hfind, Hv. auto. }
      congruence.
    - apply L.bot_least.
  Qed.
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof.
    intros a b; apply leb_read; intro k; unfold read, join.
    rewrite M.find_merge by reflexivity.
    destruct (M.find k a), (M.find k b); cbn [default];
      try apply L.leb_refl; try apply L.bot_least; apply L.join_ub_l.
  Qed.
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof.
    intros a b; apply leb_read; intro k; unfold read, join.
    rewrite M.find_merge by reflexivity.
    destruct (M.find k a), (M.find k b); cbn [default];
      try apply L.leb_refl; try apply L.bot_least; apply L.join_ub_r.
  Qed.
End MapLattice.

Module MapLatticeT (K : KEY_T) (M : MAP_T K) (L : LATTICE_T) <: LATTICE_T.
  Include MapLattice K M L.

  TimeFun leb.
  TimeFun is_bot.
  TimeFun join.

  Definition size (m : t) : nat :=
    M.nodes m + fold_right Nat.add 1 (List.map (fun p =>
      match M.find p m with Some a => L.size a + 1 | None => 0 end) (M.codes m)).
  Definition c_lat : N :=
    (64 * (M.c_map + 1) * (L.c_lat + 1) * N.of_nat (L.size L.bot + 1))%N.
  (** The lattice constant pays for at least one call. *)
  Lemma c_lat_pos : (1 <= c_lat)%N.
  Proof.
    unfold c_lat. pose proof L.c_lat_pos.
    assert (Hbot : (1 <= N.of_nat (L.size L.bot + 1))%N) by lia. nia.
  Qed.

  (** Each present code pays for its value and one binding cell. *)
  Local Definition lookup_size (m : t) (p : positive) : nat :=
    match M.find p m with Some a => L.size a + 1 | None => 0 end.

  Local Definition value_size (m : t) : nat :=
    fold_right Nat.add 0 (List.map (lookup_size m) (M.codes m)).

  (** The declared size counts skeleton nodes, present values, and one base unit. *)
  Local Lemma size_values m : size m = M.nodes m + value_size m + 1.
  Proof.
    assert (Hbase : forall xs, fold_right Nat.add 1 xs = fold_right Nat.add 0 xs + 1).
    { induction xs as [|x xs IH]; cbn [fold_right]; lia. }
    unfold size, value_size, lookup_size. rewrite Hbase. lia.
  Qed.

  (** Pointwise charges sum to the corresponding weighted code budget. *)
  Local Lemma code_sum_bound (f : positive -> N) (g : positive -> nat) c ps :
    (forall p, In p ps -> (f p <= c * N.of_nat (g p))%N) ->
    (fold_right N.add 0 (List.map f ps) <=
      c * N.of_nat (fold_right Nat.add 0%nat (List.map g ps)))%N.
  Proof.
    induction ps as [|p ps IH]; intro Hbound.
    - cbn [List.map fold_right]. lia.
    - cbn [List.map fold_right]. rewrite Nat2N.inj_add.
      specialize (IH (fun q Hq => Hbound q (or_intror Hq))).
      specialize (Hbound p (or_introl eq_refl)). nia.
  Qed.

  (** Existential callbacks are charged once for every present code. *)
  Local Lemma exists_charge_bound (f : L.t -> N) c m :
    (forall a, (f a <= c * N.of_nat (L.size a + 1))%N) ->
    (fold_right N.add 0 (List.map (fun p =>
      match M.find p m with Some a => f a | None => 0 end) (M.codes m)) <=
      c * N.of_nat (value_size m))%N.
  Proof.
    intro Hbound. unfold value_size. apply code_sum_bound.
    intros p Hin. unfold lookup_size. destruct (M.find p m); [apply Hbound | lia].
  Qed.

  (** Weighted concatenation adds the two list budgets. *)
  Local Lemma weighted_sum_app (f : positive -> nat) ps qs :
    fold_right Nat.add 0 (List.map f (ps ++ qs)) =
      fold_right Nat.add 0 (List.map f ps) + fold_right Nat.add 0 (List.map f qs).
  Proof.
    induction ps as [|p ps IH]; cbn [List.map fold_right app]; lia.
  Qed.

  (** Summing pointwise sums separates the two weights. *)
  Local Lemma weighted_sum_add (f g : positive -> nat) ps :
    fold_right Nat.add 0 (List.map (fun p => f p + g p) ps) =
      fold_right Nat.add 0 (List.map f ps) + fold_right Nat.add 0 (List.map g ps).
  Proof.
    induction ps as [|p ps IH]; cbn [List.map fold_right]; lia.
  Qed.

  (** A duplicate-free sample cannot exceed the weight of its support. *)
  Local Lemma weighted_sample (f : positive -> nat) ps :
    NoDup ps -> forall support,
    (forall p, In p ps -> ~ In p support -> f p = 0) ->
    fold_right Nat.add 0 (List.map f ps) <=
      fold_right Nat.add 0 (List.map f support).
  Proof.
    intro Hnodup. induction Hnodup as [|p ps Hnot Hnodup IH]; intros support Hsupport.
    - cbn [List.map fold_right]. lia.
    - destruct (in_dec Pos.eq_dec p support) as [Hin | Hout].
      + apply in_split in Hin as [xs [ys Heq]]. subst support.
        assert (Htail : forall q, In q ps -> ~ In q (xs ++ ys) -> f q = 0).
        { intros q Hq Houtside. apply Hsupport; [right; exact Hq |].
          rewrite !in_app_iff in *. cbn [In]. intuition congruence. }
        specialize (IH (xs ++ ys) Htail).
        rewrite weighted_sum_app in IH |- *. cbn [List.map fold_right]. lia.
      + cbn [List.map fold_right]. rewrite (Hsupport p (or_introl eq_refl) Hout).
        apply IH. intros q Hq Houtside. apply Hsupport; [right; exact Hq | exact Houtside].
  Qed.

  (** Sampling raw code lookups charges each stored value at most once. *)
  Local Lemma lookup_sample m ps : NoDup ps ->
    fold_right Nat.add 0 (List.map (lookup_size m) ps) <= value_size m.
  Proof.
    intro Hnodup. unfold value_size. apply weighted_sample; [exact Hnodup |].
    intros p Hin Houtside. unfold lookup_size.
    destruct (M.find p m) as [a |] eqn:Hfind; [|reflexivity].
    exfalso. apply Houtside. apply M.codes_spec. rewrite Hfind. discriminate.
  Qed.

  (** The two code lists duplicate each map's value budget at most twice. *)
  Local Lemma union_values a b :
    fold_right Nat.add 0 (List.map (fun p => lookup_size a p + lookup_size b p)
      (M.codes a ++ M.codes b)) <= 2 * (value_size a + value_size b).
  Proof.
    rewrite weighted_sum_add, !weighted_sum_app.
    pose proof (lookup_sample a (M.codes b) (M.codes_nodup L.t b)) as Hab.
    pose proof (lookup_sample b (M.codes a) (M.codes_nodup L.t a)) as Hba.
    unfold value_size in *. lia.
  Qed.

  (** A relational callback budget is paid by both raw maps' value sums. *)
  Local Lemma union_charge_bound (f : positive -> N) c a b :
    (forall p, In p (M.codes a ++ M.codes b) ->
      (f p <= c * N.of_nat (lookup_size a p + lookup_size b p))%N) ->
    (fold_right N.add 0 (List.map f (M.codes a ++ M.codes b)) <=
      2 * c * N.of_nat (value_size a + value_size b))%N.
  Proof.
    intro Hcallback.
    pose proof (code_sum_bound f (fun p => lookup_size a p + lookup_size b p)
      c (M.codes a ++ M.codes b) Hcallback) as Hsum.
    pose proof (union_values a b) as Hvalues. apply time_of_nat_le in Hvalues.
    rewrite Nat2N.inj_mul in Hvalues. nia.
  Qed.

  (** Every code in either map has a present binding on at least one side. *)
  Local Lemma union_present (a b : t) p : In p (M.codes a ++ M.codes b) ->
    M.find p a <> None \/ M.find p b <> None.
  Proof.
    rewrite in_app_iff. intros [Hin | Hin].
    - left. apply M.codes_spec; exact Hin.
    - right. apply M.codes_spec; exact Hin.
  Qed.

  (** A shared scalar rate absorbs traversal, callbacks, and the outer call. *)
  Local Lemma relational_budget (cm rate nodes values budget base callbacks clock : N) :
    (1 <= rate -> 1 <= budget -> nodes + values <= budget ->
      base <= rate -> callbacks <= 2 * rate * values ->
      clock <= cm * (base * nodes + callbacks) ->
      1 + clock <= 16 * (cm + 1) * rate * budget)%N.
  Proof.
    intros Hrate Hpositive Hsize Hbase Hcallbacks Hclock.
    assert (Hnodes : (base * nodes <= rate * nodes)%N).
    { apply N.mul_le_mono_r; exact Hbase. }
    assert (Hweighted : (rate * (nodes + values) <= rate * budget)%N).
    { apply N.mul_le_mono_l; exact Hsize. }
    assert (Hinside : (base * nodes + callbacks <= 2 * rate * budget)%N).
    { clear - Hnodes Hweighted Hcallbacks. nia. }
    assert (Hbody : (clock <= cm * (2 * rate * budget))%N).
    { eapply N.le_trans; [exact Hclock |]. apply N.mul_le_mono_l; exact Hinside. }
    assert (Hunit : (1 <= rate * budget)%N).
    { clear - Hrate Hpositive. nia. }
    replace (cm * (2 * rate * budget))%N with (2 * cm * (rate * budget))%N in Hbody by ring.
    replace (16 * (cm + 1) * rate * budget)%N with
      (16 * cm * (rate * budget) + 16 * (rate * budget))%N by ring.
    remember (rate * budget)%N as units eqn:Hunits in Hunit, Hbody |- *.
    clear - Hunit Hbody. nia.
  Qed.

  (** Comparison charges both skeletons and every compared stored value. *)
  Lemma T_leb_le : forall a b,
    (T_leb a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b. time_unfold @T_leb.
    set (rate := (4 * (L.c_lat + 1) * N.of_nat (L.size L.bot + 1))%N).
    lazymatch goal with
    | |- context [M.T_forall2b ?f ?Tf a b] =>
        pose proof (M.T_forall2b_sum_le L.t L.t f Tf a b) as Hclock;
        assert (Hcallback : forall p, In p (M.codes a ++ M.codes b) ->
          (Tf (M.find p a) (M.find p b) <= rate *
            N.of_nat (lookup_size a p + lookup_size b p))%N) by
          (intros p Hin; clear Hclock; pose proof (union_present a b p Hin) as Hpresent;
           unfold rate, lookup_size; destruct (M.find p a) as [x |], (M.find p b) as [y |];
           time_cbn; try (destruct Hpresent; contradiction);
           lazymatch goal with
           | |- context [L.T_leb ?v ?w] => pose proof (L.T_leb_le v w)
           end;
           rewrite !Nat2N.inj_add in *; nia);
        pose proof (union_charge_bound (fun p => Tf (M.find p a) (M.find p b))
          rate a b Hcallback) as Hsum
    end.
    time_cbn_all. fold rate in Hsum.
    assert (Hrate : (1 <= rate)%N).
    { unfold rate. clear Hclock Hsum Hcallback. rewrite Nat2N.inj_add. nia. }
    assert (Hbase : (1 + L.T_leb L.bot L.bot + 1 <= rate)%N).
    { pose proof (L.T_leb_le L.bot L.bot) as Hempty.
      unfold rate. clear - Hempty. rewrite !Nat2N.inj_add in *. nia. }
    assert (Hbudget : (N.of_nat (M.nodes a + M.nodes b + 1) +
      N.of_nat (value_size a + value_size b) <= N.of_nat (size a + size b + 1))%N).
    { rewrite !size_values. rewrite !Nat2N.inj_add. lia. }
    replace c_lat with (16 * (M.c_map + 1) * rate)%N by (unfold c_lat, rate; ring).
    eapply relational_budget; [exact Hrate | | exact Hbudget | exact Hbase | exact Hsum |].
    - lia.
    - exact Hclock.
  Qed.
  (** Joining charges the component joins over both raw maps' stored codes. *)
  Lemma T_join_le : forall a b,
    (T_join a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b. time_unfold @T_join.
    lazymatch goal with
    | |- context [M.T_merge ?f ?Tf a b] =>
        pose proof (M.T_merge_sum_le L.t L.t L.t f Tf a b) as Hclock;
        assert (Hcallback : forall p, In p (M.codes a ++ M.codes b) ->
          (Tf (M.find p a) (M.find p b) <= (L.c_lat + 4) *
            N.of_nat (lookup_size a p + lookup_size b p))%N) by
          (intros p Hin; pose proof (union_present a b p Hin) as Hpresent;
           unfold lookup_size; destruct (M.find p a) as [x |], (M.find p b) as [y |];
           time_cbn; try (destruct Hpresent; contradiction);
           try pose proof (L.T_join_le x y); rewrite !Nat2N.inj_add in *; nia);
        pose proof (union_charge_bound (fun p => Tf (M.find p a) (M.find p b))
          (L.c_lat + 4)%N a b Hcallback) as Hsum
    end.
    time_cbn_all. rewrite !size_values. unfold c_lat.
    pose proof L.c_lat_pos.
    assert (Hbot : (1 <= N.of_nat (L.size L.bot + 1))%N) by lia.
    rewrite !Nat2N.inj_add in *. nia.
  Qed.
  (** Bottom testing charges each stored value once, together with its skeleton. *)
  Lemma T_is_bot_le : forall a,
    (T_is_bot a <= c_lat * N.of_nat (size a + 1))%N.
  Proof.
    intro a. time_unfold @T_is_bot. time_simpl; time_cbn.
    lazymatch goal with
    | |- context [M.T_existsb ?f ?Tf a] =>
        pose proof (M.T_existsb_sum_le L.t f Tf a) as Hclock;
        assert (Hcallback : forall v, (Tf v <= (L.c_lat + 4) *
          N.of_nat (L.size v + 1))%N) by
          (intro v; pose proof (L.T_is_bot_le v); time_cbn;
           rewrite !Nat2N.inj_add in *; nia);
        pose proof (exists_charge_bound Tf (L.c_lat + 4)%N a Hcallback) as Hsum
    end.
    rewrite size_values. unfold c_lat.
    pose proof L.c_lat_pos.
    assert (Hbot : (1 <= N.of_nat (L.size L.bot + 1))%N) by lia.
    rewrite !Nat2N.inj_add in *. nia.
  Qed.

  (** Inclusion is linear in both map sizes. *)
  Theorem leb_complexity : bigO (X := t * t) (fun _ => True)
    (fun ab => N.of_nat (size (fst ab) + size (snd ab)))
    (fun ab => T_leb (fst ab) (snd ab)).
  Proof.
    apply bigO_intro with (c := c_lat).
    intros [a b] _; cbn [fst snd].
    pose proof (T_leb_le a b) as Hbound.
    rewrite Nat2N.inj_add in Hbound. nia.
  Qed.

  (** Joining is linear in both map sizes. *)
  Theorem join_complexity : bigO (X := t * t) (fun _ => True)
    (fun ab => N.of_nat (size (fst ab) + size (snd ab)))
    (fun ab => T_join (fst ab) (snd ab)).
  Proof.
    apply bigO_intro with (c := c_lat).
    intros [a b] _; cbn [fst snd].
    pose proof (T_join_le a b) as Hbound.
    rewrite Nat2N.inj_add in Hbound. nia.
  Qed.

  (** Bottom testing is linear in the map size. *)
  Theorem is_bot_complexity : bigO (fun _ : t => True) (fun a => N.of_nat (size a)) T_is_bot.
  Proof.
    apply bigO_intro with (c := c_lat).
    intros a _.
    pose proof (T_is_bot_le a) as Hbound.
    rewrite Nat2N.inj_add in Hbound. nia.
  Qed.
End MapLatticeT.
