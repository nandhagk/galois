(** * Token-partitioned states

    A capped list of labelled states represents their union.
    For example, a join combines states carrying the same token.
    Builds on: PartitionSig, StateSig and LatticeSig. *)

From Stdlib Require Import List NArith Arith Bool Lia.
From Argent Require Import Time Tactics Std.
From Galois.Base Require Import KeySig.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import LangSig ValueSig.
From Galois.States Require Import StateSig DisjunctionSig PartitionSig.
Import List.ListNotations.
Local Open Scope nat_scope.

(** The tail fitting operation adds at most one part to its prefix. *)
Lemma fit_tail_length {K A} (bot : A) (join : A -> A -> A) n
    (xs : list (option K * A)) : length (fit_tail bot join n xs) <= S n.
Proof.
  revert xs.
  induction n as [|n IH]; intros [|x xs]; simpl; try lia.
  specialize (IH xs); lia.
Qed.

(** Fitting parts produces a list inside the requested cap. *)
Lemma fit_parts_inside {K A} (bot : A) (join : A -> A -> A) n
    (xs : list (option K * A)) : Nat.leb (length (fit_parts bot join n xs)) n = true.
Proof.
  destruct n as [|n]; simpl; auto.
  destruct (Nat.leb (length xs) (S n)) eqn:Hfit; auto.
  apply Nat.leb_le, fit_tail_length.
Qed.

(** Absorption keeps the number of parts. *)
Lemma absorb_length {K A} (eqb : K -> K -> bool) (leb : A -> A -> bool)
    (bot : A) (join widen : A -> A -> A) strays fresh old :
    length (absorb eqb leb bot join widen strays fresh old) = length old.
Proof.
  revert strays.
  induction old as [|q rest IH]; simpl; auto.
  intros strays.
  destruct (leb (snd q) bot); simpl; now rewrite IH.
Qed.

Module PartitionCode (X Tk : KEY_OPS) (L : LANG_OPS) (V : VALUE_DOMAIN_OPS L)
    (S : STATE_DOMAIN_OPS X L V) (C : CAP) <: PARTITION_OPS X Tk L V S C.
  Definition t := capped (option Tk.t * S.t) C.k.
  Definition fit (ps : list (option Tk.t * S.t)) : t :=
    exist _ (fit_parts S.bot S.join C.k ps) (fit_parts_inside S.bot S.join C.k ps).
  Definition leb (a b : t) : bool := forallb (fun q => S.leb (snd q) S.bot ||
    existsb (fun r => S.leb (snd q) (snd r)) (proj1_sig b)) (proj1_sig a).
  Definition bot : t := exist _ [] eq_refl.
  Definition is_bot (a : t) : bool := forallb (fun q => S.leb (snd q) S.bot) (proj1_sig a).
  Definition join (a b : t) : t := fit (merge_parts Tk.eqb S.join (proj1_sig a) (proj1_sig b)).
  Definition top : t := fit [(None, S.top)].
  Definition meet (a b : t) : t := fit (flat_map (fun q =>
    map (fun r => (fst q, S.meet (snd q) (snd r))) (proj1_sig b)) (proj1_sig a)).
  Definition wparam := S.wparam.
  Definition widen (p : wparam) (a b : t) : t.
  Proof.
    destruct a as [old Hbound].
    destruct (leb b (exist _ old Hbound)).
    - exact (exist _ old Hbound).
    - destruct (is_bot (exist _ old Hbound)).
      + exact b.
      + pose (fresh := fresh_parts S.leb S.bot old (proj1_sig b)).
        refine (exist _ (absorb Tk.eqb S.leb S.bot S.join (S.widen p)
          (stray_parts Tk.eqb S.leb S.bot old fresh) fresh old) _).
        now rewrite absorb_length.
  Defined.
  Definition narrow (a _ : t) : t := a.
  Definition inject (k : Tk.t) (s : S.t) : t := fit [(Some k, s)].
  Definition merge (k : Tk.t) (a : t) : t :=
    inject k (collapse_with S.bot S.join (map snd (proj1_sig a))).
  Definition retag := merge.
  Definition map_bounded (f : S.t -> S.t) (a : t) : t.
  Proof.
    destruct a as [xs Hbound].
    refine (exist _ (map (fun q => (fst q, f (snd q))) xs) _).
    now rewrite length_map.
  Defined.
  Definition assign x e (a : t) := map_bounded (S.assign x e) a.
  Definition havoc x (a : t) := map_bounded (S.havoc x) a.
  Definition assume g es (a : t) := map_bounded (S.assume g es) a.
  Definition eval e (a : t) :=
    fold_left (fun v q => V.join v (S.eval e (snd q))) (proj1_sig a) V.bot.
End PartitionCode.

Module Specif.
  TimeFun proj1_sig.
End Specif.

Module Partition (X Tk : KEY) (L : LANG) (V : VALUE_DOMAIN L)
    (S : STATE_DOMAIN X L V) (C : POS_CAP) <: PARTITION X Tk L V S C.
  Include PartitionCode X Tk L V S C.
  Definition gamma (d : t) (st : X.t -> L.val) : Prop :=
    Exists (fun q => S.gamma (snd q) st) (proj1_sig d).
  Definition wrank (p : wparam) (d : t) : nat :=
    fold_right Nat.add 0 (map (fun q =>
      if S.leb (snd q) S.bot then 0 else S.wrank p (snd q)) (proj1_sig d)).

  (** Coverage gives a target part unless the source part lies below bottom. *)
  Lemma leb_spec a b : leb a b = true <-> forall q, In q (proj1_sig a) ->
    S.leb (snd q) S.bot = true \/
    exists r, In r (proj1_sig b) /\ S.leb (snd q) (snd r) = true.
  Proof.
    unfold leb; rewrite forallb_forall.
    split; intros Hcover q Hq; specialize (Hcover q Hq).
    - apply orb_true_iff in Hcover; destruct Hcover as [Hbot|Hcover]; auto.
      right; now apply existsb_exists in Hcover.
    - apply orb_true_iff; destruct Hcover as [Hbot|Hcover]; auto.
      right; now apply existsb_exists.
  Qed.

  (** A positive cap retains a singleton without changing its label. *)
  Lemma fit_singleton q : proj1_sig (fit [q]) = [q].
  Proof.
    unfold fit; cbn [proj1_sig].
    unfold fit_parts; destruct C.k as [|n] eqn:Hcap; simpl; auto.
    pose proof C.k_pos as Hpos; rewrite Hcap in Hpos; lia.
  Qed.

  (** A join fold remains above its initial state. *)
  Lemma fold_join_start xs a : S.leb a (fold_left S.join xs a) = true.
  Proof.
    revert a; induction xs as [|x xs IH]; intro a; cbn [fold_left].
    - apply S.leb_refl.
    - eapply S.leb_trans; [apply S.join_ub_l | apply IH].
  Qed.

  (** A join fold remains above every state it visits. *)
  Lemma fold_join_member xs a x : In x xs -> S.leb x (fold_left S.join xs a) = true.
  Proof.
    revert a; induction xs as [|y xs IH]; intros a Hin; cbn in Hin; [contradiction|].
    cbn [fold_left]; destruct Hin as [<-|Hin].
    - eapply S.leb_trans; [apply S.join_ub_r | apply fold_join_start].
    - now apply IH.
  Qed.

  (** Collapsing states covers every member of the input. *)
  Lemma collapse_covers xs x : In x xs ->
    S.leb x (collapse_with S.bot S.join xs) = true.
  Proof.
    destruct xs as [|a xs]; cbn; [contradiction|].
    intros [<-|Hin]; [apply fold_join_start | now apply fold_join_member].
  Qed.

  (** Raw coverage keeps every source part below an explicit target part. *)
  Definition parts_cover (ps qs : list (option Tk.t * S.t)) : Prop :=
    forall q, In q ps -> exists r, In r qs /\ S.leb (snd q) (snd r) = true.

  Lemma parts_cover_refl ps : parts_cover ps ps.
  Proof.
    intros q Hq; exists q; split; [exact Hq | apply S.leb_refl].
  Qed.

  Lemma parts_cover_trans ps qs rs :
    parts_cover ps qs -> parts_cover qs rs -> parts_cover ps rs.
  Proof.
    intros Hpq Hqr q Hq.
    destruct (Hpq q Hq) as [r [Hr Hle]], (Hqr r Hr) as [s [Hs Hle']].
    exists s; split; [exact Hs | eapply S.leb_trans; eassumption].
  Qed.

  (** Joining the suffix preserves coverage of the whole list. *)
  Lemma fit_tail_covers n ps : parts_cover ps (fit_tail S.bot S.join n ps).
  Proof.
    revert ps; induction n as [|n IH]; intros ps q Hq.
    - exists (None, collapse_with S.bot S.join (map snd ps)); split; simpl; auto.
      apply collapse_covers; now apply in_map.
    - destruct ps as [|r ps]; [contradiction|].
      cbn [fit_tail]; destruct Hq as [<-|Hq].
      + exists r; split; simpl; auto using S.leb_refl.
      + destruct (IH ps q Hq) as [s [Hs Hle]].
        exists s; split; simpl; auto.
  Qed.

  (** Restoring a positive cap preserves all input parts. *)
  Lemma fit_covers ps : parts_cover ps (proj1_sig (fit ps)).
  Proof.
    unfold fit; cbn [proj1_sig]; unfold fit_parts.
    destruct C.k as [|n] eqn:Hcap.
    - pose proof C.k_pos as Hpos; rewrite Hcap in Hpos; lia.
    - destruct (Nat.leb (length ps) (Datatypes.S n));
        [apply parts_cover_refl | apply fit_tail_covers].
  Qed.

  (** Insertion covers the inserted part and every previous part. *)
  Lemma insert_covers q ps : parts_cover (q :: ps) (insert_part Tk.eqb S.join q ps).
  Proof.
    induction ps as [|p ps IH]; intros r Hr; cbn [insert_part].
    - destruct Hr as [<-|Hr]; [|contradiction].
      exists q; split; simpl; auto using S.leb_refl.
    - destruct (label_eqb Tk.eqb (fst p) (fst q));
        destruct Hr as [<-|[<-|Hr]].
      + exists (fst p, S.join (snd p) (snd q)); split; simpl; auto using S.join_ub_r.
      + exists (fst p, S.join (snd p) (snd q)); split; simpl; auto using S.join_ub_l.
      + exists r; split; simpl; auto using S.leb_refl.
      + destruct (IH q (or_introl eq_refl)) as [s [Hs Hle]].
        exists s; split; simpl; auto.
      + exists p; split; simpl; auto using S.leb_refl.
      + destruct (IH r (or_intror Hr)) as [s [Hs Hle]].
        exists s; split; simpl; auto.
  Qed.

  (** Merging retains every part of its initial accumulator. *)
  Lemma merge_covers_left ps qs : parts_cover ps (merge_parts Tk.eqb S.join ps qs).
  Proof.
    unfold merge_parts; revert ps; induction qs as [|q qs IH]; intro ps; cbn [fold_left].
    - apply parts_cover_refl.
    - eapply parts_cover_trans; [|apply IH].
      intros p Hp; apply insert_covers; now right.
  Qed.

  (** Merging retains every part of the inserted list. *)
  Lemma merge_covers_right ps qs : parts_cover qs (merge_parts Tk.eqb S.join ps qs).
  Proof.
    unfold merge_parts; revert ps; induction qs as [|q qs IH]; intros ps r Hr.
    - contradiction.
    - cbn [fold_left]; destruct Hr as [<-|Hr].
      + destruct (insert_covers q ps q (or_introl eq_refl)) as [s [Hs Hle]].
        destruct (merge_covers_left (insert_part Tk.eqb S.join q ps) qs s Hs)
          as [t [Ht Hle']].
        exists t; split; [exact Ht | eapply S.leb_trans; eassumption].
      + now apply IH.
  Qed.

  Lemma leb_refl : forall a, leb a a = true.
  Proof.
    intro a; apply leb_spec; intros q Hq; right.
    exists q; split; [exact Hq | apply S.leb_refl].
  Qed.
  (** The order composes through an intermediate value. *)
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof.
    intros a b c Hab Hbc.
    pose proof (proj1 (leb_spec a b) Hab) as Hcoverab.
    pose proof (proj1 (leb_spec b c) Hbc) as Hcoverbc.
    apply leb_spec; intros q Hq; destruct (Hcoverab q Hq) as [Hbot|[r [Hr Hqr]]]; auto.
    destruct (Hcoverbc r Hr) as [Hbot|[s [Hs Hrs]]].
    - left; eapply S.leb_trans; eassumption.
    - right; exists s; split; [exact Hs | eapply S.leb_trans; eassumption].
  Qed.
  (** Bottom is below every value. *)
  Lemma bot_least : forall a, leb bot a = true.
  Proof.
    reflexivity.
  Qed.
  (** The bottom test recognizes bottom. *)
  Lemma is_bot_bot : is_bot bot = true.
  Proof.
    reflexivity.
  Qed.
  (** Every recognized bottom is below every value. *)
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof.
    intros a b Hbot; unfold is_bot in Hbot; rewrite forallb_forall in Hbot.
    apply leb_spec; intros q Hq; left; now apply Hbot.
  Qed.
  (** Join is above its left operand. *)
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof.
    intros a b; apply leb_spec; intros q Hq; right.
    eapply parts_cover_trans; [apply merge_covers_left | apply fit_covers | exact Hq].
  Qed.
  (** Join is above its right operand. *)
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof.
    intros a b; apply leb_spec; intros q Hq; right.
    eapply parts_cover_trans; [apply merge_covers_right | apply fit_covers | exact Hq].
  Qed.

  Lemma top_greatest : forall a, leb a top = true.
  Proof.
    intro a; apply leb_spec; intros q Hq; right.
    exists (None, S.top); split.
    - unfold top; rewrite fit_singleton; simpl; auto.
    - apply S.top_greatest.
  Qed.

  (** A failed existential Boolean test rejects every list member. *)
  Lemma existsb_false_spec {A} (f : A -> bool) xs :
    existsb f xs = false <-> forall x, In x xs -> f x = false.
  Proof.
    induction xs as [|x xs IH]; cbn [existsb].
    - split; [intros _ y Hy; contradiction | reflexivity].
    - rewrite orb_false_iff, IH; split.
      + intros [Hx Hxs] y [<-|Hy]; auto.
      + intro Hall; split; [apply Hall; now left | intros y Hy; apply Hall; now right].
  Qed.

  (** A failed universal Boolean test supplies a rejected member. *)
  Lemma forallb_false_member {A} (f : A -> bool) xs :
    forallb f xs = false -> exists x, In x xs /\ f x = false.
  Proof.
    induction xs as [|x xs IH]; cbn [forallb]; intro Hfalse; [discriminate|].
    destruct (f x) eqn:Hx.
    - cbn in Hfalse; destruct (IH Hfalse) as [y [Hy Hfy]].
      exists y; split; simpl; auto.
    - exists x; split; simpl; auto.
  Qed.

  (** Fresh parts are nonbottom candidate parts uncovered by every previous part. *)
  Lemma fresh_spec (old new : list (option Tk.t * S.t)) q :
    In q (fresh_parts S.leb S.bot old new) <->
    In q new /\ S.leb (snd q) S.bot = false /\
      (forall r, In r old -> S.leb (snd q) (snd r) = false).
  Proof.
    unfold fresh_parts, uncovered; rewrite !filter_In, !negb_true_iff.
    rewrite existsb_false_spec; tauto.
  Qed.

  (** A failed coverage test supplies at least one fresh part. *)
  Lemma fresh_exists a b : leb b a = false ->
    exists q, In q (fresh_parts S.leb S.bot (proj1_sig a) (proj1_sig b)).
  Proof.
    unfold leb; intro Hfalse.
    destruct (forallb_false_member _ _ Hfalse) as [q [Hq Hfalseq]].
    apply orb_false_iff in Hfalseq; destruct Hfalseq as [Hbot Hcover].
    exists q; apply fresh_spec; split; [exact Hq|].
    split; [exact Hbot | now apply existsb_false_spec].
  Qed.

  (** Absorption keeps each previous part below its corresponding result part. *)
  Lemma absorb_covers_old p strays fresh old :
    parts_cover old (absorb Tk.eqb S.leb S.bot S.join (S.widen p) strays fresh old).
  Proof.
    revert strays; induction old as [|r old IH]; intros strays q Hq; [contradiction|].
    cbn [absorb]; destruct (S.leb (snd r) S.bot); destruct Hq as [<-|Hq].
    - exists r; split; simpl; auto using S.leb_refl.
    - destruct (IH strays q Hq) as [s [Hs Hle]]; exists s; split; simpl; auto.
    - eexists; split; [left; reflexivity | apply S.widen_ub_l].
    - destruct (IH [] q Hq) as [s [Hs Hle]]; exists s; split; simpl; auto.
  Qed.

  (** A receiving part covers both its same-label inputs and its assigned strays. *)
  Lemma absorb_head_covers p strays fresh r old q :
    S.leb (snd r) S.bot = false ->
    (In q strays \/ (In q fresh /\ label_eqb Tk.eqb (fst r) (fst q) = true)) ->
    exists s, In s (absorb Tk.eqb S.leb S.bot S.join (S.widen p) strays fresh (r :: old)) /\
      S.leb (snd q) (snd s) = true.
  Proof.
    intros Hnonbot Hreceive; cbn [absorb]; rewrite Hnonbot.
    eexists; split; [left; reflexivity|].
    cbn [snd]; eapply S.leb_trans; [apply collapse_covers | apply S.widen_ub_r].
    right; apply in_map_iff; exists q; split; [reflexivity|].
    apply in_or_app; destruct Hreceive as [Hstray|[Hfresh Hlabel]]; auto.
    left; apply filter_In; auto.
  Qed.

  (** A fresh part with a live matching label reaches a receiver. *)
  Lemma absorb_covers_label p strays fresh old q : In q fresh ->
    (exists r, In r old /\ S.leb (snd r) S.bot = false /\
      label_eqb Tk.eqb (fst r) (fst q) = true) ->
    exists s, In s (absorb Tk.eqb S.leb S.bot S.join (S.widen p) strays fresh old) /\
      S.leb (snd q) (snd s) = true.
  Proof.
    revert strays; induction old as [|r old IH]; intros strays Hfresh [s [Hs [Hbot Hlabel]]].
    - contradiction.
    - destruct Hs as [<-|Hs].
      + apply absorb_head_covers; auto.
      + cbn [absorb]; destruct (S.leb (snd r) S.bot).
        * destruct (IH strays Hfresh (ex_intro _ s (conj Hs (conj Hbot Hlabel))))
            as [t [Ht Hle]].
          exists t; split; simpl; auto.
        * destruct (IH [] Hfresh (ex_intro _ s (conj Hs (conj Hbot Hlabel))))
            as [t [Ht Hle]].
          exists t; split; simpl; auto.
  Qed.

  (** A stray reaches the first previous part above bottom. *)
  Lemma absorb_covers_stray p strays fresh old q : In q strays ->
    (exists r, In r old /\ S.leb (snd r) S.bot = false) ->
    exists s, In s (absorb Tk.eqb S.leb S.bot S.join (S.widen p) strays fresh old) /\
      S.leb (snd q) (snd s) = true.
  Proof.
    induction old as [|r old IH]; intros Hstray [s [Hs Hnonbot]]; [contradiction|].
    destruct (S.leb (snd r) S.bot) eqn:Hbot.
    - destruct Hs as [<-|Hs]; [congruence|].
      cbn [absorb]; rewrite Hbot.
      destruct (IH Hstray (ex_intro _ s (conj Hs Hnonbot))) as [t [Ht Hle]].
      exists t; split; simpl; auto.
    - apply absorb_head_covers; auto.
  Qed.

  (** Every fresh part is covered after routing from a nonbottom partition. *)
  Lemma absorb_covers_fresh p old fresh q :
    (exists r, In r old /\ S.leb (snd r) S.bot = false) -> In q fresh ->
    exists s, In s (absorb Tk.eqb S.leb S.bot S.join (S.widen p)
      (stray_parts Tk.eqb S.leb S.bot old fresh) fresh old) /\
      S.leb (snd q) (snd s) = true.
  Proof.
    intros Hlive Hfresh.
    destruct (existsb (fun r => negb (S.leb (snd r) S.bot) &&
      label_eqb Tk.eqb (fst r) (fst q)) old) eqn:Hlabel.
    - apply absorb_covers_label; [exact Hfresh|].
      apply existsb_exists in Hlabel; destruct Hlabel as [r [Hr Hlabel]].
      apply andb_true_iff in Hlabel; destruct Hlabel as [Hbot Hlabel].
      apply negb_true_iff in Hbot; exists r; auto.
    - apply absorb_covers_stray; [|exact Hlive].
      unfold stray_parts; apply filter_In; split; [exact Hfresh|].
      now rewrite Hlabel.
  Qed.

  (** Widening exposes the same three branches on the bounded raw lists. *)
  Lemma widen_raw p a b : proj1_sig (widen p a b) =
    if leb b a then proj1_sig a else
    if is_bot a then proj1_sig b else
    let old := proj1_sig a in
    let fresh := fresh_parts S.leb S.bot old (proj1_sig b) in
    absorb Tk.eqb S.leb S.bot S.join (S.widen p)
      (stray_parts Tk.eqb S.leb S.bot old fresh) fresh old.
  Proof.
    destruct a as [old Hbound]; unfold widen.
    destruct (leb b (exist _ old Hbound)); [reflexivity|].
    destruct (is_bot (exist _ old Hbound)); reflexivity.
  Qed.

  (** Widening is above its previous value. *)
  Lemma widen_ub_l : forall p a b, leb a (widen p a b) = true.
  Proof.
    intros p a b; destruct (leb b a) eqn:Hstable.
    - apply leb_spec; intros q Hq; right; rewrite widen_raw, Hstable.
      apply parts_cover_refl; exact Hq.
    - destruct (is_bot a) eqn:Hbot; [now apply is_bot_least|].
      apply leb_spec; intros q Hq; right; rewrite widen_raw, Hstable, Hbot.
      now apply absorb_covers_old.
  Qed.
  (** Widening is above its candidate value. *)
  Lemma widen_ub_r : forall p a b, leb b (widen p a b) = true.
  Proof.
    intros p a b; destruct (leb b a) eqn:Hstable.
    - apply leb_spec; intros q Hq; rewrite widen_raw, Hstable.
      exact (proj1 (leb_spec b a) Hstable q Hq).
    - destruct (is_bot a) eqn:Hbot.
      + apply leb_spec; intros q Hq; right; rewrite widen_raw, Hstable, Hbot.
        apply parts_cover_refl; exact Hq.
      + apply leb_spec; intros q Hq.
        destruct (S.leb (snd q) S.bot) eqn:Hqbot; [now left|]; right.
        rewrite widen_raw, Hstable, Hbot.
        destruct (existsb (fun r => S.leb (snd q) (snd r)) (proj1_sig a)) eqn:Hcover.
        * apply existsb_exists in Hcover; destruct Hcover as [r [Hr Hqr]].
          destruct (absorb_covers_old p
            (stray_parts Tk.eqb S.leb S.bot (proj1_sig a)
              (fresh_parts S.leb S.bot (proj1_sig a) (proj1_sig b)))
            (fresh_parts S.leb S.bot (proj1_sig a) (proj1_sig b))
            (proj1_sig a) r Hr) as [s [Hs Hrs]].
          exists s; split; [exact Hs | eapply S.leb_trans; eassumption].
        * apply absorb_covers_fresh.
          -- exact (forallb_false_member _ _ Hbot).
          -- apply fresh_spec; split; [exact Hq|].
             split; [exact Hqbot | now apply existsb_false_spec].
  Qed.
  (** A candidate below the previous value leaves widening unchanged. *)
  Lemma widen_stable : forall p a b, leb b a = true -> widen p a b = a.
  Proof.
    intros p [old Hbound] b Hstable; unfold widen; rewrite Hstable; reflexivity.
  Qed.
  (** An unstable widening from a nonbottom strictly decreases rank. *)
  Lemma wrank_widen : forall p a b, is_bot a = false -> leb b a = false ->
    wrank p (widen p a b) < wrank p a.
  Proof. Admitted. (* STUB *)
  (** Widening from a nonbottom does not increase rank. *)
  Lemma wrank_widen_le : forall p a b, is_bot a = false -> wrank p (widen p a b) <= wrank p a.
  Proof. Admitted. (* STUB *)
  (** Narrowing stays between an ordered candidate and previous value. *)
  Lemma narrow_between : forall a b, leb b a = true ->
    leb b (narrow a b) = true /\ leb (narrow a b) a = true.
  Proof.
    intros a b Hle; split; [exact Hle | apply leb_refl].
  Qed.

  (** Abstract inclusion entails inclusion of concrete environments. *)
  Lemma gamma_mono : forall a b st, leb a b = true -> gamma a st -> gamma b st.
  Proof.
    intros a b st Hle Hgamma; pose proof (proj1 (leb_spec a b) Hle) as Hcover.
    apply Exists_exists in Hgamma; destruct Hgamma as [q [Hq Hgamma]].
    destruct (Hcover q Hq) as [Hbot|[r [Hr Hqr]]].
    - exfalso; apply (S.gamma_bot st); eapply S.gamma_mono; eassumption.
    - apply Exists_exists; exists r; split; [exact Hr|].
      eapply S.gamma_mono; eassumption.
  Qed.
  (** Bottom describes no concrete environment. *)
  Lemma gamma_bot : forall st, ~ gamma bot st.
  Proof.
    intros st Hgamma; inversion Hgamma.
  Qed.
  (** Top describes every concrete environment. *)
  Lemma gamma_top : forall st, gamma top st.
  Proof.
    intro st; unfold gamma, top; rewrite fit_singleton.
    apply Exists_cons_hd; apply S.gamma_top.
  Qed.

  (** Mapping a sound component transfer retains the corresponding concrete environment. *)
  Lemma map_bounded_sound f a st st' :
    (forall s, S.gamma s st -> S.gamma (f s) st') ->
    gamma a st -> gamma (map_bounded f a) st'.
  Proof.
    intros Hf Hgamma; apply Exists_exists in Hgamma.
    destruct Hgamma as [q [Hq Hgamma]]; destruct a as [ps Hbound].
    unfold gamma, map_bounded; cbn [proj1_sig]; apply Exists_exists.
    exists (fst q, f (snd q)); split.
    - apply in_map_iff; exists q; split; [reflexivity|exact Hq].
    - now apply Hf.
  Qed.
  (** Assignment contains each successful concrete update. *)
  Lemma assign_sound : forall x e s st c,
    gamma s st -> eval_term L.eval st e = Some c ->
    gamma (assign x e s) (upd X.eqb st x c).
  Proof.
    intros x e s st c Hgamma Heval; apply map_bounded_sound with (st := st); auto.
    intros a Ha; eapply S.assign_sound; eassumption.
  Qed.
  (** Havoc contains every concrete update of the selected variable. *)
  Lemma havoc_sound : forall x s st c,
    gamma s st -> gamma (havoc x s) (upd X.eqb st x c).
  Proof.
    intros x s st c Hgamma; apply map_bounded_sound with (st := st); auto.
    intros a Ha; now apply S.havoc_sound.
  Qed.
  (** Assuming a true guard retains its concrete environment. *)
  Lemma assume_sound : forall g es s st cs,
    gamma s st -> eval_terms L.eval st es = Some cs -> L.holds g cs ->
    gamma (assume g es s) st.
  Proof.
    intros g es s st cs Hgamma Heval Hholds.
    apply map_bounded_sound with (st := st); auto.
    intros a Ha; eapply S.assume_sound; eassumption.
  Qed.

  (** Evaluation's fold remains above its initial abstract value. *)
  Lemma eval_fold_start e (ps : list (option Tk.t * S.t)) v :
    V.leb v (fold_left (fun a q => V.join a (S.eval e (snd q))) ps v) = true.
  Proof.
    revert v; induction ps as [|q ps IH]; intro v; cbn [fold_left].
    - apply V.leb_refl.
    - eapply V.leb_trans; [apply V.join_ub_l | apply IH].
  Qed.

  (** Evaluation's fold covers each part's abstract result. *)
  Lemma eval_fold_member e (ps : list (option Tk.t * S.t)) v q : In q ps ->
    V.leb (S.eval e (snd q))
      (fold_left (fun a q => V.join a (S.eval e (snd q))) ps v) = true.
  Proof.
    revert v; induction ps as [|r ps IH]; intros v Hq; [contradiction|].
    cbn [fold_left]; destruct Hq as [<-|Hq].
    - eapply V.leb_trans; [apply V.join_ub_r | apply eval_fold_start].
    - now apply IH.
  Qed.
  (** Abstract evaluation describes every successful concrete result. *)
  Lemma eval_sound : forall e s st c,
    gamma s st -> eval_term L.eval st e = Some c -> V.gamma (eval e s) c.
  Proof.
    intros e s st c Hgamma Heval; apply Exists_exists in Hgamma.
    destruct Hgamma as [q [Hq Hgamma]].
    eapply V.gamma_mono; [exact (eval_fold_member e (proj1_sig s) V.bot q Hq) |].
    eapply S.eval_sound; eassumption.
  Qed.
  Lemma gamma_parts : forall a st,
    gamma a st <-> Exists (fun q => S.gamma (snd q) st) (proj1_sig a).
  Proof.
    reflexivity.
  Qed.
  Lemma leb_cover : forall a b, leb a b = forallb (fun q => S.leb (snd q) S.bot ||
    existsb (fun r => S.leb (snd q) (snd r)) (proj1_sig b)) (proj1_sig a).
  Proof.
    reflexivity.
  Qed.
  Lemma is_bot_parts : forall a,
    is_bot a = forallb (fun q => S.leb (snd q) S.bot) (proj1_sig a).
  Proof.
    reflexivity.
  Qed.
  Lemma bot_raw : proj1_sig bot = [].
  Proof.
    reflexivity.
  Qed.
  Lemma top_raw : proj1_sig top = [(None, S.top)].
  Proof.
    apply fit_singleton.
  Qed.
  Lemma join_parts : forall a b, proj1_sig (join a b) =
    fit_parts S.bot S.join C.k (merge_parts Tk.eqb S.join (proj1_sig a) (proj1_sig b)).
  Proof.
    reflexivity.
  Qed.
  Lemma wrank_parts : forall p a, wrank p a = fold_right Nat.add 0 (map (fun q =>
    if S.leb (snd q) S.bot then 0 else S.wrank p (snd q)) (proj1_sig a)).
  Proof.
    reflexivity.
  Qed.
  Lemma inject_raw : forall k s, proj1_sig (inject k s) = [(Some k, s)].
  Proof.
    intros; apply fit_singleton.
  Qed.
  Lemma merge_eq : forall k a,
    merge k a = inject k (collapse_with S.bot S.join (map snd (proj1_sig a))).
  Proof.
    reflexivity.
  Qed.
  Lemma retag_eq : forall k a, retag k a = merge k a.
  Proof.
    reflexivity.
  Qed.
  Lemma gamma_inject : forall k s st, S.gamma s st -> gamma (inject k s) st.
  Proof.
    intros k s st Hgamma; unfold gamma; rewrite inject_raw.
    now apply Exists_cons_hd.
  Qed.
  Lemma merge_sound : forall k a st, gamma a st -> gamma (merge k a) st.
  Proof.
    intros k a st Hgamma; apply Exists_exists in Hgamma.
    destruct Hgamma as [q [Hq Hgamma]]; apply gamma_inject.
    eapply S.gamma_mono; [|exact Hgamma].
    apply collapse_covers; apply in_map_iff; exists q; auto.
  Qed.
End Partition.

Module PartitionT (X Tk : KEY_T) (L : LANG_T) (V : VALUE_DOMAIN_T L)
    (S : STATE_DOMAIN_T X L V) (JS : JOIN_SIZE S) (JU : JOIN_UNITS X L V S)
    (C : POS_CAP) <: PARTITION_ALL X Tk L V S JS JU C.
  Module Plain := Partition X Tk L V S C.
  Include Plain.
  TimeFun fit.
  TimeFun leb.
  TimeFun is_bot.
  TimeFun join.
  TimeFun top.
  TimeFun widen.
  TimeFun narrow.
  TimeFun inject.
  TimeFun merge.
  TimeFun retag.
  TimeFun map_bounded.
  TimeFun assign.
  TimeFun havoc.
  TimeFun assume.
  TimeFun eval.

  Definition size (a : t) : nat := parts_size Tk.bits S.size (proj1_sig a).
  Definition wunits (a : t) : nat := parts_units S.wunits (proj1_sig a).
  Definition wsize : wparam -> nat := S.wsize.
  Definition assign_work (x : X.t) (e : term L.op X.t) (a : t) : nat :=
    fold_right Nat.add 0%nat (map (fun q => S.assign_work x e (snd q) + 1) (proj1_sig a)).
  Definition havoc_work (x : X.t) (a : t) : nat :=
    fold_right Nat.add 0%nat (map (fun q => S.havoc_work x (snd q) + 1) (proj1_sig a)).
  Definition assume_work (g : L.guard) (es : list (term L.op X.t)) (a : t) : nat :=
    fold_right Nat.add 0%nat
      (map (fun q => S.assume_work g es (snd q) + 1) (proj1_sig a)).
  Definition eval_work (e : term L.op X.t) (a : t) : nat :=
    fold_right Nat.add 0%nat (map (fun q =>
      S.eval_work e (snd q) + V.size (S.eval e (snd q)) + 1) (proj1_sig a)).
  Definition c_lat : N := 1%N. (* STUB *)
  Definition c_state : N := 1%N. (* STUB *)
  Definition c_partition : N := 1%N. (* STUB *)

  Lemma c_lat_pos : (1 <= c_lat)%N.
  Proof. Admitted. (* STUB *)
  Lemma T_leb_le : forall a b,
    (T_leb a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_join_le : forall a b,
    (T_join a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_is_bot_le : forall a,
    (T_is_bot a <= c_lat * N.of_nat (size a + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_widen_le : forall p a b,
    (T_widen p a b <= c_lat * N.of_nat
      ((wunits a + wunits b) * wsize p + (size a + size b + wsize p + 1)))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_narrow_le : forall a b,
    (T_narrow a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_assign_le : forall x e a,
    (T_assign x e a <= c_state * N.of_nat (assign_work x e a + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_havoc_le : forall x a,
    (T_havoc x a <= c_state * N.of_nat (havoc_work x a + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_assume_le : forall g es a,
    (T_assume g es a <= c_state * N.of_nat (assume_work g es a + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_eval_le : forall e a,
    (T_eval e a <= c_state * N.of_nat (eval_work e a + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma size_parts : forall a, size a = parts_size Tk.bits S.size (proj1_sig a).
  Proof. Admitted. (* STUB *)
  Lemma wunits_parts : forall a, wunits a = parts_units S.wunits (proj1_sig a).
  Proof. Admitted. (* STUB *)
  Lemma wsize_component : forall p, wsize p = S.wsize p.
  Proof. Admitted. (* STUB *)
  Lemma assign_work_parts : forall x e a, assign_work x e a =
    fold_right Nat.add 0%nat (map (fun q => S.assign_work x e (snd q) + 1) (proj1_sig a)).
  Proof. Admitted. (* STUB *)
  Lemma havoc_work_parts : forall x a, havoc_work x a =
    fold_right Nat.add 0%nat (map (fun q => S.havoc_work x (snd q) + 1) (proj1_sig a)).
  Proof. Admitted. (* STUB *)
  Lemma assume_work_parts : forall g es a, assume_work g es a =
    fold_right Nat.add 0%nat
      (map (fun q => S.assume_work g es (snd q) + 1) (proj1_sig a)).
  Proof. Admitted. (* STUB *)
  Lemma eval_work_parts : forall e a, eval_work e a = fold_right Nat.add 0%nat (map (fun q =>
    S.eval_work e (snd q) + V.size (S.eval e (snd q)) + 1) (proj1_sig a)).
  Proof. Admitted. (* STUB *)
  Lemma T_inject_le : forall k s,
    (T_inject k s <= c_partition * N.of_nat (Tk.bits k + S.size s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_merge_le : forall k a,
    (T_merge k a <= c_partition * N.of_nat (Tk.bits k + size a + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_retag_le : forall k a,
    (T_retag k a <= c_partition * N.of_nat (Tk.bits k + size a + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma join_size : forall a b,
    (N.of_nat (size (join a b)) <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma join_wunits : forall a b,
    (N.of_nat (wunits (join a b)) <= c_lat * N.of_nat (wunits a + wunits b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma merge_size : forall k a,
    (N.of_nat (size (merge k a)) <= c_partition * N.of_nat (Tk.bits k + size a + 1))%N.
  Proof. Admitted. (* STUB *)

  Definition k_partition : N := 1%N. (* STUB *)
  Definition route_time (p : S.wparam) (old new : list (option Tk.t * S.t)) : N :=
    let fresh := fresh_parts S.leb S.bot old new in
    (T_fresh_parts S.leb S.T_leb S.bot old new +
     T_stray_parts Tk.eqb Tk.T_eqb S.leb S.T_leb S.bot old fresh +
     T_absorb Tk.eqb Tk.T_eqb S.leb S.T_leb S.bot S.join S.T_join
       (S.widen p) (S.T_widen p) (stray_parts Tk.eqb S.leb S.bot old fresh) fresh old)%N.
  Definition eval_joins (e : term L.op X.t) (ps : list (option Tk.t * S.t)) : N :=
    fst (fold_left (fun acc q =>
      ((fst acc + V.T_join (snd acc) (S.eval e (snd q)) + 1)%N,
       V.join (snd acc) (S.eval e (snd q)))) ps (0%N, V.bot)).

  Lemma F1_assign : forall x e a, proj1_sig (assign x e a) =
    map (fun q => (fst q, S.assign x e (snd q))) (proj1_sig a).
  Proof. Admitted. (* STUB *)
  Lemma F2_havoc : forall x a, proj1_sig (havoc x a) =
    map (fun q => (fst q, S.havoc x (snd q))) (proj1_sig a).
  Proof. Admitted. (* STUB *)
  Lemma F3_assume : forall g es a, proj1_sig (assume g es a) =
    map (fun q => (fst q, S.assume g es (snd q))) (proj1_sig a).
  Proof. Admitted. (* STUB *)
  Lemma F4_eval : forall e a,
    eval e a = fold_left (fun v q => V.join v (S.eval e (snd q))) (proj1_sig a) V.bot.
  Proof. Admitted. (* STUB *)
  Lemma F5_widen : forall p a b, proj1_sig (widen p a b) =
    if leb b a then proj1_sig a else
    if is_bot a then proj1_sig b else
    let old := proj1_sig a in
    let fresh := fresh_parts S.leb S.bot old (proj1_sig b) in
    absorb Tk.eqb S.leb S.bot S.join (S.widen p)
      (stray_parts Tk.eqb S.leb S.bot old fresh) fresh old.
  Proof. Admitted. (* STUB *)
  Lemma F6_narrow : forall a b, narrow a b = a.
  Proof. Admitted. (* STUB *)
  Lemma F7_merge_parts_length : forall ps qs,
    length (merge_parts Tk.eqb S.join ps qs) <= length ps + length qs.
  Proof. Admitted. (* STUB *)
  Lemma F8_collapse_size : forall xs, length xs <= 2 * C.k + 1 ->
    (N.of_nat (S.size (collapse_with S.bot S.join xs)) <= k_partition * N.of_nat
      (fold_right Nat.add 0%nat (map S.size xs) + length xs + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma F9_collapse_units : forall xs, length xs <= 2 * C.k + 1 ->
    (N.of_nat (S.wunits (collapse_with S.bot S.join xs)) <= k_partition * N.of_nat
      (fold_right Nat.add 0%nat (map S.wunits xs) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma F10_merge_parts_size : forall ps qs,
    length ps <= C.k -> length qs <= C.k ->
    (N.of_nat (parts_size Tk.bits S.size
      (merge_parts Tk.eqb S.join ps qs)) <= k_partition * N.of_nat
        (parts_size Tk.bits S.size ps + parts_size Tk.bits S.size qs + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma F11_merge_parts_units : forall ps qs,
    length ps <= C.k -> length qs <= C.k ->
    (N.of_nat (parts_units S.wunits
      (merge_parts Tk.eqb S.join ps qs)) <= k_partition * N.of_nat
        (parts_units S.wunits ps + parts_units S.wunits qs + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma F12_fit_size : forall ps, length ps <= 2 * C.k ->
    (N.of_nat (parts_size Tk.bits S.size
      (fit_parts S.bot S.join C.k ps)) <= k_partition * N.of_nat
        (parts_size Tk.bits S.size ps + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma F13_fit_units : forall (ps : list (option Tk.t * S.t)), length ps <= 2 * C.k ->
    (N.of_nat (parts_units S.wunits
      (fit_parts S.bot S.join C.k ps)) <= k_partition * N.of_nat
        (parts_units S.wunits ps + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T1_leb : forall a b,
    (T_leb a b <= k_partition *
      (fold_right N.add 0%N (map (fun q => S.T_leb (snd q) S.bot +
        fold_right N.add 0%N (map (fun r => S.T_leb (snd q) (snd r) + 1) (proj1_sig b)) + 1)
        (proj1_sig a)) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T2_is_bot : forall a,
    (T_is_bot a <= k_partition *
      (fold_right N.add 0%N (map (fun q => S.T_leb (snd q) S.bot + 1) (proj1_sig a)) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T3_join : forall a b,
    (T_join a b <= k_partition *
      (T_merge_parts Tk.eqb Tk.T_eqb S.join S.T_join (proj1_sig a) (proj1_sig b) +
       T_fit_parts S.bot S.join S.T_join C.k
         (merge_parts Tk.eqb S.join (proj1_sig a) (proj1_sig b)) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T4_merge_parts : forall ps qs, length ps <= C.k -> length qs <= C.k ->
    (T_merge_parts Tk.eqb Tk.T_eqb S.join S.T_join ps qs <= k_partition *
      N.of_nat (parts_size Tk.bits S.size ps + parts_size Tk.bits S.size qs + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T5_fit_parts : forall ps, length ps <= 2 * C.k ->
    (T_fit_parts S.bot S.join S.T_join C.k ps <= k_partition *
      N.of_nat (parts_size Tk.bits S.size ps + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T6_widen : forall p a b,
    (T_widen p a b <= k_partition *
      (T_leb b a + T_is_bot a + route_time p (proj1_sig a) (proj1_sig b) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T7_route : forall p old new,
    length old <= C.k -> length new <= C.k ->
    (route_time p old new <= k_partition * N.of_nat
      ((parts_units S.wunits old + parts_units S.wunits new + 1) * S.wsize p +
       (parts_size Tk.bits S.size old + parts_size Tk.bits S.size new + S.wsize p + 1)))%N.
  Proof. Admitted. (* STUB *)
  Lemma T8_collapse : forall xs, length xs <= 2 * C.k + 1 ->
    (T_collapse_with S.bot S.join S.T_join xs <= k_partition * N.of_nat
      (fold_right Nat.add 0%nat (map S.size xs) + length xs + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T9_merge : forall k a,
    (T_merge k a <= k_partition *
      (T_collapse_with S.bot S.join S.T_join (map snd (proj1_sig a)) +
       T_inject k (collapse_with S.bot S.join (map snd (proj1_sig a))) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T10_retag : forall k a,
    (T_retag k a <= k_partition * (T_merge k a + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T11_inject : forall k s, (T_inject k s <= k_partition)%N.
  Proof. Admitted. (* STUB *)
  Lemma T12_eval : forall e a,
    (T_eval e a <= k_partition *
      (fold_right N.add 0%N (map (fun q => S.T_eval e (snd q) + 1) (proj1_sig a)) +
       eval_joins e (proj1_sig a) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T13_eval_joins : forall e ps, length ps <= C.k ->
    (eval_joins e ps <= k_partition * N.of_nat (fold_right Nat.add 0%nat
      (map (fun q => (V.size (S.eval e (snd q)) + 1)%nat) ps) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T14_assign : forall x e a,
    (T_assign x e a <= k_partition *
      (fold_right N.add 0%N
        (map (fun q => S.T_assign x e (snd q) + 1) (proj1_sig a)) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T15_havoc : forall x a,
    (T_havoc x a <= k_partition *
      (fold_right N.add 0%N (map (fun q => S.T_havoc x (snd q) + 1) (proj1_sig a)) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T16_assume : forall g es a,
    (T_assume g es a <= k_partition *
      (fold_right N.add 0%N
        (map (fun q => S.T_assume g es (snd q) + 1) (proj1_sig a)) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T17_narrow : forall a b, (T_narrow a b <= k_partition)%N.
  Proof. Admitted. (* STUB *)
End PartitionT.
