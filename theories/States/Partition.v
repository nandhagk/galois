(** * Token-partitioned states

    A capped list of labelled states represents their union.
    For example, a join combines states carrying the same token.
    Builds on: PartitionSig, StateSig and LatticeSig. *)

From Stdlib Require Import List NArith Arith Bool Lia.
From Argent Require Import Time Tactics Std BigO.
From Galois.Base Require Import KeySig.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import LangSig ValueSig.
From Galois.States Require Import StateSig DisjunctionSig Disjunction PartitionSig.
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

(** Inserting one labelled part adds at most one list entry. *)
Lemma insert_part_length {K A} (eqb : K -> K -> bool) (join : A -> A -> A)
    (q : option K * A) ps : length (insert_part eqb join q ps) <= length ps + 1.
Proof.
  induction ps as [|p ps IH]; cbn [insert_part length]; [lia|].
  destruct (label_eqb eqb (fst p) (fst q)); cbn [length]; lia.
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

Module Specif := Disjunction.Specif.

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

  (** A state above bottom cannot be recognized as bottom. *)
  Lemma nonbottom_test s : S.leb s S.bot = false -> S.is_bot s = false.
  Proof.
    intro Hnonbot; destruct (S.is_bot s) eqn:Hbot; auto.
    pose proof (S.is_bot_least s S.bot Hbot); congruence.
  Qed.

  (** Only states above bottom contribute to the partition rank. *)
  Definition live_rank p s := if S.leb s S.bot then 0 else S.wrank p s.

  (** Raw rank sums the ranks that survive the bottom test. *)
  Definition raw_rank p (ps : list (option Tk.t * S.t)) :=
    fold_right Nat.add 0 (map (fun q => live_rank p (snd q)) ps).

  Lemma raw_rank_cons p q ps :
    raw_rank p (q :: ps) = live_rank p (snd q) + raw_rank p ps.
  Proof.
    reflexivity.
  Qed.

  (** Widening a live receiver never raises its contribution to the rank. *)
  Lemma live_widen_le p a b : S.leb a S.bot = false ->
    live_rank p (S.widen p a b) <= live_rank p a.
  Proof.
    intro Hbot; pose proof (S.wrank_widen_le p a b (nonbottom_test a Hbot)) as Hrank.
    unfold live_rank; rewrite Hbot; destruct (S.leb (S.widen p a b) S.bot); lia.
  Qed.

  (** An unstable live receiver strictly lowers its contribution to the rank. *)
  Lemma live_widen_lt p a b : S.leb a S.bot = false -> S.leb b a = false ->
    live_rank p (S.widen p a b) < live_rank p a.
  Proof.
    intros Hbot Hunstable.
    pose proof (S.wrank_widen p a b (nonbottom_test a Hbot) Hunstable) as Hrank.
    unfold live_rank; rewrite Hbot; destruct (S.leb (S.widen p a b) S.bot); lia.
  Qed.

  (** A receiver of an uncovered part has an unstable collapsed candidate. *)
  Lemma received_unstable a (qs : list (option Tk.t * S.t)) q :
    In q qs -> S.leb (snd q) a = false ->
    S.leb (collapse_with S.bot S.join (a :: map snd qs)) a = false.
  Proof.
    intros Hq Hnot; destruct (S.leb (collapse_with S.bot S.join (a :: map snd qs)) a)
      eqn:Hle; auto.
    assert (Hcover : S.leb (snd q) (collapse_with S.bot S.join (a :: map snd qs)) = true).
    { apply collapse_covers; right; apply in_map; exact Hq. }
    pose proof (S.leb_trans _ _ _ Hcover Hle); congruence.
  Qed.

  (** Absorption never raises the sum of the live component ranks. *)
  Lemma absorb_rank_le p strays fresh old :
    raw_rank p (absorb Tk.eqb S.leb S.bot S.join (S.widen p) strays fresh old) <=
      raw_rank p old.
  Proof.
    revert strays; induction old as [|r old IH]; intro strays; cbn [absorb].
    - reflexivity.
    - destruct (S.leb (snd r) S.bot) eqn:Hbot; rewrite !raw_rank_cons; cbn [snd].
      + specialize (IH strays); lia.
      + pose proof (live_widen_le p (snd r)
          (collapse_with S.bot S.join (snd r :: map snd
            (filter (fun q => label_eqb Tk.eqb (fst r) (fst q)) fresh ++ strays))) Hbot).
        specialize (IH []); lia.
  Qed.

  (** Receiving one uncovered input strictly lowers the head contribution. *)
  Lemma receive_rank_lt p strays fresh r q : S.leb (snd r) S.bot = false ->
    S.leb (snd q) (snd r) = false ->
    (In q strays \/ (In q fresh /\ label_eqb Tk.eqb (fst r) (fst q) = true)) ->
    live_rank p (S.widen p (snd r) (collapse_with S.bot S.join (snd r :: map snd
      (filter (fun q => label_eqb Tk.eqb (fst r) (fst q)) fresh ++ strays)))) <
      live_rank p (snd r).
  Proof.
    intros Hbot Hnot Hreceive; apply live_widen_lt; [exact Hbot|].
    eapply received_unstable; [|exact Hnot].
    apply in_or_app; destruct Hreceive as [Hstray|[Hfresh Hlabel]]; auto.
    left; apply filter_In; auto.
  Qed.

  (** A fresh input routed by its label forces one strict rank decrease. *)
  Lemma absorb_rank_label p strays fresh old q : In q fresh ->
    (forall r, In r old -> S.leb (snd q) (snd r) = false) ->
    (exists r, In r old /\ S.leb (snd r) S.bot = false /\
      label_eqb Tk.eqb (fst r) (fst q) = true) ->
    raw_rank p (absorb Tk.eqb S.leb S.bot S.join (S.widen p) strays fresh old) <
      raw_rank p old.
  Proof.
    revert strays; induction old as [|r old IH]; intros strays Hfresh Hnot [s [Hs [Hsbot Hlabel]]].
    - contradiction.
    - destruct Hs as [<-|Hs].
      + cbn [absorb]; rewrite Hsbot, !raw_rank_cons; cbn [snd].
        pose proof (receive_rank_lt p strays fresh r q Hsbot
          (Hnot r (or_introl eq_refl)) (or_intror (conj Hfresh Hlabel))) as Hhead.
        pose proof (absorb_rank_le p [] fresh old); lia.
      + assert (Hnot_tail : forall t, In t old -> S.leb (snd q) (snd t) = false).
        { intros t Ht; apply Hnot; now right. }
        cbn [absorb]; destruct (S.leb (snd r) S.bot) eqn:Hbot;
          rewrite !raw_rank_cons; cbn [snd].
        * specialize (IH strays Hfresh Hnot_tail
            (ex_intro _ s (conj Hs (conj Hsbot Hlabel)))); lia.
        * specialize (IH [] Hfresh Hnot_tail
            (ex_intro _ s (conj Hs (conj Hsbot Hlabel)))).
          pose proof (live_widen_le p (snd r)
            (collapse_with S.bot S.join (snd r :: map snd
              (filter (fun q => label_eqb Tk.eqb (fst r) (fst q)) fresh ++ strays))) Hbot).
          lia.
  Qed.

  (** A stray forces a strict decrease at the first live receiver. *)
  Lemma absorb_rank_stray p strays fresh old q : In q strays ->
    (forall r, In r old -> S.leb (snd q) (snd r) = false) ->
    (exists r, In r old /\ S.leb (snd r) S.bot = false) ->
    raw_rank p (absorb Tk.eqb S.leb S.bot S.join (S.widen p) strays fresh old) <
      raw_rank p old.
  Proof.
    induction old as [|r old IH]; intros Hstray Hnot [s [Hs Hsbot]]; [contradiction|].
    cbn [absorb]; destruct (S.leb (snd r) S.bot) eqn:Hbot;
      rewrite !raw_rank_cons; cbn [snd].
    - destruct Hs as [<-|Hs]; [congruence|].
      assert (Hnot_tail : forall t, In t old -> S.leb (snd q) (snd t) = false).
      { intros t Ht; apply Hnot; now right. }
      specialize (IH Hstray Hnot_tail (ex_intro _ s (conj Hs Hsbot))); lia.
    - pose proof (receive_rank_lt p strays fresh r q Hbot
        (Hnot r (or_introl eq_refl)) (or_introl Hstray)) as Hhead.
      pose proof (absorb_rank_le p [] fresh old); lia.
  Qed.

  (** An unstable widening from a nonbottom strictly decreases rank. *)
  Lemma wrank_widen : forall p a b, is_bot a = false -> leb b a = false ->
    wrank p (widen p a b) < wrank p a.
  Proof.
    intros p a b Hbot Hunstable.
    change (raw_rank p (proj1_sig (widen p a b)) < raw_rank p (proj1_sig a)).
    rewrite widen_raw, Hunstable, Hbot.
    destruct (fresh_exists a b Hunstable) as [q Hfresh].
    pose proof (proj1 (fresh_spec _ _ q) Hfresh) as [_ [_ Hnot]].
    destruct (existsb (fun r => negb (S.leb (snd r) S.bot) &&
      label_eqb Tk.eqb (fst r) (fst q)) (proj1_sig a)) eqn:Hlabel.
    - eapply absorb_rank_label; [exact Hfresh | exact Hnot |].
      apply existsb_exists in Hlabel; destruct Hlabel as [r [Hr Hlabel]].
      apply andb_true_iff in Hlabel; destruct Hlabel as [Hrbot Hlabel].
      apply negb_true_iff in Hrbot; exists r; auto.
    - eapply absorb_rank_stray; [|exact Hnot |exact (forallb_false_member _ _ Hbot)].
      unfold stray_parts; apply filter_In; split; [exact Hfresh|].
      now rewrite Hlabel.
  Qed.
  (** Widening from a nonbottom does not increase rank. *)
  Lemma wrank_widen_le : forall p a b, is_bot a = false -> wrank p (widen p a b) <= wrank p a.
  Proof.
    intros p a b Hbot; destruct (leb b a) eqn:Hstable.
    - rewrite widen_stable by exact Hstable; reflexivity.
    - apply Nat.lt_le_incl, wrank_widen; assumption.
  Qed.
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
  Module ValueJoins := ValueJoinBudget L V C.
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
  (** One growth step reserves every public component rate and fixed boundary size. *)
  Local Definition growth : N := (4 * (Tk.c_key + S.c_lat + S.c_state + V.c_val +
    N.of_nat (C.k + S.size S.bot + S.wunits S.bot + V.size V.bot + 1) + 3))%N.
  Local Definition scale : N := (growth ^ N.of_nat (2 * C.k + 4))%N.
  Definition k_partition : N := (64 * (scale + 1) * (scale + 1) *
    (scale + 1) * (scale + 1))%N.
  Definition c_lat : N := (8 * (k_partition + 1) * (k_partition + 1) *
    (k_partition + 1))%N.
  Definition c_state : N := (k_partition * (S.c_state + k_partition + 1))%N.
  Definition c_partition : N := (4 * (k_partition + 1) * (k_partition + 1))%N.

  Local Lemma growth_positive : (2 <= growth)%N.
  Proof.
    unfold growth; lia.
  Qed.

  Local Lemma growth_lat : (2 * (S.c_lat + 1) <= growth)%N.
  Proof.
    unfold growth; lia.
  Qed.

  Local Lemma growth_cap : (N.of_nat (C.k + 1) <= growth)%N.
  Proof.
    unfold growth; repeat rewrite Nat2N.inj_add; lia.
  Qed.

  Local Lemma scale_power n : n <= 2 * C.k + 4 -> (growth ^ N.of_nat n <= scale)%N.
  Proof.
    intro Hn; unfold scale; apply N.pow_le_mono_r.
    - pose proof growth_positive; lia.
    - now apply time_of_nat_le.
  Qed.

  Local Lemma scale_growth : (growth <= scale)%N.
  Proof.
    pose proof (scale_power 1 ltac:(lia)); rewrite N.pow_1_r in H; exact H.
  Qed.

  Local Lemma k_partition_min : (64 <= k_partition)%N.
  Proof.
    unfold k_partition; nia.
  Qed.

  (** The shared value-join coefficient fits the partition's fixed plan coefficient. *)
  Local Lemma value_coefficient : (ValueJoins.coefficient <= k_partition)%N.
  Proof.
    assert (Hvalue : (ValueJoins.growth <= growth)%N).
    { unfold ValueJoins.growth, growth; lia. }
    assert (Hbot : (N.of_nat (V.size V.bot) + 1 <= growth)%N).
    { unfold growth; repeat rewrite Nat2N.inj_add; lia. }
    pose proof (N.pow_le_mono_l _ _ (N.of_nat (C.k + 1)) Hvalue) as Hpower.
    pose proof (N.mul_le_mono _ _ _ _ Hpower Hbot) as Hbase.
    assert (Hcombined : (growth ^ N.of_nat (C.k + 1) * growth =
      growth ^ N.of_nat (C.k + 2))%N).
    { replace (C.k + 2) with (Datatypes.S (C.k + 1)) by lia.
      rewrite Nat2N.inj_succ, N.pow_succ_r'; ring. }
    rewrite Hcombined in Hbase.
    pose proof (scale_power (C.k + 2) ltac:(lia)) as Hscale.
    pose proof growth_cap; pose proof scale_growth.
    unfold ValueJoins.coefficient, ValueJoins.base_scale, k_partition; nia.
  Qed.

  (** Adding a fixed callback overhead only changes the common coefficient. *)
  Local Lemma sum_shift {A} (f : A -> N) c xs : (1 <= c)%N ->
    (fold_right N.add 0%N (map (fun x => f x + c)%N xs) <=
      c * fold_right N.add 0%N (map (fun x => f x + 1)%N xs))%N.
  Proof.
    intro Hc; induction xs as [|x xs IH]; cbn [map fold_right]; nia.
  Qed.

  (** Mapping parts pays for the value callback and constant label projections. *)
  Local Lemma map_bounded_clock f T_f a :
    (T_map_bounded f T_f a <= 4 *
      (fold_right N.add 0%N (map (fun q => T_f (snd q) + 1)%N (proj1_sig a)) + 1))%N.
  Proof.
    destruct a as [ps Hbound]; time_unfold @T_map_bounded; time_simpl.
    cbn [proj1_sig]; clear Hbound; induction ps as [|q ps IH];
      time_unfold @ListDef.T_map; time_simpl; cbn [map fold_right] in *; nia.
  Qed.

  (** The mapped transfer contract sums the component work of every part. *)
  Local Lemma map_transfer_clock f T_f work c a :
    (forall s, (T_f s <= c * N.of_nat (work s + 1))%N) ->
    (T_map_bounded f T_f a + 1 <= 8 * (c + 1) * N.of_nat
      (fold_right Nat.add 0%nat (map (fun q => work (snd q) + 1)%nat (proj1_sig a)) + 1))%N.
  Proof.
    intro Hwork; pose proof (map_bounded_clock f T_f a) as Hmap.
    pose proof (ValueJoins.sum_cost (fun q => (T_f (snd q) + 1)%N)
      (fun q => work (snd q) + 1)%nat (c + 1)%N (proj1_sig a)) as Hsum.
    assert (Hcallback : forall q, In q (proj1_sig a) ->
      (T_f (snd q) + 1 <= (c + 1) * N.of_nat (work (snd q) + 1))%N).
    { intros q Hq; pose proof (Hwork (snd q)); rewrite Nat2N.inj_add in *; nia. }
    specialize (Hsum Hcallback); rewrite Nat2N.inj_add; nia.
  Qed.

  (** State-list size pays for each input cell as well as its stored value. *)
  Local Definition states_size (xs : list S.t) :=
    fold_right (fun a n => S.size a + 1 + n) 0 xs.

  Local Lemma states_size_sum xs :
    states_size xs = fold_right Nat.add 0 (map S.size xs) + length xs.
  Proof.
    induction xs as [|x xs IH]; [reflexivity|].
    change (S.size x + 1 + states_size xs =
      S.size x + fold_right Nat.add 0 (map S.size xs) + Datatypes.S (length xs)).
    rewrite IH; lia.
  Qed.

  Local Lemma join_step_budget a b tail :
    (1 + S.T_join a b + N.of_nat (S.size (S.join a b)) + tail + 1 <=
      growth * (N.of_nat (S.size a) + N.of_nat (S.size b) + tail + 2))%N.
  Proof.
    pose proof (S.T_join_le a b); pose proof (JS.join_size a b).
    pose proof growth_lat; repeat rewrite Nat2N.inj_add in *; nia.
  Qed.

  (** The join fold tracks both its clock and the size supplied to its next call. *)
  Local Lemma fold_clock_size xs : forall a,
    (List.T_fold_left S.join S.T_join xs a +
      N.of_nat (S.size (fold_left S.join xs a)) + 1 <=
      growth ^ N.of_nat (length xs + 1) * N.of_nat (S.size a + states_size xs + 1))%N.
  Proof.
    induction xs as [|x xs IH]; intro a.
    - time_unfold @List.T_fold_left; cbn [fold_left length states_size fold_right].
      rewrite N.pow_1_r; repeat rewrite Nat2N.inj_add.
      pose proof growth_positive; nia.
    - specialize (IH (S.join a x)).
      pose proof (join_step_budget a x (N.of_nat (states_size xs))) as Hstep.
      set (power := (growth ^ N.of_nat (length xs + 1))%N) in *.
      assert (Hpower : (1 <= power)%N).
      { unfold power; apply N.pow_lower_bound; pose proof growth_positive; lia. }
      pose proof (N.mul_le_mono_l _ _ power Hstep) as Hscaled.
      pose proof (N.mul_le_mono_r 1 power (1 + S.T_join a x)%N Hpower) as Hpaid.
      time_unfold @List.T_fold_left; cbn [fold_left length].
      replace (Datatypes.S (length xs) + 1) with (Datatypes.S (length xs + 1)) by lia.
      rewrite Nat2N.inj_succ, N.pow_succ_r'; fold power.
      set (budget := (N.of_nat (S.size a) + N.of_nat (S.size x) +
        N.of_nat (states_size xs) + 2)%N) in *.
      assert (Hbudget : N.of_nat (S.size a + states_size (x :: xs) + 1) = budget).
      { unfold budget, states_size; cbn [fold_right]; repeat rewrite Nat2N.inj_add; lia. }
      rewrite Hbudget; fold budget in Hscaled.
      replace (growth * power * budget)%N with (power * (growth * budget))%N by ring.
      repeat rewrite Nat2N.inj_add in IH.
      repeat rewrite N.mul_add_distr_l in IH, Hscaled, Hpaid.
      rewrite N.mul_1_l in Hpaid; lia.
  Qed.

  (** The fixed cap pays for every join in a collapse, including the empty bottom case. *)
  Local Lemma collapse_budget xs : length xs <= 2 * C.k + 1 ->
    (T_collapse_with S.bot S.join S.T_join xs +
      N.of_nat (S.size (collapse_with S.bot S.join xs)) + 1 <=
      scale * N.of_nat (states_size xs + 1))%N.
  Proof.
    intro Hlength; destruct xs as [|x xs].
    - assert (Hbot : (N.of_nat (S.size S.bot) + 2 <= growth)%N).
      { unfold growth; repeat rewrite Nat2N.inj_add; lia. }
      pose proof scale_growth; time_unfold @T_collapse_with.
      cbn [collapse_with states_size fold_right]; lia.
    - pose proof (fold_clock_size xs x) as Hfold.
      pose proof growth_positive as Hgrowth.
      assert (Hpower : (1 <= growth ^ N.of_nat (length xs + 1))%N).
      { apply N.pow_lower_bound; lia. }
      pose proof (scale_power (length (x :: xs) + 1) ltac:(cbn [length] in *; lia))
        as Hscale.
      time_unfold @T_collapse_with; cbn [collapse_with length] in *.
      replace (Datatypes.S (length xs) + 1) with (Datatypes.S (length xs + 1)) in Hscale by lia.
      rewrite Nat2N.inj_succ, N.pow_succ_r' in Hscale.
      unfold states_size in *; cbn [fold_right] in *; repeat rewrite Nat2N.inj_add in *.
      nia.
  Qed.

  (** Each join's unit budget composes with the units of the unvisited suffix. *)
  Local Lemma join_units_step a b tail :
    (N.of_nat (S.wunits (S.join a b)) + tail + 1 <=
      growth * (N.of_nat (S.wunits a) + N.of_nat (S.wunits b) + tail + 1))%N.
  Proof.
    pose proof (JU.join_wunits a b); pose proof growth_lat.
    repeat rewrite Nat2N.inj_add in *; nia.
  Qed.

  (** A bounded join fold has a fixed multiplicative widening-unit budget. *)
  Local Lemma fold_units xs : forall a,
    (N.of_nat (S.wunits (fold_left S.join xs a)) + 1 <=
      growth ^ N.of_nat (length xs + 1) *
        N.of_nat (S.wunits a + fold_right Nat.add 0%nat (map S.wunits xs) + 1))%N.
  Proof.
    induction xs as [|x xs IH]; intro a.
    - cbn [fold_left length map fold_right]; rewrite N.pow_1_r.
      repeat rewrite Nat2N.inj_add; pose proof growth_positive; nia.
    - specialize (IH (S.join a x)).
      pose proof (join_units_step a x
        (N.of_nat (fold_right Nat.add 0 (map S.wunits xs)))) as Hstep.
      pose proof (N.mul_le_mono_l _ _ (growth ^ N.of_nat (length xs + 1))%N Hstep)
        as Hscaled.
      cbn [fold_left length map fold_right].
      replace (Datatypes.S (length xs) + 1) with (Datatypes.S (length xs + 1)) by lia.
      rewrite Nat2N.inj_succ, N.pow_succ_r'.
      repeat rewrite Nat2N.inj_add in IH |- *.
      nia.
  Qed.

  Local Lemma collapse_units_budget xs : length xs <= 2 * C.k + 1 ->
    (N.of_nat (S.wunits (collapse_with S.bot S.join xs)) <=
      scale * N.of_nat (fold_right Nat.add 0%nat (map S.wunits xs) + 1))%N.
  Proof.
    intro Hlength; destruct xs as [|x xs].
    - assert (Hbot : (N.of_nat (S.wunits S.bot) <= growth)%N).
      { unfold growth; repeat rewrite Nat2N.inj_add; lia. }
      pose proof scale_growth; cbn [collapse_with map fold_right]; lia.
    - pose proof (fold_units xs x) as Hfold.
      pose proof (scale_power (length xs + 1) ltac:(cbn [length] in Hlength; lia)) as Hscale.
      cbn [collapse_with map fold_right].
      eapply N.le_trans; [|apply N.mul_le_mono_r; exact Hscale]; lia.
  Qed.

  Local Lemma parts_size_cons q ps : parts_size Tk.bits S.size (q :: ps) =
    S.size (snd q) + label_bits Tk.bits (fst q) + 1 + parts_size Tk.bits S.size ps.
  Proof.
    reflexivity.
  Qed.

  Local Lemma parts_units_cons (q : option Tk.t * S.t) ps :
    parts_units S.wunits (q :: ps) = S.wunits (snd q) + parts_units S.wunits ps.
  Proof.
    reflexivity.
  Qed.

  Local Lemma parts_size_length ps : length ps + 1 <= parts_size Tk.bits S.size ps.
  Proof.
    induction ps as [|q ps IH]; [reflexivity|].
    rewrite parts_size_cons; cbn [length]; lia.
  Qed.

  Local Lemma parts_size_member q ps : In q ps -> S.size (snd q) + 1 <=
    parts_size Tk.bits S.size ps.
  Proof.
    induction ps as [|r ps IH]; intro Hq; [contradiction|].
    rewrite parts_size_cons; destruct Hq as [<-|Hq]; [lia|].
    specialize (IH Hq); lia.
  Qed.

  Local Definition comparison_work (ps qs : list (option Tk.t * S.t)) : N :=
    fold_right N.add 0%N (map (fun q => S.T_leb (snd q) S.bot +
      fold_right N.add 0%N (map (fun r => S.T_leb (snd q) (snd r) + 1)%N qs) + 1)%N ps).

  Local Lemma exists_parts_clock (q : option Tk.t * S.t) (qs : list (option Tk.t * S.t)) :
    (List.T_existsb (fun r => S.leb (snd q) (snd r))
      (fun r => 1 + (Datatypes.T_snd q + Datatypes.T_snd r +
        S.T_leb (snd q) (snd r)))%N qs <=
      5 * (fold_right N.add 0%N (map (fun r => S.T_leb (snd q) (snd r) + 1)%N qs) + 1))%N.
  Proof.
    induction qs as [|r qs IH]; time_unfold @List.T_existsb; time_simpl;
      cbn [map fold_right]; [nia|].
    revert IH; time_simpl; intro IH; nia.
  Qed.

  Local Lemma leb_clock_work a b :
    (T_leb a b <= 16 * (comparison_work (proj1_sig a) (proj1_sig b) + 1))%N.
  Proof.
    destruct a as [ps Hps], b as [qs Hqs].
    time_unfold @T_leb; time_simpl; cbn [proj1_sig]; unfold comparison_work.
    clear Hps Hqs; induction ps as [|q ps IH].
    - time_unfold @List.T_forallb; cbn [map fold_right]; nia.
    - pose proof (exists_parts_clock q qs) as Hrow.
      revert Hrow; time_simpl; intro Hrow.
      time_unfold @List.T_forallb; time_simpl; cbn [map fold_right] in *; nia.
  Qed.

  Local Lemma is_bot_clock_work a :
    (T_is_bot a <= 8 * (comparison_work (proj1_sig a) [] + 1))%N.
  Proof.
    destruct a as [ps Hps]; time_unfold @T_is_bot; time_simpl; cbn [proj1_sig].
    unfold comparison_work; clear Hps; induction ps as [|q ps IH];
      time_unfold @List.T_forallb; time_simpl; cbn [map fold_right] in *; nia.
  Qed.

  Local Lemma sum_uniform {A} (f : A -> N) xs budget :
    (forall x, In x xs -> (f x <= budget)%N) ->
    (fold_right N.add 0%N (map f xs) <= N.of_nat (length xs) * budget)%N.
  Proof.
    induction xs as [|x xs IH]; intro Hbound; cbn [map fold_right length]; [lia|].
    specialize (IH (fun y Hy => Hbound y (or_intror Hy))).
    pose proof (Hbound x (or_introl eq_refl)); rewrite Nat2N.inj_succ; nia.
  Qed.

  (** The capped comparison grid has a linear budget in the two partitions' total size. *)
  Local Lemma comparison_budget ps qs : length ps <= C.k -> length qs <= C.k ->
    (comparison_work ps qs <= 3 * growth * growth * growth *
      N.of_nat (parts_size Tk.bits S.size ps + parts_size Tk.bits S.size qs + 1))%N.
  Proof.
    intros Hps Hqs; set (mass := N.of_nat
      (parts_size Tk.bits S.size ps + parts_size Tk.bits S.size qs + 1)).
    assert (Hmass : (1 <= mass)%N) by (unfold mass; lia).
    assert (Hnp : (N.of_nat (length ps) <= growth)%N) by
      (pose proof growth_cap; apply time_of_nat_le in Hps; lia).
    assert (Hnq : (N.of_nat (length qs) <= growth)%N) by
      (pose proof growth_cap; apply time_of_nat_le in Hqs; lia).
    assert (Hrate : (S.c_lat + 1 <= growth)%N) by (pose proof growth_lat; lia).
    assert (Hbot : (N.of_nat (S.size S.bot + 1) <= growth)%N).
    { unfold growth; repeat rewrite Nat2N.inj_add; lia. }
    assert (Hrow : forall q, In q ps ->
      (S.T_leb (snd q) S.bot + fold_right N.add 0%N
        (map (fun r => S.T_leb (snd q) (snd r) + 1)%N qs) + 1 <=
        (2 * growth * growth + 1) * mass)%N).
    { intros q Hq; pose proof (parts_size_member q ps Hq) as Hsizeq.
      assert (Hinner : forall r, In r qs ->
        (S.T_leb (snd q) (snd r) + 1 <= (S.c_lat + 1) * mass)%N).
      { intros r Hr; pose proof (parts_size_member r qs Hr) as Hsizer.
        pose proof (S.T_leb_le (snd q) (snd r)); unfold mass;
          repeat rewrite Nat2N.inj_add in *; nia. }
      pose proof (sum_uniform (fun r => (S.T_leb (snd q) (snd r) + 1)%N)
        qs ((S.c_lat + 1) * mass)%N Hinner) as Hsum.
      pose proof (S.T_leb_le (snd q) S.bot) as Hbottom.
      assert (Hinput : (N.of_nat (S.size (snd q) + S.size S.bot + 1) <=
        N.of_nat (S.size S.bot + 1) * mass)%N).
      { unfold mass; repeat rewrite Nat2N.inj_add; nia. }
      assert (Hsum_bound : (fold_right N.add 0%N
        (map (fun r => S.T_leb (snd q) (snd r) + 1)%N qs) <=
        growth * growth * mass)%N).
      { eapply N.le_trans; [exact Hsum|].
        replace (N.of_nat (length qs) * ((S.c_lat + 1) * mass))%N with
          ((N.of_nat (length qs) * (S.c_lat + 1)) * mass)%N by ring.
        apply N.mul_le_mono_r, N.mul_le_mono; assumption. }
      assert (Hbottom_bound : (S.T_leb (snd q) S.bot <= growth * growth * mass)%N).
      { eapply N.le_trans; [exact Hbottom|].
        eapply N.le_trans; [apply N.mul_le_mono_l; exact Hinput|].
        replace (S.c_lat * (N.of_nat (S.size S.bot + 1) * mass))%N with
          ((S.c_lat * N.of_nat (S.size S.bot + 1)) * mass)%N by ring.
        apply N.mul_le_mono_r, N.mul_le_mono; [lia|exact Hbot]. }
      nia. }
    pose proof (sum_uniform _ ps ((2 * growth * growth + 1) * mass)%N Hrow) as Hsum.
    unfold comparison_work; eapply N.le_trans; [exact Hsum|].
    replace (N.of_nat (length ps) * ((2 * growth * growth + 1) * mass))%N with
      ((N.of_nat (length ps) * (2 * growth * growth + 1)) * mass)%N by ring.
    apply N.mul_le_mono_r.
    eapply N.le_trans; [apply N.mul_le_mono_r; exact Hnp|].
    pose proof growth_positive; nia.
  Qed.

  Local Lemma comparison_coefficient : (16 * (3 * growth * growth * growth + 1) <=
    k_partition)%N.
  Proof.
    assert (Hcube : (growth * growth * growth <= scale * scale * scale)%N).
    { apply N.mul_le_mono; [apply N.mul_le_mono |]; exact scale_growth. }
    unfold k_partition; nia.
  Qed.

  Local Lemma leb_budget a b :
    (T_leb a b <= k_partition * N.of_nat (size a + size b + 1))%N.
  Proof.
    pose proof (leb_clock_work a b) as Hclock.
    pose proof (comparison_budget (proj1_sig a) (proj1_sig b)
      (proj1 (Nat.leb_le _ _) (proj2_sig a))
      (proj1 (Nat.leb_le _ _) (proj2_sig b))) as Hwork.
    pose proof comparison_coefficient; unfold size; rewrite Nat2N.inj_add; nia.
  Qed.

  Local Lemma is_bot_budget a :
    (T_is_bot a <= k_partition * N.of_nat (size a + 1))%N.
  Proof.
    pose proof (is_bot_clock_work a) as Hclock.
    pose proof (comparison_budget (proj1_sig a) []
      (proj1 (Nat.leb_le _ _) (proj2_sig a)) ltac:(cbn; lia)) as Hwork.
    pose proof comparison_coefficient; unfold size; cbn [parts_size fold_right] in Hwork.
    repeat rewrite Nat2N.inj_add in *; nia.
  Qed.

  Local Lemma states_size_parts ps :
    states_size (map snd ps) + 1 <= parts_size Tk.bits S.size ps.
  Proof.
    induction ps as [|q ps IH]; [reflexivity|].
    change (S.size (snd q) + 1 + states_size (map snd ps) + 1 <=
      S.size (snd q) + label_bits Tk.bits (fst q) + 1 + parts_size Tk.bits S.size ps).
    lia.
  Qed.

  Local Lemma parts_units_map (ps : list (option Tk.t * S.t)) :
    fold_right Nat.add 0 (map S.wunits (map snd ps)) = parts_units S.wunits ps.
  Proof.
    induction ps as [|q ps IH]; [reflexivity|].
    change (S.wunits (snd q) + fold_right Nat.add 0 (map S.wunits (map snd ps)) =
      S.wunits (snd q) + parts_units S.wunits ps).
    now rewrite IH.
  Qed.

  Local Lemma map_snd_clock (ps : list (option Tk.t * S.t)) :
    (ListDef.T_map snd (fun q => Datatypes.T_snd q) ps <=
      2 * N.of_nat (length ps) + 1)%N.
  Proof.
    apply (ListDef.T_map_le snd (fun q => Datatypes.T_snd q) 1%N ps).
    intro q; time_step.
  Qed.

  (** Keeping a prefix and collapsing its suffix pays for the same raw input size. *)
  Local Lemma fit_tail_budget n ps : length ps <= 2 * C.k ->
    (T_fit_tail S.bot S.join S.T_join n ps +
      N.of_nat (parts_size Tk.bits S.size (fit_tail S.bot S.join n ps)) + 1 <=
      (scale + 8) * N.of_nat (parts_size Tk.bits S.size ps + 1))%N.
  Proof.
    assert (Hbase : forall ps, length ps <= 2 * C.k ->
      (T_fit_tail S.bot S.join S.T_join 0 ps +
        N.of_nat (parts_size Tk.bits S.size (fit_tail S.bot S.join 0 ps)) + 1 <=
        (scale + 8) * N.of_nat (parts_size Tk.bits S.size ps + 1))%N).
    { intros qs Hlength.
      pose proof (collapse_budget (map snd qs) ltac:(rewrite length_map; lia)) as Hcollapse.
      pose proof (map_snd_clock qs) as Hmap.
      pose proof (states_size_parts qs) as Hsize; apply time_of_nat_le in Hsize.
      pose proof (parts_size_length qs) as Hlen; apply time_of_nat_le in Hlen.
      time_unfold @T_fit_tail; cbn [fit_tail parts_size fold_right label_bits fst snd].
      repeat rewrite Nat2N.inj_add in *; nia. }
    revert ps; induction n as [|n IH]; intros ps Hlength; [now apply Hbase|].
    destruct ps as [|q ps]; [apply Hbase; exact Hlength|].
    specialize (IH ps ltac:(cbn [length] in Hlength; lia)).
    time_unfold @T_fit_tail; cbn [fit_tail]; rewrite !parts_size_cons.
    repeat rewrite Nat2N.inj_add in *; nia.
  Qed.

  (** Prefix retention and suffix collapse also preserve a linear unit budget. *)
  Local Lemma fit_tail_units n (ps : list (option Tk.t * S.t)) : length ps <= 2 * C.k ->
    (N.of_nat (parts_units S.wunits (fit_tail S.bot S.join n ps)) <=
      scale * N.of_nat (parts_units S.wunits ps + 1))%N.
  Proof.
    assert (Hbase : forall ps : list (option Tk.t * S.t), length ps <= 2 * C.k ->
      (N.of_nat (parts_units S.wunits (fit_tail S.bot S.join 0 ps)) <=
        scale * N.of_nat (parts_units S.wunits ps + 1))%N).
    { intros qs Hlength.
      pose proof (collapse_units_budget (map snd qs) ltac:(rewrite length_map; lia)) as Hbound.
      rewrite parts_units_map in Hbound.
      cbn [fit_tail parts_units fold_right snd]; now rewrite Nat.add_0_r. }
    revert ps; induction n as [|n IH]; intros ps Hlength; [now apply Hbase|].
    destruct ps as [|q ps]; [apply Hbase; exact Hlength|].
    specialize (IH ps ltac:(cbn [length] in Hlength; lia)).
    change (N.of_nat (S.wunits (snd q) +
      parts_units S.wunits (fit_tail S.bot S.join n ps)) <=
      scale * N.of_nat (S.wunits (snd q) + parts_units S.wunits ps + 1))%N.
    pose proof growth_positive; pose proof scale_growth.
    repeat rewrite Nat2N.inj_add in *; nia.
  Qed.

  (** Restoring the cap charges its count, comparison and one fitted suffix. *)
  Local Lemma fit_budget ps : length ps <= 2 * C.k ->
    (T_fit_parts S.bot S.join S.T_join C.k ps +
      N.of_nat (parts_size Tk.bits S.size (fit_parts S.bot S.join C.k ps)) + 1 <=
      (scale + 16) * N.of_nat (parts_size Tk.bits S.size ps + 1))%N.
  Proof.
    intro Hlength; pose proof (Datatypes.T_length_le ps) as Hcount.
    pose proof (Nat.T_leb_le (length ps) C.k) as Hcompare.
    pose proof (parts_size_length ps) as Hlen; apply time_of_nat_le in Hlen.
    time_unfold @T_fit_parts; unfold fit_parts; destruct C.k as [|n] eqn:Hcap.
    - cbn [parts_size fold_right]; rewrite Nat2N.inj_add; nia.
    - pose proof (fit_tail_budget n ps ltac:(rewrite Hcap; exact Hlength)) as Htail.
      destruct (Nat.leb (length ps) (Datatypes.S n));
        repeat rewrite Nat2N.inj_add in *; nia.
  Qed.

  Local Definition part_size (q : option Tk.t * S.t) :=
    S.size (snd q) + label_bits Tk.bits (fst q) + 1.

  (** Optional-label comparison charges only the first label's bits. *)
  Local Lemma label_clock a b :
    (T_label_eqb Tk.eqb Tk.T_eqb a b <=
      (Tk.c_key + 1) * N.of_nat (label_bits Tk.bits a + 1))%N.
  Proof.
    destruct a as [a|], b as [b|]; time_unfold @T_label_eqb; cbn [label_bits];
      repeat rewrite Nat2N.inj_add; try nia.
    pose proof (Tk.T_eqb_le a b); rewrite Nat2N.inj_add in H; nia.
  Qed.

  (** Inserting a part accounts for one label scan and at most one component join. *)
  Local Lemma insert_budget q ps :
    (T_insert_part Tk.eqb Tk.T_eqb S.join S.T_join q ps +
      N.of_nat (parts_size Tk.bits S.size (insert_part Tk.eqb S.join q ps)) + 2 <=
      growth * N.of_nat (parts_size Tk.bits S.size ps + part_size q + 1))%N.
  Proof.
    assert (Hrate : (Tk.c_key + 2 * S.c_lat + 12 <= growth)%N) by
      (unfold growth; lia).
    induction ps as [|r ps IH].
    - time_unfold @T_insert_part; cbn [insert_part parts_size fold_right].
      unfold part_size; repeat rewrite Nat2N.inj_add; nia.
    - pose proof (label_clock (fst r) (fst q)) as Hlabel.
      time_unfold @T_insert_part; time_simpl; cbn [insert_part].
      destruct (label_eqb Tk.eqb (fst r) (fst q)); rewrite !parts_size_cons; cbn [fst snd].
      + pose proof (S.T_join_le (snd r) (snd q)) as Hclock.
        pose proof (JS.join_size (snd r) (snd q)) as Hsize.
        unfold part_size in *; repeat rewrite Nat2N.inj_add in *; nia.
      + unfold part_size in *; repeat rewrite Nat2N.inj_add in *; nia.
  Qed.

  (** Repeated insertion tracks its changing accumulator size and actual clock. *)
  Local Lemma merge_fold_budget qs : forall ps,
    (List.T_fold_left (fun acc q => insert_part Tk.eqb S.join q acc)
      (fun acc q => 1 + T_insert_part Tk.eqb Tk.T_eqb S.join S.T_join q acc)%N qs ps +
      N.of_nat (parts_size Tk.bits S.size
        (fold_left (fun acc q => insert_part Tk.eqb S.join q acc) qs ps)) + 1 <=
      growth ^ N.of_nat (length qs + 1) *
        N.of_nat (parts_size Tk.bits S.size ps + parts_size Tk.bits S.size qs + 1))%N.
  Proof.
    induction qs as [|q qs IH]; intro ps.
    - time_unfold @List.T_fold_left; cbn [fold_left length].
      change (1 + N.of_nat (parts_size Tk.bits S.size ps) + 1 <=
        growth ^ 1 * N.of_nat (parts_size Tk.bits S.size ps + 1 + 1))%N.
      rewrite N.pow_1_r; pose proof growth_positive; repeat rewrite Nat2N.inj_add; nia.
    - specialize (IH (insert_part Tk.eqb S.join q ps)).
      pose proof (insert_budget q ps) as Hinsert.
      pose proof growth_positive as Hgrowth.
      set (power := (growth ^ N.of_nat (length qs + 1))%N) in *.
      assert (Hpower : (1 <= power)%N).
      { unfold power; apply N.pow_lower_bound; lia. }
      pose proof (N.mul_le_mono_l _ _ power Hinsert) as Hscaled.
      pose proof (N.mul_le_mono_r 1 power
        (2 + T_insert_part Tk.eqb Tk.T_eqb S.join S.T_join q ps)%N Hpower) as Hpaid.
      time_unfold @List.T_fold_left; cbn [fold_left length].
      replace (Datatypes.S (length qs) + 1) with (Datatypes.S (length qs + 1)) by lia.
      rewrite Nat2N.inj_succ, N.pow_succ_r', parts_size_cons; fold power.
      unfold part_size in Hinsert, Hscaled.
      assert (Htail : (1 <= N.of_nat (parts_size Tk.bits S.size qs))%N).
      { pose proof (parts_size_length qs); lia. }
      repeat rewrite Nat2N.inj_add in IH, Hscaled |- *.
      repeat rewrite N.mul_add_distr_l in IH, Hscaled, Hpaid.
      rewrite N.mul_1_l in Hpaid; nia.
  Qed.

  Local Lemma merge_budget ps qs : length qs <= C.k ->
    (T_merge_parts Tk.eqb Tk.T_eqb S.join S.T_join ps qs +
      N.of_nat (parts_size Tk.bits S.size (merge_parts Tk.eqb S.join ps qs)) + 1 <=
      scale * N.of_nat (parts_size Tk.bits S.size ps + parts_size Tk.bits S.size qs + 1))%N.
  Proof.
    intro Hlength; pose proof (merge_fold_budget qs ps) as Hfold.
    pose proof (scale_power (length qs + 2) ltac:(lia)) as Hscale.
    assert (Hpositive : (1 <= growth ^ N.of_nat (length qs + 1))%N).
    { apply N.pow_lower_bound; pose proof growth_positive; lia. }
    replace (length qs + 2) with (Datatypes.S (length qs + 1)) in Hscale by lia.
    rewrite Nat2N.inj_succ, N.pow_succ_r' in Hscale.
    pose proof growth_positive; time_unfold @T_merge_parts; unfold merge_parts.
    repeat rewrite Nat2N.inj_add in *; nia.
  Qed.

  Local Lemma insert_units_budget q ps :
    (N.of_nat (parts_units S.wunits (insert_part Tk.eqb S.join q ps)) + 1 <=
      growth * N.of_nat (parts_units S.wunits ps + S.wunits (snd q) + 1))%N.
  Proof.
    induction ps as [|r ps IH]; cbn [insert_part].
    - cbn [parts_units fold_right]; pose proof growth_positive.
      repeat rewrite Nat2N.inj_add; nia.
    - destruct (label_eqb Tk.eqb (fst r) (fst q)); cbn [parts_units fold_right snd].
      + pose proof (JU.join_wunits (snd r) (snd q)); pose proof growth_lat.
        repeat rewrite Nat2N.inj_add in *; nia.
      + unfold parts_units in IH; pose proof growth_positive.
        repeat rewrite Nat2N.inj_add in *; nia.
  Qed.

  Local Lemma merge_fold_units qs : forall ps,
    (N.of_nat (parts_units S.wunits
      (fold_left (fun acc q => insert_part Tk.eqb S.join q acc) qs ps)) + 1 <=
      growth ^ N.of_nat (length qs + 1) *
        N.of_nat (parts_units S.wunits ps + parts_units S.wunits qs + 1))%N.
  Proof.
    induction qs as [|q qs IH]; intro ps.
    - change (N.of_nat (parts_units S.wunits ps) + 1 <=
        growth ^ 1 * N.of_nat (parts_units S.wunits ps + 0 + 1))%N.
      rewrite N.pow_1_r.
      pose proof growth_positive; repeat rewrite Nat2N.inj_add; nia.
    - specialize (IH (insert_part Tk.eqb S.join q ps)).
      pose proof (insert_units_budget q ps) as Hinsert.
      pose proof (N.mul_le_mono_l _ _ (growth ^ N.of_nat (length qs + 1))%N Hinsert)
        as Hscaled.
      cbn [fold_left length]; rewrite parts_units_cons.
      replace (Datatypes.S (length qs) + 1) with (Datatypes.S (length qs + 1)) by lia.
      rewrite Nat2N.inj_succ, N.pow_succ_r'; pose proof growth_positive.
      repeat rewrite Nat2N.inj_add in IH, Hscaled |- *; nia.
  Qed.

  (** Uniform bounds with membership hypotheses suffice for filtered sublists. *)
  Local Lemma route_filter_uniform {A} (f : A -> bool) (T_f : A -> N) xs budget :
    (forall x, In x xs -> (T_f x <= budget)%N) ->
    (List.T_filter f T_f xs <= N.of_nat (length xs) * (budget + 1) + 1)%N.
  Proof.
    induction xs as [|x xs IH]; intro Hbound.
    - time_unfold @List.T_filter; cbn [length]; lia.
    - specialize (IH (fun y Hy => Hbound y (or_intror Hy))).
      pose proof (Hbound x (or_introl eq_refl)) as Hx.
      time_unfold @List.T_filter; cbn [length]; rewrite Nat2N.inj_succ.
      destruct (f x); nia.
  Qed.

  Local Lemma route_exists_uniform {A} (f : A -> bool) (T_f : A -> N) xs budget :
    (forall x, In x xs -> (T_f x <= budget)%N) ->
    (List.T_existsb f T_f xs <= N.of_nat (length xs) * (budget + 2) + 1)%N.
  Proof.
    induction xs as [|x xs IH]; intro Hbound.
    - time_unfold @List.T_existsb; cbn [length]; lia.
    - specialize (IH (fun y Hy => Hbound y (or_intror Hy))).
      pose proof (Hbound x (or_introl eq_refl)) as Hx.
      time_unfold @List.T_existsb; time_simpl; cbn [length].
      rewrite Nat2N.inj_succ; nia.
  Qed.
  (** Routing reserves a positive fixed rate and the complete input measure. *)
  Local Definition route_scale : N := (scale + 1)%N.
  Local Definition route_measure p (old new : list (option Tk.t * S.t)) : nat :=
    ((parts_units S.wunits old + parts_units S.wunits new + 1) * S.wsize p +
      (parts_size Tk.bits S.size old + parts_size Tk.bits S.size new + S.wsize p + 1))%nat.

  Local Lemma route_rates :
    (2 <= route_scale /\ S.c_lat + 1 <= route_scale /\ Tk.c_key + 1 <= route_scale /\
      N.of_nat (C.k + 1) <= route_scale /\
      N.of_nat (S.size S.bot + 1) <= route_scale)%N.
  Proof.
    pose proof growth_positive; pose proof growth_lat; pose proof growth_cap.
    pose proof scale_growth.
    assert (Hkey : (Tk.c_key + 1 <= growth)%N) by (unfold growth; lia).
    assert (Hbot : (N.of_nat (S.size S.bot + 1) <= growth)%N).
    { unfold growth; repeat rewrite Nat2N.inj_add; lia. }
    unfold route_scale; repeat split; lia.
  Qed.

  (** A filter never increases the stored state-and-label mass or widening units. *)
  Local Lemma route_filter_measures pred ps :
    parts_size Tk.bits S.size (filter pred ps) <= parts_size Tk.bits S.size ps /\
    parts_units S.wunits (filter pred ps) <= parts_units S.wunits ps.
  Proof.
    induction ps as [|q ps [IHsize IHunits]]; cbn [filter]; [split; reflexivity|].
    destruct (pred q); rewrite ?parts_size_cons, ?parts_units_cons; split; lia.
  Qed.

  Local Lemma route_app_measures ps qs :
    parts_size Tk.bits S.size (ps ++ qs) <=
      parts_size Tk.bits S.size ps + parts_size Tk.bits S.size qs /\
    parts_units S.wunits (ps ++ qs) = parts_units S.wunits ps + parts_units S.wunits qs.
  Proof.
    induction ps as [|q ps [IHsize IHunits]]; cbn [app].
    - cbn [parts_size parts_units fold_right]; split; lia.
    - rewrite !parts_size_cons, !parts_units_cons; split; lia.
  Qed.

  Local Lemma route_member_measures q ps : In q ps ->
    S.size (snd q) + 1 <= parts_size Tk.bits S.size ps /\
    label_bits Tk.bits (fst q) + 1 <= parts_size Tk.bits S.size ps /\
    S.wunits (snd q) <= parts_units S.wunits ps.
  Proof.
    induction ps as [|r ps IH]; intro Hin; [contradiction|].
    rewrite parts_size_cons, parts_units_cons.
    destruct Hin as [<-|Hin]; [repeat split; lia|].
    destruct (IH Hin) as [Hs [Hl Hu]]; repeat split; lia.
  Qed.

  (** A receiver may see two candidate sublists, each within the new input's budget. *)
  Local Lemma route_receiver_measures old new r fresh strays :
    In r old -> length fresh <= C.k -> length strays <= C.k ->
    parts_size Tk.bits S.size fresh <= parts_size Tk.bits S.size new ->
    parts_size Tk.bits S.size strays <= parts_size Tk.bits S.size new ->
    parts_units S.wunits fresh <= parts_units S.wunits new ->
    parts_units S.wunits strays <= parts_units S.wunits new ->
    let own := filter (fun q => label_eqb Tk.eqb (fst r) (fst q)) fresh ++ strays in
    let xs := snd r :: map snd own in
    length xs <= 2 * C.k + 1 /\
    states_size xs + 1 <=
      2 * (parts_size Tk.bits S.size old + parts_size Tk.bits S.size new + 1) /\
    fold_right Nat.add 0%nat (map S.wunits xs) + 1 <=
      2 * (parts_units S.wunits old + parts_units S.wunits new + 1).
  Proof.
    intros Hr Hfresh Hstrays Hsf Hss Huf Hus.
    set (selected := filter (fun q => label_eqb Tk.eqb (fst r) (fst q)) fresh).
    destruct (route_filter_measures
      (fun q => label_eqb Tk.eqb (fst r) (fst q)) fresh) as [Hsel_size Hsel_units].
    fold selected in Hsel_size, Hsel_units.
    pose proof (filter_length_le (fun q => label_eqb Tk.eqb (fst r) (fst q)) fresh)
      as Hsel_length; fold selected in Hsel_length.
    destruct (route_app_measures selected strays) as [Hown_size Hown_units].
    destruct (route_member_measures r old Hr) as [Hrsize [Hrlabel Hrunits]].
    pose proof (states_size_parts (selected ++ strays)) as Hstates.
    change (length (snd r :: map snd (selected ++ strays)) <= 2 * C.k + 1 /\
      states_size (snd r :: map snd (selected ++ strays)) + 1 <=
        2 * (parts_size Tk.bits S.size old + parts_size Tk.bits S.size new + 1) /\
      fold_right Nat.add 0%nat (map S.wunits (snd r :: map snd (selected ++ strays))) + 1 <=
        2 * (parts_units S.wunits old + parts_units S.wunits new + 1)).
    cbn [length map fold_right]; rewrite length_map, length_app, parts_units_map.
    change (Datatypes.S (length selected + length strays) <= 2 * C.k + 1 /\
      S.size (snd r) + 1 + states_size (map snd (selected ++ strays)) + 1 <=
        2 * (parts_size Tk.bits S.size old + parts_size Tk.bits S.size new + 1) /\
      S.wunits (snd r) + parts_units S.wunits (selected ++ strays) + 1 <=
        2 * (parts_units S.wunits old + parts_units S.wunits new + 1)).
    repeat split; lia.
  Qed.

  (** The collapsed candidate's size and units pay for the component widening. *)
  Local Lemma route_receiver_join_clock p old new r fresh strays :
    In r old -> length fresh <= C.k -> length strays <= C.k ->
    parts_size Tk.bits S.size fresh <= parts_size Tk.bits S.size new ->
    parts_size Tk.bits S.size strays <= parts_size Tk.bits S.size new ->
    parts_units S.wunits fresh <= parts_units S.wunits new ->
    parts_units S.wunits strays <= parts_units S.wunits new ->
    let own := filter (fun q => label_eqb Tk.eqb (fst r) (fst q)) fresh ++ strays in
    let xs := snd r :: map snd own in
    (T_collapse_with S.bot S.join S.T_join xs +
      S.T_widen p (snd r) (collapse_with S.bot S.join xs) <=
      12 * route_scale * route_scale * N.of_nat (route_measure p old new))%N.
  Proof.
    intros Hr Hfresh Hstrays Hsf Hss Huf Hus.
    pose proof (route_receiver_measures old new r fresh strays
      Hr Hfresh Hstrays Hsf Hss Huf Hus) as Hmeasures.
    cbv zeta in Hmeasures |- *.
    set (xs := snd r :: map snd
      (filter (fun q => label_eqb Tk.eqb (fst r) (fst q)) fresh ++ strays)) in *.
    destruct Hmeasures as [Hlength [Hsize Hunits]].
    destruct (route_member_measures r old Hr) as [Hrsize [Hrlabel Hrunits]].
    destruct route_rates as [Hpositive [Hlat Hrest]].
    pose proof (collapse_budget xs Hlength) as Hcollapse.
    pose proof (collapse_units_budget xs Hlength) as Hcollapse_units.
    set (budget := N.of_nat (route_measure p old new)).
    assert (Hmass : (N.of_nat (parts_size Tk.bits S.size old +
      parts_size Tk.bits S.size new + 1) <= budget)%N) by
      (unfold budget, route_measure; lia).
    assert (Hparam : (N.of_nat (S.wsize p + 1) <= budget)%N) by
      (unfold budget, route_measure; lia).
    assert (Hunit_budget : (N.of_nat
      (parts_units S.wunits old + parts_units S.wunits new + 1) *
      N.of_nat (S.wsize p) <= budget)%N).
    { clear -budget; unfold budget, route_measure;
      repeat rewrite Nat2N.inj_add; repeat rewrite Nat2N.inj_mul; nia. }
    assert (Hcollapse_bound : (T_collapse_with S.bot S.join S.T_join xs +
      N.of_nat (S.size (collapse_with S.bot S.join xs)) + 1 <=
      2 * route_scale * budget)%N).
    { eapply N.le_trans; [exact Hcollapse|].
      assert (Hinput : (N.of_nat (states_size xs + 1) <= 2 * budget)%N).
      { clear -Hsize Hmass; apply time_of_nat_le in Hsize;
        rewrite Nat2N.inj_mul in Hsize; nia. }
      eapply N.le_trans; [apply N.mul_le_mono_l; exact Hinput|].
      clear -budget; unfold route_scale; nia. }
    assert (Hunits_bound : (N.of_nat (S.wunits (collapse_with S.bot S.join xs)) <=
      2 * route_scale * N.of_nat
        (parts_units S.wunits old + parts_units S.wunits new + 1))%N).
    { eapply N.le_trans; [exact Hcollapse_units|].
      eapply N.le_trans; [apply N.mul_le_mono_l; apply time_of_nat_le; exact Hunits|].
      clear -old new; rewrite Nat2N.inj_mul; unfold route_scale; nia. }
    assert (Hunit_sum : (N.of_nat
      (S.wunits (snd r) + S.wunits (collapse_with S.bot S.join xs)) <=
      (2 * route_scale + 1) * N.of_nat
        (parts_units S.wunits old + parts_units S.wunits new + 1))%N).
    { clear -Hunits_bound Hrunits; repeat rewrite Nat2N.inj_add in *; nia. }
    pose proof (N.mul_le_mono_r _ _ (N.of_nat (S.wsize p)) Hunit_sum) as Hproduct.
    pose proof (N.mul_le_mono_l _ _ (2 * route_scale + 1)%N Hunit_budget) as Hpaid.
    assert (Hinput : (N.of_nat
      ((S.wunits (snd r) + S.wunits (collapse_with S.bot S.join xs)) * S.wsize p +
       (S.size (snd r) + S.size (collapse_with S.bot S.join xs) + S.wsize p + 1)) <=
      8 * route_scale * budget)%N).
    { clear -Hproduct Hpaid Hrsize Hcollapse_bound Hmass Hparam Hpositive;
      repeat rewrite Nat2N.inj_add in *; repeat rewrite Nat2N.inj_mul; nia. }
    pose proof (S.T_widen_le p (snd r) (collapse_with S.bot S.join xs)) as Hwiden.
    pose proof (N.mul_le_mono_l _ _ S.c_lat Hinput) as Hscaled.
    clear -Hcollapse_bound Hwiden Hscaled Hlat Hpositive.
    nia.
  Qed.

  (** The previous part's bottom test is charged to its size and the fixed bottom size. *)
  Local Lemma route_receiver_bottom_clock p old new r : In r old ->
    (S.T_leb (snd r) S.bot <= route_scale * route_scale *
      N.of_nat (route_measure p old new))%N.
  Proof.
    intro Hr; destruct (route_member_measures r old Hr) as [Hsize Hrest].
    destruct route_rates as [Hpositive [Hlat [Hkey [Hcap Hbot]]]].
    assert (Hinput : (N.of_nat (S.size (snd r) + S.size S.bot + 1) <=
      N.of_nat (S.size S.bot + 1) * N.of_nat (route_measure p old new))%N).
    { clear -Hsize; unfold route_measure; repeat rewrite Nat2N.inj_add;
      repeat rewrite Nat2N.inj_mul; nia. }
    eapply N.le_trans; [apply S.T_leb_le|].
    eapply N.le_trans; [apply N.mul_le_mono_l; exact Hinput|].
    rewrite N.mul_assoc; apply N.mul_le_mono_r, N.mul_le_mono; lia.
  Qed.

  (** A label comparison charges the stored label of its previous receiver. *)
  Local Lemma route_receiver_label_clock p old new r (q : option Tk.t * S.t) : In r old ->
    (T_label_eqb Tk.eqb Tk.T_eqb (fst r) (fst q) <=
      route_scale * N.of_nat (route_measure p old new))%N.
  Proof.
    intro Hr; destruct (route_member_measures r old Hr) as [Hsize [Hlabel Hunits]].
    destruct route_rates as [Hpositive [Hlat [Hkey Hrest]]].
    eapply N.le_trans; [apply label_clock|].
    apply N.mul_le_mono; [exact Hkey|].
    unfold route_measure; lia.
  Qed.

  Local Lemma route_app_clock {A} (xs ys : list A) :
    Datatypes.T_app xs ys = (N.of_nat (length xs) + 1)%N.
  Proof.
    induction xs as [|x xs IH]; time_unfold @Datatypes.T_app; cbn [length];
      rewrite ?IH, ?Nat2N.inj_succ; lia.
  Qed.

  (** One absorption step pays for routing, copying, collapse and component widening. *)
  Local Lemma route_absorb_step_clock p old new r fresh strays :
    In r old -> length fresh <= C.k -> length strays <= C.k ->
    parts_size Tk.bits S.size fresh <= parts_size Tk.bits S.size new ->
    parts_size Tk.bits S.size strays <= parts_size Tk.bits S.size new ->
    parts_units S.wunits fresh <= parts_units S.wunits new ->
    parts_units S.wunits strays <= parts_units S.wunits new ->
    let selected := filter (fun q => label_eqb Tk.eqb (fst r) (fst q)) fresh in
    let own := selected ++ strays in
    let xs := snd r :: map snd own in
    (S.T_leb (snd r) S.bot +
      List.T_filter (fun q => label_eqb Tk.eqb (fst r) (fst q))
        (fun q => 1 + (Datatypes.T_fst r + Datatypes.T_fst q +
          T_label_eqb Tk.eqb Tk.T_eqb (fst r) (fst q)))%N fresh +
      Datatypes.T_app selected strays +
      ListDef.T_map snd (fun q => Datatypes.T_snd q) own +
      T_collapse_with S.bot S.join S.T_join xs +
      S.T_widen p (snd r) (collapse_with S.bot S.join xs) + 6 <=
      24 * route_scale * route_scale * N.of_nat (route_measure p old new))%N.
  Proof.
    intros Hr Hfresh Hstrays Hsf Hss Huf Hus.
    pose proof (route_receiver_join_clock p old new r fresh strays
      Hr Hfresh Hstrays Hsf Hss Huf Hus) as Hjoin.
    pose proof (route_receiver_bottom_clock p old new r Hr) as Hbottom.
    cbv zeta in Hjoin |- *.
    set (selected := filter (fun q => label_eqb Tk.eqb (fst r) (fst q)) fresh) in *.
    set (own := selected ++ strays) in *.
    set (xs := snd r :: map snd own) in *.
    set (budget := N.of_nat (route_measure p old new)) in *.
    destruct route_rates as [Hpositive [Hlat [Hkey [Hcap Hbot]]]].
    assert (Hbudget : (1 <= budget)%N) by (unfold budget, route_measure; lia).
    assert (Hcalls : forall q, In q fresh ->
      (1 + (Datatypes.T_fst r + Datatypes.T_fst q +
        T_label_eqb Tk.eqb Tk.T_eqb (fst r) (fst q)) <= route_scale * budget + 3)%N).
    { intros q Hq; pose proof (route_receiver_label_clock p old new r q Hr) as Hlabel.
      time_simpl; fold budget in Hlabel; lia. }
    pose proof (route_filter_uniform (fun q => label_eqb Tk.eqb (fst r) (fst q))
      (fun q => 1 + (Datatypes.T_fst r + Datatypes.T_fst q +
        T_label_eqb Tk.eqb Tk.T_eqb (fst r) (fst q)))%N fresh
      (route_scale * budget + 3)%N Hcalls) as Hfilter.
    assert (Hfilter_bound : (List.T_filter
      (fun q => label_eqb Tk.eqb (fst r) (fst q))
      (fun q => 1 + (Datatypes.T_fst r + Datatypes.T_fst q +
        T_label_eqb Tk.eqb Tk.T_eqb (fst r) (fst q)))%N fresh <=
      4 * route_scale * route_scale * budget)%N).
    { clear -Hfilter Hfresh Hcap Hpositive Hbudget.
      assert (Hlen : (N.of_nat (length fresh) <= route_scale)%N) by lia.
      eapply N.le_trans; [exact Hfilter|].
      pose proof (N.mul_le_mono_r _ _ (route_scale * budget + 3 + 1)%N Hlen).
      nia. }
    assert (Hselected : length selected <= length fresh) by
      (unfold selected; apply filter_length_le).
    assert (Hown : length own <= 2 * C.k) by
      (unfold own; rewrite length_app; lia).
    assert (Happend : (Datatypes.T_app selected strays <= route_scale)%N).
    { rewrite route_app_clock; lia. }
    pose proof (map_snd_clock own) as Hmap.
    assert (Hmap_bound : (ListDef.T_map snd (fun q => Datatypes.T_snd q) own <=
      4 * route_scale)%N).
    { clear -Hmap Hown Hcap; lia. }
    clear -Hjoin Hbottom Hfilter_bound Happend Hmap_bound Hpositive Hbudget.
    nia.
  Qed.

  (** Absorption visits each previous part once and clears strays after its first receiver. *)
  Local Lemma route_absorb_clock p old new fresh strays :
    length old <= C.k -> length fresh <= C.k -> length strays <= C.k ->
    parts_size Tk.bits S.size fresh <= parts_size Tk.bits S.size new ->
    parts_size Tk.bits S.size strays <= parts_size Tk.bits S.size new ->
    parts_units S.wunits fresh <= parts_units S.wunits new ->
    parts_units S.wunits strays <= parts_units S.wunits new ->
    (T_absorb Tk.eqb Tk.T_eqb S.leb S.T_leb S.bot S.join S.T_join
      (S.widen p) (S.T_widen p) strays fresh old <=
      32 * route_scale * route_scale * route_scale * route_scale *
        N.of_nat (route_measure p old new))%N.
  Proof.
    intros Hold Hfresh Hstrays Hsf Hss Huf Hus.
    set (budget := N.of_nat (route_measure p old new)).
    assert (Hwalk : forall remaining, incl remaining old -> forall extras,
      length extras <= C.k ->
      parts_size Tk.bits S.size extras <= parts_size Tk.bits S.size new ->
      parts_units S.wunits extras <= parts_units S.wunits new ->
      (T_absorb Tk.eqb Tk.T_eqb S.leb S.T_leb S.bot S.join S.T_join
        (S.widen p) (S.T_widen p) extras fresh remaining <=
        24 * route_scale * route_scale * budget * N.of_nat (length remaining) + 1)%N).
    { induction remaining as [|r remaining IH]; intros Hincl extras Hextra Hse Hue.
      - time_unfold @T_absorb; cbn [length]; lia.
      - assert (Hr : In r old) by (apply Hincl; now left).
        assert (Hremaining : incl remaining old) by
          (intros q Hq; apply Hincl; now right).
        pose proof (route_absorb_step_clock p old new r fresh extras
          Hr Hfresh Hextra Hsf Hse Huf Hue) as Hstep.
        cbv zeta in Hstep; fold budget in Hstep.
        pose proof (IH Hremaining extras Hextra Hse Hue) as Hsame.
        assert (Hempty_size : parts_size Tk.bits S.size [] <=
          parts_size Tk.bits S.size new).
        { cbn [parts_size fold_right]; pose proof (parts_size_length new); lia. }
        pose proof (IH Hremaining [] ltac:(cbn; lia) Hempty_size
          ltac:(cbn [parts_units fold_right]; lia)) as Hcleared.
        revert Hstep; time_simpl; intro Hstep.
        time_unfold @T_absorb; time_simpl; cbn [length]; rewrite Nat2N.inj_succ.
        clear -Hstep Hsame Hcleared.
        destruct (S.leb (snd r) S.bot); cbv zeta; nia. }
    pose proof (Hwalk old (fun q Hq => Hq) strays Hstrays Hss Hus) as Htotal.
    destruct route_rates as [Hpositive [Hlat [Hkey [Hcap Hbot]]]].
    assert (Hbudget : (1 <= budget)%N) by (unfold budget, route_measure; lia).
    assert (Hlength : (N.of_nat (length old) <= route_scale)%N) by lia.
    pose proof (N.mul_le_mono_l _ _ (24 * route_scale * route_scale * budget)%N
      Hlength) as Hscaled.
    clear -Htotal Hscaled Hpositive Hbudget.
    nia.
  Qed.

  (** Finding fresh parts and then strays removes entries without increasing either mass. *)
  Local Lemma route_fresh_measures old new :
    length (fresh_parts S.leb S.bot old new) <= length new /\
    parts_size Tk.bits S.size (fresh_parts S.leb S.bot old new) <=
      parts_size Tk.bits S.size new /\
    parts_units S.wunits (fresh_parts S.leb S.bot old new) <=
      parts_units S.wunits new.
  Proof.
    set (nonbottom := filter (fun q => negb (S.leb (snd q) S.bot)) new).
    set (uncovered_part := fun (q : option Tk.t * S.t) => negb
      (existsb (fun r => S.leb (snd q) (snd r)) old)).
    destruct (route_filter_measures
      (fun q => negb (S.leb (snd q) S.bot)) new) as [Hs1 Hu1].
    destruct (route_filter_measures uncovered_part nonbottom) as [Hs2 Hu2].
    pose proof (filter_length_le (fun q => negb (S.leb (snd q) S.bot)) new) as Hl1.
    pose proof (filter_length_le uncovered_part nonbottom) as Hl2.
    unfold fresh_parts, uncovered; fold nonbottom; fold uncovered_part.
    fold nonbottom in Hs1, Hu1, Hl1; repeat split; lia.
  Qed.

  Local Lemma route_stray_measures old fresh :
    length (stray_parts Tk.eqb S.leb S.bot old fresh) <= length fresh /\
    parts_size Tk.bits S.size (stray_parts Tk.eqb S.leb S.bot old fresh) <=
      parts_size Tk.bits S.size fresh /\
    parts_units S.wunits (stray_parts Tk.eqb S.leb S.bot old fresh) <=
      parts_units S.wunits fresh.
  Proof.
    unfold stray_parts; split; [apply filter_length_le|apply route_filter_measures].
  Qed.

  Local Lemma route_length_bound {A} (xs : list A) : length xs <= C.k ->
    (N.of_nat (length xs) <= route_scale)%N.
  Proof.
    intro Hlen; apply time_of_nat_le in Hlen.
    destruct route_rates as [_ [_ [_ [Hcap _]]]]; lia.
  Qed.

  Local Lemma route_measure_mass p old new :
    (N.of_nat (parts_size Tk.bits S.size old + parts_size Tk.bits S.size new + 1) <=
      N.of_nat (route_measure p old new))%N.
  Proof.
    apply time_of_nat_le; unfold route_measure; lia.
  Qed.

  Local Lemma route_measure_positive p old new :
    (1 <= N.of_nat (route_measure p old new))%N.
  Proof.
    pose proof (route_measure_mass p old new); lia.
  Qed.

  Local Lemma route_part_mass p old new q : In q old \/ In q new ->
    (N.of_nat (S.size (snd q) + 1) <= N.of_nat (route_measure p old new) /\
      N.of_nat (label_bits Tk.bits (fst q) + 1) <=
        N.of_nat (route_measure p old new))%N.
  Proof.
    intro Hin; pose proof (route_measure_mass p old new) as Hmass.
    assert (Hq : S.size (snd q) + 1 <=
      parts_size Tk.bits S.size old + parts_size Tk.bits S.size new + 1 /\
      label_bits Tk.bits (fst q) + 1 <=
        parts_size Tk.bits S.size old + parts_size Tk.bits S.size new + 1).
    { destruct Hin as [Hin|Hin];
        destruct (route_member_measures q _ Hin) as [Hs [Hl Hu]]; split; lia. }
    destruct Hq as [Hs Hl]; apply time_of_nat_le in Hs; apply time_of_nat_le in Hl.
    split; lia.
  Qed.

  Local Lemma route_bot_clock p old new q : In q old \/ In q new ->
    (S.T_leb (snd q) S.bot <=
      route_scale * route_scale * N.of_nat (route_measure p old new))%N.
  Proof.
    intro Hin; destruct (route_part_mass p old new q Hin) as [Hsize _].
    destruct route_rates as [Hpositive [Hlat [_ [_ Hbot]]]].
    pose proof (route_measure_positive p old new) as Hbudget.
    pose proof (S.T_leb_le (snd q) S.bot) as Hclock.
    assert (Hinput : (N.of_nat (S.size (snd q) + S.size S.bot + 1) <=
      route_scale * N.of_nat (route_measure p old new))%N).
    { repeat rewrite Nat2N.inj_add in *; nia. }
    pose proof (N.mul_le_mono_l _ _ S.c_lat Hinput) as Hscaled.
    clear -Hclock Hscaled Hlat; nia.
  Qed.

  Local Lemma route_pair_clock p old new q r : In q new -> In r old ->
    (S.T_leb (snd q) (snd r) <=
      route_scale * N.of_nat (route_measure p old new))%N.
  Proof.
    intros Hq Hr.
    destruct (route_member_measures q new Hq) as [Hqsize _].
    destruct (route_member_measures r old Hr) as [Hrsize _].
    pose proof (route_measure_mass p old new) as Hmass.
    destruct route_rates as [_ [Hlat _]].
    pose proof (S.T_leb_le (snd q) (snd r)) as Hclock.
    assert (Hinput : (N.of_nat (S.size (snd q) + S.size (snd r) + 1) <=
      N.of_nat (route_measure p old new))%N).
    { eapply N.le_trans with (m := N.of_nat
        (parts_size Tk.bits S.size old + parts_size Tk.bits S.size new + 1));
        [apply time_of_nat_le; lia|exact Hmass]. }
    eapply N.le_trans; [exact Hclock|].
    apply N.mul_le_mono; [lia|exact Hinput].
  Qed.

  Local Lemma route_label_clock p old new q label : In q old \/ In q new ->
    (T_label_eqb Tk.eqb Tk.T_eqb (fst q) label <=
      route_scale * N.of_nat (route_measure p old new))%N.
  Proof.
    intro Hin; destruct (route_part_mass p old new q Hin) as [_ Hlabel].
    destruct route_rates as [_ [_ [Hkey _]]].
    eapply N.le_trans; [apply label_clock|].
    now apply N.mul_le_mono.
  Qed.

  Local Lemma route_filter_cap {A} (f : A -> bool) (T_f : A -> N) xs budget :
    length xs <= C.k -> (forall x, In x xs -> (T_f x <= budget)%N) ->
    (List.T_filter f T_f xs <= route_scale * (budget + 1) + 1)%N.
  Proof.
    intros Hlen Hbound.
    eapply N.le_trans; [apply route_filter_uniform; exact Hbound|].
    apply N.add_le_mono_r, N.mul_le_mono_r; now apply route_length_bound.
  Qed.

  Local Lemma route_exists_cap {A} (f : A -> bool) (T_f : A -> N) xs budget :
    length xs <= C.k -> (forall x, In x xs -> (T_f x <= budget)%N) ->
    (List.T_existsb f T_f xs <= route_scale * (budget + 2) + 1)%N.
  Proof.
    intros Hlen Hbound.
    eapply N.le_trans; [apply route_exists_uniform; exact Hbound|].
    apply N.add_le_mono_r, N.mul_le_mono_r; now apply route_length_bound.
  Qed.

  Local Lemma route_uncovered_uniform {A} (leb : A -> A -> bool)
      (T_leb : A -> A -> N) old new budget :
    (forall q, In q new -> forall r, In r old -> (T_leb q r <= budget)%N) ->
    (T_uncovered leb T_leb old new <=
      1 + (N.of_nat (length new) * (N.of_nat (length old) * (budget + 2) + 4) + 1))%N.
  Proof.
    intro Hbound; time_unfold @T_uncovered.
    replace (N.of_nat (length old) * (budget + 2) + 4)%N with
      ((N.of_nat (length old) * (budget + 2) + 3) + 1)%N by lia.
    apply N.add_le_mono_l, route_filter_uniform.
    intros q Hq; time_simpl.
    pose proof (route_exists_uniform (leb q) (fun r => T_leb q r)
      old budget (fun r Hr => Hbound q Hq r Hr)) as Hexists.
    nia.
  Qed.

  Local Lemma route_uncovered_cap {A} (leb : A -> A -> bool)
      (T_leb : A -> A -> N) old new budget :
    length old <= C.k -> length new <= C.k ->
    (forall q, In q new -> forall r, In r old -> (T_leb q r <= budget)%N) ->
    (T_uncovered leb T_leb old new <=
      route_scale * (route_scale * (budget + 2) + 4) + 2)%N.
  Proof.
    intros Hold Hnew Hbound.
    pose proof (route_uncovered_uniform leb T_leb old new budget Hbound) as Hclock.
    pose proof (route_length_bound old Hold) as Hno.
    pose proof (route_length_bound new Hnew) as Hnn.
    assert (Hproduct : (N.of_nat (length new) *
      (N.of_nat (length old) * (budget + 2) + 4) <=
      route_scale * (route_scale * (budget + 2) + 4))%N).
    { apply N.mul_le_mono; [exact Hnn|].
      apply N.add_le_mono_r, N.mul_le_mono_r; exact Hno. }
    lia.
  Qed.

  Local Lemma route_fresh_arithmetic m budget :
    (2 <= m)%N -> (1 <= budget)%N ->
    (1 + (m * ((m * m * budget + 3) + 1) + 1 +
      (m * (m * ((m * budget + 3) + 2) + 4) + 2)) <=
      8 * m * m * m * budget)%N.
  Proof.
    intros Hm Hbudget.
    pose proof (N.mul_le_mono _ _ _ _ Hm Hm) as Hsquare.
    pose proof (N.mul_le_mono_r _ _ (m * m)%N Hm) as Hcube_square.
    pose proof (N.mul_le_mono_l _ _ m Hsquare) as Hcube_linear.
    pose proof (N.mul_le_mono _ _ _ _ Hm Hsquare) as Hcube_positive.
    pose proof (N.mul_le_mono_l _ _ (m * m * m)%N Hbudget) as Hscaled.
    nia.
  Qed.

  Local Lemma route_stray_arithmetic m budget :
    (2 <= m)%N -> (1 <= budget)%N ->
    (1 + (m * ((m * ((m * m * budget + m * budget + 6) + 2) + 3) + 1) + 1) <=
      16 * m * m * m * m * budget)%N.
  Proof.
    intros Hm Hbudget; assert (Hmone : (1 <= m)%N) by lia.
    pose proof (N.mul_le_mono_l _ _ m Hmone) as Hsquare.
    pose proof (N.mul_le_mono_l _ _ (m * m)%N Hmone) as Hcube.
    pose proof (N.mul_le_mono_l _ _ (m * m * m)%N Hmone) as Hfourth.
    pose proof (N.mul_le_mono_l _ _ (m * m * m * m)%N Hbudget) as Htotal.
    pose proof (N.mul_le_mono_r _ _ budget Hfourth) as Hcube_scaled.
    nia.
  Qed.

  (** The two filters for fresh candidates fit a cubic rate in the cap reserve. *)
  Local Lemma route_fresh_clock p old new :
    length old <= C.k -> length new <= C.k ->
    (T_fresh_parts S.leb S.T_leb S.bot old new <=
      8 * route_scale * route_scale * route_scale *
        N.of_nat (route_measure p old new))%N.
  Proof.
    intros Hold Hnew.
    set (budget := N.of_nat (route_measure p old new)).
    set (live := filter (fun q => negb (S.leb (snd q) S.bot)) new).
    assert (Hlive_length : length live <= C.k).
    { unfold live; eapply Nat.le_trans; [apply filter_length_le|exact Hnew]. }
    assert (Hlive_member : forall q, In q live -> In q new).
    { intros q Hq; unfold live in Hq; now apply filter_In in Hq as [Hq _]. }
    assert (Hlive : (List.T_filter (fun q => negb (S.leb (snd q) S.bot))
      (fun q => 1 + (Datatypes.T_snd q + S.T_leb (snd q) S.bot +
        Datatypes.T_negb (S.leb (snd q) S.bot)))%N new <=
      route_scale * ((route_scale * route_scale * budget + 3) + 1) + 1)%N).
    { apply route_filter_cap; [exact Hnew|].
      intros q Hq; pose proof (route_bot_clock p old new q (or_intror Hq)) as Hbot.
      fold budget in Hbot; time_simpl; nia. }
    assert (Hfresh : (T_uncovered (fun q r => S.leb (snd q) (snd r))
      (fun q r => 1 + (Datatypes.T_snd q + Datatypes.T_snd r +
        S.T_leb (snd q) (snd r)))%N old live <=
      route_scale * (route_scale * ((route_scale * budget + 3) + 2) + 4) + 2)%N).
    { apply route_uncovered_cap; [exact Hold|exact Hlive_length|].
      intros q Hq r Hr.
      pose proof (route_pair_clock p old new q r (Hlive_member q Hq) Hr) as Hpair.
      fold budget in Hpair; time_simpl; nia. }
    pose proof (route_measure_positive p old new) as Hbudget; fold budget in Hbudget.
    destruct route_rates as [Hpositive _].
    time_unfold @T_fresh_parts; fold live; fold budget.
    pose proof (route_fresh_arithmetic route_scale budget Hpositive Hbudget) as Htotal.
    clear -Hlive Hfresh Htotal; lia.
  Qed.

  (** Label absence scans need only the old input's state and label measures. *)
  Local Lemma route_stray_clock p old new fresh :
    length old <= C.k -> length fresh <= C.k ->
    (T_stray_parts Tk.eqb Tk.T_eqb S.leb S.T_leb S.bot old fresh <=
      16 * route_scale * route_scale * route_scale * route_scale *
        N.of_nat (route_measure p old new))%N.
  Proof.
    intros Hold Hfresh.
    set (budget := N.of_nat (route_measure p old new)).
    time_unfold @T_stray_parts.
    eapply N.le_trans with (m := (1 +
      (route_scale * ((route_scale *
        ((route_scale * route_scale * budget + route_scale * budget + 6) + 2) + 3) + 1) + 1))%N).
    - apply N.add_le_mono_l, route_filter_cap; [exact Hfresh|].
      intros q Hq; time_simpl.
      match goal with
      | |- context [List.T_existsb ?f ?T_f old] =>
        assert (Hexists : (List.T_existsb f T_f old <=
          route_scale * ((route_scale * route_scale * budget +
            route_scale * budget + 6) + 2) + 1)%N)
      end.
      { apply route_exists_cap; [exact Hold|].
        intros r Hr.
        pose proof (route_bot_clock p old new r (or_introl Hr)) as Hbot.
        pose proof (route_label_clock p old new r (fst q) (or_introl Hr)) as Hlabel.
        fold budget in Hbot, Hlabel; time_simpl; nia. }
      nia.
    - pose proof (route_measure_positive p old new) as Hbudget; fold budget in Hbudget.
      destruct route_rates as [Hpositive _].
      fold budget; now apply route_stray_arithmetic.
  Qed.

  (** The join fold pays one clock tick for each list cell and for its final case. *)
  Local Lemma fold_clock_length xs : forall a,
    (N.of_nat (length xs + 1) <= List.T_fold_left S.join S.T_join xs a)%N.
  Proof.
    induction xs as [|x xs IH]; intro a; time_unfold @List.T_fold_left;
      cbn [length]; [lia|].
    specialize (IH (S.join a x)); repeat rewrite Nat2N.inj_add in *.
    rewrite Nat2N.inj_succ; lia.
  Qed.

  Local Lemma collapse_clock_length xs :
    (N.of_nat (length xs + 1) <= T_collapse_with S.bot S.join S.T_join xs)%N.
  Proof.
    destruct xs as [|x xs]; time_unfold @T_collapse_with; cbn [length]; [lia|].
    pose proof (fold_clock_length xs x).
    repeat rewrite Nat2N.inj_add in *; rewrite Nat2N.inj_succ; lia.
  Qed.

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

  (** Evaluation separates component evaluations from its actual value-join accumulator. *)
  Local Lemma eval_clock e a : T_eval e a =
    (fold_right N.add 0%N (map (fun q => S.T_eval e (snd q) + 2)%N (proj1_sig a)) +
      eval_joins e (proj1_sig a) + 3)%N.
  Proof.
    destruct a as [ps Hbound].
    pose proof (ValueJoins.fold_clock (fun q : option Tk.t * S.t => S.eval e (snd q))
      (fun q => (1 + S.T_eval e (snd q))%N) ps V.bot 0%N) as Hfold.
    rewrite N.add_0_r in Hfold.
    assert (Hrows : map (fun q => (1 + S.T_eval e (snd q) + 1)%N) ps =
      map (fun q => (S.T_eval e (snd q) + 2)%N) ps).
    { apply map_ext; intro q; lia. }
    rewrite Hrows in Hfold.
    time_unfold @T_eval; time_unfold @Specif.T_proj1_sig; time_simpl; cbn [proj1_sig].
    unfold eval_joins; rewrite Hfold; lia.
  Qed.

  Local Lemma evaluation_sizes e (ps : list (option Tk.t * S.t)) :
    fold_right Nat.add 0%nat (map (fun q => V.size (S.eval e (snd q)) + 1)%nat ps) <=
    fold_right Nat.add 0%nat
      (map (fun q => S.eval_work e (snd q) + V.size (S.eval e (snd q)) + 1)%nat ps).
  Proof.
    induction ps as [|q ps IH]; cbn [map fold_right]; lia.
  Qed.

  Lemma assign_def : forall x e a, proj1_sig (assign x e a) =
    map (fun q => (fst q, S.assign x e (snd q))) (proj1_sig a).
  Proof.
    intros x e [ps Hbound]; reflexivity.
  Qed.
  Lemma havoc_def : forall x a, proj1_sig (havoc x a) =
    map (fun q => (fst q, S.havoc x (snd q))) (proj1_sig a).
  Proof.
    intros x [ps Hbound]; reflexivity.
  Qed.
  Lemma assume_def : forall g es a, proj1_sig (assume g es a) =
    map (fun q => (fst q, S.assume g es (snd q))) (proj1_sig a).
  Proof.
    intros g es [ps Hbound]; reflexivity.
  Qed.
  Lemma eval_def : forall e a,
    eval e a = fold_left (fun v q => V.join v (S.eval e (snd q))) (proj1_sig a) V.bot.
  Proof.
    reflexivity.
  Qed.
  Lemma widen_def : forall p a b, proj1_sig (widen p a b) =
    if leb b a then proj1_sig a else
    if is_bot a then proj1_sig b else
    let old := proj1_sig a in
    let fresh := fresh_parts S.leb S.bot old (proj1_sig b) in
    absorb Tk.eqb S.leb S.bot S.join (S.widen p)
      (stray_parts Tk.eqb S.leb S.bot old fresh) fresh old.
  Proof.
    apply widen_raw.
  Qed.
  Lemma narrow_def : forall a b, narrow a b = a.
  Proof.
    reflexivity.
  Qed.
  Lemma merge_parts_length : forall ps qs,
    length (merge_parts Tk.eqb S.join ps qs) <= length ps + length qs.
  Proof.
    intros ps qs; unfold merge_parts; revert ps.
    induction qs as [|q qs IH]; intro ps; cbn [fold_left length]; [lia|].
    specialize (IH (insert_part Tk.eqb S.join q ps)).
    pose proof (insert_part_length Tk.eqb S.join q ps); lia.
  Qed.
  Lemma collapse_size_le : forall xs, length xs <= 2 * C.k + 1 ->
    (N.of_nat (S.size (collapse_with S.bot S.join xs)) <= k_partition * N.of_nat
      (fold_right Nat.add 0%nat (map S.size xs) + length xs + 1))%N.
  Proof.
    intros xs Hlength; pose proof (collapse_budget xs Hlength) as Hbound.
    rewrite states_size_sum in Hbound.
    assert (Hscale : (scale <= k_partition)%N) by (unfold k_partition; nia).
    eapply N.le_trans; [|apply N.mul_le_mono_r; exact Hscale]; lia.
  Qed.
  Lemma collapse_units_le : forall xs, length xs <= 2 * C.k + 1 ->
    (N.of_nat (S.wunits (collapse_with S.bot S.join xs)) <= k_partition * N.of_nat
      (fold_right Nat.add 0%nat (map S.wunits xs) + 1))%N.
  Proof.
    intros xs Hlength; eapply N.le_trans; [now apply collapse_units_budget|].
    apply N.mul_le_mono_r; unfold k_partition; nia.
  Qed.
  Lemma merge_parts_size_le : forall ps qs,
    length ps <= C.k -> length qs <= C.k ->
    (N.of_nat (parts_size Tk.bits S.size
      (merge_parts Tk.eqb S.join ps qs)) <= k_partition * N.of_nat
        (parts_size Tk.bits S.size ps + parts_size Tk.bits S.size qs + 1))%N.
  Proof.
    intros ps qs Hps Hqs; pose proof (merge_budget ps qs Hqs) as Hbound.
    assert (Hconstant : (scale <= k_partition)%N) by (unfold k_partition; nia).
    eapply N.le_trans; [|apply N.mul_le_mono_r; exact Hconstant]; lia.
  Qed.
  Lemma merge_parts_units_le : forall ps qs,
    length ps <= C.k -> length qs <= C.k ->
    (N.of_nat (parts_units S.wunits
      (merge_parts Tk.eqb S.join ps qs)) <= k_partition * N.of_nat
        (parts_units S.wunits ps + parts_units S.wunits qs + 1))%N.
  Proof.
    intros ps qs Hps Hqs; pose proof (merge_fold_units qs ps) as Hfold.
    pose proof (scale_power (length qs + 1) ltac:(lia)) as Hscale.
    assert (Hconstant : (scale <= k_partition)%N) by (unfold k_partition; nia).
    assert (Hcoefficient : (growth ^ N.of_nat (length qs + 1) <= k_partition)%N).
    { eapply N.le_trans; [exact Hscale | exact Hconstant]. }
    unfold merge_parts; eapply N.le_trans;
      [|apply N.mul_le_mono_r; exact Hcoefficient]; lia.
  Qed.
  Lemma fit_parts_size_le : forall ps, length ps <= 2 * C.k ->
    (N.of_nat (parts_size Tk.bits S.size
      (fit_parts S.bot S.join C.k ps)) <= k_partition * N.of_nat
        (parts_size Tk.bits S.size ps + 1))%N.
  Proof.
    intros ps Hlength; pose proof (fit_budget ps Hlength) as Hbound.
    assert (Hconstant : (scale + 16 <= k_partition)%N) by (unfold k_partition; nia).
    eapply N.le_trans; [|apply N.mul_le_mono_r; exact Hconstant]; lia.
  Qed.
  Lemma fit_parts_units_le : forall (ps : list (option Tk.t * S.t)), length ps <= 2 * C.k ->
    (N.of_nat (parts_units S.wunits
      (fit_parts S.bot S.join C.k ps)) <= k_partition * N.of_nat
        (parts_units S.wunits ps + 1))%N.
  Proof.
    intros ps Hlength; unfold fit_parts; destruct C.k as [|n] eqn:Hcap.
    - cbn [parts_units fold_right]; lia.
    - destruct (Nat.leb (length ps) (Datatypes.S n)).
      + pose proof k_partition_min; rewrite Nat2N.inj_add; nia.
      + pose proof (fit_tail_units n ps ltac:(rewrite Hcap; exact Hlength)) as Hbound.
        assert (Hconstant : (scale <= k_partition)%N) by (unfold k_partition; nia).
        eapply N.le_trans; [exact Hbound | now apply N.mul_le_mono_r].
  Qed.
  Lemma T_leb_split : forall a b,
    (T_leb a b <= k_partition *
      (fold_right N.add 0%N (map (fun q => S.T_leb (snd q) S.bot +
        fold_right N.add 0%N (map (fun r => S.T_leb (snd q) (snd r) + 1) (proj1_sig b)) + 1)
        (proj1_sig a)) + 1))%N.
  Proof.
    intros a b; pose proof (leb_clock_work a b); pose proof k_partition_min.
    unfold comparison_work in *; nia.
  Qed.
  Lemma T_is_bot_split : forall a,
    (T_is_bot a <= k_partition *
      (fold_right N.add 0%N (map (fun q => S.T_leb (snd q) S.bot + 1) (proj1_sig a)) + 1))%N.
  Proof.
    intro a; pose proof (is_bot_clock_work a); pose proof k_partition_min.
    unfold comparison_work in *; cbn [map fold_right] in *.
    assert (Heq : map (fun q => (S.T_leb (snd q) S.bot + 0 + 1)%N) (proj1_sig a) =
      map (fun q => (S.T_leb (snd q) S.bot + 1)%N) (proj1_sig a)).
    { apply map_ext; intro q; now rewrite N.add_0_r. }
    rewrite Heq in H; nia.
  Qed.
  Lemma T_join_split : forall a b,
    (T_join a b <= k_partition *
      (T_merge_parts Tk.eqb Tk.T_eqb S.join S.T_join (proj1_sig a) (proj1_sig b) +
       T_fit_parts S.bot S.join S.T_join C.k
         (merge_parts Tk.eqb S.join (proj1_sig a) (proj1_sig b)) + 1))%N.
  Proof.
    intros [ps Hps] [qs Hqs]; pose proof k_partition_min.
    time_unfold @T_join; time_unfold @T_fit; time_simpl; cbn [proj1_sig].
    change (fun x y => Tk.T_eqb x y) with Tk.T_eqb.
    change (fun x y => S.T_join x y) with S.T_join.
    nia.
  Qed.
  Lemma T_merge_parts_le : forall ps qs, length ps <= C.k -> length qs <= C.k ->
    (T_merge_parts Tk.eqb Tk.T_eqb S.join S.T_join ps qs <= k_partition *
      N.of_nat (parts_size Tk.bits S.size ps + parts_size Tk.bits S.size qs + 1))%N.
  Proof.
    intros ps qs Hps Hqs; pose proof (merge_budget ps qs Hqs) as Hbound.
    assert (Hconstant : (scale <= k_partition)%N) by (unfold k_partition; nia).
    eapply N.le_trans; [|apply N.mul_le_mono_r; exact Hconstant]; lia.
  Qed.
  Lemma T_fit_parts_le : forall ps, length ps <= 2 * C.k ->
    (T_fit_parts S.bot S.join S.T_join C.k ps <= k_partition *
      N.of_nat (parts_size Tk.bits S.size ps + 1))%N.
  Proof.
    intros ps Hlength; pose proof (fit_budget ps Hlength) as Hbound.
    assert (Hconstant : (scale + 16 <= k_partition)%N) by (unfold k_partition; nia).
    eapply N.le_trans; [|apply N.mul_le_mono_r; exact Hconstant]; lia.
  Qed.
  Lemma T_widen_split : forall p a b,
    (T_widen p a b <= k_partition *
      (T_leb b a + T_is_bot a + route_time p (proj1_sig a) (proj1_sig b) + 1))%N.
  Proof.
    intros p [old Hbound] [new Hnew]; pose proof k_partition_min.
    unfold route_time; time_unfold @T_widen; time_simpl; cbn [proj1_sig].
    change (fun x y => Tk.T_eqb x y) with Tk.T_eqb.
    change (fun x y => S.T_leb x y) with S.T_leb.
    change (fun x y => S.T_join x y) with S.T_join.
    change (fun x y => S.T_widen p x y) with (S.T_widen p).
    destruct (leb (exist _ new Hnew) (exist _ old Hbound)); [nia|].
    destruct (is_bot (exist _ old Hbound)); nia.
  Qed.
  Lemma route_time_le : forall p old new,
    length old <= C.k -> length new <= C.k ->
    (route_time p old new <= k_partition * N.of_nat
      ((parts_units S.wunits old + parts_units S.wunits new + 1) * S.wsize p +
       (parts_size Tk.bits S.size old + parts_size Tk.bits S.size new + S.wsize p + 1)))%N.
  Proof.
    intros p old new Hold Hnew.
    change (route_time p old new <= k_partition * N.of_nat (route_measure p old new))%N.
    pose proof (route_fresh_clock p old new Hold Hnew) as Hfresh_clock.
    destruct (route_fresh_measures old new) as [Hfresh_length [Hfresh_size Hfresh_units]].
    set (fresh := fresh_parts S.leb S.bot old new) in *.
    assert (Hfresh_cap : length fresh <= C.k) by lia.
    pose proof (route_stray_clock p old new fresh Hold Hfresh_cap) as Hstray_clock.
    destruct (route_stray_measures old fresh) as [Hstray_length [Hstray_size Hstray_units]].
    set (strays := stray_parts Tk.eqb S.leb S.bot old fresh) in *.
    assert (Hstray_cap : length strays <= C.k) by lia.
    pose proof (route_absorb_clock p old new fresh strays Hold Hfresh_cap Hstray_cap
      Hfresh_size ltac:(lia) Hfresh_units ltac:(lia)) as Habsorb.
    destruct route_rates as [Hpositive _].
    unfold route_time; fold fresh; fold strays.
    change k_partition with
      (64 * route_scale * route_scale * route_scale * route_scale)%N.
    clear -Hfresh_clock Hstray_clock Habsorb Hpositive.
    nia.
  Qed.
  Lemma T_collapse_with_le : forall xs, length xs <= 2 * C.k + 1 ->
    (T_collapse_with S.bot S.join S.T_join xs <= k_partition * N.of_nat
      (fold_right Nat.add 0%nat (map S.size xs) + length xs + 1))%N.
  Proof.
    intros xs Hlength; pose proof (collapse_budget xs Hlength) as Hbound.
    rewrite states_size_sum in Hbound.
    assert (Hscale : (scale <= k_partition)%N) by (unfold k_partition; nia).
    eapply N.le_trans; [|apply N.mul_le_mono_r; exact Hscale]; lia.
  Qed.
  Lemma T_merge_split : forall k a,
    (T_merge k a <= k_partition *
      (T_collapse_with S.bot S.join S.T_join (map snd (proj1_sig a)) +
       T_inject k (collapse_with S.bot S.join (map snd (proj1_sig a))) + 1))%N.
  Proof.
    intros k [ps Hbound]; pose proof (map_snd_clock ps) as Hmap.
    pose proof (collapse_clock_length (map snd ps)) as Hlength.
    rewrite length_map, Nat2N.inj_add in Hlength.
    pose proof k_partition_min; time_unfold @T_merge; time_simpl; cbn [proj1_sig].
    change (fun x y => S.T_join x y) with S.T_join.
    revert Hmap; time_simpl; intro Hmap.
    nia.
  Qed.
  Lemma T_retag_split : forall k a,
    (T_retag k a <= k_partition * (T_merge k a + 1))%N.
  Proof.
    intros k a; pose proof k_partition_min; time_unfold @T_retag; nia.
  Qed.
  Lemma T_inject_plan_le : forall k s, (T_inject k s <= k_partition)%N.
  Proof.
    intros k s; pose proof k_partition_min.
    time_unfold @T_inject; time_unfold @T_fit; time_unfold @T_fit_parts.
    destruct C.k as [|n]; time_simpl; time_cbn.
    - lia.
    - time_unfold @Datatypes.T_length; time_unfold @Datatypes.T_length.
      time_unfold @Nat.T_leb; time_unfold @Nat.T_leb; time_simpl; time_cbn; lia.
  Qed.
  Lemma T_eval_split : forall e a,
    (T_eval e a <= k_partition *
      (fold_right N.add 0%N (map (fun q => S.T_eval e (snd q) + 1) (proj1_sig a)) +
       eval_joins e (proj1_sig a) + 1))%N.
  Proof.
    intros e a; pose proof (sum_shift (fun q => S.T_eval e (snd q)) 2%N
      (proj1_sig a) ltac:(lia)) as Hsum.
    cbv beta in Hsum.
    rewrite eval_clock; pose proof k_partition_min; nia.
  Qed.
  Lemma eval_joins_le : forall e ps, length ps <= C.k ->
    (eval_joins e ps <= k_partition * N.of_nat (fold_right Nat.add 0%nat
      (map (fun q => (V.size (S.eval e (snd q)) + 1)%nat) ps) + 1))%N.
  Proof.
    intros e ps Hlength; unfold eval_joins.
    eapply N.le_trans; [apply ValueJoins.joins_capped; exact Hlength|].
    apply N.mul_le_mono_r; exact value_coefficient.
  Qed.
  Lemma T_assign_split : forall x e a,
    (T_assign x e a <= k_partition *
      (fold_right N.add 0%N
        (map (fun q => S.T_assign x e (snd q) + 1) (proj1_sig a)) + 1))%N.
  Proof.
    intros x e a; pose proof (map_bounded_clock (S.assign x e) (fun s => S.T_assign x e s) a).
    pose proof k_partition_min; time_unfold @T_assign; nia.
  Qed.
  Lemma T_havoc_split : forall x a,
    (T_havoc x a <= k_partition *
      (fold_right N.add 0%N (map (fun q => S.T_havoc x (snd q) + 1) (proj1_sig a)) + 1))%N.
  Proof.
    intros x a; pose proof (map_bounded_clock (S.havoc x) (fun s => S.T_havoc x s) a).
    pose proof k_partition_min; time_unfold @T_havoc; nia.
  Qed.
  Lemma T_assume_split : forall g es a,
    (T_assume g es a <= k_partition *
      (fold_right N.add 0%N
        (map (fun q => S.T_assume g es (snd q) + 1) (proj1_sig a)) + 1))%N.
  Proof.
    intros g es a; pose proof (map_bounded_clock (S.assume g es) (fun s => S.T_assume g es s) a).
    pose proof k_partition_min; time_unfold @T_assume; nia.
  Qed.
  Lemma T_narrow_plan_le : forall a b, (T_narrow a b <= k_partition)%N.
  Proof.
    intros a b; pose proof k_partition_min; time_step.
  Qed.

  (** The intermediate label merge fits both the cap-restoration and size budgets. *)
  Local Lemma join_input_budget (a b : t) :
    length (merge_parts Tk.eqb S.join (proj1_sig a) (proj1_sig b)) <= 2 * C.k /\
    (N.of_nat (parts_size Tk.bits S.size
      (merge_parts Tk.eqb S.join (proj1_sig a) (proj1_sig b)) + 1) <=
      (k_partition + 1) * N.of_nat (size a + size b + 1))%N.
  Proof.
    pose proof (proj1 (Nat.leb_le _ _) (proj2_sig a)) as Ha.
    pose proof (proj1 (Nat.leb_le _ _) (proj2_sig b)) as Hb.
    pose proof (merge_parts_length (proj1_sig a) (proj1_sig b)) as Hlength.
    pose proof (merge_parts_size_le (proj1_sig a) (proj1_sig b) Ha Hb) as Hsize.
    split; [lia|]; unfold size; repeat rewrite Nat2N.inj_add in *; nia.
  Qed.

  (** Collapsing an actual partition is paid by its complete stored representation. *)
  Local Lemma collapse_parts_budget (a : t) :
    (T_collapse_with S.bot S.join S.T_join (map snd (proj1_sig a)) +
      N.of_nat (S.size (collapse_with S.bot S.join (map snd (proj1_sig a)))) + 1 <=
      k_partition * N.of_nat (size a))%N.
  Proof.
    pose proof (proj1 (Nat.leb_le _ _) (proj2_sig a)) as Ha.
    pose proof (collapse_budget (map snd (proj1_sig a))
      ltac:(rewrite length_map; lia)) as Hcollapse.
    eapply N.le_trans; [exact Hcollapse|]; apply N.mul_le_mono.
    - unfold k_partition; nia.
    - unfold size; apply time_of_nat_le, states_size_parts.
  Qed.

  (** The strict merge budget leaves one tick for the retagging wrapper. *)
  Local Lemma merge_clock_budget k a :
    (T_merge k a + 1 <= (k_partition + 1) * (k_partition + 1) *
      N.of_nat (Tk.bits k + size a + 1))%N.
  Proof.
    pose proof (T_merge_split k a) as Hclock.
    pose proof (T_inject_plan_le k
      (collapse_with S.bot S.join (map snd (proj1_sig a)))) as Hinject.
    pose proof (collapse_parts_budget a) as Hcollapse.
    set (mass := N.of_nat (Tk.bits k + size a + 1)) in *.
    assert (Hmass : (1 <= mass)%N) by (unfold mass; lia).
    assert (Hinput : (N.of_nat (size a) + 1 <= mass)%N) by
      (unfold mass; repeat rewrite Nat2N.inj_add; lia).
    pose proof (N.mul_le_mono_l _ _ k_partition Hinput) as Hinput_paid.
    assert (Hinner : (T_collapse_with S.bot S.join S.T_join (map snd (proj1_sig a)) +
      T_inject k (collapse_with S.bot S.join (map snd (proj1_sig a))) + 1 <=
      (k_partition + 1) * mass)%N) by nia.
    pose proof (N.mul_le_mono_l _ _ k_partition Hinner) as Hscaled.
    nia.
  Qed.

  (** Public contracts compose the bounded plan steps above. *)

  Lemma c_lat_pos : (1 <= c_lat)%N.
  Proof.
    unfold c_lat; nia.
  Qed.
  Lemma T_leb_le : forall a b,
    (T_leb a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b; eapply N.le_trans; [apply leb_budget|].
    apply N.mul_le_mono_r; unfold c_lat; nia.
  Qed.
  Lemma T_join_le : forall a b,
    (T_join a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b; destruct (join_input_budget a b) as [Hlength Hinput].
    pose proof (proj1 (Nat.leb_le _ _) (proj2_sig a)) as Ha.
    pose proof (proj1 (Nat.leb_le _ _) (proj2_sig b)) as Hb.
    pose proof (T_join_split a b) as Hclock.
    pose proof (T_merge_parts_le (proj1_sig a) (proj1_sig b) Ha Hb) as Hmerge.
    pose proof (T_fit_parts_le
      (merge_parts Tk.eqb S.join (proj1_sig a) (proj1_sig b)) Hlength) as Hfit.
    fold (size a) (size b) in Hmerge.
    set (mass := N.of_nat (size a + size b + 1)) in *.
    assert (Hmass : (1 <= mass)%N) by (unfold mass; lia).
    assert (Hfitted : (T_fit_parts S.bot S.join S.T_join C.k
      (merge_parts Tk.eqb S.join (proj1_sig a) (proj1_sig b)) <=
      k_partition * ((k_partition + 1) * mass))%N).
    { eapply N.le_trans; [exact Hfit|]; now apply N.mul_le_mono_l. }
    assert (Hinner : (T_merge_parts Tk.eqb Tk.T_eqb S.join S.T_join
      (proj1_sig a) (proj1_sig b) + T_fit_parts S.bot S.join S.T_join C.k
        (merge_parts Tk.eqb S.join (proj1_sig a) (proj1_sig b)) + 1 <=
      (k_partition + 1) * (k_partition + 1) * mass)%N) by nia.
    eapply N.le_trans; [exact Hclock|].
    eapply N.le_trans; [apply N.mul_le_mono_l; exact Hinner|].
    rewrite N.mul_assoc; apply N.mul_le_mono_r; unfold c_lat; nia.
  Qed.
  Lemma T_is_bot_le : forall a,
    (T_is_bot a <= c_lat * N.of_nat (size a + 1))%N.
  Proof.
    intro a; eapply N.le_trans; [apply is_bot_budget|].
    apply N.mul_le_mono_r; unfold c_lat; nia.
  Qed.
  Lemma T_widen_le : forall p a b,
    (T_widen p a b <= c_lat * N.of_nat
      ((wunits a + wunits b) * wsize p + (size a + size b + wsize p + 1)))%N.
  Proof.
    intros p a b; pose proof (T_widen_split p a b) as Hclock.
    pose proof (leb_budget b a) as Hcompare; pose proof (is_bot_budget a) as Hbottom.
    pose proof (route_time_le p (proj1_sig a) (proj1_sig b)
      (proj1 (Nat.leb_le _ _) (proj2_sig a))
      (proj1 (Nat.leb_le _ _) (proj2_sig b))) as Hroute.
    set (mass := N.of_nat ((wunits a + wunits b) * wsize p +
      (size a + size b + wsize p + 1))) in *.
    assert (Hmass : (1 <= mass)%N) by (unfold mass; lia).
    assert (Hcomp_input : (N.of_nat (size b + size a + 1) <= mass)%N).
    { unfold mass; apply time_of_nat_le; lia. }
    assert (Hbottom_input : (N.of_nat (size a + 1) <= mass)%N).
    { unfold mass; apply time_of_nat_le; lia. }
    assert (Hroute_input : (N.of_nat (route_measure p (proj1_sig a) (proj1_sig b)) <=
      2 * mass)%N).
    { assert (Hnat : route_measure p (proj1_sig a) (proj1_sig b) <=
        2 * ((wunits a + wunits b) * wsize p + (size a + size b + wsize p + 1))).
      { unfold route_measure, wunits, wsize, size; nia. }
      apply time_of_nat_le in Hnat; rewrite Nat2N.inj_mul in Hnat; exact Hnat. }
    assert (Hcomp : (T_leb b a <= k_partition * mass)%N).
    { eapply N.le_trans; [exact Hcompare|]; now apply N.mul_le_mono_l. }
    assert (Hbot : (T_is_bot a <= k_partition * mass)%N).
    { eapply N.le_trans; [exact Hbottom|]; now apply N.mul_le_mono_l. }
    assert (Hrouted : (route_time p (proj1_sig a) (proj1_sig b) <=
      k_partition * (2 * mass))%N).
    { eapply N.le_trans; [exact Hroute|].
      apply N.mul_le_mono_l; exact Hroute_input. }
    assert (Hinner : (T_leb b a + T_is_bot a +
      route_time p (proj1_sig a) (proj1_sig b) + 1 <= (4 * k_partition + 1) * mass)%N)
      by nia.
    eapply N.le_trans; [exact Hclock|].
    eapply N.le_trans; [apply N.mul_le_mono_l; exact Hinner|].
    rewrite N.mul_assoc; apply N.mul_le_mono_r; unfold c_lat; nia.
  Qed.
  Lemma T_narrow_le : forall a b,
    (T_narrow a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b; pose proof (T_narrow_plan_le a b); unfold c_lat.
    repeat rewrite Nat2N.inj_add; nia.
  Qed.
  Lemma T_assign_le : forall x e a,
    (T_assign x e a <= c_state * N.of_nat (assign_work x e a + 1))%N.
  Proof.
    intros x e a; pose proof (map_transfer_clock (S.assign x e) (fun s => S.T_assign x e s)
      (S.assign_work x e) S.c_state a (S.T_assign_le x e)) as Hmap.
    time_unfold @T_assign; unfold assign_work, c_state; pose proof k_partition_min; nia.
  Qed.
  Lemma T_havoc_le : forall x a,
    (T_havoc x a <= c_state * N.of_nat (havoc_work x a + 1))%N.
  Proof.
    intros x a; pose proof (map_transfer_clock (S.havoc x) (fun s => S.T_havoc x s)
      (S.havoc_work x) S.c_state a (S.T_havoc_le x)) as Hmap.
    time_unfold @T_havoc; unfold havoc_work, c_state; pose proof k_partition_min; nia.
  Qed.
  Lemma T_assume_le : forall g es a,
    (T_assume g es a <= c_state * N.of_nat (assume_work g es a + 1))%N.
  Proof.
    intros g es a; pose proof (map_transfer_clock (S.assume g es) (fun s => S.T_assume g es s)
      (S.assume_work g es) S.c_state a (S.T_assume_le g es)) as Hmap.
    time_unfold @T_assume; unfold assume_work, c_state; pose proof k_partition_min; nia.
  Qed.
  Lemma T_eval_le : forall e a,
    (T_eval e a <= c_state * N.of_nat (eval_work e a + 1))%N.
  Proof.
    intros e [ps Hbound]; assert (Hcap : length ps <= C.k) by now apply Nat.leb_le.
    pose proof (ValueJoins.sum_cost (fun q => (S.T_eval e (snd q) + 2)%N)
      (fun q => S.eval_work e (snd q) + V.size (S.eval e (snd q)) + 1)%nat
      (S.c_state + 2)%N ps) as Hsum.
    assert (Hcalls : forall q, In q ps -> (S.T_eval e (snd q) + 2 <=
      (S.c_state + 2) * N.of_nat
        (S.eval_work e (snd q) + V.size (S.eval e (snd q)) + 1))%N).
    { intros q Hq; pose proof (S.T_eval_le e (snd q)).
      repeat rewrite Nat2N.inj_add in *; nia. }
    specialize (Hsum Hcalls); cbv beta in Hsum.
    pose proof (eval_joins_le e ps Hcap) as Hjoins.
    pose proof (evaluation_sizes e ps) as Hvalues; apply time_of_nat_le in Hvalues.
    rewrite eval_clock; unfold eval_work; cbn [proj1_sig].
    set (work := fold_right Nat.add 0%nat
      (map (fun q => S.eval_work e (snd q) + V.size (S.eval e (snd q)) + 1)%nat ps)) in *.
    assert (Hjoined : (eval_joins e ps <= k_partition * N.of_nat (work + 1))%N).
    { eapply N.le_trans; [exact Hjoins|].
      apply N.mul_le_mono_l; repeat rewrite Nat2N.inj_add; lia. }
    assert (Hall : (fold_right N.add 0%N
      (map (fun q => (S.T_eval e (snd q) + 2)%N) ps) + eval_joins e ps + 3 <=
      (S.c_state + k_partition + 5) * N.of_nat (work + 1))%N).
    { repeat rewrite Nat2N.inj_add in *; nia. }
    eapply N.le_trans; [exact Hall|]; apply N.mul_le_mono_r.
    unfold c_state; pose proof k_partition_min; nia.
  Qed.
  Lemma size_parts : forall a, size a = parts_size Tk.bits S.size (proj1_sig a).
  Proof.
    reflexivity.
  Qed.
  Lemma wunits_parts : forall a, wunits a = parts_units S.wunits (proj1_sig a).
  Proof.
    reflexivity.
  Qed.
  Lemma wsize_component : forall p, wsize p = S.wsize p.
  Proof.
    reflexivity.
  Qed.
  Lemma assign_work_parts : forall x e a, assign_work x e a =
    fold_right Nat.add 0%nat (map (fun q => S.assign_work x e (snd q) + 1) (proj1_sig a)).
  Proof.
    reflexivity.
  Qed.
  Lemma havoc_work_parts : forall x a, havoc_work x a =
    fold_right Nat.add 0%nat (map (fun q => S.havoc_work x (snd q) + 1) (proj1_sig a)).
  Proof.
    reflexivity.
  Qed.
  Lemma assume_work_parts : forall g es a, assume_work g es a =
    fold_right Nat.add 0%nat
      (map (fun q => S.assume_work g es (snd q) + 1) (proj1_sig a)).
  Proof.
    reflexivity.
  Qed.
  Lemma eval_work_parts : forall e a, eval_work e a = fold_right Nat.add 0%nat (map (fun q =>
    S.eval_work e (snd q) + V.size (S.eval e (snd q)) + 1) (proj1_sig a)).
  Proof.
    reflexivity.
  Qed.
  Lemma T_inject_le : forall k s,
    (T_inject k s <= c_partition * N.of_nat (Tk.bits k + S.size s + 1))%N.
  Proof.
    intros k s; pose proof (T_inject_plan_le k s); unfold c_partition.
    repeat rewrite Nat2N.inj_add; nia.
  Qed.
  Lemma T_merge_le : forall k a,
    (T_merge k a <= c_partition * N.of_nat (Tk.bits k + size a + 1))%N.
  Proof.
    intros k a; pose proof (merge_clock_budget k a) as Hclock.
    assert (Hcoefficient : ((k_partition + 1) * (k_partition + 1) <= c_partition)%N)
      by (unfold c_partition; nia).
    eapply N.le_trans; [|apply N.mul_le_mono_r; exact Hcoefficient]; lia.
  Qed.
  Lemma T_retag_le : forall k a,
    (T_retag k a <= c_partition * N.of_nat (Tk.bits k + size a + 1))%N.
  Proof.
    intros k a; pose proof (merge_clock_budget k a) as Hclock.
    assert (Hcoefficient : ((k_partition + 1) * (k_partition + 1) <= c_partition)%N)
      by (unfold c_partition; nia).
    time_unfold @T_retag.
    eapply N.le_trans; [|apply N.mul_le_mono_r; exact Hcoefficient]; lia.
  Qed.
  Lemma join_size : forall a b,
    (N.of_nat (size (join a b)) <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b; destruct (join_input_budget a b) as [Hlength Hinput].
    pose proof (fit_parts_size_le
      (merge_parts Tk.eqb S.join (proj1_sig a) (proj1_sig b)) Hlength) as Hfit.
    unfold size at 1; rewrite join_parts.
    eapply N.le_trans; [exact Hfit|].
    eapply N.le_trans; [apply N.mul_le_mono_l; exact Hinput|].
    rewrite N.mul_assoc; apply N.mul_le_mono_r; unfold c_lat; nia.
  Qed.
  Lemma join_wunits : forall a b,
    (N.of_nat (wunits (join a b)) <= c_lat * N.of_nat (wunits a + wunits b + 1))%N.
  Proof.
    intros a b; destruct (join_input_budget a b) as [Hlength _].
    pose proof (proj1 (Nat.leb_le _ _) (proj2_sig a)) as Ha.
    pose proof (proj1 (Nat.leb_le _ _) (proj2_sig b)) as Hb.
    pose proof (merge_parts_units_le (proj1_sig a) (proj1_sig b) Ha Hb) as Hunits.
    pose proof (fit_parts_units_le
      (merge_parts Tk.eqb S.join (proj1_sig a) (proj1_sig b)) Hlength) as Hfit.
    fold (wunits a) (wunits b) in Hunits.
    assert (Hinput : (N.of_nat (parts_units S.wunits
      (merge_parts Tk.eqb S.join (proj1_sig a) (proj1_sig b)) + 1) <=
      (k_partition + 1) * N.of_nat (wunits a + wunits b + 1))%N).
    { repeat rewrite Nat2N.inj_add in *; nia. }
    unfold wunits at 1; rewrite join_parts.
    eapply N.le_trans; [exact Hfit|].
    eapply N.le_trans; [apply N.mul_le_mono_l; exact Hinput|].
    rewrite N.mul_assoc; apply N.mul_le_mono_r; unfold c_lat; nia.
  Qed.
  Lemma merge_size : forall k a,
    (N.of_nat (size (merge k a)) <= c_partition * N.of_nat (Tk.bits k + size a + 1))%N.
  Proof.
    intros k a; pose proof (collapse_parts_budget a) as Hcollapse.
    assert (Hcoefficient : (k_partition + 1 <= c_partition)%N) by
      (unfold c_partition; nia).
    unfold size at 1; rewrite merge_eq, inject_raw.
    cbn [parts_size fold_right label_bits fst snd].
    eapply N.le_trans; [|apply N.mul_le_mono_r; exact Hcoefficient].
    repeat rewrite Nat2N.inj_add in *; nia.
  Qed.

  (** Inclusion is linear in both partition sizes for the fixed cap. *)
  Lemma leb_complexity : bigO (X := t * t) (fun _ => True)
    (fun ab => N.of_nat (size (fst ab) + size (snd ab)))
    (fun ab => T_leb (fst ab) (snd ab)).
  Proof.
    exists c_lat; intros [a b] _.
    pose proof (T_leb_le a b) as Hbound.
    rewrite Nat2N.inj_add in Hbound; exact Hbound.
  Qed.

  (** Joining is linear in both partition sizes for the fixed cap. *)
  Lemma join_complexity : bigO (X := t * t) (fun _ => True)
    (fun ab => N.of_nat (size (fst ab) + size (snd ab)))
    (fun ab => T_join (fst ab) (snd ab)).
  Proof.
    exists c_lat; intros [a b] _.
    pose proof (T_join_le a b) as Hbound.
    rewrite Nat2N.inj_add in Hbound; exact Hbound.
  Qed.

  (** Widening pays for the state sizes and the units times the parameter size. *)
  Lemma widen_complexity : bigO (X := wparam * t * t) (fun _ => True)
    (fun '(p, a, b) => N.of_nat ((wunits a + wunits b) * wsize p + (size a + size b + wsize p)))
    (fun '(p, a, b) => T_widen p a b).
  Proof.
    exists c_lat; intros [[p a] b] _.
    pose proof (T_widen_le p a b) as Hbound.
    repeat rewrite Nat2N.inj_add in Hbound |- *; nia.
  Qed.

  (** Merging is linear in the token width and the partition size. *)
  Lemma merge_complexity : bigO (X := Tk.t * t) (fun _ => True)
    (fun ka => N.of_nat (Tk.bits (fst ka) + size (snd ka)))
    (fun ka => T_merge (fst ka) (snd ka)).
  Proof.
    exists c_partition; intros [k a] _.
    pose proof (T_merge_le k a) as Hbound.
    rewrite Nat2N.inj_add in Hbound; exact Hbound.
  Qed.

  (** The bottom test is linear in the partition size for the fixed cap. *)
  Lemma is_bot_complexity : bigO (fun _ : t => True) (fun a => N.of_nat (size a)) T_is_bot.
  Proof.
    exists c_lat; intros a _.
    pose proof (T_is_bot_le a) as Hbound.
    rewrite Nat2N.inj_add in Hbound; exact Hbound.
  Qed.

  (** Narrowing is linear in both partition sizes for the fixed cap. *)
  Lemma narrow_complexity : bigO (X := t * t) (fun _ => True)
    (fun ab => N.of_nat (size (fst ab) + size (snd ab)))
    (fun ab => T_narrow (fst ab) (snd ab)).
  Proof.
    exists c_lat; intros [a b] _.
    pose proof (T_narrow_le a b) as Hbound.
    rewrite Nat2N.inj_add in Hbound; exact Hbound.
  Qed.

  (** Assignment is linear in its component work measure. *)
  Lemma assign_complexity : bigO (X := X.t * term L.op X.t * t) (fun _ => True)
    (fun '(x, e, a) => N.of_nat (assign_work x e a)) (fun '(x, e, a) => T_assign x e a).
  Proof.
    exists c_state; intros [[x e] a] _.
    pose proof (T_assign_le x e a) as Hbound.
    rewrite Nat2N.inj_add in Hbound; exact Hbound.
  Qed.

  (** Havoc is linear in its component work measure. *)
  Lemma havoc_complexity : bigO (X := X.t * t) (fun _ => True)
    (fun '(x, a) => N.of_nat (havoc_work x a)) (fun '(x, a) => T_havoc x a).
  Proof.
    exists c_state; intros [x a] _.
    pose proof (T_havoc_le x a) as Hbound.
    rewrite Nat2N.inj_add in Hbound; exact Hbound.
  Qed.

  (** Assumption is linear in its component work measure. *)
  Lemma assume_complexity : bigO (X := L.guard * list (term L.op X.t) * t) (fun _ => True)
    (fun '(gd, es, a) => N.of_nat (assume_work gd es a)) (fun '(gd, es, a) => T_assume gd es a).
  Proof.
    exists c_state; intros [[g es] a] _.
    pose proof (T_assume_le g es a) as Hbound.
    rewrite Nat2N.inj_add in Hbound; exact Hbound.
  Qed.

  (** Evaluation is linear in its component work measure. *)
  Lemma eval_complexity : bigO (X := term L.op X.t * t) (fun _ => True)
    (fun '(e, a) => N.of_nat (eval_work e a)) (fun '(e, a) => T_eval e a).
  Proof.
    exists c_state; intros [e a] _.
    pose proof (T_eval_le e a) as Hbound.
    rewrite Nat2N.inj_add in Hbound; exact Hbound.
  Qed.

  (** Injection is linear in the token width and the component state size. *)
  Lemma inject_complexity : bigO (X := Tk.t * S.t) (fun _ => True)
    (fun ks => N.of_nat (Tk.bits (fst ks) + S.size (snd ks)))
    (fun ks => T_inject (fst ks) (snd ks)).
  Proof.
    exists c_partition; intros [k a] _.
    pose proof (T_inject_le k a) as Hbound.
    rewrite Nat2N.inj_add in Hbound; exact Hbound.
  Qed.

  (** Retagging is linear in the token width and the partition size. *)
  Lemma retag_complexity : bigO (X := Tk.t * t) (fun _ => True)
    (fun ka => N.of_nat (Tk.bits (fst ka) + size (snd ka)))
    (fun ka => T_retag (fst ka) (snd ka)).
  Proof.
    exists c_partition; intros [k a] _.
    pose proof (T_retag_le k a) as Hbound.
    rewrite Nat2N.inj_add in Hbound; exact Hbound.
  Qed.
End PartitionT.
