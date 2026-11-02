(** * Adequacy of legacy footprint overlap

    The observer preserves each comparison and accounts for every pair of footprints.
    For example, adjacent half-open intervals remain disjoint.
    Builds on: AnalysesAuditMemoryLegacyOverlap and positive equality adequacy. *)

From Stdlib Require Import List PArith ZArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsAuditPrimitive
  CollectionsAuditPrimitiveAdequacy.
From Galois.Domains Require Import DomainsFootprint.
From Galois.Analyses Require Import AnalysesMemoryLegacy AnalysesAuditMemoryLegacyOverlap.
Import List.ListNotations.

(** * Boolean agreement *)

(** A pair observer returns the source overlap test under matching site codes. *)
Lemma audit_legacy_overlap_pair_erases T C (enc : T -> positive * list C) (ET : encoding T)
    left right :
    (forall site, fst (enc site) = encode ET site) ->
    fst (audit_legacy_overlap_pair enc left right) =
      (Pos.eqb (encode ET (fp_site left)) (encode ET (fp_site right)) &&
        Z.ltb (fp_lo left) (fp_hi left) && Z.ltb (fp_lo right) (fp_hi right) &&
        Z.ltb (fp_lo left) (fp_hi right) && Z.ltb (fp_lo right) (fp_hi left))%bool.
Proof.
  intro Henc; unfold audit_legacy_overlap_pair.
  pose proof (audit_positive_eqb_erases (fst (enc (fp_site left))) (fst (enc (fp_site right))))
    as Heq.
  destruct (enc (fp_site left)) as [lc le] eqn:Hleft.
  destruct (enc (fp_site right)) as [rc re] eqn:Hright.
  destruct (audit_positive_eqb lc rc) as [same calls] eqn:Hcall.
  cbn in *.
  rewrite Hcall in Heq; cbn in Heq.
  specialize (Henc (fp_site left)) as Hlc; rewrite Hleft in Hlc; cbn in Hlc.
  specialize (Henc (fp_site right)) as Hrc; rewrite Hright in Hrc; cbn in Hrc.
  rewrite Heq, Hlc, Hrc; reflexivity.
Qed.

(** An inner scan returns the source existential test for a single left footprint. *)
Lemma audit_legacy_overlap_inner_erases T C (enc : T -> positive * list C) (ET : encoding T)
    left right :
    (forall site, fst (enc site) = encode ET site) ->
    fst (audit_legacy_overlap_inner enc left right) =
      existsb (fun item =>
        (Pos.eqb (encode ET (fp_site left)) (encode ET (fp_site item)) &&
          Z.ltb (fp_lo left) (fp_hi left) && Z.ltb (fp_lo item) (fp_hi item) &&
          Z.ltb (fp_lo left) (fp_hi item) && Z.ltb (fp_lo item) (fp_hi left))%bool) right.
Proof.
  intro Henc; induction right as [|item rest IH].
  - reflexivity.
  - cbn [audit_legacy_overlap_inner existsb].
    pose proof (audit_legacy_overlap_pair_erases T C enc ET left item Henc) as Hpair.
    destruct (audit_legacy_overlap_pair enc left item) as [head he].
    destruct (audit_legacy_overlap_inner enc left rest) as [tail te]; cbn in *.
    rewrite Hpair, IH; reflexivity.
Qed.

(** Matching site codes recover the original disjointness decision. *)
Theorem audit_legacy_disjoint_erases : audit_legacy_disjoint_erases_statement.
Proof.
  intros T C enc ET left right Henc.
  unfold audit_legacy_disjoint, legacy_disjoint_b.
  assert (Herase : fst (audit_legacy_overlap_exists enc left right) =
    existsb (fun item => existsb (fun other =>
      (Pos.eqb (encode ET (fp_site item)) (encode ET (fp_site other)) &&
        Z.ltb (fp_lo item) (fp_hi item) && Z.ltb (fp_lo other) (fp_hi other) &&
        Z.ltb (fp_lo item) (fp_hi other) && Z.ltb (fp_lo other) (fp_hi item))%bool) right) left).
  { induction left as [|item rest IH].
    - reflexivity.
    - cbn [audit_legacy_overlap_exists existsb].
      pose proof (audit_legacy_overlap_inner_erases T C enc ET item right Henc) as Hinner.
      destruct (audit_legacy_overlap_inner enc item right) as [head he].
      destruct (audit_legacy_overlap_exists enc rest right) as [tail te]; cbn in *.
      rewrite Hinner, IH; reflexivity. }
  destruct (audit_legacy_overlap_exists enc left right); cbn in *; rewrite Herase; reflexivity.
Qed.

(** * Pair counts and work *)

(** Pair counts distribute over consecutive trace segments. *)
Lemma audit_legacy_overlap_pairs_app T C (left right : list (audit_legacy_overlap_event T C)) :
    audit_legacy_overlap_pairs (left ++ right) =
      audit_legacy_overlap_pairs left + audit_legacy_overlap_pairs right.
Proof.
  induction left as [|event rest IH].
  - reflexivity.
  - destruct event; cbn; rewrite IH; lia.
Qed.

(** Every right-hand occurrence contributes one recorded pair. *)
Lemma audit_legacy_overlap_inner_count T C (enc : T -> positive * list C) left right :
    audit_legacy_overlap_pairs (snd (audit_legacy_overlap_inner enc left right)) = length right.
Proof.
  induction right as [|item rest IH].
  - reflexivity.
  - cbn [audit_legacy_overlap_inner].
    unfold audit_legacy_overlap_pair.
    destruct (enc (fp_site left)) as [lc le].
    destruct (enc (fp_site item)) as [rc re].
    destruct (audit_positive_eqb lc rc) as [same calls].
    destruct (audit_legacy_overlap_inner enc left rest) as [tail events]; cbn in *.
    lia.
Qed.

(** Each left/right occurrence contributes exactly one comparison event. *)
Theorem audit_legacy_overlap_pair_count : audit_legacy_overlap_pair_count_statement.
Proof.
  intros T C enc left right.
  assert (Hcount : audit_legacy_overlap_pairs (snd (audit_legacy_overlap_exists enc left right)) =
    length left * length right).
  { induction left as [|item rest IH].
    - reflexivity.
    - cbn [audit_legacy_overlap_exists].
      pose proof (audit_legacy_overlap_inner_count T C enc item right) as Hinner.
      destruct (audit_legacy_overlap_inner enc item right) as [head he].
      destruct (audit_legacy_overlap_exists enc rest right) as [tail te]; cbn in *.
      rewrite audit_legacy_overlap_pairs_app; cbn; lia. }
  unfold audit_legacy_disjoint.
  destruct (audit_legacy_overlap_exists enc left right); cbn in *; exact Hcount.
Qed.

(** Source-work folds distribute over consecutive trace segments. *)
Lemma audit_legacy_overlap_work_app T C work (left right : list (audit_legacy_overlap_event T C)) :
    audit_legacy_overlap_source_work work (left ++ right) =
      audit_legacy_overlap_source_work work left + audit_legacy_overlap_source_work work right.
Proof.
  induction left as [|event rest IH].
  - reflexivity.
  - destruct event; cbn; rewrite IH; lia.
Qed.

(** One inner scan is bounded by its original per-pair budget. *)
Lemma audit_legacy_overlap_inner_bound T C (enc : T -> positive * list C) work left right :
    audit_legacy_overlap_source_work work (snd (audit_legacy_overlap_inner enc left right)) <=
      audit_legacy_overlap_inner_budget enc work left right.
Proof.
  induction right as [|item rest IH].
  - reflexivity.
  - cbn [audit_legacy_overlap_inner audit_legacy_overlap_inner_budget].
    pose proof (audit_positive_eqb_source_bound (fst (enc (fp_site left)))
      (fst (enc (fp_site item)))) as Hcompare.
    unfold audit_legacy_overlap_pair.
    destruct (enc (fp_site left)) as [lc le].
    destruct (enc (fp_site item)) as [rc re].
    destruct (audit_positive_eqb lc rc) as [same calls] eqn:Hcall.
    destruct (audit_legacy_overlap_inner enc left rest) as [tail events]; cbn in *.
    rewrite Hcall in Hcompare; cbn in Hcompare.
    lia.
Qed.

(** All pair comparisons are bounded by their actual site and numeric charges. *)
Theorem audit_legacy_overlap_source_bound : audit_legacy_overlap_source_bound_statement.
Proof.
  intros T C enc work left right.
  assert (Hbound : audit_legacy_overlap_source_work work
      (snd (audit_legacy_overlap_exists enc left right)) <=
      audit_legacy_overlap_budget enc work left right).
  { induction left as [|item rest IH].
    - reflexivity.
    - cbn [audit_legacy_overlap_exists audit_legacy_overlap_budget].
      pose proof (audit_legacy_overlap_inner_bound T C enc work item right) as Hinner.
      destruct (audit_legacy_overlap_inner enc item right) as [head he].
      destruct (audit_legacy_overlap_exists enc rest right) as [tail te]; cbn in *.
      rewrite audit_legacy_overlap_work_app; cbn; lia. }
  unfold audit_legacy_disjoint.
  destruct (audit_legacy_overlap_exists enc left right); cbn in *; exact Hbound.
Qed.
