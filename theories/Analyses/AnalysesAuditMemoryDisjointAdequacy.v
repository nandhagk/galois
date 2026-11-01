(** * Adequacy of counted footprint disjointness

    The paired traversal preserves the boolean result and records each pair's source work.
    For example, a false first pair still leaves a record for each later pair.
    Builds on: AnalysesAuditMemoryDisjoint and CollectionsAuditPrimitiveAdequacy. *)

From Stdlib Require Import List PArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsAuditPrimitive
  CollectionsAuditPrimitiveAdequacy.
From Galois.Domains Require Import DomainsFootprint.
From Galois.Views Require Import ViewsMemoryEffects.
From Galois.Analyses Require Import AnalysesMemoryBase AnalysesMemoryWalk
  AnalysesAuditMemoryDisjoint.
Import List.ListNotations.
Open Scope bool_scope.

(** The paired observer returns the plain comparison for its two actual footprints. *)
Lemma audit_disjoint_pair_erases T CE (enc : T -> positive * list CE) ET left right :
  (forall site, fst (enc site) = encode ET site) ->
  fst (audit_disjoint_pair enc left right) =
    (negb (Pos.eqb (encode ET (fp_site left)) (encode ET (fp_site right))) ||
      BinInt.Z.leb (fp_hi left) (fp_lo right) || BinInt.Z.leb (fp_hi right) (fp_lo left))%bool.
Proof.
  intro Henc.
  unfold audit_disjoint_pair.
  pose proof (Henc (fp_site left)) as Hleft.
  pose proof (Henc (fp_site right)) as Hright.
  destruct (enc (fp_site left)) as [lc le].
  destruct (enc (fp_site right)) as [rc re].
  cbn in Hleft, Hright.
  pose proof (audit_positive_eqb_erases lc rc) as Heq.
  destruct (audit_positive_eqb lc rc) as [same events]; cbn in Heq |- *.
  rewrite Heq, Hleft, Hright; reflexivity.
Qed.

(** The inner traversal preserves every boolean operand in order. *)
Lemma audit_disjoint_inner_erases T CE (enc : T -> positive * list CE) ET item input :
  (forall site, fst (enc site) = encode ET site) ->
  fst (audit_disjoint_inner enc item input) =
    forallb (fun right =>
      negb (Pos.eqb (encode ET (fp_site item)) (encode ET (fp_site right))) ||
      BinInt.Z.leb (fp_hi item) (fp_lo right) || BinInt.Z.leb (fp_hi right) (fp_lo item)) input.
Proof.
  intro Henc; induction input as [|right rest IH].
  - reflexivity.
  - cbn [audit_disjoint_inner forallb].
    pose proof (audit_disjoint_pair_erases T CE enc ET item right Henc) as Hpair.
    destruct (audit_disjoint_pair enc item right) as [head he].
    destruct (audit_disjoint_inner enc item rest) as [tail te].
    cbn in Hpair, IH |- *; rewrite Hpair, IH; reflexivity.
Qed.

(** Matching site codes preserve the full pairwise disjointness result. *)
Theorem audit_footprints_disjoint_erases : audit_footprints_disjoint_erases_statement.
Proof.
  intros T CE enc ET left right Henc.
  unfold footprints_disjoint.
  induction left as [|item rest IH].
  - reflexivity.
  - cbn [audit_footprints_disjoint forallb].
    pose proof (audit_disjoint_inner_erases T CE enc ET item right Henc) as Hinner.
    destruct (audit_disjoint_inner enc item right) as [head he].
    destruct (audit_footprints_disjoint enc rest right) as [tail te].
    cbn in Hinner, IH |- *; rewrite Hinner, IH; reflexivity.
Qed.

(** Scope erasure includes the all-memory fallback. *)
Theorem audit_memory_scopes_disjoint_erases : audit_memory_scopes_disjoint_erases_statement.
Proof.
  intros T CE enc ET left right Henc.
  destruct left, right; cbn [audit_memory_scopes_disjoint memory_scopes_disjoint];
    try reflexivity.
  apply audit_footprints_disjoint_erases; exact Henc.
Qed.

(** Pair counts add over consecutive trace segments. *)
Lemma audit_disjoint_pairs_app T CE (left right : list (audit_disjoint_event T CE)) :
  audit_disjoint_pairs (left ++ right) = audit_disjoint_pairs left + audit_disjoint_pairs right.
Proof.
  induction left as [|event rest IH].
  - reflexivity.
  - destruct event; simpl; lia.
Qed.

(** The inner traversal records exactly one pair for each right footprint. *)
Lemma audit_disjoint_inner_pairs T CE (enc : T -> positive * list CE) item right :
  audit_disjoint_pairs (snd (audit_disjoint_inner enc item right)) = length right.
Proof.
  induction right as [|other rest IH].
  - reflexivity.
  - cbn [audit_disjoint_inner].
    unfold audit_disjoint_pair at 1.
    destruct (enc (fp_site item)) as [lc le].
    destruct (enc (fp_site other)) as [rc re].
    destruct (audit_positive_eqb lc rc) as [same eq_events] eqn:Heq.
    destruct (audit_disjoint_inner enc item rest) as [tail te].
    simpl in *; lia.
Qed.

(** Every pair of left and right occurrences appears exactly once. *)
Theorem audit_disjoint_pairs_count : audit_disjoint_pairs_count_statement.
Proof.
  intros T CE enc left right.
  induction left as [|item rest IH].
  - reflexivity.
  - cbn [audit_footprints_disjoint].
    pose proof (audit_disjoint_inner_pairs T CE enc item right) as Hinner.
    destruct (audit_disjoint_inner enc item right) as [head he].
    destruct (audit_footprints_disjoint enc rest right) as [tail te].
    cbn [snd] in Hinner, IH |- *.
    cbn [audit_disjoint_pairs].
    rewrite audit_disjoint_pairs_app; cbn [length]; lia.
Qed.

(** Source charges add over consecutive trace segments. *)
Lemma audit_disjoint_source_work_app T CE work (left right : list (audit_disjoint_event T CE)) :
  audit_disjoint_source_work work (left ++ right) =
    audit_disjoint_source_work work left + audit_disjoint_source_work work right.
Proof.
  induction left as [|event rest IH].
  - reflexivity.
  - destruct event; simpl; lia.
Qed.

(** The inner budget accounts for the exact comparison and both encoder traces. *)
Lemma audit_disjoint_inner_work T CE (enc : T -> positive * list CE) work item right :
  audit_disjoint_source_work work (snd (audit_disjoint_inner enc item right)) =
    audit_disjoint_inner_budget enc work item right.
Proof.
  induction right as [|other rest IH].
  - reflexivity.
  - cbn [audit_disjoint_inner audit_disjoint_inner_budget].
    unfold audit_disjoint_pair at 1.
    destruct (enc (fp_site item)) as [lc le].
    destruct (enc (fp_site other)) as [rc re].
    destruct (audit_positive_eqb lc rc) as [same eq_events] eqn:Heq.
    destruct (audit_disjoint_inner enc item rest) as [tail te].
    cbn [fst snd] in *; rewrite Heq; simpl in *; lia.
Qed.

(** The outer budget equals all selected frames and pair work. *)
Theorem audit_disjoint_source_work : audit_disjoint_source_work_statement.
Proof.
  intros T CE enc work left right.
  induction left as [|item rest IH].
  - reflexivity.
  - cbn [audit_footprints_disjoint audit_disjoint_budget].
    pose proof (audit_disjoint_inner_work T CE enc work item right) as Hinner.
    destruct (audit_disjoint_inner enc item right) as [head he].
    destruct (audit_footprints_disjoint enc rest right) as [tail te].
    cbn [snd] in Hinner, IH |- *.
    cbn [audit_disjoint_source_work].
    rewrite audit_disjoint_source_work_app; lia.
Qed.
