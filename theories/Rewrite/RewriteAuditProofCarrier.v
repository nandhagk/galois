(** * RewriteAuditProofCarrier

    This module defines provenance nodes, their reasons, timestamps, and validity conditions.
    For example, a reflexivity reason has no referenced evidence nodes.
    Builds on: RewriteEquality and
    RewriteRules. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
Import List.ListNotations.

Inductive rw_evidence_reason (K Sort V H : Type) : Type :=
  | RWEvidenceRefl : rw_evidence_reason K Sort V H
  | RWEvidenceRule : nat -> Map.t H (rw_term K Sort V) -> rw_evidence_reason K Sort V H
  | RWEvidenceSym : positive -> rw_evidence_reason K Sort V H
  | RWEvidenceTrans : positive -> positive -> rw_evidence_reason K Sort V H
  | RWEvidenceCongruence : list positive -> rw_evidence_reason K Sort V H.

Arguments RWEvidenceRefl {K Sort V H}.
Arguments RWEvidenceRule {K Sort V H}.
Arguments RWEvidenceSym {K Sort V H}.
Arguments RWEvidenceTrans {K Sort V H}.
Arguments RWEvidenceCongruence {K Sort V H}.

Record rw_evidence_node (K Sort V H : Type) : Type := RWEvidenceNode {
  rw_evidence_left : rw_term K Sort V;
  rw_evidence_right : rw_term K Sort V;
  rw_evidence_reason_of : rw_evidence_reason K Sort V H;
  rw_evidence_time : nat * nat
}.

Arguments RWEvidenceNode {K Sort V H}.
Arguments rw_evidence_left {K Sort V H}.
Arguments rw_evidence_right {K Sort V H}.
Arguments rw_evidence_reason_of {K Sort V H}.
Arguments rw_evidence_time {K Sort V H}.

Record rw_provenance (K Sort V H : Type) : Type := RWProvenance {
  rw_provenance_ids : list positive;
  rw_provenance_nodes : Map.t positive (rw_evidence_node K Sort V H)
}.

Arguments RWProvenance {K Sort V H}.
Arguments rw_provenance_ids {K Sort V H}.
Arguments rw_provenance_nodes {K Sort V H}.

Definition rw_reason_references {K Sort V H} (r : rw_evidence_reason K Sort V H) : list positive :=
  match r with
  | RWEvidenceRefl => []
  | RWEvidenceRule _ _ => []
  | RWEvidenceSym child => [child]
  | RWEvidenceTrans first second => [first; second]
  | RWEvidenceCongruence children => children
  end.

(** Evidence timestamps use lexicographic non-strict order on group and position. *)
Definition rw_evidence_time_le (first second : nat * nat) : Prop :=
  fst first < fst second \/ fst first = fst second /\ snd first <= snd second.

(** Evidence timestamps use lexicographic strict order on group and position. *)
Definition rw_evidence_time_lt (first second : nat * nat) : Prop :=
  fst first < fst second \/ fst first = fst second /\ snd first < snd second.

(** An evidence node's reason relates its endpoints by reflexivity, an instantiated
    rule, symmetry, transitivity, or congruence over stored child nodes. *)
Definition rw_evidence_reason_valid {K Sort V H} (EH : encoding H) (sig : rw_signature K Sort V)
    (rules : list (rw_rule K Sort V H)) (p : rw_provenance K Sort V H)
    (node : rw_evidence_node K Sort V H) : Prop :=
  let left := rw_evidence_left node in
  let right := rw_evidence_right node in
  let lookup id := Map.get positive_encoding id (rw_provenance_nodes p) in
  match rw_evidence_reason_of node with
  | RWEvidenceRefl => left = right
  | RWEvidenceRule index bindings =>
    exists r,
      nth_error rules index = Some r /\
      let sub := fun h => Map.get EH h bindings in
      rw_sub_typed sig (rw_hole_sort r) sub /\ rw_condition r sub = true /\
      rw_instantiate sub (rw_lhs r) = Some left /\
      rw_instantiate sub (rw_rhs r) = Some right
  | RWEvidenceSym child =>
    exists n, lookup child = Some n /\
      rw_evidence_left n = right /\ rw_evidence_right n = left
  | RWEvidenceTrans first second =>
    exists n m,
      lookup first = Some n /\ lookup second = Some m /\
      rw_evidence_left n = left /\ rw_evidence_right n = rw_evidence_left m /\
      rw_evidence_right m = right
  | RWEvidenceCongruence children =>
    exists sort op ls rs,
      left = RWApp sort op ls /\ right = RWApp sort op rs /\ length ls = length rs /\
      Forall2 (fun id pair => exists n, lookup id = Some n /\
        rw_evidence_left n = fst pair /\ rw_evidence_right n = snd pair)
        children (combine ls rs)
  end.

(** Provenance has a well-formed node map enumerated without duplicates, valid reasons,
    and existing smaller references with no later timestamps. *)
Definition rw_provenance_valid {K Sort V H} (EH : encoding H) (sig : rw_signature K Sort V)
    (rules : list (rw_rule K Sort V H)) (p : rw_provenance K Sort V H) : Prop :=
  NoDup (rw_provenance_ids p) /\
  Map.wf positive_encoding (rw_provenance_nodes p) /\
  (forall id, In id (rw_provenance_ids p) <->
    exists node, Map.get positive_encoding id (rw_provenance_nodes p) = Some node) /\
  forall id node, Map.get positive_encoding id (rw_provenance_nodes p) = Some node ->
    rw_evidence_reason_valid EH sig rules p node /\
    Forall (fun child => (child < id)%positive /\
      exists n, Map.get positive_encoding child (rw_provenance_nodes p) = Some n /\
        rw_evidence_time_le (rw_evidence_time n) (rw_evidence_time node))
      (rw_reason_references (rw_evidence_reason_of node)).

(** Every stored node of valid provenance relates its endpoints by the generated
    [rw_equal] relation for the given rules. *)
Definition rw_provenance_sound_contract : Prop :=
  forall K Sort V H C (EH : encoding H) (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (rules : list (rw_rule K Sort V H))
    (p : rw_provenance K Sort V H),
    rw_provenance_valid EH sig rules p ->
    forall id node, Map.get positive_encoding id (rw_provenance_nodes p) = Some node ->
      rw_equal sig admissible rules (rw_evidence_left node) (rw_evidence_right node).
