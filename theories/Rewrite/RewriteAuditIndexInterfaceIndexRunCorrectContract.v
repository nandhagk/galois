(** * RewriteAuditIndexInterfaceIndexRunCorrectContract

    States prospective semantic and cleanliness guarantees for index runs.
    For example, with a well-formed, sound, productive input and sound, well-formed rules,
    fuel 1 requires a clean final graph.
    Builds on: RewriteAuditIndexReference and
    RewriteRun. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexPlainPublic RewriteAuditIndexReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_index_run : forall {K Sort V H},
  encoding K -> encoding Sort -> encoding V -> encoding H -> rw_signature K Sort V ->
  list (rw_rule K Sort V H) ->
  (rw_snapshot_view K Sort V -> option (rw_attempt K Sort V H)) -> N -> rw_graph K Sort V ->
  rw_run_result K Sort V * list rw_index_event * list (rw_run_event K Sort V H).

(** Sound, well-formed rules on a well-formed, sound, productive input graph yield a
    well-formed, sound, productive extension, clean when fuel is nonzero. *)
Definition rw_index_run_correct_contract : Prop :=
  forall K Sort V H C (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (rules : list (rw_rule K Sort V H))
    strategy fuel (g : rw_graph K Sort V),
    Forall (rw_rule_wf sig) rules -> Forall (rw_rule_sound sig admissible) rules ->
    rw_graph_wf sig g -> rw_graph_sound sig admissible rules g -> rw_productive g ->
    let '(result, _, _) := rw_index_run EK ES EV EH sig rules strategy fuel g in
    rw_graph_wf sig (rw_run_graph result) /\
    rw_graph_sound sig admissible rules (rw_run_graph result) /\
    rw_productive (rw_run_graph result) /\ rw_extends g (rw_run_graph result) /\
    (fuel <> 0%N -> rw_clean (rw_run_graph result)).

End FuturePublicImplementations.
