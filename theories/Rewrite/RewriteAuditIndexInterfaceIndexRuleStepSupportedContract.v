(** * RewriteAuditIndexInterfaceIndexRuleStepSupportedContract

    This module states preservation of index support by a successful public rule step.
    For example, a successful rule-0 step must retain bucket-node support when the rules
    are well formed and the input has both support properties.
    Builds on: RewriteAuditIndexPublic and
    RewriteAuditIndexReference. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexPlainPublic RewriteAuditIndexPublic
  RewriteAuditIndexReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_index_rule_step : forall {K Sort V H},
  encoding K -> encoding Sort -> encoding V -> encoding H -> rw_signature K Sort V ->
  list (rw_rule K Sort V H) -> rw_index_state K Sort V -> rw_attempt K Sort V H ->
  option (rw_index_state K Sort V).

(** A successful rule step preserves support and bucket-node support when its rules are
    well formed and the input state has both properties. *)
Definition rw_index_rule_step_supported_contract : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (sig : rw_signature K Sort V) (rules : list (rw_rule K Sort V H))
    (state next : rw_index_state K Sort V) attempt,
    Forall (rw_rule_wf sig) rules ->
    index_supported_valid EK ES EV sig state ->
    index_bucket_node_support EK ES EV state ->
    rw_index_rule_step EK ES EV EH sig rules state attempt = Some next ->
    index_supported_valid EK ES EV sig next /\
    index_bucket_node_support EK ES EV next.

End FuturePublicImplementations.
