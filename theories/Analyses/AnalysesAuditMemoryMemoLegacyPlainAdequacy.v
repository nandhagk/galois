(** * Semantics of the memo-threaded legacy producer

    Every retained pair passes its own all-walk check, and every executed memo query preserves
    the returned persistent state. For example, duplicate nodes can overwrite only with another
    checked candidate. Builds on: plain memo query semantics and the historical byte theorem. *)

From Stdlib Require Import List Bool PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs.
From Galois.Domains Require Import DomainsFootprint.
From Galois.Views Require Import ViewsSemantics ViewsGraph ViewsMemoryEffects.
From Galois.Analyses Require Import AnalysesMemoryBase AnalysesMemoryGraph AnalysesMemoryWalk
  AnalysesMemoryLegacy
  AnalysesAuditMemoryState AnalysesAuditMemoryMemoExecute AnalysesAuditMemoryMemoExecuteAdequacy
  AnalysesAuditMemoryMemoLegacyPlain.
Import List.ListNotations.

(** A successful request's incoming version is valid by the original before-domain law. *)
Lemma audit_memo_legacy_request_valid N E T (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) (mg : memory_graph N E)
    reached listed (table : Map.t E (Map.t nat (memory_effect T)))
    (reads : N -> list (footprint T)) loads node
    scope start :
  memory_graph_wf g effects mg ->
  audit_memo_legacy_request EN EE g mg reached listed table reads loads node = Some (scope,
    start) ->
  memory_valid_version g effects mg start.
Proof.
  intros Hwf Hrequest; unfold audit_memo_legacy_request in Hrequest.
  destruct (loads node) as [[edge index]|]; [|discriminate].
  destruct (Pos.eqb (encode EN (Graph.source g edge)) (encode EN node) &&
    FinSet.mem EN (Graph.source g edge) reached && FinSet.mem EE edge listed)%bool;
    [|discriminate].
  destruct (memory_walk_effect_get EE table edge index) as [effect|]; [|discriminate].
  destruct (memory_before mg edge index) as [input|] eqn:Hbefore; [|discriminate].
  destruct (memory_effect_has_read effect); [|discriminate].
  injection Hrequest as Hscope Hstart; subst scope start.
  destruct (proj1 (memory_before_domain Hwf edge index) (ex_intro _ input Hbefore))
    as [actual Hoccurrence].
  destruct (memory_occurrence_input_valid g effects mg Hwf edge index actual Hoccurrence)
    as [version [Hversion [Hvalid Hdefinition]]].
  rewrite Hbefore in Hversion; injection Hversion as Hsame; subst version; exact Hvalid.
Qed.

(** A retained proposal has passed the actual pair checker on its original operands. *)
Lemma audit_memo_legacy_retain_checked F N E T (EN : encoding N) (EF : encoding F)
    (ET : encoding T) function (g : Graph.t N E) (prep : prepared EN g) reached writes reads
    node proposal (candidate : mem_node F N) :
  legacy_retain EN EF ET function g prep reached writes reads node proposal = Some candidate ->
  legacy_pair_check EN EF ET function g prep reached writes reads node candidate = true.
Proof.
  unfold legacy_retain; destruct proposal as [proposed|]; [|discriminate].
  destruct (legacy_pair_check EN EF ET function g prep reached writes reads node proposed)
    eqn:Hchecked; [|discriminate].
  intro Hcandidate; injection Hcandidate as Hsame; subst proposed; exact Hchecked.
Qed.

Section Nodes.
  Context {F N E T : Type}.
  Context (EN : encoding N) (EE : encoding E) (EF : encoding F) (ET : encoding T).
  Context (function : F) (g : Graph.t N E) (effects : E -> list (memory_effect T)).
  Context (mg : memory_graph N E) (cfg : Graph.t N (N * N)) (prep : prepared EN cfg).
  Context (reached : FinSet.t N) (listed : FinSet.t E).
  Context (writes reads : N -> list (footprint T)) (loads : N -> option (E * nat)).
  Context (query_fuel : positive).
  Hypothesis Hwf : memory_graph_wf g effects mg.

  (** Each node preserves memo validity and checks every candidate it returns. *)
  Lemma audit_memo_legacy_one_valid state node :
    memo_valid EN EE ET g effects mg state ->
    let '(candidate, next) := audit_memo_legacy_one EN EE EF ET function g effects mg state cfg
      prep reached listed writes reads loads query_fuel node in
    memo_valid EN EE ET g effects mg next /\
    (forall definition, candidate = Some definition ->
      legacy_pair_check EN EF ET function cfg prep reached writes reads node definition = true).
  Proof.
    intro Hvalid; unfold audit_memo_legacy_one.
    destruct (audit_memo_legacy_request EN EE g mg reached listed
      (@memo_effect_index N E T EN g effects mg state) reads loads node)
      as [[scope start]|] eqn:Hrequest.
    - pose proof (audit_memo_legacy_request_valid N E T EN EE g effects mg reached listed
        (@memo_effect_index N E T EN g effects mg state) reads loads node scope start Hwf Hrequest)
        as Hstart.
      pose proof (proj1 (audit_memory_memo_query_correct N E T EN EE ET g effects mg state scope
        start query_fuel Hvalid Hwf Hstart)) as Hnext.
      destruct (audit_memory_memo_query EN EE ET g effects mg state scope start query_fuel)
        as [result next]; cbn [snd] in Hnext.
      split; [exact Hnext|].
      intros definition Hcandidate; eapply audit_memo_legacy_retain_checked; exact Hcandidate.
    - split; [exact Hvalid|intros definition Hfalse; discriminate].
  Qed.

  (** An index invariant couples each stored node with the check for that same node. *)
  Definition audit_memo_legacy_pairs_checked (pairs : Map.t N (option (mem_node F N))) : Prop :=
    forall node definition, Map.get EN node pairs = Some (Some definition) ->
      legacy_pair_check EN EF ET function cfg prep reached writes reads node definition = true.

  (** Every sequential update retains the index invariant and the actual memo state validity. *)
  Lemma audit_memo_legacy_nodes_valid nodes state pairs :
    memo_valid EN EE ET g effects mg state -> audit_memo_legacy_pairs_checked pairs ->
    let '(final, next) := audit_memo_legacy_nodes EN EE EF ET function g effects mg cfg prep reached
      listed writes reads loads query_fuel nodes state pairs in
    memo_valid EN EE ET g effects mg next /\ audit_memo_legacy_pairs_checked final.
  Proof.
    revert state pairs; induction nodes as [|node rest IH]; intros state pairs Hstate Hpairs.
    - exact (conj Hstate Hpairs).
    - cbn [audit_memo_legacy_nodes].
      pose proof (audit_memo_legacy_one_valid state node Hstate) as Hone.
      destruct (audit_memo_legacy_one EN EE EF ET function g effects mg state cfg prep reached
        listed writes reads loads query_fuel node) as [candidate next].
      destruct Hone as [Hnext Hcandidate].
      apply IH; [exact Hnext|].
      intros queried definition Hlookup.
      destruct (Pos.eq_dec (encode EN queried) (encode EN node)) as [Hsame|Hdifferent].
      + apply (encode_injective EN) in Hsame; subst queried.
        rewrite Map.get_set_same in Hlookup; injection Hlookup as Hcandidate_eq.
        apply Hcandidate; exact Hcandidate_eq.
      + rewrite Map.get_set_other in Hlookup.
        * apply Hpairs; exact Hlookup.
        * intro Hequal; apply Hdifferent; now rewrite Hequal.
  Qed.
End Nodes.

(** The producer's indexed candidates pass the independent checker and preserve the full memo. *)
Lemma audit_memory_memo_legacy_checked :
  memo_legacy_checked_statement (@audit_memory_memo_legacy_project).
Proof.
  intros F N E T EN EE EF ET function g effects writes reads mg state loads query_fuel Hvalid Hwf.
  pose proof (audit_memo_legacy_nodes_valid EN EE EF ET function g effects mg (legacy_cfg EN g)
    (prepare EN (legacy_cfg EN g))
    (legacy_reached (prepare EN (legacy_cfg EN g)) (Graph.entries g))
    (FinSet.of_list EE (edges_of g)) writes reads loads query_fuel Hwf (Graph.nodes g) state
    Map.empty Hvalid) as Hnodes.
  assert (Hempty : audit_memo_legacy_pairs_checked EN EF ET function (legacy_cfg EN g)
    (prepare EN (legacy_cfg EN g))
    (legacy_reached (prepare EN (legacy_cfg EN g)) (Graph.entries g)) writes reads Map.empty).
  { intros node definition Hlookup; rewrite Map.get_empty in Hlookup; discriminate. }
  specialize (Hnodes Hempty).
  unfold audit_memory_memo_legacy_project.
  change (Graph.entries (legacy_cfg EN g)) with (Graph.entries g).
  destruct (audit_memo_legacy_nodes EN EE EF ET function g effects mg (legacy_cfg EN g)
    (prepare EN (legacy_cfg EN g))
    (legacy_reached (prepare EN (legacy_cfg EN g)) (Graph.entries g))
    (FinSet.of_list EE (edges_of g)) writes reads loads query_fuel (Graph.nodes g) state Map.empty)
    as [pairs next].
  destruct Hnodes as [Hnext Hchecked]; split; [|exact Hnext].
  unfold no_clobber_check; cbn [def_of_load].
  apply forallb_forall; intros node Hin.
  destruct (Map.get EN node pairs) as [[candidate|]|] eqn:Hlookup; try reflexivity.
  apply Hchecked; exact Hlookup.
Qed.

(** The fixed producer establishes acceptance before applying the same-history byte law. *)
Theorem audit_memory_memo_legacy_semantics : audit_memory_memo_legacy_semantics_statement.
Proof.
  split; [exact audit_memory_memo_legacy_checked|].
  intros S O N E T F L m bv EN EE EF ET function effects reads mg state loads query_fuel
    Hbytes Hvalid Hwf.
  pose proof (audit_memory_memo_legacy_checked F N E T EN EE EF ET function (cfg (bgv bv))
    effects (writes_at bv) reads mg state loads query_fuel Hvalid Hwf) as Hchecked.
  destruct (audit_memory_memo_legacy_project EN EE EF ET function (cfg (bgv bv)) effects
    (writes_at bv) reads mg state loads query_fuel) as [ms next]; cbn [fst].
  destruct (no_clobber_unchanged m bv EN EF ET function ms reads Hbytes (proj1 Hchecked))
    as [Hdefinition Hentry].
  split; [|exact Hentry].
  intros before after first edge rest node.
  exact (Hdefinition before first after edge rest node).
Qed.
