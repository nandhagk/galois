(** * Factored expression definitions

    Version origins distinguish missing entry values, initial values, computations and phis.
    For example, a phi definition is after parameter binding rather than at block entry.
    Builds on: AnalysesSsaPreFamily, ProgramSsaPoints and GraphFrontierSpec. *)

From Stdlib Require Import List Bool NArith.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseCode BaseEq BaseMap BaseSet BaseIndex.
From Galois.Graph Require Import GraphModel GraphPrepared GraphDomSpec GraphCheckDom
  GraphFrontierSpec GraphFrontierIdf GraphFrontierSweep GraphReach.
From Galois.Program Require Import ProgramCfg ProgramSsa ProgramSsaPoints.
From Galois.Framework Require Import FrameworkUtil.
From Galois.Analyses.Ssa Require Import AnalysesSsaPreContext AnalysesSsaPreFamily.
Import List.ListNotations Cost.Notations.

Module PreFrg.

(** Constructor origins keep unavailable sentinels distinct from valid entry values. *)
Inductive version (B E U : Type) :=
  | Unavailable (u : U)
  | Initial (u : U)
  | Fresh (e : E) (u : U)
  | Phi (b : B) (u : U).
Arguments Unavailable {B E U}.
Arguments Initial {B E U}.
Arguments Fresh {B E U}.
Arguments Phi {B E U}.

(** Each incoming link retains the real-use bit of its selected version. *)
Record operand (B E U : Type) := Operand {
  operand_version : version B E U;
  real_use : bool
}.
Arguments Operand {B E U}.
Arguments operand_version {B E U}.
Arguments real_use {B E U}.

(** Raw construction retains the actual discovery, naming and renaming engine outcome. *)
Inductive completion :=
  | Completed
  | DiscoveryExhausted
  | RenameExhausted
  | MissingBlockName.

(** The indexes distinguish incoming edge identities even when their endpoints coincide. *)
Record frg (B BE E U : Type) := Frg {
  versions : list (version B E U);
  occurrences : Map.t E (version B E U);
  fresh : FinSet.t E;
  phis : FinSet.t (B * U);
  operands : Map.t ((B * U) * BE) (operand B E U);
  unsafe : FinSet.t (B * U);
  status : completion
}.
Arguments Frg {B BE E U}.
Arguments versions {B BE E U}.
Arguments occurrences {B BE E U}.
Arguments fresh {B BE E U}.
Arguments phis {B BE E U}.
Arguments operands {B BE E U}.
Arguments unsafe {B BE E U}.
Arguments status {B BE E U}.

Definition version_expr {B E U} (d : version B E U) :=
  match d with
  | Unavailable u => u
  | Initial u => u
  | Fresh _ u => u
  | Phi _ u => u
  end.

Definition version_key {B E U} (d : version B E U) :
    U + (U + ((E * U) + (B * U))) :=
  match d with
  | Unavailable u => inl u
  | Initial u => inr (inl u)
  | Fresh e u => inr (inr (inl (e, u)))
  | Phi b u => inr (inr (inr (b, u)))
  end.

Section Encodings.
Context {B BE N E V K G C U : Type}.
Variable c : Pre.ctx B BE N E V K G C U.

Definition phi_encoding := pair_encoding (Pre.eb (Pre.keys c)) (Pre.eu (Pre.keys c)).
Definition link_encoding := pair_encoding phi_encoding (Pre.ebe (Pre.keys c)).
Definition origin_encoding :=
  sum_encoding (Pre.eu (Pre.keys c))
    (sum_encoding (Pre.eu (Pre.keys c))
      (sum_encoding (pair_encoding (Pre.ee (Pre.keys c)) (Pre.eu (Pre.keys c)))
        phi_encoding)).
Definition version_encoding : encoding (version B E U) :=
  Encoding (fun d => Cost.step ;; encode_c origin_encoding (version_key d)).

(** Version encoding delegates all component and serializer work to the owning derived encodings. *)
Theorem version_encoding_equation d :
  encode version_encoding d = encode origin_encoding (version_key d).
Proof.
  reflexivity.
Qed.

(** Each version retains the full charge of its derived constructor-tagged key. *)
Theorem version_encoding_cost d :
  Cost.ticks (encode_c version_encoding d) =
    (1 + Cost.ticks (encode_c origin_encoding (version_key d)))%N.
Proof.
  unfold version_encoding; cbn [encode_c]; autorewrite with galois_cost; reflexivity.
Qed.

(** Phi keys preserve both their block and expression identities. *)
Theorem phi_encoding_laws :
  Pre.laws c -> encoding_laws phi_encoding.
Proof.
  intro Hlaw; apply pair_encoding_laws.
  - exact (Pre.eb_laws c (Pre.graphs c Hlaw)).
  - exact (Pre.eu_laws c (Pre.graphs c Hlaw)).
Qed.

(** Incoming link keys additionally preserve the individual parallel edge identity. *)
Theorem link_encoding_laws :
  Pre.laws c -> encoding_laws link_encoding.
Proof.
  intro Hlaw; apply pair_encoding_laws; [apply phi_encoding_laws; exact Hlaw|].
  exact (Pre.ebe_laws c (Pre.graphs c Hlaw)).
Qed.

(** Tagged origins and lawful component dictionaries give injective version identities. *)
Theorem version_encoding_laws :
  Pre.laws c -> encoding_laws version_encoding.
Proof.
  intro Hlaw.
  assert (Horigins : encoding_laws origin_encoding).
  { apply sum_encoding_laws; [exact (Pre.eu_laws c (Pre.graphs c Hlaw))|].
    apply sum_encoding_laws; [exact (Pre.eu_laws c (Pre.graphs c Hlaw))|].
    apply sum_encoding_laws; [|apply phi_encoding_laws; exact Hlaw].
    apply pair_encoding_laws.
    - exact (Pre.ee_laws c (Pre.graphs c Hlaw)).
    - exact (Pre.eu_laws c (Pre.graphs c Hlaw)). }
  constructor; intros x y Hkey; rewrite !version_encoding_equation in Hkey.
  apply (encode_injective Horigins) in Hkey.
  destruct x, y; cbn [version_key] in Hkey; inversion Hkey; reflexivity.
Qed.

End Encodings.

Section Definitions.
Context {B BE N E V K G C U : Type}.
Variable c : Pre.ctx B BE N E V K G C U.

(** Definition seeds include entry, pure occurrence blocks and every ordered operand home. *)
Inductive definition_block (u : U) : B -> Prop :=
  | definition_entry : forall b, In b (Graph.entries (Pre.bg c)) -> definition_block u b
  | definition_occurrence : forall e,
      In e (Cfg.edges (Pre.point_cfg c)) ->
      Pre.recomputed c e = Some u -> Pre.pure c u = true ->
      definition_block u
        (SsaPoints.block_of_point (Pre.points (Pre.input c)) (Graph.source (Pre.pg c) e))
  | definition_operand : forall x, In x (Pre.operands c u) ->
      definition_block u (Ssa.home (Pre.ssa (Pre.input c)) x).

(** Phi placement is the least frontier closure including translated predecessor expressions. *)
Inductive phi_needed : U -> B -> Prop :=
  | phi_parameter : forall u b x, PreFamily.in_family c u ->
      In b (Graph.nodes (Pre.bg c)) -> ~ In b (Graph.entries (Pre.bg c)) ->
      In x (Pre.operands c u) ->
      In x (SsaPoints.block_params (Pre.points (Pre.input c)) b) -> phi_needed u b
  | phi_seed : forall u d b, PreFamily.in_family c u -> definition_block u d ->
      in_df (Pre.bg c) d b -> phi_needed u b
  | phi_iterate : forall u d b, phi_needed u d -> in_df (Pre.bg c) d b -> phi_needed u b
  | phi_translate : forall u b be v target, phi_needed u b ->
      In be (Cfg.edges (Pre.block_cfg c)) -> Graph.target (Pre.bg c) be = b ->
      Pre.translate c be u = Some v ->
      in_df (Pre.bg c) (Graph.source (Pre.bg c) be) target -> phi_needed v target.

(** Every recursively translated phi retains membership in the same least expression family. *)
Theorem phi_needed_family {u b} :
  phi_needed u b -> PreFamily.in_family c u.
Proof.
  intro Hneeded; induction Hneeded as
    [u b x Hu Hb Hentry Hoperand Hparam|
     u d b Hu Hdef Hfrontier|
     u d b Hneeded IH Hfrontier|
     u b be v target Hneeded IH Hbe Htarget Htranslate Hfrontier].
  - exact Hu.
  - exact Hu.
  - exact IH.
  - eapply Pre.family_translate; eassumption.
Qed.

Local Lemma frontier_target_listed {d b} :
  Pre.laws c -> in_df (Pre.bg c) d b -> In b (Graph.nodes (Pre.bg c)).
Proof.
  intros Hlaw [e [Hsource [Hedge [Htarget _]]]].
  rewrite <- Htarget; apply (reachable_in_nodes _ _ (blocks_graph_wf
    (Pre.point_laws c (Pre.graphs c Hlaw)))).
  eapply reachable_step; eassumption.
Qed.

(** Every phi site is a listed source block, including sites reached through translation. *)
Theorem phi_needed_nodes {u b} :
  Pre.laws c -> phi_needed u b -> In b (Graph.nodes (Pre.bg c)).
Proof.
  intros Hlaw Hneeded; destruct Hneeded.
  - assumption.
  - eapply frontier_target_listed; eassumption.
  - eapply frontier_target_listed; eassumption.
  - eapply frontier_target_listed; eassumption.
Qed.

Definition version_point_c (d : version B E U) :=
  match d with
  | Unavailable _ => Cost.ret None
  | Initial _ => Cost.ret (nth_error (Graph.entries (Pre.pg c)) 0)
  | Fresh e _ =>
    Cost.step ;;
    Cost.map (@Some N) (Graph.target_c (Pre.pg c) e)
  | Phi b _ =>
    Cost.step ;;
    let* e := SsaPoints.parameter_edge_c (Pre.points (Pre.input c)) b in
    Cost.step ;;
    Cost.map (@Some N) (Graph.target_c (Pre.pg c) e)
  end.
Definition version_point d := Cost.value (version_point_c d).

(** Definitions become available after their actual instruction or parameter-edge occurrence. *)
Theorem version_point_equation d :
  version_point d =
    match d with
    | Unavailable _ => None
    | Initial _ => nth_error (Graph.entries (Pre.pg c)) 0
    | Fresh e _ => Some (Graph.target (Pre.pg c) e)
    | Phi b _ => Some (Graph.target (Pre.pg c)
        (SsaPoints.parameter_edge (Pre.points (Pre.input c)) b))
    end.
Proof.
  destruct d; unfold version_point, version_point_c; autorewrite with galois_cost;
    reflexivity.
Qed.

(** Eligible definitions use the static source domains independently of a graph producer. *)
Definition definition_domain (d : version B E U) : Prop :=
  match d with
  | Unavailable u => PreFamily.in_family c u
  | Initial u => PreFamily.in_family c u /\ Pre.initial c u = true
  | Fresh e u => In e (Cfg.edges (Pre.point_cfg c)) /\ Pre.recomputed c e = Some u
  | Phi b u => phi_needed u b
  end.

End Definitions.

(** Tail membership retains membership of the original ordered point list. *)
Lemma tail_member {X} (x : X) xs : In x (tl xs) -> In x xs.
Proof.
  destruct xs; cbn; tauto.
Qed.

(** Ordered instruction chains place every edge target strictly after the first point. *)
Lemma chain_target {N E} (g : Graph.t N E) {ns es e} :
  point_chain g ns es -> In e es -> In (Graph.target g e) (tl ns).
Proof.
  intros Hchain; induction Hchain as [n|n next ns edge es Hedge Htarget Hchain IH].
  - intros [].
  - intros [<-|Hin]; [cbn; left; symmetry; exact Htarget|].
    cbn; right; exact (IH Hin).
Qed.

Local Lemma chain_target_unique {N E} (g : Graph.t N E) {ns es} :
  point_chain g ns es -> NoDup ns ->
  forall e e', In e es -> In e' es -> Graph.target g e = Graph.target g e' -> e = e'.
Proof.
  intro Hchain; induction Hchain as [n|n next ns edge es Hedge Htarget Hchain IH];
    intros Hnodup e e' He He' Heq; [contradiction|].
  apply NoDup_cons_iff in Hnodup; destruct Hnodup as [Hfirst Htail].
  apply NoDup_cons_iff in Htail; destruct Htail as [Hnext Hrest].
  destruct He as [<-|He], He' as [<-|He'].
  - reflexivity.
  - exfalso; apply Hnext; rewrite <- Htarget, Heq; exact (chain_target g Hchain He').
  - exfalso; apply Hnext; rewrite <- Htarget, <- Heq; exact (chain_target g Hchain He).
  - apply IH; [constructor; assumption|exact He|exact He'|exact Heq].
Qed.

(** Every instruction-chain edge occurs in an outgoing list of one of the chain's points. *)
Lemma chain_source {N E} (g : Graph.t N E) {ns es e} :
  point_chain g ns es -> In e es -> exists n, In n ns /\ In e (Graph.out g n).
Proof.
  intro Hchain; induction Hchain as [n|n next ns edge es Hedge Htarget Hchain IH].
  - intros [].
  - intros [<-|Hin].
    + exists n; split; [now left|exact Hedge].
    + destruct (IH Hin) as [q [Hq He]]; exists q; split; [now right|exact He].
Qed.

Section PointDomains.
Context {B BE N E V K G C U : Type}.
Variable c : Pre.ctx B BE N E V K G C U.
Let s := Pre.points (Pre.input c).

(** Every listed point belongs to the ordered point list of its actual owner block. *)
Lemma point_owner_listed {n} :
  Pre.laws c -> In n (Graph.nodes (Pre.pg c)) ->
  In (SsaPoints.block_of_point s n) (Graph.nodes (Pre.bg c)) /\
    In n (SsaPoints.points_in_block s (SsaPoints.block_of_point s n)).
Proof.
  intros Hlaw Hn; pose proof (Pre.point_laws c (Pre.graphs c Hlaw)) as Hpoints.
  fold s in Hpoints.
  apply (points_covered Hpoints) in Hn; destruct Hn as [b [Hb Hpoint]].
  rewrite (points_owner Hpoints b n Hb Hpoint); auto.
Qed.

(** Every listed internal edge belongs to its owner's ordered instruction chain. *)
Lemma internal_edge_block {e} :
  Pre.laws c -> In e (Cfg.edges (Pre.point_cfg c)) ->
  SsaPoints.block_edge_of s e = None ->
  exists b, In b (Graph.nodes (Pre.bg c)) /\
    In e (SsaPoints.instruction_edges s b) /\
    In (Graph.target (Pre.pg c) e) (tl (SsaPoints.points_in_block s b)).
Proof.
  intros Hlaw He Hinternal; apply Cfg.edges_spec in He; destruct He as [n [Hn He]].
  pose proof (Pre.point_laws c (Pre.graphs c Hlaw)) as Hpoints.
  destruct (point_owner_listed Hlaw Hn) as [Hb Hpoint].
  pose proof (instruction_edges_complete Hpoints n e Hn He Hinternal) as Hin.
  exists (SsaPoints.block_of_point s n); split; [exact Hb|]; split; [exact Hin|].
  exact (chain_target _ (points_ordered Hpoints _ Hb) Hin).
Qed.

(** Distinct internal instruction occurrences have distinct target points. *)
Lemma internal_target_unique {e e'} :
  Pre.laws c -> In e (Cfg.edges (Pre.point_cfg c)) ->
  In e' (Cfg.edges (Pre.point_cfg c)) ->
  SsaPoints.block_edge_of s e = None -> SsaPoints.block_edge_of s e' = None ->
  Graph.target (Pre.pg c) e = Graph.target (Pre.pg c) e' -> e = e'.
Proof.
  intros Hlaw He He' Hi Hi' Heq.
  pose proof (Pre.point_laws c (Pre.graphs c Hlaw)) as Hpoints.
  fold s in Hpoints.
  destruct (internal_edge_block Hlaw He Hi) as [b [Hb [Hedge Htarget]]].
  destruct (internal_edge_block Hlaw He' Hi') as [b' [Hb' [Hedge' Htarget']]].
  assert (Hsame : b = b').
  { rewrite <- (points_owner Hpoints b _ Hb (tail_member _ _ Htarget)).
    rewrite Heq; exact (points_owner Hpoints b' _ Hb' (tail_member _ _ Htarget')). }
  subst b'; eapply chain_target_unique.
  - exact (points_ordered Hpoints b Hb).
  - exact (points_unique Hpoints b).
  - exact Hedge.
  - exact Hedge'.
  - exact Heq.
Qed.

(** A listed block's parameter edge is an internal occurrence in the point graph. *)
Lemma parameter_edge_listed {b} :
  Pre.laws c -> In b (Graph.nodes (Pre.bg c)) ->
  In (SsaPoints.parameter_edge s b) (Cfg.edges (Pre.point_cfg c)) /\
    SsaPoints.block_edge_of s (SsaPoints.parameter_edge s b) = None.
Proof.
  intros Hlaw Hb; pose proof (Pre.point_laws c (Pre.graphs c Hlaw)) as Hpoints.
  pose proof (nth_error_In _ _ (parameter_edge_first Hpoints b Hb)) as He.
  split; [|exact (instruction_edges_internal Hpoints b _ Hb He)].
  destruct (chain_source _ (points_ordered Hpoints b Hb) He) as [n [Hn Hedge]].
  apply Cfg.edges_spec; exists n; split; [|exact Hedge].
  apply (points_covered Hpoints); exists b; auto.
Qed.

(** Internal definition targets cannot be the unique entry's first instruction point. *)
Lemma internal_target_not_entry {e n} :
  Pre.laws c -> In e (Cfg.edges (Pre.point_cfg c)) ->
  SsaPoints.block_edge_of s e = None -> In n (Graph.entries (Pre.pg c)) ->
  Graph.target (Pre.pg c) e <> n.
Proof.
  intros Hlaw He Hi Hentry Heq.
  pose proof (Pre.point_laws c (Pre.graphs c Hlaw)) as Hpoints.
  fold s in Hpoints.
  destruct (Pre.entry_position c (Pre.graphs c Hlaw))
    as [entry [first [Hb [Hn Hfirst]]]].
  fold s in Hfirst.
  rewrite Hn in Hentry; destruct Hentry as [<-|[]].
  assert (Hentryblock : In entry (Graph.nodes (Pre.bg c))).
  { apply (entries_in (blocks_graph_wf Hpoints)).
    change (In entry (Graph.entries (Pre.bg c))); rewrite Hb; now left. }
  destruct (internal_edge_block Hlaw He Hi) as [b [Hblock [Hedge Htarget]]].
  pose proof (nth_error_In _ _ Hfirst) as Hfirstpoint.
  assert (Howner : b = entry).
  { rewrite <- (points_owner Hpoints b _ Hblock (tail_member _ _ Htarget)).
    rewrite Heq; exact (points_owner Hpoints entry first Hentryblock Hfirstpoint). }
  subst b; rewrite Heq in Htarget.
  pose proof (points_unique Hpoints entry) as Hunique.
  destruct (SsaPoints.points_in_block s entry) as [|head rest];
    cbn in Hfirst; [discriminate|].
  inversion Hfirst; subst head; inversion Hunique; subst; contradiction.
Qed.

Local Lemma initial_fresh_disjoint {e u q} :
  Pre.laws c -> definition_domain c (Fresh e u) ->
  version_point c (Initial u) = Some q -> version_point c (Fresh e u) <> Some q.
Proof.
  intros Hlaw [He Hcomputed] Hentry Hpoint.
  rewrite version_point_equation in Hentry, Hpoint.
  inversion Hpoint; subst q.
  eapply internal_target_not_entry; [exact Hlaw|exact He| | |reflexivity].
  - exact (proj1 (Pre.real_internal c (Pre.kills c Hlaw) e u Hcomputed)).
  - exact (nth_error_In _ _ Hentry).
Qed.

Local Lemma initial_phi_disjoint {b u q} :
  Pre.laws c -> definition_domain c (Phi b u) ->
  version_point c (Initial u) = Some q -> version_point c (Phi b u) <> Some q.
Proof.
  intros Hlaw Hphi Hentry Hpoint.
  destruct (parameter_edge_listed Hlaw (phi_needed_nodes c Hlaw Hphi)) as [He Hi].
  rewrite version_point_equation in Hentry, Hpoint.
  inversion Hpoint; subst q.
  eapply internal_target_not_entry; [exact Hlaw|exact He|exact Hi| |reflexivity].
  exact (nth_error_In _ _ Hentry).
Qed.

Local Lemma fresh_phi_disjoint {e b u q} :
  Pre.laws c -> definition_domain c (Fresh e u) -> definition_domain c (Phi b u) ->
  version_point c (Fresh e u) = Some q -> version_point c (Phi b u) <> Some q.
Proof.
  intros Hlaw [He Hcomputed] Hphi Hfresh Hpoint.
  destruct (parameter_edge_listed Hlaw (phi_needed_nodes c Hlaw Hphi)) as [Hparam Hinternal].
  rewrite version_point_equation in Hfresh, Hpoint.
  fold s in Hpoint.
  assert (Hsame : e = SsaPoints.parameter_edge s b).
  { eapply internal_target_unique; [exact Hlaw|exact He|exact Hparam| |exact Hinternal|].
    - exact (proj1 (Pre.real_internal c (Pre.kills c Hlaw) e u Hcomputed)).
    - congruence. }
  exact (proj2 (Pre.real_internal c (Pre.kills c Hlaw) e u Hcomputed) b Hsame).
Qed.

Local Lemma phi_points_unique {b b' u q} :
  Pre.laws c -> definition_domain c (Phi b u) -> definition_domain c (Phi b' u) ->
  version_point c (Phi b u) = Some q -> version_point c (Phi b' u) = Some q -> b = b'.
Proof.
  intros Hlaw Hb Hb' Hpoint Hpoint'.
  pose proof (Pre.point_laws c (Pre.graphs c Hlaw)) as Hpoints.
  fold s in Hpoints.
  pose proof (phi_needed_nodes c Hlaw Hb) as Hbn.
  pose proof (phi_needed_nodes c Hlaw Hb') as Hb'n.
  pose proof (chain_target _ (points_ordered Hpoints b Hbn)
    (nth_error_In _ _ (parameter_edge_first Hpoints b Hbn))) as Htarget.
  pose proof (chain_target _ (points_ordered Hpoints b' Hb'n)
    (nth_error_In _ _ (parameter_edge_first Hpoints b' Hb'n))) as Htarget'.
  rewrite version_point_equation in Hpoint, Hpoint'.
  fold s in Hpoint, Hpoint'.
  rewrite <- (points_owner Hpoints b _ Hbn (tail_member _ _ Htarget)).
  assert (Heq : Graph.target (live_graph (SsaPoints.point_model s))
    (SsaPoints.parameter_edge s b) =
    Graph.target (live_graph (SsaPoints.point_model s)) (SsaPoints.parameter_edge s b')).
  { change (Graph.target (Pre.pg c) (SsaPoints.parameter_edge s b) =
      Graph.target (Pre.pg c) (SsaPoints.parameter_edge s b')); congruence. }
  rewrite Heq.
  exact (points_owner Hpoints b' _ Hb'n (tail_member _ _ Htarget')).
Qed.

(** Matching eligible definitions at the same instruction point have the same origin identity. *)
Theorem definition_points_unique :
  Pre.laws c ->
  forall d d' q, definition_domain c d -> definition_domain c d' ->
    version_expr d = version_expr d' ->
    version_point c d = Some q -> version_point c d' = Some q -> d = d'.
Proof.
  intros Hlaw d d' q Hd Hd' Hexpr Hpoint Hpoint'.
  destruct d as [u|u|e u|b u], d' as [v|v|e' v|b' v];
    cbn [version_expr] in Hexpr; subst v;
    try (rewrite version_point_equation in Hpoint; discriminate);
    try (rewrite version_point_equation in Hpoint'; discriminate); try reflexivity.
  - exfalso; exact (initial_fresh_disjoint Hlaw Hd' Hpoint Hpoint').
  - exfalso; exact (initial_phi_disjoint Hlaw Hd' Hpoint Hpoint').
  - exfalso; exact (initial_fresh_disjoint Hlaw Hd Hpoint' Hpoint).
  - f_equal; destruct Hd as [He Hcomputed], Hd' as [He' Hcomputed'].
    eapply internal_target_unique; [exact Hlaw|exact He|exact He'| | |].
    + exact (proj1 (Pre.real_internal c (Pre.kills c Hlaw) e u Hcomputed)).
    + exact (proj1 (Pre.real_internal c (Pre.kills c Hlaw) e' u Hcomputed')).
    + rewrite version_point_equation in Hpoint, Hpoint'; congruence.
  - exfalso; exact (fresh_phi_disjoint Hlaw Hd Hd' Hpoint Hpoint').
  - exfalso; exact (initial_phi_disjoint Hlaw Hd Hpoint' Hpoint).
  - exfalso; exact (fresh_phi_disjoint Hlaw Hd' Hd Hpoint' Hpoint).
  - f_equal; eapply phi_points_unique; eassumption.
Qed.

End PointDomains.

Section DefinitionIndex.
Context {B BE N E V K G C U : Type}.
Variable c : Pre.ctx B BE N E V K G C U.

Definition occurrence_pairs_c :=
  let* es := fw_edges_c (Pre.point_cfg c) in
  fw_flat_map_c (fun e =>
    Cost.step ;;
    let* instance := Pre.recomputed_c (Pre.input c) e in
    match instance with
    | None => Cost.ret []
    | Some u =>
      Cost.step ;;
      let* eligible := Pre.pure_c (Pre.input c) u in
      if eligible then
        Cost.step ;;
        let* n := Graph.source_c (Pre.pg c) e in
        Cost.step ;;
        let* b := SsaPoints.block_of_point_c (Pre.points (Pre.input c)) n in
        Cost.ret [(u, b)]
      else Cost.ret []
    end) es.

Definition home_pairs_c family :=
  fw_flat_map_c (fun u =>
    Cost.step ;;
    let* xs := Pre.operands_c (Pre.input c) u in
    map_c (fun x =>
      Cost.step ;;
      let* b := Ssa.home_c (Pre.ssa (Pre.input c)) x in Cost.ret (u, b)) xs) family.

Definition entry_pairs_c (family : list U) :=
  fw_flat_map_c (fun u =>
    map_c (fun b => Cost.ret (u, b)) (Graph.entries (Pre.bg c))) family.

(** Definition preparation visits the program and the family once
    before any per-expression query. *)
Definition definition_index_c family :=
  let* entries := entry_pairs_c family in
  let* occurrences := occurrence_pairs_c in
  let* homes := home_pairs_c family in
  let* suffix := app_c occurrences homes in
  let* pairs := app_c entries suffix in
  Index.group_by_c (Pre.eu (Pre.keys c)) (fun pair => Cost.ret (fst pair)) pairs.
Definition definition_index family := Cost.value (definition_index_c family).

Definition defs_c (index : Index.t U (U * B)) u :=
  let* pairs := Index.find_c (Pre.eu (Pre.keys c)) u index in
  map_c (fun pair => Cost.ret (snd pair)) pairs.
Definition defs index u := Cost.value (defs_c index u).

(* Reference occurrence lists specify multiplicity and order and are never called by the core. *)
Definition occurrence_pairs :=
  flat_map (fun e =>
    match Pre.recomputed c e with
    | None => []
    | Some u =>
      if Pre.pure c u then
        [(u, SsaPoints.block_of_point (Pre.points (Pre.input c)) (Graph.source (Pre.pg c) e))]
      else []
    end) (Cfg.edges (Pre.point_cfg c)).

Definition home_pairs family :=
  flat_map (fun u => map (fun x => (u, Ssa.home (Pre.ssa (Pre.input c)) x))
    (Pre.operands c u)) family.

Definition entry_pairs (family : list U) :=
  flat_map (fun u => map (fun b => (u, b)) (Graph.entries (Pre.bg c))) family.

Definition definition_pairs family :=
  entry_pairs family ++ occurrence_pairs ++ home_pairs family.

(** Prepared occurrence seeds retain actual source-block callbacks
    and pure recomputation identity. *)
Theorem occurrence_pairs_value : Cost.value occurrence_pairs_c = occurrence_pairs.
Proof.
  unfold occurrence_pairs_c, occurrence_pairs.
  rewrite Cost.value_bind, fw_edges_value, fw_flat_map_value.
  induction (Cfg.edges (Pre.point_cfg c)) as [|e rest IH]; [reflexivity|].
  cbn [flat_map]; rewrite IH; rewrite !Cost.value_bind.
  fold (Pre.recomputed c e); destruct (Pre.recomputed c e) as [u|]; [|reflexivity].
  rewrite !Cost.value_bind; fold (Pre.pure c u); destruct (Pre.pure c u);
    autorewrite with galois_cost; reflexivity.
Qed.

(** Home preparation retains every ordered operand occurrence and its actual home-reader work. *)
Theorem home_pairs_value family : Cost.value (home_pairs_c family) = home_pairs family.
Proof.
  unfold home_pairs_c, home_pairs; rewrite fw_flat_map_value.
  induction family as [|u rest IH]; [reflexivity|].
  cbn [flat_map]; rewrite IH, !Cost.value_bind, value_map_c.
  f_equal; apply map_ext; intro x; autorewrite with galois_cost; reflexivity.
Qed.

(** Every family occurrence contributes each entry occurrence in the supplied order. *)
Theorem entry_pairs_value family : Cost.value (entry_pairs_c family) = entry_pairs family.
Proof.
  unfold entry_pairs_c, entry_pairs; rewrite fw_flat_map_value.
  induction family as [|u rest IH]; [reflexivity|].
  cbn [flat_map]; rewrite IH, value_map_c; reflexivity.
Qed.

(** The index is exactly stable grouping of the specified entry, occurrence and home seeds. *)
Theorem definition_index_equation family :
  definition_index family =
    Index.group_by (Pre.eu (Pre.keys c)) fst (definition_pairs family).
Proof.
  unfold definition_index, definition_index_c; rewrite !Cost.value_bind.
  rewrite entry_pairs_value, occurrence_pairs_value, home_pairs_value.
  rewrite !value_app_c, Index.group_by_c_value; reflexivity.
Qed.

(** Querying definitions uses only one prepared bucket and preserves its duplicate seed values. *)
Theorem defs_equation family u :
  defs (definition_index family) u =
    map snd (filter (fun pair => eqb (Pre.eu (Pre.keys c)) (fst pair) u)
      (definition_pairs family)).
Proof.
  unfold defs, defs_c; rewrite Cost.value_bind, value_map_c.
  fold (Index.find (Pre.eu (Pre.keys c)) u (definition_index family)).
  rewrite definition_index_equation, Index.find_group_by; reflexivity.
Qed.

(** Canonical definition indexes are constructed without assuming any client laws. *)
Theorem definition_index_wf family :
  Map.wf (Pre.eu (Pre.keys c)) (definition_index family).
Proof.
  rewrite definition_index_equation; apply Index.wf_group_by.
Qed.

Local Lemma occurrence_pairs_member u b :
  In (u, b) occurrence_pairs <->
    exists e, In e (Cfg.edges (Pre.point_cfg c)) /\ Pre.recomputed c e = Some u /\
      Pre.pure c u = true /\
      SsaPoints.block_of_point (Pre.points (Pre.input c)) (Graph.source (Pre.pg c) e) = b.
Proof.
  unfold occurrence_pairs; rewrite in_flat_map; split.
  - intros [e [He Hin]]; destruct (Pre.recomputed c e) as [v|] eqn:Hcomputed;
      [|contradiction].
    destruct (Pre.pure c v) eqn:Hpure; [|contradiction].
    destruct Hin as [Heq|[]]; inversion Heq; subst v b; exists e; auto.
  - intros [e [He [Hcomputed [Hpure Hblock]]]].
    exists e; split; [exact He|]; rewrite Hcomputed, Hpure, Hblock; now left.
Qed.

(** For a supplied family member, prepared seeds have exactly
    the legacy definition-block meaning. *)
Theorem definition_pairs_spec family u :
  In u family ->
  forall b, In (u, b) (definition_pairs family) <-> definition_block c u b.
Proof.
  intros Hu b; unfold definition_pairs; rewrite !in_app_iff, occurrence_pairs_member.
  unfold entry_pairs, home_pairs; rewrite !in_flat_map; split.
  - intros [[v [Hv Hin]]|[Hreal|[v [Hv Hin]]]].
    + apply in_map_iff in Hin; destruct Hin as [entry [Heq Hentry]].
      inversion Heq; subst v entry; apply definition_entry; exact Hentry.
    + destruct Hreal as [e [He [Hcomputed [Hpure <-]]]].
      apply definition_occurrence; assumption.
    + apply in_map_iff in Hin; destruct Hin as [x [Heq Hoperand]].
      inversion Heq; subst v b; apply definition_operand; exact Hoperand.
  - intro Hdefinition; destruct Hdefinition as [b Hentry|e He Hcomputed Hpure|x Hoperand].
    + left; exists u; split; [exact Hu|].
      apply in_map_iff; exists b; auto.
    + right; left; exists e; auto.
    + right; right; exists u; split; [exact Hu|].
      apply in_map_iff; exists x; auto.
Qed.

Local Lemma bucket_member :
  Pre.laws c ->
  forall (pairs : list (U * B)) u b,
    In b (map snd (filter (fun pair => eqb (Pre.eu (Pre.keys c)) (fst pair) u) pairs)) <->
      In (u, b) pairs.
Proof.
  intros Hlaw pairs u b; rewrite in_map_iff; split.
  - intros [[v target] [Htarget Hin]]; cbn [snd] in Htarget; subst target.
    apply filter_In in Hin; destruct Hin as [Hin Hkey].
    apply (eqb_true_iff _ (Pre.eu_laws c (Pre.graphs c Hlaw))) in Hkey.
    cbn [fst] in Hkey; subst v; exact Hin.
  - intro Hin; exists (u, b); split; [reflexivity|].
    apply filter_In; split; [exact Hin|apply eqb_refl].
Qed.

(** Definition queries agree with the fixed source relation
    through public stable-index contracts. *)
Theorem defs_exact family u :
  Pre.laws c -> In u family ->
  forall b, In b (defs (definition_index family) u) <-> definition_block c u b.
Proof.
  intros Hlaw Hu b; rewrite defs_equation, bucket_member by exact Hlaw.
  apply definition_pairs_spec; exact Hu.
Qed.

End DefinitionIndex.

Section FrontierRows.
Context {B BE N E V K G C U : Type}.
Variable c : Pre.ctx B BE N E V K G C U.

(** Every listed source block has an ID in the supplied ready preparation. *)
Lemma block_node_id :
  Pre.laws c ->
  forall b, In b (Graph.nodes (Pre.bg c)) ->
    exists i, Prepared.id_of (Pre.blocks c) b = Some i.
Proof.
  intros Hlaw b Hb.
  apply (Prepared.ids_domain (Pre.blocks c)
    (proj2 (proj2 (Pre.blocks_ready c (Pre.graphs c Hlaw))))).
  rewrite Pre.blocks_source by exact (Pre.graphs c Hlaw); exact Hb.
Qed.

Definition named_mem_c ids b :=
  let* i := Prepared.id_of_c (Pre.blocks c) b in
  match i with
  | None => Cost.ret false
  | Some id => FinSet.mem_c positive_encoding id ids
  end.
Definition named_mem ids b := Cost.value (named_mem_c ids b).

(** Named membership rejects absent names and otherwise queries the same prepared ID. *)
Theorem named_mem_equation ids b :
  named_mem ids b =
    match Prepared.id_of (Pre.blocks c) b with
    | None => false
    | Some id => FinSet.mem positive_encoding id ids
    end.
Proof.
  unfold named_mem, named_mem_c; rewrite Cost.value_bind.
  fold (Prepared.id_of (Pre.blocks c) b); destruct (Prepared.id_of (Pre.blocks c) b);
    reflexivity.
Qed.

(** Static frontier rows use the public exact closure fallback
    and retain every preparation charge. *)
Definition frontier_row_c d :=
  let* ids := FrontierIdf.idf_c (Pre.blocks c) (Pre.dom c) [d] in
  filter_c (named_mem_c ids) (Graph.nodes (Pre.bg c)).
Definition frontier_row d := Cost.value (frontier_row_c d).

(** Singleton IDF rows are observed through named membership on the supplied block inventory. *)
Theorem frontier_row_equation d :
  frontier_row d =
    filter (named_mem (FrontierIdf.idf (Pre.blocks c) (Pre.dom c) [d]))
      (Graph.nodes (Pre.bg c)).
Proof.
  unfold frontier_row, frontier_row_c; rewrite Cost.value_bind, value_filter_c; reflexivity.
Qed.

Local Lemma idf_target_listed {d b} :
  Pre.laws c -> in_idf (Pre.bg c) [d] b -> In b (Graph.nodes (Pre.bg c)).
Proof.
  intros Hlaw Hclosure; destruct Hclosure; eapply frontier_target_listed; eassumption.
Qed.

Local Lemma idf_source_listed {d b} :
  Pre.laws c -> in_idf (Pre.bg c) [d] b -> In d (Graph.nodes (Pre.bg c)).
Proof.
  intros Hlaw Hclosure.
  induction Hclosure as [seed target Hseed Hdf|source target Hclosure IH Hdf];
    [|exact IH].
  destruct Hseed as [<-|[]].
  destruct Hdf as [e [Hsource [Hedge [Htarget [Hdom Hnotstrict]]]]].
  apply (reachable_in_nodes _ _ (blocks_graph_wf (Pre.point_laws c (Pre.graphs c Hlaw)))).
  exact (DomCheck.dominator_reachable (Pre.bg c) d (Graph.source (Pre.bg c) e) Hsource Hdom).
Qed.

(** Every named row is exactly the ordinary nonreflexive singleton iterated dominance frontier. *)
Theorem frontier_row_exact d :
  Pre.laws c ->
  forall b, In b (frontier_row d) <-> in_idf (Pre.bg c) [d] b.
Proof.
  intros Hlaw b; rewrite frontier_row_equation, filter_In; split.
  - intros [Hb Hmem]; destruct (block_node_id Hlaw b Hb) as [i Hi].
    rewrite named_mem_equation, Hi in Hmem.
    pose proof (FrontierIdf.idf_exact (Pre.blocks c) (Pre.dom c) [d] b i
      (Pre.blocks_ready c (Pre.graphs c Hlaw)) (Pre.tree_exact c (Pre.graphs c Hlaw)) Hi)
      as Hspec.
    rewrite (Pre.blocks_source c (Pre.graphs c Hlaw)) in Hspec.
    exact (proj1 Hspec Hmem).
  - intro Hclosure.
    pose proof (idf_target_listed Hlaw Hclosure) as Hb.
    destruct (block_node_id Hlaw b Hb) as [i Hi].
    split; [exact Hb|]; rewrite named_mem_equation, Hi.
    pose proof (FrontierIdf.idf_exact (Pre.blocks c) (Pre.dom c) [d] b i
      (Pre.blocks_ready c (Pre.graphs c Hlaw)) (Pre.tree_exact c (Pre.graphs c Hlaw)) Hi)
      as Hspec.
    rewrite (Pre.blocks_source c (Pre.graphs c Hlaw)) in Hspec.
    exact (proj2 Hspec Hclosure).
Qed.

Definition frontier_rows_c :=
  let* pairs := map_c (fun d =>
    let* row := frontier_row_c d in Cost.ret (d, row)) (Graph.nodes (Pre.bg c)) in
  Map.of_list_c (Pre.eb (Pre.keys c)) pairs.
Definition frontier_rows := Cost.value frontier_rows_c.
Definition cached_row_c (rows : Index.t B B) d := Index.find_c (Pre.eb (Pre.keys c)) d rows.
Definition cached_row rows d := Cost.value (cached_row_c rows d).

(** Static IDF preparation constructs one row for each listed source block. *)
Theorem frontier_rows_equation :
  frontier_rows = Map.of_list (Pre.eb (Pre.keys c))
    (map (fun d => (d, frontier_row d)) (Graph.nodes (Pre.bg c))).
Proof.
  unfold frontier_rows, frontier_rows_c; rewrite Cost.value_bind, value_map_c.
  assert (Hpairs : map (fun d =>
    Cost.value (let* row := frontier_row_c d in Cost.ret (d, row))) (Graph.nodes (Pre.bg c)) =
    map (fun d => (d, frontier_row d)) (Graph.nodes (Pre.bg c))).
  { apply map_ext; intro d; rewrite Cost.value_bind, Cost.value_ret; reflexivity. }
  rewrite Hpairs; reflexivity.
Qed.

(** Cached queries are exact even for absent source blocks, whose frontier must be empty. *)
Theorem cached_row_exact :
  Pre.laws c ->
  forall d b, In b (cached_row frontier_rows d) <-> in_idf (Pre.bg c) [d] b.
Proof.
  intros Hlaw d b; unfold cached_row, cached_row_c.
  fold (Index.find (Pre.eb (Pre.keys c)) d frontier_rows).
  rewrite Index.find_equation, frontier_rows_equation.
  pose proof (Pre.eb_laws c (Pre.graphs c Hlaw)) as HE.
  destruct (in_dec (eqb_dec _ HE) d (Graph.nodes (Pre.bg c))) as [Hd|Hd].
  - assert (Hnodup : NoDup (map fst
      (map (fun d => (d, frontier_row d)) (Graph.nodes (Pre.bg c))))).
    { rewrite map_map; cbn [fst]; rewrite map_id.
      exact (nodes_nodup (blocks_graph_wf (Pre.point_laws c (Pre.graphs c Hlaw)))). }
    rewrite (Pre.assignment_member _ HE _ Hnodup d (frontier_row d)).
    + apply frontier_row_exact; exact Hlaw.
    + apply in_map_iff; exists d; auto.
  - rewrite (Pre.assignment_frame _ HE).
    + cbn [In]; split; [contradiction|].
      intro Hclosure; exfalso; apply Hd; exact (idf_source_listed Hlaw Hclosure).
    + rewrite map_map; cbn [fst]; rewrite map_id; exact Hd.
Qed.

End FrontierRows.

Section Parameters.
Context {B BE N E V K G C U : Type}.
Variable c : Pre.ctx B BE N E V K G C U.

Definition parameter_pairs_c :=
  let* entries := FinSet.of_list_c (Pre.eb (Pre.keys c)) (Graph.entries (Pre.bg c)) in
  fw_flat_map_c (fun b =>
    let* entry := FinSet.mem_c (Pre.eb (Pre.keys c)) b entries in
    if entry then Cost.ret [] else
      Cost.step ;;
      let* xs := SsaPoints.block_params_c (Pre.points (Pre.input c)) b in
      map_c (fun x => Cost.ret (x, b)) xs) (Graph.nodes (Pre.bg c)).
Definition parameter_pairs :=
  flat_map (fun b =>
    if FinSet.mem (Pre.eb (Pre.keys c)) b
      (FinSet.of_list (Pre.eb (Pre.keys c)) (Graph.entries (Pre.bg c)))
    then [] else map (fun x => (x, b)) (SsaPoints.block_params (Pre.points (Pre.input c)) b))
    (Graph.nodes (Pre.bg c)).
Definition parameter_index_c :=
  let* pairs := parameter_pairs_c in
  Index.group_by_c (Pre.ev (Pre.keys c)) (fun pair => Cost.ret (fst pair)) pairs.
Definition parameter_index := Cost.value parameter_index_c.
Definition parameter_blocks_c (index : Index.t V (V * B)) x :=
  PreFamily.bucket_c (Pre.ev (Pre.keys c)) index x.
Definition parameter_blocks (index : Index.t V (V * B)) x :=
  PreFamily.bucket (Pre.ev (Pre.keys c)) index x.

(** Parameter preparation visits each nonentry block once and keeps every parameter occurrence. *)
Theorem parameter_pairs_value : Cost.value parameter_pairs_c = parameter_pairs.
Proof.
  unfold parameter_pairs_c, parameter_pairs; rewrite Cost.value_bind, fw_flat_map_value.
  fold (FinSet.of_list (Pre.eb (Pre.keys c)) (Graph.entries (Pre.bg c))).
  induction (Graph.nodes (Pre.bg c)) as [|b rest IH]; [reflexivity|].
  cbn [flat_map]; rewrite IH, Cost.value_bind.
  fold (FinSet.mem (Pre.eb (Pre.keys c)) b
    (FinSet.of_list (Pre.eb (Pre.keys c)) (Graph.entries (Pre.bg c)))).
  destruct (FinSet.mem (Pre.eb (Pre.keys c)) b
    (FinSet.of_list (Pre.eb (Pre.keys c)) (Graph.entries (Pre.bg c))));
    autorewrite with galois_cost; reflexivity.
Qed.

(** The parameter index is stable grouping by the original SSA value identity. *)
Theorem parameter_index_equation :
  parameter_index = Index.group_by (Pre.ev (Pre.keys c)) fst parameter_pairs.
Proof.
  unfold parameter_index, parameter_index_c.
  rewrite Cost.value_bind, parameter_pairs_value, Index.group_by_c_value; reflexivity.
Qed.

Local Lemma parameter_pairs_member :
  Pre.laws c ->
  forall x b, In (x, b) parameter_pairs <->
    In b (Graph.nodes (Pre.bg c)) /\ ~ In b (Graph.entries (Pre.bg c)) /\
      In x (SsaPoints.block_params (Pre.points (Pre.input c)) b).
Proof.
  intros Hlaw x b; unfold parameter_pairs; rewrite in_flat_map; split.
  - intros [block [Hb Hin]].
    destruct (FinSet.mem (Pre.eb (Pre.keys c)) block
      (FinSet.of_list (Pre.eb (Pre.keys c)) (Graph.entries (Pre.bg c)))) eqn:Hentry;
      [contradiction|].
    apply in_map_iff in Hin; destruct Hin as [v [Heq Hparam]]; inversion Heq; subst v block.
    split; [exact Hb|]; split; [|exact Hparam].
    intro Hin; rewrite FinSet.mem_of_list in Hentry.
    assert (Hmem : existsb (eqb (Pre.eb (Pre.keys c)) b) (Graph.entries (Pre.bg c)) = true).
    { apply existsb_exists; exists b; split; [exact Hin|apply eqb_refl]. }
    congruence.
  - intros [Hb [Hentry Hparam]]; exists b; split; [exact Hb|].
    destruct (FinSet.mem (Pre.eb (Pre.keys c)) b
      (FinSet.of_list (Pre.eb (Pre.keys c)) (Graph.entries (Pre.bg c)))) eqn:Hmem.
    + exfalso; apply Hentry; rewrite FinSet.mem_of_list in Hmem.
      apply existsb_exists in Hmem; destruct Hmem as [a [Ha Hkey]].
      apply (eqb_true_iff _ (Pre.eb_laws c (Pre.graphs c Hlaw))) in Hkey; subst a; exact Ha.
    + apply in_map_iff; exists x; auto.
Qed.

(** Cached parameter blocks are precisely the listed nonentry owners of that value parameter. *)
Theorem parameter_blocks_exact :
  Pre.laws c ->
  forall x b, In b (parameter_blocks parameter_index x) <->
    In b (Graph.nodes (Pre.bg c)) /\ ~ In b (Graph.entries (Pre.bg c)) /\
      In x (SsaPoints.block_params (Pre.points (Pre.input c)) b).
Proof.
  intros Hlaw x b; unfold parameter_blocks; rewrite parameter_index_equation.
  rewrite (PreFamily.bucket_group_member _ (Pre.ev_laws c (Pre.graphs c Hlaw))).
  apply parameter_pairs_member; exact Hlaw.
Qed.

Definition direct_pairs_c parameters family :=
  fw_flat_map_c (fun u =>
    Cost.step ;;
    let* xs := Pre.operands_c (Pre.input c) u in
    fw_flat_map_c (fun x =>
      let* bs := parameter_blocks_c parameters x in
      map_c (fun b => Cost.ret (u, b)) bs) xs) family.
Definition direct_pairs parameters family :=
  flat_map (fun u => flat_map (fun x =>
    map (fun b => (u, b)) (parameter_blocks parameters x)) (Pre.operands c u)) family.

(** Direct phi seeds query the shared parameter index for each ordered expression operand. *)
Theorem direct_pairs_value parameters family :
  Cost.value (direct_pairs_c parameters family) = direct_pairs parameters family.
Proof.
  unfold direct_pairs_c, direct_pairs; rewrite fw_flat_map_value.
  induction family as [|u rest IH]; [reflexivity|].
  cbn [flat_map]; rewrite IH, !Cost.value_bind, fw_flat_map_value.
  fold (Pre.operands c u).
  f_equal; induction (Pre.operands c u) as [|x xs IHxs]; [reflexivity|].
  cbn [flat_map]; rewrite IHxs, Cost.value_bind, value_map_c; reflexivity.
Qed.

(** Direct seeds retain the legacy nonentry parameter clause for every family occurrence. *)
Theorem direct_pairs_exact family :
  Pre.laws c ->
  forall u b, In (u, b) (direct_pairs parameter_index family) <->
    In u family /\ In b (Graph.nodes (Pre.bg c)) /\ ~ In b (Graph.entries (Pre.bg c)) /\
      exists x, In x (Pre.operands c u) /\
        In x (SsaPoints.block_params (Pre.points (Pre.input c)) b).
Proof.
  intros Hlaw u b; unfold direct_pairs; rewrite in_flat_map; split.
  - intros [v [Hv Hin]]; apply in_flat_map in Hin; destruct Hin as [x [Hx Hin]].
    apply in_map_iff in Hin; destruct Hin as [block [Heq Hb]]; inversion Heq; subst v block.
    apply (parameter_blocks_exact Hlaw) in Hb; destruct Hb as [Hb [Hentry Hparam]].
    split; [exact Hv|]; split; [exact Hb|]; split; [exact Hentry|exists x; auto].
  - intros [Hu [Hb [Hentry [x [Hx Hparam]]]]].
    exists u; split; [exact Hu|]; apply in_flat_map; exists x; split; [exact Hx|].
    apply in_map_iff; exists b; split; [reflexivity|].
    apply (parameter_blocks_exact Hlaw); auto.
Qed.

End Parameters.

Section PhiClosure.
Context {B BE N E V K G C U : Type}.
Variable c : Pre.ctx B BE N E V K G C U.

Definition product_encoding := pair_encoding (Pre.eu (Pre.keys c)) (Pre.eb (Pre.keys c)).

Record phi_cache := PhiCache {
  frontier_index : Index.t B B;
  parameter_index_of : Index.t V (V * B);
  definition_index_of : Index.t U (U * B)
}.

Definition phi_cache_c family :=
  let* rows := frontier_rows_c c in
  let* parameters := parameter_index_c c in
  let* definitions := definition_index_c c family in
  Cost.ret (PhiCache rows parameters definitions).
Definition cache_for family := Cost.value (phi_cache_c family).

(** The product closure shares one frontier, parameter and source-definition index. *)
Theorem cache_for_equation family :
  cache_for family = PhiCache (frontier_rows c) (parameter_index c) (definition_index c family).
Proof.
  unfold cache_for, phi_cache_c; rewrite !Cost.value_bind, Cost.value_ret; reflexivity.
Qed.

Definition product_nodes_c family :=
  let* nodes := fw_flat_map_c (fun u =>
    map_c (fun b => Cost.ret (u, b)) (Graph.nodes (Pre.bg c))) family in
  PreFamily.canonical_c product_encoding nodes.
Definition product_nodes family := Cost.value (product_nodes_c family).

(** Product nodes use exact expression/block identities and canonicalize duplicate input entries. *)
Theorem product_nodes_equation family :
  product_nodes family = PreFamily.canonical product_encoding
    (list_prod family (Graph.nodes (Pre.bg c))).
Proof.
  unfold product_nodes, product_nodes_c; rewrite Cost.value_bind, fw_flat_map_value.
  assert (Hpairs : flat_map (fun u =>
    Cost.value (map_c (fun b => Cost.ret (u, b)) (Graph.nodes (Pre.bg c)))) family =
    list_prod family (Graph.nodes (Pre.bg c))).
  { induction family as [|u rest IH]; [reflexivity|].
    cbn [flat_map list_prod]; rewrite value_map_c, IH; reflexivity. }
  rewrite Hpairs; reflexivity.
Qed.

Definition phi_roots_c cache family :=
  let* direct := direct_pairs_c c (parameter_index_of cache) family in
  let* frontiers := fw_flat_map_c (fun u =>
    let* ds := defs_c c (definition_index_of cache) u in
    fw_flat_map_c (fun d =>
      let* bs := cached_row_c c (frontier_index cache) d in
      map_c (fun b => Cost.ret (u, b)) bs) ds) family in
  app_c direct frontiers.
Definition phi_roots cache family :=
  direct_pairs c (parameter_index_of cache) family ++
    flat_map (fun u => flat_map (fun d => map (fun b => (u, b))
      (cached_row c (frontier_index cache) d))
      (defs c (definition_index_of cache) u)) family.

(** Product roots include both direct parameter sites and frontier closure of definition seeds. *)
Theorem phi_roots_value cache family :
  Cost.value (phi_roots_c cache family) = phi_roots cache family.
Proof.
  unfold phi_roots_c, phi_roots; rewrite !Cost.value_bind, value_app_c, direct_pairs_value.
  rewrite fw_flat_map_value; f_equal.
  induction family as [|u rest IH]; [reflexivity|].
  cbn [flat_map]; rewrite IH, Cost.value_bind, fw_flat_map_value.
  fold (defs c (definition_index_of cache) u).
  f_equal; induction (defs c (definition_index_of cache) u) as [|d ds_tail IHds]; [reflexivity|].
  cbn [flat_map]; rewrite IHds, Cost.value_bind, value_map_c; reflexivity.
Qed.

Definition incoming b := Cost.value (Prepared.incoming_c (Pre.blocks c) b).

Definition phi_next_c cache (key : U * B) :=
  let '(u, b) := key in
  let* same := cached_row_c c (frontier_index cache) b in
  let* ordinary := map_c (fun target => Cost.ret (u, target)) same in
  let* edges := Prepared.incoming_c (Pre.blocks c) b in
  let* translated := fw_flat_map_c (fun be =>
    Cost.step ;;
    let* value := Pre.translate_c (Pre.input c) be u in
    match value with
    | None => Cost.ret []
    | Some v =>
      Cost.step ;;
      let* source := Graph.source_c (Pre.bg c) be in
      let* bs := cached_row_c c (frontier_index cache) source in
      map_c (fun target => Cost.ret (v, target)) bs
    end) edges in
  app_c ordinary translated.
Definition phi_next cache (key : U * B) :=
  let '(u, b) := key in
  map (fun target => (u, target)) (cached_row c (frontier_index cache) b) ++
    flat_map (fun be =>
      match Pre.translate c be u with
      | None => []
      | Some v => map (fun target => (v, target))
          (cached_row c (frontier_index cache) (Graph.source (Pre.bg c) be))
      end) (incoming b).

(** Product edges include same-expression propagation
    and each incoming edge's translated frontier. *)
Theorem phi_next_value cache key : Cost.value (phi_next_c cache key) = phi_next cache key.
Proof.
  destruct key as [u b]; unfold phi_next_c, phi_next.
  rewrite !Cost.value_bind, value_map_c, value_app_c, fw_flat_map_value.
  fold (incoming b); f_equal.
  induction (incoming b) as [|be rest IH]; [reflexivity|].
  cbn [flat_map]; rewrite IH, !Cost.value_bind.
  fold (Pre.translate c be u); destruct (Pre.translate c be u) as [v|]; [|reflexivity].
  autorewrite with galois_cost; reflexivity.
Qed.

Definition phi_graph_c cache family :=
  let* nodes := product_nodes_c family in
  let* roots := phi_roots_c cache family in
  Cost.ret (PreFamily.arc_graph product_encoding nodes roots (phi_next_c cache)).
Definition phi_graph cache family := Cost.value (phi_graph_c cache family).

(** The factored placement closure uses the shared charged arc presentation. *)
Theorem phi_graph_equation cache family :
  phi_graph cache family =
    PreFamily.arc_graph product_encoding (product_nodes family) (phi_roots cache family)
      (phi_next_c cache).
Proof.
  unfold phi_graph, phi_graph_c; rewrite !Cost.value_bind, phi_roots_value, Cost.value_ret.
  reflexivity.
Qed.

Definition phi_sites_for_c family :=
  let* cache := phi_cache_c family in
  let* graph := phi_graph_c cache family in
  let* reached := PreFamily.reachable_nodes_c product_encoding graph in
  let* keys := map_c (fun key => Cost.ret (snd key, fst key)) reached in
  FinSet.of_list_c (phi_encoding c) keys.
Definition phi_sites_for family := Cost.value (phi_sites_for_c family).

Local Lemma product_encoding_laws :
  Pre.laws c -> encoding_laws product_encoding.
Proof.
  intro Hlaw; apply pair_encoding_laws.
  - exact (Pre.eu_laws c (Pre.graphs c Hlaw)).
  - exact (Pre.eb_laws c (Pre.graphs c Hlaw)).
Qed.

(** Product membership retains both family identity and the original listed block domain. *)
Theorem product_nodes_member family :
  Pre.laws c ->
  forall u b, In (u, b) (product_nodes family) <->
    In u family /\ In b (Graph.nodes (Pre.bg c)).
Proof.
  intros Hlaw u b; rewrite product_nodes_equation.
  rewrite (PreFamily.canonical_member _ (product_encoding_laws Hlaw)).
  apply in_prod_iff.
Qed.

Definition root_condition family u b : Prop :=
  In u family /\
    ((In b (Graph.nodes (Pre.bg c)) /\ ~ In b (Graph.entries (Pre.bg c)) /\
       exists x, In x (Pre.operands c u) /\
         In x (SsaPoints.block_params (Pre.points (Pre.input c)) b)) \/
     exists d, definition_block c u d /\ in_idf (Pre.bg c) [d] b).

(** Product roots have exactly the direct-parameter and definition-frontier meanings. *)
Theorem phi_roots_exact family :
  Pre.laws c ->
  forall u b, In (u, b) (phi_roots (cache_for family) family) <-> root_condition family u b.
Proof.
  intros Hlaw u b; unfold phi_roots; rewrite cache_for_equation.
  cbn [parameter_index_of definition_index_of frontier_index].
  rewrite in_app_iff, direct_pairs_exact by exact Hlaw.
  rewrite in_flat_map; split.
  - intros [[Hu Hdirect]|[v [Hv Hin]]]; [split; [exact Hu|now left]|].
    apply in_flat_map in Hin; destruct Hin as [d [Hd Hin]].
    apply in_map_iff in Hin; destruct Hin as [target [Heq Hrow]].
    inversion Heq; subst v target; split; [exact Hv|right; exists d; split].
    + apply (defs_exact c family u Hlaw Hv); exact Hd.
    + apply (cached_row_exact c Hlaw); exact Hrow.
  - intros [Hu [Hdirect|[d [Hd Hrow]]]]; [left; auto|].
    right; exists u; split; [exact Hu|]; apply in_flat_map; exists d; split.
    + apply (defs_exact c family u Hlaw Hu); exact Hd.
    + apply in_map_iff; exists b; split; [reflexivity|].
      apply (cached_row_exact c Hlaw); exact Hrow.
Qed.

(** The prepared predecessor bucket retains exactly the listed incoming edge identities. *)
Lemma incoming_exact :
  Pre.laws c ->
  forall b, In b (Graph.nodes (Pre.bg c)) ->
  forall be, In be (incoming b) <->
    In be (Cfg.edges (Pre.block_cfg c)) /\ Graph.target (Pre.bg c) be = b.
Proof.
  intros Hlaw b Hb be.
  pose proof (proj2 (proj2 (Pre.blocks_ready c (Pre.graphs c Hlaw)))) as Hp.
  destruct (block_node_id c Hlaw b Hb) as [i Hi].
  unfold incoming; rewrite Prepared.incoming_equation, Hi, in_map_iff; split.
  - intros [[edge j] [Heq Hin]]; cbn [fst] in Heq; subst edge.
    apply (Prepared.pred_agrees _ Hp b i be j Hi) in Hin.
    rewrite (Pre.blocks_source c (Pre.graphs c Hlaw)) in Hin.
    destruct Hin as [Hs [He [Ht Hname]]]; split; [|exact Ht].
    apply Cfg.edges_spec; exists (Graph.source (Pre.bg c) be); auto.
  - intros [He Htarget]; apply Cfg.edges_spec in He; destruct He as [source [Hs He]].
    pose proof (out_source (blocks_graph_wf (Pre.point_laws c (Pre.graphs c Hlaw)))
      source be He) as Hsource.
    change (Graph.source (Pre.bg c) be = source) in Hsource.
    destruct (block_node_id c Hlaw source Hs) as [j Hj].
    exists (be, j); split; [reflexivity|].
    apply (Prepared.pred_agrees _ Hp b i be j Hi).
    rewrite (Pre.blocks_source c (Pre.graphs c Hlaw)), Hsource; auto.
Qed.

Definition transition (source target : U * B) : Prop :=
  let '(u, b) := source in
  let '(v, block) := target in
  (v = u /\ in_idf (Pre.bg c) [b] block) \/
  exists be, In be (Cfg.edges (Pre.block_cfg c)) /\ Graph.target (Pre.bg c) be = b /\
    Pre.translate c be u = Some v /\
    in_idf (Pre.bg c) [Graph.source (Pre.bg c) be] block.

(** Product successors preserve both same-expression IDF propagation
    and edge-specific translation. *)
Theorem phi_next_exact family :
  Pre.laws c ->
  forall u b v target, In b (Graph.nodes (Pre.bg c)) ->
    (In (v, target) (phi_next (cache_for family) (u, b)) <->
      transition (u, b) (v, target)).
Proof.
  intros Hlaw u b v target Hb; unfold phi_next, transition; rewrite cache_for_equation.
  cbn [frontier_index]; rewrite in_app_iff, in_map_iff; split.
  - intros [[block [Heq Hrow]]|Hin].
    + inversion Heq; subst v block; left; split; [reflexivity|].
      apply (cached_row_exact c Hlaw); exact Hrow.
    + apply in_flat_map in Hin; destruct Hin as [be [Hbe Hin]].
      destruct (Pre.translate c be u) as [value|] eqn:Htranslate; [|contradiction].
      apply in_map_iff in Hin; destruct Hin as [block [Heq Hrow]].
      inversion Heq; subst value block; right; exists be.
      apply (incoming_exact Hlaw b Hb) in Hbe; destruct Hbe as [Hbe Htarget].
      repeat split; try assumption; apply (cached_row_exact c Hlaw); exact Hrow.
  - intros [[-> Hrow]|[be [Hbe [Htarget [Htranslate Hrow]]]]].
    + left; exists target; split; [reflexivity|apply (cached_row_exact c Hlaw); exact Hrow].
    + right; apply in_flat_map; exists be; split.
      * apply (incoming_exact Hlaw b Hb); auto.
      * rewrite Htranslate; apply in_map_iff; exists target; split; [reflexivity|].
        apply (cached_row_exact c Hlaw); exact Hrow.
Qed.

Local Lemma phi_idf {u d target} :
  phi_needed c u d -> in_idf (Pre.bg c) [d] target -> phi_needed c u target.
Proof.
  intros Hphi Hclosure; induction Hclosure as [source target Hseed Hdf|source target Hprev IH Hdf].
  - destruct Hseed as [<-|[]]; eapply phi_iterate; eassumption.
  - eapply phi_iterate; eassumption.
Qed.

Local Lemma definition_idf {u d target} :
  PreFamily.in_family c u -> definition_block c u d ->
    in_idf (Pre.bg c) [d] target -> phi_needed c u target.
Proof.
  intros Hfamily Hdefinition Hclosure.
  induction Hclosure as [source target Hseed Hdf|source target Hprev IH Hdf].
  - destruct Hseed as [<-|[]]; eapply phi_seed; eassumption.
  - eapply phi_iterate; eassumption.
Qed.

Local Lemma translation_idf {u b be v target} :
  phi_needed c u b -> In be (Cfg.edges (Pre.block_cfg c)) ->
  Graph.target (Pre.bg c) be = b -> Pre.translate c be u = Some v ->
  in_idf (Pre.bg c) [Graph.source (Pre.bg c) be] target -> phi_needed c v target.
Proof.
  intros Hphi Hbe Htarget Htranslate Hclosure.
  induction Hclosure as [source target Hseed Hdf|source target Hprev IH Hdf].
  - destruct Hseed as [<-|[]]; eapply phi_translate; eassumption.
  - eapply phi_iterate; eassumption.
Qed.

Local Lemma root_sound family :
  (forall u, In u family <-> PreFamily.in_family c u) ->
  forall u b, root_condition family u b -> phi_needed c u b.
Proof.
  intros Hfamily u b [Hu [Hdirect|[d [Hd Hrow]]]]; apply Hfamily in Hu.
  - destruct Hdirect as [Hb [Hentry [x [Hx Hparam]]]]; eapply phi_parameter; eassumption.
  - eapply definition_idf; eassumption.
Qed.

Local Lemma transition_sound {u b v target} :
  phi_needed c u b -> transition (u, b) (v, target) -> phi_needed c v target.
Proof.
  intros Hphi [[-> Hrow]|[be [Hbe [Htarget [Htranslate Hrow]]]]].
  - eapply phi_idf; eassumption.
  - eapply translation_idf; eassumption.
Qed.

Local Lemma transition_closed family :
  Pre.laws c -> (forall u, In u family <-> PreFamily.in_family c u) ->
  forall source target, In source (product_nodes family) -> transition source target ->
    In target (product_nodes family).
Proof.
  intros Hlaw Hfamily [u b] [v target] Hsource Htransition.
  apply (product_nodes_member family Hlaw) in Hsource; destruct Hsource as [Hu Hb].
  apply (product_nodes_member family Hlaw).
  destruct Htransition as [[-> Hrow]|[be [Hbe [Htarget [Htranslate Hrow]]]]]; split.
  - exact Hu.
  - exact (idf_target_listed c Hlaw Hrow).
  - apply Hfamily; eapply Pre.family_translate.
    + apply Hfamily; exact Hu.
    + exact Hbe.
    + exact Htranslate.
  - exact (idf_target_listed c Hlaw Hrow).
Qed.

Local Lemma roots_closed family :
  Pre.laws c -> incl (phi_roots (cache_for family) family) (product_nodes family).
Proof.
  intros Hlaw [u b] Hroot; apply (phi_roots_exact family Hlaw) in Hroot.
  destruct Hroot as [Hu [[Hb _]|[d [_ Hrow]]]].
  - apply (product_nodes_member family Hlaw); auto.
  - apply (product_nodes_member family Hlaw); split; [exact Hu|].
    exact (idf_target_listed c Hlaw Hrow).
Qed.

(** The product graph is finite, closed and outgoing-unique on the supported expression family. *)
Theorem phi_graph_domain family :
  Pre.laws c -> (forall u, In u family <-> PreFamily.in_family c u) ->
  graph_wf (phi_graph (cache_for family) family) /\
    forall key, NoDup (Graph.out (phi_graph (cache_for family) family) key).
Proof.
  intros Hlaw Hfamily; rewrite phi_graph_equation.
  apply (PreFamily.arc_graph_ready_domain _ (product_encoding_laws Hlaw)).
  - rewrite product_nodes_equation; apply PreFamily.canonical_nodup.
  - apply roots_closed; exact Hlaw.
  - intros [u b] [v target] Hnode Hnext.
    pose proof Hnode as Hlisted; apply (product_nodes_member family Hlaw) in Hlisted.
    rewrite phi_next_value, (phi_next_exact family Hlaw u b v target (proj2 Hlisted)) in Hnext.
    eapply transition_closed; eassumption.
Qed.

Local Lemma phi_graph_sound family :
  Pre.laws c -> (forall u, In u family <-> PreFamily.in_family c u) ->
  forall u b, reachable (phi_graph (cache_for family) family) (u, b) -> phi_needed c u b.
Proof.
  intros Hlaw Hfamily u b Hreach; rewrite phi_graph_equation in Hreach.
  remember (u, b) as key eqn:Hkey; revert u b Hkey.
  induction Hreach as [key Hroot|[[source block] [value target]] Hreach IH Hout];
    intros u b Hkey.
  - subst key; apply (root_sound family Hfamily).
    apply (phi_roots_exact family Hlaw); exact Hroot.
  - rewrite PreFamily.arc_graph_source in IH, Hout.
    rewrite PreFamily.arc_graph_target in Hkey; cbn [fst snd] in IH, Hkey.
    inversion Hkey; subst u b.
    pose proof (IH source block eq_refl) as Hphi.
    apply (PreFamily.arc_graph_member _ (product_encoding_laws Hlaw) _) in Hout.
    destruct Hout as [_ Hnext]; rewrite phi_next_value in Hnext.
    apply (phi_next_exact family Hlaw source block value target
      (phi_needed_nodes c Hlaw Hphi)) in Hnext.
    exact (transition_sound Hphi Hnext).
Qed.

Local Lemma phi_graph_step family :
  Pre.laws c ->
  forall u b v target, In b (Graph.nodes (Pre.bg c)) ->
    reachable (phi_graph (cache_for family) family) (u, b) ->
    transition (u, b) (v, target) ->
    reachable (phi_graph (cache_for family) family) (v, target).
Proof.
  intros Hlaw u b v target Hb Hreach Htransition.
  rewrite phi_graph_equation in Hreach |- *.
  refine (@reachable_step _ _
    (PreFamily.arc_graph product_encoding (product_nodes family)
      (phi_roots (cache_for family) family) (phi_next_c (cache_for family)))
    ((u, b), (v, target)) Hreach _).
  rewrite PreFamily.arc_graph_source.
  apply (PreFamily.arc_graph_member _ (product_encoding_laws Hlaw)); split; [reflexivity|].
  rewrite phi_next_value; apply (phi_next_exact family Hlaw u b v target Hb); exact Htransition.
Qed.

Local Lemma phi_graph_complete family :
  Pre.laws c -> (forall u, In u family <-> PreFamily.in_family c u) ->
  forall u b, phi_needed c u b -> reachable (phi_graph (cache_for family) family) (u, b).
Proof.
  intros Hlaw Hfamily u b Hphi.
  induction Hphi as [u b x Hu Hb Hentry Hx Hparam|
    u d b Hu Hd Hdf|u d b Hphi IH Hdf|
    u b be v target Hphi IH Hbe Htarget Htranslate Hdf].
  - apply reachable_entry.
    rewrite phi_graph_equation; apply (phi_roots_exact family Hlaw).
    split; [apply Hfamily; exact Hu|left; split; [exact Hb|]; split; [exact Hentry|exists x; auto]].
  - apply reachable_entry.
    rewrite phi_graph_equation; apply (phi_roots_exact family Hlaw).
    split; [apply Hfamily; exact Hu|right; exists d; split; [exact Hd|]].
    eapply idf_seed; [now left|exact Hdf].
  - eapply phi_graph_step; [exact Hlaw|exact (phi_needed_nodes c Hlaw Hphi)|exact IH|].
    left; split; [reflexivity|]; eapply idf_seed; [now left|exact Hdf].
  - eapply phi_graph_step; [exact Hlaw|exact (phi_needed_nodes c Hlaw Hphi)|exact IH|].
    right; exists be; repeat split; try assumption.
    eapply idf_seed; [now left|exact Hdf].
Qed.

(** Product reachability is exactly the least phi relation with all four legacy clauses. *)
Theorem phi_graph_exact family :
  Pre.laws c -> (forall u, In u family <-> PreFamily.in_family c u) ->
  forall u b, reachable (phi_graph (cache_for family) family) (u, b) <-> phi_needed c u b.
Proof.
  intros Hlaw Hfamily u b; split.
  - apply phi_graph_sound; assumption.
  - apply phi_graph_complete; assumption.
Qed.

(** Phi-site materialization swaps only the product coordinate order before canonical indexing. *)
Theorem phi_sites_for_equation family :
  phi_sites_for family = FinSet.of_list (phi_encoding c)
    (map (fun key => (snd key, fst key))
      (PreFamily.reachable_nodes product_encoding (phi_graph (cache_for family) family))).
Proof.
  unfold phi_sites_for, phi_sites_for_c; rewrite !Cost.value_bind, value_map_c; reflexivity.
Qed.

(** Every raw phi-site index is canonical independently of client semantic or graph laws. *)
Theorem phi_sites_for_wf family :
  FinSet.wf (phi_encoding c) (phi_sites_for family).
Proof.
  rewrite phi_sites_for_equation; apply FinSet.wf_of_list.
Qed.

(** A supplied exact expression family yields precisely the four-clause least phi placement. *)
Theorem phi_sites_for_exact family :
  Pre.laws c -> (forall u, In u family <-> PreFamily.in_family c u) ->
  forall u b, FinSet.mem (phi_encoding c) (b, u) (phi_sites_for family) = true <->
    phi_needed c u b.
Proof.
  intros Hlaw Hfamily u b.
  destruct (phi_graph_domain family Hlaw Hfamily) as [Hgraph Hout].
  rewrite phi_sites_for_equation, (PreFamily.set_member _ (phi_encoding_laws c Hlaw)).
  rewrite in_map_iff.
  assert (Hexact : In (u, b)
    (PreFamily.reachable_nodes product_encoding (phi_graph (cache_for family) family)) <->
      phi_needed c u b).
  { rewrite (PreFamily.reachable_nodes_exact _ (product_encoding_laws Hlaw) _ Hgraph Hout).
    apply phi_graph_exact; assumption. }
  split.
  - intros [[v target] [Heq Hin]]; cbn [fst snd] in Heq; inversion Heq; subst v target.
    apply Hexact; exact Hin.
  - intro Hphi; exists (u, b); split; [reflexivity|apply Hexact; exact Hphi].
Qed.

(** Successful preparation retains its actual discovered family for subsequent scoped renaming. *)
Record phi_data := PhiData {
  all_family : list U;
  sites : FinSet.t (B * U)
}.

Definition phi_sites_c : Cost.t (list U + phi_data) :=
  let* result := PreFamily.discover_c c in
  match result with
  | inl partial => Cost.ret (inl partial)
  | inr family => Cost.map (fun index => inr (PhiData family index)) (phi_sites_for_c family)
  end.
Definition phi_sites := Cost.value phi_sites_c.

(** Lawful placement returns the same exact discovered family and canonical product-closure index. *)
Theorem phi_sites_success :
  Pre.laws c ->
  phi_sites = inr (PhiData (PreFamily.universe c) (phi_sites_for (PreFamily.universe c))).
Proof.
  intro Hlaw; unfold phi_sites, phi_sites_c; rewrite Cost.value_bind.
  fold (PreFamily.discover c); rewrite (PreFamily.discover_success c Hlaw), Cost.value_map.
  reflexivity.
Qed.

(** Complete phi preparation discovers the exact family
    and computes all four legacy placement clauses. *)
Theorem phi_sites_exact :
  Pre.laws c ->
  exists data, phi_sites = inr data /\ NoDup (all_family data) /\
    (forall u, In u (all_family data) <-> PreFamily.in_family c u) /\
    forall u b, FinSet.mem (phi_encoding c) (b, u) (sites data) = true <-> phi_needed c u b.
Proof.
  intro Hlaw; exists (PhiData (PreFamily.universe c) (phi_sites_for (PreFamily.universe c))).
  split.
  - unfold phi_sites, phi_sites_c; rewrite Cost.value_bind.
    fold (PreFamily.discover c); rewrite (PreFamily.discover_success c Hlaw), Cost.value_map.
    reflexivity.
  - split; [exact (proj1 (PreFamily.universe_exact c Hlaw))|].
    split; [exact (proj2 (PreFamily.universe_exact c Hlaw))|].
    apply phi_sites_for_exact; [exact Hlaw|exact (proj2 (PreFamily.universe_exact c Hlaw))].
Qed.

End PhiClosure.

End PreFrg.
