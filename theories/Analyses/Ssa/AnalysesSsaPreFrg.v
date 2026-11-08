(** * Factored expression definitions

    Version origins distinguish missing entry values, initial values, computations and phis.
    For example, a phi definition is after parameter binding rather than at block entry.
    Builds on: AnalysesSsaPreFamily, ProgramSsaPoints and GraphFrontierSpec. *)

From Stdlib Require Import List Bool NArith.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseCode BaseEq BaseMap BaseSet BaseIndex.
From Galois.Graph Require Import GraphModel GraphPrepared GraphDomSpec GraphFrontierSpec.
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

(** The indexes distinguish incoming edge identities even when their endpoints coincide. *)
Record frg (B BE E U : Type) := Frg {
  versions : list (version B E U);
  occurrences : Map.t E (version B E U);
  fresh : FinSet.t E;
  phis : FinSet.t (B * U);
  operands : Map.t ((B * U) * BE) (operand B E U);
  unsafe : FinSet.t (B * U)
}.
Arguments Frg {B BE E U}.
Arguments versions {B BE E U}.
Arguments occurrences {B BE E U}.
Arguments fresh {B BE E U}.
Arguments phis {B BE E U}.
Arguments operands {B BE E U}.
Arguments unsafe {B BE E U}.

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

Local Lemma tail_member {X} (x : X) xs : In x (tl xs) -> In x xs.
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

Local Lemma chain_source {N E} (g : Graph.t N E) {ns es e} :
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

Local Lemma internal_edge_block {e} :
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

(** Definition preparation visits the program and the family once before any per-expression query. *)
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

(** Prepared occurrence seeds retain actual source-block callbacks and pure recomputation identity. *)
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

(** For a supplied family member, prepared seeds have exactly the legacy definition-block meaning. *)
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

(** Definition queries agree with the fixed source relation through public stable-index contracts. *)
Theorem defs_exact family u :
  Pre.laws c -> In u family ->
  forall b, In b (defs (definition_index family) u) <-> definition_block c u b.
Proof.
  intros Hlaw Hu b; rewrite defs_equation, bucket_member by exact Hlaw.
  apply definition_pairs_spec; exact Hu.
Qed.

End DefinitionIndex.

End PreFrg.
