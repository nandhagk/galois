(** * Semidominator paths of the actual shared search

    A semidominator minimizes the start rank of a nonempty path whose internal ranks exceed its end.
    For example, the later-discovered diamond arm gives a branch-to-join candidate path.
    Builds on: GraphDomPath, GraphDomDfs and the actual GraphDomSemi prologue. *)

From Stdlib Require Import List PArith Lia.
From Stdlib.Relations Require Import Relation_Operators.
From Stdlib.Relations Require Import Operators_Properties.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseIndex.
From Galois.Graph Require Import GraphModel GraphPrepared GraphSearchSpec GraphReach
  GraphDomSemi GraphDomTransport GraphDomPath GraphDomDfs GraphDomDfsPath GraphDomSemiEval
  GraphDomLink GraphDomLinkProof.
Import List.ListNotations.

Module DomSemiExact.

(** Every internal target of a nonempty high path is strictly above its chosen cutoff. *)
Inductive high_path {V E} (shared : DomSemi.semi V E) (cutoff : positive) :
    positive -> list (E + V) -> positive -> Prop :=
  | HighOne : forall u e v, DomPath.vertex shared u -> DomPath.vertex shared v ->
      DomSemi.ranked_arc shared u e v -> high_path shared cutoff u [e] v
  | HighCons : forall u e v es z, DomPath.vertex shared u ->
      DomSemi.ranked_arc shared u e v -> (cutoff < v)%positive ->
      high_path shared cutoff v es z -> high_path shared cutoff u (e :: es) z.

(** A semidominator candidate has a nonempty actual ranked path above its endpoint cutoff. *)
Definition semidom_path {V E} (p : Prepared.t V E) u n :=
  exists es, high_path (DomSemi.compute p) n u es n.

(** Semidominators minimize start rank among all such actual search paths. *)
Definition semidominator {V E} (p : Prepared.t V E) u n :=
  semidom_path p u n /\ forall v, semidom_path p v n -> (u <= v)%positive.

(** A bounded path requires its guard at every edge target, including the endpoint. *)
Inductive bounded_path {V E} (shared : DomSemi.semi V E) (guard : positive -> Prop) :
    positive -> list (E + V) -> positive -> Prop :=
  | BoundNil : forall v, DomPath.vertex shared v -> bounded_path shared guard v [] v
  | BoundCons : forall u e v es z, DomPath.vertex shared u ->
      DomSemi.ranked_arc shared u e v -> guard v ->
      bounded_path shared guard v es z -> bounded_path shared guard u (e :: es) z.

(** Every bounded path starts at an actual discovered rank. *)
Theorem bounded_start {V E} (shared : DomSemi.semi V E) guard u es v :
  bounded_path shared guard u es v -> DomPath.vertex shared u.
Proof.
  intro Hpath. destruct Hpath; assumption.
Qed.

(** Every bounded path ends at an actual discovered rank. *)
Theorem bounded_end {V E} (shared : DomSemi.semi V E) guard u es v :
  bounded_path shared guard u es v -> DomPath.vertex shared v.
Proof.
  intro Hpath. induction Hpath; assumption.
Qed.

(** Forgetting guards retains the same actual ranked path and labels. *)
Theorem bounded_sound {V E} (shared : DomSemi.semi V E) guard u es v :
  bounded_path shared guard u es v -> DomPath.path shared u es v.
Proof.
  intro Hpath. induction Hpath as [v Hv|u e v es z Hu Hedge Hguard Htail IH].
  - now constructor.
  - econstructor; [exact Hu|exact Hedge|exact IH].
Qed.

(** A pointwise weaker guard admits the same bounded path. *)
Theorem bounded_mono {V E} (shared : DomSemi.semi V E) guard guard' u es v :
  (forall x, guard x -> guard' x) ->
  bounded_path shared guard u es v -> bounded_path shared guard' u es v.
Proof.
  intros Hguard Hpath. induction Hpath as [v Hv|u e v es z Hu Hedge Hv Htail IH].
  - now constructor.
  - econstructor; [exact Hu|exact Hedge|now apply Hguard|exact IH].
Qed.

(** Bounded paths concatenate through the same actual intermediate rank. *)
Theorem bounded_app {V E} (shared : DomSemi.semi V E) guard u xs middle ys v :
  bounded_path shared guard u xs middle -> bounded_path shared guard middle ys v ->
  bounded_path shared guard u (xs ++ ys) v.
Proof.
  intros Hfirst Hlast. induction Hfirst as [u Hu|u e a xs middle Hu Hedge Hbound Htail IH].
  - exact Hlast.
  - cbn [app]. econstructor; [exact Hu|exact Hedge|exact Hbound|now apply IH].
Qed.

Local Lemma bounded_snoc {V E} (shared : DomSemi.semi V E) guard u es v e z :
  bounded_path shared guard u es v -> DomSemi.ranked_arc shared v e z ->
  DomPath.vertex shared z -> guard z -> bounded_path shared guard u (es ++ [e]) z.
Proof.
  intros Hpath Hedge Hz Hbound.
  induction Hpath as [v Hv|u edge a es v Hu Hstep Ha Htail IH].
  - cbn [app]. econstructor; [exact Hv|exact Hedge|exact Hbound|now constructor].
  - cbn [app]. econstructor; [exact Hu|exact Hstep|exact Ha|now apply IH].
Qed.

Local Lemma bounded_finish {V E} (shared : DomSemi.semi V E) cutoff u es v e :
  bounded_path shared (fun x => (cutoff < x)%positive) u es v ->
  DomSemi.ranked_arc shared v e cutoff -> DomPath.vertex shared cutoff ->
  high_path shared cutoff u (es ++ [e]) cutoff.
Proof.
  intros Hpath Hedge Hcutoff.
  induction Hpath as [v Hv|u edge a es v Hu Hstep Ha Htail IH].
  - cbn [app]. now constructor.
  - cbn [app]. econstructor; [exact Hu|exact Hstep|exact Ha|now apply IH].
Qed.

(** A high path obeys any guard satisfied by its internal ranks and its final endpoint. *)
Theorem high_as_bounded {V E} (shared : DomSemi.semi V E) cutoff u es v guard :
  high_path shared cutoff u es v ->
  (forall x, (cutoff < x)%positive -> guard x) -> guard v ->
  bounded_path shared guard u es v.
Proof.
  intros Hpath Hguard Hend.
  induction Hpath as [u e v Hu Hv Hedge|u e v es z Hu Hedge Hbound Htail IH].
  - econstructor; [exact Hu|exact Hedge|exact Hend|now constructor].
  - econstructor; [exact Hu|exact Hedge|now apply Hguard|now apply IH].
Qed.

(** The actual DFS branch supplies a labelled path whose targets stay above its starting rank. *)
Theorem tree_path {V E} (p : Prepared.t V E) u v :
  Prepared.ready p -> DomPath.vertex (DomSemi.compute p) u -> DomDfs.ancestor p u v ->
  exists es, bounded_path (DomSemi.compute p) (fun x => (u <= x)%positive) u es v.
Proof.
  intros Hready Hu Hancestor.
  pose proof (clos_rt_rtn1 positive
    (fun a b => Map.get positive_encoding b
      (DomSemi.parents (DomSemi.ranked (DomSemi.compute p))) = Some a) u v Hancestor) as Hchain.
  clear Hancestor.
  induction Hchain as [|parent child Hlink Hprefix IH].
  - exists []. now constructor.
  - destruct IH as [es Hpath].
    destruct (DomDfs.parent_arc p child parent Hready Hlink) as [e Hedge].
    exists (es ++ [e]). apply bounded_snoc with (v := parent).
    + exact Hpath.
    + exact Hedge.
    + exact (proj1 (DomDfs.parent_vertices p child parent Hready Hlink)).
    + assert (Hwhole : DomDfs.ancestor p u child).
      { eapply rt_trans.
        - exact (clos_rtn1_rt positive
            (fun a b => Map.get positive_encoding b
              (DomSemi.parents (DomSemi.ranked (DomSemi.compute p))) = Some a) u parent Hprefix).
        - apply rt_step. exact Hlink. }
      destruct (DomDfs.ancestor_order p u child Hready Hwhole) as [->|Hlt];
        [apply Pos.le_refl|now apply Pos.lt_le_incl].
Qed.

Local Lemma bounded_closure {V E} (shared : DomSemi.semi V E) guard
    (P : positive -> Prop) :
  (forall u e v, DomPath.vertex shared u -> DomPath.vertex shared v ->
    DomSemi.ranked_arc shared u e v -> guard v -> P u -> P v) ->
  forall u es v, bounded_path shared guard u es v -> P u -> P v.
Proof.
  intros Hstep u es v Hpath.
  induction Hpath as [u Hu|u e v es z Hu Hedge Hv Htail IH]; intro HP.
  - exact HP.
  - apply IH. exact (Hstep u e v Hu (bounded_start _ _ _ _ _ Htail) Hedge Hv HP).
Qed.

(** A bounded path above an ancestor rank stays inside that ancestor's actual DFS subtree. *)
Theorem bounded_region {V E} (p : Prepared.t V E) a u es v :
  Prepared.ready p -> DomPath.vertex (DomSemi.compute p) a ->
  bounded_path (DomSemi.compute p) (fun x => (a <= x)%positive) u es v ->
  DomDfs.ancestor p a u -> DomDfs.ancestor p a v.
Proof.
  intros Hready Ha Hpath Hancestor.
  eapply (bounded_closure (DomSemi.compute p) _ (DomDfs.ancestor p a)).
  - intros source e target Hsource Htarget Hedge Hbound Hanc.
    exact (DomDfsPath.subtree_edge p a source target e
      Hready Ha Hsource Htarget Hanc Hedge Hbound).
  - exact Hpath.
  - exact Hancestor.
Qed.

(** High paths are nonempty by construction, including at a self-loop. *)
Theorem high_nonempty {V E} (shared : DomSemi.semi V E) cutoff u es v :
  high_path shared cutoff u es v -> es <> [].
Proof.
  intro Hpath. destruct Hpath; discriminate.
Qed.

(** The high-path predicate retains the actual ranked labelled path. *)
Theorem high_path_sound {V E} (shared : DomSemi.semi V E) cutoff u es v :
  high_path shared cutoff u es v -> DomPath.path shared u es v.
Proof.
  intro Hpath.
  induction Hpath as [u e v Hu Hv Hedge|u e v es z Hu Hedge Hhigh Htail IH].
  - econstructor; [exact Hu|exact Hedge|now constructor].
  - econstructor; [exact Hu|exact Hedge|exact IH].
Qed.

(** Both ends of a high path denote actual recorded discovery ranks. *)
Theorem high_vertices {V E} (shared : DomSemi.semi V E) cutoff u es v :
  high_path shared cutoff u es v -> DomPath.vertex shared u /\ DomPath.vertex shared v.
Proof.
  intro Hpath.
  induction Hpath as [u e v Hu Hv Hedge|u e v es z Hu Hedge Hhigh Htail IH];
    split; tauto.
Qed.

Local Lemma high_last {V E} (shared : DomSemi.semi V E) cutoff u es v :
  high_path shared cutoff u es v ->
  exists parent prefix edge, es = prefix ++ [edge] /\
    bounded_path shared (fun x => (cutoff < x)%positive) u prefix parent /\
    DomSemi.ranked_arc shared parent edge v /\ DomPath.vertex shared v.
Proof.
  intro Hpath.
  induction Hpath as [u e v Hu Hv Hedge|u e v es z Hu Hedge Hhigh Htail IH].
  - exists u, [], e. split; [reflexivity|].
    split; [now constructor|]. auto.
  - destruct IH as [parent [prefix [edge [Heq [Hprefix [Hedge' Hz]]]]]].
    exists parent, (e :: prefix), edge. split; [cbn [app]; now rewrite Heq|].
    split; [|auto].
    econstructor; [exact Hu|exact Hedge|exact Hhigh|exact Hprefix].
Qed.

(** Every nonempty bounded path splits at its first minimum target while retaining the guard. *)
Theorem bounded_minimum {V E} (shared : DomSemi.semi V E) guard u es v :
  bounded_path shared guard u es v -> es <> [] ->
  exists least prefix suffix, es = prefix ++ suffix /\ prefix <> [] /\
    high_path shared least u prefix least /\
    bounded_path shared (fun x => (least <= x)%positive) least suffix v /\
    bounded_path shared (fun x => (least <= x)%positive) u es v /\ guard least.
Proof.
  intro Hpath.
  induction Hpath as [u Hu|u e v es z Hu Hedge Hguard Htail IH]; intro Hnonempty;
    [contradiction|].
  destruct es as [|edge es].
  - inversion Htail; subst z.
    exists v, [e], []. split; [reflexivity|]. split; [discriminate|].
    split; [now constructor|].
    split; [now constructor|]. split; [|exact Hguard].
    econstructor; [exact Hu|exact Hedge|apply Pos.le_refl|now constructor].
  - destruct (IH ltac:(discriminate))
      as [least [prefix [suffix [Hsplit [Hprefix [Hfirst [Hlast [Hwhole Hleast]]]]]]]].
    destruct (Pos.leb v least) eqn:Hcompare.
    + apply Pos.leb_le in Hcompare.
      pose proof (proj1 (high_vertices _ _ _ _ _ Hfirst)) as Hv.
      exists v, [e], (edge :: es). split; [reflexivity|]. split; [discriminate|].
      split; [now constructor|].
      assert (Htail_bound :
        bounded_path shared (fun x => (v <= x)%positive) v (edge :: es) z).
      { eapply bounded_mono; [|exact Hwhole].
        intros x Hx. eapply Pos.le_trans; eassumption. }
      split; [exact Htail_bound|]. split; [|exact Hguard].
      econstructor; [exact Hu|exact Hedge|apply Pos.le_refl|exact Htail_bound].
    + apply Pos.leb_gt in Hcompare.
      exists least, (e :: prefix), suffix.
      split; [cbn [app]; now rewrite Hsplit|]. split; [discriminate|].
      split.
      * econstructor; [exact Hu|exact Hedge|exact Hcompare|exact Hfirst].
      * split; [exact Hlast|]. split; [|exact Hleast].
        econstructor; [exact Hu|exact Hedge|now apply Pos.lt_le_incl|exact Hwhole].
Qed.

(** Each candidate's endpoints are discovered by the same stored prologue search. *)
Theorem candidate_vertices {V E} (p : Prepared.t V E) u n :
  semidom_path p u n -> DomPath.vertex (DomSemi.compute p) u /\ DomPath.vertex (DomSemi.compute p) n.
Proof.
  intros [es Hpath]. now apply high_vertices in Hpath.
Qed.

(** The least candidate rank identifies a unique semidominator without an output-map premise. *)
Theorem semidominator_unique {V E} (p : Prepared.t V E) u v n :
  semidominator p u n -> semidominator p v n -> u = v.
Proof.
  intros [Hu Hminimum_u] [Hv Hminimum_v].
  apply Pos.le_antisym; [now apply Hminimum_u|now apply Hminimum_v].
Qed.

(** Every actual DFS parent supplies a one-edge semidominator candidate. *)
Theorem parent_candidate {V E} (p : Prepared.t V E) n parent :
  Prepared.ready p ->
  Map.get positive_encoding n (DomSemi.parents (DomSemi.ranked (DomSemi.compute p))) =
    Some parent -> semidom_path p parent n.
Proof.
  intros Hready Hget. destruct (DomDfs.parent_arc p n parent Hready Hget) as [e He].
  destruct (DomDfs.parent_vertices p n parent Hready Hget) as [Hn Hparent].
  exists [e]. constructor; assumption.
Qed.

(** On every discovered nonroot, a minimum candidate strictly precedes the endpoint rank. *)
Theorem semidominator_bound {V E} (p : Prepared.t V E) u n :
  Prepared.ready p -> n <> 1%positive -> semidominator p u n -> (u < n)%positive.
Proof.
  intros Hready Hnonroot [Hpath Hminimum].
  pose proof (proj2 (candidate_vertices p u n Hpath)) as Hn.
  destruct (Map.get positive_encoding n (DomSemi.parents (DomSemi.ranked (DomSemi.compute p))))
    as [parent|] eqn:Hparent.
  - eapply Pos.le_lt_trans.
    + apply Hminimum. exact (parent_candidate p n parent Hready Hparent).
    + exact (DomDfs.parent_decreases p n parent Hready Hparent).
  - apply (proj1 (DomDfs.parent_none_iff p n Hready Hn)) in Hparent. contradiction.
Qed.

(** Every candidate splits at a predecessor or at a higher-ranked ancestor of that predecessor. *)
Theorem path_predecessor {V E} (p : Prepared.t V E) source target :
  Prepared.ready p -> semidom_path p source target ->
  exists parent edge, DomSemi.ranked_arc (DomSemi.compute p) parent edge target /\
    DomPath.vertex (DomSemi.compute p) parent /\
    (source = parent \/
      exists high, (target < high)%positive /\ DomDfs.ancestor p high parent /\
        semidom_path p source high).
Proof.
  intros Hready [es Hpath].
  destruct (high_last _ _ _ _ _ Hpath)
    as [parent [prefix [edge [Hsplit [Hprefix [Hedge Htarget]]]]]].
  exists parent, edge. split; [exact Hedge|].
  split; [exact (bounded_end _ _ _ _ _ Hprefix)|].
  destruct prefix as [|label prefix].
  - inversion Hprefix; subst parent. now left.
  - right.
    destruct (bounded_minimum _ _ _ _ _ Hprefix ltac:(discriminate))
      as [high [first [last [Hparts [Hfirst [Hcandidate [Hlast [Hwhole Hbound]]]]]]]].
    exists high. split; [exact Hbound|]. split.
    + apply (bounded_region p high high last parent Hready
        (bounded_start _ _ _ _ _ Hlast) Hlast).
      apply rt_refl.
    + now exists first.
Qed.

(** A higher ancestor's candidate extends through its DFS suffix to the current predecessor edge. *)
Theorem path_extend {V E} (p : Prepared.t V E) source high parent target edge :
  Prepared.ready p -> semidom_path p source high -> (target < high)%positive ->
  DomDfs.ancestor p high parent ->
  DomSemi.ranked_arc (DomSemi.compute p) parent edge target ->
  DomPath.vertex (DomSemi.compute p) target -> semidom_path p source target.
Proof.
  intros Hready Hcandidate Hbound Hancestor Hedge Htarget.
  pose proof (proj2 (candidate_vertices p source high Hcandidate)) as Hhigh.
  destruct Hcandidate as [prefix Hprefix].
  destruct (tree_path p high parent Hready Hhigh Hancestor) as [suffix Hsuffix].
  assert (Hfirst : bounded_path (DomSemi.compute p)
    (fun x => (target < x)%positive) source prefix high).
  { eapply high_as_bounded; [exact Hprefix| |exact Hbound].
    intros x Hx. eapply Pos.lt_trans; eassumption. }
  assert (Hlast : bounded_path (DomSemi.compute p)
    (fun x => (target < x)%positive) high suffix parent).
  { eapply bounded_mono; [|exact Hsuffix].
    intros x Hx. eapply Pos.lt_le_trans; eassumption. }
  exists ((prefix ++ suffix) ++ [edge]).
  apply bounded_finish with (v := parent).
  - eapply bounded_app; eassumption.
  - exact Hedge.
  - exact Htarget.
Qed.

(** A candidate lowers to a nonempty path with the same original labels and named endpoints. *)
Theorem candidate_original_path {V E} (p : Prepared.t V E) u n source_rank target_rank :
  Prepared.ready p ->
  Map.get positive_encoding u (Search.pre_num (DomSemi.search (DomSemi.compute p))) =
    Some source_rank ->
  Map.get positive_encoding n (Search.pre_num (DomSemi.search (DomSemi.compute p))) =
    Some target_rank ->
  semidom_path p source_rank target_rank ->
  exists es, es <> [] /\
    Search.scoped_path (DomSemi.prepared (DomSemi.compute p)) Reach.unrestricted u es n.
Proof.
  intros Hready Hu Hn [es Hpath]. exists es. split.
  - exact (high_nonempty _ _ _ _ _ Hpath).
  - apply (DomPath.lower p source_rank es target_rank Hready
      (high_path_sound _ _ _ _ _ Hpath) u n Hu Hn).
Qed.

(** A reverse-pass prefix stores proved minima exactly at discovered ranks above its cutoff. *)
Record values_ready {V E} (p : Prepared.t V E) cutoff semis : Prop := {
  values_wf : Map.wf positive_encoding semis;
  values_sound : forall n u, Map.get positive_encoding n semis = Some u ->
    n <> 1%positive /\ semidominator p u n;
  values_domain : forall n, DomPath.vertex (DomSemi.compute p) n ->
    ((exists u, Map.get positive_encoding n semis = Some u) <-> (cutoff < n)%positive)
}.

Local Lemma value_bound {V E} (p : Prepared.t V E) cutoff semis v :
  Prepared.ready p -> values_ready p cutoff semis ->
  (DomLink.identity_value semis v <= v)%positive.
Proof.
  intros Hready Hvalues. rewrite DomLink.identity_value_equation.
  destruct (Map.get positive_encoding v semis) as [u|] eqn:Hget; [|apply Pos.le_refl].
  destruct (values_sound _ _ _ Hvalues v u Hget) as [Hnonroot Hsemi].
  apply Pos.lt_le_incl. exact (semidominator_bound p u v Hready Hnonroot Hsemi).
Qed.

Local Lemma value_low {V E} (p : Prepared.t V E) cutoff semis v :
  values_ready p cutoff semis -> DomPath.vertex (DomSemi.compute p) v ->
  (v <= cutoff)%positive -> DomLink.identity_value semis v = v.
Proof.
  intros Hvalues Hv Hlow. rewrite DomLink.identity_value_equation.
  destruct (Map.get positive_encoding v semis) as [u|] eqn:Hget; [|reflexivity].
  assert (Hhigh : (cutoff < v)%positive).
  { apply (proj1 (values_domain _ _ _ Hvalues v Hv)). now exists u. }
  exact (False_rect _ (Pos.lt_irrefl cutoff (Pos.lt_le_trans _ _ _ Hhigh Hlow))).
Qed.

Local Lemma value_high {V E} (p : Prepared.t V E) cutoff semis v :
  values_ready p cutoff semis -> DomPath.vertex (DomSemi.compute p) v ->
  (cutoff < v)%positive -> semidominator p (DomLink.identity_value semis v) v.
Proof.
  intros Hvalues Hv Hhigh.
  destruct (proj2 (values_domain _ _ _ Hvalues v Hv) Hhigh) as [u Hget].
  rewrite DomLink.identity_value_equation, Hget.
  exact (proj2 (values_sound _ _ _ Hvalues v u Hget)).
Qed.

Local Lemma eval_candidate {V E} (p : Prepared.t V E) cutoff semis links source edge :
  Prepared.ready p -> values_ready p cutoff semis ->
  DomLinkProof.valid (DomLink.identity_value semis) links ->
  DomSemiEval.cut_forest p cutoff links ->
  DomPath.vertex (DomSemi.compute p) source ->
  DomPath.vertex (DomSemi.compute p) cutoff ->
  DomSemi.ranked_arc (DomSemi.compute p) source edge cutoff ->
  let '(links', chosen) :=
    Cost.value (DomLink.eval_c (DomLink.identity_value_c semis) links source) in
  DomLink.original links' = DomLink.original links /\
    DomLinkProof.valid (DomLink.identity_value semis) links' /\
    semidom_path p (DomLink.identity_value semis chosen) cutoff /\
    (DomLink.identity_value semis chosen <= source)%positive /\
    forall u, (cutoff < u)%positive -> DomDfs.ancestor p u source ->
      (DomLink.identity_value semis chosen <= DomLink.identity_value semis u)%positive.
Proof.
  intros Hready Hvalues Hvalid Hforest Hsource Hcutoff Hedge.
  pose proof (DomSemiEval.eval_minima p cutoff (DomLink.identity_value_c semis)
    links source Hready Hvalid Hforest Hsource) as Heval.
  destruct (Cost.value (DomLink.eval_c (DomLink.identity_value_c semis) links source))
    as [links' chosen].
  fold (DomLink.identity_value semis chosen) in Heval.
  fold (DomLink.identity_value semis source) in Heval.
  destruct Heval as [Horiginal [Hvalid' [Hchosen [Hsource_bound Hancestors]]]].
  split; [exact Horiginal|]. split; [exact Hvalid'|]. split.
  - destruct Hchosen as [[-> Hlow]|[Hhigh [Hvertex Hancestor]]].
    + rewrite (value_low p cutoff semis source Hvalues Hsource Hlow).
      exists [edge]. now constructor.
    + eapply path_extend; [exact Hready| |exact Hhigh|exact Hancestor|exact Hedge|exact Hcutoff].
      exact (proj1 (value_high p cutoff semis chosen Hvalues Hvertex Hhigh)).
  - split; [|exact Hancestors].
    eapply Pos.le_trans; [exact Hsource_bound|].
    exact (value_bound p cutoff semis source Hready Hvalues).
Qed.

(** A current minimum bounds a predecessor and all previously settled ancestors of that predecessor. *)
Definition incoming_bound {V E} (p : Prepared.t V E) cutoff semis source best :=
  (best <= source)%positive /\
    forall u, (cutoff < u)%positive -> DomDfs.ancestor p u source ->
      (best <= DomLink.identity_value semis u)%positive.

Local Lemma incoming_lower {V E} (p : Prepared.t V E) cutoff semis source best best' :
  (best' <= best)%positive -> incoming_bound p cutoff semis source best ->
  incoming_bound p cutoff semis source best'.
Proof.
  intros Hle [Hsource Hancestors]. split.
  - eapply Pos.le_trans; eassumption.
  - intros u Hu Hancestor. eapply Pos.le_trans; [exact Hle|now apply Hancestors].
Qed.

(** Processing an actual incoming occurrence preserves links and supplies its path-minimum bound. *)
Theorem predecessor_correct {V E} (p : Prepared.t V E) cutoff semis links best source edge :
  Prepared.ready p -> values_ready p cutoff semis ->
  DomLinkProof.valid (DomLink.identity_value semis) links ->
  DomSemiEval.cut_forest p cutoff links ->
  DomPath.vertex (DomSemi.compute p) source ->
  DomPath.vertex (DomSemi.compute p) cutoff ->
  DomSemi.ranked_arc (DomSemi.compute p) source edge cutoff ->
  semidom_path p best cutoff ->
  let '(links', best') := Cost.value (DomSemi.predecessor_c semis (links, best) source) in
  DomLink.original links' = DomLink.original links /\
    DomLinkProof.valid (DomLink.identity_value semis) links' /\
    semidom_path p best' cutoff /\ (best' <= best)%positive /\
    incoming_bound p cutoff semis source best'.
Proof.
  intros Hready Hvalues Hvalid Hforest Hsource Hcutoff Hedge Hbest.
  rewrite DomSemi.predecessor_value.
  pose proof (eval_candidate p cutoff semis links source edge
    Hready Hvalues Hvalid Hforest Hsource Hcutoff Hedge) as Heval.
  destruct (Cost.value (DomLink.eval_c (DomLink.identity_value_c semis) links source))
    as [links' chosen].
  destruct Heval as [Horiginal [Hvalid' [Hpath [Hbound Hancestors]]]].
  destruct (DomLinkProof.minimum_bounds (fun rank => Cost.ret rank)
    best (DomLink.identity_value semis chosen)) as [Hleft Hright].
  autorewrite with galois_cost in Hleft, Hright.
  split; [exact Horiginal|]. split; [exact Hvalid'|]. split.
  - destruct (DomLinkProof.minimum_member (fun rank => Cost.ret rank)
      best (DomLink.identity_value semis chosen)) as [Heq|Heq];
      rewrite Heq; assumption.
  - split; [exact Hleft|].
    apply (incoming_lower p cutoff semis source _ _ Hright). split; assumption.
Qed.

Local Lemma arc_source_vertex {V E} (p : Prepared.t V E) u e v :
  Prepared.ready p -> DomPath.vertex (DomSemi.compute p) v ->
  DomSemi.ranked_arc (DomSemi.compute p) u e v -> DomPath.vertex (DomSemi.compute p) u.
Proof.
  intros Hready [raw Hrank] Hedge.
  apply (DomTransport.ranked_arc_spec p raw v e u Hready Hrank) in Hedge.
  destruct Hedge as [source [Harc Hsource]]. now exists source.
Qed.

Local Lemma predecessors_correct {V E} (p : Prepared.t V E) cutoff semis xs :
  Prepared.ready p -> values_ready p cutoff semis ->
  DomPath.vertex (DomSemi.compute p) cutoff ->
  (forall e source, In (e, source) xs ->
    DomSemi.ranked_arc (DomSemi.compute p) source e cutoff) ->
  forall links best,
  DomLinkProof.valid (DomLink.identity_value semis) links ->
  DomSemiEval.cut_forest p cutoff links -> semidom_path p best cutoff ->
  let '(links', best') := fold_left
    (fun acc eu => Cost.value (DomSemi.predecessor_c semis acc (snd eu))) xs (links, best) in
  DomLink.original links' = DomLink.original links /\
    DomLinkProof.valid (DomLink.identity_value semis) links' /\
    semidom_path p best' cutoff /\ (best' <= best)%positive /\
    forall e source, In (e, source) xs -> incoming_bound p cutoff semis source best'.
Proof.
  intros Hready Hvalues Hcutoff.
  induction xs as [|[edge source] rest IH]; intros Hrows links best Hvalid Hforest Hbest.
  - cbn [fold_left]. split; [reflexivity|]. split; [exact Hvalid|].
    split; [exact Hbest|]. split; [apply Pos.le_refl|].
    intros e u Hin. contradiction.
  - assert (Hedge : DomSemi.ranked_arc (DomSemi.compute p) source edge cutoff).
    { apply Hrows. now left. }
    pose proof (predecessor_correct p cutoff semis links best source edge Hready Hvalues
      Hvalid Hforest (arc_source_vertex p source edge cutoff Hready Hcutoff Hedge)
      Hcutoff Hedge Hbest) as Hstep.
    destruct (Cost.value (DomSemi.predecessor_c semis (links, best) source))
      as [links' best'] eqn:Hstep_value.
    destruct Hstep as [Horiginal [Hvalid' [Hbest' [Hdecrease Hhead]]]].
    assert (Hforest' : DomSemiEval.cut_forest p cutoff links').
    { unfold DomSemiEval.cut_forest in *. now rewrite Horiginal. }
    pose proof (IH (fun e u Hin => Hrows e u (or_intror Hin)) links' best'
      Hvalid' Hforest' Hbest') as Hrest.
    cbn [fold_left snd]. rewrite Hstep_value.
    destruct (fold_left
      (fun acc eu => Cost.value (DomSemi.predecessor_c semis acc (snd eu))) rest (links', best'))
      as [final answer].
    destruct Hrest as [Horiginal' [Hfinal [Hanswer [Hdecrease' Hall]]]].
    split; [now rewrite Horiginal', Horiginal|]. split; [exact Hfinal|].
    split; [exact Hanswer|]. split.
    + eapply Pos.le_trans; eassumption.
    + intros e u [Heq|Hin].
      * injection Heq as <- <-. now apply (incoming_lower p cutoff semis source best').
      * exact (Hall e u Hin).
Qed.

Local Lemma predecessors_minimum {V E} (p : Prepared.t V E) cutoff semis best :
  Prepared.ready p -> values_ready p cutoff semis -> semidom_path p best cutoff ->
  (forall e source, DomSemi.ranked_arc (DomSemi.compute p) source e cutoff ->
    incoming_bound p cutoff semis source best) ->
  semidominator p best cutoff.
Proof.
  intros Hready Hvalues Hbest Hbounds. split; [exact Hbest|].
  intros candidate Hcandidate.
  destruct (path_predecessor p candidate cutoff Hready Hcandidate)
    as [source [edge [Hedge [Hsource [Heq|[high [Hhigh [Hancestor Hpath]]]]]]]].
  - subst candidate. exact (proj1 (Hbounds edge source Hedge)).
  - pose proof (DomDfs.ancestor_vertices p high source Hready Hancestor Hsource) as Hvertex.
    pose proof (value_high p cutoff semis high Hvalues Hvertex Hhigh) as Hsemi.
    eapply Pos.le_trans.
    + exact (proj2 (Hbounds edge source Hedge) high Hhigh Hancestor).
    + exact (proj2 Hsemi candidate Hpath).
Qed.

(** A processed prefix stores its proved minima and links precisely its settled nonroots. *)
Record prefix_ready {V E} (p : Prepared.t V E) done (st : DomSemi.state) : Prop := {
  prefix_wf : Map.wf positive_encoding (DomSemi.semis st);
  prefix_sound : forall n u, Map.get positive_encoding n (DomSemi.semis st) = Some u ->
    In n done /\ n <> 1%positive /\ semidominator p u n;
  prefix_total : forall n, DomPath.vertex (DomSemi.compute p) n ->
    In n done -> n <> 1%positive -> exists u, Map.get positive_encoding n (DomSemi.semis st) = Some u;
  prefix_links : forall n,
    Map.get positive_encoding n (DomLink.original (DomSemi.links st)) =
      match Map.get positive_encoding n (DomSemi.semis st) with
      | None => None
      | Some _ => Map.get positive_encoding n (DomSemi.parents (DomSemi.ranked (DomSemi.compute p)))
      end;
  prefix_valid : DomLinkProof.valid (DomLink.identity_value (DomSemi.semis st)) (DomSemi.links st)
}.

Local Lemma prefix_initial {V E} (p : Prepared.t V E) :
  prefix_ready p [] DomSemi.initial.
Proof.
  constructor; cbn [DomSemi.initial DomSemi.semis DomSemi.links].
  - apply Map.wf_empty.
  - intros n u Hget. rewrite Map.get_empty in Hget. discriminate.
  - intros n Hn Hin. contradiction.
  - intro n. cbn [DomLink.empty DomLink.original]. now rewrite !Map.get_empty.
  - apply DomLinkProof.empty_valid.
Qed.

Local Lemma prefix_values {V E} (p : Prepared.t V E) done st cutoff :
  prefix_ready p done st ->
  (forall n, DomPath.vertex (DomSemi.compute p) n -> (In n done <-> (cutoff < n)%positive)) ->
  values_ready p cutoff (DomSemi.semis st).
Proof.
  intros Hprefix Hcut. constructor.
  - exact (prefix_wf _ _ _ Hprefix).
  - intros n u Hget. exact (proj2 (prefix_sound _ _ _ Hprefix n u Hget)).
  - intros n Hn. split.
    + intros [u Hget]. apply (proj1 (Hcut n Hn)).
      exact (proj1 (prefix_sound _ _ _ Hprefix n u Hget)).
    + intro Hhigh. apply (prefix_total _ _ _ Hprefix n Hn (proj2 (Hcut n Hn) Hhigh)).
      intro Heq. subst n. apply Pos2Nat.inj_lt in Hhigh.
      pose proof (Pos2Nat.is_pos cutoff). cbn in Hhigh. lia.
Qed.

Local Lemma prefix_forest {V E} (p : Prepared.t V E) done st cutoff :
  Prepared.ready p -> prefix_ready p done st ->
  (forall n, DomPath.vertex (DomSemi.compute p) n -> (In n done <-> (cutoff < n)%positive)) ->
  DomSemiEval.cut_forest p cutoff (DomSemi.links st).
Proof.
  intros Hready Hprefix Hcut n parent.
  rewrite (prefix_links _ _ _ Hprefix n).
  destruct (Map.get positive_encoding n (DomSemi.semis st)) as [u|] eqn:Hget.
  - destruct (prefix_sound _ _ _ Hprefix n u Hget) as [Hin [Hnonroot Hsemi]].
    pose proof (proj2 (candidate_vertices p u n (proj1 Hsemi))) as Hn.
    split; [intro Hparent; split; [exact Hparent|now apply Hcut]|tauto].
  - split; [discriminate|]. intros [Hparent Hhigh].
    pose proof (proj1 (DomDfs.parent_vertices p n parent Hready Hparent)) as Hn.
    destruct (prefix_total _ _ _ Hprefix n Hn (proj2 (Hcut n Hn) Hhigh))
      as [value Hvalue]; [|congruence].
    intro Heq. subst n. apply Pos2Nat.inj_lt in Hhigh.
    pose proof (Pos2Nat.is_pos cutoff). cbn in Hhigh. lia.
Qed.

Local Lemma prefix_root {V E} (p : Prepared.t V E) done st :
  prefix_ready p done st -> prefix_ready p (1%positive :: done) st.
Proof.
  intro Hprefix. constructor.
  - exact (prefix_wf _ _ _ Hprefix).
  - intros n u Hget. destruct (prefix_sound _ _ _ Hprefix n u Hget) as [Hin Hrest].
    split; [now right|exact Hrest].
  - intros n Hn [Heq|Hin] Hnonroot; [congruence|].
    exact (prefix_total _ _ _ Hprefix n Hn Hin Hnonroot).
  - exact (prefix_links _ _ _ Hprefix).
  - exact (prefix_valid _ _ _ Hprefix).
Qed.

Local Lemma prefix_insert {V E} (p : Prepared.t V E) done st cutoff parent links' best :
  prefix_ready p done st ->
  Map.get positive_encoding cutoff (DomSemi.semis st) = None ->
  cutoff <> 1%positive ->
  Map.get positive_encoding cutoff (DomSemi.parents (DomSemi.ranked (DomSemi.compute p))) =
    Some parent ->
  DomLink.original links' = DomLink.original (DomSemi.links st) ->
  DomLinkProof.valid (DomLink.identity_value (DomSemi.semis st)) links' ->
  semidominator p best cutoff ->
  prefix_ready p (cutoff :: done)
    (DomSemi.State (Map.set positive_encoding cutoff best (DomSemi.semis st))
      (Cost.value (DomLink.link_c links' cutoff parent))).
Proof.
  intros Hprefix Hnone Hnonroot Hparent Horiginal Hvalid Hsemi.
  pose proof (prefix_wf _ _ _ Hprefix) as Hmap.
  assert (Hroot : Map.get positive_encoding cutoff (DomLink.original links') = None).
  { rewrite Horiginal, (prefix_links _ _ _ Hprefix cutoff), Hnone. reflexivity. }
  assert (Hrescore : DomLinkProof.valid
    (DomLink.identity_value (Map.set positive_encoding cutoff best (DomSemi.semis st))) links').
  { apply (DomLinkProof.rescore_valid (DomLink.identity_value (DomSemi.semis st))).
    - exact Hvalid.
    - intros v a Hget. rewrite !DomLink.identity_value_equation.
      rewrite Map.get_set_other; [reflexivity|exact positive_encoding_laws|exact Hmap|].
      congruence. }
  constructor; cbn [DomSemi.semis DomSemi.links].
  - now apply Map.wf_set.
  - intros n u Hget. destruct (Pos.eq_dec n cutoff) as [->|Hne].
    + rewrite Map.get_set_same in Hget by exact Hmap. injection Hget as <-.
      split; [now left|]. auto.
    + rewrite Map.get_set_other in Hget by
        (try exact positive_encoding_laws; try exact Hmap; exact Hne).
      destruct (prefix_sound _ _ _ Hprefix n u Hget) as [Hin Hrest].
      split; [now right|exact Hrest].
  - intros n Hn [Heq|Hin] Hnonroot'.
    + subst n. exists best. now apply Map.get_set_same.
    + destruct (prefix_total _ _ _ Hprefix n Hn Hin Hnonroot') as [u Hu].
      exists u. rewrite Map.get_set_other; [exact Hu|exact positive_encoding_laws|exact Hmap|].
      congruence.
  - intro n. rewrite DomLink.link_value. cbn [DomLink.original].
    destruct (Pos.eq_dec n cutoff) as [->|Hne].
    + rewrite !Map.get_set_same by
        first [exact Hmap|exact (DomLinkProof.original_wf _ _ Hvalid)].
      now rewrite Hparent.
    + rewrite !Map.get_set_other by
        first [exact positive_encoding_laws|exact Hmap|
          exact (DomLinkProof.original_wf _ _ Hvalid)|exact Hne].
      rewrite Horiginal. apply (prefix_links _ _ _ Hprefix).
  - now apply DomLinkProof.link_valid.
Qed.

(** One actual reverse-pass step proves and inserts the current nonroot's semidominator. *)
Theorem settle_correct {V E} (p : Prepared.t V E) done st cutoff :
  Prepared.ready p -> prefix_ready p done st ->
  DomPath.vertex (DomSemi.compute p) cutoff ->
  (forall n, DomPath.vertex (DomSemi.compute p) n -> (In n done <-> (cutoff < n)%positive)) ->
  prefix_ready p (cutoff :: done)
    (Cost.value (DomSemi.settle_c (DomSemi.ranked (DomSemi.compute p)) st cutoff)).
Proof.
  intros Hready Hprefix Hcutoff Hcut.
  rewrite DomSemi.settle_value.
  destruct (Map.get positive_encoding cutoff
    (DomSemi.parents (DomSemi.ranked (DomSemi.compute p)))) as [parent|] eqn:Hparent.
  - pose proof (prefix_values p done st cutoff Hprefix Hcut) as Hvalues.
    pose proof (prefix_forest p done st cutoff Hready Hprefix Hcut) as Hforest.
    pose proof (predecessors_correct p cutoff (DomSemi.semis st)
      (Index.find positive_encoding cutoff
        (DomSemi.predecessors (DomSemi.ranked (DomSemi.compute p))))
      Hready Hvalues Hcutoff (fun e source Hin => Hin) (DomSemi.links st) parent
      (prefix_valid _ _ _ Hprefix) Hforest
      (parent_candidate p cutoff parent Hready Hparent)) as Hfold.
    destruct (fold_left
      (fun acc eu => Cost.value (DomSemi.predecessor_c (DomSemi.semis st) acc (snd eu)))
      (Index.find positive_encoding cutoff
        (DomSemi.predecessors (DomSemi.ranked (DomSemi.compute p))))
      (DomSemi.links st, parent)) as [links' best].
    destruct Hfold as [Horiginal [Hvalid [Hbest [Hdecrease Hbounds]]]].
    apply (prefix_insert p done st cutoff parent links' best Hprefix).
    + destruct (Map.get positive_encoding cutoff (DomSemi.semis st)) as [u|] eqn:Hget;
        [|reflexivity].
      pose proof (proj1 (prefix_sound _ _ _ Hprefix cutoff u Hget)) as Hin.
      apply (proj1 (Hcut cutoff Hcutoff)) in Hin.
      exact (False_rect _ (Pos.lt_irrefl cutoff Hin)).
    + intro Heq. subst cutoff.
      rewrite (DomDfs.first_parent_none p Hready) in Hparent. discriminate.
    + exact Hparent.
    + exact Horiginal.
    + exact Hvalid.
    + exact (predecessors_minimum p cutoff (DomSemi.semis st) best
        Hready Hvalues Hbest Hbounds).
  - apply (proj1 (DomDfs.parent_none_iff p cutoff Hready Hcutoff)) in Hparent.
    subst cutoff. now apply prefix_root.
Qed.

Local Lemma before_head (xs : list positive) head v :
  In v xs -> before (head :: xs) head v.
Proof.
  intro Hin. apply in_split in Hin. destruct Hin as [pre [post Heq]].
  exists [], pre, post. cbn [app]. now rewrite Heq.
Qed.

Local Lemma before_tail (xs : list positive) head u v :
  before xs u v -> before (head :: xs) u v.
Proof.
  intros [pre [middle [post Heq]]].
  exists (head :: pre), middle, post. cbn [app]. now rewrite Heq.
Qed.

Local Lemma settlement_fold {V E} (p : Prepared.t V E) todo :
  Prepared.ready p ->
  (forall u v, before todo u v -> (v < u)%positive) ->
  forall done st,
  prefix_ready p done st ->
  (forall n, DomPath.vertex (DomSemi.compute p) n <-> In n done \/ In n todo) ->
  (forall u v, In u done -> In v todo -> (v < u)%positive) ->
  exists final_done,
    prefix_ready p final_done
      (fold_left (fun st w => Cost.value
        (DomSemi.settle_c (DomSemi.ranked (DomSemi.compute p)) st w)) todo st) /\
    forall n, DomPath.vertex (DomSemi.compute p) n -> In n final_done.
Proof.
  intro Hready. induction todo as [|cutoff rest IH]; intros Horder done st Hprefix Hcover Hsep.
  - exists done. split; [exact Hprefix|].
    intros n Hn. apply Hcover in Hn. destruct Hn as [Hin|Hin]; [exact Hin|contradiction].
  - assert (Hcutoff : DomPath.vertex (DomSemi.compute p) cutoff).
    { apply Hcover. right. now left. }
    assert (Hcut : forall n, DomPath.vertex (DomSemi.compute p) n ->
      (In n done <-> (cutoff < n)%positive)).
    { intros n Hn. split.
      - intro Hin. apply (Hsep n cutoff Hin). now left.
      - intro Hhigh. apply Hcover in Hn. destruct Hn as [Hin|[Heq|Hin]]; [exact Hin| |].
        + subst n. exact (False_rect _ (Pos.lt_irrefl cutoff Hhigh)).
        + pose proof (Horder cutoff n (before_head rest cutoff n Hin)) as Hlow.
          exact (False_rect _ (Pos.lt_irrefl cutoff (Pos.lt_trans _ _ _ Hhigh Hlow))). }
    cbn [fold_left]. apply (IH (fun u v Hbefore => Horder u v (before_tail rest cutoff u v Hbefore))
      (cutoff :: done)).
    + exact (settle_correct p done st cutoff Hready Hprefix Hcutoff Hcut).
    + intro n. rewrite Hcover. cbn [In]. tauto.
    + intros u v [Heq|Hin] Hv.
      * subst u. exact (Horder cutoff v (before_head rest cutoff v Hv)).
      * apply (Hsep u v Hin). now right.
Qed.

Local Lemma settled_prefix {V E} (p : Prepared.t V E) :
  Prepared.ready p ->
  exists done, prefix_ready p done (DomSemi.settled (DomSemi.compute p)) /\
    forall n, DomPath.vertex (DomSemi.compute p) n -> In n done.
Proof.
  intro Hready. rewrite DomSemi.settled_equation.
  apply (settlement_fold p (DomSemi.reverse_order (DomSemi.ranked (DomSemi.compute p)))
    Hready (fun u v Hbefore => DomDfs.settlement_decreases p u v Hready Hbefore) []).
  - apply prefix_initial.
  - intro n. rewrite (DomDfs.vertex_member p n Hready). cbn [In]. tauto.
  - intros u v Hin. contradiction.
Qed.

(** The actual single shared settlement stores exactly every discovered nonroot's least high-path start. *)
Theorem semidominators_exact {V E} (p : Prepared.t V E) n u :
  Prepared.ready p ->
  (Map.get positive_encoding n (DomSemi.semis (DomSemi.settled (DomSemi.compute p))) = Some u <->
    DomPath.vertex (DomSemi.compute p) n /\ n <> 1%positive /\ semidominator p u n).
Proof.
  intro Hready. destruct (settled_prefix p Hready) as [done [Hprefix Hall]].
  split.
  - intro Hget.
    destruct (prefix_sound _ _ _ Hprefix n u Hget) as [Hin [Hnonroot Hsemi]].
    split; [|auto]. exact (proj2 (candidate_vertices p u n (proj1 Hsemi))).
  - intros [Hn [Hnonroot Hsemi]].
    destruct (prefix_total _ _ _ Hprefix n Hn (Hall n Hn) Hnonroot) as [v Hget].
    pose proof (proj2 (proj2 (prefix_sound _ _ _ Hprefix n v Hget))) as Hsemi'.
    pose proof (semidominator_unique p u v n Hsemi Hsemi') as Heq. now subst v.
Qed.

(** Identity lookup of the actual settled map supplies the proved minimum at every discovered nonroot. *)
Theorem semidominator_value {V E} (p : Prepared.t V E) n :
  Prepared.ready p -> DomPath.vertex (DomSemi.compute p) n -> n <> 1%positive ->
  semidominator p (DomLink.identity_value (DomSemi.semis (DomSemi.settled (DomSemi.compute p))) n) n.
Proof.
  intros Hready Hn Hnonroot.
  destruct (settled_prefix p Hready) as [done [Hprefix Hall]].
  destruct (prefix_total _ _ _ Hprefix n Hn (Hall n Hn) Hnonroot) as [u Hget].
  rewrite DomLink.identity_value_equation, Hget.
  exact (proj2 (proj2 (prefix_sound _ _ _ Hprefix n u Hget))).
Qed.

(** Every nonroot semidominator is an actual strict DFS ancestor of its endpoint. *)
Theorem semidominator_ancestor {V E} (p : Prepared.t V E) u n :
  Prepared.ready p -> n <> 1%positive -> semidominator p u n -> DomDfs.ancestor p u n.
Proof.
  intros Hready Hnonroot Hsemi.
  pose proof (semidominator_bound p u n Hready Hnonroot Hsemi) as Hlt.
  pose proof (proj1 (candidate_vertices p u n (proj1 Hsemi))) as Hu.
  destruct Hsemi as [[es Hpath] Hminimum].
  apply (bounded_region p u u es n Hready Hu).
  - eapply high_as_bounded; [exact Hpath| |now apply Pos.lt_le_incl].
    intros x Hx. apply Pos.lt_le_incl. eapply Pos.lt_trans; eassumption.
  - apply rt_refl.
Qed.

End DomSemiExact.
