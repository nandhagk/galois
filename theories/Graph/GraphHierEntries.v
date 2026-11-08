(** * Witnesses in the hierarchy entry index

    Each inserted header retains its actual root or cross-component edge witness.
    For example, an irreducible component can choose either witnessed entry without assuming dominance.
    Builds on: GraphHier, GraphHierFacts and the public SCC specification. *)

From Stdlib Require Import List PArith.
From Galois.Base Require Import BaseEncoding BaseMap BaseTacticsInv.
From Galois.Graph Require Import GraphPrepared GraphVisitor GraphSearchSpec GraphSccSpec
  GraphHierSpec GraphHier GraphHierFacts GraphSearchInvariant.
Import List.ListNotations.

Module HierEntries.

(** A candidate belongs to its actual owner and satisfies entry for that same indexed component. *)
Definition candidate {V E} (p : Prepared.t V E) scope roots r i h :=
  Map.get positive_encoding h (Scc.comp_of r) = Some i /\
  forall c, nth_error (Scc.components r) (Nat.pred (Pos.to_nat i)) = Some c ->
    Hier.entry p scope roots c h.

(** Every stored header has a witnessed entry in the exact supplied SCC partition. *)
Record correct {V E} (p : Prepared.t V E) scope roots r index : Prop := {
  storage : Map.wf positive_encoding index;
  rows : forall i h, Map.get positive_encoding i index = Some h ->
    candidate p scope roots r i h
}.

Local Lemma owner_member {V E} (p : Prepared.t V E) scope roots r v i c :
  Scc.exact p scope roots r ->
  Map.get positive_encoding v (Scc.comp_of r) = Some i ->
  nth_error (Scc.components r) (Nat.pred (Pos.to_nat i)) = Some c -> In v c.
Proof.
  intros Hexact Howner Hcomponent.
  apply (Scc.owners_exact _ _ _ _ Hexact) in Howner.
  destruct Howner as [actual [Hactual Hin]].
  rewrite Hcomponent in Hactual. inversion Hactual; subst actual. exact Hin.
Qed.

(** Empty setup contains no unwitnessed header row. *)
Theorem empty_correct {V E} (p : Prepared.t V E) scope roots r :
  correct p scope roots r Map.empty.
Proof.
  constructor; [apply Map.wf_empty|].
  intros i h Hget. rewrite Map.get_empty in Hget. discriminate.
Qed.

(** A witnessed offer keeps every stored witness and can add only its own candidate. *)
Theorem offer_correct {V E} (p : Prepared.t V E) scope roots r index i h :
  correct p scope roots r index -> candidate p scope roots r i h ->
    correct p scope roots r (HierRun.offer i h index).
Proof.
  intros Hcorrect Hcandidate. rewrite HierRun.offer_equation.
  destruct (Map.get positive_encoding i index); [exact Hcorrect|].
  constructor; [apply Map.wf_set, (storage _ _ _ _ _ Hcorrect)|].
  intros j v Hget. destruct (Pos.eq_dec j i) as [->|Hne].
  - rewrite Map.get_set_same in Hget by exact (storage _ _ _ _ _ Hcorrect).
    inversion Hget; subst v. exact Hcandidate.
  - rewrite (Map.get_set_other positive_encoding positive_encoding_laws) in Hget
      by (try exact (storage _ _ _ _ _ Hcorrect); exact Hne).
    exact (rows _ _ _ _ _ Hcorrect j v Hget).
Qed.

(** Root occurrences offer an actual entry of their actual component. *)
Theorem root_correct {V E} (p : Prepared.t V E) scope roots r index v :
  Scc.exact p scope roots r -> In v roots -> correct p scope roots r index ->
    correct p scope roots r (HierRun.root_entry (Scc.comp_of r) index v).
Proof.
  intros Hexact Hroot Hcorrect. rewrite HierRun.root_entry_equation.
  destruct (Map.get positive_encoding v (Scc.comp_of r)) as [i|] eqn:Howner;
    [|exact Hcorrect].
  apply offer_correct; [exact Hcorrect|]. split; [exact Howner|].
  intros c Hcomponent. split.
  - exact (owner_member p scope roots r v i c Hexact Howner Hcomponent).
  - now left.
Qed.

Local Lemma cross_candidate {V E} (p : Prepared.t V E) scope roots r u e v i j :
  Scc.exact p scope roots r -> Search.scoped_reachable p scope roots u ->
  Prepared.arc p u e v ->
  Map.get positive_encoding u (Scc.comp_of r) = Some i ->
  Map.get positive_encoding v (Scc.comp_of r) = Some j -> i <> j ->
    candidate p scope roots r j v.
Proof.
  intros Hexact Hreach Harc Hsource Htarget Hne. split; [exact Htarget|].
  intros c Hcomponent. split.
  - exact (owner_member p scope roots r v j c Hexact Htarget Hcomponent).
  - right. exists u, e. split; [exact Hreach|]. split; [|exact Harc].
    intro Hu. assert (Hother : Map.get positive_encoding u (Scc.comp_of r) = Some j).
    { apply (Scc.owners_exact _ _ _ _ Hexact). exists c. auto. }
    rewrite Hsource in Hother. inversion Hother. contradiction.
Qed.

(** Cross-component occurrences offer their real target entry and keep all earlier witnesses. *)
Theorem edge_correct {V E} (p : Prepared.t V E) scope roots r index u e v :
  Scc.exact p scope roots r -> Search.scoped_reachable p scope roots u ->
  Prepared.arc p u e v -> correct p scope roots r index ->
    correct p scope roots r (HierRun.edge_entry (Scc.comp_of r)
      (Map.get positive_encoding u (Scc.comp_of r)) index v).
Proof.
  intros Hexact Hreach Harc Hcorrect. rewrite HierRun.edge_entry_equation.
  destruct (Map.get positive_encoding u (Scc.comp_of r)) as [i|] eqn:Hsource;
    destruct (Map.get positive_encoding v (Scc.comp_of r)) as [j|] eqn:Htarget;
    try exact Hcorrect.
  destruct (Map.code_compare i j) eqn:Hcompare; [exact Hcorrect| |].
  all: apply offer_correct; [exact Hcorrect|].
  all: apply (cross_candidate p scope roots r u e v i j Hexact Hreach Harc Hsource Htarget).
  all: intro Heq; subst j; pose proof (proj2 (Map.code_compare_eq i i) eq_refl); congruence.
Qed.

Local Lemma edge_fold_correct {V E} (p : Prepared.t V E) scope roots r u es index :
  Scc.exact p scope roots r -> Search.scoped_reachable p scope roots u ->
  (forall e v, In (e, v) es -> Prepared.arc p u e v) ->
  correct p scope roots r index ->
  correct p scope roots r (fold_left (fun index eb => HierRun.edge_entry (Scc.comp_of r)
    (Map.get positive_encoding u (Scc.comp_of r)) index (snd eb)) es index).
Proof.
  intros Hexact Hreach Harcs Hcorrect.
  apply fold_left_invariant; [exact Hcorrect|].
  intros current [e v] Hin Hcurrent. cbn [snd].
  exact (edge_correct p scope roots r current u e v Hexact Hreach (Harcs e v Hin) Hcurrent).
Qed.

(** A member's setup pass retains witnessed entries for every inspected outgoing occurrence. *)
Theorem vertex_correct {V E} (p : Prepared.t V E) scope roots r index u :
  Prepared.ready p -> Scc.exact p scope roots r ->
  Search.scoped_reachable p scope roots u -> correct p scope roots r index ->
    correct p scope roots r (HierRun.vertex_entries p (Scc.comp_of r) index u).
Proof.
  intros Hready Hexact Hreach Hcorrect. rewrite HierRun.vertex_entries_equation.
  apply edge_fold_correct; [exact Hexact|exact Hreach| |exact Hcorrect].
  intros e v Hin.
  assert (Hvalid : Prepared.valid_id p u).
  { destruct Hreach as [root [es [_ Hpath]]].
    exact (proj1 (HierFacts.path_target p scope root es u Hpath)). }
  exact (proj1 (SearchInvariant.successor_arc p u e v Hready Hvalid Hin)).
Qed.

Local Lemma root_fold_correct {V E} (p : Prepared.t V E) scope roots r xs index :
  Scc.exact p scope roots r -> incl xs roots -> correct p scope roots r index ->
  correct p scope roots r (fold_left (HierRun.root_entry (Scc.comp_of r)) xs index).
Proof.
  intros Hexact Hincl Hcorrect.
  apply fold_left_invariant; [exact Hcorrect|].
  intros current v Hin Hcurrent. apply root_correct;
    [exact Hexact|exact (Hincl v Hin)|exact Hcurrent].
Qed.

Local Lemma member_fold_correct {V E} (p : Prepared.t V E) scope roots r xs index :
  Prepared.ready p -> Scc.exact p scope roots r ->
  (forall u, In u xs -> Search.scoped_reachable p scope roots u) ->
  correct p scope roots r index ->
  correct p scope roots r (fold_left (HierRun.vertex_entries p (Scc.comp_of r)) xs index).
Proof.
  intros Hready Hexact Hreach Hcorrect.
  apply fold_left_invariant; [exact Hcorrect|].
  intros current u Hin Hcurrent.
  apply vertex_correct; [exact Hready|exact Hexact|exact (Hreach u Hin)|exact Hcurrent].
Qed.

Local Lemma component_fold_correct {V E} (p : Prepared.t V E) scope roots r cs index :
  Prepared.ready p -> Scc.exact p scope roots r ->
  (forall c u, In c cs -> In u c -> Search.scoped_reachable p scope roots u) ->
  correct p scope roots r index ->
  correct p scope roots r
    (fold_left (HierRun.component_entries p (Scc.comp_of r))
      cs index).
Proof.
  intros Hready Hexact Hreach Hcorrect.
  apply fold_left_invariant; [exact Hcorrect|].
  intros current c Hin Hcurrent. rewrite HierRun.component_entries_equation.
  apply member_fold_correct; [exact Hready|exact Hexact| |exact Hcurrent].
  intros u Hu. exact (Hreach c u Hin Hu).
Qed.

(** Every final entry row retains a root or outside-edge witness in its exact actual SCC. *)
Theorem entries_correct {V E} (p : Prepared.t V E) scope roots r :
  Prepared.ready p -> Scc.exact p scope roots r ->
    correct p scope roots r (HierRun.entries p roots r).
Proof.
  intros Hready Hexact. rewrite HierRun.entries_equation.
  apply component_fold_correct; [exact Hready|exact Hexact| |].
  - intros c u Hc Hu. apply (Scc.partition_complete _ _ _ _ Hexact), in_concat.
    exists c. auto.
  - apply root_fold_correct; [exact Hexact|intros v Hin; exact Hin|apply empty_correct].
Qed.

Definition extends (first last : Map.t positive positive) :=
  forall i h, Map.get positive_encoding i first = Some h ->
    Map.get positive_encoding i last = Some h.

(** Offering a candidate never replaces an already stored header. *)
Theorem offer_extends {V E} (p : Prepared.t V E) scope roots r index i h :
  correct p scope roots r index -> extends index (HierRun.offer i h index).
Proof.
  intros Hcorrect j v Hget. rewrite HierRun.offer_equation.
  destruct (Map.get positive_encoding i index) eqn:Hrow; [exact Hget|].
  destruct (Pos.eq_dec j i) as [->|Hne]; [congruence|].
  rewrite (Map.get_set_other positive_encoding positive_encoding_laws)
    by (try exact (storage _ _ _ _ _ Hcorrect); exact Hne).
  exact Hget.
Qed.

Local Lemma root_extends {V E} (p : Prepared.t V E) scope roots r index v :
  correct p scope roots r index ->
    extends index (HierRun.root_entry (Scc.comp_of r) index v).
Proof.
  intro Hcorrect. rewrite HierRun.root_entry_equation.
  destruct (Map.get positive_encoding v (Scc.comp_of r));
    [now apply (offer_extends p scope roots r)|intros i h Hget; exact Hget].
Qed.

Local Lemma edge_extends {V E} (p : Prepared.t V E) scope roots r index source v :
  correct p scope roots r index ->
    extends index (HierRun.edge_entry (Scc.comp_of r) source index v).
Proof.
  intro Hcorrect. rewrite HierRun.edge_entry_equation.
  destruct source as [i|]; destruct (Map.get positive_encoding v (Scc.comp_of r)) as [j|];
    try (intros key header Hget; exact Hget).
  destruct (Map.code_compare i j); try (intros key header Hget; exact Hget).
  all: now apply (offer_extends p scope roots r).
Qed.

Local Lemma fold_rows {V E A} (p : Prepared.t V E) scope roots r
    (step : Map.t positive positive -> A -> Map.t positive positive) xs index :
  correct p scope roots r index ->
  (forall current x, In x xs -> correct p scope roots r current ->
    correct p scope roots r (step current x) /\ extends current (step current x)) ->
  correct p scope roots r (fold_left step xs index) /\ extends index (fold_left step xs index).
Proof.
  intros Hcorrect Hstep. split.
  - apply fold_left_invariant; [exact Hcorrect|].
    intros current x Hin Hcurrent. exact (proj1 (Hstep current x Hin Hcurrent)).
  - intros i h Hget.
    pose proof (fold_left_invariant step xs index
      (fun current => correct p scope roots r current /\
        Map.get positive_encoding i current = Some h)) as Hfold.
    assert (Hresult : correct p scope roots r (fold_left step xs index) /\
      Map.get positive_encoding i (fold_left step xs index) = Some h).
    { apply Hfold; [exact (conj Hcorrect Hget)|].
      intros current x Hin [Hcurrent Hrow].
      destruct (Hstep current x Hin Hcurrent) as [Hnext Hext].
      split; [exact Hnext|exact (Hext i h Hrow)]. }
    exact (proj2 Hresult).
Qed.

Local Lemma vertex_step {V E} (p : Prepared.t V E) scope roots r index u :
  Prepared.ready p -> Scc.exact p scope roots r ->
  Search.scoped_reachable p scope roots u -> correct p scope roots r index ->
  correct p scope roots r (HierRun.vertex_entries p (Scc.comp_of r) index u) /\
    extends index (HierRun.vertex_entries p (Scc.comp_of r) index u).
Proof.
  intros Hready Hexact Hreach Hcorrect. rewrite HierRun.vertex_entries_equation.
  apply (fold_rows p scope roots r); [exact Hcorrect|].
  intros current [e v] Hin Hcurrent. split.
  - apply (edge_correct p scope roots r current u e v Hexact Hreach); [|exact Hcurrent].
    assert (Hvalid : Prepared.valid_id p u).
    { destruct Hreach as [root [es [_ Hpath]]].
      exact (proj1 (HierFacts.path_target p scope root es u Hpath)). }
    exact (proj1 (SearchInvariant.successor_arc p u e v Hready Hvalid Hin)).
  - exact (edge_extends p scope roots r current
      (Map.get positive_encoding u (Scc.comp_of r)) v Hcurrent).
Qed.

Local Lemma component_step {V E} (p : Prepared.t V E) scope roots r index c :
  Prepared.ready p -> Scc.exact p scope roots r ->
  (forall u, In u c -> Search.scoped_reachable p scope roots u) ->
  correct p scope roots r index ->
  correct p scope roots r (HierRun.component_entries p (Scc.comp_of r) index c) /\
    extends index (HierRun.component_entries p (Scc.comp_of r) index c).
Proof.
  intros Hready Hexact Hreach Hcorrect. rewrite HierRun.component_entries_equation.
  apply (fold_rows p scope roots r); [exact Hcorrect|].
  intros current u Hin Hcurrent.
  exact (vertex_step p scope roots r current u Hready Hexact (Hreach u Hin) Hcurrent).
Qed.

Local Lemma fold_trigger {V E A} (p : Prepared.t V E) scope roots r
    (step : Map.t positive positive -> A -> Map.t positive positive) xs index x i :
  correct p scope roots r index -> In x xs ->
  (forall current y, In y xs -> correct p scope roots r current ->
    correct p scope roots r (step current y) /\ extends current (step current y)) ->
  (forall current, correct p scope roots r current ->
    exists h, Map.get positive_encoding i (step current x) = Some h) ->
  exists h, Map.get positive_encoding i (fold_left step xs index) = Some h.
Proof.
  intros Hcorrect Hin Hstep Htrigger.
  apply in_split in Hin. destruct Hin as [first [last Hsplit]].
  assert (Hfirst : correct p scope roots r (fold_left step first index)).
  { assert (Hsteps : forall current y, In y first -> correct p scope roots r current ->
        correct p scope roots r (step current y) /\ extends current (step current y)).
    { intros current y Hy Hcurrent. apply Hstep; [rewrite Hsplit; apply in_or_app; now left|].
      exact Hcurrent. }
    exact (proj1 (fold_rows p scope roots r step first index Hcorrect Hsteps)). }
  destruct (Htrigger _ Hfirst) as [h Hrow].
  destruct (Hstep _ x ltac:(rewrite Hsplit; apply in_or_app; right; now left) Hfirst)
    as [Hnext Hext].
  assert (Hlast : extends (step (fold_left step first index) x)
    (fold_left step last (step (fold_left step first index) x))).
  { assert (Hsteps : forall current y, In y last -> correct p scope roots r current ->
        correct p scope roots r (step current y) /\ extends current (step current y)).
    { intros current y Hy Hcurrent. apply Hstep;
        [rewrite Hsplit; apply in_or_app; right; now right|exact Hcurrent]. }
    exact (proj2 (fold_rows p scope roots r step last _ Hnext Hsteps)). }
  exists h. rewrite Hsplit, fold_left_app. exact (Hlast i h Hrow).
Qed.

(** Every offered owner has a present row, whether newly inserted or retained. *)
Theorem offer_present {V E} (p : Prepared.t V E) scope roots r index i v :
  correct p scope roots r index ->
    exists h, Map.get positive_encoding i (HierRun.offer i v index) = Some h.
Proof.
  intro Hcorrect. rewrite HierRun.offer_equation.
  destruct (Map.get positive_encoding i index) as [h|] eqn:Hrow.
  - now exists h.
  - exists v. apply Map.get_set_same. exact (storage _ _ _ _ _ Hcorrect).
Qed.

Local Lemma edges_present {V E} (p : Prepared.t V E) scope roots r index u e v i j :
  Prepared.ready p -> Scc.exact p scope roots r ->
  Search.scoped_reachable p scope roots u ->
  Map.get positive_encoding u (Scc.comp_of r) = Some i ->
  Map.get positive_encoding v (Scc.comp_of r) = Some j -> i <> j ->
  In (e, v) (Prepared.succ_edges p u) -> correct p scope roots r index ->
  exists h, Map.get positive_encoding j
    (HierRun.vertex_entries p (Scc.comp_of r) index u) = Some h.
Proof.
  intros Hready Hexact Hreach Hsource Htarget Hne Hin Hcorrect.
  rewrite HierRun.vertex_entries_equation.
  apply (fold_trigger p scope roots r _ _ index (e, v) j Hcorrect Hin).
  - intros current [edge target] Hedge Hcurrent. split.
    + apply (edge_correct p scope roots r current u edge target Hexact Hreach); [|exact Hcurrent].
      assert (Hvalid : Prepared.valid_id p u).
      { destruct Hreach as [root [es [_ Hpath]]].
        exact (proj1 (HierFacts.path_target p scope root es u Hpath)). }
      exact (proj1 (SearchInvariant.successor_arc p u edge target Hready Hvalid Hedge)).
    + exact (edge_extends p scope roots r current
        (Map.get positive_encoding u (Scc.comp_of r)) target Hcurrent).
  - intros current Hcurrent. cbn [snd]. rewrite HierRun.edge_entry_equation, Hsource, Htarget.
    destruct (Map.code_compare i j) eqn:Hcompare.
    + exfalso. apply Hne, Map.code_compare_eq, Hcompare.
    + exact (offer_present p scope roots r current j v Hcurrent).
    + exact (offer_present p scope roots r current j v Hcurrent).
Qed.

Local Lemma member_reachable {V E} (p : Prepared.t V E) scope roots r c u :
  Scc.exact p scope roots r -> In c (Scc.components r) -> In u c ->
    Search.scoped_reachable p scope roots u.
Proof.
  intros Hexact Hc Hu. apply (Scc.partition_complete _ _ _ _ Hexact), in_concat.
  exists c. auto.
Qed.

Local Lemma root_row_present {V E} (p : Prepared.t V E) scope roots r v i :
  Prepared.ready p -> Scc.exact p scope roots r -> In v roots ->
  Map.get positive_encoding v (Scc.comp_of r) = Some i ->
    exists h, Map.get positive_encoding i (HierRun.entries p roots r) = Some h.
Proof.
  intros Hready Hexact Hroot Howner.
  assert (Hseed : correct p scope roots r
    (fold_left (HierRun.root_entry (Scc.comp_of r)) roots Map.empty)).
  { apply root_fold_correct; [exact Hexact|intros x Hin; exact Hin|apply empty_correct]. }
  assert (Hpresent : exists h, Map.get positive_encoding i
    (fold_left (HierRun.root_entry (Scc.comp_of r)) roots Map.empty) = Some h).
  { apply (fold_trigger p scope roots r _ roots Map.empty v i (empty_correct _ _ _ _) Hroot).
    - intros current x Hin Hcurrent. split.
      + exact (root_correct p scope roots r current x Hexact Hin Hcurrent).
      + exact (root_extends p scope roots r current x Hcurrent).
    - intros current Hcurrent. rewrite HierRun.root_entry_equation, Howner.
      exact (offer_present p scope roots r current i v Hcurrent). }
  destruct Hpresent as [h Hrow]. exists h. rewrite HierRun.entries_equation.
  assert (Hsteps : forall current c, In c (Scc.components r) ->
    correct p scope roots r current ->
    correct p scope roots r (HierRun.component_entries p (Scc.comp_of r) current c) /\
      extends current (HierRun.component_entries p (Scc.comp_of r) current c)).
  { intros current c Hc Hcurrent. apply component_step; [exact Hready|exact Hexact| |exact Hcurrent].
    intros u Hu. exact (member_reachable p scope roots r c u Hexact Hc Hu). }
  exact (proj2 (fold_rows p scope roots r _ (Scc.components r) _ Hseed Hsteps) i h Hrow).
Qed.

Local Lemma cross_row_present {V E} (p : Prepared.t V E) scope roots r u e v i j :
  Prepared.ready p -> Scc.exact p scope roots r ->
  Search.scoped_reachable p scope roots u -> Prepared.arc p u e v ->
  Map.get positive_encoding u (Scc.comp_of r) = Some i ->
  Map.get positive_encoding v (Scc.comp_of r) = Some j -> i <> j ->
    exists h, Map.get positive_encoding j (HierRun.entries p roots r) = Some h.
Proof.
  intros Hready Hexact Hreach Harc Hsource Htarget Hne.
  assert (Hdomain : In u (concat (Scc.components r))) by
    (apply (Scc.partition_complete _ _ _ _ Hexact); exact Hreach).
  apply in_concat in Hdomain. destruct Hdomain as [c [Hc Hu]].
  rewrite HierRun.entries_equation.
  apply (fold_trigger p scope roots r _ (Scc.components r) _ c j).
  - apply root_fold_correct; [exact Hexact|intros x Hin; exact Hin|apply empty_correct].
  - exact Hc.
  - intros current d Hd Hcurrent. apply component_step; [exact Hready|exact Hexact| |exact Hcurrent].
    intros x Hx. exact (member_reachable p scope roots r d x Hexact Hd Hx).
  - intros current Hcurrent. rewrite HierRun.component_entries_equation.
    apply (fold_trigger p scope roots r _ c current u j Hcurrent Hu).
    + intros index x Hx Hindex. apply vertex_step; [exact Hready|exact Hexact| |exact Hindex].
      exact (member_reachable p scope roots r c x Hexact Hc Hx).
    + intros index Hindex.
      apply (edges_present p scope roots r index u e v i j Hready Hexact Hreach
        Hsource Htarget Hne); [|exact Hindex].
      exact (SearchInvariant.arc_successor p u e v Hready Harc).
Qed.

Local Lemma path_entry {V E} (p : Prepared.t V E) scope roots c u es v :
  Prepared.ready p -> Search.scoped_reachable p scope roots u ->
  Search.scoped_path p scope u es v -> In v c ->
    In u c \/ exists h, Hier.entry p scope roots c h.
Proof.
  intros Hready Hreach Hpath. revert Hreach.
  induction Hpath as [v Hv Ha|u e v es z Hu Ha Harc Htail IH]; intros Hreach Hend.
  - now left.
  - destruct (in_dec Pos.eq_dec u c) as [Hin|Houtside]; [now left|].
    destruct (in_dec Pos.eq_dec v c) as [Hin|Houtsidev].
    + right. exists v. split; [exact Hin|right].
      exists u, e. auto.
    + assert (Hallowed : Scope.admits scope v = true) by (destruct Htail; assumption).
      destruct (IH (HierFacts.reachable_step p scope roots u e v (proj1 Hready)
        Hreach Harc Hallowed) Hend) as [Hin|Hentry].
      * contradiction.
      * now right.
Qed.

(** Every nonempty component containing a rooted reachable vertex has an actual entry witness. *)
Theorem component_entry {V E} (p : Prepared.t V E) scope roots c v :
  Prepared.ready p -> In v c -> Search.scoped_reachable p scope roots v ->
    exists h, Hier.entry p scope roots c h.
Proof.
  intros Hready Hv [root [es [Hroot Hpath]]].
  assert (Hreach : Search.scoped_reachable p scope roots root).
  { exists root, []. split; [exact Hroot|].
    assert (Hsource : Prepared.valid_id p root /\ Scope.admits scope root = true)
      by (destruct Hpath; auto).
    apply Search.scoped_nil; tauto. }
  destruct (path_entry p scope roots c root es v Hready Hreach Hpath Hv)
    as [Hinside|Hentry].
  - exists root. split; [exact Hinside|now left].
  - exact Hentry.
Qed.

Local Lemma reachable_owner {V E} (p : Prepared.t V E) scope roots r v :
  Scc.exact p scope roots r -> Search.scoped_reachable p scope roots v ->
    exists i, Map.get positive_encoding v (Scc.comp_of r) = Some i.
Proof.
  intros Hexact Hreach. apply (Scc.partition_complete _ _ _ _ Hexact) in Hreach.
  apply in_concat in Hreach. destruct Hreach as [c [Hc Hv]].
  apply In_nth_error in Hc. destruct Hc as [n Hnth].
  exists (Pos.of_succ_nat n). apply (Scc.owners_exact _ _ _ _ Hexact).
  exists c. rewrite SuccNat2Pos.id_succ. exact (conj Hnth Hv).
Qed.

(** Every actual SCC position receives a witnessed entry row in the one setup pass. *)
Theorem entries_complete {V E} (p : Prepared.t V E) scope roots r i c :
  Prepared.ready p -> Scc.exact p scope roots r ->
  nth_error (Scc.components r) (Nat.pred (Pos.to_nat i)) = Some c ->
    exists h, Map.get positive_encoding i (HierRun.entries p roots r) = Some h.
Proof.
  intros Hready Hexact Hnth.
  assert (Hc : In c (Scc.components r)) by (now apply nth_error_In in Hnth).
  pose proof (proj1 (Forall_forall _ _) (Scc.components_exact _ _ _ _ Hexact) c Hc)
    as Hblock.
  destruct Hblock as [Hnonempty [Hnodup [Hreach Hmutual]]].
  destruct c as [|v rest]; [contradiction|].
  destruct (component_entry p scope roots (v :: rest) v Hready
    (or_introl eq_refl) (Hreach v (or_introl eq_refl))) as [h [Hh Hentry]].
  assert (Htarget : Map.get positive_encoding h (Scc.comp_of r) = Some i).
  { apply (Scc.owners_exact _ _ _ _ Hexact). exists (v :: rest). auto. }
  destruct Hentry as [Hroot|[u [e [Hsource [Houtside Harc]]]]].
  - exact (root_row_present p scope roots r h i Hready Hexact Hroot Htarget).
  - destruct (reachable_owner p scope roots r u Hexact Hsource) as [j Howner].
    apply (cross_row_present p scope roots r u e h j i Hready Hexact Hsource Harc
      Howner Htarget).
    intro Heq. subst j. apply Houtside.
    exact (owner_member p scope roots r u i (v :: rest) Hexact Howner Hnth).
Qed.

(** A listed component has its actual one-based owner for every one of its members. *)
Theorem component_owner {V E} (p : Prepared.t V E) scope roots r c :
  Scc.exact p scope roots r -> In c (Scc.components r) ->
  exists i, nth_error (Scc.components r) (Nat.pred (Pos.to_nat i)) = Some c /\
    forall v, In v c -> Map.get positive_encoding v (Scc.comp_of r) = Some i.
Proof.
  intros Hexact Hc. apply In_nth_error in Hc. destruct Hc as [n Hnth].
  exists (Pos.of_succ_nat n). rewrite SuccNat2Pos.id_succ. split; [exact Hnth|].
  intros v Hv. apply (Scc.owners_exact _ _ _ _ Hexact).
  exists c. rewrite SuccNat2Pos.id_succ. exact (conj Hnth Hv).
Qed.

(** The actual ready-component header lookup selects a member satisfying the fixed entry condition. *)
Theorem selection_entry {V E} (p : Prepared.t V E) scope roots r c v :
  Prepared.ready p -> Scc.exact p scope roots r ->
  In c (Scc.components r) -> In v c ->
  exists i h body,
    Map.get positive_encoding v (Scc.comp_of r) = Some i /\
    Map.get positive_encoding i (HierRun.entries p roots r) = Some h /\
    HierRun.select (Some h) c = Some (h, body) /\
    Hier.entry p scope roots c h.
Proof.
  intros Hready Hexact Hc Hv.
  destruct (component_owner p scope roots r c Hexact Hc) as [i [Hnth Howners]].
  destruct (entries_complete p scope roots r i c Hready Hexact Hnth) as [h Hrow].
  pose proof (entries_correct p scope roots r Hready Hexact) as Hcorrect.
  destruct (rows _ _ _ _ _ Hcorrect i h Hrow) as [_ Hcandidate].
  specialize (Hcandidate c Hnth).
  destruct (HierRun.select_preferred h c (proj1 Hcandidate)) as [body Hselected].
  exists i, h, body. split; [exact (Howners v Hv)|].
  split; [exact Hrow|]. exact (conj Hselected Hcandidate).
Qed.

End HierEntries.
