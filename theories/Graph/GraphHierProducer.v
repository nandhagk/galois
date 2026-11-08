(** * Exactness of the actual recursive hierarchy

    Ready SCC partitions and witnessed entry selection prove the same producer's recursive forest.
    For example, each cyclic body uses the actual SCCs computed after deleting its selected header.
    Builds on: GraphHierEntries, GraphHierStructure, GraphHierTransport and GraphTarjanExact. *)

From Stdlib Require Import List Bool PArith Arith Lia Permutation Wf_nat.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet.
From Galois.Graph Require Import GraphPrepared GraphVisitor GraphSearchSpec GraphSearchInvariant
  GraphSccSpec GraphHierSpec GraphHier GraphHierFacts GraphHierEntries GraphHierStructure
  GraphHierTransport GraphTarjan GraphTarjanExact GraphTarjanState.
Import List.ListNotations.
Local Open Scope nat_scope.

Module HierProducer.

Local Lemma block_permutation {V E} (p : Prepared.t V E) scope roots first last :
  Permutation first last -> Scc.block p scope roots first -> Scc.block p scope roots last.
Proof.
  intros Hperm [Hnonempty [Hnodup [Hreach Hmutual]]]. split.
  - intro Hnil. subst last. apply Hnonempty, Permutation_nil, Permutation_sym, Hperm.
  - split; [exact (Permutation_NoDup Hperm Hnodup)|]. split.
    + intros u Hu. apply Hreach. exact (Permutation_in u (Permutation_sym Hperm) Hu).
    + intros u v Hu.
      specialize (Hmutual u v (Permutation_in u (Permutation_sym Hperm) Hu)).
      rewrite <- Hmutual. split; intro Hv.
      * exact (Permutation_in v (Permutation_sym Hperm) Hv).
      * exact (Permutation_in v Hperm Hv).
Qed.

Local Lemma entry_permutation {V E} (p : Prepared.t V E) scope roots first last h :
  Permutation first last -> Hier.entry p scope roots first h ->
    Hier.entry p scope roots last h.
Proof.
  intros Hperm [Hh [Hroot|[u [e [Hreach [Houtside Harc]]]]]].
  - split; [exact (Permutation_in h Hperm Hh)|now left].
  - split; [exact (Permutation_in h Hperm Hh)|right].
    exists u, e. split; [exact Hreach|]. split; [|exact Harc].
    intro Hin. exact (Houtside (Permutation_in u (Permutation_sym Hperm) Hin)).
Qed.

Local Lemma component_block {V E} (p : Prepared.t V E) scope roots r c :
  Scc.exact p scope roots r -> In c (Scc.components r) -> Scc.block p scope roots c.
Proof.
  intros Hexact Hin. exact (proj1 (Forall_forall _ _)
    (Scc.components_exact _ _ _ _ Hexact) c Hin).
Qed.

Local Lemma block_domain {V E} (p : Prepared.t V E) scope roots c v :
  Scc.block p scope roots c -> In v c ->
    Prepared.valid_id p v /\ Scope.admits scope v = true.
Proof.
  intros [_ [_ [Hreach _]]] Hin.
  destruct (Hreach v Hin) as [root [es [_ Hpath]]].
  exact (HierFacts.path_target p scope root es v Hpath).
Qed.

Local Lemma selected_body_domain {V E} (p : Prepared.t V E) scope roots c preferred h body :
  Scc.block p scope roots c -> HierRun.select preferred c = Some (h, body) ->
  NoDup body /\ forall v, In v body ->
    Prepared.valid_id p v /\ Scope.admits (HierRun.child_scope scope h body) v = true.
Proof.
  intros Hblock Hselected.
  pose proof (HierRun.select_permutation preferred c h body Hselected) as Hperm.
  pose proof (Permutation_NoDup Hperm (proj1 (proj2 Hblock))) as Hnodup.
  inversion Hnodup as [|head tail Hfresh Htail]; subst.
  split; [exact Htail|]. intros v Hv.
  destruct (block_domain p scope roots c v Hblock
    (Permutation_in v (Permutation_sym Hperm) (or_intror Hv))) as [Hvalid Hadmits].
  split; [exact Hvalid|].
  rewrite Scope.admits_equation in Hadmits. apply andb_true_iff in Hadmits.
  destruct Hadmits as [Hblocked Hwithin]. apply negb_true_iff in Hblocked.
  rewrite Scope.admits_equation, HierRun.child_scope_equation.
  cbn [Scope.blocked Scope.within]. rewrite FinSet.mem_add_raw.
  assert (Hne : eqb positive_encoding v h = false).
  { apply Bool.not_true_is_false. intro Heq.
    apply (eqb_true_iff positive_encoding positive_encoding_laws) in Heq.
    subst v. contradiction. }
  rewrite Hne, Hblocked. cbn [negb orb andb].
  rewrite FinSet.mem_of_list. apply TarjanStateFacts.member_test. exact Hv.
Qed.

Local Lemma body_reachable {V E} (p : Prepared.t V E) scope h body :
  (forall v, In v body -> Prepared.valid_id p v /\
    Scope.admits (HierRun.child_scope scope h body) v = true) ->
  forall v, Search.scoped_reachable p (HierRun.child_scope scope h body) (rev body) v <->
    In v body.
Proof.
  intros Hdomain v. split.
  - intros [root [es [_ Hpath]]].
    pose proof (proj2 (HierFacts.path_target p _ root es v Hpath)) as Hadmits.
    rewrite Scope.admits_equation, HierRun.child_scope_equation in Hadmits.
    apply andb_true_iff in Hadmits. cbn [Scope.within] in Hadmits.
    rewrite FinSet.mem_of_list in Hadmits.
    apply TarjanStateFacts.member_test. exact (proj2 Hadmits).
  - intro Hin. exists v, []. split; [now apply (proj1 (in_rev body v))|].
    destruct (Hdomain v Hin) as [Hvalid Hallowed]. now apply Search.scoped_nil.
Qed.

Local Lemma self_loop_spec {V E} (p : Prepared.t V E) h :
  Prepared.ready p -> Prepared.valid_id p h ->
  (HierRun.self_loop p h = true <-> exists e, Prepared.arc p h e h).
Proof.
  intros Hready Hvalid. rewrite HierRun.self_loop_equation, existsb_exists. split.
  - intros [[e v] [Hin Hcompare]]. cbn [snd] in Hcompare.
    destruct (Map.code_compare h v) eqn:Heq; try discriminate.
    apply Map.code_compare_eq in Heq. subst v.
    exists e. exact (proj1 (SearchInvariant.successor_arc p h e h Hready Hvalid Hin)).
  - intros [e Harc]. exists (e, h). split.
    + exact (SearchInvariant.arc_successor p h e h Hready Harc).
    + cbn [snd]. rewrite (proj2 (Map.code_compare_eq h h) eq_refl). reflexivity.
Qed.

Local Lemma body_members {V E} (p : Prepared.t V E) scope h body f :
  NoDup body ->
  (forall v, Search.scoped_reachable p (HierRun.child_scope scope h body) (rev body) v <->
    In v body) ->
  Hier.exact p (HierRun.child_scope scope h body) (rev body) f ->
    Permutation body (Hier.members f).
Proof.
  intros Hnodup Hreach Hexact.
  destruct Hexact as [scope' roots f Hunique Hcoverage Hblocks Horder].
  apply NoDup_Permutation; [exact Hnodup|exact Hunique|].
  intro v. rewrite Hcoverage. symmetry. apply Hreach.
Qed.

Local Lemma child_exact {V E} (p : Prepared.t V E) scope h body f :
  Permutation body (Hier.members f) ->
  Hier.exact p (HierRun.child_scope scope h body) (rev body) f ->
    Hier.exact p (Hier.remove_header scope h (h :: Hier.members f)) (Hier.members f) f.
Proof.
  intros Hmembers Hexact. apply (HierTransport.exact p
    (HierRun.child_scope scope h body) (rev body)
    (Hier.remove_header scope h (h :: Hier.members f)) (Hier.members f) f).
  - rewrite HierRun.child_scope_equation. reflexivity.
  - intro v. apply HierTransport.child_admits. intro x.
    split; intro Hin.
    + exact (Permutation_in x Hmembers Hin).
    + exact (Permutation_in x (Permutation_sym Hmembers) Hin).
  - intro v. rewrite <- (in_rev body v). split; intro Hin.
    + exact (Permutation_in v Hmembers Hin).
    + exact (Permutation_in v (Permutation_sym Hmembers) Hin).
  - exact Hexact.
Qed.

Local Lemma component_tree {V E} (p : Prepared.t V E) scope roots c h body f :
  Scc.block p scope roots c -> Permutation c (h :: body) ->
  Hier.entry p scope roots c h -> body <> [] ->
  Permutation body (Hier.members f) ->
  Hier.exact p (HierRun.child_scope scope h body) (rev body) f ->
  Permutation c (Hier.members_tree (Hier.Component h f)) /\
    Hier.blocks_exact p scope roots (Hier.Cons (Hier.Component h f) Hier.Nil).
Proof.
  intros Hblock Hselected Hentry Hnonempty Hmembers Hexact.
  assert (Hperm : Permutation c (h :: Hier.members f)).
  { eapply Permutation_trans; [exact Hselected|]. now apply perm_skip. }
  split; [exact Hperm|]. apply Hier.blocks_component.
  - exact (block_permutation p scope roots c _ Hperm Hblock).
  - left. intro Hnil. apply Hnonempty.
    apply Permutation_nil, Permutation_sym. now rewrite <- Hnil.
  - intros _. exact (entry_permutation p scope roots c _ h Hperm Hentry).
  - exact (child_exact p scope h body f Hmembers Hexact).
  - constructor.
Qed.

Local Lemma singleton_tree {V E} (p : Prepared.t V E) scope roots c h :
  Prepared.ready p -> Scc.block p scope roots c -> Permutation c [h] ->
  Hier.entry p scope roots c h ->
  exists t, t = (if HierRun.self_loop p h then Hier.Component h Hier.Nil else Hier.Vertex h) /\
    Permutation c (Hier.members_tree t) /\
    Hier.blocks_exact p scope roots (Hier.Cons t Hier.Nil).
Proof.
  intros Hready Hblock Hperm Hentry.
  pose proof (block_permutation p scope roots c [h] Hperm Hblock) as Hsingle.
  pose proof (block_domain p scope roots [h] h Hsingle (or_introl eq_refl)) as [Hvalid Hallowed].
  destruct (HierRun.self_loop p h) eqn:Hloop.
  - exists (Hier.Component h Hier.Nil). split; [reflexivity|].
    split; [exact Hperm|]. apply Hier.blocks_component.
    + exact Hsingle.
    + right. apply (proj1 (self_loop_spec p h Hready Hvalid)), Hloop.
    + intros _. exact (entry_permutation p scope roots c [h] h Hperm Hentry).
    + apply HierFacts.empty_roots_exact.
    + constructor.
  - exists (Hier.Vertex h). split; [reflexivity|].
    split; [exact Hperm|]. apply Hier.blocks_vertex.
    + exact Hsingle.
    + intros e Harc.
      pose proof (proj2 (self_loop_spec p h Hready Hvalid) (ex_intro _ e Harc)). congruence.
    + constructor.
Qed.

Local Lemma recursive_size {V E} (p : Prepared.t V E) scope preferred c h body roots d :
  HierRun.select preferred c = Some (h, body) ->
  In d (Scc.components (Tarjan.compute p (HierRun.child_scope scope h body) roots)) ->
    length d < length c.
Proof.
  intros Hselected Hin.
  destruct (HierRun.child_support p scope h body roots d Hin) as [Hnodup Hsub].
  pose proof (NoDup_incl_length Hnodup Hsub).
  pose proof (HierRun.select_length preferred c h body Hselected). lia.
Qed.

Local Lemma children_result {V E} (p : Prepared.t V E) scope h body :
  Prepared.ready p -> NoDup body ->
  (forall v, In v body -> Prepared.valid_id p v /\
    Scope.admits (HierRun.child_scope scope h body) v = true) ->
  let child := HierRun.child_scope scope h body in
  let roots := rev body in
  let r := Tarjan.compute p child roots in
  (forall c, In c (Scc.components r) ->
    exists t,
      Cost.value (HierRun.expand_c p (child, HierRun.entries p roots r, Scc.comp_of r, c)) =
        Some t /\
      Permutation c (Hier.members_tree t) /\
      Hier.blocks_exact p child roots (Hier.Cons t Hier.Nil)) ->
  let f := Cost.value (HierRun.assemble_c (rev (Scc.components r))
    (fun d _ => HierRun.expand_c p (child, HierRun.entries p roots r, Scc.comp_of r, d))) in
  Hier.exact p child roots f /\ Permutation body (Hier.members f).
Proof.
  intros Hready Hnodup Hdomain child roots r Hrecur f.
  assert (Hcallbacks : forall c (Hin : In c (rev (Scc.components r))), exists t,
    Cost.value ((fun d _ => HierRun.expand_c p
      (child, HierRun.entries p roots r, Scc.comp_of r, d)) c Hin) = Some t /\
    Permutation c (Hier.members_tree t) /\
    Hier.blocks_exact p child roots (Hier.Cons t Hier.Nil)).
  { intros c Hin. apply Hrecur. exact (proj2 (in_rev _ _) Hin). }
  destruct (HierStructure.assemble_exact p child roots (rev (Scc.components r))
    _ Hcallbacks) as [Haligned Hblocks].
  assert (Hexact : Hier.exact p child roots f).
  { apply (HierStructure.forest_exact p child roots r f); [|exact Haligned|exact Hblocks].
    apply TarjanExact.compute_exact, Hready. }
  split; [exact Hexact|].
  apply (body_members p scope h body f Hnodup); [apply body_reachable, Hdomain|exact Hexact].
Qed.

(** Every actual ready SCC expands to one exact tree with precisely the same component members. *)
Theorem expand_exact {V E} (p : Prepared.t V E) :
  Prepared.ready p -> forall c scope roots r,
  Scc.exact p scope roots r -> In c (Scc.components r) ->
  exists t,
    Cost.value (HierRun.expand_c p (scope, HierRun.entries p roots r, Scc.comp_of r, c)) =
      Some t /\
    Permutation c (Hier.members_tree t) /\
    Hier.blocks_exact p scope roots (Hier.Cons t Hier.Nil).
Proof.
  intro Hready.
  intro c. induction c as [c IH] using
    (well_founded_induction (well_founded_ltof _ (@length positive))).
  intros scope roots r Hexact Hc.
  pose proof (component_block p scope roots r c Hexact Hc) as Hblock.
  destruct c as [|v rest]; [exfalso; exact (proj1 Hblock eq_refl)|].
  destruct (HierEntries.selection_entry p scope roots r (v :: rest) v Hready Hexact Hc
    (or_introl eq_refl)) as [i [h [body [Howner [Hrow [Hselected Hentry]]]]]].
  pose proof (HierRun.select_permutation (Some h) (v :: rest) h body Hselected) as Hperm.
  destruct body as [|b body].
  - destruct (singleton_tree p scope roots (v :: rest) h Hready Hblock Hperm Hentry)
      as [t [Ht [Hmembers Hblocks]]].
    exists t. split.
    + rewrite HierRun.expand_value_equation, Howner, Hrow.
      cbn beta iota zeta. rewrite Hselected, Ht. reflexivity.
    + exact (conj Hmembers Hblocks).
  - destruct (selected_body_domain p scope roots (v :: rest) (Some h) h (b :: body)
      Hblock Hselected) as [Hnodup Hdomain].
    assert (Hchildren :
      forall d, In d (Scc.components
        (Tarjan.compute p (HierRun.child_scope scope h (b :: body)) (rev (b :: body)))) ->
      exists t, Cost.value (HierRun.expand_c p
        (HierRun.child_scope scope h (b :: body),
         HierRun.entries p (rev (b :: body))
           (Tarjan.compute p (HierRun.child_scope scope h (b :: body)) (rev (b :: body))),
         Scc.comp_of (Tarjan.compute p (HierRun.child_scope scope h (b :: body))
           (rev (b :: body))), d)) = Some t /\
        Permutation d (Hier.members_tree t) /\
        Hier.blocks_exact p (HierRun.child_scope scope h (b :: body)) (rev (b :: body))
          (Hier.Cons t Hier.Nil)).
    { intros d Hin. apply IH.
      - exact (recursive_size p scope (Some h) (v :: rest) h (b :: body) _ d Hselected Hin).
      - apply TarjanExact.compute_exact, Hready.
      - exact Hin. }
    destruct (children_result p scope h (b :: body) Hready Hnodup Hdomain Hchildren)
      as [Hforest Hmembers].
    destruct (component_tree p scope roots (v :: rest) h (b :: body) _ Hblock Hperm Hentry
      ltac:(discriminate) Hmembers Hforest) as [Htree_members Htree_blocks].
    eexists. split.
    + rewrite HierRun.expand_value_equation, Howner, Hrow.
      cbn beta iota zeta. rewrite Hselected. reflexivity.
    + exact (conj Htree_members Htree_blocks).
Qed.

(** Readiness makes the recursive producer exact for arbitrary scopes and supplied roots. *)
Theorem compute_exact {V E} (p : Prepared.t V E) scope roots :
  Prepared.ready p -> Hier.exact p scope roots (HierRun.compute p scope roots).
Proof.
  intro Hready. rewrite HierRun.compute_equation.
  set (r := Tarjan.compute p scope roots).
  assert (Hexact : Scc.exact p scope roots r) by (apply TarjanExact.compute_exact, Hready).
  assert (Hcallbacks : forall c (Hin : In c (rev (Scc.components r))), exists t,
    Cost.value ((fun d _ => HierRun.expand_c p
      (scope, HierRun.entries p roots r, Scc.comp_of r, d)) c Hin) = Some t /\
    Permutation c (Hier.members_tree t) /\
    Hier.blocks_exact p scope roots (Hier.Cons t Hier.Nil)).
  { intros c Hin. apply (expand_exact p Hready c scope roots r Hexact).
    exact (proj2 (in_rev _ _) Hin). }
  destruct (HierStructure.assemble_exact p scope roots (rev (Scc.components r))
    _ Hcallbacks) as [Haligned Hblocks].
  exact (HierStructure.forest_exact p scope roots r _ Hexact Haligned Hblocks).
Qed.

End HierProducer.
