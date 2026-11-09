(** * Complete primitive budgets for indexed dominance checking

    The checker bound retains setup, roots, physical candidate storage and every selected query phase.
    For example, oversized candidates pay their domain scan before early rejection.
    Builds on: GraphDomFiniteQueryCost and GraphDomAncestorIndex. *)

From Stdlib Require Import List Bool PArith NArith Arith Lia Ring.
From Galois.Cost Require Import CostMonad CostList CostBound.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet BaseMapCost BaseTrieCost.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor GraphReach GraphSearchCost
  GraphPreparedCost
  GraphDomCheckBound GraphCheckDomCost GraphDomAncestorIndex GraphDomFastCheck GraphDomFiniteView
  GraphDomFiniteReach GraphDomFiniteClosure GraphDomFiniteCost GraphDomFiniteQueryCost GraphDomCostBasis.
Import Cost.Notations.

Module DomFastCheckCost.
Local Open Scope N_scope.

Definition query_bound n m r w f := DomFiniteQueryCost.reach_bound n m r w f (3 + 4 * w).
Definition ends_bound (n : nat) w := N.of_nat n * (1 + (N.of_nat n + 2) * (2 + 2 * w)).
Definition cache_bound (n : nat) w :=
  N.of_nat n * (3 + 2 * w + (N.of_nat n + 1) * (6 + 3 * w)).
Definition pairs_bound (n m r : nat) w f :=
  N.of_nat n * (3 + w + query_bound n m r w f + N.of_nat n * (7 + 3 * w)).

(** The full budget separates raw input storage from validated live-domain work and retained root work. *)
Definition checker_bound (n m r b : nat) ek bk w wc f s :=
  DomFiniteCost.prepare_bound n m r ek bk w +
  query_bound n m r w f +
  (TrieCost.trie_k * (1 + N.of_nat n * w) + N.of_nat n) +
  2 * TrieCost.trie_k * (1 + s) + N.of_nat b * (5 + 2 * wc) +
  ends_bound n w + cache_bound n w + pairs_bound n m r w f.

Local Lemma live_support {V E} (p : Prepared.t V E) roots v :
  FinSet.mem positive_encoding v (Reach.set p Reach.unrestricted roots) = true ->
  In v (Reach.universe p).
Proof.
  intro Hv. apply DomFiniteClosure.raw_set_closure in Hv.
  now apply DomFiniteClosure.raw_support in Hv.
Qed.

Local Lemma live_length {V E} (p : Prepared.t V E) roots n m r ek bk w :
  DomFiniteCost.bounds p roots n m r ek bk w ->
  (length (FinSet.elements (Reach.set p Reach.unrestricted roots)) <= n)%nat.
Proof.
  intro Hb.
  apply (Nat.le_trans _ (length (DomFiniteView.vertices (DomFiniteView.view p roots)))).
  - apply NoDup_incl_length.
    + apply (FinSet.elements_nodup positive_encoding). apply Reach.set_wf.
    + intros v Hv.
      apply (FinSet.elements_spec positive_encoding positive_encoding_laws) in Hv;
        [|apply Reach.set_wf].
      change (In v (Graph.nodes (DomFiniteView.graph (DomFiniteView.view p roots)))).
      apply DomFiniteView.graph_nodes. now apply live_support in Hv.
  - eapply Nat.le_trans; [apply DomFiniteCost.vertex_length|exact (DomFiniteCost.input_nodes Hb)].
Qed.

Local Lemma validated_parents seen parents w :
  FinSet.wf positive_encoding seen -> Map.wf positive_encoding parents ->
  (forall v, FinSet.mem positive_encoding v seen = true -> key_bits positive_encoding v <= w) ->
  Cost.value (forallb_c (DomCheckCost.binding_ok_c seen) (Map.elements parents)) = true ->
  DomCheckCost.parent_width parents w.
Proof.
  intros Hseen Hparents Hwidth Hdomains v u Hget.
  apply Hwidth. rewrite value_forallb_c in Hdomains.
  apply (Map.elements_spec positive_encoding positive_encoding_laws v u parents Hparents) in Hget.
  apply forallb_forall with (x := (v, u)) in Hdomains; [|exact Hget].
  change (FinSet.mem positive_encoding v seen && FinSet.mem positive_encoding u seen = true)
    in Hdomains.
  apply andb_true_iff in Hdomains. exact (proj2 Hdomains).
Qed.

Local Lemma phase_cost {V E} (p : Prepared.t V E) parents n m r ek bk w f :
  DomFiniteCost.bounds p (Prepared.entry_ids p) n m r ek bk w ->
  N.pos (Pos.size (Prepared.fuel (DomFiniteView.prepared p (Prepared.entry_ids p)))) <= f ->
  Map.wf positive_encoding parents ->
  let seen := Reach.set p Reach.unrestricted (Prepared.entry_ids p) in
  let nodes := FinSet.elements seen in
  Cost.value (forallb_c (DomCheckCost.binding_ok_c seen) (Map.elements parents)) = true ->
  Cost.ticks
    (let* forests := forallb_c (DomCheckCost.ends_c (S (Map.size parents)) parents) nodes in
     if forests then
       let* index := DomAncestorIndex.build_with_c (Map.size parents) parents nodes in
       forallb_c (fun d =>
         let* avoiding := DomFastCheck.avoiding_c
           (DomFiniteView.prepared p (Prepared.entry_ids p)) d in
         forallb_c (DomFastCheck.pair_c index avoiding d) nodes) nodes
     else Cost.ret false) <= ends_bound n w + cache_bound n w + pairs_bound n m r w f.
Proof.
  intros Hb Hfuel Hparents seen nodes Hdomains.
  assert (Hseen_width : forall v, FinSet.mem positive_encoding v seen = true ->
    key_bits positive_encoding v <= w).
  { intros v Hv. apply (DomFiniteCost.universe_width Hb v). now apply live_support in Hv. }
  assert (Hwidth : forall v, In v nodes -> key_bits positive_encoding v <= w).
  { intros v Hv. apply Hseen_width.
    apply (FinSet.elements_spec positive_encoding positive_encoding_laws);
      [apply Reach.set_wf|exact Hv]. }
  pose proof (validated_parents seen parents w (Reach.set_wf p _ _) Hparents Hseen_width Hdomains)
    as Hparent_width.
  pose proof (DomFastCheck.domains_cardinality seen parents (Reach.set_wf p _ _) Hparents Hdomains)
    as Hcard.
  pose proof (live_length p (Prepared.entry_ids p) n m r ek bk w Hb) as Hlength.
  fold seen nodes in Hlength. fold nodes in Hcard.
  assert (HcardN : N.of_nat (Map.size parents) <= N.of_nat n) by lia.
  assert (HlengthN : N.of_nat (length nodes) <= N.of_nat n) by lia.
  pose proof (DomCostBasis.forallb_cost (DomCheckCost.ends_c (S (Map.size parents)) parents)
    nodes ((N.of_nat n + 2) * (2 + 2 * w))
    ltac:(intros v Hv; eapply N.le_trans;
      [exact (DomCheckCost.ends_cost (S (Map.size parents)) parents v w Hparent_width (Hwidth v Hv))
      |unfold DomCheckCost.id_get_budget; rewrite !Nat2N.inj_succ; apply N.mul_le_mono; lia]))
    as Hends.
  pose proof (DomAncestorIndex.build_with_cost (Map.size parents) parents nodes w
    Hparent_width Hwidth) as Hcache.
  unfold DomCheckCost.id_get_budget in Hcache. rewrite Nat2N.inj_succ in Hcache.
  assert (Hcache_scale :
    N.of_nat (length nodes) * (2 + (1 + 2 * w) +
      (N.of_nat (Map.size parents) + 1) * (5 + (1 + 2 * w) + w)) <= cache_bound n w).
  { unfold cache_bound. apply N.mul_le_mono; [exact HlengthN|].
    apply N.add_le_mono; [lia|]. apply N.mul_le_mono; lia. }
  assert (Hpairs : forall index,
    Cost.ticks (forallb_c (fun d =>
      let* avoiding := DomFastCheck.avoiding_c
        (DomFiniteView.prepared p (Prepared.entry_ids p)) d in
      forallb_c (DomFastCheck.pair_c index avoiding d) nodes) nodes) <= pairs_bound n m r w f).
  { intro index.
    eapply N.le_trans; [apply (DomCostBasis.forallb_cost _ nodes
      (2 + w + query_bound n m r w f + N.of_nat n * (7 + 3 * w)))|].
    - intros d Hd. cbn beta.
      assert (Havoid : Cost.ticks (DomFastCheck.avoiding_c
        (DomFiniteView.prepared p (Prepared.entry_ids p)) d) <= 2 + w + query_bound n m r w f).
      { unfold DomFastCheck.avoiding_c.
        rewrite (Cost.ticks_bind (FinSet.add_c positive_encoding d FinSet.empty)).
        fold (FinSet.add positive_encoding d FinSet.empty).
        pose proof (DomFiniteQueryCost.reach_cost p (Prepared.entry_ids p)
          n m r ek bk w f (3 + 4 * w)
          (Scope.Make (FinSet.add positive_encoding d FinSet.empty) None) Hb Hfuel
          ltac:(intros v Hv; eapply N.le_trans; [apply SearchCost.admits_cost;
            exact (DomFiniteCost.universe_width Hb v Hv)|unfold SearchCost.id_cost; lia])) as Hreach.
        rewrite FinSet.add_cost.
        change (1 + 1 + key_bits positive_encoding d +
          Cost.ticks (DomFiniteReach.reach_c
            (DomFiniteView.prepared p (Prepared.entry_ids p))
            (Scope.Make (FinSet.add positive_encoding d FinSet.empty) None)) <=
          2 + w + query_bound n m r w f).
        pose proof (Hwidth d Hd). unfold query_bound. lia. }
      assert (Hinner : forall avoiding,
        Cost.ticks (forallb_c (DomFastCheck.pair_c index avoiding d) nodes) <=
          N.of_nat n * (7 + 3 * w)).
      { intro avoiding. eapply N.le_trans.
        - apply (DomCostBasis.forallb_cost _ nodes (6 + 3 * w)).
          intros v Hv. unfold DomFastCheck.pair_c. autorewrite with galois_cost.
          pose proof (DomAncestorIndex.contains_cost index d v w (Hwidth d Hd) (Hwidth v Hv)).
          rewrite DomCostBasis.mem_cost. pose proof (Hwidth v Hv). lia.
        - apply N.mul_le_mono; [exact HlengthN|lia]. }
      rewrite (Cost.ticks_bind (DomFastCheck.avoiding_c
        (DomFiniteView.prepared p (Prepared.entry_ids p)) d)).
      pose proof (Hinner (Cost.value (DomFastCheck.avoiding_c
        (DomFiniteView.prepared p (Prepared.entry_ids p)) d))). lia.
    - unfold pairs_bound. apply N.mul_le_mono; [exact HlengthN|lia]. }
  rewrite (Cost.ticks_bind
    (forallb_c (DomCheckCost.ends_c (S (Map.size parents)) parents) nodes)).
  destruct (Cost.value (forallb_c (DomCheckCost.ends_c (S (Map.size parents)) parents) nodes)).
  - rewrite (Cost.ticks_bind (DomAncestorIndex.build_with_c (Map.size parents) parents nodes)).
    pose proof (Hpairs (Cost.value (DomAncestorIndex.build_with_c (Map.size parents) parents nodes))).
    unfold ends_bound. nia.
  - rewrite Cost.ticks_ret. unfold ends_bound. nia.
Qed.

(** Indexed checking has a complete primitive numeric bound on finite data duties without output premises. *)
Theorem check_cost {V E} (p : Prepared.t V E) parents n m r b ek bk w wc f s :
  DomFiniteCost.bounds p (Prepared.entry_ids p) n m r ek bk w ->
  N.pos (Pos.size (Prepared.fuel (DomFiniteView.prepared p (Prepared.entry_ids p)))) <= f ->
  Map.wf positive_encoding parents ->
  (Map.size parents <= b)%nat -> MapCost.skeleton_nodes parents <= s ->
  DomCheckBound.stored_width parents wc ->
  Cost.ticks (DomFastCheck.check_c p parents) <= checker_bound n m r b ek bk w wc f s.
Proof.
  intros Hb Hfuel Hparents Hcard Hskeleton Hstored.
  set (q := DomFiniteView.prepared p (Prepared.entry_ids p)).
  set (seen := Reach.set p Reach.unrestricted (Prepared.entry_ids p)).
  set (nodes := FinSet.elements seen).
  pose proof (DomFiniteCost.prepare_cost p (Prepared.entry_ids p) n m r ek bk w Hb) as Hsetup.
  pose proof (DomFiniteQueryCost.reach_cost p (Prepared.entry_ids p) n m r ek bk w f (3 + 4 * w)
    Reach.unrestricted Hb Hfuel
    ltac:(intros v Hv; eapply N.le_trans; [apply SearchCost.admits_cost;
      exact (DomFiniteCost.universe_width Hb v Hv)|unfold SearchCost.id_cost; lia])) as Hreach.
  fold q in Hreach.
  pose proof (live_length p (Prepared.entry_ids p) n m r ek bk w Hb) as Hlength.
  fold seen nodes in Hlength.
  pose proof (DomCostBasis.elements_cost seen n w (Reach.set_wf p _ _)
    ltac:(rewrite FinSet.size_elements; exact Hlength)
    ltac:(intros v Hv; apply (DomFiniteCost.universe_width Hb v);
      now apply live_support in Hv)) as Henumerate.
  pose proof (MapCost.elements_cost parents) as Hbindings.
  pose proof (MapCost.size_cost parents) as Hsize.
  assert (Hscan : TrieCost.trie_k * (1 + MapCost.skeleton_nodes parents) <=
    TrieCost.trie_k * (1 + s)) by (apply N.mul_le_mono; lia).
  pose proof (DomCostBasis.forallb_cost (DomCheckCost.binding_ok_c seen) (Map.elements parents)
    (4 + 2 * wc) ltac:(intros vu Hvu; rewrite DomCheckCost.binding_ok_cost;
      destruct (Hstored vu Hvu) as [Hchild Hparent]; rewrite !DomCostBasis.mem_cost; lia)) as Hdomains.
  rewrite <- Map.size_elements in Hdomains.
  assert (Hdomain_scale : N.of_nat (Map.size parents) * (1 + (4 + 2 * wc)) <=
    N.of_nat b * (5 + 2 * wc)) by (apply N.mul_le_mono; lia).
  unfold DomFastCheck.check_c.
  rewrite (Cost.ticks_bind (DomFiniteView.prepare_c p (Prepared.entry_ids p))). fold q.
  rewrite (Cost.ticks_bind (DomFiniteReach.reach_c q Reach.unrestricted)).
  assert (Hlive : Cost.value (DomFiniteReach.reach_c q Reach.unrestricted) = seen).
  { apply DomFiniteReach.reach_value. }
  rewrite Hlive.
  rewrite (Cost.ticks_bind (FinSet.elements_c seen)). fold nodes.
  rewrite (Cost.ticks_bind (Map.elements_c parents)). fold (Map.elements parents).
  cbn beta.
  rewrite (Cost.ticks_bind (forallb_c (DomCheckCost.binding_ok_c seen) (Map.elements parents))).
  destruct (Cost.value (forallb_c (DomCheckCost.binding_ok_c seen) (Map.elements parents)))
    eqn:Haccepted_domains.
  - rewrite (Cost.ticks_bind (Map.size_c parents)). fold (Map.size parents).
    pose proof (phase_cost p parents n m r ek bk w f Hb Hfuel Hparents Haccepted_domains) as Hphase.
    cbn zeta in Hphase. fold seen nodes in Hphase. fold q in Hphase.
    eapply N.le_trans.
    + apply N.add_le_mono; [exact Hsetup|].
      apply N.add_le_mono; [exact Hreach|].
      apply N.add_le_mono; [exact Henumerate|].
      apply N.add_le_mono; [exact Hbindings|].
      apply N.add_le_mono; [exact Hdomains|].
      apply N.add_le_mono; [exact Hsize|exact Hphase].
    + unfold checker_bound, query_bound. nia.
  - rewrite Cost.ticks_ret.
    eapply N.le_trans.
    + apply N.add_le_mono; [exact Hsetup|].
      apply N.add_le_mono; [exact Hreach|].
      apply N.add_le_mono; [exact Henumerate|].
      apply N.add_le_mono; [exact Hbindings|].
      apply N.add_le_mono; [exact Hdomains|apply N.le_refl].
    + unfold checker_bound, query_bound. nia.
Qed.

(** The same complete finite-data budget bounds every family, including early rejections. *)
Theorem check_bigO {X V E} (p : X -> Prepared.t V E) parents
    (n m r b : X -> nat) (ek bk w wc f s : X -> N) :
  (forall x, DomFiniteCost.bounds (p x) (Prepared.entry_ids (p x))
    (n x) (m x) (r x) (ek x) (bk x) (w x)) ->
  (forall x, N.pos (Pos.size (Prepared.fuel
    (DomFiniteView.prepared (p x) (Prepared.entry_ids (p x))))) <= f x) ->
  (forall x, Map.wf positive_encoding (parents x)) ->
  (forall x, (Map.size (parents x) <= b x)%nat) ->
  (forall x, MapCost.skeleton_nodes (parents x) <= s x) ->
  (forall x, DomCheckBound.stored_width (parents x) (wc x)) ->
  bigO (fun x => checker_bound (n x) (m x) (r x) (b x)
    (ek x) (bk x) (w x) (wc x) (f x) (s x))
    (fun x => Cost.ticks (DomFastCheck.check_c (p x) (parents x))).
Proof.
  intros Hb Hfuel Hparents Hcard Hskeleton Hstored.
  exists 1. intro x.
  pose proof (check_cost (p x) (parents x) (n x) (m x) (r x) (b x)
    (ek x) (bk x) (w x) (wc x) (f x) (s x)
    (Hb x) (Hfuel x) (Hparents x) (Hcard x) (Hskeleton x) (Hstored x)). lia.
Qed.

(** The coefficient retains the public preparation, search and trie constants symbolically. *)
Definition checker_k :=
  256 * (1 + PreparedCost.prepare_k + SearchCost.search_k + TrieCost.trie_k +
    PreparedCost.prepare_k * TrieCost.trie_k).

Local Lemma uniform_core_budget n m w :
  checker_bound n m n 0 w w w 0 w 0 <=
    checker_k * (1 + N.of_nat n) * (1 + N.of_nat n + N.of_nat m) * (1 + w).
Proof.
  set (a := N.of_nat n).
  set (b := N.of_nat m).
  set (target := (1 + a) * (1 + a + b) * (1 + w)).
  assert (Hproduct : forall x y z, x <= 1 + a -> y <= 1 + a + b -> z <= 1 + w ->
    x * y * z <= target).
  { intros x y z Hx Hy Hz. unfold target.
    apply N.mul_le_mono; [now apply N.mul_le_mono|exact Hz]. }
  assert (Hone : 1 <= target).
  { change (1 * 1 * 1 <= target). apply Hproduct; lia. }
  assert (Ha : a <= target).
  { replace a with (a * 1 * 1) at 1 by ring. apply Hproduct; lia. }
  assert (Hb : b <= target).
  { replace b with (1 * b * 1) at 1 by ring. apply Hproduct; lia. }
  assert (Haw : a * w <= target).
  { replace (a * w) with (a * 1 * w) at 1 by ring. apply Hproduct; lia. }
  assert (Hbw : b * w <= target).
  { replace (b * w) with (1 * b * w) at 1 by ring. apply Hproduct; lia. }
  assert (Haa : a * a <= target).
  { replace (a * a) with (a * a * 1) at 1 by ring. apply Hproduct; lia. }
  assert (Haaw : a * a * w <= target) by (apply Hproduct; lia).
  assert (Hab : a * b <= target).
  { replace (a * b) with (a * b * 1) at 1 by ring. apply Hproduct; lia. }
  assert (Habw : a * b * w <= target) by (apply Hproduct; lia).
  assert (Hpath : 1 + a * w <= target).
  { eapply N.le_trans with (m := (1 + a) * (1 + w)).
    - replace ((1 + a) * (1 + w)) with (1 + a * w + (a + w)) by ring.
      apply N.le_add_r.
    - replace ((1 + a) * (1 + w)) with ((1 + a) * (1 + w) * 1) at 1 by ring.
      unfold target. replace ((1 + a) * (1 + a + b) * (1 + w)) with
        (((1 + a) * (1 + w)) * (1 + a + b)) by ring.
      apply N.mul_le_mono; lia. }
  assert (Htrie : TrieCost.trie_k * (1 + a * w) <= TrieCost.trie_k * target).
  { apply N.mul_le_mono; [reflexivity|exact Hpath]. }
  assert (Hdata : DomFiniteCost.data_bound n m n w w w <= (32 + TrieCost.trie_k) * target).
  { unfold DomFiniteCost.data_bound. fold a b.
    replace (a * (3 + w + w + (4 + w)) +
      (TrieCost.trie_k * (1 + a * w) + a) + a * (3 + w) +
      a * (5 + 2 * w + b * (8 + 2 * w))) with
      ((16 * a + 6 * (a * w) + 8 * (a * b) + 2 * (a * b * w)) +
        TrieCost.trie_k * (1 + a * w)) by ring.
    assert (Hpure : 16 * a + 6 * (a * w) + 8 * (a * b) + 2 * (a * b * w) <= 32 * target)
      by lia.
    replace ((32 + TrieCost.trie_k) * target) with
      (32 * target + TrieCost.trie_k * target) by ring.
    now apply N.add_le_mono. }
  assert (Hprep_factor : (a + b + a) * (1 + a * w) <= 8 * target).
  { replace ((a + b + a) * (1 + a * w)) with
      (2 * a + b + 2 * (a * a * w) + a * b * w) by ring. lia. }
  assert (Hprep_scale : TrieCost.trie_k * ((a + b + a) * (1 + a * w)) <=
    TrieCost.trie_k * (8 * target)).
  { apply N.mul_le_mono; [reflexivity|exact Hprep_factor]. }
  assert (Hprep_inner :
    1 + (a + b + a) * (2 + 2 * w +
      (2 + w + TrieCost.trie_k * (1 + a * w) + 2 * a)) <=
      (32 + 8 * TrieCost.trie_k) * target).
  { assert (Hpure : 1 + (a + b + a) * (4 + 3 * w + 2 * a) <= 32 * target).
    { replace (1 + (a + b + a) * (4 + 3 * w + 2 * a)) with
        (1 + 8 * a + 4 * b + 6 * (a * w) + 3 * (b * w) + 4 * (a * a) + 2 * (a * b))
        by ring. lia. }
    replace (1 + (a + b + a) * (2 + 2 * w +
      (2 + w + TrieCost.trie_k * (1 + a * w) + 2 * a))) with
      ((1 + (a + b + a) * (4 + 3 * w + 2 * a)) +
        TrieCost.trie_k * ((a + b + a) * (1 + a * w))) by ring.
    replace ((32 + 8 * TrieCost.trie_k) * target) with
      (32 * target + TrieCost.trie_k * (8 * target)) by ring.
    now apply N.add_le_mono. }
  assert (Hprepare : DomFiniteCost.preparation_bound n m n w <=
    PreparedCost.prepare_k * ((32 + 8 * TrieCost.trie_k) * target)).
  { unfold DomFiniteCost.preparation_bound, DomFiniteCost.out_bound. fold a b.
    apply N.mul_le_mono; [reflexivity|exact Hprep_inner]. }
  assert (Hquery_factor : (1 + a) * ((a + b + a) * (2 + w) + a * w) <= 32 * target).
  { replace ((1 + a) * ((a + b + a) * (2 + w) + a * w)) with
      (4 * a + 2 * b + 3 * (a * w) + b * w + 4 * (a * a) + 2 * (a * b) +
        3 * (a * a * w) + a * b * w) by ring. lia. }
  assert (Hquery_scale : SearchCost.search_k *
    ((1 + a) * ((a + b + a) * (2 + w) + a * w)) <=
    SearchCost.search_k * (32 * target)).
  { apply N.mul_le_mono; [reflexivity|exact Hquery_factor]. }
  assert (Hquery : (1 + a) * query_bound n m n w w <=
    (64 + 32 * SearchCost.search_k) * target).
  { unfold query_bound, DomFiniteQueryCost.reach_bound, DomFiniteQueryCost.translation_bound,
      DomFiniteQueryCost.search_bound. fold a b.
    replace ((1 + a) * (a * (8 + (3 + 4 * w) + 2 * w) +
      SearchCost.search_k * ((a + b + a) * (2 + w) + a * w) + 2 * a * (4 + w))) with
      (((19 * a + 19 * (a * a)) + (8 * (a * w) + 8 * (a * a * w))) +
        SearchCost.search_k * ((1 + a) * ((a + b + a) * (2 + w) + a * w))) by ring.
    assert (Hpure : (19 * a + 19 * (a * a)) + (8 * (a * w) + 8 * (a * a * w)) <=
      64 * target) by lia.
    replace ((64 + 32 * SearchCost.search_k) * target) with
      (64 * target + SearchCost.search_k * (32 * target)) by ring.
    now apply N.add_le_mono. }
  assert (Hscan_scale : 2 * TrieCost.trie_k <= 2 * TrieCost.trie_k * target).
  { replace (2 * TrieCost.trie_k) with ((2 * TrieCost.trie_k) * 1) at 1 by ring.
    apply N.mul_le_mono; [reflexivity|exact Hone]. }
  assert (Hscan : (TrieCost.trie_k * (1 + a * w) + a) + 2 * TrieCost.trie_k <=
    (3 * TrieCost.trie_k + 1) * target).
  { replace ((3 * TrieCost.trie_k + 1) * target) with
      ((TrieCost.trie_k * target + target) + 2 * TrieCost.trie_k * target) by ring.
    apply N.add_le_mono; [now apply N.add_le_mono|exact Hscan_scale]. }
  assert (Hends : ends_bound n w <= 13 * target).
  { unfold ends_bound. fold a.
    replace (a * (1 + (a + 2) * (2 + 2 * w))) with
      (5 * a + 2 * (a * a) + 4 * (a * w) + 2 * (a * a * w)) by ring. lia. }
  assert (Hcache : cache_bound n w <= 23 * target).
  { unfold cache_bound. fold a.
    replace (a * (3 + 2 * w + (a + 1) * (6 + 3 * w))) with
      (9 * a + 6 * (a * a) + 5 * (a * w) + 3 * (a * a * w)) by ring. lia. }
  assert (Hpairs : a * (3 + w + a * (7 + 3 * w)) <= 14 * target).
  { replace (a * (3 + w + a * (7 + 3 * w))) with
      (3 * a + a * w + 7 * (a * a) + 3 * (a * a * w)) by ring. lia. }
  replace (checker_k * (1 + a) * (1 + a + b) * (1 + w))
    with (checker_k * target) by (unfold target; ring).
  replace (checker_bound n m n 0 w w w 0 w 0) with
    (DomFiniteCost.data_bound n m n w w w + DomFiniteCost.preparation_bound n m n w +
      (1 + a) * query_bound n m n w w +
      ((TrieCost.trie_k * (1 + a * w) + a) + 2 * TrieCost.trie_k) +
      ends_bound n w + cache_bound n w + a * (3 + w + a * (7 + 3 * w)))
    by (unfold checker_bound, DomFiniteCost.prepare_bound, pairs_bound,
      query_bound, DomFiniteQueryCost.reach_bound, DomFiniteQueryCost.translation_bound,
      DomFiniteQueryCost.search_bound; unfold a; cbn [N.of_nat]; ring).
  eapply N.le_trans.
  - apply N.add_le_mono; [|exact Hpairs].
    apply N.add_le_mono; [|exact Hcache].
    apply N.add_le_mono; [|exact Hends].
    apply N.add_le_mono; [|exact Hscan].
    apply N.add_le_mono; [|exact Hquery].
    apply N.add_le_mono; [exact Hdata|exact Hprepare].
  - replace ((32 + TrieCost.trie_k) * target +
      PreparedCost.prepare_k * ((32 + 8 * TrieCost.trie_k) * target) +
      (64 + 32 * SearchCost.search_k) * target +
      (3 * TrieCost.trie_k + 1) * target + 13 * target + 23 * target + 14 * target) with
      ((147 + 4 * TrieCost.trie_k + 32 * PreparedCost.prepare_k +
        8 * (PreparedCost.prepare_k * TrieCost.trie_k) + 32 * SearchCost.search_k) * target)
      by ring.
    apply N.mul_le_mono; [unfold checker_k; lia|reflexivity].
Qed.

(** Graph work has the design-table upper-bound shape when primitive budgets and roots fit its width domain. *)
Theorem core_budget n m r ek bk w f :
  (r <= n)%nat -> ek <= w -> bk <= w -> f <= w ->
  checker_bound n m r 0 ek bk w 0 f 0 <=
    checker_k * (1 + N.of_nat n) * (1 + N.of_nat n + N.of_nat m) * (1 + w).
Proof.
  intros Hr Hek Hbk Hfuel.
  assert (Hmono : checker_bound n m r 0 ek bk w 0 f 0 <=
    checker_bound n m n 0 w w w 0 w 0).
  { unfold checker_bound, DomFiniteCost.prepare_bound, DomFiniteCost.data_bound,
      DomFiniteCost.preparation_bound, DomFiniteCost.out_bound, pairs_bound, query_bound,
      DomFiniteQueryCost.reach_bound, DomFiniteQueryCost.translation_bound,
      DomFiniteQueryCost.search_bound, ends_bound, cache_bound.
    repeat match goal with
    | |- (?a + ?b <= ?c + ?d)%N => apply N.add_le_mono
    | |- (?a * ?b <= ?c * ?d)%N => apply N.mul_le_mono
    | |- _ => first [reflexivity | assumption | lia]
    end.
    all: lia. }
  eapply N.le_trans; [exact Hmono|].
  apply uniform_core_budget.
Qed.

(** The graph upper bound retains rejected candidate storage as a separate, genuine additive input cost. *)
Theorem check_graph_cost {V E} (p : Prepared.t V E) parents n m r b ek bk w wc f s :
  DomFiniteCost.bounds p (Prepared.entry_ids p) n m r ek bk w ->
  N.pos (Pos.size (Prepared.fuel (DomFiniteView.prepared p (Prepared.entry_ids p)))) <= f ->
  Map.wf positive_encoding parents ->
  (Map.size parents <= b)%nat -> MapCost.skeleton_nodes parents <= s ->
  DomCheckBound.stored_width parents wc ->
  (r <= n)%nat -> ek <= w -> bk <= w -> f <= w ->
  Cost.ticks (DomFastCheck.check_c p parents) <=
    checker_k * (1 + N.of_nat n) * (1 + N.of_nat n + N.of_nat m) * (1 + w) +
      2 * TrieCost.trie_k * s + N.of_nat b * (5 + 2 * wc).
Proof.
  intros Hb Hfuel Hparents Hcard Hskeleton Hstored Hr Hek Hbk Hf.
  pose proof (check_cost p parents n m r b ek bk w wc f s
    Hb Hfuel Hparents Hcard Hskeleton Hstored) as Hcheck.
  pose proof (core_budget n m r ek bk w f Hr Hek Hbk Hf) as Hcore.
  assert (Hequation : checker_bound n m r b ek bk w wc f s =
    checker_bound n m r 0 ek bk w 0 f 0 +
      2 * TrieCost.trie_k * s + N.of_nat b * (5 + 2 * wc)).
  { unfold checker_bound. nia. }
  rewrite Hequation in Hcheck. lia.
Qed.

(** The bounded-input coefficient also covers raw candidate scans and their physical trie skeleton. *)
Definition table_k := checker_k + 2 * TrieCost.trie_k + 7.

(** Bounded raw candidates give the design-table upper bound without assuming acceptance or a forest. *)
Theorem check_table_cost {V E} (p : Prepared.t V E) parents n m r ek bk w :
  DomFiniteCost.bounds p (Prepared.entry_ids p) n m r ek bk w ->
  N.pos (Pos.size (Prepared.fuel (DomFiniteView.prepared p (Prepared.entry_ids p)))) <= w ->
  Map.wf positive_encoding parents -> (Map.size parents <= n)%nat ->
  DomCheckBound.stored_width parents w ->
  (r <= n)%nat -> ek <= w -> bk <= w ->
  Cost.ticks (DomFastCheck.check_c p parents) <=
    table_k * (1 + N.of_nat n) * (1 + N.of_nat n + N.of_nat m) * (1 + w).
Proof.
  intros Hb Hfuel Hparents Hcard Hstored Hr Hek Hbk.
  pose proof (check_graph_cost p parents n m r (Map.size parents) ek bk w w w
    (MapCost.skeleton_nodes parents) Hb Hfuel Hparents (Nat.le_refl _) (N.le_refl _)
    Hstored Hr Hek Hbk (N.le_refl _)) as Hcheck.
  pose proof (MapCost.skeleton_width positive_encoding parents w Hparents
    ltac:(intros v u Hget;
      apply (Map.elements_spec positive_encoding positive_encoding_laws v u parents Hparents) in Hget;
      exact (proj1 (Hstored (v, u) Hget)))) as Hskeleton.
  set (a := N.of_nat n).
  set (b := N.of_nat m).
  set (target := (1 + a) * (1 + a + b) * (1 + w)).
  assert (Hn : a <= target).
  { replace a with (a * 1 * 1) at 1 by ring. unfold target.
    apply N.mul_le_mono; [apply N.mul_le_mono; lia|lia]. }
  assert (Hnw : a * w <= target).
  { replace (a * w) with (a * 1 * w) at 1 by ring. unfold target.
    apply N.mul_le_mono; [apply N.mul_le_mono; lia|lia]. }
  assert (Hscale : MapCost.skeleton_nodes parents <= target).
  { eapply N.le_trans; [exact Hskeleton|].
    eapply N.le_trans with (m := a * w); [apply N.mul_le_mono; [unfold a; lia|reflexivity]|exact Hnw]. }
  assert (Hscan : 2 * TrieCost.trie_k * MapCost.skeleton_nodes parents <=
    2 * TrieCost.trie_k * target).
  { apply N.mul_le_mono; [reflexivity|exact Hscale]. }
  assert (Hbindings : N.of_nat (Map.size parents) * (5 + 2 * w) <= 7 * target).
  { eapply N.le_trans with (m := a * (5 + 2 * w)).
    - apply N.mul_le_mono; [unfold a; lia|reflexivity].
    - replace (a * (5 + 2 * w)) with (5 * a + 2 * (a * w)) by ring. lia. }
  fold a b in Hcheck.
  replace (checker_k * (1 + a) * (1 + a + b) * (1 + w))
    with (checker_k * target) in Hcheck by (unfold target; ring).
  replace (table_k * (1 + a) * (1 + a + b) * (1 + w))
    with (checker_k * target + 2 * TrieCost.trie_k * target + 7 * target)
    by (unfold table_k, target; ring).
  lia.
Qed.

(** Every family in the explicit bounded-input domain has the graph design-table upper-bound shape. *)
Theorem check_table_bigO {X V E} (p : X -> Prepared.t V E) parents
    (n m r : X -> nat) (ek bk w : X -> N) :
  (forall x, DomFiniteCost.bounds (p x) (Prepared.entry_ids (p x))
    (n x) (m x) (r x) (ek x) (bk x) (w x)) ->
  (forall x, N.pos (Pos.size (Prepared.fuel
    (DomFiniteView.prepared (p x) (Prepared.entry_ids (p x))))) <= w x) ->
  (forall x, Map.wf positive_encoding (parents x)) ->
  (forall x, (Map.size (parents x) <= n x)%nat) ->
  (forall x, DomCheckBound.stored_width (parents x) (w x)) ->
  (forall x, (r x <= n x)%nat) -> (forall x, ek x <= w x) -> (forall x, bk x <= w x) ->
  bigO (fun x => (1 + N.of_nat (n x)) * (1 + N.of_nat (n x) + N.of_nat (m x)) * (1 + w x))
    (fun x => Cost.ticks (DomFastCheck.check_c (p x) (parents x))).
Proof.
  intros Hb Hfuel Hparents Hcard Hstored Hr Hek Hbk.
  exists table_k. intro x.
  pose proof (check_table_cost (p x) (parents x) (n x) (m x) (r x)
    (ek x) (bk x) (w x) (Hb x) (Hfuel x) (Hparents x) (Hcard x)
    (Hstored x) (Hr x) (Hek x) (Hbk x)) as Hcheck.
  replace (table_k * (1 + N.of_nat (n x)) *
    (1 + N.of_nat (n x) + N.of_nat (m x)) * (1 + w x)) with
    (table_k * ((1 + N.of_nat (n x)) *
      (1 + N.of_nat (n x) + N.of_nat (m x)) * (1 + w x))) in Hcheck by ring.
  eapply N.le_trans; [exact Hcheck|].
  apply N.mul_le_mono; [reflexivity|lia].
Qed.

End DomFastCheckCost.
