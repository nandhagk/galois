(** * Physical-storage bounds for raw dominance checking

    The bound retains shared closure work, every candidate binding and its actual skeleton.
    For example, a candidate with unrelated deep stored support still pays all enumeration scans.
    Builds on: GraphCheckDomCost, GraphDomReachCost and public map and set contracts. *)

From Stdlib Require Import List Bool PArith NArith Nnat Arith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet BaseMapCost BaseTrieCost.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor GraphSearchSpec
  GraphReach GraphDomSpec GraphCheckDomCost GraphDomReachCost GraphFrontierSweep.
Import List.ListNotations Cost.Notations.

Module DomCheckBound.
Local Open Scope N_scope.

Definition singleton_bound w := 1 + 2 * w.

(** Stored endpoint widths cover raw displayed keys independently of the queried code paths. *)
Definition stored_width (m : Map.t positive positive) w : Prop :=
  forall vu, In vu (Map.elements m) ->
    key_bits positive_encoding (fst vu) <= w /\ key_bits positive_encoding (snd vu) <= w.

(** The checker budget is a closed primitive/public-callee polynomial in graph and raw storage sizes. *)
Definition checker_bound (n m l b : nat) w a q h s :=
  let nodes := N.of_nat n in
  let bindings := N.of_nat b in
  let scan := TrieCost.trie_k * (1 + s) in
  let pair := DomCheckCost.ancestor_bound b w s + 2 + w in
  let avoiding := singleton_bound w +
    DomReachCost.reach_bound nodes (N.of_nat m) (N.of_nat l) w a q (3 + w) in
  DomReachCost.reach_bound nodes (N.of_nat m) (N.of_nat l) w a q h +
    (TrieCost.trie_k * (1 + nodes * w) + nodes) +
    scan + bindings * (2 * (2 + w) + 1) + scan +
    nodes * ((bindings + 2) * (1 + DomCheckCost.id_get_budget w) + 1) +
    nodes * (avoiding + nodes * (pair + 1) + 1).

Local Lemma forallb_cost_on {A} (f : A -> Cost.t bool) xs k :
  (forall x, In x xs -> Cost.ticks (f x) <= k) ->
  Cost.ticks (forallb_c f xs) <= N.of_nat (length xs) * (k + 1).
Proof.
  induction xs as [|x rest IH]; intro Hcost.
  - rewrite ticks_forallb_c_nil. lia.
  - rewrite ticks_forallb_c_cons. pose proof (Hcost x (or_introl eq_refl)) as Hhead.
    specialize (IH ltac:(intros y Hy; apply Hcost; now right)).
    cbn [length]. rewrite Nat2N.inj_succ. destruct (Cost.value (f x)); nia.
Qed.

Local Lemma path_endpoint_valid {V E} (p : Prepared.t V E) scope u es v :
  Search.scoped_path p scope u es v -> Prepared.valid_id p v.
Proof.
  intro Hpath. induction Hpath; assumption.
Qed.

(** Shared closure enumeration contains only valid IDs on the graph-readiness domain. *)
Theorem live_support {V E} (p : Prepared.t V E) scope :
  Prepared.ready p ->
  Forall (Prepared.valid_id p)
    (FinSet.elements (Reach.set p scope (Prepared.entry_ids p))).
Proof.
  intro Hready. apply Forall_forall. intros v Hv.
  apply (FinSet.elements_spec positive_encoding positive_encoding_laws) in Hv;
    [|apply Reach.set_wf].
  apply (Reach.exact _ _ _ _ Hready) in Hv.
  destruct Hv as [root [es [Hroot Hpath]]]. now apply path_endpoint_valid in Hpath.
Qed.

Local Lemma live_length {V E} (p : Prepared.t V E) scope n :
  Prepared.ready p -> (length (Reach.universe p) <= n)%nat ->
  (length (FinSet.elements (Reach.set p scope (Prepared.entry_ids p))) <= n)%nat.
Proof.
  intros Hready Hsize. eapply Nat.le_trans; [|exact Hsize].
  apply NoDup_incl_length.
  - apply (FinSet.elements_nodup positive_encoding). apply Reach.set_wf.
  - intros v Hv. apply Reach.universe_spec.
    exact (proj1 (Forall_forall _ _) (live_support p scope Hready) v Hv).
Qed.

Local Lemma enumerate_live_cost {V E} (p : Prepared.t V E) scope t n m l b w a q h s :
  Prepared.ready p -> FrontierSweep.resources p t n m l b w a q h s ->
  Cost.ticks (FinSet.elements_c (Reach.set p scope (Prepared.entry_ids p))) <=
    TrieCost.trie_k * (1 + N.of_nat n * w) + N.of_nat n.
Proof.
  intros Hready Hr.
  set (seen := Reach.set p scope (Prepared.entry_ids p)).
  pose proof (Reach.set_wf p scope (Prepared.entry_ids p)) as Hseen.
  fold seen in Hseen.
  pose proof (live_support p scope Hready) as Hsupport. fold seen in Hsupport.
  pose proof (live_length p scope n Hready (FrontierSweep.universe_bound Hr)) as Hlength.
  fold seen in Hlength.
  assert (Hsize : (Map.size seen <= n)%nat).
  { assert (Hcard : Map.size seen = length (FinSet.elements seen)).
    { exact (FinSet.size_elements seen). }
    lia. }
  assert (Hwidth : forall v u, Map.get positive_encoding v seen = Some u ->
    key_bits positive_encoding v <= w).
  { intros v [] Hget.
    assert (Hin : In v (FinSet.elements seen)).
    { apply (FinSet.elements_spec positive_encoding positive_encoding_laws);
        [exact Hseen|].
      now apply FinSet.mem_spec. }
    exact (FrontierSweep.width_bound Hr v
      (proj1 (Forall_forall _ _) Hsupport v Hin)). }
  pose proof (MapCost.elements_numeric_cost positive_encoding seen w Hseen Hwidth) as Hmap.
  rewrite FinSet.elements_cost_equation.
  assert (Hcard : N.of_nat (Map.size seen) <= N.of_nat n) by lia.
  assert (Hscale :
    TrieCost.trie_k * (1 + N.of_nat (Map.size seen) * w) <=
      TrieCost.trie_k * (1 + N.of_nat n * w)).
  { apply N.mul_le_mono; [reflexivity|].
    apply N.add_le_mono; [reflexivity|]. now apply N.mul_le_mono. }
  rewrite FinSet.size_elements.
  lia.
Qed.

Local Lemma singleton_cost d w :
  key_bits positive_encoding d <= w ->
  Cost.ticks (FinSet.add_c positive_encoding d FinSet.empty) <= singleton_bound w.
Proof.
  intro Hwidth. rewrite FinSet.add_cost.
  pose proof (encode_cost_bound positive_encoding_cost_laws d).
  fold (key_bits positive_encoding d). unfold singleton_bound. nia.
Qed.

(** The actual raw checker has a coarse closed bound with explicit stored endpoint and parent widths. *)
Theorem check_cost {V E} (p : Prepared.t V E) candidate n m l b w a q h s :
  Prepared.ready p ->
  FrontierSweep.resources p (Dom.Tree candidate Map.empty Map.empty) n m l b w a q h s ->
  DomCheckCost.parent_width candidate w -> stored_width candidate w ->
  Cost.ticks (DomCheckCost.check_c p candidate) <= checker_bound n m l b w a q h s.
Proof.
  intros Hready Hr Hparents Hstored.
  set (seen := Reach.set p Reach.unrestricted (Prepared.entry_ids p)).
  set (vs := FinSet.elements seen).
  set (nodes := N.of_nat n).
  set (bindings := N.of_nat b).
  set (pair := DomCheckCost.ancestor_bound b w s + 2 + w).
  set (avoid := singleton_bound w +
    DomReachCost.reach_bound nodes (N.of_nat m) (N.of_nat l) w a q (3 + w)).
  assert (Hsize : (Map.size candidate <= b)%nat) by exact (FrontierSweep.bindings_bound Hr).
  assert (Hskeleton : MapCost.skeleton_nodes candidate <= s)
    by exact (FrontierSweep.skeleton_bound Hr).
  assert (Hwidth : forall v, In v vs -> key_bits positive_encoding v <= w).
  { intros v Hv. exact (FrontierSweep.width_bound Hr v
      (proj1 (Forall_forall _ _) (live_support p Reach.unrestricted Hready) v Hv)). }
  assert (Hlength : (length vs <= n)%nat).
  { exact (live_length p Reach.unrestricted n Hready (FrontierSweep.universe_bound Hr)). }
  assert (HlengthN : N.of_nat (length vs) <= nodes) by (unfold nodes; lia).
  pose proof (DomReachCost.reach_cost p Reach.unrestricted _ n m l b w a q h s h
    Hready Hr (FrontierSweep.admission_bound Hr)) as Hreach.
  pose proof (enumerate_live_cost p Reach.unrestricted _ n m l b w a q h s Hready Hr)
    as Henumerate.
  fold seen in Henumerate.
  pose proof (MapCost.elements_cost candidate) as Hbindings.
  pose proof (MapCost.size_cost candidate) as Hcount.
  assert (Hscan : TrieCost.trie_k * (1 + MapCost.skeleton_nodes candidate) <=
    TrieCost.trie_k * (1 + s)) by (apply N.mul_le_mono; lia).
  assert (Hdomains : Cost.ticks
    (forallb_c (DomCheckCost.binding_ok_c seen) (Map.elements candidate)) <=
    bindings * (2 * (2 + w) + 1)).
  { eapply N.le_trans.
    - apply (forallb_cost_on _ _ (2 * (2 + w))). intros vu Hvu.
      destruct (Hstored vu Hvu) as [Hv Hu].
      rewrite DomCheckCost.binding_ok_cost.
      pose proof (FrontierSweep.positive_mem_cost seen (fst vu) w Hv).
      pose proof (FrontierSweep.positive_mem_cost seen (snd vu) w Hu). lia.
    - apply N.mul_le_mono; [unfold bindings; rewrite <- Map.size_elements; lia|reflexivity]. }
  assert (Hends : Cost.ticks
    (forallb_c (DomCheckCost.ends_c (S (Map.size candidate)) candidate) vs) <=
      nodes * ((bindings + 2) * (1 + DomCheckCost.id_get_budget w) + 1)).
  { eapply N.le_trans.
    - apply (forallb_cost_on _ _ ((bindings + 2) * (1 + DomCheckCost.id_get_budget w))).
      intros v Hv.
      eapply N.le_trans; [apply DomCheckCost.ends_cost; [exact Hparents|now apply Hwidth]|].
      apply N.mul_le_mono; [unfold bindings; rewrite !Nat2N.inj_succ; lia|reflexivity].
    - apply N.mul_le_mono; [exact HlengthN|reflexivity]. }
  assert (Havoid : forall d, In d vs -> Cost.ticks (DomCheckCost.avoiding_c p d) <= avoid).
  { intros d Hd. rewrite DomCheckCost.avoiding_cost.
    pose proof (singleton_cost d w (Hwidth d Hd)) as Hsingleton.
    pose proof (DomReachCost.reach_cost p (Reach.blocked d) _ n m l b w a q h s (3 + w)
      Hready Hr ltac:(intros v Hv; apply DomReachCost.blocked_admission_cost;
        exact (FrontierSweep.width_bound Hr v Hv))) as Hclosure.
    unfold avoid, nodes. lia. }
  assert (Hpairs : forall d avoiding, In d vs ->
    Cost.ticks (forallb_c (DomCheckCost.pair_ok_c candidate avoiding d) vs) <=
      nodes * (pair + 1)).
  { intros d avoiding Hd. eapply N.le_trans.
    - apply (forallb_cost_on _ _ pair). intros v Hv.
      rewrite DomCheckCost.pair_ok_cost.
      pose proof (DomCheckCost.ancestor_numeric_cost candidate d v w b s Hparents
        (Hwidth d Hd) (Hwidth v Hv) Hsize Hskeleton) as Hanc.
      pose proof (FrontierSweep.positive_mem_cost avoiding v w (Hwidth v Hv)) as Hmem.
      unfold pair. lia.
    - apply N.mul_le_mono; [exact HlengthN|reflexivity]. }
  assert (Houter : Cost.ticks (forallb_c (fun d =>
    let* avoiding := DomCheckCost.avoiding_c p d in
    forallb_c (DomCheckCost.pair_ok_c candidate avoiding d) vs) vs) <=
      nodes * (avoid + nodes * (pair + 1) + 1)).
  { eapply N.le_trans.
    - apply (forallb_cost_on _ _ (avoid + nodes * (pair + 1))). intros d Hd.
      rewrite Cost.ticks_bind. pose proof (Havoid d Hd).
      pose proof (Hpairs d (Cost.value (DomCheckCost.avoiding_c p d)) Hd). lia.
    - apply N.mul_le_mono; [exact HlengthN|reflexivity]. }
  rewrite DomCheckCost.check_c_equation.
  rewrite !Cost.ticks_bind, FrontierSweep.reach_value.
  fold seen. fold (FinSet.elements seen). fold vs.
  fold (Map.elements candidate). fold (Map.size candidate).
  autorewrite with galois_cost.
  rewrite !N.add_0_r.
  unfold checker_bound. cbn zeta. fold nodes bindings pair avoid.
  unfold nodes, bindings, pair, avoid in *. lia.
Qed.

End DomCheckBound.
