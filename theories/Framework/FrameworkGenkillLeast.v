(** * Indexed gen/kill paths

    Least solutions are characterized by paths over the actual seed and edge inventories.
    For example, may paths can start empty in an entry-unreachable component.
    Builds on: FrameworkGenkillSound, BaseRel and FixpointLeast. *)

From Stdlib Require Import List Bool Arith NArith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseEq BaseSet BaseRel.
From Galois.Lattice Require Import LatticeCore LatticeSet.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramCfg.
From Galois.Fixpoint Require Import FixpointSystem FixpointLeast FixpointAnalysis.
From Galois.Framework Require Import FrameworkDense FrameworkBitvector FrameworkGenkillSound.
Import List.ListNotations Cost.Notations.
Import GenkillSound.
Local Open Scope nat_scope.

Module GenkillLeast.

(** An oriented path reads the same source unknown as the generated flow row. *)
Definition from {N E U} (P : Bitvector.t N E U) :=
  Dense.from (Bitvector.may_dense P (Bitvector.prepare P)).

(** An oriented path writes the same destination unknown as the generated flow row. *)
Definition into {N E U} (P : Bitvector.t N E U) :=
  Dense.into (Bitvector.may_dense P (Bitvector.prepare P)).

(** Indexed steps use listed edges and the generator's orientation in both directions. *)
Definition oriented {N E U} (P : Bitvector.t N E U) a e b :=
  In e (Cfg.edges (Bitvector.cfg P)) /\ a = from P e /\ b = into P e.

(** Paths retain every edge label and both oriented endpoints. *)
Definition path {N E U} (P : Bitvector.t N E U) := Rel.lpath (oriented P).

(** Path evaluation is a costed left fold of the frozen prepared transfer. *)
Definition apply_path_c {N E U} (P : Bitvector.t N E U) es a :=
  let* p := Bitvector.prepare_c P in
  fold_left_c (fun a e => Bitvector.may_transfer_c p e a) es a.

(** The pure path fold is the value projection of its charged evaluator. *)
Definition apply_path {N E U} (P : Bitvector.t N E U) es a :=
  Cost.value (apply_path_c P es a).

(** The path evaluator agrees with the literal left fold of prepared transfers. *)
Theorem apply_path_equation {N E U} (P : Bitvector.t N E U) es a :
  apply_path P es a =
    fold_left (fun a e => Bitvector.may_transfer (Bitvector.prepare P) e a) es a.
Proof.
  unfold apply_path, apply_path_c; rewrite Cost.value_bind; apply value_fold_left_c.
Qed.

(** Path evaluation charges preparation, fold visits and invariant-bounded transfer callbacks. *)
Theorem apply_path_cost {N E U} (P : Bitvector.t N E U) es a
    (I : set_t (Bitvector.fact_enc P) -> Prop) k :
  (forall a e, I a -> In e es ->
    I (Bitvector.may_transfer (Bitvector.prepare P) e a) /\
    (Cost.ticks (Bitvector.may_transfer_c (Bitvector.prepare P) e a) <= k)%N) ->
  I a ->
  (Cost.ticks (apply_path_c P es a) <= Cost.ticks (Bitvector.prepare_c P) +
    N.of_nat (length es) * (k + 1))%N.
Proof.
  intros Hcost Ha; unfold apply_path_c; rewrite Cost.ticks_bind.
  apply N.add_le_mono_l.
  pose proof (ticks_fold_left_c_potential
    (fun a e => Bitvector.may_transfer_c (Bitvector.prepare P) e a) I
    (fun _ => 0%N) k es a) as Hbound.
  assert (Hstep : forall a e, I a -> In e es ->
    I (Bitvector.may_transfer (Bitvector.prepare P) e a) /\
    (Cost.ticks (Bitvector.may_transfer_c (Bitvector.prepare P) e a) + 0 <= k + 0)%N).
  { intros a' e HI He; destruct (Hcost a' e HI He) as [Hpreserve Hticks].
    split; [exact Hpreserve|lia]. }
  specialize (Hbound Hstep Ha); cbn beta in Hbound.
  rewrite !N.add_0_r in Hbound; exact Hbound.
Qed.

(** Finite start conversion is charged before preparing and traversing the path. *)
Definition path_value_c {N E U} (P : Bitvector.t N E U) xs es :=
  let* a := set_of_list_c (Bitvector.fact_enc P) xs in
  apply_path_c P es a.

(** A path value uses its actual finite start inventory, without a universe clamp. *)
Definition path_value {N E U} (P : Bitvector.t N E U) xs es :=
  Cost.value (path_value_c P xs es).

(** The costed path value is the path fold applied to the finite start list. *)
Theorem path_value_equation {N E U} (P : Bitvector.t N E U) xs es :
  path_value P xs es = apply_path P es (set_of_list (Bitvector.fact_enc P) xs).
Proof.
  unfold path_value, path_value_c; rewrite Cost.value_bind; reflexivity.
Qed.

(** Start-list construction and path evaluation retain their separate charges. *)
Theorem path_value_cost {N E U} (P : Bitvector.t N E U) xs es :
  Cost.ticks (path_value_c P xs es) =
    (Cost.ticks (set_of_list_c (Bitvector.fact_enc P) xs) +
     Cost.ticks (apply_path_c P es (set_of_list (Bitvector.fact_enc P) xs)))%N.
Proof.
  unfold path_value_c; rewrite Cost.ticks_bind; reflexivity.
Qed.

Lemma apply_path_nil {N E U} (P : Bitvector.t N E U) a :
  apply_path P [] a = a.
Proof.
  rewrite apply_path_equation; reflexivity.
Qed.

Lemma apply_path_cons {N E U} (P : Bitvector.t N E U) e es a :
  apply_path P (e :: es) a =
    apply_path P es (Bitvector.may_transfer (Bitvector.prepare P) e a).
Proof.
  rewrite !apply_path_equation; reflexivity.
Qed.

Lemma apply_path_snoc {N E U} (P : Bitvector.t N E U) es e a :
  apply_path P (es ++ [e]) a =
    Bitvector.may_transfer (Bitvector.prepare P) e (apply_path P es a).
Proof.
  rewrite !apply_path_equation, fold_left_app; reflexivity.
Qed.

(** May starts include every empty listed node and every present generated boundary. *)
Inductive may_start {N E U} (P : Bitvector.t N E U) : N -> set_t (Bitvector.fact_enc P) -> Prop :=
  | start_empty n : In n (Graph.nodes (Cfg.graph (Bitvector.cfg P))) ->
      may_start P n (set_empty (Bitvector.fact_enc P))
  | start_boundary n xs : In n (Bitvector.seeds P) -> Bitvector.boundary P n = Some xs ->
      may_start P n (set_of_list (Bitvector.fact_enc P) xs).

(** May path production includes implicit starts even when no entry reaches the query. *)
Definition produces {N E U} (P : Bitvector.t N E U) n u :=
  exists root a es, may_start P root a /\ path P root es n /\ member (apply_path P es a) u.

(** Must paths start at actual present finite boundaries from the generated seed inventory. *)
Definition boundary_path {N E U} (P : Bitvector.t N E U) root xs es n :=
  In root (Bitvector.seeds P) /\ Bitvector.boundary P root = Some xs /\ path P root es n.

(** Universal finite-boundary path membership is vacuous at a node with no boundary path. *)
Definition keeps {N E U} (P : Bitvector.t N E U) n u :=
  forall root xs es, boundary_path P root xs es n -> member (path_value P xs es) u.

Lemma edge_nodes {N E U} (P : Bitvector.t N E U) :
  graph_wf (Cfg.graph (Bitvector.cfg P)) ->
  forall e, In e (Cfg.edges (Bitvector.cfg P)) ->
    In (from P e) (Graph.nodes (Cfg.graph (Bitvector.cfg P))) /\
    In (into P e) (Graph.nodes (Cfg.graph (Bitvector.cfg P))).
Proof.
  intros Hwf e He; apply Cfg.edges_spec in He as [n [Hn He]].
  pose proof (out_target_in Hwf n e Hn He) as Htarget.
  pose proof (out_source Hwf n e He) as Hsource.
  unfold from, into, Dense.from, Dense.into, Dense.from_c, Dense.into_c;
    cbn [Bitvector.may_dense Dense.cfg Dense.dir].
  destruct (Bitvector.dir P).
  - change (In (Graph.source (Cfg.graph (Bitvector.cfg P)) e)
      (Graph.nodes (Cfg.graph (Bitvector.cfg P))) /\
      In (Graph.target (Cfg.graph (Bitvector.cfg P)) e)
      (Graph.nodes (Cfg.graph (Bitvector.cfg P)))).
    rewrite Hsource; split; assumption.
  - change (In (Graph.target (Cfg.graph (Bitvector.cfg P)) e)
      (Graph.nodes (Cfg.graph (Bitvector.cfg P))) /\
      In (Graph.source (Cfg.graph (Bitvector.cfg P)) e)
      (Graph.nodes (Cfg.graph (Bitvector.cfg P)))).
    rewrite Hsource; split; assumption.
Qed.

Lemma seed_node {N E U} (P : Bitvector.t N E U) :
  graph_wf (Cfg.graph (Bitvector.cfg P)) ->
  forall n, In n (Bitvector.seeds P) -> In n (Graph.nodes (Cfg.graph (Bitvector.cfg P))).
Proof.
  intros Hwf n Hn; unfold Bitvector.seeds in Hn; destruct (Bitvector.dir P).
  - exact (entries_in Hwf n Hn).
  - exact Hn.
Qed.

Lemma transfer_monotone {N E U} (P : Bitvector.t N E U)
    (HE : encoding_laws (Cfg.edge_enc (Bitvector.cfg P)))
    (HU : encoding_laws (Bitvector.fact_enc P)) e a b :
  In e (Cfg.edges (Bitvector.cfg P)) ->
  (forall u, member a u -> member b u) ->
  forall u, member (Bitvector.may_transfer (Bitvector.prepare P) e a) u ->
    member (Bitvector.may_transfer (Bitvector.prepare P) e b) u.
Proof.
  intros He Hab u Hu; apply (transfer_member P e b u HE HU He).
  apply (transfer_member P e a u HE HU He) in Hu.
  destruct Hu as [[Hu Hkill]|Hu].
  - left; split; [apply Hab; exact Hu|exact Hkill].
  - right; exact Hu.
Qed.

Lemma path_monotone {N E U} (P : Bitvector.t N E U)
    (HE : encoding_laws (Cfg.edge_enc (Bitvector.cfg P)))
    (HU : encoding_laws (Bitvector.fact_enc P)) root es n :
  path P root es n -> forall a b, (forall u, member a u -> member b u) ->
    forall u, member (apply_path P es a) u -> member (apply_path P es b) u.
Proof.
  intro Hpath; induction Hpath as [n|x e y es n [He [Hx Hy]] Hpath IH];
    intros a b Hab u Hu.
  - rewrite !apply_path_nil in *; apply Hab; exact Hu.
  - rewrite !apply_path_cons in *; eapply IH; [|exact Hu].
    eapply transfer_monotone; eassumption.
Qed.

Lemma path_below_post {N E U} (P : Bitvector.t N E U)
    (HE : encoding_laws (Cfg.edge_enc (Bitvector.cfg P)))
    (HU : encoding_laws (Bitvector.fact_enc P)) sigma root es n :
  path P root es n ->
  (forall e, In e (Cfg.edges (Bitvector.cfg P)) ->
    leb (may (Bitvector.fact_enc P))
      (Bitvector.may_transfer (Bitvector.prepare P) e (sigma (from P e)))
      (sigma (into P e)) = true) ->
  forall a, (forall u, member a u -> member (sigma root) u) ->
    forall u, member (apply_path P es a) u -> member (sigma n) u.
Proof.
  intro Hpath; induction Hpath as [n|x e y es n [He [-> ->]] Hpath IH];
    intros Hflow a Ha u Hu.
  - rewrite apply_path_nil in Hu; apply Ha; exact Hu.
  - rewrite apply_path_cons in Hu; eapply IH; [exact Hflow| |exact Hu].
    intros v Hv; apply (member_monotone _ HU _ _ v (Hflow e He)).
    eapply transfer_monotone; eassumption.
Qed.

(** Every produced may fact belongs to every actual may post-solution. *)
Theorem produces_in_post {N E U} (P : Bitvector.t N E U)
    (HN : encoding_laws (Cfg.node_enc (Bitvector.cfg P)))
    (HE : encoding_laws (Cfg.edge_enc (Bitvector.cfg P)))
    (HU : encoding_laws (Bitvector.fact_enc P)) sigma n u :
  post_solution (Analysis.lat (Bitvector.may_analysis P))
    (Analysis.system (Bitvector.may_analysis P)) sigma ->
  produces P n u -> member (sigma n) u.
Proof.
  intros Hpost [root [a [es [Hstart [Hpath Hu]]]]].
  destruct (proj1 (Bitvector.may_source_post_iff P sigma HN HU) Hpost) as [Hseed Hflow].
  eapply path_below_post; [exact HE|exact HU|exact Hpath|exact Hflow| |exact Hu].
  intros v Hv; destruct Hstart as [root Hroot|root xs Hroot Hb].
  - change (FinSet.mem (Bitvector.fact_enc P) v FinSet.empty = true) in Hv.
    rewrite FinSet.mem_empty in Hv; discriminate.
  - exact (member_monotone _ HU _ _ v (Hseed root xs Hroot Hb) Hv).
Qed.

(* Finite Boolean closure is proof-only separation evidence. It is not a solver or fuel bound. *)
Local Lemma count_mono {A} (xs : list A) (p q : A -> bool) :
  (forall x, In x xs -> p x = true -> q x = true) ->
  length (filter p xs) <= length (filter q xs).
Proof.
  induction xs as [|x xs IH]; intro Hpq; cbn; [lia|].
  assert (Ht : length (filter p xs) <= length (filter q xs)).
  { apply IH; intros y Hy; apply Hpq; right; exact Hy. }
  specialize (Hpq x (or_introl eq_refl)); destruct (p x), (q x); cbn in *;
    try discriminate; lia.
Qed.

Local Lemma count_equal {A} (xs : list A) (p q : A -> bool) :
  (forall x, In x xs -> p x = true -> q x = true) ->
  length (filter p xs) = length (filter q xs) ->
  forall x, In x xs -> p x = q x.
Proof.
  induction xs as [|a xs IH]; intros Hpq Hcount x Hx; [contradiction|].
  assert (Ht : forall y, In y xs -> p y = true -> q y = true).
  { intros y Hy; apply Hpq; right; exact Hy. }
  pose proof (count_mono xs p q Ht) as Hle.
  specialize (Hpq a (or_introl eq_refl)); cbn in Hcount.
  destruct (p a) eqn:Hp, (q a) eqn:Hq; cbn in Hcount; try discriminate;
    try (exfalso; lia).
  - destruct Hx as [<-|Hx]; [rewrite Hp, Hq; reflexivity|apply IH; [exact Ht|lia|exact Hx]].
  - destruct Hx as [<-|Hx]; [rewrite Hp, Hq; reflexivity|apply IH; [exact Ht|lia|exact Hx]].
Qed.

Local Lemma finite_closure {A} (xs : list A) (F : (A -> bool) -> A -> bool)
    (I : (A -> bool) -> Prop) :
  (forall b x, b x = true -> F b x = true) ->
  (forall b, I b -> I (F b)) -> I (fun _ => false) ->
  exists b, I b /\ forall x, In x xs -> F b x = b x.
Proof.
  intros Hgrow Hstep Hempty.
  assert (Hbound : forall p : A -> bool, length (filter p xs) <= length xs).
  { intro p; induction xs as [|x xs IH]; cbn; [lia|]; destruct (p x); cbn; lia. }
  assert (Hsearch : forall k b, length xs - length (filter b xs) <= k -> I b ->
    exists c, I c /\ forall x, In x xs -> F c x = c x).
  { induction k as [|k IH]; intros b Hcapacity Hb.
    - pose proof (Hbound (F b)).
      pose proof (count_mono xs b (F b) (fun x _ => Hgrow b x)).
      exists b; split; [exact Hb|]; intros x Hx; symmetry.
      apply (count_equal xs b (F b)); [intros y _; apply Hgrow|lia|exact Hx].
    - pose proof (Hbound (F b)).
      pose proof (count_mono xs b (F b) (fun x _ => Hgrow b x)).
      destruct (Nat.eq_dec (length (filter b xs)) (length (filter (F b) xs))) as [Heq|Hne].
      + exists b; split; [exact Hb|]; intros x Hx; symmetry.
        apply (count_equal xs b (F b)); [intros y _; apply Hgrow|exact Heq|exact Hx].
      + apply (IH (F b)); [lia|apply Hstep; exact Hb]. }
  apply (Hsearch (length xs) (fun _ => false)); [lia|exact Hempty].
Qed.

(** A listed boundary contributes its exact finite facts to may path production. *)
Lemma produces_seed {N E U} (P : Bitvector.t N E U)
    (HU : encoding_laws (Bitvector.fact_enc P)) n xs u :
  In n (Bitvector.seeds P) -> Bitvector.boundary P n = Some xs ->
  In u xs -> produces P n u.
Proof.
  intros Hn Hb Hu; exists n, (set_of_list (Bitvector.fact_enc P) xs), [].
  split; [eapply start_boundary; eassumption|]; split; [constructor|].
  rewrite apply_path_nil; apply member_list; assumption.
Qed.

Lemma produces_step {N E U} (P : Bitvector.t N E U)
    (HE : encoding_laws (Cfg.edge_enc (Bitvector.cfg P)))
    (HU : encoding_laws (Bitvector.fact_enc P)) e u :
  graph_wf (Cfg.graph (Bitvector.cfg P)) -> In e (Cfg.edges (Bitvector.cfg P)) ->
  ((produces P (from P e) u /\ ~ In u (Bitvector.kill P e)) \/
    In u (Bitvector.gen P e)) -> produces P (into P e) u.
Proof.
  intros Hwf He [[Hproduce Hkill]|Hgen].
  - destruct Hproduce as [root [a [es [Hstart [Hpath Hu]]]]].
    exists root, a, (es ++ [e]); split; [exact Hstart|]; split.
    + eapply Rel.lpath_app; [exact Hpath|].
      econstructor; [split; [exact He|split; reflexivity]|constructor].
    + rewrite apply_path_snoc; apply transfer_member; [exact HE|exact HU|exact He|].
      left; split; assumption.
  - exists (from P e), (set_empty (Bitvector.fact_enc P)), [e].
    split; [apply start_empty; exact (proj1 (edge_nodes P Hwf e He))|]; split.
    + econstructor; [split; [exact He|split; reflexivity]|constructor].
    + rewrite apply_path_cons, apply_path_nil.
      apply transfer_member; [exact HE|exact HU|exact He|right; exact Hgen].
Qed.

Section MaySeparation.
Context {N E U} (P : Bitvector.t N E U)
  (HN : encoding_laws (Cfg.node_enc (Bitvector.cfg P)))
  (HE : encoding_laws (Cfg.edge_enc (Bitvector.cfg P)))
  (HU : encoding_laws (Bitvector.fact_enc P)).

Local Definition seed_has x n :=
  existsb (fun root => eqb (Cfg.node_enc (Bitvector.cfg P)) n root &&
    match Bitvector.boundary P root with
    | None => false
    | Some xs => existsb (eqb (Bitvector.fact_enc P) x) xs
    end) (Bitvector.seeds P).

Local Lemma seed_has_spec x n :
  seed_has x n = true <->
    exists xs, In n (Bitvector.seeds P) /\ Bitvector.boundary P n = Some xs /\ In x xs.
Proof.
  unfold seed_has; rewrite existsb_exists; split.
  - intros [root [Hr Hhit]]; apply andb_true_iff in Hhit as [Hnr Hhit].
    apply (eqb_true_iff _ HN) in Hnr; subst root.
    destruct (Bitvector.boundary P n) as [xs|] eqn:Hb; [|discriminate].
    exists xs; split; [exact Hr|]; split; [reflexivity|].
    apply (proj1 (member_list _ HU xs x)); unfold member.
    rewrite set_of_list_raw, FinSet.mem_of_list; exact Hhit.
  - intros [xs [Hn [Hb Hx]]]; exists n; split; [exact Hn|].
    rewrite eqb_refl, Hb; cbn; apply existsb_exists; exists x.
    split; [exact Hx|apply eqb_refl].
Qed.

Local Definition may_close x b n :=
  b n || seed_has x n ||
  existsb (fun e => eqb (Cfg.node_enc (Bitvector.cfg P)) n (into P e) &&
    (existsb (eqb (Bitvector.fact_enc P) x) (Bitvector.gen P e) ||
      (b (from P e) && negb (existsb (eqb (Bitvector.fact_enc P) x)
        (Bitvector.kill P e))))) (Cfg.edges (Bitvector.cfg P)).

Local Lemma may_close_spec x b n :
  may_close x b n = true <->
    b n = true \/ (exists xs, In n (Bitvector.seeds P) /\
      Bitvector.boundary P n = Some xs /\ In x xs) \/
    exists e, In e (Cfg.edges (Bitvector.cfg P)) /\ n = into P e /\
      (In x (Bitvector.gen P e) \/ (b (from P e) = true /\ ~ In x (Bitvector.kill P e))).
Proof.
  unfold may_close; rewrite !orb_true_iff, seed_has_spec, existsb_exists.
  assert (Hlist : forall xs, existsb (eqb (Bitvector.fact_enc P) x) xs = true <-> In x xs).
  { intro xs; rewrite <- (member_list _ HU xs x); unfold member.
    rewrite set_of_list_raw, FinSet.mem_of_list; reflexivity. }
  assert (Hnot : forall xs, existsb (eqb (Bitvector.fact_enc P) x) xs = false <->
    ~ In x xs).
  { intro xs; rewrite <- Hlist; destruct (existsb _ xs); intuition discriminate. }
  setoid_rewrite andb_true_iff; setoid_rewrite (eqb_true_iff _ HN).
  setoid_rewrite orb_true_iff; setoid_rewrite andb_true_iff.
  setoid_rewrite negb_true_iff; setoid_rewrite Hlist; setoid_rewrite Hnot; tauto.
Qed.

Local Lemma may_closure x :
  graph_wf (Cfg.graph (Bitvector.cfg P)) ->
  exists b, (forall n, b n = true -> produces P n x) /\
    forall n, In n (Graph.nodes (Cfg.graph (Bitvector.cfg P))) -> may_close x b n = b n.
Proof.
  intro Hwf; apply (finite_closure _ (may_close x)
    (fun b => forall n, b n = true -> produces P n x)).
  - intros b n Hb; apply may_close_spec; left; exact Hb.
  - intros b Hb n Hn; apply may_close_spec in Hn.
    destruct Hn as [Hn|[[xs [Hseed [Hboundary Hx]]]|[e [He [-> Hflow]]]]].
    + apply Hb; exact Hn.
    + eapply produces_seed; eassumption.
    + eapply produces_step; [exact HE|exact HU|exact Hwf|exact He|].
      destruct Hflow as [Hgen|[Hfrom Hkill]]; [right; exact Hgen|].
      left; split; [apply Hb; exact Hfrom|exact Hkill].
  - intros n Hbad; discriminate.
Qed.

Local Definition may_candidate x (b : N -> bool) n :=
  set_of_list (Bitvector.fact_enc P)
    (filter (fun y => negb (eqb (Bitvector.fact_enc P) y x) || b n) (Bitvector.universe P)).

Local Lemma may_candidate_spec x b n y :
  member (may_candidate x b n) y <->
    In y (Bitvector.universe P) /\ (y <> x \/ b n = true).
Proof.
  unfold may_candidate; rewrite member_list by exact HU.
  rewrite filter_In, orb_true_iff, negb_true_iff, (eqb_false_iff _ HU); reflexivity.
Qed.

Local Lemma may_candidate_post x b :
  graph_wf (Cfg.graph (Bitvector.cfg P)) -> Bitvector.supported P ->
  (forall n, In n (Graph.nodes (Cfg.graph (Bitvector.cfg P))) -> may_close x b n = b n) ->
  post_solution (Analysis.lat (Bitvector.may_analysis P))
    (Analysis.system (Bitvector.may_analysis P)) (may_candidate x b).
Proof.
  intros Hwf [Hedges Hseeds] Hclosed; apply (Bitvector.may_source_post_iff P _ HN HU).
  split.
  - intros n xs Hn Hb; apply (may_leb _ HU); intros y Hy.
    apply (proj1 (member_list _ HU xs y)) in Hy.
    apply may_candidate_spec; split; [exact (Hseeds n xs Hn Hb y Hy)|].
    destruct (eqb_dec _ HU y x) as [->|Hne]; [right|left; exact Hne].
    rewrite <- Hclosed by (apply seed_node; assumption).
    apply may_close_spec; right; left; exists xs; repeat split; assumption.
  - intros e He; apply (may_leb _ HU); intros y Hy.
    apply (transfer_member P e _ y HE HU He) in Hy.
    apply may_candidate_spec; split.
    + destruct Hy as [[Hy _]|Hy].
      * apply may_candidate_spec in Hy; tauto.
      * exact (proj1 (Hedges e He) y Hy).
    + destruct (eqb_dec _ HU y x) as [->|Hne]; [right|left; exact Hne].
      rewrite <- Hclosed by exact (proj2 (edge_nodes P Hwf e He)).
      apply may_close_spec; right; right; exists e; split; [exact He|].
      split; [reflexivity|]; destruct Hy as [[Hy Hkill]|Hy]; [right|left; exact Hy].
      apply may_candidate_spec in Hy; destruct Hy as [_ [Hbad|Hy]]; [contradiction|].
      split; assumption.
Qed.

(** Actual least may solutions equal indexed path production in either orientation. *)
Theorem may_least_paths sigma :
  graph_wf (Cfg.graph (Bitvector.cfg P)) -> Bitvector.supported P ->
  least_solution (Analysis.lat (Bitvector.may_analysis P))
    (Analysis.system (Bitvector.may_analysis P)) sigma ->
  forall n u, In n (Graph.nodes (Cfg.graph (Bitvector.cfg P))) ->
    (member (sigma n) u <-> produces P n u).
Proof.
  intros Hwf Hsupport [Hpost Hleast] n u Hn; split.
  - intro Hu; destruct (may_closure u Hwf) as [b [Hsound Hclosed]].
    pose proof (Hleast _ (may_candidate_post u b Hwf Hsupport Hclosed) n) as Hle.
    apply (member_monotone _ HU _ _ u Hle) in Hu.
    apply may_candidate_spec in Hu; destruct Hu as [_ [Hbad|Hu]]; [contradiction|].
    apply Hsound; exact Hu.
  - eapply produces_in_post; eassumption.
Qed.

End MaySeparation.

(** Syntactic finite-use liveness permits a generated use without any exit endpoint. *)
Inductive syntactic_live {N E U} (P : Bitvector.t N E U) (u : U) : N -> Prop :=
  | live_seed n xs : In n (Bitvector.seeds P) -> Bitvector.boundary P n = Some xs ->
      In u xs -> syntactic_live P u n
  | live_use e : In e (Cfg.edges (Bitvector.cfg P)) -> In u (Bitvector.gen P e) ->
      syntactic_live P u (into P e)
  | live_next e : In e (Cfg.edges (Bitvector.cfg P)) -> ~ In u (Bitvector.kill P e) ->
      syntactic_live P u (from P e) -> syntactic_live P u (into P e).

Lemma produces_live {N E U} (P : Bitvector.t N E U)
    (HE : encoding_laws (Cfg.edge_enc (Bitvector.cfg P)))
    (HU : encoding_laws (Bitvector.fact_enc P)) n u :
  produces P n u -> syntactic_live P u n.
Proof.
  intros [root [a [es [Hstart [Hpath Hu]]]]].
  assert (Hsound : forall root es n, path P root es n -> forall a,
    may_start P root a -> member (apply_path P es a) u -> syntactic_live P u n).
  { apply (Rel.lpath_snoc_ind (oriented P) (fun root es n => forall a,
      may_start P root a -> member (apply_path P es a) u -> syntactic_live P u n)).
    - intros v a' Hstart' Hu'; rewrite apply_path_nil in Hu'.
      destruct Hstart' as [v Hv|v xs Hv Hb].
      + change (FinSet.mem (Bitvector.fact_enc P) u FinSet.empty = true) in Hu'.
        rewrite FinSet.mem_empty in Hu'; discriminate.
      + eapply live_seed; try eassumption; exact (proj1 (member_list _ HU xs u) Hu').
    - intros v fs mid e dest Hprefix IH [He [Hmid Hdest]] a' Hstart' Hu'.
      subst mid dest; rewrite apply_path_snoc in Hu'.
      apply (transfer_member P e _ u HE HU He) in Hu'.
      destruct Hu' as [[Hu' Hkill]|Hu'].
      + eapply live_next; [exact He|exact Hkill|apply (IH a'); assumption].
      + eapply live_use; eassumption. }
  exact (Hsound root es n Hpath a Hstart Hu).
Qed.

(** Least backward may membership equals the legacy finite-use rules, including unreachable uses. *)
Theorem syntactic_live_least {N E U} (P : Bitvector.t N E U)
    (HN : encoding_laws (Cfg.node_enc (Bitvector.cfg P)))
    (HE : encoding_laws (Cfg.edge_enc (Bitvector.cfg P)))
    (HU : encoding_laws (Bitvector.fact_enc P)) sigma :
  graph_wf (Cfg.graph (Bitvector.cfg P)) -> Bitvector.supported P ->
  Bitvector.dir P = Backward ->
  least_solution (Analysis.lat (Bitvector.may_analysis P))
    (Analysis.system (Bitvector.may_analysis P)) sigma ->
  forall n u, In n (Graph.nodes (Cfg.graph (Bitvector.cfg P))) ->
    (member (sigma n) u <-> syntactic_live P u n).
Proof.
  intros Hwf Hsupport Hdir Hleast n u Hn.
  rewrite (may_least_paths P HN HE HU sigma Hwf Hsupport Hleast n u Hn); split.
  - apply produces_live; assumption.
  - intro Hlive; clear Hn.
    induction Hlive as [n xs Hseed Hb Hu|e He Hu|e He Hkill Hlive IH].
    + eapply produces_seed; eassumption.
    + eapply produces_step; [exact HE|exact HU|exact Hwf|exact He|right; exact Hu].
    + eapply produces_step; [exact HE|exact HU|exact Hwf|exact He|left; split; assumption].
Qed.

Section MustPaths.
Context {N E U} (P : Bitvector.t N E U)
  (HN : encoding_laws (Cfg.node_enc (Bitvector.cfg P)))
  (HE : encoding_laws (Cfg.edge_enc (Bitvector.cfg P)))
  (HU : encoding_laws (Bitvector.fact_enc P)).

Local Lemma transfer_order e a b :
  In e (Cfg.edges (Bitvector.cfg P)) ->
  leb (must (Bitvector.fact_enc P)) a b = true ->
  leb (must (Bitvector.fact_enc P))
    (Bitvector.must_transfer (Bitvector.prepare P) e a)
    (Bitvector.must_transfer (Bitvector.prepare P) e b) = true.
Proof.
  intros He Hab; rewrite !must_transfer_equation.
  rewrite must_leb_equation in Hab |- *.
  destruct a as [|a], b as [|b]; try reflexivity; try discriminate.
  apply (may_leb _ HU); eapply transfer_monotone; [exact HE|exact HU|exact He|].
  exact (proj1 (may_leb _ HU b a) Hab).
Qed.

Local Lemma must_path_bound sigma root es n :
  path P root es n ->
  (forall e, In e (Cfg.edges (Bitvector.cfg P)) ->
    leb (must (Bitvector.fact_enc P))
      (Bitvector.must_transfer (Bitvector.prepare P) e (sigma (from P e)))
      (sigma (into P e)) = true) ->
  forall a, leb (must (Bitvector.fact_enc P)) (Only a) (sigma root) = true ->
    leb (must (Bitvector.fact_enc P)) (Only (apply_path P es a)) (sigma n) = true.
Proof.
  intro Hpath; induction Hpath as [n|x e y es n [He [-> ->]] Hpath IH];
    intros Hflow a Ha.
  - rewrite apply_path_nil; exact Ha.
  - rewrite apply_path_cons; apply IH; [exact Hflow|].
    eapply (leb_trans (must_laws _ HU)); [|exact (Hflow e He)].
    exact (transfer_order e (Only a) _ He Ha).
Qed.

(** Each finite boundary path bounds every must post-solution in reverse inclusion. *)
Theorem must_boundary_path_bound sigma root xs es n :
  post_solution (Analysis.lat (Bitvector.must_analysis P))
    (Analysis.system (Bitvector.must_analysis P)) sigma ->
  boundary_path P root xs es n ->
  leb (must (Bitvector.fact_enc P)) (Only (path_value P xs es)) (sigma n) = true.
Proof.
  intros Hpost [Hroot [Hb Hpath]].
  destruct (proj1 (Bitvector.must_source_post_iff P sigma HN HU) Hpost) as [Hseed Hflow].
  exact (must_path_bound sigma root es n Hpath Hflow _ (Hseed root xs Hroot Hb)).
Qed.

(** Every least or nonleast must post-solution keeps its facts on every finite boundary path. *)
Theorem must_post_keeps sigma :
  post_solution (Analysis.lat (Bitvector.must_analysis P))
    (Analysis.system (Bitvector.must_analysis P)) sigma ->
  forall n u, must_member (sigma n) u -> keeps P n u.
Proof.
  intros Hpost n u Hu root xs es [Hroot [Hb Hpath]].
  destruct (proj1 (Bitvector.must_source_post_iff P sigma HN HU) Hpost) as [Hseed Hflow].
  pose proof (must_path_bound sigma root es n Hpath Hflow _
    (Hseed root xs Hroot Hb)) as Hbound.
  exact (must_member_antitone _ HU _ _ u Hbound Hu).
Qed.

Local Definition present n :=
  match Bitvector.boundary P n with Some _ => true | None => false end.

Local Definition reach_close r n :=
  r n ||
    existsb (fun root => eqb (Cfg.node_enc (Bitvector.cfg P)) n root && present root)
      (Bitvector.seeds P) ||
    existsb (fun e => eqb (Cfg.node_enc (Bitvector.cfg P)) n (into P e) && r (from P e))
      (Cfg.edges (Bitvector.cfg P)).

(** A boundary reaches a node through its actual present finite seed and an oriented path. *)
Definition boundary_reaches n :=
  exists root xs es, boundary_path P root xs es n.

Local Lemma reach_close_spec r n :
  reach_close r n = true <->
    r n = true \/ (In n (Bitvector.seeds P) /\ exists xs, Bitvector.boundary P n = Some xs) \/
    exists e, In e (Cfg.edges (Bitvector.cfg P)) /\ n = into P e /\ r (from P e) = true.
Proof.
  unfold reach_close; rewrite !orb_true_iff, !existsb_exists.
  setoid_rewrite andb_true_iff; setoid_rewrite (eqb_true_iff _ HN).
  assert (Hp : forall n, present n = true <-> exists xs, Bitvector.boundary P n = Some xs).
  { intro v; unfold present; destruct (Bitvector.boundary P v) as [xs|].
    - split; [intros _; exists xs; reflexivity|intros _; reflexivity].
    - split; [discriminate|intros [xs Hbad]; discriminate]. }
  setoid_rewrite Hp; split.
  - intros [[Hr|[root [Hroot [-> Hb]]]]|He].
    + left; exact Hr.
    + right; left; auto.
    + right; right; exact He.
  - intros [Hr|[[Hn Hb]|He]].
    + left; left; exact Hr.
    + left; right; exists n; auto.
    + right; exact He.
Qed.

Local Lemma reach_closure :
  exists r, (forall n, r n = true -> boundary_reaches n) /\
    forall n, In n (Graph.nodes (Cfg.graph (Bitvector.cfg P))) -> reach_close r n = r n.
Proof.
  apply (finite_closure _ reach_close (fun r => forall n, r n = true -> boundary_reaches n)).
  - intros r n Hr; apply reach_close_spec; left; exact Hr.
  - intros r Hr n Hn; apply reach_close_spec in Hn.
    destruct Hn as [Hn|[[Hn [xs Hb]]|[e [He [-> Hfrom]]]]].
    + apply Hr; exact Hn.
    + exists n, xs, []; split; [exact Hn|]; split; [exact Hb|constructor].
    + destruct (Hr _ Hfrom) as [root [xs [es [Hroot [Hb Hpath]]]]].
      exists root, xs, (es ++ [e]); split; [exact Hroot|]; split; [exact Hb|].
      eapply Rel.lpath_app; [exact Hpath|].
      econstructor; [split; [exact He|split; reflexivity]|constructor].
  - intros n Hbad; discriminate.
Qed.

Local Definition list_has x xs := existsb (eqb (Bitvector.fact_enc P) x) xs.

Local Lemma list_has_spec x xs : list_has x xs = true <-> In x xs.
Proof.
  unfold list_has; rewrite <- (member_list _ HU xs x); unfold member.
  rewrite set_of_list_raw, FinSet.mem_of_list; reflexivity.
Qed.

Local Lemma list_lacks_spec x xs : list_has x xs = false <-> ~ In x xs.
Proof.
  rewrite <- list_has_spec; destruct (list_has x xs); intuition discriminate.
Qed.

Local Definition bad_close x r b n :=
  b n ||
    existsb (fun root => eqb (Cfg.node_enc (Bitvector.cfg P)) n root &&
      match Bitvector.boundary P root with
      | Some xs => negb (list_has x xs)
      | None => false
      end) (Bitvector.seeds P) ||
    existsb (fun e => eqb (Cfg.node_enc (Bitvector.cfg P)) n (into P e) &&
      (r (from P e) && negb (list_has x (Bitvector.gen P e)) &&
        (list_has x (Bitvector.kill P e) || b (from P e)))) (Cfg.edges (Bitvector.cfg P)).

Local Lemma bad_close_spec x r b n :
  bad_close x r b n = true <->
    b n = true \/
    (exists xs, In n (Bitvector.seeds P) /\ Bitvector.boundary P n = Some xs /\ ~ In x xs) \/
    exists e, In e (Cfg.edges (Bitvector.cfg P)) /\ n = into P e /\
      r (from P e) = true /\ ~ In x (Bitvector.gen P e) /\
      (In x (Bitvector.kill P e) \/ b (from P e) = true).
Proof.
  unfold bad_close; rewrite !orb_true_iff, !existsb_exists.
  assert (Hb : forall n,
    (match Bitvector.boundary P n with Some xs => negb (list_has x xs) | None => false end) =
      true <-> exists xs, Bitvector.boundary P n = Some xs /\ ~ In x xs).
  { intro v; destruct (Bitvector.boundary P v) as [xs|].
    - rewrite negb_true_iff, list_lacks_spec; split.
      + intro Hx; exists xs; auto.
      + intros [ys [Hsame Hx]]; inversion Hsame; subst; exact Hx.
    - split; [discriminate|intros [xs [Hbad _]]; discriminate]. }
  setoid_rewrite andb_true_iff; setoid_rewrite (eqb_true_iff _ HN).
  setoid_rewrite Hb.
  repeat setoid_rewrite orb_true_iff.
  repeat setoid_rewrite andb_true_iff.
  repeat setoid_rewrite negb_true_iff.
  repeat setoid_rewrite list_has_spec.
  repeat setoid_rewrite list_lacks_spec.
  split.
  - intros [[Hn|[root [Hroot [-> [xs [Hboundary Hx]]]]]]|[e [He [Hn [[Hr Hgen] Hrest]]]]].
    + left; exact Hn.
    + right; left; exists xs; auto.
    + right; right; exists e; repeat split; try assumption.
      apply orb_true_iff in Hrest; destruct Hrest as [Hkill|Hnext].
      * left; apply list_has_spec; exact Hkill.
      * right; exact Hnext.
  - intros [Hn|[[xs [Hn [Hb' Hx]]]|[e [He [Hn [Hr [Hgen Hrest]]]]]]].
    + left; left; exact Hn.
    + left; right; exists n; split; [exact Hn|]; split; [reflexivity|exists xs; auto].
    + right; exists e; repeat split; try assumption.
      apply orb_true_iff; destruct Hrest as [Hkill|Hnext].
      * left; apply list_has_spec; exact Hkill.
      * right; exact Hnext.
Qed.

Local Definition bad_path x n :=
  exists root xs es, boundary_path P root xs es n /\ ~ member (path_value P xs es) x.

Local Lemma bad_closure x r :
  (forall n, r n = true -> boundary_reaches n) ->
  exists b, (forall n, b n = true -> bad_path x n) /\
    forall n, In n (Graph.nodes (Cfg.graph (Bitvector.cfg P))) -> bad_close x r b n = b n.
Proof.
  intro Hr; apply (finite_closure _ (bad_close x r)
    (fun b => forall n, b n = true -> bad_path x n)).
  - intros b n Hb; apply bad_close_spec; left; exact Hb.
  - intros b Hb n Hn; apply bad_close_spec in Hn.
    destruct Hn as [Hn|[[xs [Hn [Hboundary Hx]]]|[e [He [-> [Hfrom [Hgen Hrest]]]]]]].
    + apply Hb; exact Hn.
    + exists n, xs, []; split; [split; [exact Hn|split; [exact Hboundary|constructor]]|].
      rewrite path_value_equation, apply_path_nil; rewrite member_list by exact HU; exact Hx.
    + assert (Hw : exists root xs es, boundary_path P root xs es (from P e) /\
        (In x (Bitvector.kill P e) \/ ~ member (path_value P xs es) x)).
      { destruct Hrest as [Hkill|Hbad].
        - destruct (Hr _ Hfrom) as [root [xs [es Hpath]]].
          exists root, xs, es; auto.
        - destruct (Hb _ Hbad) as [root [xs [es [Hpath Hnot]]]].
          exists root, xs, es; auto. }
      destruct Hw as [root [xs [es [[Hroot [Hboundary Hpath]] Hlast]]]].
      exists root, xs, (es ++ [e]); split.
      * split; [exact Hroot|]; split; [exact Hboundary|].
        eapply Rel.lpath_app; [exact Hpath|].
        econstructor; [split; [exact He|split; reflexivity]|constructor].
      * rewrite path_value_equation, apply_path_snoc, (transfer_member P e _ x HE HU He).
        rewrite path_value_equation in Hlast; tauto.
  - intros n Hbad; discriminate.
Qed.

Local Definition must_candidate x (r b : N -> bool) n :=
  if r n then Only (set_of_list (Bitvector.fact_enc P) (if b n then [] else [x])) else All.

Local Lemma candidate_member x (b : N -> bool) n y :
  member (set_of_list (Bitvector.fact_enc P) (if b n then [] else [x])) y <->
    b n = false /\ y = x.
Proof.
  rewrite member_list by exact HU; destruct (b n); cbn; intuition congruence.
Qed.

Local Lemma must_candidate_post x r b :
  graph_wf (Cfg.graph (Bitvector.cfg P)) ->
  (forall n, In n (Graph.nodes (Cfg.graph (Bitvector.cfg P))) -> reach_close r n = r n) ->
  (forall n, In n (Graph.nodes (Cfg.graph (Bitvector.cfg P))) -> bad_close x r b n = b n) ->
  post_solution (Analysis.lat (Bitvector.must_analysis P))
    (Analysis.system (Bitvector.must_analysis P)) (must_candidate x r b).
Proof.
  intros Hwf Hreach Hbad; apply (Bitvector.must_source_post_iff P _ HN HU); split.
  - intros n xs Hn Hb.
    assert (Hr : r n = true).
    { rewrite <- Hreach by (apply seed_node; assumption).
      apply reach_close_spec; right; left; split; [exact Hn|exists xs; exact Hb]. }
    unfold must_candidate; rewrite Hr, must_leb_equation.
    apply (may_leb _ HU); intros y Hy; apply candidate_member in Hy as [Hbn ->].
    apply (member_list _ HU).
    destruct (in_dec (eqb_dec _ HU) x xs) as [Hx|Hx]; [exact Hx|].
    assert (Hbt : b n = true).
    { rewrite <- Hbad by (apply seed_node; assumption).
      apply bad_close_spec; right; left; exists xs; auto. }
    congruence.
  - intros e He.
    change (leb (must (Bitvector.fact_enc P))
      (Bitvector.must_transfer (Bitvector.prepare P) e (must_candidate x r b (from P e)))
      (must_candidate x r b (into P e)) = true).
    unfold must_candidate.
    rewrite must_transfer_equation, must_leb_equation.
    destruct (r (from P e)) eqn:Hfrom; [|reflexivity].
    assert (Hinto : r (into P e) = true).
    { rewrite <- Hreach by exact (proj2 (edge_nodes P Hwf e He)).
      apply reach_close_spec; right; right; exists e; auto. }
    rewrite Hinto.
    apply (may_leb _ HU); intros y Hy; apply candidate_member in Hy as [Hbn ->].
    apply (transfer_member P e _ x HE HU He).
    destruct (in_dec (eqb_dec _ HU) x (Bitvector.gen P e)) as [Hgen|Hgen];
      [right; exact Hgen|left].
    assert (Hnot : ~ (In x (Bitvector.kill P e) \/ b (from P e) = true)).
    { intro Hrest; assert (Hbinto : b (into P e) = true).
      { rewrite <- Hbad by exact (proj2 (edge_nodes P Hwf e He)).
        apply bad_close_spec; right; right; exists e; auto. }
      congruence. }
    split.
    + apply candidate_member; split; [destruct (b (from P e)); tauto|reflexivity].
    + tauto.
Qed.

(** Least reverse-inclusion solutions are exactly the universal finite-boundary path facts. *)
Theorem must_greatest_paths sigma :
  graph_wf (Cfg.graph (Bitvector.cfg P)) ->
  least_solution (Analysis.lat (Bitvector.must_analysis P))
    (Analysis.system (Bitvector.must_analysis P)) sigma ->
  forall n u, In n (Graph.nodes (Cfg.graph (Bitvector.cfg P))) ->
    (must_member (sigma n) u <-> keeps P n u).
Proof.
  intros Hwf [Hpost Hleast] n u Hn; split; [apply must_post_keeps; exact Hpost|].
  intro Hkeeps; destruct reach_closure as [r [Hr Hreach]].
  destruct (bad_closure u r Hr) as [b [Hb Hbad]].
  pose proof (Hleast _ (must_candidate_post u r b Hwf Hreach Hbad) n) as Hle.
  apply (must_member_antitone _ HU _ _ u Hle).
  unfold must_candidate; destruct (r n); [|exact I].
  assert (Hbn : b n = false).
  { destruct (b n) eqn:Hbn; [|reflexivity].
    destruct (Hb n Hbn) as [root [xs [es [Hpath Hnot]]]].
    exfalso; apply Hnot; exact (Hkeeps root xs es Hpath). }
  change (member (set_of_list (Bitvector.fact_enc P) (if b n then [] else [u])) u).
  apply candidate_member; split; [exact Hbn|reflexivity].
Qed.

(** No finite boundary path leaves the actual least must value at fresh All. *)
Theorem must_no_path_all sigma n :
  graph_wf (Cfg.graph (Bitvector.cfg P)) ->
  least_solution (Analysis.lat (Bitvector.must_analysis P))
    (Analysis.system (Bitvector.must_analysis P)) sigma ->
  In n (Graph.nodes (Cfg.graph (Bitvector.cfg P))) ->
  (sigma n = All <-> ~ boundary_reaches n).
Proof.
  intros Hwf [Hpost Hleast] Hn; split.
  - intros Hall [root [xs [es [Hroot [Hb Hpath]]]]].
    destruct (proj1 (Bitvector.must_source_post_iff P sigma HN HU) Hpost) as [Hseed Hflow].
    pose proof (must_path_bound sigma root es n Hpath Hflow _
      (Hseed root xs Hroot Hb)) as Hbound.
    rewrite Hall, must_leb_equation in Hbound; discriminate.
  - intro Hnone; destruct reach_closure as [r [Hr Hreach]].
    pose (candidate := fun n => if r n then Only (set_empty (Bitvector.fact_enc P)) else All).
    assert (Hcandidate : post_solution (Analysis.lat (Bitvector.must_analysis P))
      (Analysis.system (Bitvector.must_analysis P)) candidate).
    { apply (Bitvector.must_source_post_iff P _ HN HU); split.
      - intros root xs Hroot Hb; unfold candidate.
        assert (Hhit : r root = true).
        { rewrite <- Hreach by (apply seed_node; assumption).
          apply reach_close_spec; right; left; split; [exact Hroot|exists xs; exact Hb]. }
        rewrite Hhit, must_leb_equation.
        apply (bot_least (may_laws _ HU)).
      - intros e He.
        change (leb (must (Bitvector.fact_enc P))
          (Bitvector.must_transfer (Bitvector.prepare P) e (candidate (from P e)))
          (candidate (into P e)) = true).
        unfold candidate; rewrite must_transfer_equation, must_leb_equation.
        destruct (r (from P e)) eqn:Hfrom; [|reflexivity].
        assert (Hhit : r (into P e) = true).
        { rewrite <- Hreach by exact (proj2 (edge_nodes P Hwf e He)).
          apply reach_close_spec; right; right; exists e; auto. }
        rewrite Hhit.
        apply (bot_least (may_laws _ HU)). }
    pose proof (Hleast candidate Hcandidate n) as Hbound.
    change (leb (must (Bitvector.fact_enc P)) (sigma n) (candidate n) = true) in Hbound.
    unfold candidate in Hbound.
    destruct (r n) eqn:Hrn; [exfalso; apply Hnone; apply Hr; exact Hrn|].
    rewrite must_leb_equation in Hbound.
    destruct (sigma n); [reflexivity|discriminate].
Qed.

End MustPaths.

(** Coverage requires a boundary prefix for every listed start in the query's oriented cone. *)
Definition boundary_coverage {N E U} (P : Bitvector.t N E U) n :=
  forall root es, In root (Graph.nodes (Cfg.graph (Bitvector.cfg P))) ->
    path P root es n ->
    exists entry xs pre, boundary_path P entry xs pre root.

(** Boundary production uses present boundaries and has no implicit empty starts. *)
Definition boundary_produces {N E U} (P : Bitvector.t N E U) n u :=
  exists root xs es, boundary_path P root xs es n /\ member (path_value P xs es) u.

Lemma apply_path_app {N E U} (P : Bitvector.t N E U) es fs a :
  apply_path P (es ++ fs) a = apply_path P fs (apply_path P es a).
Proof.
  rewrite !apply_path_equation, fold_left_app; reflexivity.
Qed.

(** Oriented cone coverage absorbs all implicit empty starts into actual boundary paths. *)
Theorem may_boundary_paths {N E U} (P : Bitvector.t N E U)
    (HN : encoding_laws (Cfg.node_enc (Bitvector.cfg P)))
    (HE : encoding_laws (Cfg.edge_enc (Bitvector.cfg P)))
    (HU : encoding_laws (Bitvector.fact_enc P)) sigma n u :
  graph_wf (Cfg.graph (Bitvector.cfg P)) -> Bitvector.supported P ->
  least_solution (Analysis.lat (Bitvector.may_analysis P))
    (Analysis.system (Bitvector.may_analysis P)) sigma ->
  In n (Graph.nodes (Cfg.graph (Bitvector.cfg P))) -> boundary_coverage P n ->
  (member (sigma n) u <-> boundary_produces P n u).
Proof.
  intros Hwf Hsupport Hleast Hn Hcoverage.
  rewrite (may_least_paths P HN HE HU sigma Hwf Hsupport Hleast n u Hn); split.
  - intros [root [a [es [Hstart [Hpath Hu]]]]].
    destruct Hstart as [root Hroot|root xs Hroot Hb].
    + destruct (Hcoverage root es Hroot Hpath) as [entry [xs [pre [Hentry [Hb Hpre]]]]].
      exists entry, xs, (pre ++ es); split.
      * split; [exact Hentry|]; split; [exact Hb|eapply Rel.lpath_app; eassumption].
      * rewrite path_value_equation, apply_path_app.
        eapply path_monotone; [exact HE|exact HU|exact Hpath| |exact Hu].
        intros v Hv; change (FinSet.mem (Bitvector.fact_enc P) v FinSet.empty = true) in Hv.
        rewrite FinSet.mem_empty in Hv; discriminate.
    + exists root, xs, es; split; [repeat split; assumption|exact Hu].
  - intros [root [xs [es [[Hroot [Hb Hpath]] Hu]]]].
    exists root, (set_of_list (Bitvector.fact_enc P) xs), es.
    split; [eapply start_boundary; eassumption|split; assumption].
Qed.

End GenkillLeast.
