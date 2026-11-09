(** * Numerical costs of raw value propagation

    Listed summary destinations and raw call endpoints contribute separate finite inventories.
    For example, an unlisted seed still pays for its actual value update and pending key.
    Builds on: FrameworkTabValues, FrameworkTabValueProgress and primitive encoding costs. *)

From Stdlib Require Import List Arith NArith Lia Ring.
From Galois.Cost Require Import CostMonad CostList CostLoop CostBound.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet BaseIndex BaseIndexCost.
From Galois.Lattice Require Import LatticeCore LatticeHeight.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramCfg ProgramIcfg.
From Galois.Framework Require Import FrameworkUtil FrameworkMicro FrameworkIfds FrameworkIde
  FrameworkTabulate FrameworkTabValues FrameworkTabPaths FrameworkTabCost FrameworkTabEncodingCost
  FrameworkTabPrepareCost FrameworkTabRunCost FrameworkTabCheckCost FrameworkTabValueProgress.
Import List.ListNotations Cost.Notations.

Module TabValueRunCost.

(** Value coordinates contain the seed, raw roots/endpoints and listed summary destinations. *)
Definition coordinate {N E P D A F} (I : Ide.t N E P D A F) start v :=
  v = start \/ TabRunCost.coordinate I (fst start) v \/ In v (IdeValue.vertices I).

(** Primitive value duties use the finite key domain and the entire value/function domains. *)
Record primitives {N E P D A F} (I : Ide.t N E P D A F) start e w m : Prop := {
  node : forall v, coordinate I start v ->
    TabEncodingCost.bounded (Cfg.node_enc (Icfg.cfg (Ifds.icfg (Ide.ifds I))))
      (fst v) e w;
  fact : forall v, coordinate I start v ->
    match snd v with
    | Some d => TabEncodingCost.bounded (Ifds.fact_enc (Ide.ifds I)) d e w
    | None => True
    end;
  apply : forall f a, (Cost.ticks (Micro.apply_c (Ide.micro I) f a) <= m)%N;
  compare : forall a b, (Cost.ticks (leb_c (Ide.values I) a b) <= m)%N;
  joining : forall a b, (Cost.ticks (join_c (Ide.values I) a b) <= m)%N
}.
Arguments node {N E P D A F I start e w m}.
Arguments fact {N E P D A F I start e w m}.
Arguments apply {N E P D A F I start e w m}.
Arguments compare {N E P D A F I start e w m}.
Arguments joining {N E P D A F I start e w m}.

Definition vertices {N E P D A F} (I : Ide.t N E P D A F) :=
  (TabPrepareCost.nodes I * (1 + TabPrepareCost.facts I))%N.
Definition transitions {N E P D A F} (I : Ide.t N E P D A F) :=
  (TabRunCost.roots I * vertices I + TabPrepareCost.arc_count I)%N.
Definition keys {N E P D A F} (I : Ide.t N E P D A F) := (1 + 2 * transitions I)%N.
Definition probe e w := (1 + TabRunCost.ve e w + TabRunCost.vw w)%N.
Definition update e w m := (4 * probe e w + 2 + 2 * m)%N.
Definition arc_charge e w m := (probe e w + 1 + m + update e w m)%N.
Definition step_charge {N E P D A F} (I : Ide.t N E P D A F) e w m :=
  (2 * probe e w + transitions I * (1 + arc_charge e w m))%N.
Definition initial_charge {N E P D A F} (I : Ide.t N E P D A F) e w m :=
  ((1 + transitions I) * (1 + 2 * probe e w) + update e w m)%N.
Definition prepare_charge {N E P D A F} (I : Ide.t N E P D A F)
    ko ks kt kk kf kw q e w :=
  let d := TabPrepareCost.facts I in
  let a := TabPrepareCost.arc_count I in
  let r := TabRunCost.roots I in
  let v := vertices I in
  let t := transitions I in
  (TabPrepareCost.arcs_charge I ko ks kt kk kf kw q + (3 * d + 2 + a) +
    d + TabPrepareCost.nodes I * (4 + 2 * d) +
    r * (2 + v * (2 + TabRunCost.probe e w)) + a + r * v +
    1 + t * (6 + 2 * TabRunCost.ve e w + 4 * TabRunCost.vw w) + 3 * t)%N.

Local Lemma nat_N_le a b : (a <= b)%nat -> (N.of_nat a <= N.of_nat b)%N.
Proof.
  intro Hle; apply (proj1 (N.compare_le_iff _ _)).
  rewrite <- Nat2N.inj_compare; apply (proj2 (Nat.compare_le_iff _ _)); exact Hle.
Qed.

(** Sum bounds use actual leaf contracts before combining their arithmetic budgets. *)
Local Ltac add_budgets :=
  first [
    eassumption
  | match goal with
    | |- (?a + ?b <= _)%N => eapply N.add_le_mono; add_budgets
    end
  | apply N.le_refl ].

(** The listed-vertex generator has its original value, including every duplicate occurrence. *)
Theorem vertices_value {N E P D A F} (I : Ide.t N E P D A F) :
  Cost.value (fw_flat_map_c (fun n =>
    map_c (fun d => Cost.ret (n, d)) (Jump.fact_domain (Ide.ifds I)))
    (Graph.nodes (Cfg.graph (Icfg.cfg (Ifds.icfg (Ide.ifds I)))))) = IdeValue.vertices I.
Proof.
  rewrite fw_flat_map_value; unfold IdeValue.vertices.
  apply flat_map_ext; intro n; rewrite value_map_c; reflexivity.
Qed.

Local Lemma fact_count {N E P D} (I : Ifds.t N E P D) :
  N.of_nat (length (Jump.fact_domain I)) = (1 + N.of_nat (length (Ifds.facts I)))%N.
Proof.
  unfold Jump.fact_domain; cbn [length]; rewrite length_map, Nat2N.inj_succ; lia.
Qed.

(** Listed destinations are bounded by supplied node/fact occurrences without a graph law. *)
Theorem vertices_length {N E P D A F} (I : Ide.t N E P D A F) :
  (N.of_nat (length (IdeValue.vertices I)) <= vertices I)%N.
Proof.
  unfold IdeValue.vertices, vertices; eapply N.le_trans.
  - apply TabPrepareCost.flat_length; intros n Hn; rewrite length_map.
    rewrite fact_count; reflexivity.
  - unfold TabPrepareCost.nodes, TabPrepareCost.facts; reflexivity.
Qed.

(** Destination generation pays the map, both flattening traversals and every copied vertex. *)
Theorem vertices_cost {N E P D A F} (I : Ide.t N E P D A F) :
  (Cost.ticks (fw_flat_map_c (fun n =>
    map_c (fun d => Cost.ret (n, d)) (Jump.fact_domain (Ide.ifds I)))
    (Graph.nodes (Cfg.graph (Icfg.cfg (Ifds.icfg (Ide.ifds I)))))) <=
    TabPrepareCost.nodes I * (4 + 2 * TabPrepareCost.facts I))%N.
Proof.
  eapply N.le_trans.
  - apply TabPrepareCost.flat_map_cost with
      (k := (1 + TabPrepareCost.facts I)%N) (q := (1 + TabPrepareCost.facts I)%N).
    intros n Hn; split.
    + rewrite TabPrepareCost.pure_map_cost, fact_count; reflexivity.
    + rewrite value_map_c, length_map, fact_count; reflexivity.
  - unfold TabPrepareCost.nodes; nia.
Qed.

(** The transition inventory retains all root/destination pairs and actual raw call occurrences. *)
Theorem transitions_length {N E P D A F} (I : Ide.t N E P D A F) J start :
  (N.of_nat (length (TabValues.transitions I J start)) <= transitions I)%N.
Proof.
  unfold TabValues.transitions; rewrite length_app, Nat2N.inj_add.
  change (Cost.value (Jump.roots_c I (fst start) (Jump.arcs I)))
    with (TabPaths.roots I (fst start)).
  assert (Hbody : forall root : N * option D,
    (N.of_nat (length (map (fun dst => ((root, dst), Jump.lookup I J (root, dst)))
      (IdeValue.vertices I))) <= vertices I)%N).
  { intro root; rewrite length_map; apply vertices_length. }
  pose proof (TabPrepareCost.flat_length (fun root =>
    map (fun dst => ((root, dst), Jump.lookup I J (root, dst))) (IdeValue.vertices I))
    (TabPaths.roots I (fst start)) (vertices I)
    (fun root _ => Hbody root)) as Hsummaries.
  pose proof (TabPrepareCost.filter_map_length (fun a : Jump.arc N E P D F =>
    match Jump.kind a with
    | Icfg.Call _ => Some ((Jump.source a, Jump.target a), Jump.weight a)
    | _ => None
    end) (Jump.arcs I)) as Hcalls.
  apply nat_N_le in Hcalls.
  pose proof (TabRunCost.root_count I (fst start)) as Hroots.
  assert (Hproduct :
    (N.of_nat (length (TabPaths.roots I (fst start))) * vertices I <=
      TabRunCost.roots I * vertices I)%N) by (apply N.mul_le_mono_r; exact Hroots).
  unfold transitions; fold (TabPrepareCost.arc_count I) in Hcalls; lia.
Qed.

Section Run.
Context {N E P D A F} (I : Ide.t N E P D A F) (J : Map.t positive F)
  (start : N * option D) (e w m : BinNums.N).
Context (HP : primitives I start e w m).
Context (HV : encoding_laws (IdeValue.key_enc I)).

(** Value vertices retain their own original node and optional-fact encoding charges. *)
Theorem vertex_budget v :
  coordinate I start v ->
  TabEncodingCost.bounded (IdeValue.key_enc I) v (TabRunCost.ve e w) (TabRunCost.vw w).
Proof.
  intro Hv; destruct v as [n d]; apply TabEncodingCost.vertex_bounded.
  - exact (node HP (n, d) Hv).
  - exact (fact HP (n, d) Hv).
Qed.

(** Summary preparation prices the actual composite jump reader even for listed bottom entries. *)
Theorem jump_probe js root dst :
  coordinate I start root -> coordinate I start dst ->
  (Cost.ticks (Jump.lookup_c I js (root, dst)) <= TabRunCost.probe e w)%N.
Proof.
  intros Hr Hd.
  destruct (TabEncodingCost.jump_bounded I root dst _ _
    (vertex_budget root Hr) (vertex_budget dst Hd)) as [He Hw].
  fold (TabRunCost.je e w) in He; fold (TabRunCost.jw w) in Hw.
  unfold Jump.lookup_c; rewrite !Cost.ticks_bind, Cost.ticks_step.
  rewrite Map.find_or_cost, Map.get_cost, positive_encoding_cost, positive_encoding_equation.
  fold (encode (Jump.enc I) (root, dst)).
  fold (key_bits (Jump.enc I) (root, dst)).
  unfold TabRunCost.probe; lia.
Qed.

(** Every transition endpoint belongs to the seed/root/raw/listed coordinate domain. *)
Theorem transition_domain a :
  In a (TabValues.transitions I J start) ->
  coordinate I start (fst (fst a)) /\ coordinate I start (snd (fst a)).
Proof.
  rewrite TabValues.transitions_spec.
  intros [[root [dst [Hr [Hd ->]]]]|[call [p [Ha [Hkind ->]]]]].
  - split; [right; left; left; exact Hr|right; right; exact Hd].
  - split; right; left; right; exists call; split; [exact Ha|left; reflexivity|exact Ha|].
    right; reflexivity.
Qed.

Local Lemma summaries_cost :
  TabCheckCost.list_bound (fw_flat_map_c (fun root =>
    map_c (fun dst =>
      let* weight := Jump.lookup_c I J (root, dst) in Cost.ret ((root, dst), weight))
      (IdeValue.vertices I)) (TabPaths.roots I (fst start)))
    (TabRunCost.roots I * (2 + vertices I * (2 + TabRunCost.probe e w)))
    (TabRunCost.roots I * vertices I).
Proof.
  assert (Hbody : forall root, In root (TabPaths.roots I (fst start)) ->
    TabCheckCost.list_bound (map_c (fun dst =>
      let* weight := Jump.lookup_c I J (root, dst) in Cost.ret ((root, dst), weight))
      (IdeValue.vertices I)) (vertices I * (1 + TabRunCost.probe e w)) (vertices I)).
  { intros root Hr; split.
    - eapply N.le_trans.
      + apply TabPrepareCost.map_cost_on with (k := TabRunCost.probe e w); intros dst Hd.
        rewrite Cost.ticks_bind, Cost.ticks_ret.
        pose proof (jump_probe J root dst (or_intror (or_introl (or_introl Hr)))
          (or_intror (or_intror Hd))); lia.
      + apply N.mul_le_mono_r; apply vertices_length.
    - rewrite value_map_c, length_map; apply vertices_length. }
  destruct (TabCheckCost.flat_bound _ _ _ _ Hbody) as [Hcost Hlen].
  pose proof (TabRunCost.root_count I (fst start)) as Hroots.
  split.
  - eapply N.le_trans; [exact Hcost|].
    eapply N.le_trans; [apply N.mul_le_mono_r; exact Hroots|]; nia.
  - eapply N.le_trans; [exact Hlen|apply N.mul_le_mono_r; exact Hroots].
Qed.

Local Lemma summaries_value :
  Cost.value (fw_flat_map_c (fun root =>
    map_c (fun dst =>
      let* weight := Jump.lookup_c I J (root, dst) in Cost.ret ((root, dst), weight))
      (IdeValue.vertices I)) (TabPaths.roots I (fst start))) =
  flat_map (fun root => map (fun dst => ((root, dst), Jump.lookup I J (root, dst)))
    (IdeValue.vertices I)) (TabPaths.roots I (fst start)).
Proof.
  rewrite fw_flat_map_value; apply flat_map_ext; intro root.
  rewrite value_map_c; apply map_ext; intro dst; reflexivity.
Qed.

Local Lemma grouping_cost :
  (Cost.ticks (Index.group_by_c (IdeValue.key_enc I)
    (fun a => Cost.ret (fst (fst a))) (TabValues.transitions I J start)) <=
    1 + transitions I * (6 + 2 * TabRunCost.ve e w + 4 * TabRunCost.vw w))%N.
Proof.
  pose proof (IndexCost.group_by_cost Map.cost_laws_hold (IdeValue.key_enc I) HV
    (fun a => Cost.ret (fst (fst a))) (TabValues.transitions I J start)
    (TabRunCost.ve e w) (TabRunCost.vw w) 0%N) as Hgroup.
  assert (Hbody : forall a, In a (TabValues.transitions I J start) ->
    (Cost.ticks (Cost.ret (fst (fst a))) <= 0)%N /\
    (Cost.ticks (encode_c (IdeValue.key_enc I) (fst (fst a))) <= TabRunCost.ve e w)%N /\
    (key_bits (IdeValue.key_enc I) (fst (fst a)) <= TabRunCost.vw w)%N).
  { intros a Ha; split; [reflexivity|].
    apply vertex_budget; exact (proj1 (transition_domain a Ha)). }
  specialize (Hgroup Hbody).
  pose proof (transitions_length I J start) as Hlength.
  eapply N.le_trans; [exact Hgroup|].
  apply N.add_le_mono_l, N.mul_le_mono_r; exact Hlength.
Qed.

(** Value preparation retains jump reads, actual calls, both inventories and index reversal. *)
Theorem prepare_cost ko ks kt kk kf kw q :
  TabPrepareCost.callbacks I ko ks kt kk kf kw q ->
  (Cost.ticks (TabValues.prepare_c I J start) <=
    prepare_charge I ko ks kt kk kf kw q e w)%N.
Proof.
  intro HC.
  pose proof (TabPrepareCost.arcs_cost I ko ks kt kk kf kw q HC) as Harcs.
  pose proof (TabPrepareCost.roots_cost I (fst start) (Jump.arcs I)) as Hroots.
  pose proof (vertices_cost I) as Hvertices.
  destruct summaries_cost as [Hsummaries Hsummary_length].
  pose proof grouping_cost as Hgroup.
  pose proof (transitions_length I J start) as Htransitions.
  rewrite summaries_value in Hsummary_length.
  unfold TabValues.transitions in Hgroup, Htransitions.
  change (Cost.value (Jump.roots_c I (fst start) (Jump.arcs I)))
    with (TabPaths.roots I (fst start)) in Hgroup, Htransitions.
  unfold TabValues.prepare_c; rewrite !Cost.ticks_bind.
  change (Cost.value (Jump.arcs_c I)) with (Jump.arcs I).
  change (Cost.value (Jump.roots_c I (fst start) (Jump.arcs I)))
    with (TabPaths.roots I (fst start)).
  rewrite TabPrepareCost.pure_map_cost, value_map_c.
  change (fun d : D => Cost.value (Cost.ret (Some d))) with (@Some D).
  change (None :: map (@Some D) (Ifds.facts (Ide.ifds I)))
    with (Jump.fact_domain (Ide.ifds I)).
  rewrite vertices_value.
  rewrite !TabPrepareCost.pure_map_cost, TabPrepareCost.pure_filter_map_cost.
  rewrite !ticks_app_c, !value_app_c.
  rewrite summaries_value, value_filter_map_c.
  change (fun a : Jump.arc N E P D F => Cost.value (Cost.ret
    (match Jump.kind a with
     | Icfg.Call _ => Some ((Jump.source a, Jump.target a), Jump.weight a)
     | _ => None
     end))) with (fun a : Jump.arc N E P D F =>
       match Jump.kind a with
       | Icfg.Call _ => Some ((Jump.source a, Jump.target a), Jump.weight a)
       | _ => None
       end).
  fold (TabValues.transitions I J start).
  rewrite !value_map_c, !length_map, Cost.ticks_ret.
  change (fun a : TabValues.arc N D F => Cost.value (Cost.ret (fst (fst a))))
    with (fun a : TabValues.arc N D F => fst (fst a)).
  rewrite ?length_map.
  fold (TabPrepareCost.facts I) (TabPrepareCost.arc_count I) in *.
  rewrite Hroots.
  eapply N.le_trans; [add_budgets|].
  unfold prepare_charge; cbn zeta; lia.
Qed.

Local Lemma lookup_cost s v :
  coordinate I start v ->
  (Cost.ticks (TabValues.lookup_c I (TabValues.values s) v) <= probe e w)%N.
Proof.
  intro Hv; destruct (vertex_budget v Hv) as [He Hw].
  unfold TabValues.lookup_c; rewrite Map.find_or_cost, Map.get_cost.
  fold (key_bits (IdeValue.key_enc I) v); unfold probe; lia.
Qed.

Local Lemma schedule_cost s v :
  coordinate I start v ->
  (Cost.ticks (TabValues.schedule_c I v s) <= 2 * probe e w)%N.
Proof.
  intro Hv; destruct (vertex_budget v Hv) as [He Hw].
  unfold TabValues.schedule_c; rewrite Cost.ticks_bind.
  change (Cost.value (FinSet.mem_c (IdeValue.key_enc I) v (TabValues.pending s)))
    with (FinSet.mem (IdeValue.key_enc I) v (TabValues.pending s)).
  destruct (FinSet.mem (IdeValue.key_enc I) v (TabValues.pending s));
    autorewrite with galois_cost; rewrite FinSet.mem_cost, ?FinSet.add_cost;
    fold (key_bits (IdeValue.key_enc I) v); unfold probe; lia.
Qed.

Local Lemma update_cost s v a :
  coordinate I start v ->
  (Cost.ticks (TabValues.update_c I v a s) <= update e w m)%N.
Proof.
  intro Hv; destruct (vertex_budget v Hv) as [He Hw].
  pose proof (lookup_cost s v Hv) as Hlookup.
  unfold TabValues.update_c; rewrite !Cost.ticks_bind.
  change (Cost.value (TabValues.lookup_c I (TabValues.values s) v))
    with (TabValues.lookup I (TabValues.values s) v).
  change (Cost.value (leb_c (Ide.values I) a (TabValues.lookup I (TabValues.values s) v)))
    with (leb (Ide.values I) a (TabValues.lookup I (TabValues.values s) v)).
  destruct (leb (Ide.values I) a (TabValues.lookup I (TabValues.values s) v)).
  - rewrite Cost.ticks_step, Cost.ticks_ret.
    pose proof (compare HP a (TabValues.lookup I (TabValues.values s) v)); unfold update; lia.
  - rewrite !Cost.ticks_bind, !Cost.ticks_step, Map.set_cost.
    pose proof (compare HP a (TabValues.lookup I (TabValues.values s) v)) as Hcompare.
    pose proof (joining HP (TabValues.lookup I (TabValues.values s) v) a) as Hjoin.
    match goal with
    | |- context [Cost.ticks (TabValues.schedule_c I v ?s)] =>
      pose proof (schedule_cost s v Hv) as Hschedule
    end.
    fold (key_bits (IdeValue.key_enc I) v); unfold update, probe in *; lia.
Qed.

Local Lemma arc_cost s a :
  In a (TabValues.transitions I J start) ->
  (Cost.ticks (TabValues.arc_c I a s) <= arc_charge e w m)%N.
Proof.
  intro Ha; destruct (transition_domain a Ha) as [Hsrc Hdst].
  unfold TabValues.arc_c; eapply N.le_trans.
  - eapply TabRunCost.bind_cost; [apply lookup_cost; exact Hsrc|]; intro prior.
    eapply TabRunCost.bind_cost; [reflexivity|]; intros [].
    eapply TabRunCost.bind_cost; [exact (apply HP _ _)|]; intro value.
    apply update_cost; exact Hdst.
  - autorewrite with galois_cost; unfold arc_charge; lia.
Qed.

(** Prepared work keys belong to the explicit seed/raw/listed coordinate domain. *)
Theorem inventory_domain v :
  In v (TabValues.inventory (TabValues.prepare I J start)) -> coordinate I start v.
Proof.
  rewrite TabValues.prepare_equation; cbn [TabValues.inventory].
  intros [Heq|Hin]; [left; symmetry; exact Heq|].
  apply in_app_iff in Hin; destruct Hin as [Hin|Hin]; apply in_map_iff in Hin;
    destruct Hin as [a [Heq Ha]]; subst v.
  - exact (proj1 (transition_domain a Ha)).
  - exact (proj2 (transition_domain a Ha)).
Qed.

(** Actual finite transition counts bound every stored or pending inventory occurrence. *)
Theorem inventory_length :
  (N.of_nat (length (TabValues.inventory (TabValues.prepare I J start))) <= keys I)%N.
Proof.
  rewrite TabValues.prepare_equation.
  change (N.of_nat (S (length
    (map (fun a => fst (fst a)) (TabValues.transitions I J start) ++
      map (fun a => snd (fst a)) (TabValues.transitions I J start)))) <= keys I)%N.
  rewrite length_app, !length_map, Nat2N.inj_succ, Nat2N.inj_add.
  pose proof (transitions_length I J start) as Hlength; unfold keys.
  rewrite N.add_1_l; apply (proj1 (N.succ_le_mono _ _)).
  replace (2 * transitions I)%N with (transitions I + transitions I)%N by ring.
  apply N.add_le_mono; exact Hlength.
Qed.

Local Lemma step_cost s :
  TabValueProgress.invariant I (TabValues.prepare I J start) s ->
  (Cost.ticks (TabValues.step_c I (TabValues.prepare I J start) s) <=
    step_charge I e w m)%N.
Proof.
  intros [Hshape [Hwork Hstored]]; unfold TabValues.step_c.
  destruct (TabValues.work s) as [|v rest] eqn:Hworklist; [rewrite Cost.ticks_ret; lia|].
  assert (Hv : coordinate I start v) by (apply inventory_domain, Hwork; left; reflexivity).
  destruct (vertex_budget v Hv) as [He Hw].
  assert (Hout : (N.of_nat (length (Index.find (IdeValue.key_enc I) v
    (TabValues.outgoing (TabValues.prepare I J start)))) <= transitions I)%N).
  { rewrite TabValues.prepare_equation; cbn [TabValues.outgoing]; rewrite Index.find_group_by.
    eapply N.le_trans; [apply nat_N_le, List.filter_length_le|apply transitions_length]. }
  assert (Hfold : forall t, (Cost.ticks (fold_left_c (fun t a => TabValues.arc_c I a t)
    (Index.find (IdeValue.key_enc I) v (TabValues.outgoing (TabValues.prepare I J start))) t) <=
    transitions I * (1 + arc_charge e w m))%N).
  { intro t; eapply N.le_trans.
    - apply TabRunCost.fold_cost with (P := fun _ => True); [|exact Logic.I].
      intros u a Hu Ha; split; [exact Logic.I|]; apply arc_cost.
      rewrite TabValues.prepare_equation in Ha; cbn [TabValues.outgoing] in Ha.
      rewrite Index.find_group_by in Ha; apply filter_In in Ha; exact (proj1 Ha).
    - apply N.mul_le_mono_r; exact Hout. }
  autorewrite with galois_cost; rewrite FinSet.remove_cost, Index.find_cost, Map.get_cost.
  fold (key_bits (IdeValue.key_enc I) v).
  match goal with
  | |- context [Cost.ticks (fold_left_c _ _ ?t)] => specialize (Hfold t)
  end.
  change (Cost.value (Index.find_c (IdeValue.key_enc I) v
    (TabValues.outgoing (TabValues.prepare I J start))))
    with (Index.find (IdeValue.key_enc I) v (TabValues.outgoing (TabValues.prepare I J start))).
  unfold step_charge, probe in *; lia.
Qed.

Local Lemma initial_cost a0 :
  (Cost.ticks (TabValues.initial_c I (TabValues.prepare I J start) start a0) <=
    initial_charge I e w m)%N.
Proof.
  unfold TabValues.initial_c; rewrite Cost.ticks_bind.
  assert (Hs : forall t,
    (Cost.ticks (fold_left_c (fun t v => TabValues.schedule_c I v t)
      (TabValues.sources (TabValues.prepare I J start)) t) <=
      (1 + transitions I) * (1 + 2 * probe e w))%N).
  { intro t; eapply N.le_trans.
    - apply TabRunCost.fold_cost with (P := fun _ => True); [|exact Logic.I].
      intros u v Hu Hv; split; [exact Logic.I|]; apply schedule_cost.
      rewrite TabValues.prepare_equation in Hv; cbn [TabValues.sources] in Hv.
      destruct Hv as [Heq|Hin]; [left; symmetry; exact Heq|].
      apply in_map_iff in Hin; destruct Hin as [a [Heq Ha]]; subst v.
      exact (proj1 (transition_domain a Ha)).
    - apply N.mul_le_mono_r; rewrite TabValues.prepare_equation.
      change (N.of_nat (S (length (map (fun a => fst (fst a))
        (TabValues.transitions I J start)))) <= 1 + transitions I)%N.
      rewrite length_map, Nat2N.inj_succ.
      rewrite N.add_1_l; apply (proj1 (N.succ_le_mono _ _)), transitions_length. }
  match goal with
  | |- context [Cost.ticks (TabValues.update_c I start a0 ?t)] =>
    pose proof (update_cost t start a0 (or_introl eq_refl)) as Hu
  end.
  specialize (Hs (TabValues.State Map.empty [] FinSet.empty)).
  unfold initial_charge; lia.
Qed.

(** Raw value propagation retains preparation, initialization and every binary-driver tick. *)
Theorem raw_cost a0 fuel ko ks kt kk kf kw q :
  TabPrepareCost.callbacks I ko ks kt kk kf kw q ->
  (Cost.ticks (TabValues.raw_c I J start a0 fuel) <=
    prepare_charge I ko ks kt kk kf kw q e w + initial_charge I e w m +
    (step_charge I e w m + 2) * N.pos fuel)%N.
Proof.
  intro HC.
  pose proof (iterate_cost_amortised (TabValues.step_c I (TabValues.prepare I J start))
    (TabValueProgress.invariant I (TabValues.prepare I J start)) (fun _ => 0%N)
    (step_charge I e w m)) as Hloop.
  assert (Hstep : forall s, TabValueProgress.invariant I (TabValues.prepare I J start) s ->
    (match Cost.value (TabValues.step_c I (TabValues.prepare I J start) s) with
     | inl next => TabValueProgress.invariant I (TabValues.prepare I J start) next
     | inr _ => True
     end) /\
    (Cost.ticks (TabValues.step_c I (TabValues.prepare I J start) s) +
      result_potential (fun _ => 0%N)
        (Cost.value (TabValues.step_c I (TabValues.prepare I J start) s)) <=
      step_charge I e w m + 0)%N).
  { intros s Hs; split.
    - pose proof (TabValueProgress.step_invariant I J start HV s Hs) as Hnext.
      destruct (Cost.value (TabValues.step_c I (TabValues.prepare I J start) s));
        [exact Hnext|exact Logic.I].
    - rewrite result_potential_zero; pose proof (step_cost s Hs); lia. }
  specialize (Hloop Hstep fuel
    (Cost.value (TabValues.initial_c I (TabValues.prepare I J start) start a0))
    (TabValueProgress.initial_invariant I J start a0 HV)).
  destruct Hloop as [Hresult Hloop]; rewrite result_potential_zero in Hloop.
  assert (Hloopcost :
    (Cost.ticks (iterate (TabValues.step_c I (TabValues.prepare I J start)) fuel
      (Cost.value (TabValues.initial_c I (TabValues.prepare I J start) start a0))) <=
      (step_charge I e w m + 2) * N.pos fuel)%N) by lia.
  pose proof (prepare_cost ko ks kt kk kf kw q HC) as Hprep.
  pose proof (initial_cost a0) as Hinitial.
  unfold TabValues.raw_c; rewrite !Cost.ticks_bind.
  change (Cost.value (TabValues.prepare_c I J start)) with (TabValues.prepare I J start).
  eapply N.le_trans; [add_budgets|]; lia.
Qed.

End Run.

(** Supplied-fuel raw value families retain actual preparation, initialization and driver work. *)
Theorem raw_bigO {X N E P D A F} (I : X -> Ide.t N E P D A F)
    (J : X -> Map.t positive F) (start : X -> N * option D) (a0 : X -> A)
    (fuel : X -> positive) (e w m ko ks kt kk kf kw q : X -> BinNums.N) :
  (forall x, primitives (I x) (start x) (e x) (w x) (m x)) ->
  (forall x, encoding_laws (IdeValue.key_enc (I x))) ->
  (forall x, TabPrepareCost.callbacks (I x) (ko x) (ks x) (kt x) (kk x) (kf x) (kw x) (q x)) ->
  bigO
    (fun x => (prepare_charge (I x) (ko x) (ks x) (kt x) (kk x) (kf x) (kw x) (q x)
      (e x) (w x) + initial_charge (I x) (e x) (w x) (m x) +
      (step_charge (I x) (e x) (w x) (m x) + 2) * N.pos (fuel x))%N)
    (fun x => Cost.ticks (TabValues.raw_c (I x) (J x) (start x) (a0 x) (fuel x))).
Proof.
  intros HP HV HC; exists 1%N; intro x.
  pose proof (raw_cost (I x) (J x) (start x) (e x) (w x) (m x) (HP x) (HV x)
    (a0 x) (fuel x) (ko x) (ks x) (kt x) (kk x) (kf x) (kw x) (q x) (HC x)); lia.
Qed.

(** Constructed fuel pays the separate value height and both transition endpoint inventories. *)
Definition complete_charge {N E P D A F} (I : Ide.t N E P D A F)
    ko ks kt kk kf kw q e w m h :=
  (prepare_charge I ko ks kt kk kf kw q e w + initial_charge I e w m +
    h + keys I + 1 + (step_charge I e w m + 2) * (1 + (1 + h) * keys I))%N.

(** Constructed raw values compose primitive preparation, updates and actual height fuel. *)
Theorem complete_raw_cost {N E P D A F} (I : Ide.t N E P D A F) J start a0 e w m
    ko ks kt kk kf kw q (H : height (Ide.values I)) :
  primitives I start e w m -> encoding_laws (IdeValue.key_enc I) ->
  TabPrepareCost.callbacks I ko ks kt kk kf kw q ->
  (Cost.ticks (TabValueProgress.complete_raw_c I J start a0 H) <=
    complete_charge I ko ks kt kk kf kw q e w m (N.of_nat (bound H)))%N.
Proof.
  intros HP HV HC.
  set (p := TabValues.prepare I J start).
  set (fuel := TabCost.inventory_fuel (TabValues.inventory p) (bound H)).
  pose proof (raw_cost I J start e w m HP HV a0 fuel ko ks kt kk kf kw q HC) as Hraw.
  assert (Hequation :
    Cost.ticks (TabValueProgress.complete_raw_c I J start a0 H) =
      (Cost.ticks (TabValues.raw_c I J start a0 fuel) +
        Cost.ticks (TabCost.inventory_fuel_c (TabValues.inventory p) (bound H)))%N).
  { rewrite TabValueProgress.complete_raw_cost_equation; cbn zeta.
    unfold TabValues.raw_c; rewrite !Cost.ticks_bind.
    change (Cost.value (TabValues.prepare_c I J start)) with p.
    fold p; fold fuel; lia. }
  pose proof (inventory_length I J start) as Hkeys; fold p in Hkeys.
  assert (Hfuel : (N.pos fuel <= 1 + (1 + N.of_nat (bound H)) * keys I)%N).
  { unfold fuel; rewrite TabCost.inventory_fuel_equation, N.succ_pos_spec.
    pose proof (N.mul_le_mono_l _ _ (1 + N.of_nat (bound H)) Hkeys); lia. }
  assert (Hloop :
    ((step_charge I e w m + 2) * N.pos fuel <=
      (step_charge I e w m + 2) * (1 + (1 + N.of_nat (bound H)) * keys I))%N).
  { apply N.mul_le_mono_l; exact Hfuel. }
  rewrite Hequation, TabCost.inventory_fuel_cost.
  unfold complete_charge; lia.
Qed.

(** Constructed raw value families retain their own height and complete primitive-derived bound. *)
Theorem complete_raw_bigO {X N E P D A F} (I : X -> Ide.t N E P D A F)
    (J : X -> Map.t positive F) (start : X -> N * option D) (a0 : X -> A)
    (e w m ko ks kt kk kf kw q : X -> BinNums.N)
    (H : forall x, height (Ide.values (I x))) :
  (forall x, primitives (I x) (start x) (e x) (w x) (m x)) ->
  (forall x, encoding_laws (IdeValue.key_enc (I x))) ->
  (forall x, TabPrepareCost.callbacks (I x) (ko x) (ks x) (kt x) (kk x) (kf x) (kw x) (q x)) ->
  bigO
    (fun x => complete_charge (I x) (ko x) (ks x) (kt x) (kk x) (kf x) (kw x) (q x)
      (e x) (w x) (m x) (N.of_nat (bound (H x))))
    (fun x => Cost.ticks (TabValueProgress.complete_raw_c (I x) (J x) (start x) (a0 x) (H x))).
Proof.
  intros HP HV HC; exists 1%N; intro x.
  pose proof (complete_raw_cost (I x) (J x) (start x) (a0 x) (e x) (w x) (m x)
    (ko x) (ks x) (kt x) (kk x) (kf x) (kw x) (q x) (H x) (HP x) (HV x) (HC x)); lia.
Qed.

End TabValueRunCost.
