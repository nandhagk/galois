(** * Primitive numerical preparation costs

    Preparation retains supplied occurrences even when the tabulation never reaches them.
    For example, duplicate facts cause separate flow calls and separate initial inventory slots.
    Builds on: FrameworkTabEncodingCost, BaseIndexCost and the charged preparation definitions. *)

From Stdlib Require Import List Arith NArith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseMap BaseIndex BaseIndexCost.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramCfg ProgramIcfg.
From Galois.Framework Require Import FrameworkUtil FrameworkIfds FrameworkIde FrameworkTabulate
  FrameworkTabEncodingCost.
Import List.ListNotations Cost.Notations.

Module TabPrepareCost.

Local Lemma nat_N_le a b : (a <= b)%nat -> (N.of_nat a <= N.of_nat b)%N.
Proof.
  intro Hle; apply (proj1 (N.compare_le_iff _ _)).
  rewrite <- Nat2N.inj_compare; apply (proj2 (Nat.compare_le_iff _ _)); exact Hle.
Qed.

(** Mapping prices callbacks only on their actual supplied occurrences. *)
Theorem map_cost_on {X Y} (f : X -> Cost.t Y) xs k :
  (forall x, In x xs -> (Cost.ticks (f x) <= k)%N) ->
  (Cost.ticks (map_c f xs) <= N.of_nat (length xs) * (1 + k))%N.
Proof.
  rewrite ticks_map_c; induction xs as [|x xs IH]; intro Hbound; cbn [fold_right length].
  - lia.
  - rewrite Nat2N.inj_succ.
    specialize (IH (fun y Hy => Hbound y (or_intror Hy))).
    specialize (Hbound x (or_introl eq_refl)); nia.
Qed.

(** Flattening retains both traversal ticks, every callback body and every copied output cell. *)
Theorem flat_map_cost {X Y} (f : X -> Cost.t (list Y)) xs k q :
  (forall x, In x xs ->
    (Cost.ticks (f x) <= k)%N /\ (N.of_nat (length (Cost.value (f x))) <= q)%N) ->
  (Cost.ticks (fw_flat_map_c f xs) <= N.of_nat (length xs) * (2 + k + q))%N.
Proof.
  unfold fw_flat_map_c; induction xs as [|x xs IH]; intro Hbound.
  - rewrite ticks_fold_right_c_nil; lia.
  - rewrite ticks_fold_right_c_cons; autorewrite with galois_cost.
    cbn [length]; rewrite Nat2N.inj_succ.
    specialize (IH (fun y Hy => Hbound y (or_intror Hy))).
    destruct (Hbound x (or_introl eq_refl)) as [Hcost Hlength]; nia.
Qed.

(** Flattening multiplies supplied occurrences by the maximum actual callback output length. *)
Theorem flat_length {X Y} (f : X -> list Y) xs q :
  (forall x, In x xs -> (N.of_nat (length (f x)) <= q)%N) ->
  (N.of_nat (length (flat_map f xs)) <= N.of_nat (length xs) * q)%N.
Proof.
  induction xs as [|x xs IH]; intro Hbound; cbn [flat_map length].
  - lia.
  - rewrite length_app, Nat2N.inj_add, Nat2N.inj_succ.
    specialize (IH (fun y Hy => Hbound y (or_intror Hy))).
    specialize (Hbound x (or_introl eq_refl)); nia.
Qed.

(** Filtering and optional mapping emit at most one item per supplied occurrence. *)
Theorem filter_map_length {X Y} (f : X -> option Y) xs :
  (length (filter_map f xs) <= length xs)%nat.
Proof.
  unfold filter_map; induction xs as [|x xs IH]; cbn [fold_right length]; [lia|].
  destruct (f x); cbn [length]; lia.
Qed.

(** A returned constant-time mapping body retains one traversal tick per occurrence. *)
Theorem pure_map_cost {X Y} (f : X -> Y) xs :
  Cost.ticks (map_c (fun x => Cost.ret (f x)) xs) = N.of_nat (length xs).
Proof.
  rewrite ticks_map_c; induction xs as [|x xs IH]; cbn [fold_right length].
  - reflexivity.
  - rewrite Cost.ticks_ret, Nat2N.inj_succ; lia.
Qed.

(** A returned optional body retains one traversal tick even for rejected occurrences. *)
Theorem pure_filter_map_cost {X Y} (f : X -> option Y) xs :
  Cost.ticks (filter_map_c (fun x => Cost.ret (f x)) xs) = N.of_nat (length xs).
Proof.
  rewrite ticks_filter_map_c; induction xs as [|x xs IH]; cbn [fold_right length].
  - reflexivity.
  - rewrite Cost.ticks_ret, Nat2N.inj_succ; lia.
Qed.

(** Outgoing-list preparation charges every supplied node and every emitted edge occurrence. *)
Theorem edges_cost {N E} (cfg : Cfg.t N E) ko :
  (forall n, In n (Graph.nodes (Cfg.graph cfg)) ->
    (Cost.ticks (Graph.out_c (Cfg.graph cfg) n) <= ko)%N) ->
  (Cost.ticks (fw_edges_c cfg) <=
    N.of_nat (length (Graph.nodes (Cfg.graph cfg))) * (2 + ko) +
      N.of_nat (length (Cfg.edges cfg)))%N.
Proof.
  unfold fw_edges_c, fw_flat_map_c.
  change ((forall n, In n (Graph.nodes (Cfg.graph cfg)) ->
    (Cost.ticks (Graph.out_c (Cfg.graph cfg) n) <= ko)%N) ->
    (Cost.ticks (fold_right_c
      (fun n rest => Cost.step ;; let* es := Graph.out_c (Cfg.graph cfg) n in app_c es rest)
      [] (Graph.nodes (Cfg.graph cfg))) <=
    N.of_nat (length (Graph.nodes (Cfg.graph cfg))) * (2 + ko) +
      N.of_nat (length (flat_map (Graph.out (Cfg.graph cfg)) (Graph.nodes (Cfg.graph cfg)))))%N).
  induction (Graph.nodes (Cfg.graph cfg)) as [|n ns IH]; intro Hout.
  - change (0 <= 0 + 0)%N; lia.
  - rewrite ticks_fold_right_c_cons; autorewrite with galois_cost.
    change (1 + Cost.ticks (fold_right_c
      (fun v rest => Cost.step ;; let* es := Graph.out_c (Cfg.graph cfg) v in app_c es rest)
      [] ns) +
      (1 + (Cost.ticks (Graph.out_c (Cfg.graph cfg) n) +
        N.of_nat (length (Graph.out (Cfg.graph cfg) n)))) <=
      N.of_nat (S (length ns)) * (2 + ko) +
        N.of_nat (length (Graph.out (Cfg.graph cfg) n ++
          flat_map (Graph.out (Cfg.graph cfg)) ns)))%N.
    specialize (IH (fun v Hv => Hout v (or_intror Hv))).
    specialize (Hout n (or_introl eq_refl)).
    cbn [length flat_map]; rewrite length_app, Nat2N.inj_add, Nat2N.inj_succ; nia.
Qed.

(** Callback duties range over the supplied graph, supported inputs and actual flow outputs. *)
Record callbacks {N E P D A F} (I : Ide.t N E P D A F)
    (ko ks kt kk kf kw q : BinNums.N) : Prop := Callbacks {
  out_cost : forall n, In n (Graph.nodes (Cfg.graph (Icfg.cfg (Ifds.icfg (Ide.ifds I))))) ->
    (Cost.ticks (Graph.out_c (Cfg.graph (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) n) <= ko)%N;
  source_cost : forall e, In e (Cfg.edges (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) ->
    (Cost.ticks (Graph.source_c (Cfg.graph (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) e) <= ks)%N;
  target_cost : forall e, In e (Cfg.edges (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) ->
    (Cost.ticks (Graph.target_c (Cfg.graph (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) e) <= kt)%N;
  kind_cost : forall e, In e (Cfg.edges (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) ->
    (Cost.ticks (Icfg.kind_c (Ifds.icfg (Ide.ifds I)) e) <= kk)%N;
  flow_cost : forall e x, In e (Cfg.edges (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) ->
    In x (Jump.fact_domain (Ide.ifds I)) ->
    (Cost.ticks (Ifds.flow_c (Ide.ifds I) e x) <= kf)%N;
  flow_length : forall e x, In e (Cfg.edges (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) ->
    In x (Jump.fact_domain (Ide.ifds I)) ->
    (N.of_nat (length (Ifds.flow (Ide.ifds I) e x)) <= q)%N;
  weight_cost : forall e x y, In e (Cfg.edges (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) ->
    In x (Jump.fact_domain (Ide.ifds I)) -> In y (Ifds.flow (Ide.ifds I) e x) ->
    (Cost.ticks (Ide.weight_c I e x y) <= kw)%N
}.
Arguments out_cost {N E P D A F I ko ks kt kk kf kw q}.
Arguments source_cost {N E P D A F I ko ks kt kk kf kw q}.
Arguments target_cost {N E P D A F I ko ks kt kk kf kw q}.
Arguments kind_cost {N E P D A F I ko ks kt kk kf kw q}.
Arguments flow_cost {N E P D A F I ko ks kt kk kf kw q}.
Arguments flow_length {N E P D A F I ko ks kt kk kf kw q}.
Arguments weight_cost {N E P D A F I ko ks kt kk kf kw q}.

Definition nodes {N E P D A F} (I : Ide.t N E P D A F) :=
  N.of_nat (length (Graph.nodes (Cfg.graph (Icfg.cfg (Ifds.icfg (Ide.ifds I)))))).
Definition edges {N E P D A F} (I : Ide.t N E P D A F) :=
  N.of_nat (length (Cfg.edges (Icfg.cfg (Ifds.icfg (Ide.ifds I))))).
Definition facts {N E P D A F} (I : Ide.t N E P D A F) :=
  N.of_nat (length (Ifds.facts (Ide.ifds I))).
Definition arc_count {N E P D A F} (I : Ide.t N E P D A F) :=
  N.of_nat (length (Jump.arcs I)).

Definition arcs_bound {N E P D A F} (I : Ide.t N E P D A F) q :=
  (edges I * (1 + facts I) * q)%N.
Definition arcs_charge {N E P D A F} (I : Ide.t N E P D A F) ko ks kt kk kf kw q :=
  (nodes I * (2 + ko) + edges I + facts I +
    edges I * (5 + ks + kt + kk +
      (1 + facts I) * (3 + kf + q * (4 + kw))))%N.

Local Lemma fact_domain_length {N E P D} (I : Ifds.t N E P D) :
  N.of_nat (length (Jump.fact_domain I)) = (1 + N.of_nat (length (Ifds.facts I)))%N.
Proof.
  unfold Jump.fact_domain; cbn [length]; rewrite length_map, Nat2N.inj_succ; lia.
Qed.

(** Actual exploded-arc length retains all supplied edge, fact and duplicate output occurrences. *)
Theorem arcs_length {N E P D A F} (I : Ide.t N E P D A F) ko ks kt kk kf kw q :
  callbacks I ko ks kt kk kf kw q -> (arc_count I <= arcs_bound I q)%N.
Proof.
  intro HC; unfold arc_count; rewrite Jump.arcs_equation; unfold arcs_bound.
  eapply N.le_trans.
  - apply flat_length; intros e He.
    eapply N.le_trans.
    + apply flat_length; intros x Hx; rewrite length_map; exact (flow_length HC e x He Hx).
    + rewrite fact_domain_length; reflexivity.
  - unfold edges, facts; nia.
Qed.

(** Arc preparation bounds genuine callbacks and both flattening/copying levels numerically. *)
Theorem arcs_cost {N E P D A F} (I : Ide.t N E P D A F) ko ks kt kk kf kw q :
  callbacks I ko ks kt kk kf kw q ->
  (Cost.ticks (Jump.arcs_c I) <= arcs_charge I ko ks kt kk kf kw q)%N.
Proof.
  intro HC.
  pose proof (edges_cost (Icfg.cfg (Ifds.icfg (Ide.ifds I))) ko (out_cost HC)) as Hedges.
  unfold Jump.arcs_c; rewrite Cost.ticks_bind, fw_edges_value, Cost.ticks_bind.
  rewrite pure_map_cost, value_map_c.
  assert (Hbody : forall e, In e (Cfg.edges (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) ->
    (Cost.ticks
      (Cost.step ;; let* src := Graph.source_c (Cfg.graph (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) e in
       Cost.step ;; let* dst := Graph.target_c (Cfg.graph (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) e in
       Cost.step ;; let* kind := Icfg.kind_c (Ifds.icfg (Ide.ifds I)) e in
       fw_flat_map_c (fun x =>
         Cost.step ;; let* ys := Ifds.flow_c (Ide.ifds I) e x in
         map_c (fun y =>
           Cost.step ;; let* w := Ide.weight_c I e x y in
           Cost.ret (Jump.Arc e (src, x) (dst, y) kind w)) ys)
         (Jump.fact_domain (Ide.ifds I))) <=
      3 + ks + kt + kk + (1 + facts I) * (3 + kf + q * (3 + kw)))%N).
  { intros e He; autorewrite with galois_cost.
    pose proof (source_cost HC e He) as Hs.
    pose proof (target_cost HC e He) as Ht.
    pose proof (kind_cost HC e He) as Hk.
    assert (Hflat : forall (src dst : N) (kind : Icfg.kind P),
      (Cost.ticks (fw_flat_map_c (fun x =>
        Cost.step ;; let* ys := Ifds.flow_c (Ide.ifds I) e x in
        map_c (fun y => Cost.step ;; let* w := Ide.weight_c I e x y in
          Cost.ret (Jump.Arc e (src, x) (dst, y) kind w)) ys)
        (Jump.fact_domain (Ide.ifds I))) <=
        (1 + facts I) * (3 + kf + q * (3 + kw)))%N).
    { intros src dst kind; eapply N.le_trans.
      - apply flat_map_cost with (k := (1 + kf + q * (2 + kw))%N) (q := q).
        intros x Hx; split.
        + pose proof (map_cost_on
            (fun y => Cost.step ;; let* w := Ide.weight_c I e x y in
              Cost.ret (Jump.Arc e (src, x) (dst, y) kind w))
            (Ifds.flow (Ide.ifds I) e x) (1 + kw)%N) as Hmap.
          specialize (Hmap (fun y Hy => ltac:(
            change (1 + (Cost.ticks (Ide.weight_c I e x y) + 0) <= 1 + kw)%N;
            pose proof (weight_cost HC e x y He Hx Hy); lia))).
          change (1 + (Cost.ticks (Ifds.flow_c (Ide.ifds I) e x) +
            Cost.ticks (map_c
              (fun y => Cost.step ;; let* w := Ide.weight_c I e x y in
                Cost.ret (Jump.Arc e (src, x) (dst, y) kind w))
              (Ifds.flow (Ide.ifds I) e x))) <=
            1 + kf + q * (2 + kw))%N.
          pose proof (flow_cost HC e x He Hx).
          pose proof (flow_length HC e x He Hx); nia.
        + autorewrite with galois_cost; rewrite length_map; exact (flow_length HC e x He Hx).
      - rewrite fact_domain_length; unfold facts; nia. }
    specialize (Hflat
      (Graph.source (Cfg.graph (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) e)
      (Graph.target (Cfg.graph (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) e)
      (Icfg.edge_kind (Ifds.icfg (Ide.ifds I)) e)).
    fold (Graph.source (Cfg.graph (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) e)
      (Graph.target (Cfg.graph (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) e)
      (Icfg.edge_kind (Ifds.icfg (Ide.ifds I)) e).
    nia. }
  assert (Hlength : forall e, In e (Cfg.edges (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) ->
    forall (src dst : N) (kind : Icfg.kind P),
    (N.of_nat (length (Cost.value
      (fw_flat_map_c (fun x => Cost.step ;; let* ys := Ifds.flow_c (Ide.ifds I) e x in
        map_c (fun y => Cost.step ;; let* w := Ide.weight_c I e x y in
          Cost.ret (Jump.Arc e (src, x) (dst, y) kind w)) ys)
        (Jump.fact_domain (Ide.ifds I))))) <= (1 + facts I) * q)%N).
  { intros e He src dst kind; rewrite fw_flat_map_value; apply N.le_trans with
      (N.of_nat (length (Jump.fact_domain (Ide.ifds I))) * q)%N.
    - apply flat_length; intros x Hx; autorewrite with galois_cost.
      rewrite length_map; exact (flow_length HC e x He Hx).
    - rewrite fact_domain_length; reflexivity. }
  eapply N.le_trans.
  - apply N.add_le_mono_l, N.add_le_mono_l.
    apply flat_map_cost with
      (k := (3 + ks + kt + kk + (1 + facts I) * (3 + kf + q * (3 + kw)))%N)
      (q := ((1 + facts I) * q)%N).
    intros e He; split.
    + apply Hbody; exact He.
    + autorewrite with galois_cost; apply Hlength; exact He.
  - unfold arcs_charge, nodes, edges, facts in *; nia.
Qed.

(** The root inventory retains start facts and every exploded call-target occurrence. *)
Theorem roots_length {N E P D A F} (I : Ide.t N E P D A F) start as_ :
  (N.of_nat (length (Cost.value (Jump.roots_c I start as_))) <=
    1 + facts I + N.of_nat (length as_))%N.
Proof.
  rewrite Jump.roots_c_value, length_app, length_map, Nat2N.inj_add, fact_domain_length.
  pose proof (filter_map_length (fun a : Jump.arc N E P D F =>
    match Jump.kind a with Icfg.Call _ => Some (Jump.target a) | _ => None end) as_) as Hlen.
  apply nat_N_le in Hlen; unfold facts; lia.
Qed.

(** Root construction pays both fact maps, the full call scan and the copied initial roots. *)
Theorem roots_cost {N E P D A F} (I : Ide.t N E P D A F) start as_ :
  Cost.ticks (Jump.roots_c I start as_) = (3 * facts I + 2 + N.of_nat (length as_))%N.
Proof.
  unfold Jump.roots_c; rewrite !Cost.ticks_bind.
  rewrite pure_map_cost, value_map_c, pure_map_cost, pure_filter_map_cost.
  rewrite ticks_app_c, value_map_c, length_map; cbn [length].
  rewrite length_map, Nat2N.inj_succ; unfold facts; lia.
Qed.

Local Lemma vertices_length {N E P D F} (as_ : list (Jump.arc N E P D F)) :
  N.of_nat (length (flat_map (fun a => [Jump.source a; Jump.target a]) as_)) =
    (2 * N.of_nat (length as_))%N.
Proof.
  induction as_ as [|a as_ IH]; cbn [flat_map app length]; [reflexivity|].
  rewrite !Nat2N.inj_succ; lia.
Qed.

Local Lemma flat_map_cardinality {X Y} (f : X -> list Y) xs q :
  (forall x, In x xs -> length (f x) = q) ->
  length (flat_map f xs) = (length xs * q)%nat.
Proof.
  induction xs as [|x xs IH]; intro Hlength; cbn [flat_map length]; [reflexivity|].
  rewrite length_app, Hlength by (left; reflexivity).
  rewrite IH by (intros y Hy; apply Hlength; right; exact Hy).
  lia.
Qed.

(** The actual initial jump inventory retains each root and both endpoints of every arc occurrence. *)
Theorem inventory_length {N E P D A F} (I : Ide.t N E P D A F) start :
  N.of_nat (length (Tab.inventory (Tab.prepare I start))) =
    (N.of_nat (length (Cost.value (Jump.roots_c I start (Jump.arcs I)))) *
      (1 + 2 * arc_count I))%N.
Proof.
  rewrite Tab.prepare_equation; cbn [Tab.inventory].
  rewrite flat_map_cardinality with
    (q := S (length (flat_map (fun a => [Jump.source a; Jump.target a]) (Jump.arcs I)))).
  - rewrite Nat2N.inj_mul, Nat2N.inj_succ, vertices_length.
    unfold arc_count; nia.
  - intros root Hroot; rewrite length_map; reflexivity.
Qed.

(** Initial-coordinate support has a numerical bound even for duplicate or unsupported raw endpoints. *)
Theorem inventory_bound {N E P D A F} (I : Ide.t N E P D A F) start :
  (N.of_nat (length (Tab.inventory (Tab.prepare I start))) <=
    (1 + facts I + arc_count I) * (1 + 2 * arc_count I))%N.
Proof.
  rewrite inventory_length.
  pose proof (roots_length I start (Jump.arcs I)) as Hroots.
  fold (arc_count I) in Hroots; nia.
Qed.

Local Lemma source_budget {N E P D A F} (I : Ide.t N E P D A F) a en ed wn wd :
  (forall e, In e (Cfg.edges (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) ->
    TabEncodingCost.bounded (Cfg.node_enc (Icfg.cfg (Ifds.icfg (Ide.ifds I))))
      (Graph.source (Cfg.graph (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) e) en wn) ->
  (forall d, In d (Ifds.facts (Ide.ifds I)) ->
    TabEncodingCost.bounded (Ifds.fact_enc (Ide.ifds I)) d ed wd) ->
  In a (Jump.arcs I) ->
  TabEncodingCost.bounded (IdeValue.key_enc I) (Jump.source a)
    (TabEncodingCost.pair_charge en (TabEncodingCost.option_charge ed wd)
      wn (TabEncodingCost.option_width wd))
    (TabEncodingCost.pair_width wn (TabEncodingCost.option_width wd)).
Proof.
  intros Hnodes Hfacts Ha; rewrite Jump.arcs_equation in Ha.
  apply in_flat_map in Ha; destruct Ha as [e [He Ha]].
  apply in_flat_map in Ha; destruct Ha as [x [Hx Ha]].
  apply in_map_iff in Ha; destruct Ha as [y [Heq Hy]]; subst a; cbn [Jump.source].
  apply TabEncodingCost.vertex_bounded; [apply Hnodes; exact He|].
  destruct x as [d|]; [|exact Logic.I].
  change (In (Some d) (None :: map (@Some D) (Ifds.facts (Ide.ifds I)))) in Hx.
  destruct Hx as [Hbad|Hin]; [discriminate|].
  apply in_map_iff in Hin; destruct Hin as [d' [Heq Hd]].
  injection Heq as Heq; subst d'; apply Hfacts; exact Hd.
Qed.

Definition prepare_charge {N E P D A F} (I : Ide.t N E P D A F)
    ko ks kt kk kf kw q en ed wn wd :=
  let a := arc_count I in
  let ve := TabEncodingCost.pair_charge en (TabEncodingCost.option_charge ed wd)
    wn (TabEncodingCost.option_width wd) in
  let vw := TabEncodingCost.pair_width wn (TabEncodingCost.option_width wd) in
  (arcs_charge I ko ks kt kk kf kw q + 3 * facts I + 2 + a +
    (1 + a * (6 + 2 * ve + 4 * vw)) + 4 * a +
    (1 + facts I + a) * (4 + 4 * a))%N.

Local Lemma vertices_cost {N E P D F} (as_ : list (Jump.arc N E P D F)) :
  (Cost.ticks (fw_flat_map_c (fun a => Cost.ret [Jump.source a; Jump.target a]) as_) <=
    4 * N.of_nat (length as_))%N.
Proof.
  eapply N.le_trans; [apply flat_map_cost with (k := 0%N) (q := 2%N)|].
  - intros a Ha; split; reflexivity.
  - nia.
Qed.

Local Lemma keys_cost {N E P D F} roots (as_ : list (Jump.arc N E P D F)) :
  (Cost.ticks (fw_flat_map_c (fun root =>
    map_c (fun v => Cost.ret (root, v))
      (root :: flat_map (fun a => [Jump.source a; Jump.target a]) as_)) roots) <=
    N.of_nat (length roots) * (4 + 4 * N.of_nat (length as_)))%N.
Proof.
  eapply N.le_trans.
  - apply flat_map_cost with (k := (1 + 2 * N.of_nat (length as_))%N)
      (q := (1 + 2 * N.of_nat (length as_))%N).
    intros root Hroot; split.
    + rewrite pure_map_cost; cbn [length]; rewrite Nat2N.inj_succ, vertices_length; lia.
    + rewrite value_map_c, length_map; cbn [length].
      rewrite Nat2N.inj_succ, vertices_length; lia.
  - nia.
Qed.

(** Full jump preparation charges every primitive callback, source-index reversal and inventory scan. *)
Theorem prepare_cost {N E P D A F} (I : Ide.t N E P D A F) start
    ko ks kt kk kf kw q en ed wn wd :
  callbacks I ko ks kt kk kf kw q ->
  encoding_laws (IdeValue.key_enc I) ->
  (forall e, In e (Cfg.edges (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) ->
    TabEncodingCost.bounded (Cfg.node_enc (Icfg.cfg (Ifds.icfg (Ide.ifds I))))
      (Graph.source (Cfg.graph (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) e) en wn) ->
  (forall d, In d (Ifds.facts (Ide.ifds I)) ->
    TabEncodingCost.bounded (Ifds.fact_enc (Ide.ifds I)) d ed wd) ->
  (Cost.ticks (Tab.prepare_c I start) <=
    prepare_charge I ko ks kt kk kf kw q en ed wn wd)%N.
Proof.
  intros HC HV Hnodes Hfacts.
  pose proof (arcs_cost I ko ks kt kk kf kw q HC) as Harcs.
  pose proof (roots_cost I start (Jump.arcs I)) as Hroots.
  pose proof (roots_length I start (Jump.arcs I)) as Hrootlength.
  pose proof (vertices_cost (Jump.arcs I)) as Hvertices.
  pose proof (keys_cost (Cost.value (Jump.roots_c I start (Jump.arcs I))) (Jump.arcs I))
    as Hkeys.
  pose proof (IndexCost.group_by_cost Map.cost_laws_hold (IdeValue.key_enc I) HV
    (fun a => Cost.ret (Jump.source a)) (Jump.arcs I)
    (TabEncodingCost.pair_charge en (TabEncodingCost.option_charge ed wd)
      wn (TabEncodingCost.option_width wd))
    (TabEncodingCost.pair_width wn (TabEncodingCost.option_width wd)) 0%N) as Hgroup.
  assert (Hbudgets : forall a, In a (Jump.arcs I) ->
    (Cost.ticks (Cost.ret (Jump.source a)) <= 0)%N /\
    (Cost.ticks (encode_c (IdeValue.key_enc I) (Jump.source a)) <=
      TabEncodingCost.pair_charge en (TabEncodingCost.option_charge ed wd)
        wn (TabEncodingCost.option_width wd))%N /\
    (key_bits (IdeValue.key_enc I) (Jump.source a) <=
      TabEncodingCost.pair_width wn (TabEncodingCost.option_width wd))%N).
  { intros a Ha; split; [reflexivity|].
    exact (source_budget I a en ed wn wd Hnodes Hfacts Ha). }
  specialize (Hgroup Hbudgets).
  unfold Tab.prepare_c; rewrite !Cost.ticks_bind, Cost.ticks_ret.
  fold (Jump.arcs I).
  rewrite fw_flat_map_value.
  change (Cost.ticks (Jump.arcs_c I) +
    (Cost.ticks (Jump.roots_c I start (Jump.arcs I)) +
    (Cost.ticks (Index.group_by_c (IdeValue.key_enc I)
      (fun a => Cost.ret (Jump.source a)) (Jump.arcs I)) +
    (Cost.ticks (fw_flat_map_c (fun a => Cost.ret [Jump.source a; Jump.target a])
      (Jump.arcs I)) +
    (Cost.ticks (fw_flat_map_c (fun root =>
      map_c (fun v => Cost.ret (root, v))
        (root :: flat_map (fun a => [Jump.source a; Jump.target a]) (Jump.arcs I)))
      (Cost.value (Jump.roots_c I start (Jump.arcs I)))) + 0)))) <=
      prepare_charge I ko ks kt kk kf kw q en ed wn wd)%N.
  unfold prepare_charge, arc_count in *; cbn zeta; nia.
Qed.

End TabPrepareCost.
