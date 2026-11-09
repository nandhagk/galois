(** * Ground jump checking and certified-run costs

    The checker pays for actual row generation and every reached primitive probe.
    For example, a stopped raw result retains the complete matched-return row preparation charge.
    Builds on: FrameworkTabRunCost and the existing unconditional ground jump checker. *)

From Stdlib Require Import List Arith NArith Lia.
From Galois.Cost Require Import CostMonad CostList CostBound.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Lattice Require Import LatticeCore LatticeHeight.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramCfg ProgramIcfg.
From Galois.Framework Require Import FrameworkUtil FrameworkMicro FrameworkIfds FrameworkIde
  FrameworkTabulate FrameworkTabPaths FrameworkTabCost FrameworkTabEncodingCost
  FrameworkTabPrepareCost FrameworkTabRunCost FrameworkTabJumpProgress.
Import List.ListNotations Cost.Notations.

Module TabCheckCost.

Local Lemma nat_N_le a b : (a <= b)%nat -> (N.of_nat a <= N.of_nat b)%N.
Proof.
  intro Hle; apply (proj1 (N.compare_le_iff _ _)).
  rewrite <- Nat2N.inj_compare; apply (proj2 (Nat.compare_le_iff _ _)); exact Hle.
Qed.

(** A list budget retains both callback work and the actual number of emitted occurrences. *)
Definition list_bound {X} (c : Cost.t (list X)) k n :=
  (Cost.ticks c <= k)%N /\ (N.of_nat (length (Cost.value c)) <= n)%N.

(** Optional callbacks are charged only on the actual supplied input list. *)
Theorem filter_cost_on {X Y} (f : X -> Cost.t (option Y)) xs k :
  (forall x, In x xs -> (Cost.ticks (f x) <= k)%N) ->
  list_bound (filter_map_c f xs) (N.of_nat (length xs) * (1 + k)) (N.of_nat (length xs)).
Proof.
  intro Hbound; split.
  - rewrite ticks_filter_map_c; induction xs as [|x xs IH]; cbn [fold_right length].
    + lia.
    + rewrite Nat2N.inj_succ.
      specialize (IH (fun y Hy => Hbound y (or_intror Hy))).
      specialize (Hbound x (or_introl eq_refl)); nia.
  - rewrite value_filter_map_c; apply nat_N_le, TabPrepareCost.filter_map_length.
Qed.

(** Flattening composes body work and actual emitted lengths at both traversal levels. *)
Theorem flat_bound {X Y} (f : X -> Cost.t (list Y)) xs k n :
  (forall x, In x xs -> list_bound (f x) k n) ->
  list_bound (fw_flat_map_c f xs)
    (N.of_nat (length xs) * (2 + k + n)) (N.of_nat (length xs) * n).
Proof.
  intro Hbound; split.
  - apply TabPrepareCost.flat_map_cost; exact Hbound.
  - rewrite fw_flat_map_value; apply TabPrepareCost.flat_length.
    intros x Hx; exact (proj2 (Hbound x Hx)).
Qed.

(** Short-circuit checking costs at most all actually listed callback bodies. *)
Theorem forall_cost_on {X} (f : X -> Cost.t bool) xs k :
  (forall x, In x xs -> (Cost.ticks (f x) <= k)%N) ->
  (Cost.ticks (forallb_c f xs) <= N.of_nat (length xs) * (1 + k))%N.
Proof.
  induction xs as [|x xs IH]; intro Hbound.
  - rewrite ticks_forallb_c_nil; lia.
  - rewrite ticks_forallb_c_cons; cbn [length]; rewrite Nat2N.inj_succ.
    specialize (IH (fun y Hy => Hbound y (or_intror Hy))).
    specialize (Hbound x (or_introl eq_refl)); destruct (Cost.value (f x)); nia.
Qed.

Definition row_count {N E P D A F} (I : Ide.t N E P D A F) :=
  let a := TabPrepareCost.arc_count I in
  let r := TabRunCost.roots I in
  (1 + TabPrepareCost.facts I + a + r * a + r * a * a)%N.
Definition rows_charge {N E P D A F} (I : Ide.t N E P D A F)
    ko ks kt kk kf kw q e w :=
  let a := TabPrepareCost.arc_count I in
  let d := TabPrepareCost.facts I in
  let r := TabRunCost.roots I in
  let match_charge := (2 + 2 * e + w)%N in
  (TabPrepareCost.arcs_charge I ko ks kt kk kf kw q + (3 * d + 2 + a) +
    d + (1 + d) + a + r * (2 + 2 * a) +
    r * (2 + a * (2 + a * (2 + match_charge)) + a * a) +
    r * a + a + (1 + d))%N.
Definition row_charge e w m := (6 + 3 * TabRunCost.probe e w + 4 * m)%N.
Definition checker_charge {N E P D A F} (I : Ide.t N E P D A F)
    ko ks kt kk kf kw q e w m :=
  (rows_charge I ko ks kt kk kf kw q e w +
    row_count I * (1 + row_charge e w m))%N.

Section Check.
Context {N E P D A F} (I : Ide.t N E P D A F) (start : N) (e w m : BinNums.N).
Context (HP : TabRunCost.primitives I start e w m).

Local Lemma path_rows root :
  list_bound (filter_map_c (fun a : Jump.arc N E P D F =>
    Cost.ret (match Jump.kind a with Icfg.Internal => Some (Jump.Path root a) | _ => None end))
    (Jump.arcs I)) (TabPrepareCost.arc_count I) (TabPrepareCost.arc_count I).
Proof.
  split.
  - rewrite TabPrepareCost.pure_filter_map_cost; reflexivity.
  - rewrite value_filter_map_c; apply nat_N_le, TabPrepareCost.filter_map_length.
Qed.

Local Lemma matched_rows root a :
  In a (Jump.arcs I) ->
  list_bound (filter_map_c (fun b =>
    let* yes := Jump.matches_c (Icfg.site_enc (Ifds.icfg (Ide.ifds I))) a b in
    Cost.ret (if yes then Some (Jump.Return root a b) else None)) (Jump.arcs I))
    (TabPrepareCost.arc_count I * (1 + (2 + 2 * e + w)))
    (TabPrepareCost.arc_count I).
Proof.
  intro Ha; apply filter_cost_on; intros b Hb.
  rewrite Cost.ticks_bind; autorewrite with galois_cost.
  pose proof (TabRunCost.matches_cost I start e w m HP a b Ha Hb); lia.
Qed.

Local Lemma return_rows root :
  list_bound (fw_flat_map_c (fun a =>
    filter_map_c (fun b =>
      let* yes := Jump.matches_c (Icfg.site_enc (Ifds.icfg (Ide.ifds I))) a b in
      Cost.ret (if yes then Some (Jump.Return root a b) else None)) (Jump.arcs I))
    (Jump.arcs I))
    (TabPrepareCost.arc_count I * (2 + TabPrepareCost.arc_count I * (2 + (2 + 2 * e + w))))
    (TabPrepareCost.arc_count I * TabPrepareCost.arc_count I).
Proof.
  pose proof (flat_bound (fun a =>
    filter_map_c (fun b =>
      let* yes := Jump.matches_c (Icfg.site_enc (Ifds.icfg (Ide.ifds I))) a b in
      Cost.ret (if yes then Some (Jump.Return root a b) else None)) (Jump.arcs I))
    (Jump.arcs I) _ _ (matched_rows root)) as [Hcost Hlength].
  split; [eapply N.le_trans; [exact Hcost|]; unfold TabPrepareCost.arc_count; nia|exact Hlength].
Qed.

Local Lemma all_paths :
  list_bound (fw_flat_map_c (fun root =>
    filter_map_c (fun a : Jump.arc N E P D F => Cost.ret
      (match Jump.kind a with Icfg.Internal => Some (Jump.Path root a) | _ => None end))
      (Jump.arcs I)) (TabPaths.roots I start))
    (TabRunCost.roots I * (2 + 2 * TabPrepareCost.arc_count I))
    (TabRunCost.roots I * TabPrepareCost.arc_count I).
Proof.
  destruct (flat_bound _ (TabPaths.roots I start) _ _
    (fun root _ => path_rows root)) as [Hcost Hlength].
  pose proof (TabRunCost.root_count I start) as Hroots.
  split.
  - eapply N.le_trans; [exact Hcost|].
    eapply N.le_trans; [apply N.mul_le_mono_r; exact Hroots|]; nia.
  - eapply N.le_trans; [exact Hlength|apply N.mul_le_mono_r; exact Hroots].
Qed.

Local Lemma all_returns :
  list_bound (fw_flat_map_c (fun root =>
    fw_flat_map_c (fun a =>
      filter_map_c (fun b =>
        let* yes := Jump.matches_c (Icfg.site_enc (Ifds.icfg (Ide.ifds I))) a b in
        Cost.ret (if yes then Some (Jump.Return root a b) else None)) (Jump.arcs I))
      (Jump.arcs I)) (TabPaths.roots I start))
    (TabRunCost.roots I * (2 +
      TabPrepareCost.arc_count I * (2 + TabPrepareCost.arc_count I * (2 + (2 + 2 * e + w))) +
      TabPrepareCost.arc_count I * TabPrepareCost.arc_count I))
    (TabRunCost.roots I * TabPrepareCost.arc_count I * TabPrepareCost.arc_count I).
Proof.
  destruct (flat_bound _ (TabPaths.roots I start) _ _
    (fun root _ => return_rows root)) as [Hcost Hlength].
  pose proof (TabRunCost.root_count I start) as Hroots.
  split.
  - eapply N.le_trans; [exact Hcost|apply N.mul_le_mono_r; exact Hroots].
  - eapply N.le_trans; [exact Hlength|].
    eapply N.le_trans; [apply N.mul_le_mono_r; exact Hroots|]; nia.
Qed.

Local Lemma initial_fact_count :
  N.of_nat (length (Jump.fact_domain (Ide.ifds I))) = (1 + TabPrepareCost.facts I)%N.
Proof.
  unfold Jump.fact_domain; cbn [length]; rewrite length_map, Nat2N.inj_succ.
  unfold TabPrepareCost.facts; lia.
Qed.

(** Row preparation charges actual callback bodies, both return scans and all copied list cells. *)
Theorem rows_cost ko ks kt kk kf kw q :
  TabPrepareCost.callbacks I ko ks kt kk kf kw q ->
  list_bound (Jump.rows_c I start)
    (rows_charge I ko ks kt kk kf kw q e w) (row_count I).
Proof.
  intro HC.
  pose proof (TabPrepareCost.arcs_cost I ko ks kt kk kf kw q HC) as Harcs.
  pose proof (TabPrepareCost.roots_cost I start (Jump.arcs I)) as Hroots.
  destruct all_paths as [Hpaths Hpath_length].
  destruct all_returns as [Hreturns Hreturn_length].
  pose proof (TabPrepareCost.filter_map_length (fun a : Jump.arc N E P D F =>
    match Jump.kind a with Icfg.Call _ => Some (Jump.Call a) | _ => None end)
    (Jump.arcs I)) as Hcall_length; apply nat_N_le in Hcall_length.
  fold (TabPrepareCost.arc_count I) in Hroots, Hcall_length.
  unfold list_bound; split.
  - unfold Jump.rows_c; rewrite !Cost.ticks_bind.
    change (Cost.value (Jump.arcs_c I)) with (Jump.arcs I).
    change (Cost.value (Jump.roots_c I start (Jump.arcs I))) with (TabPaths.roots I start).
    rewrite !TabPrepareCost.pure_map_cost, TabPrepareCost.pure_filter_map_cost.
    rewrite !ticks_app_c.
    autorewrite with galois_cost.
    change (None :: map (@Some D) (Ifds.facts (Ide.ifds I)))
      with (Jump.fact_domain (Ide.ifds I)).
    rewrite !length_map, ?initial_fact_count.
    cbn [length]; rewrite ?length_map, ?Nat2N.inj_succ.
    change (fun a : Jump.arc N E P D F => Cost.value (Cost.ret
      (match Jump.kind a with Icfg.Call _ => Some (Jump.Call a) | _ => None end)))
      with (fun a : Jump.arc N E P D F =>
        match Jump.kind a with Icfg.Call _ => Some (Jump.Call a) | _ => None end).
    fold (TabPrepareCost.facts I) (TabPrepareCost.arc_count I).
    unfold rows_charge; cbn zeta; lia.
  - unfold Jump.rows_c; autorewrite with galois_cost.
    change (Cost.value (Jump.arcs_c I)) with (Jump.arcs I).
    change (Cost.value (Jump.roots_c I start (Jump.arcs I))) with (TabPaths.roots I start).
    change (None :: map (@Some D) (Ifds.facts (Ide.ifds I)))
      with (Jump.fact_domain (Ide.ifds I)).
    rewrite !length_app, !length_map, !Nat2N.inj_add.
    rewrite ?initial_fact_count.
    cbn [length]; rewrite ?length_map, ?Nat2N.inj_succ.
    change (fun a : Jump.arc N E P D F => Cost.value (Cost.ret
      (match Jump.kind a with Icfg.Call _ => Some (Jump.Call a) | _ => None end)))
      with (fun a : Jump.arc N E P D F =>
        match Jump.kind a with Icfg.Call _ => Some (Jump.Call a) | _ => None end).
    fold (TabPrepareCost.arc_count I) in Hcall_length.
    fold (TabPrepareCost.facts I).
    unfold row_count; cbn zeta; lia.
Qed.

Local Lemma source_domain a :
  In a (Jump.arcs I) -> TabRunCost.coordinate I start (Jump.source a).
Proof.
  intro Ha; right; exists a; split; [exact Ha|left; reflexivity].
Qed.

Local Lemma target_domain a :
  In a (Jump.arcs I) -> TabRunCost.coordinate I start (Jump.target a).
Proof.
  intro Ha; right; exists a; split; [exact Ha|right; reflexivity].
Qed.

Local Lemma row_keys row :
  In row (Jump.rows I start) ->
  TabRunCost.coordinate I start (fst (Jump.output row)) /\
  TabRunCost.coordinate I start (snd (Jump.output row)).
Proof.
  rewrite Jump.rows_spec; intros [[root [Hr ->]]|
    [[a [p [Ha [Hkind ->]]]]|[[root [a [Hr [Ha [Hkind ->]]]]]|
    [root [a [b [Hr [Ha [Hb [Hmatch ->]]]]]]]]]].
  - assert (Hroot : In root (TabPaths.roots I start)).
    { rewrite TabPaths.roots_value; apply in_or_app; left; exact Hr. }
    split; left; exact Hroot.
  - split; apply target_domain; exact Ha.
  - split; [left; exact Hr|apply target_domain; exact Ha].
  - split; [left; exact Hr|apply target_domain; exact Hb].
Qed.

Local Lemma rhs_cost js row :
  In row (Jump.rows I start) ->
  (Cost.ticks (Jump.rhs_c I (Jump.lookup_c I js) row) <=
    5 + 2 * TabRunCost.probe e w + 3 * m)%N.
Proof.
  rewrite Jump.rows_spec; intros [[root [Hr ->]]|
    [[a [p [Ha [Hkind ->]]]]|[[root [a [Hr [Ha [Hkind ->]]]]]|
    [root [a [b [Hr [Ha [Hb [Hmatch ->]]]]]]]]]].
  - cbn [Jump.rhs_c]; rewrite Cost.ticks_ret; lia.
  - cbn [Jump.rhs_c]; rewrite Cost.ticks_ret; lia.
  - cbn [Jump.rhs_c]; eapply N.le_trans.
    + eapply TabRunCost.bind_cost; [reflexivity|]; intros [].
      eapply TabRunCost.bind_cost.
      * apply TabRunCost.lookup_cost with (start := start) (e := e) (w := w) (m := m).
        -- exact HP.
        -- left; exact Hr.
        -- apply source_domain; exact Ha.
      * intro prior; eapply TabRunCost.bind_cost; [reflexivity|]; intros [].
        exact (TabRunCost.compose HP _ _).
    + autorewrite with galois_cost; lia.
  - cbn [Jump.rhs_c]; eapply N.le_trans.
    + eapply TabRunCost.bind_cost; [reflexivity|]; intros [].
      eapply TabRunCost.bind_cost.
      * apply TabRunCost.lookup_cost with (start := start) (e := e) (w := w) (m := m).
        -- exact HP.
        -- left; exact Hr.
        -- apply source_domain; exact Ha.
      * intro prior; eapply TabRunCost.bind_cost; [reflexivity|]; intros [].
        eapply TabRunCost.bind_cost.
        -- apply TabRunCost.lookup_cost with (start := start) (e := e) (w := w) (m := m).
           ++ exact HP.
           ++ apply target_domain; exact Ha.
           ++ apply source_domain; exact Hb.
        -- intro inside; eapply TabRunCost.bind_cost; [reflexivity|]; intros [].
           eapply TabRunCost.bind_cost; [exact (TabRunCost.compose HP _ _)|]; intro pushed.
           eapply TabRunCost.bind_cost; [reflexivity|]; intros [].
           eapply TabRunCost.bind_cost; [exact (TabRunCost.compose HP _ _)|]; intro body.
           eapply TabRunCost.bind_cost; [reflexivity|]; intros [].
           exact (TabRunCost.compose HP _ _).
    + autorewrite with galois_cost; lia.
Qed.

(** Any candidate pays a numerical checker bound without a certificate or final-state hypothesis. *)
Theorem checker_cost js ko ks kt kk kf kw q :
  TabPrepareCost.callbacks I ko ks kt kk kf kw q ->
  (Cost.ticks (check_jumps_c I start js) <=
    checker_charge I ko ks kt kk kf kw q e w m)%N.
Proof.
  intro HC; destruct (rows_cost ko ks kt kk kf kw q HC) as [Hprepare Hlength].
  assert (Hrow : forall row, In row (Jump.rows I start) ->
    (Cost.ticks
      (let* value := Jump.rhs_c I (Jump.lookup_c I js) row in
       let* bound := Jump.lookup_c I js (Jump.output row) in
       Cost.step ;; leb_c (Micro.lat (Ide.micro I)) value bound) <= row_charge e w m)%N).
  { intros row Hr; destruct (row_keys row Hr) as [Hroot Hdst].
    destruct (Jump.output row) as [root dst] eqn:Houtput.
    eapply N.le_trans.
    - eapply TabRunCost.bind_cost; [apply rhs_cost; exact Hr|]; intro value.
      eapply TabRunCost.bind_cost.
      + apply TabRunCost.lookup_cost with (start := start) (e := e) (w := w) (m := m);
          assumption.
      + intro bound; eapply TabRunCost.bind_cost; [reflexivity|]; intros [].
        exact (TabRunCost.compare HP _ _).
    - autorewrite with galois_cost; unfold row_charge; lia. }
  pose proof (forall_cost_on _ (Jump.rows I start) _ Hrow) as Hcheck.
  assert (Hscaled :
    (N.of_nat (length (Jump.rows I start)) * (1 + row_charge e w m) <=
      row_count I * (1 + row_charge e w m))%N).
  { apply N.mul_le_mono_r; exact Hlength. }
  unfold check_jumps_c; rewrite Cost.ticks_bind.
  change (Cost.value (Jump.rows_c I start)) with (Jump.rows I start).
  unfold checker_charge; lia.
Qed.

End Check.

(** The charged jump wrapper includes full row generation and checking on every stopped candidate. *)
Theorem tabulate_cost {N E P D A F} (I : Ide.t N E P D A F) start fuel e w m
    ko ks kt kk kf kw q :
  TabRunCost.primitives I start e w m ->
  encoding_laws (IdeValue.key_enc I) -> encoding_laws (Jump.enc I) ->
  TabPrepareCost.callbacks I ko ks kt kk kf kw q ->
  (forall edge, In edge (Cfg.edges (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) ->
    TabEncodingCost.bounded (Cfg.node_enc (Icfg.cfg (Ifds.icfg (Ide.ifds I))))
      (Graph.source (Cfg.graph (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) edge) e w) ->
  (forall d, In d (Ifds.facts (Ide.ifds I)) ->
    TabEncodingCost.bounded (Ifds.fact_enc (Ide.ifds I)) d e w) ->
  (Cost.ticks (Tab.tabulate_c I start fuel) <=
    TabPrepareCost.prepare_charge I ko ks kt kk kf kw q e e w w +
    TabRunCost.initial_charge I e w m + (TabRunCost.step_charge I e w m + 2) * N.pos fuel +
    checker_charge I ko ks kt kk kf kw q e w m)%N.
Proof.
  intros HP HV HK HC Hnodes Hfacts.
  pose proof (TabRunCost.raw_numeric I start e w m HP HV HK fuel
    ko ks kt kk kf kw q HC Hnodes Hfacts) as Hraw.
  rewrite Tab.tabulate_cost_equation.
  destruct (Tab.raw I start fuel) as [exhausted|stopped]; [lia|].
  pose proof (checker_cost I start e w m HP (Tab.jumps stopped) ko ks kt kk kf kw q HC); lia.
Qed.

(** Constructed certified jump execution retains both fuel construction and the actual checker. *)
Theorem complete_cost {N E P D A F} (I : Ide.t N E P D A F) start e w m
    ko ks kt kk kf kw q (H : height (Micro.lat (Ide.micro I))) :
  TabRunCost.primitives I start e w m ->
  encoding_laws (IdeValue.key_enc I) -> encoding_laws (Jump.enc I) ->
  TabPrepareCost.callbacks I ko ks kt kk kf kw q ->
  (forall edge, In edge (Cfg.edges (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) ->
    TabEncodingCost.bounded (Cfg.node_enc (Icfg.cfg (Ifds.icfg (Ide.ifds I))))
      (Graph.source (Cfg.graph (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) edge) e w) ->
  (forall d, In d (Ifds.facts (Ide.ifds I)) ->
    TabEncodingCost.bounded (Ifds.fact_enc (Ide.ifds I)) d e w) ->
  (Cost.ticks (TabJumpProgress.complete_c I start H) <=
    TabRunCost.complete_charge I ko ks kt kk kf kw q e w m (N.of_nat (bound H)) +
    checker_charge I ko ks kt kk kf kw q e w m)%N.
Proof.
  intros HP HV HK HC Hnodes Hfacts.
  pose proof (TabRunCost.complete_raw_numeric I start e w m
    ko ks kt kk kf kw q H HP HV HK HC Hnodes Hfacts) as Hraw.
  rewrite TabJumpProgress.complete_cost_equation.
  destruct (TabJumpProgress.complete_raw I start H) as [exhausted|stopped]; [lia|].
  pose proof (checker_cost I start e w m HP (Tab.jumps stopped) ko ks kt kk kf kw q HC); lia.
Qed.

(** A family of certified jump runs has the complete primitive-derived polynomial as its big-O bound. *)
Theorem tabulate_bigO {X N E P D A F}
    (I : X -> Ide.t N E P D A F) (start : X -> N)
    (e w m ko ks kt kk kf kw q : X -> BinNums.N)
    (H : forall x, height (Micro.lat (Ide.micro (I x)))) :
  (forall x, TabRunCost.primitives (I x) (start x) (e x) (w x) (m x)) ->
  (forall x, encoding_laws (IdeValue.key_enc (I x))) ->
  (forall x, encoding_laws (Jump.enc (I x))) ->
  (forall x, TabPrepareCost.callbacks (I x) (ko x) (ks x) (kt x) (kk x) (kf x) (kw x) (q x)) ->
  (forall x edge, In edge (Cfg.edges (Icfg.cfg (Ifds.icfg (Ide.ifds (I x))))) ->
    TabEncodingCost.bounded (Cfg.node_enc (Icfg.cfg (Ifds.icfg (Ide.ifds (I x)))))
      (Graph.source (Cfg.graph (Icfg.cfg (Ifds.icfg (Ide.ifds (I x))))) edge) (e x) (w x)) ->
  (forall x d, In d (Ifds.facts (Ide.ifds (I x))) ->
    TabEncodingCost.bounded (Ifds.fact_enc (Ide.ifds (I x))) d (e x) (w x)) ->
  bigO
    (fun x => (TabRunCost.complete_charge (I x) (ko x) (ks x) (kt x) (kk x) (kf x) (kw x) (q x)
      (e x) (w x) (m x) (N.of_nat (bound (H x))) +
      checker_charge (I x) (ko x) (ks x) (kt x) (kk x) (kf x) (kw x) (q x)
        (e x) (w x) (m x))%N)
    (fun x => Cost.ticks (TabJumpProgress.complete_c (I x) (start x) (H x))).
Proof.
  intros HP HV HK HC Hnodes Hfacts; exists 1%N; intro x.
  pose proof (complete_cost (I x) (start x) (e x) (w x) (m x)
    (ko x) (ks x) (kt x) (kk x) (kf x) (kw x) (q x) (H x)
    (HP x) (HV x) (HK x) (HC x) (Hnodes x) (Hfacts x)); lia.
Qed.

End TabCheckCost.
