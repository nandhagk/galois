(** * Primitive costs of value certificate preparation

    Prepared row plans keep their actual fixed reads and captured symbolic weights.
    For example, a Seed plan reads no listed destination and retains an unlisted start.
    Builds on: FrameworkTabValueRunCost, FrameworkRows and public bulk-query equations. *)

From Stdlib Require Import List Arith NArith Lia.
From Galois.Cost Require Import CostMonad CostList CostBound.
From Galois.Base Require Import BaseEncoding BaseCode BaseEq BaseMap.
From Galois.Lattice Require Import LatticeCore LatticeHeight.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramCfg ProgramIcfg.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointAnalysis FixpointEval
  FixpointCheck.
From Galois.Framework Require Import FrameworkUtil FrameworkMicro FrameworkIfds FrameworkIde
  FrameworkRows FrameworkTabulate FrameworkTabValues FrameworkTabCost FrameworkTabEncodingCost
  FrameworkTabPrepareCost FrameworkTabPaths FrameworkTabRunCost FrameworkTabCheckCost
  FrameworkTabValueRunCost
  FrameworkTabValueProgress.
Import List.ListNotations Cost.Notations.

Module TabValueCheckCost.

Local Lemma nat_N_le a b : (a <= b)%nat -> (N.of_nat a <= N.of_nat b)%N.
Proof.
  intro Hle; apply (proj1 (N.compare_le_iff _ _)).
  rewrite <- Nat2N.inj_compare; apply (proj2 (Nat.compare_le_iff _ _)); exact Hle.
Qed.

Definition inner_width w :=
  TabEncodingCost.sum_width (TabRunCost.jw w + TabRunCost.aw w).
Definition inner_charge e w :=
  TabEncodingCost.sum_charge (TabRunCost.je e w + TabRunCost.ae e w)
    (TabRunCost.jw w + TabRunCost.aw w).
Definition row_width w := TabEncodingCost.sum_width (1 + inner_width w).
Definition row_charge e w := (2 + TabEncodingCost.sum_charge (1 + inner_charge e w)
  (1 + inner_width w))%N.
Definition row_probe e w := (1 + row_charge e w + row_width w)%N.
Definition rows {N E P D A F} (I : Ide.t N E P D A F) :=
  (1 + TabValueRunCost.transitions I)%N.

(** A prepared plan uses at most one supported read and a genuine bounded evaluator callback. *)
Record plan_bound {N E P D A F} (I : Ide.t N E P D A F) start m
    (plan : Rows.t (N * option D) A) : Prop := {
  target_supported : TabValueRunCost.coordinate I start (Rows.target plan);
  reads_supported : forall v, In v (Rows.reads plan) ->
    TabValueRunCost.coordinate I start v;
  reads_length : (length (Rows.reads plan) <= 1)%nat;
  eval_cost : forall values, (Cost.ticks (Rows.eval_c plan values) <= 1 + m)%N
}.
Arguments target_supported {N E P D A F I start m plan}.
Arguments reads_supported {N E P D A F I start m plan}.
Arguments reads_length {N E P D A F I start m plan}.
Arguments eval_cost {N E P D A F I start m plan}.

Local Ltac add_budgets :=
  first [
    eassumption
  | match goal with
    | |- (?a + ?b <= _)%N => eapply N.add_le_mono; add_budgets
    end
  | apply N.le_refl ].

Section Plans.
Context {N E P D A F} (I : Ide.t N E P D A F) (J : Map.t positive F)
  (start : N * option D) (a0 : A) (e w m : BinNums.N).
Context (HP : TabValueRunCost.primitives I start e w m).
Context (HE : forall a, In a (Jump.arcs I) ->
  TabEncodingCost.bounded (Cfg.edge_enc (Icfg.cfg (Ifds.icfg (Ide.ifds I))))
    (Jump.edge a) e w).

Local Lemma row_seed_budget :
  TabEncodingCost.bounded (IdeValue.row_enc I) VSeed (row_charge e w) (row_width w).
Proof.
  split.
  - unfold IdeValue.row_enc; rewrite encoding_comap_cost, Cost.ticks_ret.
    pose proof (TabEncodingCost.sum_bounded unit_encoding
      (FrameworkKey.sum (Jump.enc I) (Tab.arc_enc I)) (inl tt)
      (1 + inner_charge e w)%N (1 + inner_width w)%N) as Hsum.
    assert (Hunit : TabEncodingCost.bounded unit_encoding tt
      (1 + inner_charge e w)%N (1 + inner_width w)%N).
    { split.
      - change (1 <= 1 + inner_charge e w)%N; lia.
      - change (1 <= 1 + inner_width w)%N; lia. }
    destruct (Hsum Hunit) as [Hcost Hbits].
    change (2 + 0 + Cost.ticks (encode_c
      (FrameworkKey.sum unit_encoding (FrameworkKey.sum (Jump.enc I) (Tab.arc_enc I)))
      (inl tt)) <= row_charge e w)%N.
    eapply N.le_trans; [add_budgets|]; unfold row_charge; lia.
  - change (key_bits (FrameworkKey.sum unit_encoding
      (FrameworkKey.sum (Jump.enc I) (Tab.arc_enc I))) (inl tt) <= row_width w)%N.
    rewrite TabEncodingCost.sum_bits.
    change (5 + 2 * 1 <= row_width w)%N.
    unfold row_width, TabEncodingCost.sum_width; lia.
Qed.

Local Lemma row_jump_budget root dst :
  TabValueRunCost.coordinate I start root -> TabValueRunCost.coordinate I start dst ->
  TabEncodingCost.bounded (IdeValue.row_enc I) (VJump root dst)
    (row_charge e w) (row_width w).
Proof.
  intros Hr Hd.
  destruct (TabEncodingCost.jump_bounded I root dst _ _
    (TabValueRunCost.vertex_budget I start e w m HP root Hr)
    (TabValueRunCost.vertex_budget I start e w m HP dst Hd)) as [He Hw].
  fold (TabRunCost.je e w) in He; fold (TabRunCost.jw w) in Hw.
  assert (Hjump : TabEncodingCost.bounded (Jump.enc I) (root, dst)
    (TabRunCost.je e w + TabRunCost.ae e w)%N
    (TabRunCost.jw w + TabRunCost.aw w)%N) by (split; lia).
  pose proof (TabEncodingCost.sum_bounded (Jump.enc I) (Tab.arc_enc I) (inl (root, dst))
    _ _ Hjump) as Hinner.
  fold (inner_charge e w) (inner_width w) in Hinner.
  assert (Hinner' : TabEncodingCost.bounded
    (FrameworkKey.sum (Jump.enc I) (Tab.arc_enc I)) (inl (root, dst))
    (1 + inner_charge e w)%N (1 + inner_width w)%N).
  { destruct Hinner as [Hc Hb]; split; lia. }
  pose proof (TabEncodingCost.sum_bounded unit_encoding
    (FrameworkKey.sum (Jump.enc I) (Tab.arc_enc I)) (inr (inl (root, dst)))
    _ _ Hinner') as [Hcost Hbits].
  split.
  - unfold IdeValue.row_enc; rewrite encoding_comap_cost, Cost.ticks_ret.
    change (2 + 0 + Cost.ticks (encode_c
      (FrameworkKey.sum unit_encoding (FrameworkKey.sum (Jump.enc I) (Tab.arc_enc I)))
      (inr (inl (root, dst)))) <= row_charge e w)%N.
    eapply N.le_trans; [add_budgets|]; unfold row_charge; lia.
  - exact Hbits.
Qed.

Local Lemma row_call_budget a :
  In a (Jump.arcs I) ->
  TabEncodingCost.bounded (IdeValue.row_enc I)
    (VCall (Jump.edge a) (snd (Jump.source a)) (snd (Jump.target a)))
    (row_charge e w) (row_width w).
Proof.
  intro Ha.
  assert (Hs : TabValueRunCost.coordinate I start (Jump.source a)).
  { right; left; right; exists a; split; [exact Ha|left; reflexivity]. }
  assert (Ht : TabValueRunCost.coordinate I start (Jump.target a)).
  { right; left; right; exists a; split; [exact Ha|right; reflexivity]. }
  destruct (TabEncodingCost.arc_bounded I a e e w w (HE a Ha)
    (TabValueRunCost.fact HP (Jump.source a) Hs)
    (TabValueRunCost.fact HP (Jump.target a) Ht)) as [Hea Hwa].
  fold (TabRunCost.ae e w) in Hea; fold (TabRunCost.aw w) in Hwa.
  assert (Harc : TabEncodingCost.bounded (Tab.arc_enc I) (Tab.arc_key a)
    (TabRunCost.je e w + TabRunCost.ae e w)%N
    (TabRunCost.jw w + TabRunCost.aw w)%N) by (split; lia).
  pose proof (TabEncodingCost.sum_bounded (Jump.enc I) (Tab.arc_enc I) (inr (Tab.arc_key a))
    _ _ Harc) as Hinner.
  fold (inner_charge e w) (inner_width w) in Hinner.
  assert (Hinner' : TabEncodingCost.bounded
    (FrameworkKey.sum (Jump.enc I) (Tab.arc_enc I)) (inr (Tab.arc_key a))
    (1 + inner_charge e w)%N (1 + inner_width w)%N).
  { destruct Hinner as [Hc Hb]; split; lia. }
  pose proof (TabEncodingCost.sum_bounded unit_encoding
    (FrameworkKey.sum (Jump.enc I) (Tab.arc_enc I)) (inr (inr (Tab.arc_key a)))
    _ _ Hinner') as [Hcost Hbits].
  split.
  - unfold IdeValue.row_enc; rewrite encoding_comap_cost, Cost.ticks_ret.
    change (2 + 0 + Cost.ticks (encode_c
      (FrameworkKey.sum unit_encoding (FrameworkKey.sum (Jump.enc I) (Tab.arc_enc I)))
      (inr (inr (Tab.arc_key a)))) <= row_charge e w)%N.
    eapply N.le_trans; [add_budgets|]; unfold row_charge; lia.
  - exact Hbits.
Qed.

Local Lemma seed_plan :
  plan_bound I start m (Rows.Make start [] (fun _ => Cost.ret a0)).
Proof.
  constructor.
  - left; reflexivity.
  - intros v Hv; inversion Hv.
  - cbn [Rows.reads length]; lia.
  - intro values; cbn [Rows.eval_c]; rewrite Cost.ticks_ret; lia.
Qed.

Local Lemma transfer_plan source target weight :
  TabValueRunCost.coordinate I start source -> TabValueRunCost.coordinate I start target ->
  plan_bound I start m (Rows.Make target [source] (fun values =>
    match values with
    | a :: _ => Cost.step ;; Micro.apply_c (Ide.micro I) weight a
    | [] => Cost.ret (bot (Ide.values I))
    end)).
Proof.
  intros Hsource Htarget; constructor; cbn [Rows.target Rows.reads Rows.eval_c].
  - exact Htarget.
  - intros v [Heq|Hbad]; [subst v; exact Hsource|contradiction].
  - cbn [length]; lia.
  - intros [|a values].
    + rewrite Cost.ticks_ret; lia.
    + rewrite Cost.ticks_bind, Cost.ticks_step.
      pose proof (TabValueRunCost.apply HP weight a); lia.
Qed.

(** Every actually generated plan and row code satisfies its own primitive-derived contract. *)
Theorem prepared_plans row plan :
  In (row, plan) (Cost.value (IdeValue.prepare_c I (Jump.lookup_c I J) start a0)) ->
  plan_bound I start m plan /\
    TabEncodingCost.bounded (IdeValue.row_enc I) row (row_charge e w) (row_width w).
Proof.
  unfold IdeValue.prepare_c; rewrite Cost.value_bind.
  change (Cost.value (Jump.arcs_c I)) with (Jump.arcs I).
  rewrite Cost.value_bind.
  change (Cost.value (Jump.roots_c I (fst start) (Jump.arcs I)))
    with (TabPaths.roots I (fst start)).
  rewrite Cost.value_bind, value_map_c.
  change (fun d : D => Cost.value (Cost.ret (Some d))) with (@Some D).
  change (None :: map (@Some D) (Ifds.facts (Ide.ifds I)))
    with (Jump.fact_domain (Ide.ifds I)).
  rewrite Cost.value_bind, TabValueRunCost.vertices_value.
  autorewrite with galois_cost.
  intros [Hseed|Hin].
  - injection Hseed as Hrow Hplan; subst row plan; split; [apply seed_plan|apply row_seed_budget].
  - apply in_app_iff in Hin; destruct Hin as [Hsummary|Hcall].
    + rewrite fw_flat_map_value in Hsummary.
      apply in_flat_map in Hsummary; destruct Hsummary as [root [Hr Hsummary]].
      rewrite value_map_c in Hsummary; apply in_map_iff in Hsummary.
      destruct Hsummary as [dst [Heq Hd]].
      autorewrite with galois_cost in Heq; injection Heq as Hrow Hplan; subst row plan.
      split.
      * apply transfer_plan; [right; left; left; exact Hr|right; right; exact Hd].
      * apply row_jump_budget; [right; left; left; exact Hr|right; right; exact Hd].
    + apply filter_map_spec in Hcall; destruct Hcall as [a [Ha Heq]].
      destruct (Jump.kind a) as [|p|p] eqn:Hkind; cbn [Cost.value] in Heq; try discriminate.
      injection Heq as Hrow Hplan; subst row plan; split.
      * apply transfer_plan; right; left; right; exists a; split;
          [exact Ha|left; reflexivity|exact Ha|right; reflexivity].
      * apply row_call_budget; exact Ha.
Qed.

End Plans.

(** A fixed-read plan constructs at most one Ask and retains its evaluator's actual charge. *)
Theorem query_build_cost {N E P D A F} (I : Ide.t N E P D A F) start m plan :
  plan_bound I start m plan -> (Cost.ticks (Rows.query_c plan) <= 3 + m)%N.
Proof.
  intro HP; pose proof (reads_length HP) as Hlen.
  unfold Rows.query_c; destruct (Rows.reads plan) as [|x [|y xs]] eqn:Hreads.
  - rewrite ask_all_c_nil; autorewrite with galois_cost.
    pose proof (eval_cost HP []); lia.
  - rewrite ask_all_c_cons; autorewrite with galois_cost; lia.
  - cbn [length] in Hlen; lia.
Qed.

(** The selected fixed-read query has at most two nodes and bounded actual continuation work. *)
Theorem query_within {N E P D A F} (I : Ide.t N E P D A F) start m plan sigma :
  plan_bound I start m plan ->
  Query.within (3 + m)%N sigma 2 (Rows.query plan).
Proof.
  intro HP; pose proof (reads_length HP) as Hlen.
  unfold Rows.query, Rows.query_c.
  destruct (Rows.reads plan) as [|x [|y xs]] eqn:Hreads.
  - rewrite ask_all_c_nil; autorewrite with galois_cost.
    eapply Query.within_bound; [apply Query.within_ret|lia].
  - rewrite ask_all_c_cons; autorewrite with galois_cost.
    apply Query.within_ask.
    + rewrite ask_all_c_nil; autorewrite with galois_cost.
      pose proof (eval_cost HP [sigma x]); lia.
    + rewrite ask_all_c_nil; autorewrite with galois_cost; apply Query.within_ret.
  - cbn [length] in Hlen; lia.
Qed.

(** Every default lookup in a constructed plan table returns an actual safe payload or its default. *)
Theorem of_list_payload {K V} (EK : encoding K) (P : V -> Prop) xs key fallback :
  P fallback -> (forall kv, In kv xs -> P (snd kv)) ->
  P (Map.find_or EK fallback key (Map.of_list EK xs)).
Proof.
  intros Hfallback Hentries; rewrite Map.find_or_equation, Map.of_list_get.
  assert (Hfold : forall ys old,
    (forall kv, In kv ys -> P (snd kv)) ->
    (match old with Some value => P value | None => True end) ->
    match fold_left (fun old kv => if BaseEq.eqb EK key (fst kv) then Some (snd kv) else old)
      ys old with
    | Some value => P value
    | None => True
    end).
  { intro ys; induction ys as [|kv ys IH]; intros old Hys Hold; cbn [fold_left].
    - exact Hold.
    - apply IH.
      + intros entry Hin; apply Hys; right; exact Hin.
      + destruct (BaseEq.eqb EK key (fst kv)); [apply Hys; left; reflexivity|exact Hold]. }
  specialize (Hfold xs None Hentries Logic.I).
  destruct (fold_left _ xs None); [exact Hfold|exact Hfallback].
Qed.

Definition plan_charge {N E P D A F} (I : Ide.t N E P D A F)
    ko ks kt kk kf kw q e w :=
  (TabPrepareCost.arcs_charge I ko ks kt kk kf kw q +
    (3 * TabPrepareCost.facts I + 2 + TabPrepareCost.arc_count I) +
    TabPrepareCost.facts I + TabPrepareCost.nodes I * (4 + 2 * TabPrepareCost.facts I) +
    TabRunCost.roots I *
      (2 + TabValueRunCost.vertices I * (3 + TabRunCost.probe e w)) +
    TabPrepareCost.arc_count I + TabRunCost.roots I * TabValueRunCost.vertices I)%N.
Definition analysis_charge {N E P D A F} (I : Ide.t N E P D A F)
    ko ks kt kk kf kw q e w :=
  (plan_charge I ko ks kt kk kf kw q e w +
    rows I * (3 + row_charge e w + row_width w))%N.
Definition constraint_charge e w m :=
  (32 + 2 * row_probe e w + 4 * TabValueRunCost.probe e w + 5 * m)%N.
Definition checker_charge {N E P D A F} (I : Ide.t N E P D A F)
    ko ks kt kk kf kw q e w m :=
  (analysis_charge I ko ks kt kk kf kw q e w +
    rows I * (1 + constraint_charge e w m))%N.

Section Preparation.
Context {N E P D A F} (I : Ide.t N E P D A F) (J : Map.t positive F)
  (start : N * option D) (a0 : A) (e w m : BinNums.N).
Context (HP : TabValueRunCost.primitives I start e w m).
Context (HE : forall a, In a (Jump.arcs I) ->
  TabEncodingCost.bounded (Cfg.edge_enc (Icfg.cfg (Ifds.icfg (Ide.ifds I))))
    (Jump.edge a) e w).

Local Lemma summary_plans {B} (make : (N * option D) -> (N * option D) -> F -> B) :
  TabCheckCost.list_bound
    (fw_flat_map_c (fun root =>
      map_c (fun dst =>
        Cost.step ;; let* weight := Jump.lookup_c I J (root, dst) in
        Cost.ret (make root dst weight)) (IdeValue.vertices I))
      (TabPaths.roots I (fst start)))
    (TabRunCost.roots I *
      (2 + TabValueRunCost.vertices I * (3 + TabRunCost.probe e w)))
    (TabRunCost.roots I * TabValueRunCost.vertices I).
Proof.
  assert (Hbody : forall root, In root (TabPaths.roots I (fst start)) ->
    TabCheckCost.list_bound (map_c (fun dst =>
      Cost.step ;; let* weight := Jump.lookup_c I J (root, dst) in
      Cost.ret (make root dst weight)) (IdeValue.vertices I))
      (TabValueRunCost.vertices I * (2 + TabRunCost.probe e w)) (TabValueRunCost.vertices I)).
  { intros root Hr; split.
    - eapply N.le_trans.
      + apply TabPrepareCost.map_cost_on with (k := (1 + TabRunCost.probe e w)%N).
        intros dst Hd; autorewrite with galois_cost.
        pose proof (TabValueRunCost.jump_probe I start e w m HP J root dst
          (or_intror (or_introl (or_introl Hr))) (or_intror (or_intror Hd))); lia.
      + eapply N.le_trans; [apply N.mul_le_mono_r; apply TabValueRunCost.vertices_length|]; nia.
    - rewrite value_map_c, length_map; apply TabValueRunCost.vertices_length. }
  destruct (TabCheckCost.flat_bound _ _ _ _ Hbody) as [Hcost Hlength].
  pose proof (TabRunCost.root_count I (fst start)) as Hroots.
  split.
  - eapply N.le_trans; [exact Hcost|].
    eapply N.le_trans; [apply N.mul_le_mono_r; exact Hroots|]; nia.
  - eapply N.le_trans; [exact Hlength|apply N.mul_le_mono_r; exact Hroots].
Qed.

(** Actual certificate plan generation retains captured jump-reader costs and row occurrences. *)
Theorem prepare_cost ko ks kt kk kf kw q :
  TabPrepareCost.callbacks I ko ks kt kk kf kw q ->
  TabCheckCost.list_bound (IdeValue.prepare_c I (Jump.lookup_c I J) start a0)
    (plan_charge I ko ks kt kk kf kw q e w) (rows I).
Proof.
  intro HC.
  pose proof (TabPrepareCost.arcs_cost I ko ks kt kk kf kw q HC) as Harcs.
  pose proof (TabPrepareCost.roots_cost I (fst start) (Jump.arcs I)) as Hroots.
  pose proof (TabValueRunCost.vertices_cost I) as Hvertices.
  destruct (summary_plans (fun root dst weight =>
    (@VJump N E D root dst, Rows.Make dst [root] (fun values =>
      match values with
      | a :: _ => Cost.step ;; Micro.apply_c (Ide.micro I) weight a
      | [] => Cost.ret (bot (Ide.values I))
      end)))) as [Hsummary Hsummary_length].
  pose proof (TabPrepareCost.filter_map_length (fun a : Jump.arc N E P D F =>
    match Jump.kind a with
    | Icfg.Call _ => Some
        (@VCall N E D (Jump.edge a) (snd (Jump.source a)) (snd (Jump.target a)),
        Rows.Make (Jump.target a) [Jump.source a] (fun values =>
          match values with
          | value :: _ => Cost.step ;; Micro.apply_c (Ide.micro I) (Jump.weight a) value
          | [] => Cost.ret (bot (Ide.values I))
          end))
    | _ => None
    end) (Jump.arcs I)) as Hcalls.
  assert (HcallsN : (N.of_nat (length (filter_map (fun a : Jump.arc N E P D F =>
    match Jump.kind a with
    | Icfg.Call _ => Some
        (@VCall N E D (Jump.edge a) (snd (Jump.source a)) (snd (Jump.target a)),
        Rows.Make (Jump.target a) [Jump.source a] (fun values =>
          match values with
          | value :: _ => Cost.step ;; Micro.apply_c (Ide.micro I) (Jump.weight a) value
          | [] => Cost.ret (bot (Ide.values I))
          end))
    | _ => None
    end) (Jump.arcs I))) <= TabPrepareCost.arc_count I)%N) by (apply nat_N_le; exact Hcalls).
  unfold TabCheckCost.list_bound; split.
  - unfold IdeValue.prepare_c; rewrite !Cost.ticks_bind.
    change (Cost.value (Jump.arcs_c I)) with (Jump.arcs I).
    change (Cost.value (Jump.roots_c I (fst start) (Jump.arcs I)))
      with (TabPaths.roots I (fst start)).
    rewrite TabPrepareCost.pure_map_cost, value_map_c.
    change (fun d : D => Cost.value (Cost.ret (Some d))) with (@Some D).
    change (None :: map (@Some D) (Ifds.facts (Ide.ifds I)))
      with (Jump.fact_domain (Ide.ifds I)).
    rewrite TabValueRunCost.vertices_value.
    rewrite TabPrepareCost.pure_filter_map_cost, ticks_app_c, !Cost.ticks_ret.
    fold (TabPrepareCost.facts I) (TabPrepareCost.arc_count I) in *.
    rewrite Hroots.
    eapply N.le_trans; [add_budgets|]; unfold plan_charge; lia.
  - unfold IdeValue.prepare_c; rewrite !Cost.value_bind.
    change (Cost.value (Jump.arcs_c I)) with (Jump.arcs I).
    change (Cost.value (Jump.roots_c I (fst start) (Jump.arcs I)))
      with (TabPaths.roots I (fst start)).
    rewrite value_map_c.
    change (fun d : D => Cost.value (Cost.ret (Some d))) with (@Some D).
    change (None :: map (@Some D) (Ifds.facts (Ide.ifds I)))
      with (Jump.fact_domain (Ide.ifds I)).
    rewrite TabValueRunCost.vertices_value.
    rewrite !Cost.value_ret, value_app_c, value_filter_map_c.
    change (fun a : Jump.arc N E P D F => Cost.value (Cost.ret
      (match Jump.kind a with
       | Icfg.Call _ => Some
           (@VCall N E D (Jump.edge a) (snd (Jump.source a)) (snd (Jump.target a)),
           Rows.Make (Jump.target a) [Jump.source a] (fun values =>
             match values with
             | value :: _ => Cost.step ;; Micro.apply_c (Ide.micro I) (Jump.weight a) value
             | [] => Cost.ret (bot (Ide.values I))
             end))
       | _ => None
       end))) with (fun a : Jump.arc N E P D F =>
       match Jump.kind a with
       | Icfg.Call _ => Some
           (@VCall N E D (Jump.edge a) (snd (Jump.source a)) (snd (Jump.target a)),
           Rows.Make (Jump.target a) [Jump.source a] (fun values =>
             match values with
             | value :: _ => Cost.step ;; Micro.apply_c (Ide.micro I) (Jump.weight a) value
             | [] => Cost.ret (bot (Ide.values I))
             end))
       | _ => None
       end).
    match goal with
    | |- (N.of_nat (length (_ :: ?tail)) <= _)%N =>
      change (N.of_nat (S (length tail)) <= rows I)%N
    end.
    rewrite length_app, Nat2N.inj_succ, Nat2N.inj_add.
    unfold rows, TabValueRunCost.transitions; nia.
Qed.

(** Analysis construction prices the actual plan table insertion and row-list traversal. *)
Theorem analysis_cost ko ks kt kk kf kw q :
  TabPrepareCost.callbacks I ko ks kt kk kf kw q ->
  (Cost.ticks (IdeValue.analysis_c I (Jump.lookup_c I J) start a0) <=
    analysis_charge I ko ks kt kk kf kw q e w)%N.
Proof.
  intro HC; destruct (prepare_cost ko ks kt kk kf kw q HC) as [Hprepare Hlength].
  set (plans := Cost.value (IdeValue.prepare_c I (Jump.lookup_c I J) start a0)).
  assert (Htable : (Cost.ticks (Map.of_list_c (IdeValue.row_enc I) plans) <=
    rows I * (2 + row_charge e w + row_width w))%N).
  { rewrite Map.of_list_cost_equation.
    change (Cost.ticks (@Map.empty_c (vrow N E D) (Rows.t (N * option D) A))) with 0%N.
    eapply N.le_trans.
    - apply N.add_le_mono_l.
      apply TabRunCost.fold_cost with (P := fun _ => True)
        (k := (1 + row_charge e w + row_width w)%N); [|exact Logic.I].
      intros table [row plan] Htrue Hin; split; [exact Logic.I|].
      destruct (proj2 (prepared_plans I J start a0 e w m HP HE row plan Hin)) as [He Hw].
      cbn [fst snd]; rewrite Map.set_cost; fold (key_bits (IdeValue.row_enc I) row); lia.
    - fold plans in Hlength.
      assert (Hscale :
        (N.of_nat (length plans) * (1 + (1 + row_charge e w + row_width w)) <=
          rows I * (1 + (1 + row_charge e w + row_width w)))%N).
      { apply N.mul_le_mono_r; exact Hlength. }
      nia. }
  unfold IdeValue.analysis_c; rewrite !Cost.ticks_bind.
  change (Cost.value (IdeValue.prepare_c I (Jump.lookup_c I J) start a0)) with plans.
  rewrite TabPrepareCost.pure_map_cost, Cost.ticks_ret.
  fold plans in Hlength; unfold analysis_charge; lia.
Qed.

End Preparation.

Local Lemma sum_on {X} (f : X -> BinNums.N) xs k :
  (forall x, In x xs -> (f x <= k)%N) ->
  (fold_right (fun x n => f x + n) 0%N xs <= N.of_nat (length xs) * k)%N.
Proof.
  induction xs as [|x xs IH]; intro Hbound; cbn [fold_right length].
  - lia.
  - rewrite Nat2N.inj_succ; specialize (IH (fun y Hy => Hbound y (or_intror Hy))).
    specialize (Hbound x (or_introl eq_refl)); nia.
Qed.

(** Fixed-read system checking derives evaluation charges from actual plans and primitive reads. *)
Theorem system_cost {N E P D A F C} (I : Ide.t N E P D A F) start e w m
    (cs : list C) (get : C -> Cost.t (Rows.t (N * option D) A))
    (look : (N * option D) -> Cost.t A) :
  (forall c, In c cs ->
    (Cost.ticks (get c) <= row_probe e w)%N /\ plan_bound I start m (Cost.value (get c))) ->
  (forall v, TabValueRunCost.coordinate I start v ->
    (Cost.ticks (look v) <= TabValueRunCost.probe e w)%N) ->
  (forall a b, (Cost.ticks (leb_c (Ide.values I) a b) <= m)%N) ->
  (Cost.ticks (check_post_c (Ide.values I) (Rows.system cs get) look) <=
    N.of_nat (length cs) * (1 + constraint_charge e w m))%N.
Proof.
  intros Hget Hlook Hcompare; apply check_post_cost.
  unfold check_budget.
  change (fold_right (fun c total =>
    (1 + Cost.ticks (Eval.outputs_c (Rows.system cs get) look c) +
      fold_right (fun xa subtotal => 3 + Cost.ticks (look (fst xa)) +
        Cost.ticks (leb_c (Ide.values I) (snd xa) (Cost.value (look (fst xa)))) + subtotal)
      0 (fst (Cost.value (Eval.outputs_c (Rows.system cs get) look c))) + total)%N) 0 cs <=
    N.of_nat (length cs) * (1 + constraint_charge e w m))%N.
  apply sum_on; intros c Hc; destruct (Hget c Hc) as [Hgetcost Hplan].
  set (plan := Cost.value (get c)) in *.
  set (sigma := fun v => Cost.value (look v)).
  assert (Htarget : (Cost.ticks (System.target_c (Rows.system cs get) c) <=
    1 + row_probe e w)%N).
  { change (Cost.ticks (Cost.step ;; Cost.map Rows.target (get c)) <=
      1 + row_probe e w)%N.
    rewrite Cost.ticks_bind, Cost.ticks_step, Cost.ticks_map; lia. }
  assert (Hrhs : (Cost.ticks (System.rhs_c (Rows.system cs get) c) <=
    1 + row_probe e w + (3 + m))%N).
  { change (Cost.ticks (Cost.step ;; let* p := get c in Rows.query_c p) <=
      1 + row_probe e w + (3 + m))%N.
    rewrite !Cost.ticks_bind, Cost.ticks_step.
    pose proof (query_build_cost I start m plan Hplan).
    fold plan; lia. }
  assert (Hquery : (Cost.ticks (Query.run_c look (Rows.query plan)) <=
    2 * (3 + TabValueRunCost.probe e w + (3 + m)))%N).
  { apply Query.run_c_cost_on with (s := sigma) (nu := 2%nat) (tau := (3 + m)%N).
    - exact (query_within I start m plan sigma Hplan).
    - reflexivity.
    - intros v Hv; rewrite (proj1 (Rows.query_spec plan sigma)) in Hv.
      apply Hlook, (reads_supported Hplan); exact Hv. }
  assert (Houtputs :
    fst (Cost.value (Eval.outputs_c (Rows.system cs get) look c)) =
      [(Rows.target plan, Cost.value (Rows.eval_c plan (map sigma (Rows.reads plan))))]).
  { rewrite (Eval.outputs_c_spec _ _ look sigma) by reflexivity.
    rewrite Eval.outputs_spec.
    change ((Rows.target plan, Query.eval (Rows.query plan) sigma) ::
      Query.sides (Rows.query plan) sigma =
      [(Rows.target plan, Cost.value (Rows.eval_c plan (map sigma (Rows.reads plan))))]).
    destruct (Rows.query_spec plan sigma) as [Hreads [Heval Hsides]].
    rewrite Heval, Hsides; reflexivity. }
  rewrite Houtputs; cbn [fold_right fst snd].
  pose proof (Hlook (Rows.target plan) (target_supported Hplan)) as Htargetlook.
  pose proof (Hcompare
    (Cost.value (Rows.eval_c plan (map sigma (Rows.reads plan))))
    (Cost.value (look (Rows.target plan)))) as Horder.
  rewrite Eval.outputs_cost.
  change (System.rhs (Rows.system cs get) c) with (Rows.query plan).
  unfold constraint_charge; nia.
Qed.

(** Actual candidate certification discharges plan, table, row and query bounds from primitives. *)
Theorem certify_cost {N E P D A F} (I : Ide.t N E P D A F) J start a0 e w m s
    ko ks kt kk kf kw q :
  TabValueRunCost.primitives I start e w m ->
  (forall a, In a (Jump.arcs I) ->
    TabEncodingCost.bounded (Cfg.edge_enc (Icfg.cfg (Ifds.icfg (Ide.ifds I))))
      (Jump.edge a) e w) ->
  TabPrepareCost.callbacks I ko ks kt kk kf kw q ->
  (Cost.ticks (TabValues.certify_c I J start a0 s) <=
    checker_charge I ko ks kt kk kf kw q e w m)%N.
Proof.
  intros HP HE HC.
  pose proof (analysis_cost I J start a0 e w m HP HE ko ks kt kk kf kw q HC) as Hanalysis.
  destruct (prepare_cost I J start a0 e w m HP ko ks kt kk kf kw q HC)
    as [Hprepare Hlength].
  set (plans := Cost.value (IdeValue.prepare_c I (Jump.lookup_c I J) start a0)).
  set (fallback := Rows.Make start [] (fun _ => Cost.ret (bot (Ide.values I)))).
  set (get := fun row => Map.find_or_c (IdeValue.row_enc I) fallback row
    (Map.of_list (IdeValue.row_enc I) plans)).
  assert (Hplans : forall row plan, In (row, plan) plans ->
    plan_bound I start m plan /\
      TabEncodingCost.bounded (IdeValue.row_enc I) row (row_charge e w) (row_width w)).
  { intros row plan Hin; exact (prepared_plans I J start a0 e w m HP HE row plan Hin). }
  assert (Hget : forall row, In row (map fst plans) ->
    (Cost.ticks (get row) <= row_probe e w)%N /\ plan_bound I start m (Cost.value (get row))).
  { intros row Hrow; apply in_map_iff in Hrow.
    destruct Hrow as [[key plan] [Hkey Hin]]; cbn [fst] in Hkey; subst key.
    destruct (Hplans row plan Hin) as [Hplan [Henc Hbits]]; split.
    - unfold get; rewrite Map.find_or_cost, Map.get_cost.
      fold (key_bits (IdeValue.row_enc I) row); unfold row_probe; lia.
    - change (plan_bound I start m (Map.find_or (IdeValue.row_enc I) fallback row
        (Map.of_list (IdeValue.row_enc I) plans))).
      apply of_list_payload.
      + unfold fallback; constructor.
        * left; reflexivity.
        * intros v Hv; inversion Hv.
        * cbn [Rows.reads length]; lia.
        * intro values; cbn [Rows.eval_c]; rewrite Cost.ticks_ret; lia.
      + intros [r p] Hentry; exact (proj1 (Hplans r p Hentry)). }
  assert (Hlookup : forall v, TabValueRunCost.coordinate I start v ->
    (Cost.ticks (TabValues.lookup_c I (TabValues.values s) v) <=
      TabValueRunCost.probe e w)%N).
  { intros v Hv.
    destruct (TabValueRunCost.vertex_budget I start e w m HP v Hv) as [Henc Hbits].
    unfold TabValues.lookup_c; rewrite Map.find_or_cost, Map.get_cost.
    fold (key_bits (IdeValue.key_enc I) v); unfold TabValueRunCost.probe; lia. }
  pose proof (system_cost I start e w m (map fst plans) get
    (TabValues.lookup_c I (TabValues.values s)) Hget Hlookup
    (TabValueRunCost.compare HP)) as Hcheck.
  assert (Hsystem : Analysis.system (value_analysis I (Jump.lookup_c I J) start a0) =
    Rows.system (map fst plans) get).
  { unfold value_analysis, IdeValue.analysis_c; autorewrite with galois_cost.
    fold plans; change (Cost.value (Map.of_list_c (IdeValue.row_enc I) plans))
      with (Map.of_list (IdeValue.row_enc I) plans).
    reflexivity. }
  rewrite length_map in Hcheck.
  assert (Hscale :
    (N.of_nat (length plans) * (1 + constraint_charge e w m) <=
      rows I * (1 + constraint_charge e w m))%N).
  { apply N.mul_le_mono_r; exact Hlength. }
  rewrite TabValues.certify_cost_equation, Hsystem.
  unfold checker_charge; lia.
Qed.

(** The raw value wrapper pays the derived checker bound on each actually stopped candidate. *)
Theorem tabulate_cost {N E P D A F} (I : Ide.t N E P D A F) J start a0 fuel e w m
    ko ks kt kk kf kw q :
  TabValueRunCost.primitives I start e w m -> encoding_laws (IdeValue.key_enc I) ->
  (forall a, In a (Jump.arcs I) ->
    TabEncodingCost.bounded (Cfg.edge_enc (Icfg.cfg (Ifds.icfg (Ide.ifds I))))
      (Jump.edge a) e w) ->
  TabPrepareCost.callbacks I ko ks kt kk kf kw q ->
  (Cost.ticks (TabValues.tabulate_values_c I J start a0 fuel) <=
    TabValueRunCost.prepare_charge I ko ks kt kk kf kw q e w +
    TabValueRunCost.initial_charge I e w m +
    (TabValueRunCost.step_charge I e w m + 2) * N.pos fuel +
    checker_charge I ko ks kt kk kf kw q e w m)%N.
Proof.
  intros HP HV HE HC.
  pose proof (TabValueRunCost.raw_cost I J start e w m HP HV a0 fuel
    ko ks kt kk kf kw q HC) as Hraw.
  unfold TabValues.tabulate_values_c; rewrite Cost.ticks_bind.
  change (Cost.value (TabValues.raw_c I J start a0 fuel)) with (TabValues.raw I J start a0 fuel).
  destruct (TabValues.raw I J start a0 fuel) as [exhausted|stopped].
  - rewrite Cost.ticks_ret; lia.
  - pose proof (certify_cost I J start a0 e w m stopped ko ks kt kk kf kw q HP HE HC); lia.
Qed.

(** Constructed value certification includes separate height fuel, actual row plans and query costs. *)
Theorem complete_cost {N E P D A F} (I : Ide.t N E P D A F) J start a0 e w m
    ko ks kt kk kf kw q (H : height (Ide.values I)) :
  TabValueRunCost.primitives I start e w m -> encoding_laws (IdeValue.key_enc I) ->
  (forall a, In a (Jump.arcs I) ->
    TabEncodingCost.bounded (Cfg.edge_enc (Icfg.cfg (Ifds.icfg (Ide.ifds I))))
      (Jump.edge a) e w) ->
  TabPrepareCost.callbacks I ko ks kt kk kf kw q ->
  (Cost.ticks (TabValueProgress.complete_c I J start a0 H) <=
    TabValueRunCost.complete_charge I ko ks kt kk kf kw q e w m (N.of_nat (bound H)) +
    checker_charge I ko ks kt kk kf kw q e w m)%N.
Proof.
  intros HP HV HE HC.
  pose proof (TabValueRunCost.complete_raw_cost I J start a0 e w m
    ko ks kt kk kf kw q H HP HV HC) as Hraw.
  rewrite TabValueProgress.complete_cost_equation.
  destruct (TabValueProgress.complete_raw I J start a0 H) as [exhausted|stopped]; [lia|].
  pose proof (certify_cost I J start a0 e w m stopped ko ks kt kk kf kw q HP HE HC); lia.
Qed.

(** Certified value families have a primitive-derived big-O bound with a separate value height. *)
Theorem tabulate_bigO {X N E P D A F}
    (I : X -> Ide.t N E P D A F) (J : X -> Map.t positive F)
    (start : X -> N * option D) (a0 : X -> A)
    (e w m ko ks kt kk kf kw q : X -> BinNums.N)
    (H : forall x, height (Ide.values (I x))) :
  (forall x, TabValueRunCost.primitives (I x) (start x) (e x) (w x) (m x)) ->
  (forall x, encoding_laws (IdeValue.key_enc (I x))) ->
  (forall x a, In a (Jump.arcs (I x)) ->
    TabEncodingCost.bounded (Cfg.edge_enc (Icfg.cfg (Ifds.icfg (Ide.ifds (I x)))))
      (Jump.edge a) (e x) (w x)) ->
  (forall x, TabPrepareCost.callbacks (I x) (ko x) (ks x) (kt x) (kk x) (kf x) (kw x) (q x)) ->
  bigO
    (fun x => (TabValueRunCost.complete_charge (I x) (ko x) (ks x) (kt x) (kk x)
      (kf x) (kw x) (q x) (e x) (w x) (m x) (N.of_nat (bound (H x))) +
      checker_charge (I x) (ko x) (ks x) (kt x) (kk x) (kf x) (kw x) (q x)
        (e x) (w x) (m x))%N)
    (fun x => Cost.ticks (TabValueProgress.complete_c (I x) (J x) (start x) (a0 x) (H x))).
Proof.
  intros HP HV HE HC; exists 1%N; intro x.
  pose proof (complete_cost (I x) (J x) (start x) (a0 x) (e x) (w x) (m x)
    (ko x) (ks x) (kt x) (kk x) (kf x) (kw x) (q x) (H x)
    (HP x) (HV x) (HE x) (HC x)); lia.
Qed.

End TabValueCheckCost.
