(** * Summary scheduling and joining leastness

    The conservative SCC policy cuts cycles and joining least solutions agree across policies.
    For example, both members of a recursive pair are widening points in the reference policy.
    Builds on: FrameworkSummaryClosure, GraphSccSpec and FixpointAnalyze. *)

From Stdlib Require Import List Bool Arith PArith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Lattice Require Import LatticeCore.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor GraphSearchSpec GraphSccSpec
  GraphReach.
From Galois.Program Require Import ProgramCalls.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointLeast FixpointAnalysis
  FixpointSolver FixpointAnalyze.
From Galois.Framework Require Import FrameworkUtil FrameworkSummary FrameworkSummarySound
  FrameworkSummaryClosure.
Import List.ListNotations Cost.Notations.

Module SummarySched.

Local Lemma policy_rows {F P} (C : Calls.t F P) m :
  Cost.value (map_c (fun f =>
    let* reach := Summary.reach_get_c (Calls.fn_enc C) f m in
    let* count := FinSet.size_c reach in
    Cost.ret (f, (Pos.of_succ_nat count, true))) (Calls.functions C)) =
  map (fun f => (f, (Pos.of_succ_nat (FinSet.size (SummaryClosure.row C m f)), true)))
    (Calls.functions C).
Proof.
  rewrite value_map_c; apply map_ext; intro f; autorewrite with galois_cost; reflexivity.
Qed.

(** Listed functions retain their reachable-set-size order and are all widening points. *)
Theorem policy_scc_listed {F P} (C : Calls.t F P) f :
  encoding_laws (Calls.fn_enc C) -> In f (Calls.functions C) ->
  Policy.widen_at (summary_policy_scc C) f = true /\
  Policy.order (summary_policy_scc C) f =
    Pos.of_succ_nat (FinSet.size (SummaryClosure.row C (Cost.value (Summary.closure_c C)) f)).
Proof.
  intros HE Hf.
  unfold summary_policy_scc, Summary.policy_scc; rewrite !policy_rows.
  autorewrite with galois_cost.
  set (rank := fun f => Pos.of_succ_nat
    (FinSet.size (SummaryClosure.row C (Cost.value (Summary.closure_c C)) f))).
  set (table := Map.of_list (Calls.fn_enc C)
    (map (fun g => (g, (rank g, true))) (Calls.functions C))).
  assert (Hget : Map.get (Calls.fn_enc C) f table = Some (rank f, true)).
  { exact (SummarySound.table_lookup (Calls.fn_enc C) HE
      (fun g => (rank g, true)) (Calls.functions C) f Hf). }
  split.
  - change ((match Map.get (Calls.fn_enc C) f table
      with Some pr => snd pr | None => false end) = true).
    rewrite Hget; reflexivity.
  - change (Cost.value (match Map.get (Calls.fn_enc C) f table with
      | Some pr => Cost.ret (fst pr)
      | None => Cost.step ;; encode_c (Calls.fn_enc C) f
      end) = rank f).
    rewrite Hget; reflexivity.
Qed.

(** Unknown keys are not widening points when function encodings are injective. *)
Theorem policy_scc_unknown {F P} (C : Calls.t F P) f :
  encoding_laws (Calls.fn_enc C) -> ~ In f (Calls.functions C) ->
  Policy.widen_at (summary_policy_scc C) f = false.
Proof.
  intros HE Hnot.
  unfold summary_policy_scc, Summary.policy_scc; rewrite !policy_rows.
  autorewrite with galois_cost.
  set (rank := fun f => Pos.of_succ_nat
    (FinSet.size (SummaryClosure.row C (Cost.value (Summary.closure_c C)) f))).
  change ((match Map.get (Calls.fn_enc C) f
    (Map.of_list (Calls.fn_enc C) (map (fun g => (g, (rank g, true))) (Calls.functions C)))
    with Some pr => snd pr | None => false end) = false).
  rewrite (SummarySound.table_absent _ HE) by exact Hnot; reflexivity.
Qed.

(** Every listed cycle meets the current conservative policy at its own starting function. *)
Theorem policy_scc_cuts {F P} (C : Calls.t F P) :
  encoding_laws (Calls.fn_enc C) ->
  cycles_cut (Calls.graph C) (fun f => Policy.widen_at (summary_policy_scc C) f = true).
Proof.
  intros HE f es Hf Hpath Hnonempty; left.
  exact (proj1 (policy_scc_listed C f HE Hf)).
Qed.

(** Strict graph reachability orders a callee before a caller with no return path. *)
Theorem policy_scc_reach_order {F P} (C : Calls.t F P) f g :
  encoding_laws (Calls.fn_enc C) -> graph_wf (Calls.graph C) ->
  In f (Calls.functions C) -> In g (Calls.functions C) ->
  reaches (Calls.graph C) f g -> ~ reaches (Calls.graph C) g f ->
  (Policy.order (summary_policy_scc C) g < Policy.order (summary_policy_scc C) f)%positive.
Proof.
  intros HE Hwf Hf Hg Hfg Hnot.
  rewrite (proj2 (policy_scc_listed C f HE Hf)), (proj2 (policy_scc_listed C g HE Hg)).
  apply Pos2Nat.inj_lt; rewrite !SuccNat2Pos.id_succ.
  pose proof (SummaryClosure.closure_size_order C f g HE Hwf Hf Hg Hfg Hnot); lia.
Qed.

Local Lemma scoped_path_lift {V E} (p : Prepared.t V E) f es g :
  Prepared.laws p -> graph_wf (Prepared.graph p) ->
  path (Prepared.graph p) f es g ->
  forall u v, In f (Graph.nodes (Prepared.graph p)) ->
    Prepared.id_of p f = Some u -> Prepared.id_of p g = Some v ->
    Search.scoped_path p Reach.unrestricted u es v.
Proof.
  intros Hp Hwf Hpath.
  induction Hpath as [f|e es g He Hpath IH]; intros u v Hf Hu Hv.
  - assert (u = v) by congruence; subst v; constructor.
    + exists f; auto.
    + apply Reach.admits_unrestricted.
  - pose proof (out_target_in Hwf _ _ Hf He) as Htarget.
    destruct (proj1 (Prepared.ids_domain p Hp _) Htarget) as [w Hw].
    eapply Search.scoped_cons with (v := w).
    + exists (Graph.source (Prepared.graph p) e); auto.
    + apply Reach.admits_unrestricted.
    + exists (Graph.source (Prepared.graph p) e), (Graph.target (Prepared.graph p) e).
      repeat split; try reflexivity; assumption.
    + apply IH; assumption.
Qed.

Local Lemma different_scc_no_return {V E} (p : Prepared.t V E) roots r f g u v i j :
  Prepared.laws p -> graph_wf (Prepared.graph p) ->
  Scc.exact p Reach.unrestricted roots r ->
  In f (Graph.nodes (Prepared.graph p)) -> In g (Graph.nodes (Prepared.graph p)) ->
  Prepared.id_of p f = Some u -> Prepared.id_of p g = Some v ->
  Map.get positive_encoding u (Scc.comp_of r) = Some i ->
  Map.get positive_encoding v (Scc.comp_of r) = Some j ->
  i <> j -> reaches (Prepared.graph p) f g -> ~ reaches (Prepared.graph p) g f.
Proof.
  intros Hp Hwf Hscc Hf Hg Hu Hv Hownerf Hownerg Hneq [es Hfg] [gs Hgf].
  destruct (proj1 (Scc.owners_exact p Reach.unrestricted roots r Hscc u i) Hownerf)
    as [ci [Hci Huci]].
  destruct (proj1 (Scc.owners_exact p Reach.unrestricted roots r Hscc v j) Hownerg)
    as [cj [Hcj Hvcj]].
  pose proof (Scc.components_exact p Reach.unrestricted roots r Hscc) as Hblocks.
  rewrite Forall_forall in Hblocks.
  destruct (Hblocks ci (nth_error_In _ _ Hci)) as [_ [_ [_ Hmaximal]]].
  assert (Hreachable : Search.scoped_reachable p Reach.unrestricted roots v).
  { apply (proj1 (Scc.partition_complete p Reach.unrestricted roots r Hscc v)).
    apply in_concat; exists cj; split; [eapply nth_error_In; exact Hcj|exact Hvcj]. }
  assert (Hvci : In v ci).
  { apply (proj2 (Hmaximal u v Huci)); split; [exact Hreachable|split].
    - exists es; exact (scoped_path_lift p f es g Hp Hwf Hfg u v Hf Hu Hv).
    - exists gs; exact (scoped_path_lift p g gs f Hp Hwf Hgf v u Hg Hv Hu). }
  pose proof (proj2 (Scc.owners_exact p Reach.unrestricted roots r Hscc v i)
    (ex_intro _ ci (conj Hci Hvci))) as Howner.
  rewrite Hownerg in Howner; apply Hneq; congruence.
Qed.

(** Supplied exact SCC owners put a cross-component callee strictly before its caller.
    Prepared graph and endpoint identities refer to the same supplied witnesses. *)
Theorem policy_scc_order {F P} (C : Calls.t F P)
    (p : Prepared.t F (call_edge F P)) roots r f e g u v i j :
  encoding_laws (Calls.fn_enc C) -> graph_wf (Calls.graph C) ->
  Prepared.laws p -> Prepared.graph p = Calls.graph C ->
  Scc.exact p Reach.unrestricted roots r ->
  In f (Calls.functions C) -> In e (Graph.out (Calls.graph C) f) ->
  Graph.target (Calls.graph C) e = g ->
  Prepared.id_of p f = Some u -> Prepared.id_of p g = Some v ->
  Map.get positive_encoding u (Scc.comp_of r) = Some i ->
  Map.get positive_encoding v (Scc.comp_of r) = Some j -> i <> j ->
  (Policy.order (summary_policy_scc C) g < Policy.order (summary_policy_scc C) f)%positive.
Proof.
  intros HE Hwf Hp Hgraph Hscc Hf He Htarget Hu Hv Hownerf Hownerg Hneq.
  assert (Hg : In g (Calls.functions C)).
  { rewrite <- Htarget; exact (out_target_in Hwf f e Hf He). }
  assert (Hfg : reaches (Calls.graph C) f g).
  { exists [e]; rewrite <- (out_source Hwf f e He).
    constructor; [rewrite (out_source Hwf f e He); exact He|rewrite Htarget; constructor]. }
  apply policy_scc_reach_order; [exact HE|exact Hwf|exact Hf|exact Hg|exact Hfg|].
  rewrite <- Hgraph.
  apply (different_scc_no_return p roots r f g u v i j Hp).
  - rewrite Hgraph; exact Hwf.
  - exact Hscc.
  - rewrite Hgraph; exact Hf.
  - rewrite Hgraph; exact Hg.
  - exact Hu.
  - exact Hv.
  - exact Hownerf.
  - exact Hownerg.
  - exact Hneq.
  - rewrite Hgraph; exact Hfg.
Qed.

(** Replacing the policy leaves the generated equations, lattice and dictionaries unchanged. *)
Definition using_policy {X R A} (a : Analysis.t X R A) (pol : Policy.t X) :=
  Analysis.Make (Analysis.key_enc a) (Analysis.row_enc a) (Analysis.lat a)
    (Analysis.system a) (Analysis.static a) pol.

(** Computational policy replacement preserves analysis laws. *)
Theorem using_policy_laws {X R A} (a : Analysis.t X R A) pol :
  Analysis.laws a -> Analysis.laws (using_policy a pol).
Proof.
  intros [HE HR HL HS]; constructor; assumption.
Qed.

(** Monotone call lifting gives a monotone generated summary system. *)
Theorem monotone {F P A} (C : Calls.t F P) (sp : Summary.spec F P A) :
  encoding_laws (Calls.fn_enc C) -> encoding_laws (Calls.site_enc C) ->
  lattice_laws (Summary.lat sp) ->
  (forall p g, monotone_fun (Summary.lat sp) (Summary.lat sp) (Summary.via_call sp p g)) ->
  monotone_system (Summary.lat sp) (Analysis.system (summary_analysis C sp)).
Proof.
  intros HF HP HL Hvia r Hr.
  assert (Hrows : System.constraints (Analysis.system (summary_analysis C sp)) =
    Cost.value (Summary.rows_c C)).
  { unfold summary_analysis, Summary.analysis, Summary.prepare_c;
      autorewrite with galois_cost; reflexivity. }
  rewrite Hrows in Hr.
  split.
  - intros sigma tau Hbelow.
    destruct (SummarySound.row_spec C sp r sigma HF HP Hr) as [_ [_ [Hs _]]].
    destruct (SummarySound.row_spec C sp r tau HF HP Hr) as [_ [_ [Ht _]]].
    rewrite Hs, Ht; destruct r as [f|p g].
    + apply (leb_refl HL).
    + apply Hvia, Hbelow.
  - intros sigma tau Hbelow x a Hin.
    rewrite (proj2 (proj2 (proj2 (SummarySound.row_spec C sp r sigma HF HP Hr)))) in Hin.
    contradiction.
Qed.

(** Solved joining policies without narrowing agree under least joins and monotone lifting.
    This theorem uses the published generic leastness interface and does not unfold analyze. *)
Theorem policy_independent {F P A} (C : Calls.t F P) (sp : Summary.spec F P A)
    pol1 pol2 fuel1 fuel2 s1 s2 :
  encoding_laws (Calls.fn_enc C) -> encoding_laws (Calls.site_enc C) ->
  lattice_laws (Summary.lat sp) -> lub_laws (Summary.lat sp) ->
  (forall p g, monotone_fun (Summary.lat sp) (Summary.lat sp) (Summary.via_call sp p g)) ->
  (forall f, Policy.widen_at pol1 f = false) ->
  (forall f, Policy.widen_at pol2 f = false) ->
  Policy.narrowing pol1 = 0 -> Policy.narrowing pol2 = 0 ->
  analyze (using_policy (summary_analysis C sp) pol1) fuel1 = Outcome.Solved s1 ->
  analyze (using_policy (summary_analysis C sp) pol2) fuel2 = Outcome.Solved s2 ->
  forall f, equivalent (Summary.lat sp) (proj1_sig s1 f) (proj1_sig s2 f).
Proof.
  intros HF HP HL Hlub Hvia Hjoin1 Hjoin2 Hnarrow1 Hnarrow2 Hsolved1 Hsolved2.
  pose proof (Summary.analysis_laws C sp HF HP HL) as Ha.
  pose proof (monotone C sp HF HP HL Hvia) as Hmono.
  pose proof (analyze_least _ fuel1 s1 (using_policy_laws _ pol1 Ha)
    Hlub Hmono Hjoin1 Hnarrow1 Hsolved1) as Hleast1.
  pose proof (analyze_least _ fuel2 s2 (using_policy_laws _ pol2 Ha)
    Hlub Hmono Hjoin2 Hnarrow2 Hsolved2) as Hleast2.
  destruct (least_solution_unique _ _ _ _ Hleast1 Hleast2) as [H12 H21].
  intro f; split; [apply H12|apply H21].
Qed.

(** Accepted context lookup and monotone lifting give a monotone contextual system. *)
Theorem ctx_monotone {F P K A} (C : Calls.t F P) (cx : Ctx.t F P K)
    (sp : Summary.spec F P A) :
  encoding_laws (Calls.fn_enc C) -> encoding_laws (Calls.site_enc C) ->
  encoding_laws (Ctx.ctx_enc cx) -> lattice_laws (Summary.lat sp) ->
  (forall p g, monotone_fun (Summary.lat sp) (Summary.lat sp) (Summary.via_call sp p g)) ->
  monotone_system (Summary.lat sp) (Analysis.system (ctx_summary_analysis C cx sp)).
Proof.
  intros HF HP HK HL Hvia rk Hr.
  assert (Hrows : System.constraints (Analysis.system (ctx_summary_analysis C cx sp)) =
    SummarySound.ctx_rows C cx).
  { unfold ctx_summary_analysis, Summary.ctx_analysis.
    change (Cost.value (fw_flat_map_c (fun k =>
      map_c (fun r => Cost.ret (r, k)) (Cost.value (Summary.rows_c C)))
      (Ctx.contexts cx)) = SummarySound.ctx_rows C cx).
    rewrite fw_flat_map_value; unfold SummarySound.ctx_rows.
    apply flat_map_ext; intro k; rewrite value_map_c; reflexivity. }
  rewrite Hrows in Hr; split.
  - intros sigma tau Hbelow.
    destruct (SummarySound.ctx_row_spec C cx sp rk sigma HF HP HK Hr) as [_ [_ [Hs _]]].
    destruct (SummarySound.ctx_row_spec C cx sp rk tau HF HP HK Hr) as [_ [_ [Ht _]]].
    rewrite Hs, Ht; destruct rk as [[f|p g] k].
    + apply (leb_refl HL).
    + unfold Summary.ctx_get_c; autorewrite with galois_cost.
      fold (Ctx.enter cx p g k); destruct (Ctx.enter cx p g k).
      * apply Hvia, Hbelow.
      * apply (leb_refl HL).
  - intros sigma tau Hbelow x a Hin.
    rewrite (proj2 (proj2 (proj2
      (SummarySound.ctx_row_spec C cx sp rk sigma HF HP HK Hr)))) in Hin.
    contradiction.
Qed.

(** Solved insensitive and ordinary analyses agree up to preorder equivalence at each function. *)
Theorem ctx_insensitive_results_agree {F P A} (C : Calls.t F P)
    (sp : Summary.spec F P A) fuel1 fuel2 s1 s2 :
  encoding_laws (Calls.fn_enc C) -> encoding_laws (Calls.site_enc C) ->
  lattice_laws (Summary.lat sp) -> lub_laws (Summary.lat sp) ->
  (forall p g, monotone_fun (Summary.lat sp) (Summary.lat sp) (Summary.via_call sp p g)) ->
  analyze (ctx_summary_analysis C (Ctx.insensitive F P) sp) fuel1 = Outcome.Solved s1 ->
  analyze (summary_analysis C sp) fuel2 = Outcome.Solved s2 ->
  forall f, equivalent (Summary.lat sp) (proj1_sig s1 (f, tt)) (proj1_sig s2 f).
Proof.
  intros HF HP HL Hlub Hvia Hsolved1 Hsolved2.
  pose proof (Summary.ctx_analysis_laws C (Ctx.insensitive F P) sp
    HF HP unit_encoding_laws HL) as Hctxlaws.
  pose proof (Summary.analysis_laws C sp HF HP HL) as Hsumlaws.
  assert (Hctxjoin : Analysis.joining (ctx_summary_analysis C (Ctx.insensitive F P) sp)).
  { intros [f []]; reflexivity. }
  assert (Hsumjoin : Analysis.joining (summary_analysis C sp)).
  { intro f; unfold summary_analysis, Summary.analysis.
    destruct (Cost.value (Summary.prepare_c C sp)); reflexivity. }
  assert (Hctxnarrow : Policy.narrowing
    (Analysis.policy (ctx_summary_analysis C (Ctx.insensitive F P) sp)) = 0).
  { reflexivity. }
  assert (Hsumnarrow : Policy.narrowing (Analysis.policy (summary_analysis C sp)) = 0).
  { unfold summary_analysis, Summary.analysis.
    destruct (Cost.value (Summary.prepare_c C sp)); reflexivity. }
  apply (SummarySound.ctx_insensitive_least_agrees C sp _ _ HF HP HL).
  - exact (analyze_least _ fuel1 s1 Hctxlaws Hlub
      (ctx_monotone C (Ctx.insensitive F P) sp HF HP unit_encoding_laws HL Hvia)
      Hctxjoin Hctxnarrow Hsolved1).
  - exact (analyze_least _ fuel2 s2 Hsumlaws Hlub (monotone C sp HF HP HL Hvia)
      Hsumjoin Hsumnarrow Hsolved2).
Qed.

End SummarySched.
