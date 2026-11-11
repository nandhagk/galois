(** * Tabulation invariants

    Intermediate jump values stay below every solution of the ground jump rows.
    For example, a matched return composes two existing bounds before joining its output.
    Builds on: FrameworkTabulate and the public map and jump-row contracts. *)

From Stdlib Require Import List Bool NArith.
From Galois.Cost Require Import CostMonad CostList CostLoop.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseIndex BaseSet.
From Galois.Lattice Require Import LatticeCore LatticeSimple.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramCfg ProgramIcfg.
From Galois.Fixpoint Require Import FixpointSystem FixpointAnalysis.
From Galois.Framework Require Import FrameworkMicro FrameworkIfds FrameworkIde FrameworkStack
  FrameworkTabulate FrameworkTabPaths FrameworkTabWeight FrameworkTabJumpPaths FrameworkTabValues
  FrameworkTabValueSound.
Import List.ListNotations.

Module TabSound.

(** Every readable map value satisfies its payload invariant. *)
Definition map_all {K V} (E : encoding K) (P : V -> Prop) (m : Map.t K V) :=
  Map.wf E m /\ forall k v, Map.get E k m = Some v -> P v.

Local Lemma map_all_empty {K V} (E : encoding K) (P : V -> Prop) :
  map_all E P Map.empty.
Proof.
  split; [apply Map.wf_empty|].
  intros k v Hget; rewrite Map.get_empty in Hget; discriminate.
Qed.

Local Lemma map_all_set {K V} (E : encoding K) (P : V -> Prop) m k v :
  map_all E P m -> P v -> map_all E P (Map.set E k v m).
Proof.
  intros [Hwf Hall] Hv; split; [apply Map.wf_set; exact Hwf|].
  intros q w Hget; rewrite Map.get_set in Hget by exact Hwf.
  destruct (eqb E q k).
  - injection Hget as Heq; subst w; exact Hv.
  - eapply Hall; exact Hget.
Qed.

Local Lemma map_all_bucket {K V} (E : encoding K) (P : V -> Prop) m k default :
  map_all E P m -> P default -> P (Map.find_or E default k m).
Proof.
  intros [_ Hall] Hd; rewrite Map.find_or_equation.
  destruct (Map.get E k m) as [v|] eqn:Hget; [eapply Hall; exact Hget|exact Hd].
Qed.

Local Lemma map_all_elements {K V} (E : encoding K) (HE : encoding_laws E)
    (P : V -> Prop) m k v :
  map_all E P m -> In (k, v) (Map.elements m) -> P v.
Proof.
  intros [Hwf Hall] Hin; apply Hall with (k := k).
  apply (proj1 (Map.elements_spec E HE k v m Hwf)); exact Hin.
Qed.

Definition roots {N E P D A F} (I : Ide.t N E P D A F) start :=
  TabPaths.roots I start.

(** Caller records retain actual roots and actual exploded call occurrences. *)
Definition caller_valid {N E P D A F} (I : Ide.t N E P D A F) start
    (c : Tab.incoming N E P D F) :=
  In (fst c) (roots I start) /\ In (snd c) (Jump.arcs I) /\
    exists p, Jump.kind (snd c) = Icfg.Call p.

(** End records retain actual exploded return occurrences. *)
Definition end_valid {N E P D A F} (I : Ide.t N E P D A F)
    (a : Jump.arc N E P D F) :=
  In a (Jump.arcs I) /\ exists p, Jump.kind a = Icfg.Return p.

(** Record provenance is independent of the symbolic values held by the jump map. *)
Definition records_valid {N E P D A F} (I : Ide.t N E P D A F) start
    (s : Tab.state N E P D F) :=
  map_all (IdeValue.key_enc I)
    (map_all positive_encoding (caller_valid I start)) (Tab.callers s) /\
  map_all (IdeValue.key_enc I)
    (map_all positive_encoding (end_valid I)) (Tab.ends s).

(** A candidate map is pointwise below a comparison solution in function order. *)
Definition bounded {N E P D A F} (I : Ide.t N E P D A F)
    (J : jkey N D -> F) (s : Tab.state N E P D F) :=
  Map.wf positive_encoding (Tab.jumps s) /\
  forall k, leb (Micro.lat (Ide.micro I)) (Jump.lookup I (Tab.jumps s) k) (J k) = true.

(** Scheduling cannot change a jump value or its comparison bound. *)
Theorem schedule_bounded {N E P D A F} (I : Ide.t N E P D A F) J k s :
  bounded I J s -> bounded I J (Tab.schedule I k s).
Proof.
  intro Hbound; rewrite Tab.schedule_equation.
  destruct (FinSet.mem (Jump.enc I) k (Tab.pending s)); exact Hbound.
Qed.

(** A justified contribution keeps the candidate below every comparison solution. *)
Theorem update_bounded {N E P D A F} (I : Ide.t N E P D A F) J k f s :
  encoding_laws (Jump.enc I) ->
  lattice_laws (Micro.lat (Ide.micro I)) ->
  lub_laws (Micro.lat (Ide.micro I)) ->
  bounded I J s ->
  leb (Micro.lat (Ide.micro I)) f (J k) = true ->
  bounded I J (Tab.update I k f s).
Proof.
  intros HE HL Hlub [Hwf Hbound] Hf; rewrite Tab.update_equation.
  destruct (leb (Micro.lat (Ide.micro I)) f (Jump.lookup I (Tab.jumps s) k)).
  - split; assumption.
  - apply schedule_bounded; split; [apply Map.wf_set; exact Hwf|].
    intro q; cbn [Tab.jumps].
    rewrite Jump.lookup_equation, Map.find_or_equation, Map.get_set by exact Hwf.
    destruct (eqb positive_encoding (encode (Jump.enc I) q) (encode (Jump.enc I) k))
      eqn:Hkey.
    + apply (eqb_true_iff positive_encoding positive_encoding_laws) in Hkey.
      apply (encode_injective HE) in Hkey; subst q.
      apply join_least; [exact Hlub|apply Hbound|exact Hf].
    + specialize (Hbound q); rewrite Jump.lookup_equation, Map.find_or_equation in Hbound.
      exact Hbound.
Qed.

(** The empty jump map is below every comparison map under the bottom law. *)
Theorem empty_bounded {N E P D A F} (I : Ide.t N E P D A F) J cs es ws ps :
  lattice_laws (Micro.lat (Ide.micro I)) ->
  bounded I J (Tab.State Map.empty cs es ws ps).
Proof.
  intro HL; split; [apply Map.wf_empty|].
  intro k; cbn [Tab.jumps].
  rewrite Jump.lookup_equation, Map.find_or_equation, Map.get_empty.
  apply bot_least; exact HL.
Qed.

Local Lemma internal_row {N E P D A F} (I : Ide.t N E P D A F) start r a :
  In r (roots I start) -> In a (Jump.arcs I) -> Jump.kind a = Icfg.Internal ->
  In (Jump.Path r a) (Jump.rows I start).
Proof.
  intros Hr Ha Hkind; apply Jump.rows_spec; right; right; left.
  exists r, a; repeat split; assumption || reflexivity.
Qed.

Local Lemma matched_row {N E P D A F} (I : Ide.t N E P D A F) start r a b :
  In r (roots I start) -> In a (Jump.arcs I) -> In b (Jump.arcs I) ->
  Cost.value (Jump.matches_c (Icfg.site_enc (Ifds.icfg (Ide.ifds I))) a b) = true ->
  In (Jump.Return r a b) (Jump.rows I start).
Proof.
  intros Hr Ha Hb Hmatch; apply Jump.rows_spec; right; right; right.
  exists r, a, b; repeat split; assumption || reflexivity.
Qed.

(** A matched-return contribution is below the corresponding row of any post-solution. *)
Theorem return_bounded {N E P D A F} (I : Ide.t N E P D A F) start J r a b s :
  encoding_laws (Jump.enc I) ->
  micro_laws (Ide.values I) (Ide.micro I) ->
  jump_post I start J -> bounded I J s ->
  In r (roots I start) -> In a (Jump.arcs I) -> In b (Jump.arcs I) ->
  bounded I J (Tab.return_ I r a b s).
Proof.
  intros HE HM Hpost Hbound Hr Ha Hb; rewrite Tab.return_equation.
  destruct (Cost.value
    (Jump.matches_c (Icfg.site_enc (Ifds.icfg (Ide.ifds I))) a b)) eqn:Hmatch.
  - apply update_bounded; [exact HE|exact (lat_ok _ _ HM)|exact (lub_ok _ _ HM)|exact Hbound|].
    eapply leb_trans; [exact (lat_ok _ _ HM)| |].
    + apply (compose_mono _ _ HM); [apply leb_refl; exact (lat_ok _ _ HM)|].
      apply (compose_mono _ _ HM); [apply (proj2 Hbound)|].
      apply (compose_mono _ _ HM); [apply leb_refl; exact (lat_ok _ _ HM)|].
      apply (proj2 Hbound).
    + exact (Hpost _ (matched_row I start r a b Hr Ha Hb Hmatch)).
  - exact Hbound.
Qed.

(** Pending keys always retain a declared entry root. *)
Definition work_valid {N E P D A F} (I : Ide.t N E P D A F) start
    (s : Tab.state N E P D F) :=
  forall k, In k (Tab.work s) -> In (fst k) (roots I start).

(** The leastness invariant combines payload provenance, roots and pointwise bounds. *)
Definition invariant {N E P D A F} (I : Ide.t N E P D A F) start J s :=
  bounded I J s /\ records_valid I start s /\ work_valid I start s.

Local Lemma fold_valid {X S} (P : S -> Prop) (f : S -> X -> S) xs s :
  (forall s x, P s -> In x xs -> P (f s x)) -> P s -> P (fold_left f xs s).
Proof.
  revert s; induction xs as [|x xs IH]; intros s Hstep Hs; cbn [fold_left].
  - exact Hs.
  - apply IH.
    + intros t y Ht Hy; apply Hstep; [exact Ht|right; exact Hy].
    + apply Hstep; [exact Hs|left; reflexivity].
Qed.

Local Lemma schedule_invariant {N E P D A F} (I : Ide.t N E P D A F) start J k s :
  invariant I start J s -> In (fst k) (roots I start) ->
  invariant I start J (Tab.schedule I k s).
Proof.
  intros [Hbound [Hrecords Hwork]] Hroot.
  split; [apply schedule_bounded; exact Hbound|].
  rewrite !Tab.schedule_equation; destruct (FinSet.mem (Jump.enc I) k (Tab.pending s)).
  - split; assumption.
  - split; [exact Hrecords|].
    intros q [Heq|Hin]; [subst q; exact Hroot|apply Hwork; exact Hin].
Qed.

Local Lemma update_invariant {N E P D A F} (I : Ide.t N E P D A F) start J k f s :
  encoding_laws (Jump.enc I) -> micro_laws (Ide.values I) (Ide.micro I) ->
  invariant I start J s -> In (fst k) (roots I start) ->
  leb (Micro.lat (Ide.micro I)) f (J k) = true ->
  invariant I start J (Tab.update I k f s).
Proof.
  intros HE HM [Hbound [Hrecords Hwork]] Hroot Hf; split.
  - apply update_bounded; try assumption; [exact (lat_ok _ _ HM)|exact (lub_ok _ _ HM)].
  - rewrite !Tab.update_equation.
    destruct (leb (Micro.lat (Ide.micro I)) f (Jump.lookup I (Tab.jumps s) k)).
    + split; assumption.
    + rewrite !Tab.schedule_equation.
      cbn [Tab.pending Tab.callers Tab.ends Tab.work].
      destruct (FinSet.mem (Jump.enc I) k (Tab.pending s)); split; try exact Hrecords.
      * exact Hwork.
      * intros q [Heq|Hin]; [subst q; exact Hroot|apply Hwork; exact Hin].
Qed.

Local Lemma return_invariant {N E P D A F} (I : Ide.t N E P D A F) start J r a b s :
  encoding_laws (Jump.enc I) -> micro_laws (Ide.values I) (Ide.micro I) ->
  jump_post I start J -> invariant I start J s ->
  In r (roots I start) -> In a (Jump.arcs I) -> In b (Jump.arcs I) ->
  invariant I start J (Tab.return_ I r a b s).
Proof.
  intros HE HM Hpost Hinv Hr Ha Hb; split.
  - apply return_bounded with (start := start); try assumption; exact (proj1 Hinv).
  - destruct Hinv as [Hbound [Hrecords Hwork]]; rewrite !Tab.return_equation.
    destruct (Cost.value (Jump.matches_c (Icfg.site_enc (Ifds.icfg (Ide.ifds I))) a b)).
    + rewrite !Tab.update_equation.
      destruct (leb (Micro.lat (Ide.micro I)) _ _).
      * split; assumption.
      * rewrite !Tab.schedule_equation.
        cbn [Tab.pending Tab.callers Tab.ends Tab.work].
        match goal with
        | |- context [if ?queued then _ else _] => destruct queued
        end;
          split; try exact Hrecords.
        -- exact Hwork.
        -- intros q [Heq|Hin]; [subst q; exact Hr|apply Hwork; exact Hin].
    + split; assumption.
Qed.

Local Lemma call_invariant {N E P D A F} (I : Ide.t N E P D A F) start J r a s :
  encoding_laws (Jump.enc I) -> micro_laws (Ide.values I) (Ide.micro I) ->
  jump_post I start J -> invariant I start J s ->
  In r (roots I start) -> In a (Jump.arcs I) ->
  (exists p, Jump.kind a = Icfg.Call p) ->
  invariant I start J (Cost.value (Tab.call_c I r a s)).
Proof.
  intros HE HM Hpost [Hbound [[Hcallers Hends] Hwork]] Hr Ha Hkind.
  rewrite Tab.call_equation; apply fold_valid.
  - intros t [code b] Ht Hb; cbn [snd].
    apply return_invariant with (start := start); try assumption.
    assert (Hvalid : end_valid I b).
    { eapply map_all_elements; [exact positive_encoding_laws| |exact Hb].
      apply map_all_bucket with (P := map_all positive_encoding (end_valid I));
        [exact Hends|apply map_all_empty].
    }
    exact (proj1 Hvalid).
  - split; [exact Hbound|]; split; [split|exact Hwork].
    + apply map_all_set; [exact Hcallers|].
      apply map_all_set.
      * apply map_all_bucket with
          (P := map_all positive_encoding (caller_valid I start));
          [exact Hcallers|apply map_all_empty].
      * split; [exact Hr|]; split; assumption.
    + exact Hends.
Qed.

Local Lemma end_invariant {N E P D A F} (I : Ide.t N E P D A F) start J r a s :
  encoding_laws (Jump.enc I) -> micro_laws (Ide.values I) (Ide.micro I) ->
  jump_post I start J -> invariant I start J s ->
  In a (Jump.arcs I) -> (exists p, Jump.kind a = Icfg.Return p) ->
  invariant I start J (Cost.value (Tab.end_c I r a s)).
Proof.
  intros HE HM Hpost [Hbound [[Hcallers Hends] Hwork]] Ha Hkind.
  rewrite Tab.end_equation; apply fold_valid.
  - intros t [code [outer call]] Ht Hcall; cbn [snd fst].
    assert (Hvalid : caller_valid I start (outer, call)).
    { eapply map_all_elements; [exact positive_encoding_laws| |exact Hcall].
      apply map_all_bucket with
        (P := map_all positive_encoding (caller_valid I start));
        [exact Hcallers|apply map_all_empty]. }
    destruct Hvalid as [Hr [Harc Hcallkind]].
    apply return_invariant with (start := start); assumption.
  - split; [exact Hbound|]; split; [split|exact Hwork].
    + exact Hcallers.
    + apply map_all_set; [exact Hends|].
      apply map_all_set.
      * apply map_all_bucket with (P := map_all positive_encoding (end_valid I));
          [exact Hends|apply map_all_empty].
      * split; assumption.
Qed.

(** Each specialized arc case preserves the leastness invariant. *)
Theorem arc_invariant {N E P D A F} (I : Ide.t N E P D A F) start J r a s :
  encoding_laws (Jump.enc I) -> micro_laws (Ide.values I) (Ide.micro I) ->
  jump_post I start J -> invariant I start J s ->
  In r (roots I start) -> In a (Jump.arcs I) ->
  invariant I start J (Cost.value (Tab.arc_c I r a s)).
Proof.
  intros HE HM Hpost Hinv Hr Ha; rewrite Tab.arc_equation.
  destruct (Jump.kind a) as [|p|p] eqn:Hkind.
  - apply update_invariant; try assumption.
    eapply leb_trans; [exact (lat_ok _ _ HM)| |].
    + apply (compose_mono _ _ HM); [apply leb_refl; exact (lat_ok _ _ HM)|].
      apply (proj2 (proj1 Hinv)).
    + exact (Hpost _ (internal_row I start r a Hr Ha Hkind)).
  - apply call_invariant with (start := start); try assumption.
    exists p; exact Hkind.
  - apply end_invariant with (start := start); try assumption.
    exists p; exact Hkind.
Qed.

(** Every entry root has an identity row, including unreachable callee entries. *)
Theorem root_identity {N E P D A F} (I : Ide.t N E P D A F) start J r :
  jump_post I start J -> In r (roots I start) ->
  leb (Micro.lat (Ide.micro I)) (Micro.id (Ide.micro I)) (J (r, r)) = true.
Proof.
  apply TabPaths.root_identity.
Qed.

(** Every prepared key retains one of the actual start or call-entry roots. *)
Theorem prepared_inventory_roots {N E P D A F} (I : Ide.t N E P D A F) start k :
  In k (Tab.inventory (Tab.prepare I start)) -> In (fst k) (roots I start).
Proof.
  rewrite Tab.prepare_equation; cbn [Tab.inventory].
  intro Hkey; apply in_flat_map in Hkey.
  destruct Hkey as [r [Hr Hkey]]; apply in_map_iff in Hkey.
  destruct Hkey as [v [Heq Hv]]; subst k; exact Hr.
Qed.

(** Every prepared source bucket contains actual exploded arcs. *)
Theorem prepared_outgoing_arcs {N E P D A F} (I : Ide.t N E P D A F) start v a :
  In a (Index.find (IdeValue.key_enc I) v (Tab.outgoing (Tab.prepare I start))) ->
  In a (Jump.arcs I).
Proof.
  rewrite Tab.prepare_equation; cbn [Tab.outgoing].
  rewrite Index.find_group_by; intro Hin; apply filter_In in Hin; exact (proj1 Hin).
Qed.

(** Initialization establishes bounds against every ground post-solution. *)
Theorem initial_invariant {N E P D A F} (I : Ide.t N E P D A F) start J :
  encoding_laws (Jump.enc I) -> micro_laws (Ide.values I) (Ide.micro I) ->
  jump_post I start J -> invariant I start J (Tab.initial I (Tab.prepare I start)).
Proof.
  intros HE HM Hpost; rewrite Tab.initial_equation; apply fold_valid.
  - intros s r Hs Hr.
    assert (Hroot : In r (roots I start)).
    { rewrite Tab.prepare_equation in Hr; exact Hr. }
    apply update_invariant; try assumption; apply root_identity with (start := start);
      assumption.
  - apply fold_valid.
    + intros s k Hs Hk; apply schedule_invariant; [exact Hs|].
      apply prepared_inventory_roots with (start := start); exact Hk.
    + split; [apply empty_bounded; exact (lat_ok _ _ HM)|]; split.
      * split; apply map_all_empty.
      * intros k Hk; inversion Hk.
Qed.

(** A loop step retains provenance and bounds in both its continuing and stopping outcomes. *)
Theorem step_invariant {N E P D A F} (I : Ide.t N E P D A F) start J s :
  encoding_laws (Jump.enc I) -> micro_laws (Ide.values I) (Ide.micro I) ->
  jump_post I start J -> invariant I start J s ->
  match Tab.step I (Tab.prepare I start) s with
  | inl next | inr next => invariant I start J next
  end.
Proof.
  intros HE HM Hpost [Hbound [Hrecords Hwork]]; rewrite Tab.tabulate_equation.
  destruct (Tab.work s) as [|[r v] rest] eqn:Hqueue.
  - split; [exact Hbound|]; split; assumption.
  - apply fold_valid.
    + intros t a Ht Ha; apply arc_invariant with (start := start); try assumption.
      * apply (Hwork (r, v)); rewrite Hqueue; left; reflexivity.
      * apply prepared_outgoing_arcs with (start := start) (v := v); exact Ha.
    + split; [exact Hbound|]; split; [exact Hrecords|].
      intros k Hk; apply Hwork; rewrite Hqueue; right; exact Hk.
Qed.

(** Every raw result, including exhaustion, stays below every ground jump post-solution. *)
Theorem raw_bounded {N E P D A F} (I : Ide.t N E P D A F) start J fuel :
  encoding_laws (Jump.enc I) -> micro_laws (Ide.values I) (Ide.micro I) ->
  jump_post I start J ->
  match Tab.raw I start fuel with
  | inl s | inr s => bounded I J s
  end.
Proof.
  intros HE HM Hpost; rewrite Tab.raw_equation.
  pose proof (iterate_value (Tab.step_c I (Tab.prepare I start)) fuel
    (Tab.initial I (Tab.prepare I start))) as Hrun.
  assert (Hpreserved : forall n s result,
    runs (Tab.step_c I (Tab.prepare I start)) n s result ->
    invariant I start J s ->
    match result with
    | inl next | inr next => invariant I start J next
    end).
  { intros n s result Hr; induction Hr as [s|n s r Hstop|n s next result Hnext Hr IH];
      intro Hinv.
    - exact Hinv.
    - pose proof (step_invariant I start J s HE HM Hpost Hinv) as Hstep.
      rewrite Tab.step_c_value in Hstop; rewrite Hstop in Hstep; exact Hstep.
    - apply IH; pose proof (step_invariant I start J s HE HM Hpost Hinv) as Hstep.
      rewrite Tab.step_c_value in Hnext; rewrite Hnext in Hstep; exact Hstep. }
  specialize (Hpreserved _ _ _ Hrun (initial_invariant I start J HE HM Hpost)).
  destruct (Cost.value (iterate _ fuel _)); exact (proj1 Hpreserved).
Qed.

(** Every certified raw outcome satisfies the existing ground jump postcondition. *)
Theorem tabulate_jump_post {N E P D A F} (I : Ide.t N E P D A F) start fuel c :
  Tab.tabulate I start fuel = Tab.Certified c ->
  jump_post I start (Jump.lookup I (proj1_sig c)).
Proof.
  intro Hresult; exact (proj2_sig c).
Qed.

(** Every certified raw outcome is least among all maps satisfying the same ground rows. *)
Theorem tabulate_jump_least {N E P D A F} (I : Ide.t N E P D A F) start fuel c J :
  encoding_laws (Jump.enc I) -> micro_laws (Ide.values I) (Ide.micro I) ->
  Tab.tabulate I start fuel = Tab.Certified c ->
  jump_post I start J ->
  forall k, leb (Micro.lat (Ide.micro I))
    (Jump.lookup I (proj1_sig c) k) (J k) = true.
Proof.
  intros HE HM Hresult Hpost k.
  pose proof (raw_bounded I start J fuel HE HM Hpost) as Hbound.
  rewrite Tab.outcome_equation in Hresult.
  destruct (Tab.raw I start fuel) as [s|s] eqn:Hraw; [discriminate|].
  apply Tab.certify_candidate in Hresult; rewrite Hresult.
  exact (proj2 Hbound k).
Qed.

(** Certified jumps bound a labelled refinement of each original supported balanced execution. *)
Theorem tabulate_jump_sound {N E P D A F} (I : Ide.t N E P D A F)
    start fuel c origin n d :
  micro_laws (Ide.values I) (Ide.micro I) -> TabWeight.laws (Ide.micro I) ->
  Ifds.flow_closed (Ide.ifds I) -> Ifds.seed_supported (Ide.ifds I) origin ->
  In origin (roots I start) ->
  Tab.tabulate I start fuel = Tab.Certified c ->
  Stack.balanced (Ide.ifds I) (fst origin) (snd origin) n d ->
  exists as_, TabPaths.trace I (fst origin, snd origin, []) as_ (n, d, []) /\
    Forall (fun a => In a (Jump.arcs I)) as_ /\
    leb (Micro.lat (Ide.micro I)) (TabWeight.weight I as_)
      (Jump.lookup I (proj1_sig c) (origin, (n, d))) = true.
Proof.
  intros HM HW Hclosed Hsupported Hroot Hrun Hpath.
  apply (TabJumpPaths.balanced_path_sound I start (Jump.lookup I (proj1_sig c))
    origin HM HW Hclosed (tabulate_jump_post I start fuel c Hrun) n d);
    assumption.
Qed.

(** Value leastness uses the value lattice's own laws and the actual public value analysis. *)
Theorem tabulate_values_least {N E P D A F} (I : Ide.t N E P D A F)
    J start a0 fuel c sigma :
  encoding_laws (Cfg.node_enc (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) ->
  encoding_laws (Cfg.edge_enc (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) ->
  encoding_laws (Ifds.fact_enc (Ide.ifds I)) ->
  lattice_laws (Ide.values I) -> lub_laws (Ide.values I) ->
  micro_laws (Ide.values I) (Ide.micro I) ->
  TabValues.tabulate_values I J start a0 fuel = TabValues.Certified c ->
  post_solution (Ide.values I)
    (Analysis.system (value_analysis I (Jump.lookup_c I J) start a0)) sigma ->
  forall v, leb (Ide.values I) (TabValues.lookup I (proj1_sig c) v) (sigma v) = true.
Proof.
  intros HN HE HD HL HJ HM Hrun Hpost.
  exact (TabValueSound.tabulate_values_least I J start a0 sigma HN HE HD HL HJ HM Hpost
    fuel c Hrun).
Qed.

(** Actual certified value maps bound every original prefix, including pending calls and empty runs. *)
Theorem tabulate_values_sound {N E P D A F} (I : Ide.t N E P D A F)
    start a0 jump_fuel value_fuel jumps values n d stack :
  encoding_laws (Cfg.node_enc (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) ->
  encoding_laws (Cfg.edge_enc (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) ->
  encoding_laws (Ifds.fact_enc (Ide.ifds I)) ->
  lattice_laws (Ide.values I) ->
  micro_laws (Ide.values I) (Ide.micro I) -> TabWeight.laws (Ide.micro I) ->
  graph_wf (Cfg.graph (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) ->
  Ifds.flow_closed (Ide.ifds I) -> Ifds.seed_supported (Ide.ifds I) start ->
  Tab.tabulate I (fst start) jump_fuel = Tab.Certified jumps ->
  TabValues.tabulate_values I (proj1_sig jumps) start a0 value_fuel = TabValues.Certified values ->
  Stack.path (Ide.ifds I) (fst start, snd start, []) (n, d, stack) ->
  exists as_, TabPaths.trace I (fst start, snd start, []) as_ (n, d, stack) /\
    Forall (fun a => In a (Jump.arcs I)) as_ /\
    leb (Ide.values I) (Micro.apply (Ide.micro I) (TabWeight.weight I as_) a0)
      (TabValues.lookup I (proj1_sig values) (n, d)) = true.
Proof.
  intros HN HE HD HL HM HW HG Hclosed Hsupported Hjump Hvalue Hpath.
  apply (TabJumpPaths.prefix_path_sound I (fst start) (Jump.lookup I (proj1_sig jumps))
    start HM HW Hclosed (tabulate_jump_post I (fst start) jump_fuel jumps Hjump)
    (Jump.lookup_c I (proj1_sig jumps)) a0 (TabValues.lookup I (proj1_sig values))).
  - intro k; reflexivity.
  - exact HN.
  - exact HE.
  - exact HD.
  - exact HL.
  - reflexivity.
  - exact (proj2_sig values).
  - exact HG.
  - destruct start as [node fact].
    rewrite TabPaths.roots_value; apply in_app_iff; left; apply in_map.
    destruct fact as [fact|].
    + right; apply in_map; exact Hsupported.
    + left; reflexivity.
  - exact Hsupported.
  - exact Hpath.
Qed.

(** A semantic flow alternative has one canonical prepared exploded arc. *)
Definition observed_arc {N E P D A F} (I : Ide.t N E P D A F) e x y :=
  TabPaths.label I e x y.

(** Arc preparation covers each listed edge and each actual supported flow alternative. *)
Theorem observed_arc_member {N E P D A F} (I : Ide.t N E P D A F) e x y :
  In e (Cfg.edges (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) ->
  Ifds.fact_supported (Ide.ifds I) x -> In y (Ifds.flow (Ide.ifds I) e x) ->
  In (observed_arc I e x y) (Jump.arcs I).
Proof.
  apply TabPaths.label_member.
Qed.

(** Every prepared exploded call contributes its own callee-entry root. *)
Theorem call_target_root {N E P D A F} (I : Ide.t N E P D A F) start a p :
  In a (Jump.arcs I) -> Jump.kind a = Icfg.Call p ->
  In (Jump.target a) (roots I start).
Proof.
  apply TabPaths.call_target_root.
Qed.

(** Every supported start fact contributes an initial procedure-entry root. *)
Theorem supported_start_root {N E P D A F} (I : Ide.t N E P D A F) start d :
  Ifds.fact_supported (Ide.ifds I) d -> In (start, d) (roots I start).
Proof.
  intro Hd; unfold roots; rewrite TabPaths.roots_value.
  apply in_app_iff; left; apply in_map.
  destruct d as [d|]; [right; apply in_map; exact Hd|left; reflexivity].
Qed.

Local Lemma bool_internal {N E P D} (I : Ifds.t N E P D) J r a :
  Jump.holds (Ifds.as_ide I) J (Jump.Path r a) ->
  Jump.weight a = true -> J (r, Jump.source a) = true ->
  J (r, Jump.target a) = true.
Proof.
  unfold Jump.holds; intros Hrow Hweight Hbefore.
  rewrite Hweight, Hbefore in Hrow.
  assert (Hle : leb bool_lattice true (J (r, Jump.target a)) = true) by exact Hrow.
  destruct (J (r, Jump.target a)); [reflexivity|discriminate Hle].
Qed.

Local Lemma bool_return {N E P D} (I : Ifds.t N E P D) J r a b :
  Jump.holds (Ifds.as_ide I) J (Jump.Return r a b) ->
  Jump.weight a = true -> Jump.weight b = true ->
  J (r, Jump.source a) = true -> J (Jump.target a, Jump.source b) = true ->
  J (r, Jump.target b) = true.
Proof.
  unfold Jump.holds; intros Hrow Hcall Hret Hbefore Hinside.
  rewrite Hcall, Hret, Hbefore, Hinside in Hrow.
  assert (Hle : leb bool_lattice true (J (r, Jump.target b)) = true) by exact Hrow.
  destruct (J (r, Jump.target b)); [reflexivity|discriminate Hle].
Qed.

(** A Boolean jump post-solution covers every balanced Stack path on supported seed facts. *)
Theorem ifds_post_balanced {N E P D} (I : Ifds.t N E P D) start J root n d :
  Ifds.flow_closed I -> Ifds.seed_supported I root ->
  In root (roots (Ifds.as_ide I) start) ->
  jump_post (Ifds.as_ide I) start J ->
  Stack.balanced I (fst root) (snd root) n d -> J (root, (n, d)) = true.
Proof.
  intros Hclosed Hsupported Hroot Hpost Hpath.
  eapply TabPaths.balanced_induction with
    (R := fun r => In r (roots (Ifds.as_ide I) start))
    (Q := fun r v => J (r, v) = true); try eassumption.
  - intros r Hr.
    cbn beta.
    pose proof (root_identity (Ifds.as_ide I) start J r Hpost Hr) as Hidentity.
    assert (Hle : leb bool_lattice true (J (r, r)) = true) by exact Hidentity.
    destruct (J (r, r)) eqn:Hrr.
    + exact Hrr.
    + discriminate Hle.
  - intros e p x y He Hkind Hx Hxy.
    apply (call_target_root (Ifds.as_ide I) start (observed_arc (Ifds.as_ide I) e x y) p).
    + apply observed_arc_member; assumption.
    + exact Hkind.
  - intros r e x y Hr Hx Hbefore He Hkind Hxy.
    apply (bool_internal I J r (observed_arc (Ifds.as_ide I) e x y)).
    + apply Hpost, internal_row; try assumption.
      apply observed_arc_member; assumption.
    + reflexivity.
    + exact Hbefore.
  - intros r call ret p x entry exit y Hr Hx Hbefore Hcall Hcallkind Hentry
      Hexit Hinside Hret Hretkind Hy.
    apply (bool_return I J r
      (observed_arc (Ifds.as_ide I) call x entry)
      (observed_arc (Ifds.as_ide I) ret exit y)); try assumption; try reflexivity.
    apply Hpost, matched_row; try assumption.
    + apply observed_arc_member; assumption.
    + apply observed_arc_member; assumption.
    + rewrite Jump.matches_c_value; unfold observed_arc; rewrite !TabPaths.label_kind.
      assert (Hcallview :
        Icfg.edge_kind (Ifds.icfg (Ide.ifds (Ifds.as_ide I))) call = Icfg.Call p)
        by exact Hcallkind.
      assert (Hretview :
        Icfg.edge_kind (Ifds.icfg (Ide.ifds (Ifds.as_ide I))) ret = Icfg.Return p)
        by exact Hretkind.
      rewrite Hcallview, Hretview; apply eqb_refl.
Qed.

End TabSound.
