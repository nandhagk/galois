(** * Prepared frame-cache agreement

    Preparation retains the exact family, expression IDs and instruction/operand source tables.
    For example, repeated client values keep one dense frame identity without losing operand order.
    Builds on: AnalysesSsaPreRename, AnalysesSsaPreFrg and the public interning/index contracts. *)

From Stdlib Require Import List Bool.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet BaseIndex BaseIntern.
From Galois.Graph Require Import GraphModel GraphPrepared.
From Galois.Program Require Import ProgramCfg ProgramSsaPoints.
From Galois.Framework Require Import FrameworkBitvector FrameworkUtil.
From Galois.Analyses.Ssa Require Import AnalysesSsaPreContext AnalysesSsaPreFamily
  AnalysesSsaPreFrg AnalysesSsaPreRename.
Import List.ListNotations Cost.Notations.

Module PreFrameCache.

Local Lemma assignment_inventory {X Y} (enc : encoding X) (HE : encoding_laws enc)
    (f : X -> Y) :
  forall xs x, In x xs ->
    Map.get enc x (Map.of_list enc (map (fun key => (key, f key)) xs)) = Some (f x).
Proof.
  intros xs x Hx; rewrite Map.of_list_get.
  assert (Hfold : forall ys old, old = Some (f x) \/ In x ys ->
    fold_left (fun acc pair =>
      if eqb enc x (fst pair) then Some (snd pair) else acc)
      (map (fun key => (key, f key)) ys) old = Some (f x)).
  { induction ys as [|key rest IH]; intros old Hhit; cbn [map fold_left fst snd].
    - destruct Hhit as [Hhit|[]]; exact Hhit.
    - destruct (eqb enc x key) eqn:Hsame.
      + apply (eqb_true_iff _ HE) in Hsame; subst key; apply IH; now left.
      + apply IH; destruct Hhit as [Hhit|[Heq|Hhit]]; [now left| |now right].
        subst key; rewrite eqb_refl in Hsame; discriminate. }
  apply Hfold; now right.
Qed.

Local Lemma assignment_sound {X Y} (enc : encoding X) (HE : encoding_laws enc)
    (pairs : list (X * Y)) :
  forall x y, Map.get enc x (Map.of_list enc pairs) = Some y -> In (x, y) pairs.
Proof.
  intros x y; rewrite Map.of_list_get.
  assert (Hfold : forall xs old,
    fold_left (fun acc pair =>
      if eqb enc x (fst pair) then Some (snd pair) else acc) xs old = Some y ->
    old = Some y \/ In (x, y) xs).
  { induction xs as [|[key value] rest IH]; intros old Hresult; [now left|].
    cbn [fold_left fst snd] in Hresult.
    destruct (eqb enc x key) eqn:Hsame.
    - destruct (IH _ Hresult) as [Hvalue|Hin].
      + apply (eqb_true_iff _ HE) in Hsame; inversion Hvalue; subst key value; right; now left.
      + right; now right.
    - destruct (IH _ Hresult) as [Hvalue|Hin]; [now left|right; now right]. }
  intro Hresult; destruct (Hfold pairs None Hresult) as [Hfalse|Hin];
    [discriminate|exact Hin].
Qed.

Section Cache.
Context {B BE N E V K G C U : Type}.
Variable c : Pre.ctx B BE N E V K G C U.

(** Placement duties are the already-proved family and four-clause phi observations of one result. *)
Record placement_laws (data : PreFrg.phi_data) : Prop := PlacementLaws {
  placement_family_nodup : NoDup (PreFrg.all_family data);
  placement_family : forall u, In u (PreFrg.all_family data) <-> PreFamily.in_family c u;
  placement_sites_wf : FinSet.wf (PreFrg.phi_encoding c) (PreFrg.sites data);
  placement_sites : forall u b,
    FinSet.mem (PreFrg.phi_encoding c) (b, u) (PreFrg.sites data) = true <->
      PreFrg.phi_needed c u b
}.

(** Every actual lawful placement result supplies these cache-input duties. *)
Theorem placement_from_output :
  Pre.laws c ->
  forall data, PreFrg.phi_sites c = inr data -> placement_laws data.
Proof.
  intros Hlaw data Houtput.
  pose proof (PreFrg.phi_sites_success c Hlaw) as Hactual.
  assert (Heq : data = PreFrg.PhiData (PreFamily.universe c)
    (PreFrg.phi_sites_for c (PreFamily.universe c))) by congruence.
  subst data; constructor.
  - exact (proj1 (PreFamily.universe_exact c Hlaw)).
  - exact (proj2 (PreFamily.universe_exact c Hlaw)).
  - apply PreFrg.phi_sites_for_wf.
  - apply PreFrg.phi_sites_for_exact; [exact Hlaw|exact (proj2 (PreFamily.universe_exact c Hlaw))].
Qed.

Definition eligible (data : @PreFrg.phi_data B U) :=
  filter (Pre.pure c) (PreFrg.all_family data).
Definition names data := Intern.of_list (Pre.eu (Pre.keys c)) (eligible data).
Definition phi_pairs data :=
  Cost.value (PreRename.phi_pairs_c c (names data) (FinSet.elements (PreFrg.sites data))).
Definition keys data := map (fun pair => (fst pair, snd (snd pair))) (phi_pairs data).
Definition event_description bank e := Cost.value (PreRename.event_c c bank e).

Local Lemma initial_symbols family :
  PreRename.symbols (PreRename.initial_scope c family) =
    Intern.of_list (Pre.eu (Pre.keys c)) family.
Proof.
  rewrite PreRename.initial_scope_equation; reflexivity.
Qed.

(** Prepared-cache observations identify every stored table with its actual source constructor. *)
Record prepared_laws (data : PreFrg.phi_data) (index : PreRename.prepared B BE N E U) : Prop :=
  PreparedLaws {
  cached_eligible : PreRename.eligible_family index = eligible data;
  cached_entry : PreRename.entry_scope index = PreRename.initial_scope c (eligible data);
  cached_ids : PreRename.family_ids index = Map.elements (Intern.inverse (names data));
  cached_events : PreRename.events index = Cost.value (PreRename.event_index_c c (names data));
  cached_exits : PreRename.exit_points index = Cost.value (PreRename.exits_c c);
  cached_phi_keys : PreRename.phi_keys index = keys data;
  cached_phi_definitions : PreRename.phi_definitions index =
    Index.group_by (Pre.eb (Pre.keys c)) fst (phi_pairs data);
  cached_arguments : PreRename.arguments index =
    Cost.value (PreRename.arguments_c c (names data) (keys data))
}.

(** The actual preparation establishes all literal cache observations without semantic premises. *)
Theorem prepare_laws data : prepared_laws data (PreRename.prepare c data).
Proof.
  constructor; rewrite PreRename.prepare_equation; cbn zeta;
    cbn [PreRename.eligible_family PreRename.entry_scope PreRename.family_ids PreRename.events
      PreRename.exit_points PreRename.phi_keys PreRename.phi_definitions PreRename.arguments];
    rewrite ?initial_symbols; reflexivity.
Qed.

(** The eligible list preserves the exact pure part of the discovered family. *)
Theorem eligible_exact data :
  placement_laws data ->
  forall u, In u (eligible data) <-> PreFamily.in_family c u /\ Pre.pure c u = true.
Proof.
  intros Hdata u; unfold eligible; rewrite filter_In, (placement_family data Hdata u); reflexivity.
Qed.

(** Prepared expression symbols form a lawful dense interning table on any supplied list. *)
Theorem names_wf data :
  Pre.laws c -> Intern.wf (Pre.eu (Pre.keys c)) (names data).
Proof.
  intro Hlaw; apply Intern.wf_of_list; exact (Pre.eu_laws c (Pre.graphs c Hlaw)).
Qed.

(** Dense expression lookup succeeds exactly for eligible family members. *)
Theorem names_domain data :
  Pre.laws c -> placement_laws data ->
  forall u, (exists id, Intern.find (Pre.eu (Pre.keys c)) u (names data) = Some id) <->
    PreFamily.in_family c u /\ Pre.pure c u = true.
Proof.
  intros Hlaw Hdata u; unfold names.
  rewrite <- (Intern.intern_list_spec _ (Pre.eu_laws c (Pre.graphs c Hlaw))).
  apply eligible_exact; exact Hdata.
Qed.

(** Two expression names assigned the same dense ID are the same client expression. *)
Theorem names_injective data :
  Pre.laws c ->
  forall u v id, Intern.find (Pre.eu (Pre.keys c)) u (names data) = Some id ->
    Intern.find (Pre.eu (Pre.keys c)) v (names data) = Some id -> u = v.
Proof.
  intros Hlaw u v id Hu Hv.
  pose proof (Intern.key_of_find _ _ _ _ (names_wf data Hlaw) Hu) as Hname.
  pose proof (Intern.key_of_find _ _ _ _ (names_wf data Hlaw) Hv) as Hname'; congruence.
Qed.

(** Canonical scopes carry a lawful shared symbol table and canonical dense frame bindings. *)
Definition scope_wf (frames : PreRename.scope B E U) : Prop :=
  Intern.wf (Pre.eu (Pre.keys c)) (PreRename.symbols frames) /\
    Map.wf positive_encoding (PreRename.bindings frames).

(** Entry preparation establishes both symbol and dense-frame representation invariants. *)
Theorem initial_scope_wf family :
  Pre.laws c -> scope_wf (PreRename.initial_scope c family).
Proof.
  intro Hlaw; rewrite PreRename.initial_scope_equation; split.
  - apply Intern.wf_of_list; exact (Pre.eu_laws c (Pre.graphs c Hlaw)).
  - apply Map.wf_of_list.
Qed.

(** Dense stores retain the interner and canonical binding representation. *)
Theorem store_wf {frames id frame} :
  scope_wf frames -> scope_wf (PreRename.store frames id frame).
Proof.
  intros [Hnames Hframes]; rewrite PreRename.store_equation; split; [exact Hnames|].
  apply Map.wf_set; exact Hframes.
Qed.

(** Semantic expression lookup is the same dense top lookup for the supplied prepared binding. *)
Theorem top_id_agrees {frames u id} :
  Intern.find (Pre.eu (Pre.keys c)) u (PreRename.symbols frames) = Some id ->
    PreRename.top c frames u = PreRename.top_id frames id u.
Proof.
  intro Hid; rewrite PreRename.top_equation, Hid; reflexivity.
Qed.

(** Initial frames agree with the actual initially-available callback on every supplied family member. *)
Theorem initial_top family :
  Pre.laws c ->
  forall u, In u family ->
    PreRename.top c (PreRename.initial_scope c family) u = PreRename.initial_frame c u.
Proof.
  intros Hlaw u Hu; pose proof (Pre.eu_laws c (Pre.graphs c Hlaw)) as HE.
  set (bank := Intern.of_list (Pre.eu (Pre.keys c)) family).
  assert (Hbank : Intern.wf (Pre.eu (Pre.keys c)) bank) by (apply Intern.wf_of_list; exact HE).
  destruct (proj1 (Intern.intern_list_spec _ HE family u) Hu) as [id Hid].
  rewrite PreRename.initial_scope_equation, PreRename.top_equation.
  cbn [PreRename.symbols PreRename.bindings]; fold bank; fold bank in Hid; rewrite Hid.
  rewrite Map.find_or_equation.
  set (entries := Map.elements (Intern.inverse bank)).
  assert (Hnodup : NoDup (map fst
    (map (fun pair => (fst pair, PreRename.initial_frame c (snd pair))) entries))).
  { rewrite map_map; cbn [fst]; apply (Map.elements_nodup positive_encoding).
    exact (proj2 (Intern.wf_maps _ _ Hbank)). }
  rewrite (Pre.assignment_member positive_encoding positive_encoding_laws _ Hnodup id
    (PreRename.initial_frame c u)); [reflexivity|].
  apply in_map_iff; exists (id, u); split; [reflexivity|].
  apply (Map.elements_spec positive_encoding positive_encoding_laws);
    [exact (proj2 (Intern.wf_maps _ _ Hbank))|].
  rewrite <- Intern.key_of_equation; exact (Intern.key_of_find _ _ _ _ Hbank Hid).
Qed.

(** A dense store changes exactly the expression having the written ID in the same lawful table. *)
Theorem top_store :
  Pre.laws c ->
  forall frames u id frame, scope_wf frames ->
    Intern.find (Pre.eu (Pre.keys c)) u (PreRename.symbols frames) = Some id ->
    forall v, PreRename.top c (PreRename.store frames id frame) v =
      if eqb (Pre.eu (Pre.keys c)) v u then frame else PreRename.top c frames v.
Proof.
  intros Hlaw frames u id frame [Hnames Hframes] Hu v.
  rewrite !PreRename.top_equation, PreRename.store_equation.
  cbn [PreRename.symbols PreRename.bindings].
  destruct (eqb (Pre.eu (Pre.keys c)) v u) eqn:Hsame.
  - apply (eqb_true_iff _ (Pre.eu_laws c (Pre.graphs c Hlaw))) in Hsame; subst v.
    rewrite Hu, Map.find_or_equation, Map.get_set_same by exact Hframes; reflexivity.
  - destruct (Intern.find (Pre.eu (Pre.keys c)) v (PreRename.symbols frames))
      as [other|] eqn:Hv; [|reflexivity].
    rewrite !Map.find_or_equation, (Map.get_set_other positive_encoding positive_encoding_laws)
      by (try exact Hframes; intro Heq; subst other;
        pose proof (Intern.key_of_find _ _ _ _ Hnames Hu);
        pose proof (Intern.key_of_find _ _ _ _ Hnames Hv);
        assert (v = u) by congruence; subst v; rewrite eqb_refl in Hsame; discriminate).
    reflexivity.
Qed.

(** Every listed point edge reads the same prepared event as its original syntax callbacks. *)
Theorem event_lookup data :
  Pre.laws c ->
  forall e, In e (Cfg.edges (Pre.point_cfg c)) ->
    Map.get (Pre.ee (Pre.keys c)) e (PreRename.events (PreRename.prepare c data)) =
      Some (event_description (names data) e).
Proof.
  intros Hlaw e He.
  rewrite (cached_events data _ (prepare_laws data)), PreRename.event_index_value.
  apply assignment_inventory; [exact (Pre.ee_laws c (Pre.graphs c Hlaw))|exact He].
Qed.

(** Prepared event lookup cannot invent an unlisted source edge or change its event description. *)
Theorem event_lookup_domain data :
  Pre.laws c ->
  forall e info, Map.get (Pre.ee (Pre.keys c)) e
    (PreRename.events (PreRename.prepare c data)) = Some info ->
    In e (Cfg.edges (Pre.point_cfg c)) /\ info = event_description (names data) e.
Proof.
  intros Hlaw e info Hget.
  rewrite (cached_events data _ (prepare_laws data)), PreRename.event_index_value in Hget.
  apply (assignment_sound _ (Pre.ee_laws c (Pre.graphs c Hlaw))) in Hget.
  apply in_map_iff in Hget; destruct Hget as [edge [Heq He]].
  inversion Heq; subst edge info; auto.
Qed.

(** Event evaluation contains precisely a pure recomputation and its actual dense name binding. *)
Theorem evaluation_exact bank e {id u} :
  PreRename.evaluation (event_description bank e) = Some (id, u) <->
    Pre.recomputed c e = Some u /\ Pre.pure c u = true /\
      Intern.find (Pre.eu (Pre.keys c)) u bank = Some id.
Proof.
  unfold event_description; rewrite PreRename.event_value.
  cbn [PreRename.evaluation]; rewrite PreRename.evaluation_value.
  destruct (Pre.recomputed c e) as [value|] eqn:Hcomputed; [|intuition discriminate].
  destruct (Pre.pure c value) eqn:Hpure; [|intuition congruence].
  destruct (Intern.find (Pre.eu (Pre.keys c)) value bank) as [found|] eqn:Hfind;
    cbn [option_map]; intuition congruence.
Qed.

Local Lemma alterations_member bank e {id u} :
  In (id, u) (PreRename.alterations (event_description bank e)) <->
    In u (Bitvector.kill (Pre.expr (Pre.input c)) e) /\
      Intern.find (Pre.eu (Pre.keys c)) u bank = Some id.
Proof.
  unfold event_description; rewrite PreRename.event_value.
  cbn [PreRename.alterations]; rewrite Prepared.present_c_value, Prepared.present_spec.
  split.
  - intros [value [Hvalue Hlookup]]; rewrite PreRename.lookup_expression_value in Hlookup.
    destruct (Intern.find (Pre.eu (Pre.keys c)) value bank) as [found|] eqn:Hfind;
      cbn [option_map] in Hlookup; [|discriminate].
    inversion Hlookup; subst value found; auto.
  - intros [Hu Hfind]; exists u; split; [exact Hu|].
    rewrite PreRename.lookup_expression_value, Hfind; reflexivity.
Qed.

(** Kill-list membership agrees with the context's Boolean killing observation. *)
Theorem killed_member :
  Pre.laws c ->
  forall e u, Pre.killed c e u = true <-> In u (Bitvector.kill (Pre.expr (Pre.input c)) e).
Proof.
  intros Hlaw e u; rewrite Pre.killed_equation, existsb_exists; split.
  - intros [v [Hv Hsame]]; apply (eqb_true_iff _ (Pre.eu_laws c (Pre.graphs c Hlaw))) in Hsame.
    subst v; exact Hv.
  - intro Hu; exists u; split; [exact Hu|apply eqb_refl].
Qed.

(** Ordered prepared alterations cover exactly the killing eligible IDs, including duplicate arrivals. *)
Theorem event_alterations bank e :
  Pre.laws c ->
  forall id u, In (id, u) (PreRename.alterations (event_description bank e)) <->
    Pre.killed c e u = true /\ Intern.find (Pre.eu (Pre.keys c)) u bank = Some id.
Proof.
  intros Hlaw id u; rewrite alterations_member, (killed_member Hlaw); reflexivity.
Qed.

(** Event endpoints are the actual point-edge targets. *)
Theorem event_endpoint bank e :
  PreRename.endpoint (event_description bank e) = Graph.target (Pre.pg c) e.
Proof.
  unfold event_description; rewrite PreRename.event_value; reflexivity.
Qed.

(** Every pure source recomputation receives a prepared expression ID in the discovered family. *)
Theorem evaluation_available data :
  Pre.laws c -> placement_laws data ->
  forall e u, Pre.recomputed c e = Some u -> Pre.pure c u = true ->
    exists id, PreRename.evaluation (event_description (names data) e) = Some (id, u) /\
      Intern.find (Pre.eu (Pre.keys c)) u (names data) = Some id.
Proof.
  intros Hlaw Hdata e u Hcomputed Hpure.
  assert (Hfamily : PreFamily.in_family c u).
  { apply Pre.family_seed; exact (Pre.occurrences_seeded c (Pre.shapes c Hlaw) e u Hcomputed). }
  destruct (proj2 (names_domain data Hlaw Hdata u) (conj Hfamily Hpure)) as [id Hid].
  exists id; split; [apply evaluation_exact; auto|exact Hid].
Qed.

(** The entry scope carries exactly the same symbol table used to construct every event. *)
Theorem entry_symbols data :
  PreRename.symbols (PreRename.entry_scope (PreRename.prepare c data)) = names data.
Proof.
  rewrite (cached_entry data _ (prepare_laws data)), initial_symbols; reflexivity.
Qed.

(** Every entry scope built by preparation satisfies its concrete representation duties. *)
Theorem entry_scope_wf data :
  Pre.laws c -> scope_wf (PreRename.entry_scope (PreRename.prepare c data)).
Proof.
  intro Hlaw; rewrite (cached_entry data _ (prepare_laws data)).
  apply initial_scope_wf; exact Hlaw.
Qed.

(** The family-ID inventory enumerates precisely the dense bindings of that same shared table. *)
Theorem family_ids_exact data :
  Pre.laws c ->
  forall id u, In (id, u) (PreRename.family_ids (PreRename.prepare c data)) <->
    Intern.find (Pre.eu (Pre.keys c)) u (names data) = Some id.
Proof.
  intros Hlaw id u; rewrite (cached_ids data _ (prepare_laws data)).
  rewrite (Map.elements_spec positive_encoding positive_encoding_laws)
    by exact (proj2 (Intern.wf_maps _ _ (names_wf data Hlaw))).
  rewrite <- Intern.key_of_equation; split.
  - apply Intern.find_key_of; exact (names_wf data Hlaw).
  - apply Intern.key_of_find; exact (names_wf data Hlaw).
Qed.

(** Prepared exit flags cover exactly listed explicit exits and listed points with no successors. *)
Theorem exits_exact data :
  Pre.laws c ->
  forall n, FinSet.mem (Pre.en (Pre.keys c)) n
    (PreRename.exit_points (PreRename.prepare c data)) = true <->
    In n (Graph.nodes (Pre.pg c)) /\ (Pre.exit_point c n = true \/ Graph.out (Pre.pg c) n = []).
Proof.
  intros Hlaw n; rewrite (cached_exits data _ (prepare_laws data)), PreRename.exits_value.
  rewrite (PreFamily.set_member _ (Pre.en_laws c (Pre.graphs c Hlaw))).
  rewrite filter_In, !Cost.value_bind.
  fold (Pre.exit_point c n); destruct (Pre.exit_point c n) eqn:Hending.
  - rewrite Cost.value_ret; intuition congruence.
  - rewrite !Cost.value_bind; fold (Graph.out (Pre.pg c) n).
    destruct (Graph.out (Pre.pg c) n); rewrite Cost.value_ret; intuition congruence.
Qed.

(** Each prepared phi-ID pair retains the original canonical site and the actual expression binding. *)
Theorem phi_pairs_exact data :
  Pre.laws c -> placement_laws data ->
  forall b id u, In (b, (id, u)) (phi_pairs data) <->
    PreFrg.phi_needed c u b /\ Intern.find (Pre.eu (Pre.keys c)) u (names data) = Some id.
Proof.
  intros Hlaw Hdata b id u; unfold phi_pairs, PreRename.phi_pairs_c.
  rewrite Prepared.present_c_value, Prepared.present_spec; split.
  - intros [[block value] [Hsite Hlookup]].
    rewrite Cost.value_bind, Cost.value_ret in Hlookup.
    cbn [fst snd] in Hlookup.
    fold (Intern.find (Pre.eu (Pre.keys c)) value (names data)) in Hlookup.
    destruct (Intern.find (Pre.eu (Pre.keys c)) value (names data)) as [found|] eqn:Hfind;
      cbn [option_map fst snd] in Hlookup; [|discriminate].
    inversion Hlookup; subst block value found; split; [|exact Hfind].
    apply (placement_sites data Hdata).
    apply (FinSet.elements_spec _ (PreFrg.phi_encoding_laws c Hlaw));
      [exact (placement_sites_wf data Hdata)|exact Hsite].
  - intros [Hsite Hfind]; exists (b, u); split.
    + apply (FinSet.elements_spec _ (PreFrg.phi_encoding_laws c Hlaw));
        [exact (placement_sites_wf data Hdata)|].
      apply (placement_sites data Hdata); exact Hsite.
    + rewrite Cost.value_bind, Cost.value_ret; cbn [fst snd].
      fold (Intern.find (Pre.eu (Pre.keys c)) u (names data)).
      rewrite Hfind; reflexivity.
Qed.

(** Eligible phi keys are exactly the pure sites of the fixed four-clause placement relation. *)
Theorem keys_exact data :
  Pre.laws c -> placement_laws data ->
  forall b u, In (b, u) (keys data) <-> PreFrg.phi_needed c u b /\ Pre.pure c u = true.
Proof.
  intros Hlaw Hdata b u; unfold keys; rewrite in_map_iff; split.
  - intros [[block [id value]] [Heq Hin]]; cbn [fst snd] in Heq; inversion Heq; subst block value.
    apply (phi_pairs_exact data Hlaw Hdata) in Hin; destruct Hin as [Hphi Hid].
    split; [exact Hphi|].
    assert (Heligible : PreFamily.in_family c u /\ Pre.pure c u = true).
    { apply (proj1 (names_domain data Hlaw Hdata u)); now exists id. }
    exact (proj2 Heligible).
  - intros [Hphi Hpure].
    destruct (proj2 (names_domain data Hlaw Hdata u)
      (conj (PreFrg.phi_needed_family c Hphi) Hpure)) as [id Hid].
    exists (b, (id, u)); split; [reflexivity|].
    apply (phi_pairs_exact data Hlaw Hdata); auto.
Qed.

(** The block phi bucket has exactly the sites and IDs that its frame installation must define. *)
Theorem phi_definitions_exact data :
  Pre.laws c -> placement_laws data ->
  forall b id u, In (b, (id, u))
    (Index.find (Pre.eb (Pre.keys c)) b (PreRename.phi_definitions (PreRename.prepare c data))) <->
      PreFrg.phi_needed c u b /\ Intern.find (Pre.eu (Pre.keys c)) u (names data) = Some id.
Proof.
  intros Hlaw Hdata b id u; rewrite (cached_phi_definitions data _ (prepare_laws data)).
  rewrite Index.find_group_by, filter_In; cbn [fst]; rewrite eqb_refl.
  rewrite (phi_pairs_exact data Hlaw Hdata); tauto.
Qed.

Local Lemma argument_pairs_member bank keys {source b u be v id} :
  In (source, PreRename.Argument (b, u) be v id) (PreRename.argument_pairs c bank keys) <->
    In (b, u) keys /\ In be (Cost.value (Prepared.incoming_c (Pre.blocks c) b)) /\
      Graph.source (Pre.bg c) be = source /\ Pre.translate c be u = Some v /\
      Intern.find (Pre.eu (Pre.keys c)) v bank = id.
Proof.
  unfold PreRename.argument_pairs; rewrite in_flat_map; split.
  - intros [key [Hkey Hin]]; apply in_flat_map in Hin; destruct Hin as [edge [Hedge Hin]].
    destruct (Pre.translate c edge (snd key)) as [value|] eqn:Htranslate; [|contradiction].
    destruct Hin as [Heq|[]]; inversion Heq; subst.
    cbn [fst snd] in *; repeat split; try assumption; reflexivity.
  - intros [Hkey [Hbe [Hsource [Htranslate Hid]]]].
    exists (b, u); split; [exact Hkey|]; apply in_flat_map; exists be; split; [exact Hbe|].
    cbn [snd]; rewrite Htranslate, Hsource, Hid; now left.
Qed.

(** Every outgoing argument bucket retains its phi key, edge identity and exact source translation. *)
Theorem arguments_exact data :
  Pre.laws c -> placement_laws data ->
  forall source b u be v id, In (source, PreRename.Argument (b, u) be v id)
    (Index.find (Pre.eb (Pre.keys c)) source (PreRename.arguments (PreRename.prepare c data))) <->
    PreFrg.phi_needed c u b /\ Pre.pure c u = true /\
    In be (Cfg.edges (Pre.block_cfg c)) /\ Graph.target (Pre.bg c) be = b /\
    Graph.source (Pre.bg c) be = source /\ Pre.translate c be u = Some v /\
    Intern.find (Pre.eu (Pre.keys c)) v (names data) = id.
Proof.
  intros Hlaw Hdata source b u be v id.
  rewrite (cached_arguments data _ (prepare_laws data)), PreRename.arguments_value.
  rewrite Index.find_group_by, filter_In; cbn [fst]; rewrite eqb_refl.
  rewrite argument_pairs_member, (keys_exact data Hlaw Hdata).
  split.
  - intros [[[Hphi Hpure] [Hbe [Hsource [Htranslate Hid]]]] _].
    fold (PreFrg.incoming c b) in Hbe.
    apply (PreFrg.incoming_exact c Hlaw b (PreFrg.phi_needed_nodes c Hlaw Hphi)) in Hbe.
    destruct Hbe as [Hbe Htarget]; repeat split; assumption.
  - intros [Hphi [Hpure [Hbe [Htarget [Hsource [Htranslate Hid]]]]]]; split; [|reflexivity].
    split; [auto|]; split; [|auto].
    apply (PreFrg.incoming_exact c Hlaw b (PreFrg.phi_needed_nodes c Hlaw Hphi)); auto.
Qed.

(** Every required incoming phi edge receives a translated eligible ID in the source bucket. *)
Theorem arguments_total data :
  Pre.laws c -> placement_laws data ->
  forall u b be, PreFrg.phi_needed c u b -> Pre.pure c u = true ->
    In be (Cfg.edges (Pre.block_cfg c)) -> Graph.target (Pre.bg c) be = b ->
    exists v id, Pre.translate c be u = Some v /\
      Intern.find (Pre.eu (Pre.keys c)) v (names data) = Some id /\
      In (Graph.source (Pre.bg c) be, PreRename.Argument (b, u) be v (Some id))
        (Index.find (Pre.eb (Pre.keys c)) (Graph.source (Pre.bg c) be)
          (PreRename.arguments (PreRename.prepare c data))).
Proof.
  intros Hlaw Hdata u b be Hphi Hpure Hbe Htarget.
  pose proof (PreFrg.phi_needed_family c Hphi) as Hfamily.
  destruct (Pre.closed_translation c (Pre.shapes c Hlaw) be u Hbe Hfamily) as [v Htranslate].
  assert (Hv : PreFamily.in_family c v) by (eapply Pre.family_translate; eassumption).
  pose proof (Pre.translation_pure c (Pre.shapes c Hlaw) be u v Hpure Htranslate) as Hvpure.
  destruct (proj2 (names_domain data Hlaw Hdata v) (conj Hv Hvpure)) as [id Hid].
  exists v, id; split; [exact Htranslate|]; split; [exact Hid|].
  apply (arguments_exact data Hlaw Hdata); repeat split; try assumption; reflexivity.
Qed.

End Cache.

End PreFrameCache.
