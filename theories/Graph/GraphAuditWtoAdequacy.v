(** * Weak topological order audit adequacy

    Relates the counted construction to its source operations and cost bounds.
    For example, removing a component head records one comparison per vertex.
    Builds on: GraphAuditWto and graph traversal adequacy. *)

From Stdlib Require Import List Bool PArith Arith Lia Permutation ZArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditCost
  CollectionsAuditEncodingAdequacy CollectionsAuditCompareAdequacy
  CollectionsAuditPrimitiveAdequacy CollectionsAuditTrieAdequacy.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphScc GraphWto
  GraphAuditBase GraphAuditBaseAdequacy GraphAuditDfs GraphAuditScc GraphAuditWto
  GraphAuditDfsAdequacy
  GraphAuditSccAdequacy.
Import List.ListNotations.

(** * Local traversal equations *)

(** The choose traversal returns the corresponding uninstrumented result. *)
Lemma audit_wto_choose_result {V E} (EV : encoding V) ranks rest header :
    fst (@audit_wto_choose_counted V E EV ranks rest header) =
    fold_left (wto_earlier EV ranks) rest header.
Proof.
  revert header; induction rest as [|v rest IH]; intro header.
  - reflexivity.
  - cbn [audit_wto_choose_counted].
    assert (Hchoose : fst (@audit_wto_earlier_counted V E EV ranks header v) =
      wto_earlier EV ranks header v) by reflexivity.
    destruct (audit_wto_earlier_counted EV ranks header v) as [next here].
    cbn in Hchoose; subst next.
    specialize (IH (wto_earlier EV ranks header v)).
    destruct (audit_wto_choose_counted EV ranks rest (wto_earlier EV ranks header v));
      cbn in *; exact IH.
Qed.

(** The remove traversal returns the corresponding uninstrumented result. *)
Lemma audit_wto_remove_result {V E} (EV : encoding V) header vertices :
    fst (@audit_wto_remove_counted V E EV header vertices) = wto_remove EV header vertices.
Proof.
  unfold wto_remove; induction vertices as [|v rest IH].
  - reflexivity.
  - cbn [audit_wto_remove_counted filter].
    destruct (Pos.eqb (encode EV header) (encode EV v)); cbn;
      destruct (audit_wto_remove_counted EV header rest); cbn in *; congruence.
Qed.

(** The self edges traversal returns the corresponding uninstrumented result. *)
Lemma audit_wto_self_edges_result {V E} (EV : encoding V) (g : Graph.t V E) v edges :
    fst (audit_wto_self_edges EV g v edges) =
    existsb (fun e => Pos.eqb (encode EV v) (encode EV (Graph.target g e))) edges.
Proof.
  induction edges as [|edge rest IH].
  - reflexivity.
  - cbn [audit_wto_self_edges existsb].
    destruct (audit_wto_self_edges EV g v rest); cbn in *; congruence.
Qed.

(** The ranks traversal returns the corresponding uninstrumented result. *)
Lemma audit_wto_ranks_result {V E} (EV : encoding V) order clock m :
    fst (@audit_wto_ranks_counted V E EV order clock m) =
    snd (fold_left (fun acc v =>
      (Pos.succ (fst acc), Map.set EV v (fst acc) (snd acc))) order (clock, m)).
Proof.
  revert clock m; induction order as [|v rest IH]; intros clock m.
  - reflexivity.
  - cbn [audit_wto_ranks_counted fold_left].
    specialize (IH (Pos.succ clock) (Map.set EV v clock m)).
    destruct (audit_wto_ranks_counted EV rest (Pos.succ clock) (Map.set EV v clock m));
      cbn in *; exact IH.
Qed.

(** The component traversal returns the corresponding uninstrumented result. *)
Lemma audit_wto_component_result {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) ranks recur component :
    fst (audit_wto_component_counted p ranks recur component) =
    wto_component p ranks (fun region => fst (recur region)) component.
Proof.
  destruct component as [|h rest]; [reflexivity|].
  unfold audit_wto_component_counted, wto_component.
  pose proof (@audit_wto_choose_result V E EV ranks rest h) as Hchoose.
  destruct (audit_wto_choose_counted EV ranks rest h) as [header events].
  cbn in Hchoose; rewrite <- Hchoose.
  destruct rest as [|v rest].
  - cbn [audit_wto_choose_counted] in Hchoose.
    unfold wto_self_loop, succ_edges, index_edges.
    destruct (Map.get EV h (out_index p)) as [edges|].
    + pose proof (audit_wto_self_edges_result EV g h edges) as Hself.
      destruct (audit_wto_self_edges EV g h edges) as [self trace]; cbn in Hself.
      rewrite <- Hself; destruct self; reflexivity.
    + reflexivity.
  - pose proof (@audit_wto_remove_result V E EV header (h :: v :: rest)) as Hremove.
    destruct (audit_wto_remove_counted EV header (h :: v :: rest)) as [smaller trace].
    change (smaller = wto_remove EV header (h :: v :: rest)) in Hremove.
    rewrite <- Hremove.
    destruct (recur smaller); reflexivity.
Qed.

(** The components traversal returns the corresponding uninstrumented result. *)
Lemma audit_wto_components_result {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) ranks recur components :
    fst (audit_wto_components_counted p ranks recur components) =
    flat_map (wto_component p ranks (fun region => fst (recur region))) components.
Proof.
  induction components as [|component rest IH].
  - reflexivity.
  - cbn [audit_wto_components_counted flat_map].
    pose proof (audit_wto_component_result p ranks recur component) as Hfirst.
    destruct (audit_wto_component_counted p ranks recur component) as [first here].
    destruct (audit_wto_components_counted p ranks recur rest) as [later events].
    cbn in Hfirst, IH |- *; now rewrite Hfirst, IH.
Qed.

(** The layer traversal returns the corresponding uninstrumented result. *)
Lemma audit_wto_layer_result {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) ranks recur region :
    fst (audit_wto_layer_counted p ranks recur region) =
    wto_unfold p ranks (fun region => fst (recur region)) region.
Proof.
  unfold audit_wto_layer_counted, wto_unfold.
  pose proof (audit_scc_counted_erases EV g p region) as Hscc.
  destruct (audit_scc_within_counted p region) as [result events].
  cbn in Hscc; rewrite <- Hscc, <- rev_alt.
  pose proof (audit_wto_components_result p ranks recur (rev (components result))) as Hcomponents.
  destruct (audit_wto_components_counted p ranks recur (rev (components result))).
  exact Hcomponents.
Qed.

(** A WTO layer depends extensionally on its recursive callback. *)
Lemma audit_wto_unfold_ext {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) ranks first second region :
    (forall part, first part = second part) ->
    wto_unfold p ranks first region = wto_unfold p ranks second region.
Proof.
  intro Hrecur; unfold wto_unfold.
  apply flat_map_ext; intro component.
  unfold wto_component.
  destruct component as [|h rest]; [reflexivity|].
  destruct rest as [|v rest]; [reflexivity|].
  now rewrite Hrecur.
Qed.

(** The iter traversal returns the corresponding uninstrumented result. *)
Lemma audit_wto_iter_result {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) ranks fuel
    (base : list V -> wto V * list (audit_wto_call V E)) plain :
    (forall region, fst (base region) = plain region) ->
    forall region,
      fst (fst (audit_pos_iter
        (fun recur => (audit_wto_layer_counted p ranks recur, @nil (audit_wto_call V E)))
        base fuel) region) =
      Pos.iter (wto_unfold p ranks) plain fuel region.
Proof.
  revert base plain; induction fuel as [fuel IH|fuel IH|]; intros base plain Hbase region.
  - cbn [audit_pos_iter Pos.iter].
    pose proof (IH base plain Hbase) as Hfirst.
    destruct (audit_pos_iter
      (fun recur => (audit_wto_layer_counted p ranks recur, @nil (audit_wto_call V E)))
      base fuel)
      as [middle first].
    pose proof (IH middle (Pos.iter (wto_unfold p ranks) plain fuel) Hfirst) as Hsecond.
    destruct (audit_pos_iter
      (fun recur => (audit_wto_layer_counted p ranks recur, @nil (audit_wto_call V E)))
      middle fuel)
      as [last second].
    cbn in Hsecond |- *; rewrite audit_wto_layer_result.
    apply audit_wto_unfold_ext; exact Hsecond.
  - cbn [audit_pos_iter Pos.iter].
    pose proof (IH base plain Hbase) as Hfirst.
    destruct (audit_pos_iter
      (fun recur => (audit_wto_layer_counted p ranks recur, @nil (audit_wto_call V E)))
      base fuel)
      as [middle first].
    pose proof (IH middle (Pos.iter (wto_unfold p ranks) plain fuel) Hfirst) as Hsecond.
    destruct (audit_pos_iter
      (fun recur => (audit_wto_layer_counted p ranks recur, @nil (audit_wto_call V E)))
      middle fuel)
      as [last second].
    exact (Hsecond region).
  - change (fst (audit_wto_layer_counted p ranks base region) =
      wto_unfold p ranks plain region).
    rewrite audit_wto_layer_result.
    apply audit_wto_unfold_ext; exact Hbase.
Qed.

(** The counted traversal returns the corresponding uninstrumented result. *)
Lemma audit_wto_counted_result {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) : fst (audit_wto_counted p) = wto_of p.
Proof.
  unfold audit_wto_counted, wto_of.
  pose proof (audit_dfs_full_counted_erases p FinSet.empty (Graph.entries g)) as Hdfs.
  destruct (audit_dfs_full_counted p FinSet.empty (Graph.entries g)) as [search events].
  cbn in Hdfs; rewrite <- Hdfs.
  pose proof (@audit_wto_ranks_result V E EV (rpo search) 1%positive Map.empty) as Hranks.
  destruct (audit_wto_ranks_counted EV (rpo search) 1%positive Map.empty) as [ranks rank_events].
  change (ranks = wto_ranks EV (rpo search)) in Hranks; rewrite <- Hranks.
  pose proof (audit_wto_iter_result p ranks (Pos.of_succ_nat (length (rpo search)))
    (fun _ => ([], [])) (fun _ => []) (fun _ => eq_refl) (rpo search)) as Hiter.
  destruct (audit_pos_iter
    (fun recur => (audit_wto_layer_counted p ranks recur, @nil (audit_wto_call V E)))
    (fun _ => ([], [])) (Pos.of_succ_nat (length (rpo search)))) as [run trace].
  cbn in Hiter.
  destruct (run (rpo search)); exact Hiter.
Qed.

(** * Nested traversal erasure *)

(** The nested ranks traversal erases to the corresponding counted computation. *)
Lemma audit_wto_nested_ranks_erases {V E B} (EV : encoding V) (g : Graph.t V E)
    (cb : audit_dfs_callback_model V E B) order clock m :
    audit_dfs_callbacks_erase EV g cb ->
    (fst (audit_wto_nested_ranks cb order clock m),
      map fst (snd (audit_wto_nested_ranks cb order clock m))) =
    @audit_wto_ranks_counted V E EV order clock m.
Proof.
  intros [_ Hencode]; revert clock m.
  induction order as [|v rest IH]; intros clock m; [reflexivity|].
  specialize (Hencode v) as Hvalue.
  destruct (audit_dfs_encode_model cb v) as [code body] eqn:Hcall; cbn in Hvalue; subst code.
  cbn [audit_wto_nested_ranks audit_wto_ranks_counted].
  unfold audit_tarjan_nested_set; rewrite Hcall.
  change (CollectionsTrie.Trie.set (encode EV v) (v, clock) m) with (Map.set EV v clock m).
  pose proof (IH (Pos.succ clock) (Map.set EV v clock m)) as Hrest.
  destruct (audit_wto_nested_ranks cb rest (Pos.succ clock) (Map.set EV v clock m))
    as [result events].
  destruct (audit_wto_ranks_counted EV rest (Pos.succ clock) (Map.set EV v clock m))
    as [result' events'].
  cbn in Hrest |- *; inversion Hrest; reflexivity.
Qed.

(** The nested earlier traversal erases to the corresponding counted computation. *)
Lemma audit_wto_nested_earlier_erases {V E B} (EV : encoding V) (g : Graph.t V E)
    (cb : audit_dfs_callback_model V E B) ranks u v :
    audit_dfs_callbacks_erase EV g cb ->
    (fst (audit_wto_nested_earlier cb ranks u v),
      map fst (snd (audit_wto_nested_earlier cb ranks u v))) =
    @audit_wto_earlier_counted V E EV ranks u v.
Proof.
  intros [_ Hencode].
  specialize (Hencode u) as Hu; specialize (Hencode v) as Hv.
  destruct (audit_dfs_encode_model cb u) as [uc ub] eqn:Huc; cbn in Hu; subst uc.
  destruct (audit_dfs_encode_model cb v) as [vc vb] eqn:Hvc; cbn in Hv; subst vc.
  unfold audit_wto_nested_earlier, audit_tarjan_nested_get, audit_wto_earlier_counted.
  rewrite Huc, Hvc; reflexivity.
Qed.

(** The nested choose traversal erases to the corresponding counted computation. *)
Lemma audit_wto_nested_choose_erases {V E B} (EV : encoding V) (g : Graph.t V E)
    (cb : audit_dfs_callback_model V E B) ranks rest header :
    audit_dfs_callbacks_erase EV g cb ->
    (fst (audit_wto_nested_choose cb ranks rest header),
      map fst (snd (audit_wto_nested_choose cb ranks rest header))) =
    @audit_wto_choose_counted V E EV ranks rest header.
Proof.
  intro Hcallbacks; revert header; induction rest as [|v rest IH]; intro header.
  - reflexivity.
  - cbn [audit_wto_nested_choose audit_wto_choose_counted].
    pose proof (audit_wto_nested_earlier_erases EV g cb ranks header v Hcallbacks) as Hhere.
    destruct (audit_wto_nested_earlier cb ranks header v) as [next here].
    destruct (audit_wto_earlier_counted EV ranks header v) as [next' here'].
    cbn in Hhere; inversion Hhere; subst next' here'.
    specialize (IH next).
    destruct (audit_wto_nested_choose cb ranks rest next) as [result later].
    destruct (audit_wto_choose_counted EV ranks rest next) as [result' later'].
    cbn in IH |- *; inversion IH; subst result' later'.
    now rewrite map_app.
Qed.

(** The nested remove traversal erases to the corresponding counted computation. *)
Lemma audit_wto_nested_remove_erases {V E B} (EV : encoding V) (g : Graph.t V E)
    (cb : audit_dfs_callback_model V E B) header vertices :
    audit_dfs_callbacks_erase EV g cb ->
    (fst (audit_wto_nested_remove cb header vertices),
      map fst (snd (audit_wto_nested_remove cb header vertices))) =
    @audit_wto_remove_counted V E EV header vertices.
Proof.
  intros [_ Hencode]; induction vertices as [|v rest IH]; [reflexivity|].
  specialize (Hencode header) as Hheader; specialize (Hencode v) as Hv.
  destruct (audit_dfs_encode_model cb header) as [hc hb] eqn:Hhc; cbn in Hheader; subst hc.
  destruct (audit_dfs_encode_model cb v) as [vc vb] eqn:Hvc; cbn in Hv; subst vc.
  cbn [audit_wto_nested_remove audit_wto_remove_counted]; rewrite Hhc, Hvc.
  destruct (audit_wto_nested_remove cb header rest) as [tail events].
  destruct (audit_wto_remove_counted EV header rest) as [tail' events'].
  cbn in IH |- *; inversion IH; subst tail' events'.
  destruct (Pos.eqb (encode EV header) (encode EV v)); reflexivity.
Qed.

(** The nested self edges traversal erases to the corresponding counted computation. *)
Lemma audit_wto_nested_self_edges_erases {V E B} (EV : encoding V) (g : Graph.t V E)
    (cb : audit_dfs_callback_model V E B) v edges :
    audit_dfs_callbacks_erase EV g cb ->
    (fst (audit_wto_nested_self_edges cb v edges),
      map fst (snd (audit_wto_nested_self_edges cb v edges))) =
    audit_wto_self_edges EV g v edges.
Proof.
  intros [Htarget Hencode]; induction edges as [|edge rest IH]; [reflexivity|].
  specialize (Hencode v) as Hv; specialize (Htarget edge) as Hedge.
  destruct (audit_dfs_encode_model cb v) as [vc vb] eqn:Hvc; cbn in Hv; subst vc.
  destruct (audit_dfs_target_model cb edge) as [target tb] eqn:Htarget'; cbn in Hedge; subst target.
  specialize (Hencode (Graph.target g edge)) as Hout.
  destruct (audit_dfs_encode_model cb (Graph.target g edge)) as [tc tb'] eqn:Htc;
    cbn in Hout; subst tc.
  cbn [audit_wto_nested_self_edges audit_wto_self_edges]; rewrite Hvc, Htarget', Htc.
  destruct (audit_wto_nested_self_edges cb v rest) as [later events].
  destruct (audit_wto_self_edges EV g v rest) as [later' events'].
  cbn in IH |- *; inversion IH; reflexivity.
Qed.

(** The nested component traversal erases to the corresponding counted computation. *)
Lemma audit_wto_nested_component_erases {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) ranks recur nested component :
    audit_dfs_callbacks_erase EV g cb ->
    (forall region, (fst (nested region), map fst (snd (nested region))) = recur region) ->
    (fst (audit_wto_nested_component p cb ranks nested component),
      map fst (snd (audit_wto_nested_component p cb ranks nested component))) =
    audit_wto_component_counted p ranks recur component.
Proof.
  intros Hcallbacks Hrecur; destruct component as [|h rest]; [reflexivity|].
  unfold audit_wto_nested_component, audit_wto_component_counted.
  pose proof (audit_wto_nested_choose_erases EV g cb ranks rest h Hcallbacks) as Hchoose.
  destruct (audit_wto_nested_choose cb ranks rest h) as [header choose].
  destruct (audit_wto_choose_counted EV ranks rest h) as [header' choose'].
  cbn in Hchoose; inversion Hchoose; subst header' choose'.
  destruct rest as [|v rest].
  - destruct Hcallbacks as [Htarget Hencode].
    specialize (Hencode h) as Hvalue.
    destruct (audit_dfs_encode_model cb h) as [code body] eqn:Hcode; cbn in Hvalue; subst code.
    unfold audit_tarjan_nested_get; rewrite Hcode.
    change (Map.code_get (encode EV h) (out_index p)) with (Map.get EV h (out_index p)).
    destruct (Map.get EV h (out_index p)) as [edges|] eqn:Hedges.
    + pose proof (audit_wto_nested_self_edges_erases EV g cb h edges (conj Htarget Hencode))
        as Hself.
      destruct (audit_wto_nested_self_edges cb h edges) as [self trace].
      destruct (audit_wto_self_edges EV g h edges) as [self' trace'].
      cbn in Hself; inversion Hself; subst self' trace'.
      destruct self; cbn; rewrite ?map_app; cbn; rewrite ?map_app; cbn;
        rewrite ?map_app; reflexivity.
    + cbn [audit_wto_nested_self_edges audit_wto_self_edges].
      cbn; rewrite ?map_app; cbn; rewrite ?map_app; reflexivity.
  - pose proof (audit_wto_nested_remove_erases EV g cb header (h :: v :: rest) Hcallbacks)
      as Hremove.
    destruct (audit_wto_nested_remove cb header (h :: v :: rest)) as [smaller trace].
    destruct (audit_wto_remove_counted EV header (h :: v :: rest)) as [smaller' trace'].
    cbn in Hremove; inversion Hremove; subst smaller' trace'.
    specialize (Hrecur smaller).
    destruct (nested smaller) as [inside events].
    destruct (recur smaller) as [inside' events'].
    cbn in Hrecur; inversion Hrecur; subst inside' events'.
    cbn; rewrite ?map_app; cbn; rewrite ?map_app; reflexivity.
Qed.

(** The nested components traversal erases to the corresponding counted computation. *)
Lemma audit_wto_nested_components_erases {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) ranks recur nested components :
    audit_dfs_callbacks_erase EV g cb ->
    (forall region, (fst (nested region), map fst (snd (nested region))) = recur region) ->
    (fst (audit_wto_nested_components p cb ranks nested components),
      map fst (snd (audit_wto_nested_components p cb ranks nested components))) =
    audit_wto_components_counted p ranks recur components.
Proof.
  intros Hcallbacks Hrecur; induction components as [|component rest IH]; [reflexivity|].
  cbn [audit_wto_nested_components audit_wto_components_counted].
  pose proof (audit_wto_nested_component_erases p cb ranks recur nested component Hcallbacks Hrecur)
    as Hfirst.
  destruct (audit_wto_nested_component p cb ranks nested component) as [first here].
  destruct (audit_wto_component_counted p ranks recur component) as [first' here'].
  cbn in Hfirst; inversion Hfirst; subst first' here'.
  destruct (audit_wto_nested_components p cb ranks nested rest) as [later events].
  destruct (audit_wto_components_counted p ranks recur rest) as [later' events'].
  cbn in IH; inversion IH; subst later' events'.
  cbn; rewrite ?map_app; cbn; rewrite ?map_app; reflexivity.
Qed.

(** The nested layer traversal erases to the corresponding counted computation. *)
Lemma audit_wto_nested_layer_erases {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) ranks recur nested region :
    audit_dfs_callbacks_erase EV g cb ->
    (forall region, (fst (nested region), map fst (snd (nested region))) = recur region) ->
    (fst (audit_wto_nested_layer p cb ranks nested region),
      map fst (snd (audit_wto_nested_layer p cb ranks nested region))) =
    audit_wto_layer_counted p ranks recur region.
Proof.
  intros Hcallbacks Hrecur; unfold audit_wto_nested_layer, audit_wto_layer_counted.
  pose proof (audit_scc_nested_erases p cb region Hcallbacks) as Hscc.
  destruct (audit_scc_within_nested_counted p cb region) as [result events].
  destruct (audit_scc_within_counted p region) as [result' events'].
  cbn in Hscc; inversion Hscc; subst result' events'.
  pose proof (audit_wto_nested_components_erases p cb ranks recur nested
    (rev (components result)) Hcallbacks Hrecur) as Hcomponents.
  destruct (audit_wto_nested_components p cb ranks nested (rev (components result)))
    as [output trace].
  destruct (audit_wto_components_counted p ranks recur (rev (components result)))
    as [output' trace'].
  cbn in Hcomponents; inversion Hcomponents; subst output' trace'.
  cbn; rewrite !map_app, !map_map; reflexivity.
Qed.

(** The nested iter traversal erases to the corresponding counted computation. *)
Lemma audit_wto_nested_iter_erases {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) ranks fuel
    (nested : list V -> wto V * list (audit_wto_nested_event V E B))
    (counted : list V -> wto V * list (audit_wto_call V E)) :
    audit_dfs_callbacks_erase EV g cb ->
    (forall region, (fst (nested region), map fst (snd (nested region))) = counted region) ->
    forall region,
      let '(nrun, nevents) := audit_pos_iter
        (fun recur => (audit_wto_nested_layer p cb ranks recur, @nil (audit_wto_call V E)))
        nested fuel in
      let '(crun, cevents) := audit_pos_iter
        (fun recur => (audit_wto_layer_counted p ranks recur, @nil (audit_wto_call V E)))
        counted fuel in
      (fst (nrun region), map fst (snd (nrun region))) = crun region /\ nevents = cevents.
Proof.
  intro Hcallbacks; revert nested counted.
  induction fuel as [fuel IH|fuel IH|]; intros nested counted Hbase region.
  - cbn [audit_pos_iter].
    pose proof (fun r => IH nested counted Hbase r) as Hfirst.
    destruct (audit_pos_iter
      (fun recur => (audit_wto_nested_layer p cb ranks recur, @nil (audit_wto_call V E)))
      nested fuel) as [nm ne].
    destruct (audit_pos_iter
      (fun recur => (audit_wto_layer_counted p ranks recur, @nil (audit_wto_call V E)))
      counted fuel) as [cm ce].
    assert (Hmiddle : forall r, (fst (nm r), map fst (snd (nm r))) = cm r).
    { intro r; exact (proj1 (Hfirst r)). }
    pose proof (fun r => IH nm cm Hmiddle r) as Hsecond.
    destruct (audit_pos_iter
      (fun recur => (audit_wto_nested_layer p cb ranks recur, @nil (audit_wto_call V E)))
      nm fuel) as [nl ne'].
    destruct (audit_pos_iter
      (fun recur => (audit_wto_layer_counted p ranks recur, @nil (audit_wto_call V E)))
      cm fuel) as [cl ce'].
    split.
    + apply audit_wto_nested_layer_erases; [exact Hcallbacks|].
      intro r; exact (proj1 (Hsecond r)).
    + rewrite (proj2 (Hfirst region)), (proj2 (Hsecond region)); reflexivity.
  - cbn [audit_pos_iter].
    pose proof (fun r => IH nested counted Hbase r) as Hfirst.
    destruct (audit_pos_iter
      (fun recur => (audit_wto_nested_layer p cb ranks recur, @nil (audit_wto_call V E)))
      nested fuel) as [nm ne].
    destruct (audit_pos_iter
      (fun recur => (audit_wto_layer_counted p ranks recur, @nil (audit_wto_call V E)))
      counted fuel) as [cm ce].
    assert (Hmiddle : forall r, (fst (nm r), map fst (snd (nm r))) = cm r).
    { intro r; exact (proj1 (Hfirst r)). }
    pose proof (fun r => IH nm cm Hmiddle r) as Hsecond.
    destruct (audit_pos_iter
      (fun recur => (audit_wto_nested_layer p cb ranks recur, @nil (audit_wto_call V E)))
      nm fuel) as [nl ne'].
    destruct (audit_pos_iter
      (fun recur => (audit_wto_layer_counted p ranks recur, @nil (audit_wto_call V E)))
      cm fuel) as [cl ce'].
    split; [exact (proj1 (Hsecond region))|].
    rewrite (proj2 (Hfirst region)), (proj2 (Hsecond region)); reflexivity.
  - cbn [audit_pos_iter].
    split; [apply audit_wto_nested_layer_erases; assumption|reflexivity].
Qed.

(** Erasing nested callback bodies recovers the counted computation. *)
Lemma audit_wto_nested_erases {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) :
    audit_dfs_callbacks_erase EV g cb ->
    (fst (audit_wto_nested_counted p cb), map fst (snd (audit_wto_nested_counted p cb))) =
    audit_wto_counted p.
Proof.
  intro Hcallbacks; unfold audit_wto_nested_counted, audit_wto_counted.
  pose proof (audit_dfs_nested_counted_erases p cb FinSet.empty (Graph.entries g) Hcallbacks)
    as Hdfs.
  destruct (audit_dfs_nested_counted p cb FinSet.empty (Graph.entries g)) as [search dfs_events].
  destruct (audit_dfs_full_counted p FinSet.empty (Graph.entries g)) as [search' dfs_events'].
  cbn in Hdfs; inversion Hdfs; subst search' dfs_events'.
  pose proof (audit_wto_nested_ranks_erases EV g cb (rpo search) 1%positive Map.empty Hcallbacks)
    as Hranks.
  destruct (audit_wto_nested_ranks cb (rpo search) 1%positive Map.empty) as [ranks rank_events].
  destruct (audit_wto_ranks_counted EV (rpo search) 1%positive Map.empty)
    as [ranks' rank_events'].
  cbn in Hranks; inversion Hranks; subst ranks' rank_events'.
  pose proof (audit_wto_nested_iter_erases p cb ranks (Pos.of_succ_nat (length (rpo search)))
    (fun _ => ([], [])) (fun _ => ([], [])) Hcallbacks (fun _ => eq_refl) (rpo search)) as Hiter.
  destruct (audit_pos_iter
    (fun recur => (audit_wto_nested_layer p cb ranks recur, @nil (audit_wto_call V E)))
    (fun _ => ([], [])) (Pos.of_succ_nat (length (rpo search)))) as [nrun nevents].
  destruct (audit_pos_iter
    (fun recur => (audit_wto_layer_counted p ranks recur, @nil (audit_wto_call V E)))
    (fun _ => ([], [])) (Pos.of_succ_nat (length (rpo search)))) as [crun cevents].
  destruct Hiter as [Hrun Hevents]; subst cevents.
  destruct (nrun (rpo search)) as [result trace].
  destruct (crun (rpo search)) as [result' trace'].
  cbn in Hrun; inversion Hrun; subst result' trace'.
  cbn; repeat (rewrite ?map_app, ?map_map; cbn); reflexivity.
Qed.

(** * Source traversal erasure *)

(** The source scc agrees with the nested computation. *)
Lemma audit_wto_source_scc_agrees {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) region :
    audit_scc_source_counted p cb region =
      audit_scc_within_nested_counted p (audit_graph_capture_callbacks cb) region.
Proof.
  unfold audit_scc_source_counted, audit_scc_within_nested_counted, tarjan_result.
  destruct (audit_tarjan_nested_region (audit_graph_capture_callbacks cb) region FinSet.empty)
    as [keep events].
  destruct (audit_tarjan_nested_roots p (audit_graph_capture_callbacks cb) keep region
    tarjan_initial).
  now rewrite <- !rev_alt.
Qed.

(** The source dfs agrees with the nested computation. *)
Lemma audit_wto_source_dfs_agrees {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) blocked roots :
    audit_dfs_source_counted p cb blocked roots =
      audit_dfs_nested_counted p (audit_graph_capture_callbacks cb) blocked roots.
Proof.
  unfold audit_dfs_source_counted, audit_dfs_nested_counted.
  destruct (audit_dfs_nested_roots p (audit_graph_capture_callbacks cb) blocked roots dfs_initial).
  now rewrite <- !rev_alt.
Qed.

(** The source layer agrees with the nested computation. *)
Lemma audit_wto_source_layer_agrees {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) ranks recur region :
    audit_wto_source_layer p cb ranks recur region =
      audit_wto_nested_layer p (audit_graph_capture_callbacks cb) ranks recur region.
Proof.
  unfold audit_wto_source_layer, audit_wto_nested_layer.
  rewrite audit_wto_source_scc_agrees.
  destruct (audit_scc_within_nested_counted p (audit_graph_capture_callbacks cb) region).
  rewrite <- rev_alt.
  reflexivity.
Qed.

(** The counted contract implies the nested contract by event erasure. *)
Lemma audit_wto_nested_from_counted :
    audit_wto_counted_statement -> audit_wto_nested_statement.
Proof.
  intros Hcounted V E B EV g p cb weight Hcallbacks.
  pose proof (audit_wto_nested_erases p cb Hcallbacks) as Herase.
  pose proof (Hcounted V E EV g p) as Hbound.
  destruct (audit_wto_nested_counted p cb) as [result events].
  destruct (audit_wto_counted p) as [counted trace].
  change ((result, map fst events) = (counted, trace)) in Herase.
  inversion Herase; subst counted trace.
  change (result = wto_of p /\ length (map fst events) <= audit_wto_input_event_bound p /\
    audit_wto_model_work EV (map fst events) <= audit_wto_input_budget EV g p) in Hbound.
  destruct Hbound as [Hresult [Hlength Hwork]].
  rewrite length_map in Hlength.
  split; [exact Hresult|].
  split; [reflexivity|].
  split; [exact Hlength|].
  unfold audit_wto_nested_total_work; now apply Nat.add_le_mono_r.
Qed.

(** Pointwise equal recursive callbacks give equal nested component traversals. *)
Lemma audit_wto_nested_components_ext {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) ranks first second components :
    (forall region, first region = second region) ->
    audit_wto_nested_components p cb ranks first components =
      audit_wto_nested_components p cb ranks second components.
Proof.
  intro Hrecur; induction components as [|component rest IH]; [reflexivity|].
  cbn [audit_wto_nested_components].
  assert (Hcomponent : audit_wto_nested_component p cb ranks first component =
    audit_wto_nested_component p cb ranks second component).
  { unfold audit_wto_nested_component; destruct component as [|h tail]; [reflexivity|].
    destruct (audit_wto_nested_choose cb ranks tail h) as [head chosen].
    destruct tail as [|v tail]; [reflexivity|].
    destruct (audit_wto_nested_remove cb head (h :: v :: tail)) as [smaller removed].
    now rewrite Hrecur. }
  now rewrite Hcomponent, IH.
Qed.

(** Pointwise equal recursive callbacks give equal nested layers. *)
Lemma audit_wto_nested_layer_ext {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) ranks first second region :
    (forall part, first part = second part) ->
    audit_wto_nested_layer p cb ranks first region =
      audit_wto_nested_layer p cb ranks second region.
Proof.
  intro Hrecur; unfold audit_wto_nested_layer.
  destruct (audit_scc_within_nested_counted p cb region) as [scc events].
  now rewrite (audit_wto_nested_components_ext p cb ranks first second _ Hrecur).
Qed.

(** The source iter agrees with the nested computation. *)
Lemma audit_wto_source_iter_agrees {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) ranks fuel
    (source nested : list V -> wto V *
      list (audit_wto_nested_event V E (audit_graph_callback_capture V E B))) :
    (forall region, source region = nested region) ->
    forall region,
      let '(srun, sevents) := audit_pos_iter
        (fun recur => (audit_wto_source_layer p cb ranks recur, @nil (audit_wto_call V E)))
        source fuel in
      let '(nrun, nevents) := audit_pos_iter
        (fun recur => (audit_wto_nested_layer p (audit_graph_capture_callbacks cb) ranks recur,
          @nil (audit_wto_call V E))) nested fuel in
      srun region = nrun region /\ sevents = nevents.
Proof.
  revert source nested; induction fuel as [fuel IH|fuel IH|]; intros source nested Hbase region.
  - cbn [audit_pos_iter].
    pose proof (fun r => IH source nested Hbase r) as Hfirst.
    destruct (audit_pos_iter
      (fun recur => (audit_wto_source_layer p cb ranks recur, @nil (audit_wto_call V E)))
      source fuel) as [sm se].
    destruct (audit_pos_iter
      (fun recur => (audit_wto_nested_layer p (audit_graph_capture_callbacks cb) ranks recur,
        @nil (audit_wto_call V E))) nested fuel) as [nm ne].
    assert (Hmiddle : forall r, sm r = nm r) by (intro r; exact (proj1 (Hfirst r))).
    pose proof (fun r => IH sm nm Hmiddle r) as Hsecond.
    destruct (audit_pos_iter
      (fun recur => (audit_wto_source_layer p cb ranks recur, @nil (audit_wto_call V E)))
      sm fuel) as [sl se'].
    destruct (audit_pos_iter
      (fun recur => (audit_wto_nested_layer p (audit_graph_capture_callbacks cb) ranks recur,
        @nil (audit_wto_call V E))) nm fuel) as [nl ne'].
    split.
    + rewrite audit_wto_source_layer_agrees.
      apply audit_wto_nested_layer_ext; intro r; exact (proj1 (Hsecond r)).
    + rewrite (proj2 (Hfirst region)), (proj2 (Hsecond region)); reflexivity.
  - cbn [audit_pos_iter].
    pose proof (fun r => IH source nested Hbase r) as Hfirst.
    destruct (audit_pos_iter
      (fun recur => (audit_wto_source_layer p cb ranks recur, @nil (audit_wto_call V E)))
      source fuel) as [sm se].
    destruct (audit_pos_iter
      (fun recur => (audit_wto_nested_layer p (audit_graph_capture_callbacks cb) ranks recur,
        @nil (audit_wto_call V E))) nested fuel) as [nm ne].
    assert (Hmiddle : forall r, sm r = nm r) by (intro r; exact (proj1 (Hfirst r))).
    pose proof (fun r => IH sm nm Hmiddle r) as Hsecond.
    destruct (audit_pos_iter
      (fun recur => (audit_wto_source_layer p cb ranks recur, @nil (audit_wto_call V E)))
      sm fuel) as [sl se'].
    destruct (audit_pos_iter
      (fun recur => (audit_wto_nested_layer p (audit_graph_capture_callbacks cb) ranks recur,
        @nil (audit_wto_call V E))) nm fuel) as [nl ne'].
    split; [exact (proj1 (Hsecond region))|].
    rewrite (proj2 (Hfirst region)), (proj2 (Hsecond region)); reflexivity.
  - cbn [audit_pos_iter].
    split; [|reflexivity].
    rewrite audit_wto_source_layer_agrees.
    apply audit_wto_nested_layer_ext; exact Hbase.
Qed.

(** The source agrees with the nested computation. *)
Lemma audit_wto_source_agrees {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) :
    audit_wto_source_counted p cb =
      audit_wto_nested_counted p (audit_graph_capture_callbacks cb).
Proof.
  unfold audit_wto_source_counted, audit_wto_nested_counted.
  rewrite audit_wto_source_dfs_agrees.
  destruct (audit_dfs_nested_counted p (audit_graph_capture_callbacks cb) FinSet.empty
    (Graph.entries g)) as [search events].
  change (rev_append (postorder search) []) with (rpo search).
  destruct (audit_wto_nested_ranks (audit_graph_capture_callbacks cb) (rpo search) 1%positive
    Map.empty) as [ranks rank_events].
  pose proof (audit_wto_source_iter_agrees p cb ranks (Pos.of_succ_nat (length (rpo search)))
    (fun _ => ([], [])) (fun _ => ([], [])) (fun _ => eq_refl) (rpo search)) as Hiter.
  destruct (audit_pos_iter
    (fun recur => (audit_wto_source_layer p cb ranks recur, @nil (audit_wto_call V E)))
    (fun _ => ([], [])) (Pos.of_succ_nat (length (rpo search)))) as [srun sevents].
  destruct (audit_pos_iter
    (fun recur => (audit_wto_nested_layer p (audit_graph_capture_callbacks cb) ranks recur,
      @nil (audit_wto_call V E))) (fun _ => ([], []))
    (Pos.of_succ_nat (length (rpo search)))) as [nrun nevents].
  destruct Hiter as [Hrun Hevents]; subst nevents.
  rewrite Hrun; reflexivity.
Qed.

(** Erasing source callback bodies recovers the counted computation. *)
Lemma audit_wto_source_erases {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) :
    audit_dfs_callbacks_erase EV g cb ->
    (fst (audit_wto_source_counted p cb), map fst (snd (audit_wto_source_counted p cb))) =
    audit_wto_counted p.
Proof.
  intro Hcallbacks; rewrite audit_wto_source_agrees.
  apply audit_wto_nested_erases.
  apply audit_graph_capture_callbacks_erases_holds; exact Hcallbacks.
Qed.

(** * Original-region bounds *)

(** Every member returned by SCC decomposition belongs to its input region. *)
Lemma audit_wto_scc_members_in_region {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) region :
    incl (concat (components (scc_within p region))) region.
Proof.
  pose proof (tarjan_fold_bookkeeping EV g p (FinSet.of_list EV region) region
    tarjan_initial (tarjan_initial_bookkeeping EV)) as Hbook.
  assert (Hdomain : tarjan_in_region EV (FinSet.of_list EV region)
    (fold_left (tarjan_root p (FinSet.of_list EV region)) region tarjan_initial)).
  { apply tarjan_fold_in_region.
    - intros v d Hfalse; cbn [tarjan_initial disc] in Hfalse.
      rewrite Map.get_empty in Hfalse; discriminate.
    - intros v Hin; apply FinSet.of_list_spec; exact Hin. }
  intro x; intro Hin.
  unfold scc_within in Hin; unfold tarjan_result in Hin.
  cbn [components] in Hin; rewrite <- rev_alt in Hin.
  apply (proj1 (tarjan_concat_rev_in _ _)) in Hin.
  apply (proj1 (FinSet.of_list_spec EV x region)).
  assert (Hmember : In x (pending (fold_left (tarjan_root p (FinSet.of_list EV region))
    region tarjan_initial) ++ concat (components (emitted (fold_left
      (tarjan_root p (FinSet.of_list EV region)) region tarjan_initial))))).
  { apply in_or_app; right; exact Hin. }
  apply (tarjan_book_disc _ _ Hbook) in Hmember.
  destruct Hmember as [number Hget].
  exact (Hdomain x number Hget).
Qed.

(** The concatenated SCC members have length at most that of the input region. *)
Lemma audit_wto_scc_size_bound {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) region :
    length (concat (components (scc_within p region))) <= length region.
Proof.
  apply NoDup_incl_length.
  - exact (proj1 (scc_within_indexes EV g p region)).
  - apply audit_wto_scc_members_in_region.
Qed.

(** The choose traversal has the stated event count. *)
Lemma audit_wto_choose_event_count {V E} (EV : encoding V) ranks rest header :
    length (snd (@audit_wto_choose_counted V E EV ranks rest header)) = 1 + 4 * length rest.
Proof.
  revert header; induction rest as [|v rest IH]; intro header; [reflexivity|].
  cbn [audit_wto_choose_counted].
  destruct (audit_wto_earlier_counted EV ranks header v) as [next here] eqn:Hhere.
  assert (Hlength : length here = 3).
  { unfold audit_wto_earlier_counted in Hhere.
    repeat match type of Hhere with
    | context [match ?value with
      | Some _ => _
      | None => _
      end] => destruct value
    end;
    destruct (Pos.leb _ _); inversion Hhere; reflexivity. }
  specialize (IH next).
  destruct (audit_wto_choose_counted EV ranks rest next) as [result events].
  cbn in IH |- *; rewrite length_app, Hlength; lia.
Qed.

(** The remove traversal has the stated event count. *)
Lemma audit_wto_remove_event_count {V E} (EV : encoding V) header vertices :
    length (snd (@audit_wto_remove_counted V E EV header vertices)) = 1 + 4 * length vertices.
Proof.
  induction vertices as [|v rest IH]; [reflexivity|].
  cbn [audit_wto_remove_counted].
  destruct (audit_wto_remove_counted EV header rest) as [result events].
  destruct (Pos.eqb (encode EV header) (encode EV v)); cbn in IH |- *; lia.
Qed.

(** The self edges traversal has the stated event count. *)
Lemma audit_wto_self_edges_event_count {V E} (EV : encoding V) (g : Graph.t V E) v edges :
    length (snd (audit_wto_self_edges EV g v edges)) = 1 + 5 * length edges.
Proof.
  induction edges as [|edge rest IH]; [reflexivity|].
  cbn [audit_wto_self_edges].
  destruct (audit_wto_self_edges EV g v rest) as [result events]; cbn in IH |- *; lia.
Qed.

(** The SCC decomposition has at most one nonempty component per input vertex. *)
Lemma audit_wto_component_count_bound {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) region :
    length (components (scc_within p region)) <= length region.
Proof.
  pose proof (scc_within_indexes EV g p region) as Hindexes.
  destruct Hindexes as [_ [Hnonempty _]].
  pose proof (audit_wto_scc_size_bound EV g p region) as Hsize.
  set (parts := components (scc_within p region)) in *.
  assert (Hparts : length parts <= length (concat parts)).
  { clear Hsize; induction parts as [|part rest IH]; [reflexivity|].
    assert (Hpart : part <> []).
    { apply Hnonempty; left; reflexivity. }
    assert (Hrest : forall c, In c rest -> c <> []).
    { intros c Hin; apply Hnonempty; right; exact Hin. }
    specialize (IH Hrest).
    destruct part as [|head tail]; [contradiction|].
    cbn [concat length]; rewrite length_app; cbn; lia. }
  lia.
Qed.

(** The ranks traversal has the stated event count. *)
Lemma audit_wto_ranks_event_count {V E} (EV : encoding V) order clock m :
    length (snd (@audit_wto_ranks_counted V E EV order clock m)) = 1 + 3 * length order.
Proof.
  revert clock m; induction order as [|v rest IH]; intros clock m; [reflexivity|].
  cbn [audit_wto_ranks_counted].
  specialize (IH (Pos.succ clock) (Map.set EV v clock m)).
  destruct (audit_wto_ranks_counted EV rest (Pos.succ clock) (Map.set EV v clock m))
    as [result events].
  cbn in IH |- *; lia.
Qed.

(** Every indexed row length is bounded by the maximum outgoing length. *)
Lemma audit_wto_max_out_member {V E} (rows : list (V * list E)) row :
    In row rows -> length (snd row) <=
      fold_right (fun row n => Nat.max (length (snd row)) n) 0 rows.
Proof.
  induction rows as [|first rest IH]; intro Hin; [contradiction|].
  destruct Hin as [Heq|Hin].
  - subst first; cbn; apply Nat.le_max_l.
  - cbn; eapply Nat.le_trans; [apply IH; exact Hin|apply Nat.le_max_r].
Qed.

(** Every retrieved adjacency list fits the indexed maximum outgoing length. *)
Lemma audit_wto_out_length_bound {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) v edges :
    Map.get EV v (out_index p) = Some edges -> length edges <= audit_wto_input_max_out p.
Proof.
  unfold Map.get, Map.code_get.
  destruct (CollectionsTrie.Trie.get (encode EV v) (out_index p)) as [[stored output]|]
    eqn:Hget; cbn; intro Hresult; [|discriminate].
  inversion Hresult; subst output; unfold audit_wto_input_max_out.
  apply (audit_wto_max_out_member _ (stored, edges)).
  unfold Map.elements; apply in_map_iff.
  exists (encode EV v, (stored, edges)); split; [reflexivity|].
  apply CollectionsTrie.Trie.elements_complete; exact Hget.
Qed.

(** The actual DFS reverse postorder fits the input-derived order bound. *)
Lemma audit_wto_order_length_bound {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) :
    length (rpo (dfs p FinSet.empty (Graph.entries g))) <= audit_wto_input_order_bound p.
Proof.
  pose proof (audit_dfs_roots_clock_bound p FinSet.empty (Graph.entries g) dfs_initial)
    as [_ Hclock].
  assert (Hinit : audit_dfs_list_clock_invariant (@dfs_initial V E)).
  { unfold audit_dfs_list_clock_invariant, dfs_initial; cbn; lia. }
  pose proof (audit_dfs_roots_list_clock p FinSet.empty (Graph.entries g) dfs_initial Hinit)
    as [_ Hlength].
  unfold rpo, dfs, audit_wto_input_order_bound.
  rewrite <- rev_alt, length_rev.
  cbn [postorder]; rewrite <- rev_alt, length_rev.
  cbn [dfs_initial] in Hclock; cbn in Hclock; lia.
Qed.

(** The component traversal satisfies the stated size bound. *)
Lemma audit_wto_component_size_bound {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) ranks recur component bound :
    (forall region, length region <= length component ->
      length (fst (recur region)) <= bound /\ length (snd (recur region)) <= bound) ->
    length (fst (audit_wto_component_counted p ranks recur component)) <= bound + 2 /\
    length (snd (audit_wto_component_counted p ranks recur component)) <=
      bound + 8 + 8 * length component + 5 * audit_wto_input_max_out p.
Proof.
  intro Hrecur; destruct component as [|h rest].
  - cbn [audit_wto_component_counted]; cbn; split; lia.
  - unfold audit_wto_component_counted.
    pose proof (@audit_wto_choose_event_count V E EV ranks rest h) as Hchoose.
    destruct (audit_wto_choose_counted EV ranks rest h) as [header choose].
    cbn in Hchoose; destruct rest as [|v rest].
    + cbn in Hchoose.
      destruct (Map.get EV h (out_index p)) as [edges|] eqn:Hedges.
      * pose proof (audit_wto_out_length_bound p h edges Hedges) as Hout.
        pose proof (audit_wto_self_edges_event_count EV g h edges) as Hself.
        destruct (audit_wto_self_edges EV g h edges) as [self events].
        cbn in Hself |- *; rewrite length_app; cbn; destruct self; cbn;
          rewrite ?length_app; cbn; split; lia.
      * cbn [audit_wto_self_edges]; cbn; rewrite ?length_app; cbn; split; lia.
    + pose proof (@audit_wto_remove_event_count V E EV header (h :: v :: rest)) as Hremove.
      destruct (audit_wto_remove_counted EV header (h :: v :: rest)) as [smaller remove_events]
        eqn:Hremove_eq.
      assert (Hsize : length smaller <= length (h :: v :: rest)).
      { pose proof (@audit_wto_remove_result V E EV header (h :: v :: rest)) as Hresult.
        rewrite Hremove_eq in Hresult.
        change (smaller = wto_remove EV header (h :: v :: rest)) in Hresult.
        rewrite Hresult.
        unfold wto_remove; apply filter_length_le. }
      specialize (Hrecur smaller Hsize).
      destruct (recur smaller) as [inside events].
      cbn in Hrecur, Hremove, Hchoose |- *; rewrite !length_app; cbn;
        rewrite ?length_app; cbn; split; lia.
Qed.

(** The components traversal satisfies the stated size bound. *)
Lemma audit_wto_components_size_bound {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) ranks recur components bound :
    (forall region, length region <= length (concat components) ->
      length (fst (recur region)) <= bound /\
      length (snd (recur region)) <= bound) ->
    length (fst (audit_wto_components_counted p ranks recur components)) <=
      length components * (bound + 2) /\
    length (snd (audit_wto_components_counted p ranks recur components)) <=
      1 + length components * (bound + 10 + 5 * audit_wto_input_max_out p) +
        8 * length (concat components).
Proof.
  induction components as [|component rest IH]; intro Hrecur.
  - cbn [audit_wto_components_counted]; cbn; split; lia.
  - cbn [audit_wto_components_counted].
    assert (Hcomponent_recur : forall region, length region <= length component ->
      length (fst (recur region)) <= bound /\ length (snd (recur region)) <= bound).
    { intros region Hlen; apply Hrecur. cbn; rewrite length_app; lia. }
    pose proof (audit_wto_component_size_bound p ranks recur component bound Hcomponent_recur)
      as Hfirst.
    assert (Hrest_recur : forall region, length region <= length (concat rest) ->
      length (fst (recur region)) <= bound /\ length (snd (recur region)) <= bound).
    { intros region Hlen; apply Hrecur. cbn; rewrite length_app; lia. }
    specialize (IH Hrest_recur).
    destruct (audit_wto_component_counted p ranks recur component) as [first here].
    destruct (audit_wto_components_counted p ranks recur rest) as [later events].
    cbn in Hfirst, IH |- *; rewrite !length_app; cbn; rewrite ?length_app; cbn.
    split; nia.
Qed.

(** The layer traversal satisfies the stated size bound. *)
Lemma audit_wto_layer_size_bound {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) ranks recur region bound :
    (forall part, length part <= length region ->
      length (fst (recur part)) <= bound /\ length (snd (recur part)) <= bound) ->
    length (fst (audit_wto_layer_counted p ranks recur region)) <=
      length region * (bound + 2) /\
    length (snd (audit_wto_layer_counted p ranks recur region)) <=
      audit_tarjan_input_event_bound p region + 2 +
      length region * (bound + 18 + 5 * audit_wto_input_max_out p).
Proof.
  intro Hrecur; unfold audit_wto_layer_counted.
  pose proof (audit_scc_counted_erases EV g p region) as Hscc.
  pose proof (audit_scc_counted_event_bound p region) as Hcount.
  destruct (audit_scc_within_counted p region) as [scc events].
  change (scc = scc_within p region) in Hscc; subst scc.
  change (length events <= audit_tarjan_input_event_bound p region) in Hcount.
  pose proof (audit_wto_scc_size_bound EV g p region) as Hsize.
  pose proof (audit_wto_component_count_bound EV g p region) as Hparts.
  pose proof (Permutation_length (tarjan_concat_rev (components (scc_within p region)))) as Hrev.
  assert (Hcomponent_recur : forall part,
    length part <= length (concat (rev (components (scc_within p region)))) ->
    length (fst (recur part)) <= bound /\ length (snd (recur part)) <= bound).
  { intros part Hlen; apply Hrecur; rewrite Hrev in Hlen; lia. }
  pose proof (audit_wto_components_size_bound p ranks recur
    (rev (components (scc_within p region))) bound Hcomponent_recur) as Hcomponents.
  rewrite length_rev in Hcomponents.
  rewrite Hrev in Hcomponents.
  destruct (audit_wto_components_counted p ranks recur (rev (components (scc_within p region))))
    as [result trace].
  change (length result <= length (components (scc_within p region)) * (bound + 2) /\
    length trace <= 1 + length (components (scc_within p region)) *
      (bound + 10 + 5 * audit_wto_input_max_out p) +
      8 * length (concat (components (scc_within p region)))) in Hcomponents.
  cbn [fst snd]; rewrite !length_app, length_map; cbn [length].
  set (n := length region) in *.
  set (m := audit_wto_input_max_out p) in *.
  set (s := audit_tarjan_input_event_bound p region) in *.
  split; nia.
Qed.

(** The remove traversal satisfies the stated size bound. *)
Lemma audit_wto_remove_size_bound {V} (EV : encoding V) header vertices :
    length (wto_remove EV header vertices) <= length vertices.
Proof.
  unfold wto_remove; apply filter_length_le.
Qed.

(** The SCC input event bound grows monotonically with the region size. *)
Lemma audit_wto_scc_event_envelope {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) region n :
    length region <= n ->
    audit_tarjan_input_event_bound p region <=
      (3 + n * (12 + 12 * S (Pos.to_nat (fuel p)))) *
        (12 + 6 * S (n * S (Pos.to_nat (fuel p)))).
Proof.
  intro Hlength; unfold audit_tarjan_input_event_bound.
  apply Nat.mul_le_mono; nia.
Qed.

(** The layer traversal preserves the stated traversal envelope. *)
Lemma audit_wto_layer_envelope {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) ranks recur n bound region :
    length region <= n ->
    (forall part, length part <= n ->
      length (fst (recur part)) <= bound /\ length (snd (recur part)) <= bound) ->
    length (fst (audit_wto_layer_counted p ranks recur region)) <=
      n * (bound + 2) /\
    length (snd (audit_wto_layer_counted p ranks recur region)) <=
      (3 + n * (12 + 12 * S (Pos.to_nat (fuel p)))) *
        (12 + 6 * S (n * S (Pos.to_nat (fuel p)))) + 2 +
      n * (bound + 18 + 5 * audit_wto_input_max_out p).
Proof.
  intros Hlength Hrecur.
  pose proof (audit_wto_layer_size_bound p ranks recur region bound) as Hlayer.
  assert (Hlocal : forall part, length part <= length region ->
    length (fst (recur part)) <= bound /\ length (snd (recur part)) <= bound).
  { intros part Hpart; apply Hrecur; lia. }
  specialize (Hlayer Hlocal).
  pose proof (audit_wto_scc_event_envelope p region n Hlength) as Hscc.
  set (s := audit_tarjan_input_event_bound p region) in *.
  set (m := audit_wto_input_max_out p) in *.
  set (f := S (Pos.to_nat (fuel p))) in *.
  destruct Hlayer; split; nia.
Qed.

(** A uniform allowance for one WTO layer, excluding recursive callback work. *)
Definition audit_wto_layer_allowance {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) n : nat :=
  (3 + n * (12 + 12 * S (Pos.to_nat (fuel p)))) *
    (12 + 6 * S (n * S (Pos.to_nat (fuel p)))) + 2 +
  n * (18 + 5 * audit_wto_input_max_out p) + 2.

(** The iter traversal preserves the stated traversal envelope. *)
Lemma audit_wto_iter_envelope {V T C} (n allowance : nat)
    (step : (list V -> list T * list C) -> list V -> list T * list C)
    (base : list V -> list T * list C) initial fuel :
    (forall run bound region, length region <= n ->
      (forall part, length part <= n ->
        length (fst (run part)) <= bound /\ length (snd (run part)) <= bound) ->
      length (fst (step run region)) <= n * bound + allowance /\
      length (snd (step run region)) <= n * bound + allowance) ->
    (forall region, length region <= n ->
      length (fst (base region)) <= initial /\ length (snd (base region)) <= initial) ->
    forall region, length region <= n ->
      let run := Pos.iter step base fuel in
      length (fst (run region)) <= Nat.pow (S n) (Pos.to_nat fuel) * (initial + allowance) /\
      length (snd (run region)) <= Nat.pow (S n) (Pos.to_nat fuel) * (initial + allowance).
Proof.
  intros Hstep Hbase; induction fuel using Pos.peano_ind; intros region Hregion.
  - cbn [Pos.iter Pos.to_nat Nat.pow].
    replace (Pos.to_nat 1%positive) with 1 by reflexivity.
    rewrite Nat.pow_1_r.
    specialize (Hstep base initial region Hregion Hbase); destruct Hstep; split; nia.
  - rewrite Pos.iter_succ, Pos2Nat.inj_succ.
    change (Nat.pow (S n) (S (Pos.to_nat fuel))) with
      (S n * Nat.pow (S n) (Pos.to_nat fuel)).
    specialize (Hstep (Pos.iter step base fuel)
      (Nat.pow (S n) (Pos.to_nat fuel) * (initial + allowance)) region Hregion IHfuel).
    set (power := Nat.pow (S n) (Pos.to_nat fuel)) in *.
    assert (Hpower : 1 <= power).
    { unfold power; apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia. }
    destruct Hstep; split; nia.
Qed.

(** One layer bounds both result and trace using the recursive allowance. *)
Lemma audit_wto_layer_allowance_step {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) ranks n recur bound region :
    length region <= n ->
    (forall part, length part <= n ->
      length (fst (recur part)) <= bound /\ length (snd (recur part)) <= bound) ->
    length (fst (audit_wto_layer_counted p ranks recur region)) <=
      n * bound + audit_wto_layer_allowance p n /\
    length (snd (audit_wto_layer_counted p ranks recur region)) <=
      n * bound + audit_wto_layer_allowance p n.
Proof.
  intros Hregion Hrecur.
  pose proof (audit_wto_layer_envelope p ranks recur n bound region Hregion Hrecur) as Hlayer.
  unfold audit_wto_layer_allowance.
  set (f := S (Pos.to_nat (fuel p))) in *.
  set (m := audit_wto_input_max_out p) in *.
  set (s := (3 + n * (12 + 12 * f)) * (12 + 6 * S (n * f))) in *.
  destruct Hlayer; split; nia.
Qed.

(** The iter traversal satisfies the stated event bound. *)
Lemma audit_wto_iter_trace_bound {A C} (step : A -> A) initial fuel :
    length (snd (audit_pos_iter (fun x => (step x, @nil C)) initial fuel)) + 1 <=
      2 * Pos.to_nat fuel.
Proof.
  revert initial; induction fuel as [fuel IH|fuel IH|]; intro initial.
  - cbn [audit_pos_iter].
    pose proof (IH initial) as Hfirst.
    destruct (audit_pos_iter (fun x => (step x, @nil C)) initial fuel) as [middle first].
    pose proof (IH middle) as Hsecond.
    destruct (audit_pos_iter (fun x => (step x, @nil C)) middle fuel) as [last second].
    cbn in Hfirst, Hsecond |- *; rewrite !length_app, Pos2Nat.inj_xI; cbn; lia.
  - cbn [audit_pos_iter].
    pose proof (IH initial) as Hfirst.
    destruct (audit_pos_iter (fun x => (step x, @nil C)) initial fuel) as [middle first].
    pose proof (IH middle) as Hsecond.
    destruct (audit_pos_iter (fun x => (step x, @nil C)) middle fuel) as [last second].
    cbn in Hfirst, Hsecond |- *; rewrite length_app, Pos2Nat.inj_xO; cbn; lia.
  - reflexivity.
Qed.

(** The run satisfies the stated size bound. *)
Lemma audit_wto_run_size_bound {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) ranks n fuel region :
    length region <= n ->
    let base := fun _ : list V => (@nil (wto_token V), @nil (audit_wto_call V E)) in
    let step := fun recur => audit_wto_layer_counted p ranks recur in
    let '(run, _) := audit_pos_iter (fun recur => (step recur, @nil (audit_wto_call V E)))
      base fuel in
    length (fst (run region)) <= Nat.pow (S n) (Pos.to_nat fuel) *
      audit_wto_layer_allowance p n /\
    length (snd (run region)) <= Nat.pow (S n) (Pos.to_nat fuel) *
      audit_wto_layer_allowance p n.
Proof.
  intro Hregion.
  set (base := fun _ : list V => (@nil (wto_token V), @nil (audit_wto_call V E))).
  set (step := fun recur => audit_wto_layer_counted p ranks recur).
  pose proof (audit_pos_iter_holds _ _ (fun recur => (step recur, @nil (audit_wto_call V E)))
    step base fuel (fun _ => eq_refl)) as Hiter.
  pose proof (audit_wto_iter_envelope n (audit_wto_layer_allowance p n) step base 0 fuel) as Hbound.
  assert (Hstep : forall run bound part, length part <= n ->
    (forall nested, length nested <= n ->
      length (fst (run nested)) <= bound /\ length (snd (run nested)) <= bound) ->
    length (fst (step run part)) <= n * bound + audit_wto_layer_allowance p n /\
    length (snd (step run part)) <= n * bound + audit_wto_layer_allowance p n).
  { intros run bound part Hpart Hnested; apply audit_wto_layer_allowance_step; assumption. }
  assert (Hbase : forall part, length part <= n ->
    length (fst (base part)) <= 0 /\ length (snd (base part)) <= 0).
  { intros part Hpart; split; reflexivity. }
  specialize (Hbound Hstep Hbase region Hregion).
  change (let '(run, _) := audit_pos_iter
    (fun recur => (step recur, @nil (audit_wto_call V E))) base fuel in
    length (fst (run region)) <= Nat.pow (S n) (Pos.to_nat fuel) *
      audit_wto_layer_allowance p n /\
    length (snd (run region)) <= Nat.pow (S n) (Pos.to_nat fuel) *
      audit_wto_layer_allowance p n).
  destruct (audit_pos_iter (fun recur => (step recur, @nil (audit_wto_call V E))) base fuel)
    as [run events].
  cbn in Hiter; destruct Hiter as [Hrun _]; rewrite Hrun.
  change (length (fst (Pos.iter step base fuel region)) <=
    Nat.pow (S n) (Pos.to_nat fuel) * audit_wto_layer_allowance p n /\
    length (snd (Pos.iter step base fuel region)) <=
    Nat.pow (S n) (Pos.to_nat fuel) * audit_wto_layer_allowance p n) in Hbound.
  exact Hbound.
Qed.

(** The layer allowance fits the uniform bound used for the whole traversal. *)
Lemma audit_wto_allowance_bound {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) n :
    let f := S (Pos.to_nat (fuel p)) in
    let m := audit_wto_input_max_out p in
    let s := (3 + n * (12 + 12 * f)) * (12 + 6 * S (n * f)) in
    audit_wto_layer_allowance p n <= 32 * S (s + n * (m + n) + f).
Proof.
  cbn zeta; unfold audit_wto_layer_allowance.
  set (f := S (Pos.to_nat (fuel p))).
  set (m := audit_wto_input_max_out p).
  set (s := (3 + n * (12 + 12 * f)) * (12 + 6 * S (n * f))).
  assert (Hn : n <= S (n * n)) by nia.
  nia.
Qed.

(** The counted traversal satisfies the stated event bound. *)
Lemma audit_wto_counted_event_bound {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) :
    length (snd (audit_wto_counted p)) <= audit_wto_input_event_bound p.
Proof.
  unfold audit_wto_counted.
  pose proof (audit_dfs_full_counted_erases p FinSet.empty (Graph.entries g)) as Hdfs.
  pose proof (audit_dfs_full_counted_event_bound p FinSet.empty (Graph.entries g)) as Hdfs_count.
  destruct (audit_dfs_full_counted p FinSet.empty (Graph.entries g)) as [search dfs_events].
  change (search = dfs p FinSet.empty (Graph.entries g)) in Hdfs.
  change (length dfs_events <= audit_dfs_full_input_event_bound p (Graph.entries g)) in Hdfs_count.
  pose proof (audit_wto_order_length_bound p) as Horder.
  rewrite <- Hdfs in Horder.
  pose proof (@audit_wto_ranks_event_count V E EV (rpo search) 1%positive Map.empty) as Hranks.
  destruct (audit_wto_ranks_counted EV (rpo search) 1%positive Map.empty) as [ranks rank_events].
  change (length rank_events = 1 + 3 * length (rpo search)) in Hranks.
  set (n := audit_wto_input_order_bound p) in *.
  set (depth := Pos.of_succ_nat (length (rpo search))).
  pose proof (audit_wto_run_size_bound p ranks n depth (rpo search) Horder) as Hrun.
  pose proof (@audit_wto_iter_trace_bound _ (audit_wto_call V E)
    (fun recur => audit_wto_layer_counted p ranks recur)
    (fun _ : list V => (@nil (wto_token V), @nil (audit_wto_call V E))) depth) as Hiter.
  cbn zeta in Hrun.
  destruct (audit_pos_iter
    (fun recur => (audit_wto_layer_counted p ranks recur, @nil (audit_wto_call V E)))
    (fun _ => ([], [])) depth) as [run iter_events].
  change (length iter_events + 1 <= 2 * Pos.to_nat depth) in Hiter.
  destruct (run (rpo search)) as [result events].
  change (length result <= Nat.pow (S n) (Pos.to_nat depth) * audit_wto_layer_allowance p n /\
    length events <= Nat.pow (S n) (Pos.to_nat depth) * audit_wto_layer_allowance p n) in Hrun.
  cbn [fst snd]; rewrite !length_app, !length_map; cbn [length].
  unfold audit_wto_input_event_bound; fold n.
  unfold depth in Hiter, Hrun; rewrite !SuccNat2Pos.id_succ in Hiter, Hrun.
  pose proof (audit_wto_allowance_bound p n) as Hallow.
  set (f := S (Pos.to_nat (fuel p))) in *.
  set (m := audit_wto_input_max_out p) in *.
  set (s := (3 + n * (12 + 12 * f)) * (12 + 6 * S (n * f))) in *.
  set (x := S (s + n * (m + n) + f)) in *.
  set (power := Nat.pow (S n) (S n)) in *.
  assert (Hpow : Nat.pow (S n) (S (length (rpo search))) <= power).
  { unfold power; apply Nat.pow_le_mono_r; lia. }
  assert (Hpower : 1 <= power).
  { unfold power; apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia. }
  assert (Hx : 1 <= x) by (unfold x; lia).
  assert (Hnx : n <= x) by (unfold x; nia).
  change (audit_wto_layer_allowance p n <= 32 * x) in Hallow.
  assert (Hdfs_n : length dfs_events <= 3 + 40 * n).
  { unfold n, audit_wto_input_order_bound.
    unfold audit_dfs_full_input_event_bound in Hdfs_count; nia. }
  assert (Hevents : length events <= 32 * (power * x)).
  { eapply Nat.le_trans; [exact (proj2 Hrun)|].
    eapply Nat.le_trans; [apply Nat.mul_le_mono; [exact Hpow|exact Hallow]|].
    nia. }
  assert (Hproduct : x <= power * x).
  { replace x with (1 * x) at 1 by lia; apply Nat.mul_le_mono_r; exact Hpower. }
  assert (Hcube : x <= Nat.pow x 3).
  { replace (Nat.pow x 3) with (x * x * x) by (cbn [Nat.pow]; lia).
    eapply Nat.le_trans with (m := x * x).
    - replace x with (x * 1) at 1 by lia; apply Nat.mul_le_mono_l; exact Hx.
    - replace (x * x) with (x * x * 1) at 1 by lia.
      apply Nat.mul_le_mono_l; exact Hx. }
  assert (Hscaled : 1024 * (power * x) <= 1024 * power * Nat.pow x 3).
  { rewrite Nat.mul_assoc; apply Nat.mul_le_mono_l; exact Hcube. }
  set (product := power * x) in *.
  lia.
Qed.

(** * Captured event correspondence *)

(** A source event has the required capture shape and primitive correspondence. *)
Definition audit_wto_source_event_valid {V E B}
    (event : audit_wto_nested_event V E (audit_graph_callback_capture V E B)) : Prop :=
  audit_wto_source_event_wellformed event /\ audit_wto_source_event_primitive event.

(** The source ranks traversal preserves validity of its emitted source events. *)
Lemma audit_wto_source_ranks_valid {V E B} (cb : audit_dfs_callback_model V E B)
    order clock m :
    Forall audit_wto_source_event_valid
      (snd (audit_wto_nested_ranks (audit_graph_capture_callbacks cb) order clock m)).
Proof.
  revert clock m; induction order as [|v rest IH]; intros clock m.
  - cbn [audit_wto_nested_ranks]; repeat constructor.
  - cbn [audit_wto_nested_ranks].
    unfold audit_tarjan_nested_set, audit_graph_capture_callbacks; cbn.
    destruct (audit_dfs_encode_model cb v) as [code body] eqn:Hcode.
    fold (audit_graph_capture_callbacks cb).
    specialize (IH (Pos.succ clock) (CollectionsTrie.Trie.set code (v, clock) m)).
    destruct (audit_wto_nested_ranks (audit_graph_capture_callbacks cb) rest (Pos.succ clock)
      (CollectionsTrie.Trie.set code (v, clock) m)) as [result events].
    cbn in IH |- *.
    constructor; [split; reflexivity|].
    constructor.
    + split; [reflexivity|apply audit_positive_succ_erases].
    + constructor; [split; [cbn [audit_wto_source_event_wellformed]; eauto|exact I]|exact IH].
Qed.

(** The source earlier traversal preserves validity of its emitted source events. *)
Lemma audit_wto_source_earlier_valid {V E B} (cb : audit_dfs_callback_model V E B) ranks u v :
    Forall audit_wto_source_event_valid
      (snd (audit_wto_nested_earlier (audit_graph_capture_callbacks cb) ranks u v)).
Proof.
  unfold audit_wto_nested_earlier, audit_tarjan_nested_get, audit_graph_capture_callbacks; cbn.
  destruct (audit_dfs_encode_model cb u) as [uc ub].
  destruct (audit_dfs_encode_model cb v) as [vc vb].
  destruct (Map.code_get uc ranks) as [a|]; destruct (Map.code_get vc ranks) as [b|];
    cbn; repeat constructor; try reflexivity; try exact I;
    try (cbn [audit_wto_source_event_wellformed]; eauto);
    apply (proj1 (proj2 (audit_positive_order _ _))).
Qed.

(** The source choose traversal preserves validity of its emitted source events. *)
Lemma audit_wto_source_choose_valid {V E B} (cb : audit_dfs_callback_model V E B)
    ranks rest header :
    Forall audit_wto_source_event_valid
      (snd (audit_wto_nested_choose (audit_graph_capture_callbacks cb) ranks rest header)).
Proof.
  revert header; induction rest as [|v rest IH]; intro header.
  - cbn [audit_wto_nested_choose]; repeat constructor.
  - cbn [audit_wto_nested_choose].
    pose proof (audit_wto_source_earlier_valid cb ranks header v) as Hhere.
    destruct (audit_wto_nested_earlier (audit_graph_capture_callbacks cb) ranks header v)
      as [next here].
    specialize (IH next).
    destruct (audit_wto_nested_choose (audit_graph_capture_callbacks cb) ranks rest next)
      as [result later].
    cbn in Hhere, IH |- *; constructor; [split; reflexivity|].
    apply Forall_app; split; assumption.
Qed.

(** The source remove traversal preserves validity of its emitted source events. *)
Lemma audit_wto_source_remove_valid {V E B} (cb : audit_dfs_callback_model V E B)
    header vertices :
    Forall audit_wto_source_event_valid
      (snd (audit_wto_nested_remove (audit_graph_capture_callbacks cb) header vertices)).
Proof.
  induction vertices as [|v rest IH].
  - cbn [audit_wto_nested_remove]; repeat constructor.
  - cbn [audit_wto_nested_remove].
    unfold audit_graph_capture_callbacks at 1 2; cbn.
    destruct (audit_dfs_encode_model cb header) as [hc hb].
    destruct (audit_dfs_encode_model cb v) as [vc vb].
    destruct (audit_wto_nested_remove (audit_graph_capture_callbacks cb) header rest)
      as [result events].
    cbn in IH |- *; destruct (Pos.eqb hc vc) eqn:Heq; cbn;
      repeat constructor; try reflexivity; try exact I;
      try (cbn [audit_wto_source_event_wellformed]; eauto);
      try (cbn [audit_wto_source_event_primitive]; rewrite <- Heq;
        apply audit_positive_eqb_erases); exact IH.
Qed.

(** The source self edges traversal preserves validity of its emitted source events. *)
Lemma audit_wto_source_self_edges_valid {V E B} (cb : audit_dfs_callback_model V E B)
    vertex edges :
    Forall audit_wto_source_event_valid
      (snd (audit_wto_nested_self_edges (audit_graph_capture_callbacks cb) vertex edges)).
Proof.
  induction edges as [|edge rest IH].
  - cbn [audit_wto_nested_self_edges]; repeat constructor.
  - cbn [audit_wto_nested_self_edges].
    unfold audit_graph_capture_callbacks at 1 2 3; cbn.
    destruct (audit_dfs_encode_model cb vertex) as [vc vb].
    destruct (audit_dfs_target_model cb edge) as [target body].
    destruct (audit_dfs_encode_model cb target) as [tc tb].
    destruct (audit_wto_nested_self_edges (audit_graph_capture_callbacks cb) vertex rest)
      as [result events].
    cbn in IH |- *; destruct (Pos.eqb vc tc) eqn:Heq; cbn;
      repeat constructor; try reflexivity; try exact I;
      try (cbn [audit_wto_source_event_wellformed]; eauto);
      try (cbn [audit_wto_source_event_primitive]; rewrite <- Heq;
        apply audit_positive_eqb_erases); exact IH.
Qed.

(** The source component traversal preserves validity of its emitted source events. *)
Lemma audit_wto_source_component_valid {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) ranks recur component :
    (forall region, Forall audit_wto_source_event_valid (snd (recur region))) ->
    Forall audit_wto_source_event_valid
      (snd (audit_wto_nested_component p (audit_graph_capture_callbacks cb) ranks recur component)).
Proof.
  intro Hrecur; destruct component as [|h rest].
  - cbn [audit_wto_nested_component]; repeat constructor.
  - unfold audit_wto_nested_component.
    pose proof (audit_wto_source_choose_valid cb ranks rest h) as Hchoose.
    destruct (audit_wto_nested_choose (audit_graph_capture_callbacks cb) ranks rest h)
      as [header choose].
    cbn in Hchoose; destruct rest as [|v rest].
    + unfold audit_tarjan_nested_get, audit_graph_capture_callbacks at 1; cbn.
      destruct (audit_dfs_encode_model cb h) as [code body].
      destruct (Map.code_get code (out_index p)) as [edges|].
      * pose proof (audit_wto_source_self_edges_valid cb h edges) as Hedges.
        destruct (audit_wto_nested_self_edges (audit_graph_capture_callbacks cb) h edges)
          as [self events].
        cbn in Hedges |- *; constructor; [split; reflexivity|].
        apply Forall_app; split; [exact Hchoose|].
        constructor; [split; reflexivity|].
        constructor; [split; [cbn [audit_wto_source_event_wellformed]; eauto|exact I]|].
        apply Forall_app; split; [exact Hedges|].
        destruct self; repeat constructor.
      * cbn [audit_wto_nested_self_edges]; cbn.
        constructor; [split; reflexivity|].
        apply Forall_app; split; [exact Hchoose|].
        repeat constructor; try reflexivity; try exact I;
          cbn [audit_wto_source_event_wellformed]; eauto.
    + pose proof (audit_wto_source_remove_valid cb header (h :: v :: rest)) as Hremove.
      destruct (audit_wto_nested_remove (audit_graph_capture_callbacks cb) header (h :: v :: rest))
        as [smaller remove_events].
      specialize (Hrecur smaller).
      destruct (recur smaller) as [inside events].
      cbn in Hremove, Hrecur |- *; constructor; [split; reflexivity|].
      apply Forall_app; split; [exact Hchoose|].
      constructor; [split; reflexivity|].
      apply Forall_app; split; [exact Hremove|].
      apply Forall_app; split; [exact Hrecur|repeat constructor].
Qed.

(** The source components traversal preserves validity of its emitted source events. *)
Lemma audit_wto_source_components_valid {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) ranks recur components :
    (forall region, Forall audit_wto_source_event_valid (snd (recur region))) ->
    Forall audit_wto_source_event_valid
      (snd (audit_wto_nested_components p (audit_graph_capture_callbacks cb) ranks recur
        components)).
Proof.
  intro Hrecur; induction components as [|component rest IH].
  - cbn [audit_wto_nested_components]; repeat constructor.
  - cbn [audit_wto_nested_components].
    pose proof (audit_wto_source_component_valid p cb ranks recur component Hrecur) as Hfirst.
    destruct (audit_wto_nested_component p (audit_graph_capture_callbacks cb) ranks recur component)
      as [first events].
    destruct (audit_wto_nested_components p (audit_graph_capture_callbacks cb) ranks recur rest)
      as [later trace].
    cbn in Hfirst, IH |- *; constructor; [split; reflexivity|].
    apply Forall_app; split; [exact Hfirst|].
    apply Forall_app; split; [exact IH|repeat constructor].
Qed.

(** The source layer traversal preserves validity of its emitted source events. *)
Lemma audit_wto_source_layer_valid {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) ranks recur region :
    audit_dfs_callbacks_erase EV g cb ->
    (forall part, Forall audit_wto_source_event_valid (snd (recur part))) ->
    Forall audit_wto_source_event_valid (snd (audit_wto_source_layer p cb ranks recur region)).
Proof.
  intros Hcallbacks Hrecur; unfold audit_wto_source_layer.
  pose proof (audit_scc_source_events_wellformed p cb region) as Hshape.
  pose proof (audit_scc_source_primitive_correspondence_holds V E B EV g p cb region Hcallbacks)
    as Hprimitive.
  destruct (audit_scc_source_counted p cb region) as [scc scc_events].
  cbn in Hshape, Hprimitive |- *.
  pose proof (audit_wto_source_components_valid p cb ranks recur (rev_append (components scc) [])
    Hrecur) as Hcomponents.
  destruct (audit_wto_nested_components p (audit_graph_capture_callbacks cb) ranks recur
    (rev_append (components scc) [])) as [result events].
  cbn in Hcomponents |- *; apply Forall_app; split.
  - apply Forall_forall; intros [event body] Hin.
    apply in_map_iff in Hin; destruct Hin as [[nested receipt] [Heq Hin]]; cbn in Heq.
    inversion Heq; subst event body.
    apply Forall_forall with (x := (nested, receipt)) in Hshape; [|exact Hin].
    apply Forall_forall with (x := (nested, receipt)) in Hprimitive; [|exact Hin].
    split; assumption.
  - constructor; [split; reflexivity|exact Hcomponents].
Qed.

(** A step invariant is preserved by the actual binary iterator. *)
Lemma audit_wto_iter_invariant {A C} (step : A -> A) (P : A -> Prop) initial fuel :
    (forall state, P state -> P (step state)) -> P initial ->
    P (fst (audit_pos_iter (fun state => (step state, @nil C)) initial fuel)).
Proof.
  intros Hstep Hinitial.
  pose proof (audit_pos_iter_holds A C (fun state => (step state, @nil C))
    step initial fuel (fun _ => eq_refl)) as Hagrees.
  destruct (audit_pos_iter (fun state => (step state, @nil C)) initial fuel) as [result events].
  cbn in Hagrees |- *; rewrite (proj1 Hagrees).
  clear Hagrees result events.
  induction fuel using Pos.peano_ind.
  - cbn [Pos.iter]; apply Hstep; exact Hinitial.
  - rewrite Pos.iter_succ; apply Hstep; exact IHfuel.
Qed.

(** The source iter traversal preserves validity of its emitted source events. *)
Lemma audit_wto_source_iter_valid {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) ranks fuel base :
    audit_dfs_callbacks_erase EV g cb ->
    (forall region, Forall audit_wto_source_event_valid (snd (base region))) ->
    forall region,
      Forall audit_wto_source_event_valid
        (snd (fst (audit_pos_iter
          (fun recur => (audit_wto_source_layer p cb ranks recur, @nil (audit_wto_call V E)))
          base fuel) region)).
Proof.
  intros Hcallbacks Hbase region.
  assert (Hrun : forall part, Forall audit_wto_source_event_valid
    (snd (fst (audit_pos_iter
      (fun recur => (audit_wto_source_layer p cb ranks recur, @nil (audit_wto_call V E)))
      base fuel) part))).
  { eapply audit_wto_iter_invariant.
    - intros recur Hrecur part; apply audit_wto_source_layer_valid; assumption.
    - exact Hbase. }
  exact (Hrun region).
Qed.

(** The iterator bookkeeping events have valid empty callback captures. *)
Lemma audit_wto_iter_events_valid {V E B A} (step : A -> A) initial fuel :
    Forall audit_wto_source_event_valid
      (map (fun event => (audit_wto_iter_event event, @nil (audit_graph_callback_capture V E B)))
        (snd (audit_pos_iter (fun x => (step x, @nil (audit_wto_call V E))) initial fuel))).
Proof.
  revert initial; induction fuel as [fuel IH|fuel IH|]; intro initial.
  - cbn [audit_pos_iter].
    pose proof (IH initial) as Hfirst.
    destruct (audit_pos_iter (fun x => (step x, @nil (audit_wto_call V E))) initial fuel)
      as [middle first].
    pose proof (IH middle) as Hsecond.
    destruct (audit_pos_iter (fun x => (step x, @nil (audit_wto_call V E))) middle fuel)
      as [last second].
    cbn in Hfirst, Hsecond |- *; constructor; [split; reflexivity|].
    rewrite !map_app; apply Forall_app; split; [exact Hfirst|].
    apply Forall_app; split; [exact Hsecond|repeat constructor].
  - cbn [audit_pos_iter].
    pose proof (IH initial) as Hfirst.
    destruct (audit_pos_iter (fun x => (step x, @nil (audit_wto_call V E))) initial fuel)
      as [middle first].
    pose proof (IH middle) as Hsecond.
    destruct (audit_pos_iter (fun x => (step x, @nil (audit_wto_call V E))) middle fuel)
      as [last second].
    cbn in Hfirst, Hsecond |- *; constructor; [split; reflexivity|].
    rewrite map_app; apply Forall_app; split; assumption.
  - cbn [audit_pos_iter]; repeat constructor.
Qed.

(** Every source event carries its matching callback capture and primitive result. *)
Theorem audit_wto_source_event_correspondence_holds :
    audit_wto_source_event_correspondence_statement.
Proof.
  intros V E B EV g p cb Hcallbacks.
  unfold audit_wto_source_counted.
  pose proof (audit_dfs_source_events_wellformed p cb FinSet.empty (Graph.entries g)) as Hshape.
  pose proof (audit_dfs_source_successor_correspondence_holds V E B EV g p cb FinSet.empty
    (Graph.entries g) Hcallbacks) as Hprimitive.
  destruct (audit_dfs_source_counted p cb FinSet.empty (Graph.entries g)) as [search dfs_events].
  cbn in Hshape, Hprimitive |- *.
  set (order := rev_append (postorder search) []).
  pose proof (audit_wto_source_ranks_valid cb order 1%positive Map.empty) as Hranks.
  destruct (audit_wto_nested_ranks (audit_graph_capture_callbacks cb) order 1%positive Map.empty)
    as [ranks rank_events].
  cbn in Hranks |- *.
  set (depth := Pos.of_succ_nat (length order)).
  set (base := fun _ : list V => (@nil (wto_token V),
    @nil (audit_wto_nested_event V E (audit_graph_callback_capture V E B)))).
  set (step := fun recur => audit_wto_source_layer p cb ranks recur).
  assert (Hbase : forall region, Forall audit_wto_source_event_valid (snd (base region))).
  { intro region; constructor. }
  pose proof (audit_wto_source_iter_valid p cb ranks depth base Hcallbacks Hbase order) as Hrun.
  pose proof (@audit_wto_iter_events_valid V E B _ step base depth) as Hiter.
  cbn zeta in Hrun.
  change (Forall audit_wto_source_event_valid
    (snd (fst (audit_pos_iter (fun recur => (step recur, @nil (audit_wto_call V E)))
      base depth) order))) in Hrun.
  destruct (audit_pos_iter (fun recur => (step recur, @nil (audit_wto_call V E))) base depth)
    as [run iter_events].
  cbn in Hrun.
  destruct (run order) as [result events].
  cbn in Hrun, Hiter |- *.
  assert (Hdfs : Forall audit_wto_source_event_valid
    (map (fun item => (AuditWtoDfs (fst item), snd item)) dfs_events)).
  { apply Forall_forall; intros [event body] Hin.
    apply in_map_iff in Hin; destruct Hin as [[nested receipt] [Heq Hin]]; cbn in Heq.
    inversion Heq; subst event body.
    apply Forall_forall with (x := (nested, receipt)) in Hshape; [|exact Hin].
    apply Forall_forall with (x := (nested, receipt)) in Hprimitive; [|exact Hin].
    split; assumption. }
  assert (Hdepth : @audit_wto_source_event_valid V E B (AuditWtoDepth (length order) depth, [])).
  { split; [reflexivity|].
    unfold audit_wto_source_event_primitive; cbn; unfold depth.
    exact (audit_nat_encode_erases (length order)). }
  assert (Hall : Forall audit_wto_source_event_valid
    (map (fun item => (AuditWtoDfs (fst item), snd item)) dfs_events ++
      [(AuditWtoOutput (length (postorder search)), [])] ++ rank_events ++
      [(AuditWtoDepth (length order) depth, [])] ++
      map (fun event => (audit_wto_iter_event event, [])) iter_events ++ events ++
      [(AuditWtoOutput (length result), [])])).
  { repeat rewrite Forall_app.
    repeat split; try assumption; try (constructor; [split; reflexivity|constructor]).
    constructor; [exact Hdepth|constructor]. }
  split; eapply Forall_impl; [|exact Hall| |exact Hall]; intros item [Hwell Hprim]; assumption.
Qed.

(** * External callback accounting *)

(** Every callback capture comes from the corresponding callback invocation. *)
Definition audit_wto_event_receipts {V E B} (cb : audit_dfs_callback_model V E B)
    (event : audit_wto_nested_event V E (audit_graph_callback_capture V E B)) : Prop :=
  Forall (audit_dfs_capture_receipt cb) (snd event).

(** Callback receipts bound actual body work by the external callback budgets. *)
Lemma audit_wto_source_bodies_bound {V E B} (cb : audit_dfs_callback_model V E B)
    (weight : B -> nat) encode_source target_source encode_budget target_budget events :
    audit_graph_external_callback_adapter (audit_dfs_encode_model cb) weight encode_source
      encode_budget ->
    audit_graph_external_callback_adapter (audit_dfs_target_model cb) weight target_source
      target_budget ->
    Forall (audit_wto_event_receipts cb) events ->
    audit_wto_source_body_work weight events <=
      audit_wto_source_external_budget encode_budget target_budget events.
Proof.
  intros Hencode Htarget Hreceipts.
  induction Hreceipts as [|[event body] events Hbody Htail IH].
  - reflexivity.
  - unfold audit_wto_event_receipts in Hbody; cbn in Hbody.
    change (fold_right (fun capture n => audit_graph_capture_work weight capture + n) 0 body +
      audit_wto_source_body_work weight events <=
      fold_right (fun capture n => audit_scc_capture_budget encode_budget target_budget capture + n)
        0 body + audit_wto_source_external_budget encode_budget target_budget events).
    assert (Hbody_bound :
      fold_right (fun capture n => audit_graph_capture_work weight capture + n) 0 body <=
      fold_right (fun capture n => audit_scc_capture_budget encode_budget target_budget capture + n)
        0 body).
    { clear IH Htail events event.
      induction Hbody as [|capture body Hcapture Hrest IHbody]; cbn; [lia|].
      pose proof (audit_dfs_capture_body_bound cb weight encode_source target_source encode_budget
        target_budget capture Hencode Htarget Hcapture) as Hbound.
      destruct capture; cbn [audit_scc_capture_budget audit_dfs_capture_budget] in *; lia. }
    lia.
Qed.

(** The source contract and callback receipts imply the adapted contract. *)
Lemma audit_wto_source_adapted_from_receipts :
    audit_wto_source_statement ->
    (forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
      (cb : audit_dfs_callback_model V E B),
      Forall (audit_wto_event_receipts cb) (snd (audit_wto_source_counted p cb))) ->
    audit_wto_source_adapted_statement.
Proof.
  intros Hsource Hreceipts V E B EV g p cb weight encode_source target_source encode_budget
    target_budget Hcallbacks Hencode Htarget.
  pose proof (Hsource V E B EV g p cb weight Hcallbacks) as Hwork.
  pose proof (audit_wto_source_bodies_bound cb weight encode_source target_source encode_budget
    target_budget (snd (audit_wto_source_counted p cb)) Hencode Htarget
    (Hreceipts V E B EV g p cb)) as Hbody.
  destruct (audit_wto_source_counted p cb) as [result events].
  change (result = wto_of p /\ length events <= audit_wto_input_event_bound p /\
    audit_wto_source_work weight events <= audit_wto_source_budget EV g p +
      audit_wto_source_body_work weight events) in Hwork.
  change (audit_wto_source_body_work weight events <=
    audit_wto_source_external_budget encode_budget target_budget events) in Hbody.
  destruct Hwork as [Hresult [_ Hbound]]; split; [exact Hresult|lia].
Qed.

(** The source ranks traversal preserves the callback receipts in its source events. *)
Lemma audit_wto_source_ranks_receipts {V E B} (cb : audit_dfs_callback_model V E B)
    order clock m :
    Forall (audit_wto_event_receipts cb)
      (snd (audit_wto_nested_ranks (audit_graph_capture_callbacks cb) order clock m)).
Proof.
  revert clock m; induction order as [|v rest IH]; intros clock m.
  - cbn [audit_wto_nested_ranks]; repeat constructor.
  - cbn [audit_wto_nested_ranks].
    unfold audit_tarjan_nested_set, audit_graph_capture_callbacks; cbn.
    destruct (audit_dfs_encode_model cb v) as [code body] eqn:Hcode.
    fold (audit_graph_capture_callbacks cb).
    specialize (IH (Pos.succ clock) (CollectionsTrie.Trie.set code (v, clock) m)).
    destruct (audit_wto_nested_ranks (audit_graph_capture_callbacks cb) rest (Pos.succ clock)
      (CollectionsTrie.Trie.set code (v, clock) m)) as [result events].
    cbn in IH |- *; repeat constructor; try exact IH; exact Hcode.
Qed.

(** The source earlier traversal preserves the callback receipts in its source events. *)
Lemma audit_wto_source_earlier_receipts {V E B} (cb : audit_dfs_callback_model V E B) ranks u v :
    Forall (audit_wto_event_receipts cb)
      (snd (audit_wto_nested_earlier (audit_graph_capture_callbacks cb) ranks u v)).
Proof.
  unfold audit_wto_nested_earlier, audit_tarjan_nested_get, audit_graph_capture_callbacks; cbn.
  destruct (audit_dfs_encode_model cb u) as [uc ub] eqn:Hu.
  destruct (audit_dfs_encode_model cb v) as [vc vb] eqn:Hv.
  destruct (Map.code_get uc ranks); destruct (Map.code_get vc ranks); cbn;
    repeat constructor; assumption.
Qed.

(** The source choose traversal preserves the callback receipts in its source events. *)
Lemma audit_wto_source_choose_receipts {V E B} (cb : audit_dfs_callback_model V E B)
    ranks rest header :
    Forall (audit_wto_event_receipts cb)
      (snd (audit_wto_nested_choose (audit_graph_capture_callbacks cb) ranks rest header)).
Proof.
  revert header; induction rest as [|v rest IH]; intro header.
  - cbn [audit_wto_nested_choose]; repeat constructor.
  - cbn [audit_wto_nested_choose].
    pose proof (audit_wto_source_earlier_receipts cb ranks header v) as Hhere.
    destruct (audit_wto_nested_earlier (audit_graph_capture_callbacks cb) ranks header v)
      as [next here].
    specialize (IH next).
    destruct (audit_wto_nested_choose (audit_graph_capture_callbacks cb) ranks rest next)
      as [result later].
    cbn in Hhere, IH |- *; constructor; [constructor|].
    apply Forall_app; split; assumption.
Qed.

(** The source remove traversal preserves the callback receipts in its source events. *)
Lemma audit_wto_source_remove_receipts {V E B} (cb : audit_dfs_callback_model V E B)
    header vertices :
    Forall (audit_wto_event_receipts cb)
      (snd (audit_wto_nested_remove (audit_graph_capture_callbacks cb) header vertices)).
Proof.
  induction vertices as [|v rest IH].
  - cbn [audit_wto_nested_remove]; repeat constructor.
  - cbn [audit_wto_nested_remove].
    unfold audit_graph_capture_callbacks at 1 2; cbn.
    destruct (audit_dfs_encode_model cb header) as [hc hb] eqn:Hheader.
    destruct (audit_dfs_encode_model cb v) as [vc vb] eqn:Hv.
    destruct (audit_wto_nested_remove (audit_graph_capture_callbacks cb) header rest)
      as [result events].
    cbn in IH |- *; destruct (Pos.eqb hc vc); cbn;
      repeat constructor; try exact Hheader; try exact Hv; exact IH.
Qed.

(** The source self edges traversal preserves the callback receipts in its source events. *)
Lemma audit_wto_source_self_edges_receipts {V E B} (cb : audit_dfs_callback_model V E B)
    vertex edges :
    Forall (audit_wto_event_receipts cb)
      (snd (audit_wto_nested_self_edges (audit_graph_capture_callbacks cb) vertex edges)).
Proof.
  induction edges as [|edge rest IH].
  - cbn [audit_wto_nested_self_edges]; repeat constructor.
  - cbn [audit_wto_nested_self_edges].
    unfold audit_graph_capture_callbacks at 1 2 3; cbn.
    destruct (audit_dfs_encode_model cb vertex) as [vc vb] eqn:Hv.
    destruct (audit_dfs_target_model cb edge) as [target body] eqn:Ht.
    destruct (audit_dfs_encode_model cb target) as [tc tb] eqn:Htarget.
    destruct (audit_wto_nested_self_edges (audit_graph_capture_callbacks cb) vertex rest)
      as [result events].
    cbn in IH |- *; destruct (Pos.eqb vc tc); cbn;
      repeat constructor; try exact Hv; try exact Ht; try exact Htarget; exact IH.
Qed.

(** The source component traversal preserves the callback receipts in its source events. *)
Lemma audit_wto_source_component_receipts {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) ranks recur component :
    (forall region, Forall (audit_wto_event_receipts cb) (snd (recur region))) ->
    Forall (audit_wto_event_receipts cb)
      (snd (audit_wto_nested_component p (audit_graph_capture_callbacks cb) ranks recur component)).
Proof.
  intro Hrecur; destruct component as [|h rest].
  - cbn [audit_wto_nested_component]; repeat constructor.
  - unfold audit_wto_nested_component.
    pose proof (audit_wto_source_choose_receipts cb ranks rest h) as Hchoose.
    destruct (audit_wto_nested_choose (audit_graph_capture_callbacks cb) ranks rest h)
      as [header choose].
    cbn in Hchoose; destruct rest as [|v rest].
    + unfold audit_tarjan_nested_get, audit_graph_capture_callbacks at 1; cbn.
      destruct (audit_dfs_encode_model cb h) as [code body] eqn:Hcode.
      destruct (Map.code_get code (out_index p)) as [edges|].
      * pose proof (audit_wto_source_self_edges_receipts cb h edges) as Hedges.
        destruct (audit_wto_nested_self_edges (audit_graph_capture_callbacks cb) h edges)
          as [self events].
        cbn in Hedges |- *; constructor; [constructor|].
        apply Forall_app; split; [exact Hchoose|].
        constructor; [constructor|].
        constructor; [repeat constructor; exact Hcode|].
        apply Forall_app; split; [exact Hedges|].
        destruct self; repeat constructor.
      * cbn [audit_wto_nested_self_edges]; cbn.
        constructor; [constructor|].
        apply Forall_app; split; [exact Hchoose|].
        repeat constructor; exact Hcode.
    + pose proof (audit_wto_source_remove_receipts cb header (h :: v :: rest)) as Hremove.
      destruct (audit_wto_nested_remove (audit_graph_capture_callbacks cb) header (h :: v :: rest))
        as [smaller remove_events].
      specialize (Hrecur smaller).
      destruct (recur smaller) as [inside events].
      cbn in Hremove, Hrecur |- *; constructor; [constructor|].
      apply Forall_app; split; [exact Hchoose|].
      constructor; [constructor|].
      apply Forall_app; split; [exact Hremove|].
      apply Forall_app; split; [exact Hrecur|repeat constructor].
Qed.

(** The source components traversal preserves the callback receipts in its source events. *)
Lemma audit_wto_source_components_receipts {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) ranks recur components :
    (forall region, Forall (audit_wto_event_receipts cb) (snd (recur region))) ->
    Forall (audit_wto_event_receipts cb)
      (snd (audit_wto_nested_components p (audit_graph_capture_callbacks cb) ranks recur
        components)).
Proof.
  intro Hrecur; induction components as [|component rest IH].
  - cbn [audit_wto_nested_components]; repeat constructor.
  - cbn [audit_wto_nested_components].
    pose proof (audit_wto_source_component_receipts p cb ranks recur component Hrecur) as Hfirst.
    destruct (audit_wto_nested_component p (audit_graph_capture_callbacks cb) ranks recur component)
      as [first events].
    destruct (audit_wto_nested_components p (audit_graph_capture_callbacks cb) ranks recur rest)
      as [later trace].
    cbn in Hfirst, IH |- *; constructor; [constructor|].
    apply Forall_app; split; [exact Hfirst|].
    apply Forall_app; split; [exact IH|repeat constructor].
Qed.

(** The source layer traversal preserves the callback receipts in its source events. *)
Lemma audit_wto_source_layer_receipts {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) ranks recur region :
    (forall part, Forall (audit_wto_event_receipts cb) (snd (recur part))) ->
    Forall (audit_wto_event_receipts cb) (snd (audit_wto_source_layer p cb ranks recur region)).
Proof.
  intro Hrecur; unfold audit_wto_source_layer.
  pose proof (audit_scc_source_receipts p cb region) as Hscc.
  destruct (audit_scc_source_counted p cb region) as [scc scc_events].
  cbn in Hscc |- *.
  pose proof (audit_wto_source_components_receipts p cb ranks recur
    (rev_append (components scc) []) Hrecur) as Hcomponents.
  destruct (audit_wto_nested_components p (audit_graph_capture_callbacks cb) ranks recur
    (rev_append (components scc) [])) as [result events].
  cbn in Hcomponents |- *; apply Forall_app; split.
  - apply Forall_forall; intros [event body] Hin.
    apply in_map_iff in Hin; destruct Hin as [[nested receipt] [Heq Hin]]; cbn in Heq.
    inversion Heq; subst event body.
    apply Forall_forall with (x := (nested, receipt)) in Hscc; [exact Hscc|exact Hin].
  - constructor; [constructor|exact Hcomponents].
Qed.

(** The source iter traversal preserves the callback receipts in its source events. *)
Lemma audit_wto_source_iter_receipts {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) ranks fuel base :
    (forall region, Forall (audit_wto_event_receipts cb) (snd (base region))) ->
    forall region,
      Forall (audit_wto_event_receipts cb)
        (snd (fst (audit_pos_iter
          (fun recur => (audit_wto_source_layer p cb ranks recur, @nil (audit_wto_call V E)))
          base fuel) region)).
Proof.
  intros Hbase region.
  assert (Hrun : forall part, Forall (audit_wto_event_receipts cb)
    (snd (fst (audit_pos_iter
      (fun recur => (audit_wto_source_layer p cb ranks recur, @nil (audit_wto_call V E)))
      base fuel) part))).
  { eapply audit_wto_iter_invariant.
    - intros recur Hrecur part; apply audit_wto_source_layer_receipts; exact Hrecur.
    - exact Hbase. }
  exact (Hrun region).
Qed.

(** The source preserves the callback receipts in its source events. *)
Lemma audit_wto_source_receipts {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) :
    Forall (audit_wto_event_receipts cb) (snd (audit_wto_source_counted p cb)).
Proof.
  unfold audit_wto_source_counted.
  pose proof (audit_dfs_source_receipts p cb FinSet.empty (Graph.entries g)) as Hdfs.
  destruct (audit_dfs_source_counted p cb FinSet.empty (Graph.entries g)) as [search dfs_events].
  cbn in Hdfs |- *.
  set (order := rev_append (postorder search) []).
  pose proof (audit_wto_source_ranks_receipts cb order 1%positive Map.empty) as Hranks.
  destruct (audit_wto_nested_ranks (audit_graph_capture_callbacks cb) order 1%positive Map.empty)
    as [ranks rank_events].
  cbn in Hranks |- *.
  set (depth := Pos.of_succ_nat (length order)).
  set (base := fun _ : list V => (@nil (wto_token V),
    @nil (audit_wto_nested_event V E (audit_graph_callback_capture V E B)))).
  set (step := fun recur => audit_wto_source_layer p cb ranks recur).
  assert (Hbase : forall region, Forall (audit_wto_event_receipts cb) (snd (base region))).
  { intro region; constructor. }
  pose proof (audit_wto_source_iter_receipts p cb ranks depth base Hbase order) as Hrun.
  change (Forall (audit_wto_event_receipts cb)
    (snd (fst (audit_pos_iter (fun recur => (step recur, @nil (audit_wto_call V E)))
      base depth) order))) in Hrun.
  destruct (audit_pos_iter (fun recur => (step recur, @nil (audit_wto_call V E))) base depth)
    as [run iter_events].
  cbn in Hrun; destruct (run order) as [result events].
  cbn in Hrun |- *.
  assert (Hmapped : Forall (audit_wto_event_receipts cb)
    (map (fun item => (AuditWtoDfs (fst item), snd item)) dfs_events)).
  { apply Forall_forall; intros [event body] Hin.
    apply in_map_iff in Hin; destruct Hin as [[nested receipt] [Heq Hin]]; cbn in Heq.
    inversion Heq; subst event body.
    apply Forall_forall with (x := (nested, receipt)) in Hdfs; [exact Hdfs|exact Hin]. }
  assert (Hiter : Forall (audit_wto_event_receipts cb)
    (map (fun event => (audit_wto_iter_event event, [])) iter_events)).
  { apply Forall_forall; intros item Hin.
    apply in_map_iff in Hin; destruct Hin as [event [Heq Hin]]; subst item; constructor. }
  apply Forall_app; split; [exact Hmapped|].
  constructor; [constructor|].
  apply Forall_app; split; [exact Hranks|].
  constructor; [constructor|].
  apply Forall_app; split; [exact Hiter|].
  apply Forall_app; split; [exact Hrun|repeat constructor].
Qed.

(** The source contract implies its adapted version using actual receipts. *)
Lemma audit_wto_source_adapted_from_source :
    audit_wto_source_statement -> audit_wto_source_adapted_statement.
Proof.
  intro Hsource; apply audit_wto_source_adapted_from_receipts; [exact Hsource|].
  intros; apply audit_wto_source_receipts.
Qed.

(** * Rank-value bounds *)

(** The ranks traversal preserves the stated numeric envelope. *)
Lemma audit_wto_ranks_numbers {V E} (EV : encoding V) order clock m ceiling :
    Pos.to_nat clock <= ceiling -> audit_tarjan_map_numbers EV ceiling m ->
    audit_tarjan_map_numbers EV (ceiling + length order)
      (fst (@audit_wto_ranks_counted V E EV order clock m)).
Proof.
  revert clock m ceiling; induction order as [|v rest IH]; intros clock m ceiling Hclock Hmap.
  - cbn [audit_wto_ranks_counted]; cbn; replace (ceiling + 0) with ceiling by lia; exact Hmap.
  - cbn [audit_wto_ranks_counted].
    assert (Hnext : Pos.to_nat (Pos.succ clock) <= S ceiling).
    { rewrite Pos2Nat.inj_succ; lia. }
    assert (Hnew : audit_tarjan_map_numbers EV (S ceiling) (Map.set EV v clock m)).
    { apply audit_tarjan_map_numbers_set; [lia|].
      eapply (audit_tarjan_map_numbers_mono EV ceiling (S ceiling)); [lia|exact Hmap]. }
    pose proof (IH (Pos.succ clock) (Map.set EV v clock m) (S ceiling) Hnext Hnew) as Hrest.
    destruct (audit_wto_ranks_counted EV rest (Pos.succ clock) (Map.set EV v clock m))
      as [result events].
    change (audit_tarjan_map_numbers EV (S ceiling + length rest) result) in Hrest.
    replace (ceiling + length (v :: rest)) with (S ceiling + length rest) by (cbn; lia).
    exact Hrest.
Qed.

(** * DFS result key envelope *)

(** The DFS stack and postorder use only vertices and edges in their envelopes. *)
Definition audit_wto_dfs_keys {V E} (vertices : list V) (edges : list E)
    (work : dfs_stack V E * DfsState.t V E) : Prop :=
  audit_dfs_stack_keys vertices edges (fst work) /\ incl (DfsState.post (snd work)) vertices.

(** The dfs step preserves the stated key envelope. *)
Lemma audit_wto_dfs_step_keys {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) blocked vertices work :
    let edges := flat_map snd (Map.elements (out_index p)) in
    (forall edge, In edge edges -> In (Graph.target g edge) vertices) ->
    audit_wto_dfs_keys vertices edges work ->
    audit_wto_dfs_keys vertices edges (dfs_step p blocked work).
Proof.
  intros edges Hall [Hstack Hpost].
  pose proof (audit_dfs_full_step_keys p blocked vertices work Hall Hstack) as [_ Hstack'].
  rewrite audit_dfs_full_step_erases in Hstack'.
  split; [exact Hstack'|].
  destruct work as [stack st], stack as [|[v outgoing] rest].
  - exact Hpost.
  - inversion Hstack as [|frame tail Hframe Htail]; subst frame tail.
    destruct Hframe as [Hv Hedges]; destruct outgoing as [|edge outgoing].
    + cbn [dfs_step dfs_finish DfsState.post]; intros node [Heq|Hin].
      * subst node; exact Hv.
      * apply Hpost; exact Hin.
    + cbn [dfs_step].
      destruct (FinSet.mem EV (Graph.target g edge) blocked ||
        FinSet.mem EV (Graph.target g edge) (DfsState.seen st));
        cbn [dfs_discover DfsState.post]; exact Hpost.
Qed.

(** The dfs run preserves the stated key envelope. *)
Lemma audit_wto_dfs_run_keys {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) blocked vertices fuel work :
    let edges := flat_map snd (Map.elements (out_index p)) in
    (forall edge, In edge edges -> In (Graph.target g edge) vertices) ->
    audit_wto_dfs_keys vertices edges work ->
    audit_wto_dfs_keys vertices edges (dfs_run p blocked fuel work).
Proof.
  intros edges Hall Hwork; rewrite (dfs_run_agrees EV g p blocked fuel work).
  induction fuel using Pos.peano_ind.
  - cbn [Pos.iter]; apply audit_wto_dfs_step_keys; assumption.
  - rewrite Pos.iter_succ; apply audit_wto_dfs_step_keys; assumption.
Qed.

(** The dfs root preserves the stated key envelope. *)
Lemma audit_wto_dfs_root_keys {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) blocked vertices st vertex :
    let edges := flat_map snd (Map.elements (out_index p)) in
    (forall edge, In edge edges -> In (Graph.target g edge) vertices) ->
    In vertex vertices -> incl (DfsState.post st) vertices ->
    incl (DfsState.post (dfs_root p blocked st vertex)) vertices.
Proof.
  intros edges Hall Hvertex Hpost; unfold dfs_root.
  destruct (FinSet.mem EV vertex blocked || FinSet.mem EV vertex (DfsState.seen st)).
  - exact Hpost.
  - assert (Hout : incl (succ_edges p vertex) edges).
    { unfold succ_edges, index_edges.
      destruct (Map.get EV vertex (out_index p)) as [outgoing|] eqn:Hget.
      - subst edges; now apply (audit_dfs_outgoing_edges p vertex outgoing Hget).
      - intros edge Hin; contradiction. }
    assert (Hinitial : audit_wto_dfs_keys vertices edges
      ([(vertex, succ_edges p vertex)], dfs_discover EV vertex None st)).
    { split.
      - constructor; [cbn; split; assumption|constructor].
      - cbn [dfs_discover DfsState.post]; exact Hpost. }
    pose proof (audit_wto_dfs_run_keys p blocked vertices (fuel p)
      ([(vertex, succ_edges p vertex)], dfs_discover EV vertex None st) Hall Hinitial) as Hrun.
    exact (proj2 Hrun).
Qed.

(** The dfs roots traversal preserves the stated key envelope. *)
Lemma audit_wto_dfs_roots_keys {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) blocked vertices roots st :
    let edges := flat_map snd (Map.elements (out_index p)) in
    (forall edge, In edge edges -> In (Graph.target g edge) vertices) ->
    incl roots vertices -> incl (DfsState.post st) vertices ->
    incl (DfsState.post (fold_left (dfs_root p blocked) roots st)) vertices.
Proof.
  intros edges Hall; revert st; induction roots as [|root rest IH]; intros st Hroots Hpost.
  - exact Hpost.
  - cbn [fold_left].
    apply IH.
    + intros v Hin; apply Hroots; right; exact Hin.
    + apply (audit_wto_dfs_root_keys p blocked vertices st root Hall).
      * apply Hroots; left; reflexivity.
      * exact Hpost.
Qed.

(** DFS reverse postorder contains only entries or indexed edge targets. *)
Lemma audit_wto_order_keys {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) :
    incl (rpo (dfs p FinSet.empty (Graph.entries g)))
      (Graph.entries g ++ map (Graph.target g) (flat_map snd (Map.elements (out_index p)))).
Proof.
  set (vertices := Graph.entries g ++
    map (Graph.target g) (flat_map snd (Map.elements (out_index p)))).
  assert (Hall : forall edge, In edge (flat_map snd (Map.elements (out_index p))) ->
    In (Graph.target g edge) vertices).
  { intros edge Hin; unfold vertices; apply in_or_app; right; now apply in_map. }
  assert (Hroots : incl (Graph.entries g) vertices).
  { intros vertex Hin; unfold vertices; apply in_or_app; left; exact Hin. }
  assert (Hinitial : incl (DfsState.post (@dfs_initial V E)) vertices).
  { intros vertex Hin; contradiction. }
  pose proof (audit_wto_dfs_roots_keys p FinSet.empty vertices (Graph.entries g) dfs_initial
    Hall Hroots Hinitial) as Hpost.
  unfold rpo, dfs; cbn [postorder]; rewrite <- !rev_alt.
  intros vertex Hin; apply in_rev in Hin; apply in_rev in Hin.
  apply Hpost; exact Hin.
Qed.

(** * Counted event key provenance *)

(** Vertex operands of an event, including delegated events, stay in the envelope. *)
Definition audit_wto_event_keys {V E} (vertices : list V) (event : audit_wto_call V E) : Prop :=
  match event with
  | AuditWtoDfs nested => audit_dfs_full_event_keys vertices nested
  | AuditWtoScc nested => audit_tarjan_event_keys vertices nested
  | AuditWtoRead v _ _
  | AuditWtoEdges v _ _
  | AuditWtoWrite v _ _
  | AuditWtoEncode v _
  | AuditWtoTarget _ v => In v vertices
  | _ => True
  end.

(** The ranks traversal preserves the stated key envelope. *)
Lemma audit_wto_ranks_keys {V E} (EV : encoding V) vertices order clock m :
    incl order vertices ->
    Forall (audit_wto_event_keys vertices) (snd (@audit_wto_ranks_counted V E EV order clock m)).
Proof.
  intro Horder; revert clock m; induction order as [|v rest IH]; intros clock m.
  - cbn [audit_wto_ranks_counted]; repeat constructor.
  - cbn [audit_wto_ranks_counted].
    specialize (IH (fun x Hx => Horder x (or_intror Hx)) (Pos.succ clock) (Map.set EV v clock m)).
    destruct (audit_wto_ranks_counted EV rest (Pos.succ clock) (Map.set EV v clock m))
      as [result events].
    cbn in IH |- *; constructor; [exact I|].
    constructor; [exact I|].
    constructor; [apply Horder; left; reflexivity|exact IH].
Qed.

(** The earlier preserves the stated key envelope. *)
Lemma audit_wto_earlier_keys {V E} (EV : encoding V) vertices ranks u v :
    In u vertices -> In v vertices ->
    Forall (audit_wto_event_keys vertices) (snd (@audit_wto_earlier_counted V E EV ranks u v)).
Proof.
  intros Hu Hv; unfold audit_wto_earlier_counted.
  destruct (Map.get EV u ranks); destruct (Map.get EV v ranks); destruct (Pos.leb _ _);
    cbn; repeat constructor; assumption || exact I.
Qed.

(** The earlier of two vertices is one of those vertices. *)
Lemma audit_wto_earlier_member {V} (EV : encoding V) ranks u v :
    wto_earlier EV ranks u v = u \/ wto_earlier EV ranks u v = v.
Proof.
  unfold wto_earlier; destruct (Pos.leb _ _); auto.
Qed.

(** The chosen header is either the initial header or a candidate. *)
Lemma audit_wto_choose_member {V E} (EV : encoding V) ranks rest header :
    In (fst (@audit_wto_choose_counted V E EV ranks rest header)) (header :: rest).
Proof.
  rewrite audit_wto_choose_result; revert header.
  induction rest as [|v rest IH]; intro header; [left; reflexivity|].
  cbn [fold_left]; specialize (IH (wto_earlier EV ranks header v)).
  destruct (audit_wto_earlier_member EV ranks header v) as [Heq|Heq]; rewrite Heq in IH;
    cbn in *; firstorder congruence.
Qed.

(** The choose traversal preserves the stated key envelope. *)
Lemma audit_wto_choose_keys {V E} (EV : encoding V) vertices ranks rest header :
    In header vertices -> incl rest vertices ->
    Forall (audit_wto_event_keys vertices)
      (snd (@audit_wto_choose_counted V E EV ranks rest header)).
Proof.
  intros Hheader Hrest; revert header Hheader.
  induction rest as [|v rest IH]; intros header Hheader.
  - cbn [audit_wto_choose_counted]; repeat constructor.
  - cbn [audit_wto_choose_counted].
    assert (Hv : In v vertices) by (apply Hrest; left; reflexivity).
    pose proof (@audit_wto_earlier_keys V E EV vertices ranks header v Hheader Hv) as Hhere.
    pose proof (audit_wto_earlier_member EV ranks header v) as Hmember.
    destruct (audit_wto_earlier_counted EV ranks header v) as [next here] eqn:Hnext.
    assert (Hnext_member : In next vertices).
    { assert (Hvalue : fst (@audit_wto_earlier_counted V E EV ranks header v) =
        wto_earlier EV ranks header v) by reflexivity.
      rewrite Hnext in Hvalue; cbn in Hvalue.
      rewrite Hvalue; destruct Hmember as [Heq|Heq]; rewrite Heq; assumption. }
    assert (Htail : incl rest vertices) by (intros x Hx; apply Hrest; right; exact Hx).
    specialize (IH Htail next Hnext_member).
    destruct (audit_wto_choose_counted EV ranks rest next) as [result later].
    cbn in Hhere, IH |- *; constructor; [exact I|].
    apply Forall_app; split; assumption.
Qed.

(** The remove traversal preserves the stated key envelope. *)
Lemma audit_wto_remove_keys {V E} (EV : encoding V) vertices header region :
    In header vertices -> incl region vertices ->
    Forall (audit_wto_event_keys vertices)
      (snd (@audit_wto_remove_counted V E EV header region)).
Proof.
  intros Hheader Hregion; induction region as [|v rest IH].
  - cbn [audit_wto_remove_counted]; repeat constructor.
  - cbn [audit_wto_remove_counted].
    assert (Hv : In v vertices) by (apply Hregion; left; reflexivity).
    assert (Hrest : incl rest vertices) by (intros x Hx; apply Hregion; right; exact Hx).
    specialize (IH Hrest).
    destruct (audit_wto_remove_counted EV header rest) as [result events].
    cbn in IH |- *; destruct (Pos.eqb (encode EV header) (encode EV v)); cbn;
      repeat constructor; assumption || exact I.
Qed.

(** The self edges traversal preserves the stated key envelope. *)
Lemma audit_wto_self_edges_keys {V E} (EV : encoding V) (g : Graph.t V E)
    vertices vertex edges :
    In vertex vertices -> (forall edge, In edge edges -> In (Graph.target g edge) vertices) ->
    Forall (audit_wto_event_keys vertices) (snd (audit_wto_self_edges EV g vertex edges)).
Proof.
  intros Hvertex Hedges; induction edges as [|edge rest IH].
  - cbn [audit_wto_self_edges]; repeat constructor.
  - cbn [audit_wto_self_edges].
    assert (Htarget : In (Graph.target g edge) vertices) by (apply Hedges; left; reflexivity).
    assert (Hrest : forall e, In e rest -> In (Graph.target g e) vertices) by
      (intros e Hin; apply Hedges; right; exact Hin).
    specialize (IH Hrest).
    destruct (audit_wto_self_edges EV g vertex rest) as [result events].
    cbn in IH |- *; repeat constructor; assumption || exact I.
Qed.

(** The component traversal preserves the stated key envelope. *)
Lemma audit_wto_component_keys {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) vertices ranks recur component :
    (forall edge, In edge (flat_map snd (Map.elements (out_index p))) ->
      In (Graph.target g edge) vertices) ->
    incl component vertices ->
    (forall region, incl region component ->
      Forall (audit_wto_event_keys vertices) (snd (recur region))) ->
    Forall (audit_wto_event_keys vertices)
      (snd (audit_wto_component_counted p ranks recur component)).
Proof.
  intros Hall Hcomponent Hrecur; destruct component as [|h rest].
  - cbn [audit_wto_component_counted]; repeat constructor.
  - unfold audit_wto_component_counted.
    assert (Hh : In h vertices) by (apply Hcomponent; left; reflexivity).
    assert (Hrest : incl rest vertices) by (intros v Hin; apply Hcomponent; right; exact Hin).
    pose proof (@audit_wto_choose_keys V E EV vertices ranks rest h Hh Hrest) as Hchoose.
    pose proof (@audit_wto_choose_member V E EV ranks rest h) as Hmember.
    destruct (audit_wto_choose_counted EV ranks rest h) as [header choose].
    cbn in Hchoose, Hmember.
    assert (Hheader : In header vertices) by (apply Hcomponent; exact Hmember).
    destruct rest as [|v rest].
    + destruct (Map.get EV h (out_index p)) as [edges|] eqn:Hedges.
      * assert (Htargets : forall e, In e edges -> In (Graph.target g e) vertices).
        { intros e Hin; apply Hall; eapply audit_dfs_outgoing_edges; eauto. }
        pose proof (audit_wto_self_edges_keys EV g vertices h edges Hh Htargets) as Hself.
        destruct (audit_wto_self_edges EV g h edges) as [self events].
        cbn in Hself |- *; constructor; [exact I|].
        apply Forall_app; split; [exact Hchoose|].
        constructor; [exact I|].
        constructor; [exact Hh|].
        apply Forall_app; split; [exact Hself|destruct self; repeat constructor].
      * cbn [audit_wto_self_edges]; cbn; constructor; [exact I|].
        apply Forall_app; split; [exact Hchoose|].
        repeat constructor; assumption || exact I.
    + pose proof (@audit_wto_remove_keys V E EV vertices header (h :: v :: rest)
        Hheader Hcomponent) as Hremove.
      pose proof (@audit_wto_remove_result V E EV header (h :: v :: rest)) as Hresult.
      destruct (audit_wto_remove_counted EV header (h :: v :: rest)) as [smaller remove_events].
      change (smaller = wto_remove EV header (h :: v :: rest)) in Hresult.
      assert (Hsmaller : incl smaller (h :: v :: rest)).
      { rewrite Hresult; unfold wto_remove; intros x Hin; apply filter_In in Hin; tauto. }
      specialize (Hrecur smaller Hsmaller).
      destruct (recur smaller) as [inside events].
      cbn in Hremove, Hrecur |- *; constructor; [exact I|].
      apply Forall_app; split; [exact Hchoose|].
      constructor; [exact I|].
      apply Forall_app; split; [exact Hremove|].
      apply Forall_app; split; [exact Hrecur|repeat constructor].
Qed.

(** The components traversal preserves the stated key envelope. *)
Lemma audit_wto_components_keys {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) vertices ranks recur components :
    (forall edge, In edge (flat_map snd (Map.elements (out_index p))) ->
      In (Graph.target g edge) vertices) ->
    incl (concat components) vertices ->
    (forall region, incl region vertices ->
      Forall (audit_wto_event_keys vertices) (snd (recur region))) ->
    Forall (audit_wto_event_keys vertices)
      (snd (audit_wto_components_counted p ranks recur components)).
Proof.
  intros Hall Hcomponents Hrecur; induction components as [|component rest IH].
  - cbn [audit_wto_components_counted]; repeat constructor.
  - cbn [audit_wto_components_counted].
    assert (Hcomponent : incl component vertices).
    { intros v Hin; apply Hcomponents; cbn; apply in_or_app; left; exact Hin. }
    assert (Hrest : incl (concat rest) vertices).
    { intros v Hin; apply Hcomponents; cbn; apply in_or_app; right; exact Hin. }
    assert (Hlocal : forall region, incl region component ->
      Forall (audit_wto_event_keys vertices) (snd (recur region))).
    { intros region Hregion; apply Hrecur; eapply incl_tran; eassumption. }
    pose proof (audit_wto_component_keys p vertices ranks recur component Hall Hcomponent Hlocal)
      as Hfirst.
    specialize (IH Hrest).
    destruct (audit_wto_component_counted p ranks recur component) as [first here].
    destruct (audit_wto_components_counted p ranks recur rest) as [later events].
    cbn in Hfirst, IH |- *; constructor; [exact I|].
    apply Forall_app; split; [exact Hfirst|].
    apply Forall_app; split; [exact IH|repeat constructor].
Qed.

(** The layer traversal preserves the stated key envelope. *)
Lemma audit_wto_layer_keys {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) vertices ranks recur region :
    (forall edge, In edge (flat_map snd (Map.elements (out_index p))) ->
      In (Graph.target g edge) vertices) ->
    incl region vertices ->
    (forall part, incl part vertices ->
      Forall (audit_wto_event_keys vertices) (snd (recur part))) ->
    Forall (audit_wto_event_keys vertices) (snd (audit_wto_layer_counted p ranks recur region)).
Proof.
  intros Hall Hregion Hrecur; unfold audit_wto_layer_counted.
  pose proof (audit_scc_counted_keys p region) as Hscc_keys.
  pose proof (audit_scc_counted_erases EV g p region) as Hscc.
  destruct (audit_scc_within_counted p region) as [scc events].
  cbn in Hscc_keys; change (scc = scc_within p region) in Hscc; subst scc.
  assert (Hcomponents : incl (concat (rev (components (scc_within p region)))) vertices).
  { intros v Hin; apply (proj1 (tarjan_concat_rev_in _ _)) in Hin.
    apply Hregion; apply (audit_wto_scc_members_in_region EV g p region); exact Hin. }
  pose proof (audit_wto_components_keys p vertices ranks recur
    (rev (components (scc_within p region))) Hall Hcomponents Hrecur) as Hbody.
  destruct (audit_wto_components_counted p ranks recur (rev (components (scc_within p region))))
    as [result trace].
  cbn in Hbody |- *; apply Forall_app; split.
  - assert (Hinclude : incl
      (region ++ map (Graph.target g) (flat_map snd (Map.elements (out_index p)))) vertices).
    { intros v Hin; apply in_app_iff in Hin; destruct Hin as [Hin|Hin].
      - now apply Hregion.
      - apply in_map_iff in Hin; destruct Hin as [edge [Heq Hedge]]; subst; now apply Hall. }
    apply Forall_map; eapply Forall_impl; [|exact Hscc_keys].
    intros event Hkeys; cbn [audit_wto_event_keys].
    destruct event as [site|edge target|v set member|v map value|v before after|
      v number before after|v rest before after|helper|v set|left right];
      cbn [audit_tarjan_event_keys] in *; try exact I; try now apply Hinclude.
    destruct helper; cbn [audit_tarjan_helper_keys] in *; try exact I; try now apply Hinclude.
    destruct Hkeys as [Hleft Hright]; split; now apply Hinclude.
  - constructor; [exact I|exact Hbody].
Qed.

(** The iter traversal preserves the stated key envelope. *)
Lemma audit_wto_iter_keys {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) vertices ranks fuel base :
    (forall edge, In edge (flat_map snd (Map.elements (out_index p))) ->
      In (Graph.target g edge) vertices) ->
    (forall region, incl region vertices ->
      Forall (audit_wto_event_keys vertices) (snd (base region))) ->
    forall region, incl region vertices ->
      Forall (audit_wto_event_keys vertices)
        (snd (fst (audit_pos_iter
          (fun recur => (audit_wto_layer_counted p ranks recur, @nil (audit_wto_call V E)))
          base fuel) region)).
Proof.
  intros Hall Hbase region Hregion.
  assert (Hrun : forall part, incl part vertices ->
    Forall (audit_wto_event_keys vertices)
      (snd (fst (audit_pos_iter
        (fun recur => (audit_wto_layer_counted p ranks recur, @nil (audit_wto_call V E)))
        base fuel) part))).
  { eapply audit_wto_iter_invariant.
    - intros recur Hrecur part Hpart; apply audit_wto_layer_keys; assumption.
    - exact Hbase. }
  exact (Hrun region Hregion).
Qed.

(** The iter event preserves the stated key envelope. *)
Lemma audit_wto_iter_event_keys {V E A} (vertices : list V) (step : A -> A) initial fuel :
    Forall (audit_wto_event_keys vertices)
      (map (@audit_wto_iter_event V E)
        (snd (audit_pos_iter (fun x => (step x, @nil (audit_wto_call V E))) initial fuel))).
Proof.
  revert initial; induction fuel as [fuel IH|fuel IH|]; intro initial.
  - cbn [audit_pos_iter].
    pose proof (IH initial) as Hfirst.
    destruct (audit_pos_iter (fun x => (step x, @nil (audit_wto_call V E))) initial fuel)
      as [middle first].
    pose proof (IH middle) as Hsecond.
    destruct (audit_pos_iter (fun x => (step x, @nil (audit_wto_call V E))) middle fuel)
      as [last second].
    cbn in Hfirst, Hsecond |- *; constructor; [exact I|].
    rewrite !map_app; apply Forall_app; split; [exact Hfirst|].
    apply Forall_app; split; [exact Hsecond|repeat constructor].
  - cbn [audit_pos_iter].
    pose proof (IH initial) as Hfirst.
    destruct (audit_pos_iter (fun x => (step x, @nil (audit_wto_call V E))) initial fuel)
      as [middle first].
    pose proof (IH middle) as Hsecond.
    destruct (audit_pos_iter (fun x => (step x, @nil (audit_wto_call V E))) middle fuel)
      as [last second].
    cbn in Hfirst, Hsecond |- *; constructor; [exact I|].
    rewrite map_app; apply Forall_app; split; assumption.
  - cbn [audit_pos_iter]; repeat constructor.
Qed.

(** The counted traversal preserves the stated key envelope. *)
Lemma audit_wto_counted_keys {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) :
    let vertices := Graph.entries g ++
      map (Graph.target g) (flat_map snd (Map.elements (out_index p))) in
    Forall (audit_wto_event_keys vertices) (snd (audit_wto_counted p)).
Proof.
  intros vertices; unfold audit_wto_counted.
  pose proof (audit_dfs_full_counted_keys p FinSet.empty (Graph.entries g)) as Hdfs_keys.
  pose proof (audit_dfs_full_counted_erases p FinSet.empty (Graph.entries g)) as Hdfs.
  destruct (audit_dfs_full_counted p FinSet.empty (Graph.entries g)) as [search dfs_events].
  change (search = dfs p FinSet.empty (Graph.entries g)) in Hdfs.
  pose proof (audit_wto_order_keys p) as Horder; rewrite <- Hdfs in Horder.
  change (incl (rpo search) vertices) in Horder.
  assert (Hall : forall edge, In edge (flat_map snd (Map.elements (out_index p))) ->
    In (Graph.target g edge) vertices).
  { intros edge Hin; subst vertices; apply in_or_app; right; now apply in_map. }
  pose proof (@audit_wto_ranks_keys V E EV vertices (rpo search) 1%positive Map.empty Horder)
    as Hranks.
  destruct (audit_wto_ranks_counted EV (rpo search) 1%positive Map.empty) as [ranks rank_events].
  cbn in Hranks |- *.
  set (depth := Pos.of_succ_nat (length (rpo search))).
  set (base := fun _ : list V => (@nil (wto_token V), @nil (audit_wto_call V E))).
  set (step := fun recur => audit_wto_layer_counted p ranks recur).
  assert (Hbase : forall region, incl region vertices ->
    Forall (audit_wto_event_keys vertices) (snd (base region))).
  { intros region Hregion; constructor. }
  pose proof (audit_wto_iter_keys p vertices ranks depth base Hall Hbase (rpo search) Horder)
    as Hrun.
  pose proof (@audit_wto_iter_event_keys V E _ vertices step base depth) as Hiter.
  change (Forall (audit_wto_event_keys vertices)
    (snd (fst (audit_pos_iter (fun recur => (step recur, @nil (audit_wto_call V E)))
      base depth) (rpo search)))) in Hrun.
  destruct (audit_pos_iter (fun recur => (step recur, @nil (audit_wto_call V E))) base depth)
    as [run iter_events].
  cbn in Hrun; destruct (run (rpo search)) as [result events].
  cbn in Hrun, Hiter |- *.
  apply Forall_app; split.
  - apply Forall_map; exact Hdfs_keys.
  - constructor; [exact I|].
    apply Forall_app; split; [exact Hranks|].
    constructor; [exact I|].
    apply Forall_app; split; [exact Hiter|].
    apply Forall_app; split; [exact Hrun|repeat constructor].
Qed.

(** * Numeric operand widths *)

(** Numeric operands and delegated outputs obey the given ceiling and width. *)
Definition audit_wto_event_numbers {V E} (width ceiling : nat)
    (event : audit_wto_call V E) : Prop :=
  match event with
  | AuditWtoDfs nested => audit_dfs_full_event_clock nested <= ceiling /\
      audit_dfs_full_event_output nested <= 2 * ceiling
  | AuditWtoScc nested => audit_tarjan_event_numbers ceiling nested /\
      audit_tarjan_event_output nested <= 2 * ceiling
  | AuditWtoSucc before _ => Pos.size_nat before <= width
  | AuditWtoLe a b _
  | AuditWtoEqual a b _ => Pos.size_nat a <= width /\ Pos.size_nat b <= width
  | AuditWtoEncode _ code => Pos.size_nat code <= width
  | AuditWtoDepth len depth => len <= ceiling /\ Pos.size_nat depth <= width /\
      Pos.to_nat depth <= ceiling
  | _ => True
  end.

(** The ranks traversal preserves the stated numeric envelope. *)
Lemma audit_wto_ranks_numbers_events {V E} (EV : encoding V) order clock m ceiling width :
    Pos.to_nat clock + length order <= ceiling ->
    (forall value, Pos.to_nat value <= ceiling -> Pos.size_nat value <= width) ->
    Forall (audit_wto_event_numbers width ceiling)
      (snd (@audit_wto_ranks_counted V E EV order clock m)).
Proof.
  intros Hclock Hwidth; revert clock m Hclock; induction order as [|v rest IH];
    intros clock m Hclock.
  - cbn [audit_wto_ranks_counted]; repeat constructor.
  - cbn [audit_wto_ranks_counted].
    assert (Hnext : Pos.to_nat (Pos.succ clock) + length rest <= ceiling).
    { rewrite Pos2Nat.inj_succ; cbn in Hclock; lia. }
    specialize (IH (Pos.succ clock) (Map.set EV v clock m) Hnext).
    destruct (audit_wto_ranks_counted EV rest (Pos.succ clock) (Map.set EV v clock m))
      as [result events].
    cbn in IH |- *; constructor; [exact I|].
    constructor; [apply Hwidth; cbn in Hclock; lia|].
    constructor; [exact I|exact IH].
Qed.

(** The earlier preserves the stated numeric envelope. *)
Lemma audit_wto_earlier_numbers {V E} (EV : encoding V) ranks u v ceiling width :
    audit_tarjan_map_numbers EV ceiling ranks ->
    (forall value, Pos.to_nat value <= ceiling -> Pos.size_nat value <= width) ->
    1 <= ceiling ->
    Forall (audit_wto_event_numbers width ceiling)
      (snd (@audit_wto_earlier_counted V E EV ranks u v)).
Proof.
  intros Hmap Hwidth Hone; unfold audit_wto_earlier_counted.
  destruct (Map.get EV u ranks) as [a|] eqn:Hu;
    destruct (Map.get EV v ranks) as [b|] eqn:Hv;
    destruct (Pos.leb _ _); cbn.
  all: constructor; [exact I|].
  all: constructor; [exact I|].
  all: constructor; [|constructor].
  all: cbn [audit_wto_event_numbers]; split; apply Hwidth; try lia; eapply Hmap; eassumption.
Qed.

(** The choose traversal preserves the stated numeric envelope. *)
Lemma audit_wto_choose_numbers {V E} (EV : encoding V) ranks rest header ceiling width :
    audit_tarjan_map_numbers EV ceiling ranks ->
    (forall value, Pos.to_nat value <= ceiling -> Pos.size_nat value <= width) ->
    1 <= ceiling ->
    Forall (audit_wto_event_numbers width ceiling)
      (snd (@audit_wto_choose_counted V E EV ranks rest header)).
Proof.
  intros Hmap Hwidth Hone; revert header; induction rest as [|v rest IH]; intro header.
  - cbn [audit_wto_choose_counted]; repeat constructor.
  - cbn [audit_wto_choose_counted].
    pose proof (@audit_wto_earlier_numbers V E EV ranks header v ceiling width Hmap Hwidth Hone)
      as Hhere.
    destruct (audit_wto_earlier_counted EV ranks header v) as [next here].
    specialize (IH next).
    destruct (audit_wto_choose_counted EV ranks rest next) as [result later].
    cbn in Hhere, IH |- *; constructor; [exact I|].
    apply Forall_app; split; assumption.
Qed.

(** The remove traversal preserves the stated numeric envelope. *)
Lemma audit_wto_remove_numbers {V E} (EV : encoding V) vertices header region ceiling width :
    In header vertices -> incl region vertices ->
    (forall v, In v vertices -> Pos.size_nat (encode EV v) <= width) ->
    Forall (audit_wto_event_numbers width ceiling)
      (snd (@audit_wto_remove_counted V E EV header region)).
Proof.
  intros Hheader Hregion Hwidth; induction region as [|v rest IH].
  - cbn [audit_wto_remove_counted]; repeat constructor.
  - cbn [audit_wto_remove_counted].
    assert (Hv : In v vertices) by (apply Hregion; left; reflexivity).
    assert (Hrest : incl rest vertices) by (intros x Hx; apply Hregion; right; exact Hx).
    specialize (IH Hrest).
    destruct (audit_wto_remove_counted EV header rest) as [result events].
    cbn in IH |- *; destruct (Pos.eqb (encode EV header) (encode EV v)); cbn.
    all: constructor; [exact I|].
    all: constructor; [apply Hwidth; exact Hheader|].
    all: constructor; [apply Hwidth; exact Hv|].
    all: constructor; [split; apply Hwidth; assumption|exact IH].
Qed.

(** The self edges traversal preserves the stated numeric envelope. *)
Lemma audit_wto_self_edges_numbers {V E} (EV : encoding V) (g : Graph.t V E)
    vertices vertex edges ceiling width :
    In vertex vertices -> (forall edge, In edge edges -> In (Graph.target g edge) vertices) ->
    (forall v, In v vertices -> Pos.size_nat (encode EV v) <= width) ->
    Forall (audit_wto_event_numbers width ceiling) (snd (audit_wto_self_edges EV g vertex edges)).
Proof.
  intros Hvertex Hedges Hwidth; induction edges as [|edge rest IH].
  - cbn [audit_wto_self_edges]; repeat constructor.
  - cbn [audit_wto_self_edges].
    assert (Htarget : In (Graph.target g edge) vertices) by (apply Hedges; left; reflexivity).
    assert (Hrest : forall e, In e rest -> In (Graph.target g e) vertices) by
      (intros e Hin; apply Hedges; right; exact Hin).
    specialize (IH Hrest).
    destruct (audit_wto_self_edges EV g vertex rest) as [result events].
    cbn in IH |- *; constructor; [exact I|].
    constructor; [apply Hwidth; exact Hvertex|].
    constructor; [exact I|].
    constructor; [apply Hwidth; exact Htarget|].
    constructor; [split; apply Hwidth; assumption|exact IH].
Qed.

(** The component traversal preserves the stated numeric envelope. *)
Lemma audit_wto_component_numbers {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) vertices ranks recur component ceiling width :
    (forall edge, In edge (flat_map snd (Map.elements (out_index p))) ->
      In (Graph.target g edge) vertices) ->
    incl component vertices -> audit_tarjan_map_numbers EV ceiling ranks ->
    (forall value, Pos.to_nat value <= ceiling -> Pos.size_nat value <= width) ->
    (forall v, In v vertices -> Pos.size_nat (encode EV v) <= width) ->
    1 <= ceiling ->
    (forall region, incl region component -> length region <= length component ->
      Forall (audit_wto_event_numbers width ceiling) (snd (recur region))) ->
    Forall (audit_wto_event_numbers width ceiling)
      (snd (audit_wto_component_counted p ranks recur component)).
Proof.
  intros Hall Hcomponent Hmap Hwidth Hkeys Hone Hrecur; destruct component as [|h rest].
  - cbn [audit_wto_component_counted]; repeat constructor.
  - unfold audit_wto_component_counted.
    assert (Hh : In h vertices) by (apply Hcomponent; left; reflexivity).
    pose proof (@audit_wto_choose_numbers V E EV ranks rest h ceiling width Hmap Hwidth Hone)
      as Hchoose.
    pose proof (@audit_wto_choose_member V E EV ranks rest h) as Hmember.
    destruct (audit_wto_choose_counted EV ranks rest h) as [header choose].
    cbn in Hchoose, Hmember.
    assert (Hheader : In header vertices) by (apply Hcomponent; exact Hmember).
    destruct rest as [|v rest].
    + destruct (Map.get EV h (out_index p)) as [edges|] eqn:Hedges.
      * assert (Htargets : forall e, In e edges -> In (Graph.target g e) vertices).
        { intros e Hin; apply Hall; eapply audit_dfs_outgoing_edges; eauto. }
        pose proof (audit_wto_self_edges_numbers EV g vertices h edges ceiling width
          Hh Htargets Hkeys) as Hself.
        destruct (audit_wto_self_edges EV g h edges) as [self events].
        cbn in Hself |- *; constructor; [exact I|].
        apply Forall_app; split; [exact Hchoose|].
        constructor; [exact I|].
        constructor; [exact I|].
        apply Forall_app; split; [exact Hself|destruct self; repeat constructor].
      * cbn [audit_wto_self_edges]; cbn; constructor; [exact I|].
        apply Forall_app; split; [exact Hchoose|].
        repeat constructor.
    + pose proof (@audit_wto_remove_numbers V E EV vertices header (h :: v :: rest) ceiling width
        Hheader Hcomponent Hkeys) as Hremove.
      pose proof (@audit_wto_remove_result V E EV header (h :: v :: rest)) as Hresult.
      destruct (audit_wto_remove_counted EV header (h :: v :: rest)) as [smaller remove_events].
      change (smaller = wto_remove EV header (h :: v :: rest)) in Hresult.
      assert (Hsmaller : incl smaller (h :: v :: rest)).
      { rewrite Hresult; unfold wto_remove; intros x Hin; apply filter_In in Hin; tauto. }
      assert (Hsize : length smaller <= length (h :: v :: rest)).
      { rewrite Hresult; unfold wto_remove; apply filter_length_le. }
      specialize (Hrecur smaller Hsmaller Hsize).
      destruct (recur smaller) as [inside events].
      cbn in Hremove, Hrecur |- *; constructor; [exact I|].
      apply Forall_app; split; [exact Hchoose|].
      constructor; [exact I|].
      apply Forall_app; split; [exact Hremove|].
      apply Forall_app; split; [exact Hrecur|repeat constructor].
Qed.

(** The components traversal preserves the stated numeric envelope. *)
Lemma audit_wto_components_numbers {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) vertices ranks recur components ceiling width n :
    (forall edge, In edge (flat_map snd (Map.elements (out_index p))) ->
      In (Graph.target g edge) vertices) ->
    incl (concat components) vertices -> length (concat components) <= n ->
    audit_tarjan_map_numbers EV ceiling ranks ->
    (forall value, Pos.to_nat value <= ceiling -> Pos.size_nat value <= width) ->
    (forall v, In v vertices -> Pos.size_nat (encode EV v) <= width) ->
    1 <= ceiling ->
    (forall region, incl region vertices -> length region <= n ->
      Forall (audit_wto_event_numbers width ceiling) (snd (recur region))) ->
    Forall (audit_wto_event_numbers width ceiling)
      (snd (audit_wto_components_counted p ranks recur components)).
Proof.
  intros Hall; induction components as [|component rest IH];
    intros Hcomponents Hsize Hmap Hwidth Hkeys Hone Hrecur.
  - cbn [audit_wto_components_counted]; repeat constructor.
  - cbn [audit_wto_components_counted].
    assert (Hcomponent : incl component vertices).
    { intros v Hin; apply Hcomponents; cbn; apply in_or_app; left; exact Hin. }
    assert (Hrest : incl (concat rest) vertices).
    { intros v Hin; apply Hcomponents; cbn; apply in_or_app; right; exact Hin. }
    assert (Hlocal : forall region, incl region component -> length region <= length component ->
      Forall (audit_wto_event_numbers width ceiling) (snd (recur region))).
    { intros region Hregion Hlen; apply Hrecur.
      - eapply incl_tran; eassumption.
      - cbn in Hsize; rewrite length_app in Hsize; lia. }
    pose proof (audit_wto_component_numbers p vertices ranks recur component ceiling width
      Hall Hcomponent Hmap Hwidth Hkeys Hone Hlocal) as Hfirst.
    assert (Hrest_size : length (concat rest) <= n).
    { cbn in Hsize; rewrite length_app in Hsize; lia. }
    specialize (IH Hrest Hrest_size Hmap Hwidth Hkeys Hone Hrecur).
    destruct (audit_wto_component_counted p ranks recur component) as [first here].
    destruct (audit_wto_components_counted p ranks recur rest) as [later events].
    cbn in Hfirst, IH |- *; constructor; [exact I|].
    apply Forall_app; split; [exact Hfirst|].
    apply Forall_app; split; [exact IH|repeat constructor].
Qed.

(** The layer traversal preserves the stated numeric envelope. *)
Lemma audit_wto_layer_numbers {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) vertices ranks recur region ceiling width n :
    (forall edge, In edge (flat_map snd (Map.elements (out_index p))) ->
      In (Graph.target g edge) vertices) ->
    incl region vertices -> length region <= n ->
    2 + n * S (Pos.to_nat (fuel p)) <= ceiling ->
    audit_tarjan_map_numbers EV ceiling ranks ->
    (forall value, Pos.to_nat value <= ceiling -> Pos.size_nat value <= width) ->
    (forall v, In v vertices -> Pos.size_nat (encode EV v) <= width) ->
    (forall part, incl part vertices -> length part <= n ->
      Forall (audit_wto_event_numbers width ceiling) (snd (recur part))) ->
    Forall (audit_wto_event_numbers width ceiling)
      (snd (audit_wto_layer_counted p ranks recur region)).
Proof.
  intros Hall Hregion Hlen Hceiling Hmap Hwidth Hkeys Hrecur.
  unfold audit_wto_layer_counted.
  pose proof (audit_scc_counted_numbers p region) as Hnumbers.
  pose proof (audit_scc_counted_event_output p region) as Houtput.
  pose proof (audit_scc_counted_erases EV g p region) as Hscc.
  destruct (audit_scc_within_counted p region) as [scc events].
  cbn in Hnumbers, Houtput; change (scc = scc_within p region) in Hscc; subst scc.
  assert (Hcomponents : incl (concat (rev (components (scc_within p region)))) vertices).
  { intros v Hin; apply (proj1 (tarjan_concat_rev_in _ _)) in Hin.
    apply Hregion; apply (audit_wto_scc_members_in_region EV g p region); exact Hin. }
  assert (Hsize : length (concat (rev (components (scc_within p region)))) <= n).
  { rewrite (Permutation_length (tarjan_concat_rev (components (scc_within p region)))).
    pose proof (audit_wto_scc_size_bound EV g p region); lia. }
  pose proof (audit_wto_components_numbers p vertices ranks recur
    (rev (components (scc_within p region))) ceiling width n Hall Hcomponents Hsize Hmap
    Hwidth Hkeys ltac:(lia) Hrecur) as Hbody.
  destruct (audit_wto_components_counted p ranks recur (rev (components (scc_within p region))))
    as [result trace].
  cbn in Hbody |- *; apply Forall_app; split.
  - assert (Hnum : Forall (audit_tarjan_event_numbers ceiling) events).
    { eapply audit_tarjan_events_numbers_mono; [|exact Hnumbers]; nia. }
    apply Forall_map; apply Forall_forall; intros event Hin.
    apply Forall_forall with (x := event) in Hnum; [|exact Hin].
    apply Forall_forall with (x := event) in Houtput; [|exact Hin].
    split; [exact Hnum|nia].
  - constructor; [exact I|exact Hbody].
Qed.

(** The iter traversal preserves the stated numeric envelope. *)
Lemma audit_wto_iter_numbers {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) vertices ranks (depth : positive) base ceiling width n :
    (forall edge, In edge (flat_map snd (Map.elements (out_index p))) ->
      In (Graph.target g edge) vertices) ->
    2 + n * S (Pos.to_nat (fuel p)) <= ceiling ->
    audit_tarjan_map_numbers EV ceiling ranks ->
    (forall value, Pos.to_nat value <= ceiling -> Pos.size_nat value <= width) ->
    (forall v, In v vertices -> Pos.size_nat (encode EV v) <= width) ->
    (forall region, incl region vertices -> length region <= n ->
      Forall (audit_wto_event_numbers width ceiling) (snd (base region))) ->
    forall region, incl region vertices -> length region <= n ->
      Forall (audit_wto_event_numbers width ceiling)
        (snd (fst (audit_pos_iter
          (fun recur => (audit_wto_layer_counted p ranks recur, @nil (audit_wto_call V E)))
          base depth) region)).
Proof.
  intros Hall Hceiling Hmap Hwidth Hkeys Hbase region Hregion Hlen.
  assert (Hrun : forall part, incl part vertices -> length part <= n ->
    Forall (audit_wto_event_numbers width ceiling)
      (snd (fst (audit_pos_iter
        (fun recur => (audit_wto_layer_counted p ranks recur, @nil (audit_wto_call V E)))
        base depth) part))).
  { eapply audit_wto_iter_invariant.
    - intros recur Hrecur part Hpart Hsize; eapply audit_wto_layer_numbers; eassumption.
    - exact Hbase. }
  exact (Hrun region Hregion Hlen).
Qed.

(** The iter event preserves the stated numeric envelope. *)
Lemma audit_wto_iter_event_numbers {V E A} width ceiling (step : A -> A) initial fuel :
    Forall (audit_wto_event_numbers width ceiling)
      (map (@audit_wto_iter_event V E)
        (snd (audit_pos_iter (fun x => (step x, @nil (audit_wto_call V E))) initial fuel))).
Proof.
  revert initial; induction fuel as [fuel IH|fuel IH|]; intro initial.
  - cbn [audit_pos_iter].
    pose proof (IH initial) as Hfirst.
    destruct (audit_pos_iter (fun x => (step x, @nil (audit_wto_call V E))) initial fuel)
      as [middle first].
    pose proof (IH middle) as Hsecond.
    destruct (audit_pos_iter (fun x => (step x, @nil (audit_wto_call V E))) middle fuel)
      as [last second].
    cbn in Hfirst, Hsecond |- *; constructor; [exact I|].
    rewrite !map_app; apply Forall_app; split; [exact Hfirst|].
    apply Forall_app; split; [exact Hsecond|repeat constructor].
  - cbn [audit_pos_iter].
    pose proof (IH initial) as Hfirst.
    destruct (audit_pos_iter (fun x => (step x, @nil (audit_wto_call V E))) initial fuel)
      as [middle first].
    pose proof (IH middle) as Hsecond.
    destruct (audit_pos_iter (fun x => (step x, @nil (audit_wto_call V E))) middle fuel)
      as [last second].
    cbn in Hfirst, Hsecond |- *; constructor; [exact I|].
    rewrite map_app; apply Forall_app; split; assumption.
  - cbn [audit_pos_iter]; repeat constructor.
Qed.

(** The counted traversal preserves the stated numeric envelope. *)
Lemma audit_wto_counted_numbers {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) :
    let n := audit_wto_input_order_bound p in
    let ceiling := 2 + n * S (Pos.to_nat (fuel p)) in
    let width := Nat.max (audit_dfs_full_input_width EV g p (Graph.entries g))
      (Pos.size_nat (Pos.of_succ_nat ceiling)) in
    Forall (audit_wto_event_numbers width ceiling) (snd (audit_wto_counted p)).
Proof.
  intros n ceiling width; unfold audit_wto_counted.
  pose proof (audit_dfs_full_counted_event_clock p FinSet.empty (Graph.entries g)) as Hdfs_clock.
  pose proof (audit_dfs_full_counted_event_output p FinSet.empty (Graph.entries g)) as Hdfs_output.
  pose proof (audit_dfs_full_counted_erases p FinSet.empty (Graph.entries g)) as Hdfs.
  destruct (audit_dfs_full_counted p FinSet.empty (Graph.entries g)) as [search dfs_events].
  change (search = dfs p FinSet.empty (Graph.entries g)) in Hdfs.
  pose proof (audit_wto_order_length_bound p) as Horder; rewrite <- Hdfs in Horder.
  change (length (rpo search) <= n) in Horder.
  set (vertices := Graph.entries g ++
    map (Graph.target g) (flat_map snd (Map.elements (out_index p)))).
  pose proof (audit_wto_order_keys p) as Horder_keys; rewrite <- Hdfs in Horder_keys.
  change (incl (rpo search) vertices) in Horder_keys.
  assert (Hall : forall edge, In edge (flat_map snd (Map.elements (out_index p))) ->
    In (Graph.target g edge) vertices).
  { intros edge Hin; subst vertices; apply in_or_app; right; now apply in_map. }
  assert (Hkeys : forall v, In v vertices -> Pos.size_nat (encode EV v) <= width).
  { intros v Hin; subst vertices.
    pose proof (audit_dfs_envelope_width EV g p (Graph.entries g) v Hin) as Hkey.
    change (Pos.size_nat (encode EV v) <= audit_dfs_full_input_width EV g p (Graph.entries g))
      in Hkey.
    unfold width; eapply Nat.le_trans; [exact Hkey|apply Nat.le_max_l]. }
  assert (Hwidth : forall value, Pos.to_nat value <= ceiling -> Pos.size_nat value <= width).
  { intros value Hvalue; unfold width.
    eapply Nat.le_trans; [exact (audit_dfs_clock_width value ceiling Hvalue)|apply Nat.le_max_r]. }
  assert (Hceiling : 2 + n * S (Pos.to_nat (fuel p)) <= ceiling) by reflexivity.
  assert (Hone : 1 + length (rpo search) <= ceiling).
  { unfold ceiling; pose proof (Pos2Nat.is_pos (fuel p)); nia. }
  pose proof (@audit_wto_ranks_numbers V E EV (rpo search) 1%positive Map.empty 1) as Hmap.
  assert (Hempty : audit_tarjan_map_numbers EV 1 Map.empty).
  { intros v value Hget; rewrite Map.get_empty in Hget; discriminate. }
  specialize (Hmap ltac:(reflexivity) Hempty).
  pose proof (@audit_wto_ranks_numbers_events V E EV (rpo search) 1%positive Map.empty
    ceiling width ltac:(cbn; lia) Hwidth) as Hranks.
  destruct (audit_wto_ranks_counted EV (rpo search) 1%positive Map.empty) as [ranks rank_events].
  change (audit_tarjan_map_numbers EV (1 + length (rpo search)) ranks) in Hmap.
  assert (Hmap' : audit_tarjan_map_numbers EV ceiling ranks).
  { eapply audit_tarjan_map_numbers_mono; [exact Hone|exact Hmap]. }
  cbn in Hranks |- *.
  set (depth := Pos.of_succ_nat (length (rpo search))).
  set (base := fun _ : list V => (@nil (wto_token V), @nil (audit_wto_call V E))).
  set (step := fun recur => audit_wto_layer_counted p ranks recur).
  assert (Hbase : forall region, incl region vertices -> length region <= n ->
    Forall (audit_wto_event_numbers width ceiling) (snd (base region))).
  { intros region Hregion Hlen; constructor. }
  pose proof (audit_wto_iter_numbers p vertices ranks depth base ceiling width n Hall Hceiling
    Hmap' Hwidth Hkeys Hbase (rpo search) Horder_keys Horder) as Hrun.
  pose proof (@audit_wto_iter_event_numbers V E _ width ceiling step base depth) as Hiter.
  change (Forall (audit_wto_event_numbers width ceiling)
    (snd (fst (audit_pos_iter (fun recur => (step recur, @nil (audit_wto_call V E)))
      base depth) (rpo search)))) in Hrun.
  destruct (audit_pos_iter (fun recur => (step recur, @nil (audit_wto_call V E))) base depth)
    as [run iter_events].
  cbn in Hrun; destruct (run (rpo search)) as [result events].
  cbn in Hrun, Hiter |- *; apply Forall_app; split.
  - apply Forall_map; apply Forall_forall; intros event Hin.
    apply Forall_forall with (x := event) in Hdfs_clock; [|exact Hin].
    apply Forall_forall with (x := event) in Hdfs_output; [|exact Hin].
    change (audit_dfs_full_event_clock event <= 2 + n) in Hdfs_clock.
    change (audit_dfs_full_event_output event <= 2 * (2 + n)) in Hdfs_output.
    split; unfold ceiling; pose proof (Pos2Nat.is_pos (fuel p)); nia.
  - constructor; [exact I|].
    apply Forall_app; split; [exact Hranks|].
    constructor.
    + split; [unfold ceiling; pose proof (Pos2Nat.is_pos (fuel p)); nia|].
      split; [apply Hwidth|]; unfold depth; rewrite SuccNat2Pos.id_succ; exact Hone.
    + apply Forall_app; split; [exact Hiter|].
      apply Forall_app; split; [exact Hrun|repeat constructor].
Qed.

(** * Counted output sizes *)

(** Extract the recorded WTO output size, or zero for other events. *)
Definition audit_wto_event_output {V E} (event : audit_wto_call V E) : nat :=
  match event with
  | AuditWtoOutput size => size
  | _ => 0
  end.

(** An output-size envelope remains valid when its bound grows. *)
Lemma audit_wto_outputs_mono {V E} small large (events : list (audit_wto_call V E)) :
    small <= large -> Forall (fun event => audit_wto_event_output event <= small) events ->
    Forall (fun event => audit_wto_event_output event <= large) events.
Proof.
  intros Hbound Hevents; eapply Forall_impl; [|exact Hevents].
  intros event Hsmall; cbn beta in Hsmall; lia.
Qed.

(** The choose traversal emits no WTO output-size events. *)
Lemma audit_wto_choose_no_output {V E} (EV : encoding V) ranks rest header :
    Forall (fun event => audit_wto_event_output event = 0)
      (snd (@audit_wto_choose_counted V E EV ranks rest header)).
Proof.
  revert header; induction rest as [|v rest IH]; intro header.
  - cbn [audit_wto_choose_counted]; repeat constructor.
  - cbn [audit_wto_choose_counted].
    assert (Hhere : Forall (fun event => audit_wto_event_output event = 0)
      (snd (@audit_wto_earlier_counted V E EV ranks header v))).
    { unfold audit_wto_earlier_counted.
      destruct (Map.get EV header ranks); destruct (Map.get EV v ranks); destruct (Pos.leb _ _);
        cbn; repeat constructor. }
    destruct (audit_wto_earlier_counted EV ranks header v) as [next here].
    specialize (IH next).
    destruct (audit_wto_choose_counted EV ranks rest next) as [result events].
    cbn in Hhere, IH |- *; constructor; [reflexivity|].
    apply Forall_app; split; assumption.
Qed.

(** The remove traversal emits no WTO output-size events. *)
Lemma audit_wto_remove_no_output {V E} (EV : encoding V) header region :
    Forall (fun event => audit_wto_event_output event = 0)
      (snd (@audit_wto_remove_counted V E EV header region)).
Proof.
  induction region as [|v rest IH].
  - cbn [audit_wto_remove_counted]; repeat constructor.
  - cbn [audit_wto_remove_counted].
    destruct (audit_wto_remove_counted EV header rest) as [result events].
    cbn in IH |- *; destruct (Pos.eqb (encode EV header) (encode EV v)); cbn;
      repeat constructor; exact IH.
Qed.

(** The self edges traversal emits no WTO output-size events. *)
Lemma audit_wto_self_edges_no_output {V E} (EV : encoding V) (g : Graph.t V E) vertex edges :
    Forall (fun event => audit_wto_event_output event = 0)
      (snd (audit_wto_self_edges EV g vertex edges)).
Proof.
  induction edges as [|edge rest IH].
  - cbn [audit_wto_self_edges]; repeat constructor.
  - cbn [audit_wto_self_edges].
    destruct (audit_wto_self_edges EV g vertex rest) as [result events].
    cbn in IH |- *; repeat constructor; exact IH.
Qed.

(** Zero output sizes satisfy any natural-number upper bound. *)
Lemma audit_wto_no_output_bound {V E} bound (events : list (audit_wto_call V E)) :
    Forall (fun event => audit_wto_event_output event = 0) events ->
    Forall (fun event => audit_wto_event_output event <= bound) events.
Proof.
  intro Hevents; eapply Forall_impl; [|exact Hevents].
  intros event Hzero; cbn beta in Hzero; lia.
Qed.

(** The component traversal satisfies the stated output-size envelope. *)
Lemma audit_wto_component_outputs {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) ranks recur component :
    (forall region,
      length (fst (recur region)) <= length (snd (recur region)) /\
      Forall (fun event => audit_wto_event_output event <= length (snd (recur region)))
        (snd (recur region))) ->
    let '(result, events) := audit_wto_component_counted p ranks recur component in
    length result <= length events /\
    Forall (fun event => audit_wto_event_output event <= length events) events.
Proof.
  intro Hrecur; destruct component as [|h rest].
  - cbn [audit_wto_component_counted]; cbn; split; [lia|repeat constructor; lia].
  - unfold audit_wto_component_counted.
    pose proof (@audit_wto_choose_no_output V E EV ranks rest h) as Hchoose.
    destruct (audit_wto_choose_counted EV ranks rest h) as [header choose].
    cbn in Hchoose; destruct rest as [|v rest].
    + destruct (Map.get EV h (out_index p)) as [edges|].
      * pose proof (audit_wto_self_edges_no_output EV g h edges) as Hself.
        destruct (audit_wto_self_edges EV g h edges) as [self events].
        cbn in Hself |- *; destruct self; cbn; rewrite !length_app; cbn.
        all: split; [lia|].
        all: constructor; [cbn; lia|].
        all: apply Forall_app; split; [apply audit_wto_no_output_bound; exact Hchoose|].
        all: constructor; [cbn; lia|].
        all: constructor; [cbn; lia|].
        all: apply Forall_app; split; [apply audit_wto_no_output_bound; exact Hself|].
        all: repeat constructor; cbn; lia.
      * cbn [audit_wto_self_edges]; cbn; rewrite !length_app; cbn; split; try lia.
        constructor; [cbn; lia|].
        apply Forall_app; split.
        -- apply audit_wto_no_output_bound; exact Hchoose.
        -- repeat constructor; cbn; lia.
    + pose proof (@audit_wto_remove_no_output V E EV header (h :: v :: rest)) as Hremoved.
      destruct (audit_wto_remove_counted EV header (h :: v :: rest)) as [smaller removed].
      specialize (Hrecur smaller); destruct (recur smaller) as [inside events].
      cbn in Hremoved, Hrecur |- *; rewrite !length_app; cbn; rewrite ?length_app; cbn.
      split; [lia|].
      constructor; [cbn; lia|].
      apply Forall_app; split.
      * apply audit_wto_no_output_bound; exact Hchoose.
      * constructor; [cbn; lia|].
        apply Forall_app; split.
        -- apply audit_wto_no_output_bound; exact Hremoved.
        -- apply Forall_app; split.
           ++ eapply audit_wto_outputs_mono; [|exact (proj2 Hrecur)]; lia.
           ++ repeat constructor; cbn; lia.
Qed.

(** The components traversal satisfies the stated output-size envelope. *)
Lemma audit_wto_components_outputs {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) ranks recur components :
    (forall region,
      length (fst (recur region)) <= length (snd (recur region)) /\
      Forall (fun event => audit_wto_event_output event <= length (snd (recur region)))
        (snd (recur region))) ->
    let '(result, events) := audit_wto_components_counted p ranks recur components in
    length result <= length events /\ length components <= length events /\
    Forall (fun event => audit_wto_event_output event <= length events) events.
Proof.
  intro Hrecur; induction components as [|component rest IH].
  - cbn [audit_wto_components_counted]; cbn; split; [lia|].
    split; [lia|repeat constructor; lia].
  - cbn [audit_wto_components_counted].
    pose proof (audit_wto_component_outputs p ranks recur component Hrecur) as Hfirst.
    destruct (audit_wto_component_counted p ranks recur component) as [first here].
    destruct (audit_wto_components_counted p ranks recur rest) as [later events].
    cbn in Hfirst, IH |- *; rewrite !length_app; cbn; rewrite ?length_app; cbn.
    destruct Hfirst as [Hfirst_len Hfirst_events].
    destruct IH as [Hrest_len [Hcount Hrest_events]].
    split; [lia|].
    split; [lia|].
    constructor; [cbn; lia|].
    apply Forall_app; split.
    + eapply audit_wto_outputs_mono; [|exact Hfirst_events]; lia.
    + apply Forall_app; split.
      * eapply audit_wto_outputs_mono; [|exact Hrest_events]; lia.
      * repeat constructor; cbn; lia.
Qed.

(** The layer traversal satisfies the stated output-size envelope. *)
Lemma audit_wto_layer_outputs {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) ranks recur region :
    (forall part,
      length (fst (recur part)) <= length (snd (recur part)) /\
      Forall (fun event => audit_wto_event_output event <= length (snd (recur part)))
        (snd (recur part))) ->
    let '(result, events) := audit_wto_layer_counted p ranks recur region in
    length result <= length events /\
    Forall (fun event => audit_wto_event_output event <= length events) events.
Proof.
  intro Hrecur; unfold audit_wto_layer_counted.
  destruct (audit_scc_within_counted p region) as [scc events].
  pose proof (audit_wto_components_outputs p ranks recur (rev (components scc)) Hrecur) as Hbody.
  destruct (audit_wto_components_counted p ranks recur (rev (components scc))) as [result trace].
  cbn in Hbody |- *; rewrite length_rev in Hbody.
  rewrite !length_app, length_map; cbn.
  destruct Hbody as [Hresult [Hcount Houtputs]].
  split; [lia|].
  apply Forall_app; split.
  - apply Forall_map; apply Forall_forall; intros event Hin; cbn [audit_wto_event_output]; lia.
  - constructor; [cbn [audit_wto_event_output]; lia|].
    eapply audit_wto_outputs_mono; [|exact Houtputs]; lia.
Qed.

(** The iter traversal satisfies the stated output-size envelope. *)
Lemma audit_wto_iter_outputs {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) ranks fuel base :
    (forall region,
      length (fst (base region)) <= length (snd (base region)) /\
      Forall (fun event => audit_wto_event_output event <= length (snd (base region)))
        (snd (base region))) ->
    forall region,
      let run := fst (audit_pos_iter
        (fun recur => (audit_wto_layer_counted p ranks recur, @nil (audit_wto_call V E)))
        base fuel) in
      length (fst (run region)) <= length (snd (run region)) /\
      Forall (fun event => audit_wto_event_output event <= length (snd (run region)))
        (snd (run region)).
Proof.
  revert base; induction fuel as [fuel IH|fuel IH|]; intros base Hbase region.
  - cbn [audit_pos_iter].
    pose proof (fun r => IH base Hbase r) as Hfirst.
    destruct (audit_pos_iter
      (fun recur => (audit_wto_layer_counted p ranks recur, @nil (audit_wto_call V E)))
      base fuel) as [middle first].
    pose proof (fun r => IH middle Hfirst r) as Hsecond.
    destruct (audit_pos_iter
      (fun recur => (audit_wto_layer_counted p ranks recur, @nil (audit_wto_call V E)))
      middle fuel) as [last second].
    pose proof (audit_wto_layer_outputs p ranks last region Hsecond) as Hlayer.
    cbn [fst] in *.
    destruct (audit_wto_layer_counted p ranks last region); exact Hlayer.
  - cbn [audit_pos_iter].
    pose proof (fun r => IH base Hbase r) as Hfirst.
    destruct (audit_pos_iter
      (fun recur => (audit_wto_layer_counted p ranks recur, @nil (audit_wto_call V E)))
      base fuel) as [middle first].
    pose proof (IH middle Hfirst region) as Hsecond.
    destruct (audit_pos_iter
      (fun recur => (audit_wto_layer_counted p ranks recur, @nil (audit_wto_call V E)))
      middle fuel) as [last second].
    exact Hsecond.
  - pose proof (audit_wto_layer_outputs p ranks base region Hbase) as Hlayer.
    cbn [audit_pos_iter fst].
    destruct (audit_wto_layer_counted p ranks base region); exact Hlayer.
Qed.

(** The ranks traversal emits no WTO output-size events. *)
Lemma audit_wto_ranks_no_output {V E} (EV : encoding V) order clock m :
    Forall (fun event => audit_wto_event_output event = 0)
      (snd (@audit_wto_ranks_counted V E EV order clock m)).
Proof.
  revert clock m; induction order as [|v rest IH]; intros clock m.
  - cbn [audit_wto_ranks_counted]; repeat constructor.
  - cbn [audit_wto_ranks_counted].
    specialize (IH (Pos.succ clock) (Map.set EV v clock m)).
    destruct (audit_wto_ranks_counted EV rest (Pos.succ clock) (Map.set EV v clock m))
      as [result events].
    cbn in IH |- *; repeat constructor; exact IH.
Qed.

(** The iterator bookkeeping emits no WTO output-size events. *)
Lemma audit_wto_iter_no_output {V E A} (step : A -> A) initial fuel :
    Forall (fun event => audit_wto_event_output event = 0)
      (map (@audit_wto_iter_event V E)
        (snd (audit_pos_iter (fun x => (step x, @nil (audit_wto_call V E))) initial fuel))).
Proof.
  revert initial; induction fuel as [fuel IH|fuel IH|]; intro initial.
  - cbn [audit_pos_iter].
    pose proof (IH initial) as Hfirst.
    destruct (audit_pos_iter (fun x => (step x, @nil (audit_wto_call V E))) initial fuel)
      as [middle first].
    pose proof (IH middle) as Hsecond.
    destruct (audit_pos_iter (fun x => (step x, @nil (audit_wto_call V E))) middle fuel)
      as [last second].
    cbn in Hfirst, Hsecond |- *; constructor; [reflexivity|].
    rewrite !map_app; apply Forall_app; split; [exact Hfirst|].
    apply Forall_app; split; [exact Hsecond|repeat constructor].
  - cbn [audit_pos_iter].
    pose proof (IH initial) as Hfirst.
    destruct (audit_pos_iter (fun x => (step x, @nil (audit_wto_call V E))) initial fuel)
      as [middle first].
    pose proof (IH middle) as Hsecond.
    destruct (audit_pos_iter (fun x => (step x, @nil (audit_wto_call V E))) middle fuel)
      as [last second].
    cbn in Hfirst, Hsecond |- *; constructor; [reflexivity|].
    rewrite map_app; apply Forall_app; split; assumption.
  - cbn [audit_pos_iter]; repeat constructor.
Qed.

(** The counted traversal satisfies the stated output-size envelope. *)
Lemma audit_wto_counted_outputs {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) :
    let events := snd (audit_wto_counted p) in
    Forall (fun event => audit_wto_event_output event <=
      length events + audit_wto_input_order_bound p) events.
Proof.
  unfold audit_wto_counted.
  pose proof (audit_dfs_full_counted_erases p FinSet.empty (Graph.entries g)) as Hdfs.
  destruct (audit_dfs_full_counted p FinSet.empty (Graph.entries g)) as [search dfs_events].
  change (search = dfs p FinSet.empty (Graph.entries g)) in Hdfs.
  pose proof (audit_wto_order_length_bound p) as Horder; rewrite <- Hdfs in Horder.
  assert (Hpost : length (postorder search) <= audit_wto_input_order_bound p).
  { unfold rpo in Horder; rewrite <- rev_alt, length_rev in Horder; exact Horder. }
  pose proof (@audit_wto_ranks_no_output V E EV (rpo search) 1%positive Map.empty) as Hranks.
  destruct (audit_wto_ranks_counted EV (rpo search) 1%positive Map.empty) as [ranks rank_events].
  cbn in Hranks |- *.
  set (depth := Pos.of_succ_nat (length (rpo search))).
  set (base := fun _ : list V => (@nil (wto_token V), @nil (audit_wto_call V E))).
  set (step := fun recur => audit_wto_layer_counted p ranks recur).
  assert (Hbase : forall region, length (fst (base region)) <= length (snd (base region)) /\
    Forall (fun event => audit_wto_event_output event <= length (snd (base region)))
      (snd (base region))).
  { intro region; unfold base; cbn; split; [lia|constructor]. }
  pose proof (audit_wto_iter_outputs p ranks depth base Hbase (rpo search)) as Hrun.
  pose proof (@audit_wto_iter_no_output V E _ step base depth) as Hiter.
  change (length (fst (fst (audit_pos_iter
    (fun recur => (step recur, @nil (audit_wto_call V E))) base depth) (rpo search))) <=
      length (snd (fst (audit_pos_iter
        (fun recur => (step recur, @nil (audit_wto_call V E))) base depth) (rpo search))) /\
    Forall (fun event => audit_wto_event_output event <=
      length (snd (fst (audit_pos_iter
        (fun recur => (step recur, @nil (audit_wto_call V E))) base depth) (rpo search))))
      (snd (fst (audit_pos_iter
        (fun recur => (step recur, @nil (audit_wto_call V E))) base depth) (rpo search)))) in Hrun.
  destruct (audit_pos_iter (fun recur => (step recur, @nil (audit_wto_call V E))) base depth)
    as [run iter_events].
  cbn in Hrun; destruct (run (rpo search)) as [result events].
  cbn in Hrun, Hiter |- *.
  repeat rewrite length_app; rewrite !length_map; cbn [length];
    repeat rewrite length_app; cbn [length].
  apply Forall_app; split.
  - apply Forall_map; apply Forall_forall; intros event Hin; cbn [audit_wto_event_output]; lia.
  - constructor; [cbn [audit_wto_event_output]; lia|].
    apply Forall_app; split; [apply audit_wto_no_output_bound; exact Hranks|].
    constructor; [cbn [audit_wto_event_output]; lia|].
    apply Forall_app; split; [apply audit_wto_no_output_bound; exact Hiter|].
    apply Forall_app; split.
    + eapply audit_wto_outputs_mono; [|exact (proj2 Hrun)].
      repeat rewrite length_app; rewrite ?length_map; cbn; lia.
    + constructor; [|constructor].
      cbn [audit_wto_event_output]; repeat rewrite length_app; rewrite ?length_map; cbn; lia.
Qed.

(** * Per-event model work *)

(** Variable work from traversal outputs, depth conversion, and WTO output. *)
Definition audit_wto_event_extra {V E} (event : audit_wto_call V E) : nat :=
  match event with
  | AuditWtoDfs nested => audit_dfs_full_event_output nested
  | AuditWtoScc nested => audit_tarjan_event_output nested
  | AuditWtoDepth len depth => S len + len * Pos.size_nat depth
  | AuditWtoOutput size => S size
  | _ => 0
  end.

(** A DFS event uses only keys within the stated width envelope. *)
Lemma audit_wto_dfs_event_width {V E} (EV : encoding V) vertices width
    (event : audit_dfs_full_call V E) :
    (forall v, In v vertices -> audit_key_bits_weight (encode EV v) <= width) ->
    audit_dfs_full_event_keys vertices event -> audit_dfs_full_event_width EV event <= width.
Proof.
  intros Hwidth Hkeys; destruct event as [site|edge target|v set result|v index result|
    v via before after|v before after|detail|pre post];
    cbn [audit_dfs_full_event_keys audit_dfs_full_event_width] in *; try lia; try now apply Hwidth.
  destruct detail; cbn [audit_dfs_full_event_keys audit_dfs_full_event_width] in *;
    try lia; now apply Hwidth.
Qed.

(** SCC event work is bounded by key width and its output size. *)
Lemma audit_wto_scc_event_work {V E} (EV : encoding V) vertices ceiling width
    (event : audit_tarjan_call V E) :
    (forall v, In v vertices -> audit_key_bits_weight (encode EV v) <= width) ->
    (forall value, Pos.to_nat value <= ceiling -> Pos.size_nat value <= width) ->
    audit_tarjan_event_keys vertices event -> audit_tarjan_event_numbers ceiling event ->
    audit_tarjan_event_work EV event <= 140 + 12 * width + audit_tarjan_event_output event.
Proof.
  intros Hkeys Hnumbers Hkey Hnumber.
  destruct event as [site|edge target|v set result|v map value|v before after|
    v number before after|v rest before after|helper|v set|left right].
  all: try (eapply Nat.le_trans;
    [eapply audit_tarjan_internal_event_work_bound; eauto; exact I|cbn; lia]).
  unfold audit_tarjan_event_work; cbn [audit_tarjan_event_output]; lia.
Qed.

(** The event satisfies the stated work bound. *)
Lemma audit_wto_event_work_bound {V E} (EV : encoding V) vertices ceiling width
    (event : audit_wto_call V E) :
    (forall v, In v vertices -> audit_key_bits_weight (encode EV v) <= width) ->
    (forall value, Pos.to_nat value <= ceiling -> Pos.size_nat value <= width) ->
    Pos.size_nat (Pos.of_succ_nat ceiling) <= width ->
    audit_wto_event_keys vertices event -> audit_wto_event_numbers width ceiling event ->
    audit_wto_event_work EV event <= 256 + 24 * width + audit_wto_event_extra event.
Proof.
  intros Hkeys Hnumbers Hclockwidth Hkey Hnumber.
  destruct event as [site|dfs|scc|v m result|v m result|v value m|before after|
    a b result|v code|edge target|a b result|len depth|size];
    cbn [audit_wto_event_keys audit_wto_event_numbers] in Hkey, Hnumber;
    unfold audit_wto_event_work, audit_wto_event_extra; cbn.
  - lia.
  - change (64 + audit_dfs_full_model_event EV dfs <=
      256 + 24 * width + audit_dfs_full_event_output dfs).
    pose proof (audit_wto_dfs_event_width EV vertices width dfs Hkeys Hkey) as Hwidth.
    destruct Hnumber as [Hclock Houtput].
    pose proof (audit_dfs_full_model_event_bound EV dfs width ceiling Hwidth Hclock) as Hwork.
    rewrite Nat.max_l in Hwork by exact Hclockwidth; lia.
  - destruct Hnumber as [Hnumber Houtput].
    change (64 + audit_tarjan_event_work EV scc <=
      256 + 24 * width + audit_tarjan_event_output scc).
    pose proof (audit_wto_scc_event_work EV vertices ceiling width scc Hkeys Hnumbers Hkey Hnumber)
      as Hwork; lia.
  - specialize (Hkeys v Hkey); unfold audit_encoding_weight, audit_key_bits_weight,
      audit_get_weight in *; lia.
  - specialize (Hkeys v Hkey); unfold audit_encoding_weight, audit_key_bits_weight,
      audit_get_weight in *; lia.
  - specialize (Hkeys v Hkey); unfold audit_encoding_weight, audit_key_bits_weight,
      audit_set_weight in *; lia.
  - change (64 + audit_binary_weight (Z.pos before) 1 <= 256 + 24 * width + 0).
    unfold audit_binary_weight; rewrite audit_dfs_positive_z_bits.
    change (64 + (1 + Pos.size_nat before + 1) <= 256 + 24 * width + 0); lia.
  - destruct Hnumber as [Ha Hb].
    change (64 + audit_binary_weight (Z.pos a) (Z.pos b) <= 256 + 24 * width + 0).
    unfold audit_binary_weight; rewrite !audit_dfs_positive_z_bits; lia.
  - unfold audit_encoding_weight, audit_key_bits_weight; lia.
  - lia.
  - destruct Hnumber as [Ha Hb].
    change (64 + audit_binary_weight (Z.pos a) (Z.pos b) <= 256 + 24 * width + 0).
    unfold audit_binary_weight; rewrite !audit_dfs_positive_z_bits; lia.
  - change (64 + (S len + len * Pos.size_nat depth) <=
      256 + 24 * width + (S len + len * Pos.size_nat depth)); lia.
  - lia.
Qed.

(** A positive number has binary size at most its natural value. *)
Lemma audit_wto_positive_size_bound (value : positive) : Pos.size_nat value <= Pos.to_nat value.
Proof.
  induction value as [value IH|value IH|]; cbn [Pos.size_nat];
    try rewrite Pos2Nat.inj_xI; try rewrite Pos2Nat.inj_xO; try lia.
Qed.

(** Numeric and output envelopes bound the extra work of one event. *)
Lemma audit_wto_event_extra_bound {V E} width ceiling count n (event : audit_wto_call V E) :
    audit_wto_event_numbers width ceiling event ->
    audit_wto_event_output event <= count + n ->
    audit_wto_event_extra event <= 2 * ceiling + S ceiling * S ceiling + count + n + 1.
Proof.
  intros Hnumbers Houtput.
  destruct event as [site|dfs|scc|v m result|v m result|v value m|before after|
    a b result|v code|edge target|a b result|len depth|size];
    cbn [audit_wto_event_numbers audit_wto_event_output audit_wto_event_extra] in *;
    try lia.
  destruct Hnumbers as [Hlen [Hwidth Hdepth]].
  pose proof (audit_wto_positive_size_bound depth) as Hsize; nia.
Qed.

(** The input event bound has room for the numeric and output overhead. *)
Lemma audit_wto_input_budget_room {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) :
    let n := audit_wto_input_order_bound p in
    let ceiling := 2 + n * S (Pos.to_nat (fuel p)) in
    2 * ceiling + S ceiling * S ceiling + n + 1 <= audit_wto_input_event_bound p.
Proof.
  intros n ceiling; unfold audit_wto_input_event_bound; fold n.
  set (f := S (Pos.to_nat (fuel p))).
  set (m := audit_wto_input_max_out p).
  set (s := (3 + n * (12 + 12 * f)) * (12 + 6 * S (n * f))).
  set (x := S (s + n * (m + n) + f)).
  set (power := Nat.pow (S n) (S n)).
  change (2 * ceiling + S ceiling * S ceiling + n + 1 <= 1024 * power * Nat.pow x 3).
  assert (Hf : 1 <= f) by (unfold f; lia).
  assert (Hs : 2 + n * f <= s).
  { unfold s; eapply Nat.le_trans with (m := 12 + 6 * S (n * f)); [lia|].
    replace (12 + 6 * S (n * f)) with (1 * (12 + 6 * S (n * f))) at 1 by lia.
    apply Nat.mul_le_mono_r; lia. }
  clearbody s.
  assert (Hceil : ceiling <= x) by (unfold ceiling, x; lia).
  assert (Hn : n <= x) by (unfold x; nia).
  assert (Hx : 1 <= x) by (unfold x; lia).
  assert (Hpower : 1 <= power).
  { unfold power; apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia. }
  assert (Hquadratic : 2 * ceiling + S ceiling * S ceiling + n + 1 <= 10 * (x * x)).
  { clear - Hceil Hn Hx; clearbody ceiling n x; nia. }
  assert (Hcube : x * x <= Nat.pow x 3).
  { replace (Nat.pow x 3) with (x * x * x) by (cbn [Nat.pow]; lia).
    replace (x * x) with (x * x * 1) at 1 by lia.
    apply Nat.mul_le_mono_l; exact Hx. }
  assert (Hscaled : 10 * (x * x) <= 1024 * power * Nat.pow x 3).
  { eapply Nat.le_trans with (m := 10 * Nat.pow x 3).
    - apply Nat.mul_le_mono_l; exact Hcube.
    - apply Nat.mul_le_mono_r; lia. }
  lia.
Qed.

(** Summing per-event work gives the stated trace-wide bound. *)
Lemma audit_wto_event_sum_bound {V E} (EV : encoding V) vertices ceiling width count n
    (events : list (audit_wto_call V E)) :
    (forall v, In v vertices -> audit_key_bits_weight (encode EV v) <= width) ->
    (forall value, Pos.to_nat value <= ceiling -> Pos.size_nat value <= width) ->
    Pos.size_nat (Pos.of_succ_nat ceiling) <= width ->
    Forall (audit_wto_event_keys vertices) events ->
    Forall (audit_wto_event_numbers width ceiling) events ->
    Forall (fun event => audit_wto_event_output event <= count + n) events ->
    fold_right (fun event total => audit_wto_event_work EV event + total) 0 events <=
      length events * (256 + 24 * width + 2 * ceiling + S ceiling * S ceiling + count + n + 1).
Proof.
  intros Hkeys Hnumbers Hclockwidth Hkey_events Hnum_events Houtputs.
  induction events as [|event rest IH]; [reflexivity|].
  inversion Hkey_events as [|? ? Hkey Hkey_rest]; subst.
  inversion Hnum_events as [|? ? Hnumber Hnum_rest]; subst.
  inversion Houtputs as [|? ? Houtput Houtput_rest]; subst.
  specialize (IH Hkey_rest Hnum_rest Houtput_rest).
  pose proof (audit_wto_event_work_bound EV vertices ceiling width event Hkeys Hnumbers
    Hclockwidth Hkey Hnumber) as Hwork.
  pose proof (audit_wto_event_extra_bound width ceiling count n event Hnumber Houtput) as Hextra.
  cbn [fold_right length]; rewrite Nat.mul_succ_l; lia.
Qed.

(** The model budget absorbs trace length and per-event overhead. *)
Lemma audit_wto_work_arithmetic count bound width room total :
    count <= bound -> room <= bound ->
    total <= count * (256 + 24 * width + count + room) ->
    256 * S count * S count + total <=
      1024 * S bound * S bound + bound * (512 + 24 * width).
Proof.
  intros Hcount Hroom Hsum.
  assert (Hquad : 256 * S count * S count <= 256 * S bound * S bound).
  { apply Nat.mul_le_mono; [apply Nat.mul_le_mono_l|]; lia. }
  assert (Hlinear : count * (256 + 24 * width) <= bound * (256 + 24 * width)).
  { apply Nat.mul_le_mono_r; exact Hcount. }
  assert (Hextra : count * (count + room) <= 2 * S bound * S bound).
  { replace (2 * S bound * S bound) with (S bound * (2 * S bound)) by nia.
    apply Nat.mul_le_mono; lia. }
  nia.
Qed.

(** Input-derived widths bound keys in the vertex envelope and bounded clocks. *)
Lemma audit_wto_input_width_envelope {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) :
    let n := audit_wto_input_order_bound p in
    let ceiling := 2 + n * S (Pos.to_nat (fuel p)) in
    let width := Nat.max (audit_dfs_full_input_width EV g p (Graph.entries g))
      (Pos.size_nat (Pos.of_succ_nat ceiling)) in
    let vertices := Graph.entries g ++
      map (Graph.target g) (flat_map snd (Map.elements (out_index p))) in
    (forall v, In v vertices -> audit_key_bits_weight (encode EV v) <= width) /\
    (forall value, Pos.to_nat value <= ceiling -> Pos.size_nat value <= width) /\
    Pos.size_nat (Pos.of_succ_nat ceiling) <= width.
Proof.
  intros n ceiling width vertices; split.
  - intros v Hin; subst vertices.
    pose proof (audit_dfs_envelope_width EV g p (Graph.entries g) v Hin) as Hkey.
    change (audit_key_bits_weight (encode EV v) <=
      audit_dfs_full_input_width EV g p (Graph.entries g)) in Hkey.
    unfold width; eapply Nat.le_trans; [exact Hkey|apply Nat.le_max_l].
  - split.
    + intros value Hvalue; unfold width; eapply Nat.le_trans;
        [exact (audit_dfs_clock_width value ceiling Hvalue)|apply Nat.le_max_r].
    + unfold width; apply Nat.le_max_r.
Qed.

(** The counted traversal satisfies the stated work bound. *)
Lemma audit_wto_counted_work_bound {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) :
    audit_wto_model_work EV (snd (audit_wto_counted p)) <= audit_wto_input_budget EV g p.
Proof.
  set (n := audit_wto_input_order_bound p).
  set (ceiling := 2 + n * S (Pos.to_nat (fuel p))).
  set (width := Nat.max (audit_dfs_full_input_width EV g p (Graph.entries g))
    (Pos.size_nat (Pos.of_succ_nat ceiling))).
  set (vertices := Graph.entries g ++
    map (Graph.target g) (flat_map snd (Map.elements (out_index p)))).
  pose proof (audit_wto_input_width_envelope p) as [Hkeys [Hnumbers Hclockwidth]].
  change (forall v, In v vertices -> audit_key_bits_weight (encode EV v) <= width) in Hkeys.
  change (forall value, Pos.to_nat value <= ceiling -> Pos.size_nat value <= width) in Hnumbers.
  change (Pos.size_nat (Pos.of_succ_nat ceiling) <= width) in Hclockwidth.
  pose proof (audit_wto_counted_keys p) as Hkey_events.
  change (Forall (audit_wto_event_keys vertices) (snd (audit_wto_counted p))) in Hkey_events.
  pose proof (audit_wto_counted_numbers p) as Hnum_events.
  change (Forall (audit_wto_event_numbers width ceiling) (snd (audit_wto_counted p)))
    in Hnum_events.
  pose proof (audit_wto_counted_outputs p) as Houtputs.
  change (Forall (fun event => audit_wto_event_output event <=
    length (snd (audit_wto_counted p)) + n) (snd (audit_wto_counted p))) in Houtputs.
  pose proof (audit_wto_counted_event_bound p) as Hcount.
  pose proof (audit_wto_input_budget_room p) as Hroom.
  change (2 * ceiling + S ceiling * S ceiling + n + 1 <= audit_wto_input_event_bound p) in Hroom.
  destruct (audit_wto_counted p) as [result events].
  change (length events <= audit_wto_input_event_bound p) in Hcount.
  change (Forall (audit_wto_event_keys vertices) events) in Hkey_events.
  change (Forall (audit_wto_event_numbers width ceiling) events) in Hnum_events.
  change (Forall (fun event => audit_wto_event_output event <= length events + n) events)
    in Houtputs.
  pose proof (audit_wto_event_sum_bound EV vertices ceiling width (length events) n events
    Hkeys Hnumbers Hclockwidth Hkey_events Hnum_events Houtputs) as Hsum.
  unfold audit_wto_model_work, audit_wto_input_budget; fold n ceiling width.
  change (256 * S (length events) * S (length events) +
    fold_right (fun event total => audit_wto_event_work EV event + total) 0 events <=
    1024 * S (audit_wto_input_event_bound p) * S (audit_wto_input_event_bound p) +
    audit_wto_input_event_bound p * (512 + 24 * width)).
  apply (audit_wto_work_arithmetic (length events) (audit_wto_input_event_bound p) width
    (2 * ceiling + S ceiling * S ceiling + n + 1)); [exact Hcount|exact Hroom|].
  replace (256 + 24 * width + length events +
    (2 * ceiling + S ceiling * S ceiling + n + 1)) with
    (256 + 24 * width + 2 * ceiling + S ceiling * S ceiling + length events + n + 1) by lia.
  exact Hsum.
Qed.

(** Counted WTO construction returns the original WTO within its input-derived work budget. *)
Theorem audit_wto_counted_correct : audit_wto_counted_statement.
Proof.
  intros V E EV g p.
  pose proof (audit_wto_counted_result p) as Hresult.
  pose proof (audit_wto_counted_event_bound p) as Hcount.
  pose proof (audit_wto_counted_work_bound p) as Hwork.
  destruct (audit_wto_counted p) as [result events].
  change (result = wto_of p) in Hresult.
  change (length events <= audit_wto_input_event_bound p) in Hcount.
  change (audit_wto_model_work EV events <= audit_wto_input_budget EV g p) in Hwork.
  split; [exact Hresult|].
  split; assumption.
Qed.

(** Nested WTO construction keeps the counted result, trace and same-run callback work. *)
Theorem audit_wto_nested_holds : audit_wto_nested_statement.
Proof.
  apply audit_wto_nested_from_counted; exact audit_wto_counted_correct.
Qed.

(** * Concrete source work *)

(** Captured map-operation codes match the encoding of their actual keys. *)
Definition audit_wto_source_code_matches {V E B} (EV : encoding V)
    (item : audit_wto_nested_event V E (audit_graph_callback_capture V E B)) : Prop :=
  let '(event, body) := item in
  match event with
  | AuditWtoDfs nested => audit_dfs_source_code_matches EV (nested, body)
  | AuditWtoScc nested => audit_scc_source_code_matches EV (nested, body)
  | AuditWtoRead v _ _
  | AuditWtoEdges v _ _
  | AuditWtoWrite v _ _ => audit_dfs_source_code body = encode EV v
  | _ => True
  end.

(** Well-formed receipts identify the actual code used by each source event. *)
Lemma audit_wto_source_event_code {V E B} (EV : encoding V) (g : Graph.t V E)
    (cb : audit_dfs_callback_model V E B) item :
    audit_dfs_callbacks_erase EV g cb -> audit_wto_source_event_wellformed item ->
    audit_wto_event_receipts cb item -> audit_wto_source_code_matches EV item.
Proof.
  intros Hcallbacks Hshape Hreceipts; destruct item as [event body].
  destruct event as [site|dfs|scc|v m result|v m result|v value m|before after|
    a b result|v code|edge target|a b result|len depth|size];
    cbn [audit_wto_source_code_matches audit_wto_source_event_wellformed] in *; try exact I.
  all: try solve [eapply audit_dfs_source_event_code; eassumption].
  all: try solve [eapply audit_scc_source_event_code; eassumption].
  all: destruct Hshape as [code [trace Hbody]]; subst body;
    cbn [audit_wto_event_receipts] in Hreceipts; inversion Hreceipts as [|? ? Hreceipt ?];
    cbn [audit_dfs_source_code]; eapply audit_dfs_receipt_code; eauto.
Qed.

(** The source event satisfies the stated work bound. *)
Lemma audit_wto_source_event_work_bound {V E B} (EV : encoding V) (weight : B -> nat)
    vertices ceiling width
    (item : audit_wto_nested_event V E (audit_graph_callback_capture V E B)) :
    (forall v, In v vertices -> audit_key_bits_weight (encode EV v) <= width) ->
    (forall value, Pos.to_nat value <= ceiling -> Pos.size_nat value <= width) ->
    Pos.size_nat (Pos.of_succ_nat ceiling) <= width ->
    audit_wto_event_keys vertices (fst item) ->
    audit_wto_event_numbers width ceiling (fst item) -> audit_wto_source_code_matches EV item ->
    audit_wto_source_event_work weight item <=
      1024 + 128 * width + 4 * audit_wto_event_extra (fst item) +
      audit_wto_source_body_work weight [item].
Proof.
  intros Hkeys Hnumbers Hclockwidth Hkey Hnumber Hcode; destruct item as [event body].
  destruct event as [site|dfs|scc|v m result|v m result|v value m|before after|
    a b result|v code|edge target|a b result|len depth|size];
    cbn [fst audit_wto_event_keys audit_wto_event_numbers audit_wto_source_code_matches] in *;
    unfold audit_wto_source_event_work, audit_wto_source_body_work, audit_wto_event_extra; cbn;
    try lia.
  - destruct Hnumber as [Hclock Houtput].
    pose proof (audit_wto_dfs_event_width EV vertices width dfs Hkeys Hkey) as Hwidth.
    pose proof (audit_dfs_source_event_bound EV weight (dfs, body) width ceiling
      Hcode Hwidth Hclock)
      as Hwork.
    rewrite Nat.max_l in Hwork by exact Hclockwidth.
    change (audit_dfs_source_event_work weight (dfs, body) <=
      512 + 64 * width + 2 * audit_dfs_full_event_output dfs +
        (fold_right (fun item n => audit_graph_capture_work weight item + n) 0 body + 0)) in Hwork.
    change (64 + audit_dfs_source_event_work weight (dfs, body) <=
      1024 + 128 * width + 4 * audit_dfs_full_event_output dfs +
        (fold_right (fun item n => audit_graph_capture_work weight item + n) 0 body + 0)); lia.
  - destruct Hnumber as [Hnumber Houtput].
    pose proof (audit_scc_source_event_work_bound EV weight vertices ceiling width (scc, body)
      Hkeys Hnumbers Hkey Hnumber Hcode) as Hwork.
    change (audit_scc_source_event_work weight (scc, body) <=
      512 + 64 * width + 2 * audit_tarjan_event_output scc +
        (fold_right (fun item n => audit_graph_capture_work weight item + n) 0 body + 0)) in Hwork.
    change (64 + audit_scc_source_event_work weight (scc, body) <=
      1024 + 128 * width + 4 * audit_tarjan_event_output scc +
        (fold_right (fun item n => audit_graph_capture_work weight item + n) 0 body + 0)); lia.
  - rewrite Hcode; pose proof (audit_trie_get_source_work_bound _ (encode EV v) m) as Hget.
    specialize (Hkeys v Hkey); unfold audit_key_bits_weight in Hkeys; lia.
  - rewrite Hcode; pose proof (audit_trie_get_source_work_bound _ (encode EV v) m) as Hget.
    specialize (Hkeys v Hkey); unfold audit_key_bits_weight in Hkeys; lia.
  - rewrite Hcode.
    pose proof (audit_trie_update_source_work_bound _ (encode EV v) (Some (v, value)) m) as Hset.
    specialize (Hkeys v Hkey); unfold audit_key_bits_weight in Hkeys; lia.
  - change (64 + (fold_right (fun item n => audit_graph_capture_work weight item + n) 0 body) +
      S len + 2 * S len * S (Pos.size_nat depth) <=
      1024 + 128 * width + 4 * (S len + len * Pos.size_nat depth) +
      (fold_right (fun item n => audit_graph_capture_work weight item + n) 0 body + 0)).
    destruct Hnumber as [_ [Hbits _]].
    set (bits := Pos.size_nat depth) in *.
    set (callback := fold_right (fun item n => audit_graph_capture_work weight item + n) 0 body)
      in *.
    clear - Hbits.
    clearbody bits callback.
    nia.
Qed.

(** The source trace bound includes every captured callback body. *)
Lemma audit_wto_source_sum_bound {V E B} (EV : encoding V) (g : Graph.t V E)
    (cb : audit_dfs_callback_model V E B) (weight : B -> nat) vertices ceiling width count n
    (events : list (audit_wto_nested_event V E (audit_graph_callback_capture V E B))) :
    audit_dfs_callbacks_erase EV g cb ->
    (forall v, In v vertices -> audit_key_bits_weight (encode EV v) <= width) ->
    (forall value, Pos.to_nat value <= ceiling -> Pos.size_nat value <= width) ->
    Pos.size_nat (Pos.of_succ_nat ceiling) <= width ->
    Forall (fun item => audit_wto_event_keys vertices (fst item)) events ->
    Forall (fun item => audit_wto_event_numbers width ceiling (fst item)) events ->
    Forall (fun item => audit_wto_event_output (fst item) <= count + n) events ->
    Forall audit_wto_source_event_wellformed events ->
    Forall (audit_wto_event_receipts cb) events ->
    audit_wto_source_work weight events <=
      length events * (1024 + 128 * width +
        4 * (2 * ceiling + S ceiling * S ceiling + count + n + 1)) +
      audit_wto_source_body_work weight events.
Proof.
  intros Hcallbacks Hkeys Hnumbers Hclockwidth Hkey_events Hnum_events Houtputs Hshape Hreceipts.
  induction events as [|[event body] rest IH]; [reflexivity|].
  inversion Hkey_events as [|? ? Hkey Hkey_rest]; subst.
  inversion Hnum_events as [|? ? Hnumber Hnum_rest]; subst.
  inversion Houtputs as [|? ? Houtput Houtput_rest]; subst.
  inversion Hshape as [|? ? Hwell Hshape_rest]; subst.
  inversion Hreceipts as [|? ? Hreceipt Hreceipt_rest]; subst.
  specialize (IH Hkey_rest Hnum_rest Houtput_rest Hshape_rest Hreceipt_rest).
  pose proof (audit_wto_source_event_code EV g cb (event, body) Hcallbacks Hwell Hreceipt) as Hcode.
  pose proof (audit_wto_source_event_work_bound EV weight vertices ceiling width (event, body)
    Hkeys Hnumbers Hclockwidth Hkey Hnumber Hcode) as Hwork.
  pose proof (audit_wto_event_extra_bound width ceiling count n event Hnumber Houtput) as Hextra.
  change (audit_wto_source_event_work weight (event, body) + audit_wto_source_work weight rest <=
    S (length rest) * (1024 + 128 * width +
      4 * (2 * ceiling + S ceiling * S ceiling + count + n + 1)) +
    (fold_right (fun capture total => audit_graph_capture_work weight capture + total) 0 body +
      audit_wto_source_body_work weight rest)).
  change (audit_wto_source_event_work weight (event, body) <=
    1024 + 128 * width + 4 * audit_wto_event_extra event +
      (fold_right (fun capture total => audit_graph_capture_work weight capture + total)
        0 body + 0))
    in Hwork.
  rewrite Nat.mul_succ_l; lia.
Qed.

(** The source budget absorbs trace overhead while retaining body work. *)
Lemma audit_wto_source_arithmetic count bound width room body :
    count <= bound -> room <= bound ->
    count * (1024 + 128 * width + 4 * (count + room)) + body <=
      4096 * Nat.pow (S bound) 3 + bound * (1024 + 128 * width) + body.
Proof.
  intros Hcount Hroom.
  assert (Hlinear : count * (1024 + 128 * width) <= bound * (1024 + 128 * width)).
  { apply Nat.mul_le_mono_r; exact Hcount. }
  assert (Hquad : count * (count + room) <= 2 * S bound * S bound).
  { replace (2 * S bound * S bound) with (S bound * (2 * S bound)) by nia.
    apply Nat.mul_le_mono; lia. }
  assert (Hcube : S bound * S bound <= Nat.pow (S bound) 3).
  { replace (Nat.pow (S bound) 3) with (S bound * S bound * S bound) by (cbn [Nat.pow]; lia).
    replace (S bound * S bound) with (S bound * S bound * 1) at 1 by lia.
    apply Nat.mul_le_mono_l; lia. }
  assert (Hscaled : 8 * (S bound * S bound) <= 4096 * Nat.pow (S bound) 3).
  { eapply Nat.le_trans with (m := 8 * Nat.pow (S bound) 3).
    - apply Nat.mul_le_mono_l; exact Hcube.
    - apply Nat.mul_le_mono_r; lia. }
  nia.
Qed.

(** Captured source execution returns the WTO and prices its actual recursive callbacks. *)
Theorem audit_wto_source_holds : audit_wto_source_statement.
Proof.
  intros V E B EV g p cb weight Hcallbacks.
  set (n := audit_wto_input_order_bound p).
  set (ceiling := 2 + n * S (Pos.to_nat (fuel p))).
  set (width := Nat.max (audit_dfs_full_input_width EV g p (Graph.entries g))
    (Pos.size_nat (Pos.of_succ_nat ceiling))).
  set (vertices := Graph.entries g ++
    map (Graph.target g) (flat_map snd (Map.elements (out_index p)))).
  pose proof (audit_wto_input_width_envelope p) as [Hkeys [Hnumbers Hclockwidth]].
  change (forall v, In v vertices -> audit_key_bits_weight (encode EV v) <= width) in Hkeys.
  change (forall value, Pos.to_nat value <= ceiling -> Pos.size_nat value <= width) in Hnumbers.
  change (Pos.size_nat (Pos.of_succ_nat ceiling) <= width) in Hclockwidth.
  pose proof (audit_wto_source_erases p cb Hcallbacks) as Herase.
  pose proof (audit_wto_counted_result p) as Hresult.
  pose proof (audit_wto_counted_event_bound p) as Hcount.
  pose proof (audit_wto_counted_keys p) as Hkey_events.
  change (Forall (audit_wto_event_keys vertices) (snd (audit_wto_counted p))) in Hkey_events.
  pose proof (audit_wto_counted_numbers p) as Hnum_events.
  change (Forall (audit_wto_event_numbers width ceiling) (snd (audit_wto_counted p)))
    in Hnum_events.
  pose proof (audit_wto_counted_outputs p) as Houtputs.
  change (Forall (fun event => audit_wto_event_output event <=
    length (snd (audit_wto_counted p)) + n) (snd (audit_wto_counted p))) in Houtputs.
  pose proof (audit_wto_source_event_correspondence_holds V E B EV g p cb Hcallbacks) as Hshape.
  pose proof (audit_wto_source_receipts p cb) as Hreceipts.
  pose proof (audit_wto_input_budget_room p) as Hroom.
  change (2 * ceiling + S ceiling * S ceiling + n + 1 <= audit_wto_input_event_bound p) in Hroom.
  destruct (audit_wto_source_counted p cb) as [result events].
  destruct (audit_wto_counted p) as [counted trace].
  change ((result, map fst events) = (counted, trace)) in Herase.
  inversion Herase; subst counted trace.
  change (result = wto_of p) in Hresult.
  change (length (map fst events) <= audit_wto_input_event_bound p) in Hcount.
  change (Forall (audit_wto_event_keys vertices) (map fst events)) in Hkey_events.
  change (Forall (audit_wto_event_numbers width ceiling) (map fst events)) in Hnum_events.
  change (Forall (fun event => audit_wto_event_output event <= length (map fst events) + n)
    (map fst events)) in Houtputs.
  change (Forall audit_wto_source_event_wellformed events /\
    Forall audit_wto_source_event_primitive events) in Hshape.
  change (Forall (audit_wto_event_receipts cb) events) in Hreceipts.
  rewrite length_map in Hcount, Houtputs.
  rewrite Forall_map in Hkey_events, Hnum_events, Houtputs.
  pose proof (audit_wto_source_sum_bound EV g cb weight vertices ceiling width (length events) n
    events Hcallbacks Hkeys Hnumbers Hclockwidth Hkey_events Hnum_events Houtputs (proj1 Hshape)
    Hreceipts) as Hsum.
  split; [exact Hresult|].
  split; [exact Hcount|].
  unfold audit_wto_source_budget; fold n ceiling width.
  change (audit_wto_source_work weight events <=
    4096 * Nat.pow (S (audit_wto_input_event_bound p)) 3 +
    audit_wto_input_event_bound p * (1024 + 128 * width) +
    audit_wto_source_body_work weight events).
  eapply Nat.le_trans; [exact Hsum|].
  replace (1024 + 128 * width + 4 *
    (2 * ceiling + S ceiling * S ceiling + length events + n + 1)) with
    (1024 + 128 * width + 4 *
      (length events + (2 * ceiling + S ceiling * S ceiling + n + 1))) by lia.
  apply audit_wto_source_arithmetic; assumption.
Qed.

(** External callback adapters bound the bodies captured by the same source execution. *)
Theorem audit_wto_source_adapted_holds : audit_wto_source_adapted_statement.
Proof.
  apply audit_wto_source_adapted_from_source; exact audit_wto_source_holds.
Qed.

(** The complete source contract combines WTO, traversal and primitive obligations. *)
Theorem audit_wto_source_contract_holds : audit_wto_source_contract_statement.
Proof.
  split; [exact audit_wto_source_holds|].
  split; [exact audit_wto_source_adapted_holds|].
  split; [exact audit_scc_source_contract_correct|].
  split; [exact audit_dfs_source_contract_holds|].
  split; [exact audit_graph_reverse_fast_counted_holds|].
  split; [exact audit_nat_encode_run_total|].
  split; [exact audit_nat_encode_run_correct|].
  split; [exact audit_positive_order|exact audit_wto_source_event_correspondence_holds].
Qed.
