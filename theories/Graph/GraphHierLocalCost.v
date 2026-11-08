(** * Hierarchy primitive budgets

    Primitive bounds retain all map, set, adjacency, callback and traversal charges.
    For example, entry indexing pays for absent target owners as well as present ones.
    Builds on: GraphHier and the public Cost and container bounds. *)

From Stdlib Require Import List Bool PArith NArith Arith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet BaseTacticsInv.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor GraphSearchSpec
  GraphSearchCost GraphSearchInvariant GraphSccSpec GraphHierSpec GraphHier GraphHierWork
  GraphHierEntries.
Import List.ListNotations Cost.Notations.
Local Open Scope N_scope.

Module HierLocalCost.

Definition id_cost w := 1 + 2 * w.

(** Key lookup is bounded by the supplied encoded width on arbitrary storage. *)
Theorem get_cost {A} w v (m : Map.t positive A) :
  key_bits positive_encoding v <= w ->
    Cost.ticks (Map.get_c positive_encoding v m) <= id_cost w.
Proof.
  intro Hwidth. rewrite Map.get_cost.
  pose proof (encode_cost_bound positive_encoding_cost_laws v).
  fold (key_bits positive_encoding v). unfold id_cost. nia.
Qed.

(** Key insertion is bounded by the supplied encoded width on arbitrary storage. *)
Theorem set_cost {A} w v a (m : Map.t positive A) :
  key_bits positive_encoding v <= w ->
    Cost.ticks (Map.set_c positive_encoding v a m) <= id_cost w.
Proof.
  intro Hwidth. rewrite Map.set_cost.
  pose proof (encode_cost_bound positive_encoding_cost_laws v).
  fold (key_bits positive_encoding v). unfold id_cost. nia.
Qed.

(** Finite component-position keys share a budget independent of any produced result. *)
Definition counter_width {V E} (p : Prepared.t V E) w :=
  forall i, (Pos.to_nat i <= length (Graph.nodes (Prepared.graph p)))%nat ->
    key_bits positive_encoding i <= w.

Definition owner_width r w :=
  forall v i, Map.get positive_encoding v (Scc.comp_of r) = Some i ->
    key_bits positive_encoding i <= w.

(** Header offers pay both the optional lookup and any selected insertion. *)
Theorem offer_cost w i v index :
  key_bits positive_encoding i <= w ->
    Cost.ticks (HierRun.offer_c i v index) <= 2 * id_cost w.
Proof.
  intro Hwidth. unfold HierRun.offer_c. rewrite Cost.ticks_bind.
  fold (Map.get positive_encoding i index).
  pose proof (get_cost w i index Hwidth).
  pose proof (set_cost w i v index Hwidth).
  destruct (Map.get positive_encoding i index); rewrite ?Cost.ticks_ret; nia.
Qed.

(** Every supplied root occurrence pays its lookup and any owner-index offer. *)
Theorem root_cost w r index v :
  key_bits positive_encoding v <= w -> owner_width r w ->
    Cost.ticks (HierRun.root_entry_c (Scc.comp_of r) index v) <= 3 * id_cost w.
Proof.
  intros Hwidth Howners. unfold HierRun.root_entry_c. rewrite Cost.ticks_bind.
  fold (Map.get positive_encoding v (Scc.comp_of r)).
  pose proof (get_cost w v (Scc.comp_of r) Hwidth).
  destruct (Map.get positive_encoding v (Scc.comp_of r)) as [i|] eqn:Howner.
  - pose proof (offer_cost w i v index (Howners v i Howner)). nia.
  - rewrite Cost.ticks_ret. nia.
Qed.

(** Outgoing entry tests retain absent-owner queries, owner comparisons and any header offer. *)
Theorem edge_cost w r source index v :
  key_bits positive_encoding v <= w -> owner_width r w ->
  (forall i, source = Some i -> key_bits positive_encoding i <= w) ->
    Cost.ticks (HierRun.edge_entry_c (Scc.comp_of r) source index v) <= 4 * id_cost w.
Proof.
  intros Hwidth Howners Hsource. unfold HierRun.edge_entry_c. rewrite Cost.ticks_bind.
  fold (Map.get positive_encoding v (Scc.comp_of r)).
  pose proof (get_cost w v (Scc.comp_of r) Hwidth) as Hget.
  destruct source as [i|]; destruct (Map.get positive_encoding v (Scc.comp_of r)) as [j|]
    eqn:Htarget; rewrite ?Cost.ticks_ret; try (unfold id_cost in *; nia).
  rewrite Cost.ticks_bind. fold (Map.code_compare i j).
  pose proof (Map.code_compare_cost i j) as Hcompare.
  specialize (Hsource i eq_refl).
  change (N.pos (Pos.size i) <= w) in Hsource.
  pose proof (offer_cost w j v index (Howners v j Htarget)) as Hoffer.
  destruct (Map.code_compare i j); rewrite ?Cost.ticks_ret; unfold id_cost in *; nia.
Qed.

(** A left-fold bound sums each actual callback charge without assuming its final accumulator. *)
Theorem fold_cost {A B} (f : B -> A -> Cost.t B) weight xs init :
  (forall current x, In x xs -> Cost.ticks (f current x) <= weight x) ->
    Cost.ticks (fold_left_c f xs init) <=
      HierWork.sum (fun x => 1 + weight x) xs.
Proof.
  revert init. induction xs as [|x rest IH]; intros init Hcost.
  - rewrite ticks_fold_left_c_nil. reflexivity.
  - rewrite ticks_fold_left_c_cons.
    change (1 + Cost.ticks (f init x) +
      Cost.ticks (fold_left_c f rest (Cost.value (f init x))) <=
      1 + weight x + HierWork.sum (fun x => 1 + weight x) rest).
    pose proof (Hcost init x (or_introl eq_refl)).
    pose proof (IH (Cost.value (f init x))
      ltac:(intros current y Hy; apply Hcost; now right)). lia.
Qed.

(** A vertex entry pass pays its source lookup, adjacency lookup and every outgoing occurrence. *)
Theorem vertex_cost {V E} (p : Prepared.t V E) w r index u :
  Prepared.ready p -> SearchCost.width_bound p [] w -> owner_width r w ->
  Prepared.valid_id p u ->
  Cost.ticks (HierRun.vertex_entries_c p (Scc.comp_of r) index u) <=
    16 * (1 + N.of_nat (length (Prepared.succ_edges p u))) * (1 + w).
Proof.
  intros Hready Hwidth Howners Hvalid.
  unfold HierRun.vertex_entries_c. rewrite !Cost.ticks_bind.
  fold (Map.get positive_encoding u (Scc.comp_of r)).
  fold (Prepared.succ_edges p u).
  pose proof (get_cost w u (Scc.comp_of r) (Hwidth u (or_introl Hvalid))) as Hget.
  pose proof (SearchCost.successors_cost p w u (Hwidth u (or_introl Hvalid))) as Hsucc.
  assert (Hfold :
    Cost.ticks (fold_left_c (fun entries eb => HierRun.edge_entry_c (Scc.comp_of r)
      (Map.get positive_encoding u (Scc.comp_of r)) entries (snd eb))
      (Prepared.succ_edges p u) index) <=
      N.of_nat (length (Prepared.succ_edges p u)) * (1 + 4 * id_cost w)).
  { pose proof (fold_cost
      (fun entries eb => HierRun.edge_entry_c (Scc.comp_of r)
        (Map.get positive_encoding u (Scc.comp_of r)) entries (snd eb))
      (fun _ => 4 * id_cost w) (Prepared.succ_edges p u) index) as Hbound.
    assert (Hstep : forall current eb, In eb (Prepared.succ_edges p u) ->
      Cost.ticks (HierRun.edge_entry_c (Scc.comp_of r)
        (Map.get positive_encoding u (Scc.comp_of r)) current (snd eb)) <= 4 * id_cost w).
    { intros current [e v] Hin. apply edge_cost.
      - apply Hwidth. left. exact (proj2 (SearchInvariant.successor_arc p u e v Hready Hvalid Hin)).
      - exact Howners.
      - intros i Hi. exact (Howners u i Hi). }
    specialize (Hbound Hstep).
    assert (Hsum : HierWork.sum (fun _ : E * positive => 1 + 4 * id_cost w)
      (Prepared.succ_edges p u) =
        N.of_nat (length (Prepared.succ_edges p u)) * (1 + 4 * id_cost w)).
    { apply HierWork.sum_constant. }
    cbn beta in Hbound. rewrite Hsum in Hbound. exact Hbound. }
  rewrite SearchCost.id_cost_equation in Hsucc. unfold id_cost in *. nia.
Qed.

(** Header selection pays a list step and at most one full key comparison per source occurrence. *)
Theorem select_cost w preferred c :
  (forall v, In v c -> key_bits positive_encoding v <= w) ->
  Cost.ticks (HierRun.select_c preferred c) <= N.of_nat (length c) * (1 + w).
Proof.
  induction c as [|v rest IH]; intro Hwidth; [reflexivity|].
  specialize (IH ltac:(intros x Hin; apply Hwidth; now right)).
  pose proof (Hwidth v (or_introl eq_refl)) as Hv.
  change (N.pos (Pos.size v) <= w) in Hv.
  cbn [HierRun.select_c]. autorewrite with galois_cost.
  destruct preferred as [h|]; autorewrite with galois_cost.
  - pose proof (Map.code_compare_cost v h).
    fold (Map.code_compare v h). destruct (Map.code_compare v h);
      autorewrite with galois_cost; cbn [length]; rewrite Nat2N.inj_succ; nia.
  - autorewrite with galois_cost. cbn [length]. rewrite Nat2N.inj_succ. nia.
Qed.

(** Child restriction charges header insertion and every body occurrence's set construction. *)
Theorem child_scope_cost w scope h body :
  key_bits positive_encoding h <= w ->
  (forall v, In v body -> key_bits positive_encoding v <= w) ->
  Cost.ticks (HierRun.child_scope_c scope h body) <=
    4 * (1 + N.of_nat (length body)) * (1 + w).
Proof.
  intros Hheader Hbody.
  unfold HierRun.child_scope_c. rewrite !Cost.ticks_bind, Cost.ticks_ret.
  pose proof (FinSet.of_list_numeric_cost Map.cost_laws_hold positive_encoding body w w
    ltac:(intros v Hv; split;
      [eapply N.le_trans; [exact (encode_cost_bound positive_encoding_cost_laws v)|apply Hbody, Hv]
      |apply Hbody, Hv])) as Hset.
  rewrite FinSet.add_cost.
  pose proof (encode_cost_bound positive_encoding_cost_laws h) as Hencode.
  fold (key_bits positive_encoding h). nia.
Qed.

(** The self-edge test pays adjacency lookup and each inspected key comparison. *)
Theorem self_loop_cost {V E} (p : Prepared.t V E) w h :
  key_bits positive_encoding h <= w ->
  Cost.ticks (HierRun.self_loop_c p h) <=
    SearchCost.id_cost w + N.of_nat (length (Prepared.succ_edges p h)) * (1 + w).
Proof.
  intro Hwidth. unfold HierRun.self_loop_c. rewrite Cost.ticks_bind.
  fold (Prepared.succ_edges p h).
  pose proof (SearchCost.successors_cost p w h Hwidth) as Hsucc.
  pose proof (ticks_existsb_c_le
    (fun eb : E * positive =>
      let* comparison := Map.code_compare_c h (snd eb) in
      Cost.ret (match comparison with Eq => true | _ => false end))
    w (Prepared.succ_edges p h)) as Hscan.
  assert (Hcallback : forall eb : E * positive,
    Cost.ticks
      (let* comparison := Map.code_compare_c h (snd eb) in
      Cost.ret (match comparison with Eq => true | _ => false end)) <= w).
  { intros [e target]. cbn [snd]. rewrite Cost.ticks_bind, Cost.ticks_ret.
    pose proof (Map.code_compare_cost h target).
    change (N.pos (Pos.size h) <= w) in Hwidth. nia. }
  specialize (Hscan Hcallback). nia.
Qed.

(** An entry pass pays every source row, outgoing occurrence and supplied root occurrence. *)
Theorem entries_cost {V E} (p : Prepared.t V E) w r roots :
  Prepared.ready p -> SearchCost.width_bound p roots w -> owner_width r w ->
  (forall v, In v (concat (Scc.components r)) -> Prepared.valid_id p v) ->
  Cost.ticks (HierRun.entries_c p roots r) <=
    32 * (N.of_nat (length roots) + N.of_nat (length (Scc.components r)) +
      N.of_nat (length (concat (Scc.components r))) +
      HierWork.outgoing p (concat (Scc.components r))) * (1 + w).
Proof.
  intros Hready Hwidth Howners Hvalid.
  assert (Hwidth' : SearchCost.width_bound p [] w).
  { intros v [Hv|Hfalse]; [apply Hwidth; now left|contradiction]. }
  unfold HierRun.entries_c. rewrite Cost.ticks_bind.
  pose proof (fold_cost (HierRun.root_entry_c (Scc.comp_of r))
    (fun _ => 3 * id_cost w) roots Map.empty
    ltac:(intros current v Hin; apply root_cost; [apply Hwidth; now right|exact Howners]))
    as Hroots.
  cbn beta in Hroots. rewrite HierWork.sum_constant in Hroots.
  assert (Hcomponents : forall index,
    Cost.ticks (fold_left_c (HierRun.component_entries_c p (Scc.comp_of r))
      (Scc.components r) index) <=
    N.of_nat (length (Scc.components r)) +
      17 * (N.of_nat (length (concat (Scc.components r))) +
        HierWork.outgoing p (concat (Scc.components r))) * (1 + w)).
  { intro index.
    assert (Hcomponent : forall current c, In c (Scc.components r) ->
      Cost.ticks (HierRun.component_entries_c p (Scc.comp_of r) current c) <=
        17 * (N.of_nat (length c) + HierWork.outgoing p c) * (1 + w)).
    { intros current c Hc. unfold HierRun.component_entries_c.
      pose proof (fold_cost (HierRun.vertex_entries_c p (Scc.comp_of r))
        (fun v => 16 * (1 + N.of_nat (length (Prepared.succ_edges p v))) * (1 + w))
        c current ltac:(intros before v Hv; apply vertex_cost; [exact Hready|exact Hwidth'|
          exact Howners|apply Hvalid, in_concat; exists c; auto])) as Hfold.
      eapply N.le_trans; [exact Hfold|].
      assert (Hpoint : forall v, In v c ->
        1 + 16 * (1 + N.of_nat (length (Prepared.succ_edges p v))) * (1 + w) <=
          17 * ((1 + N.of_nat (length (Prepared.succ_edges p v))) * (1 + w))).
      { intros v Hv. nia. }
      eapply N.le_trans; [apply HierWork.sum_mono, Hpoint|].
      rewrite HierWork.sum_scale.
      rewrite HierWork.source_work_scale. nia. }
    pose proof (fold_cost (HierRun.component_entries_c p (Scc.comp_of r))
      (fun c => 17 * (N.of_nat (length c) + HierWork.outgoing p c) * (1 + w))
      (Scc.components r) index Hcomponent) as Hfold.
    eapply N.le_trans; [exact Hfold|].
    cbn beta. rewrite HierWork.sum_add, HierWork.sum_constant,
      HierWork.sum_scale_r, HierWork.sum_scale, HierWork.source_partition.
    nia. }
  specialize (Hcomponents (Cost.value (fold_left_c
    (HierRun.root_entry_c (Scc.comp_of r)) roots Map.empty))).
  unfold id_cost in Hroots. nia.
Qed.

(** Preferred-header lookup retains the member query and its optional owner-index query. *)
Theorem preferred_cost w r index c :
  (forall v, In v c -> key_bits positive_encoding v <= w) -> owner_width r w ->
    Cost.ticks (HierRun.preferred_c (Scc.comp_of r) index c) <= 2 * id_cost w.
Proof.
  intros Hwidth Howners. destruct c as [|v rest]; [unfold id_cost; cbn; lia|].
  unfold HierRun.preferred_c. rewrite Cost.ticks_bind.
  fold (Map.get positive_encoding v (Scc.comp_of r)).
  pose proof (get_cost w v (Scc.comp_of r) (Hwidth v (or_introl eq_refl))).
  destruct (Map.get positive_encoding v (Scc.comp_of r)) as [i|] eqn:Howner.
  - pose proof (get_cost w i index (Howners v i Howner)). lia.
  - rewrite Cost.ticks_ret. unfold id_cost in *. nia.
Qed.

End HierLocalCost.
