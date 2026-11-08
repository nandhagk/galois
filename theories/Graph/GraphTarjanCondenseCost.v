(** * Condensation's finite work bounds

    Bounds count component members and every inspected outgoing occurrence before owner filtering.
    For example, an edge leaving the owned scope contributes work even when it produces no pair.
    Builds on: GraphCondense, BaseIndexCost and the public prepared-search cost laws. *)

From Stdlib Require Import List Bool PArith NArith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet BaseIndex BaseIndexCost
  BaseInternCost.
From Galois.Graph Require Import GraphPrepared GraphVisitor GraphSearchSpec GraphSearchInvariant
  GraphSearchCost GraphSccSpec GraphCondense.
Import List.ListNotations Cost.Notations.

Module TarjanCondenseCost.
Local Open Scope N_scope.

(** Inspected work counts all outgoing occurrences, including targets without a component owner. *)
Definition inspected {V E} (p : Prepared.t V E) vs :=
  fold_right (fun u n => (length (Prepared.succ_edges p u) + n)%nat) 0%nat vs.

Definition component_width r :=
  N.pos (Pos.size (Pos.of_succ_nat (length (Scc.components r)))).

Definition id_cost w := 1 + 2 * w.
Definition condense_k : N := 32.

(** Condensation size separates node-key width from the actual component-index width. *)
Definition size {V E} (p : Prepared.t V E) r w :=
  (1 + N.of_nat (length (Scc.components r)) +
    N.of_nat (length (concat (Scc.components r))) +
    N.of_nat (inspected p (concat (Scc.components r)))) *
    (1 + w + component_width r).

Local Lemma get_cost {A} w v (m : Map.t positive A) :
  key_bits positive_encoding v <= w ->
  Cost.ticks (Map.get_c positive_encoding v m) <= id_cost w.
Proof.
  intro Hwidth. rewrite Map.get_cost.
  pose proof (encode_cost_bound positive_encoding_cost_laws v).
  fold (key_bits positive_encoding v). unfold id_cost. nia.
Qed.

Local Lemma set_cost {A} w v a (m : Map.t positive A) :
  key_bits positive_encoding v <= w ->
  Cost.ticks (Map.set_c positive_encoding v a m) <= id_cost w.
Proof.
  intro Hwidth. rewrite Map.set_cost.
  pose proof (encode_cost_bound positive_encoding_cost_laws v).
  fold (key_bits positive_encoding v). unfold id_cost. nia.
Qed.

Local Lemma mem_cost w v s :
  key_bits positive_encoding v <= w ->
  Cost.ticks (FinSet.mem_c positive_encoding v s) <= id_cost w.
Proof.
  intro Hwidth. rewrite FinSet.mem_cost.
  pose proof (encode_cost_bound positive_encoding_cost_laws v).
  fold (key_bits positive_encoding v). unfold id_cost. nia.
Qed.

Local Lemma add_cost w v s :
  key_bits positive_encoding v <= w ->
  Cost.ticks (FinSet.add_c positive_encoding v s) <= id_cost w.
Proof.
  intro Hwidth. rewrite FinSet.add_cost.
  pose proof (encode_cost_bound positive_encoding_cost_laws v).
  fold (key_bits positive_encoding v). unfold id_cost. nia.
Qed.

Local Lemma present_length {A B} (f : A -> option B) xs :
  (length (Prepared.present f xs) <= length xs)%nat.
Proof.
  induction xs as [|x rest IH]; [reflexivity|].
  cbn [Prepared.present]. destruct (f x); cbn [length]; lia.
Qed.

Local Lemma present_cost {A B} (f : A -> Cost.t (option B)) xs k :
  (forall x, In x xs -> Cost.ticks (f x) <= k) ->
  Cost.ticks (Prepared.present_c f xs) <= N.of_nat (length xs) * (2 + k).
Proof.
  induction xs as [|x rest IH]; intro Hf; [reflexivity|].
  cbn [Prepared.present_c]. autorewrite with galois_cost.
  specialize (IH ltac:(intros y Hy; apply Hf; now right)).
  pose proof (Hf x (or_introl eq_refl)).
  cbn [length]. rewrite Nat2N.inj_succ. nia.
Qed.

Local Lemma vertex_length {V E} (p : Prepared.t V E) r u :
  (length (Condense.vertex p r u) <= length (Prepared.succ_edges p u))%nat.
Proof.
  rewrite Condense.vertex_equation.
  destruct (Map.get positive_encoding u (Scc.comp_of r)); [apply present_length|cbn; lia].
Qed.

Local Lemma vertex_cost {V E} (p : Prepared.t V E) r u w :
  key_bits positive_encoding u <= w ->
  (forall e v, In (e, v) (Prepared.succ_edges p u) -> key_bits positive_encoding v <= w) ->
  Cost.ticks (Condense.vertex_c p r u) <=
    2 * id_cost w + N.of_nat (length (Prepared.succ_edges p u)) * (2 + id_cost w).
Proof.
  intros Hu Htargets.
  pose proof (get_cost w u (Scc.comp_of r) Hu).
  pose proof (SearchCost.successors_cost p w u Hu).
  unfold Condense.vertex_c. autorewrite with galois_cost.
  fold (Map.get positive_encoding u (Scc.comp_of r)).
  destruct (Map.get positive_encoding u (Scc.comp_of r)) as [i|];
    autorewrite with galois_cost; [|nia].
  fold (Prepared.succ_edges p u).
  pose proof (present_cost (Condense.target_c r i) (Prepared.succ_edges p u)
    (id_cost w)) as Hpresent.
  assert (Hcallback : forall ev, In ev (Prepared.succ_edges p u) ->
    Cost.ticks (Condense.target_c r i ev) <= id_cost w).
  { intros [e v] He. unfold Condense.target_c. autorewrite with galois_cost.
    cbn [snd].
    destruct (Cost.value (Map.get_c positive_encoding v (Scc.comp_of r)));
      autorewrite with galois_cost; rewrite N.add_0_r;
      apply get_cost, (Htargets e v He). }
  specialize (Hpresent Hcallback). unfold id_cost, SearchCost.id_cost in *. nia.
Qed.

Local Lemma inspected_app {V E} (p : Prepared.t V E) xs ys :
  inspected p (xs ++ ys) = (inspected p xs + inspected p ys)%nat.
Proof.
  unfold inspected. rewrite fold_right_app.
  induction xs as [|x rest IH]; cbn [fold_right]; [reflexivity|]. lia.
Qed.

Local Lemma vertices_length {V E} (p : Prepared.t V E) r vs :
  (length (Condense.vertices p r vs) <= inspected p vs)%nat.
Proof.
  rewrite Condense.vertices_equation. induction vs as [|u rest IH]; [reflexivity|].
  cbn [flat_map inspected fold_right]. rewrite length_app.
  unfold inspected in IH.
  pose proof (vertex_length p r u). lia.
Qed.

(** Vertex traversal charges one visit per member and every outgoing target-owner lookup. *)
Theorem vertices_cost {V E} (p : Prepared.t V E) r vs w :
  (forall u, In u vs -> key_bits positive_encoding u <= w /\
    forall e v, In (e, v) (Prepared.succ_edges p u) ->
      key_bits positive_encoding v <= w) ->
  Cost.ticks (Condense.vertices_c p r vs) <=
    N.of_nat (length vs) * (1 + 2 * id_cost w) +
      N.of_nat (inspected p vs) * (3 + id_cost w).
Proof.
  intro Hkeys. unfold Condense.vertices_c.
  induction vs as [|u rest IH]; [reflexivity|].
  rewrite ticks_fold_right_c_cons. autorewrite with galois_cost.
  fold (Condense.vertex p r u).
  specialize (IH ltac:(intros v Hv; apply Hkeys; now right)).
  destruct (Hkeys u (or_introl eq_refl)) as [Hu Htargets].
  pose proof (vertex_cost p r u w Hu Htargets).
  pose proof (vertex_length p r u).
  cbn [length inspected fold_right]. rewrite Nat2N.inj_succ, Nat2N.inj_add.
  unfold inspected in IH. nia.
Qed.

(** Component traversal retains the copies of collected edge pairs in its charged concatenations. *)
Theorem cross_cost {V E} (p : Prepared.t V E) r w :
  (forall u, In u (concat (Scc.components r)) -> key_bits positive_encoding u <= w /\
    forall e v, In (e, v) (Prepared.succ_edges p u) ->
      key_bits positive_encoding v <= w) ->
  Cost.ticks (Condense.cross_edges_c p r) <=
    N.of_nat (length (Scc.components r)) +
    N.of_nat (length (concat (Scc.components r))) * (1 + 2 * id_cost w) +
    N.of_nat (inspected p (concat (Scc.components r))) * (4 + id_cost w).
Proof.
  unfold Condense.cross_edges_c.
  induction (Scc.components r) as [|vs rest IH]; intro Hkeys; [reflexivity|].
  rewrite ticks_fold_right_c_cons. autorewrite with galois_cost.
  fold (Condense.vertices p r vs).
  assert (Hvs : forall u, In u vs -> key_bits positive_encoding u <= w /\
    forall e v, In (e, v) (Prepared.succ_edges p u) ->
      key_bits positive_encoding v <= w).
  { intros u Hu. apply Hkeys. cbn [concat]. apply in_or_app. now left. }
  specialize (IH ltac:(intros u Hu; apply Hkeys; cbn [concat]; apply in_or_app; now right)).
  pose proof (vertices_cost p r vs w Hvs).
  pose proof (vertices_length p r vs).
  cbn [length concat]. rewrite length_app, inspected_app, Nat2N.inj_succ, !Nat2N.inj_add. nia.
Qed.

(** Cross-edge output cannot outnumber the inspected outgoing occurrences. *)
Theorem cross_length {V E} (p : Prepared.t V E) r :
  (length (Condense.cross_edges p r) <= inspected p (concat (Scc.components r)))%nat.
Proof.
  rewrite Condense.cross_edges_equation.
  induction (concat (Scc.components r)) as [|u rest IH]; [reflexivity|].
  cbn [flat_map inspected fold_right]. rewrite length_app.
  unfold inspected in IH.
  pose proof (vertex_length p r u). lia.
Qed.

(** Deduplication charges each bucket occurrence even when the target was already retained. *)
Theorem unique_cost xs seen w :
  (forall ev, In ev xs -> key_bits positive_encoding (snd ev) <= w) ->
  Cost.ticks (Condense.unique_c xs seen) <= N.of_nat (length xs) * (1 + 2 * id_cost w).
Proof.
  revert seen. induction xs as [|[i j] rest IH]; intros seen Hkeys; [reflexivity|].
  assert (Hj : key_bits positive_encoding j <= w) by exact (Hkeys (i, j) (or_introl eq_refl)).
  assert (Hrest : forall ev, In ev rest -> key_bits positive_encoding (snd ev) <= w).
  { intros ev He. apply Hkeys. now right. }
  pose proof (mem_cost w j seen Hj). pose proof (add_cost w j seen Hj).
  cbn [Condense.unique_c]. autorewrite with galois_cost.
  fold (FinSet.mem positive_encoding j seen).
  destruct (FinSet.mem positive_encoding j seen); autorewrite with galois_cost;
    [pose proof (IH seen Hrest)|pose proof (IH (FinSet.add positive_encoding j seen) Hrest)];
    fold (FinSet.add positive_encoding j seen);
    cbn [length]; rewrite Nat2N.inj_succ; nia.
Qed.

(** Proof indices enumerate the same component range as the charged row builder. *)
Fixpoint indices (cs : list (list positive)) start :=
  match cs with
  | [] => []
  | _ :: rest => start :: indices rest (Pos.succ start)
  end.

Local Lemma indices_range cs start i :
  In i (indices cs start) ->
    (Pos.to_nat start <= Pos.to_nat i < Pos.to_nat start + length cs)%nat.
Proof.
  revert start. induction cs as [|c rest IH]; intros start Hi; [contradiction|].
  cbn [indices In] in Hi. cbn [length].
  destruct Hi as [<-|Hi]; [lia|]. specialize (IH (Pos.succ start) Hi).
  rewrite Pos2Nat.inj_succ in IH. lia.
Qed.

Local Lemma indices_nodup cs start : NoDup (indices cs start).
Proof.
  revert start. induction cs as [|c rest IH]; intro start; cbn [indices]; constructor.
  - intro Hin. pose proof (indices_range rest (Pos.succ start) start Hin) as Hrange.
    rewrite Pos2Nat.inj_succ in Hrange. lia.
  - apply IH.
Qed.

Local Lemma matching_zero i ks :
  ~ In i ks ->
  fold_right (fun k n => if eqb positive_encoding i k then (1 + n)%N else n) 0 ks = 0.
Proof.
  induction ks as [|k rest IH]; intro Hnot; [reflexivity|].
  cbn [fold_right]. destruct (eqb_spec positive_encoding positive_encoding_laws i k).
  - subst k. exfalso. apply Hnot. now left.
  - apply IH. intro Hin. apply Hnot. now right.
Qed.

Local Lemma matching_bound i ks :
  NoDup ks ->
  fold_right (fun k n => if eqb positive_encoding i k then (1 + n)%N else n) 0 ks <= 1.
Proof.
  intro Hnodup. induction Hnodup as [|k rest Hnot Hnodup IH]; [cbn; lia|].
  cbn [fold_right]. destruct (eqb_spec positive_encoding positive_encoding_laws i k).
  - subst k. rewrite matching_zero by exact Hnot. lia.
  - exact IH.
Qed.

Local Lemma filter_mass_cons (ev : positive * positive) es ks :
  fold_right (fun k n => N.of_nat (length
    (filter (fun a => eqb positive_encoding (fst a) k) (ev :: es))) + n) 0 ks =
  fold_right (fun k n => N.of_nat (length
    (filter (fun a => eqb positive_encoding (fst a) k) es)) + n) 0 ks +
  fold_right (fun k n => if eqb positive_encoding (fst ev) k then 1 + n else n) 0 ks.
Proof.
  induction ks as [|k rest IH]; [reflexivity|].
  cbn [fold_right]. rewrite IH. cbn [filter].
  destruct (eqb positive_encoding (fst ev) k); cbn [length];
    rewrite ?Nat2N.inj_succ; lia.
Qed.

(** Distinct component rows inspect each collected pair in exactly one matching bucket at most. *)
Theorem bucket_mass (es : list (positive * positive)) ks :
  NoDup ks ->
  fold_right (fun k n => N.of_nat (length
    (Index.find positive_encoding k (Index.group_by positive_encoding fst es))) + n) 0 ks <=
      N.of_nat (length es).
Proof.
  intro Hnodup.
  assert (Hfind : forall k, Index.find positive_encoding k
    (Index.group_by positive_encoding fst es) =
    filter (fun a => eqb positive_encoding (fst a) k) es) by
    (intro k; apply Index.find_group_by).
  assert (Hmass : fold_right (fun k n => N.of_nat (length
    (Index.find positive_encoding k (Index.group_by positive_encoding fst es))) + n) 0 ks =
    fold_right (fun k n => N.of_nat (length
      (filter (fun a => eqb positive_encoding (fst a) k) es)) + n) 0 ks).
  { clear Hnodup. induction ks as [|k rest IH]; [reflexivity|].
    cbn [fold_right]. now rewrite Hfind, IH. }
  rewrite Hmass. clear Hfind Hmass.
  induction es as [|ev rest IH].
  - clear Hnodup. induction ks; cbn [fold_right filter length]; [reflexivity|exact IHks].
  - rewrite filter_mass_cons. pose proof (matching_bound (fst ev) ks Hnodup).
    cbn [length]. rewrite Nat2N.inj_succ. lia.
Qed.

(** Row construction is linear in component count and total grouped bucket mass. *)
Theorem rows_cost cs start es w :
  (forall i, In i (indices cs start) -> key_bits positive_encoding i <= w) ->
  (forall ev, In ev es -> key_bits positive_encoding (snd ev) <= w) ->
  Cost.ticks (Condense.rows_c cs start (Index.group_by positive_encoding fst es)) <=
    (N.of_nat (length cs) + N.of_nat (length es)) * (1 + 2 * id_cost w).
Proof.
  intros Hindices Htargets.
  assert (Hrows : forall cs start,
    (forall i, In i (indices cs start) -> key_bits positive_encoding i <= w) ->
    Cost.ticks (Condense.rows_c cs start (Index.group_by positive_encoding fst es)) <=
      N.of_nat (length cs) * (1 + 2 * id_cost w) +
      fold_right (fun k n => N.of_nat (length (Index.find positive_encoding k
        (Index.group_by positive_encoding fst es))) + n) 0 (indices cs start) *
        (1 + 2 * id_cost w)).
  { intros todo. induction todo as [|c rest IH]; intros first Hkeys; [reflexivity|].
    pose proof (Hkeys first (or_introl eq_refl)) as Hfirst.
    pose proof (get_cost w first (Index.group_by positive_encoding fst es) Hfirst).
    pose proof (set_cost w first
      (Condense.unique (Index.find positive_encoding first
        (Index.group_by positive_encoding fst es)) FinSet.empty)
      (Condense.rows rest (Pos.succ first) (Index.group_by positive_encoding fst es)) Hfirst).
    pose proof (unique_cost (Index.find positive_encoding first
      (Index.group_by positive_encoding fst es)) FinSet.empty w) as Hunique.
    assert (Hbucket : forall ev, In ev (Index.find positive_encoding first
      (Index.group_by positive_encoding fst es)) ->
      key_bits positive_encoding (snd ev) <= w).
    { intros ev He. rewrite Index.find_group_by in He. apply filter_In in He.
      now apply Htargets, (proj1 He). }
    specialize (Hunique Hbucket).
    specialize (IH (Pos.succ first) ltac:(intros i Hi; apply Hkeys; now right)).
    cbn [Condense.rows_c]. autorewrite with galois_cost.
    rewrite Index.find_cost.
    fold (Condense.rows rest (Pos.succ first) (Index.group_by positive_encoding fst es)).
    fold (Index.find positive_encoding first (Index.group_by positive_encoding fst es)).
    fold (Condense.unique (Index.find positive_encoding first
      (Index.group_by positive_encoding fst es)) FinSet.empty).
    cbn [length indices fold_right]. rewrite Nat2N.inj_succ. nia. }
  pose proof (Hrows cs start Hindices).
  pose proof (bucket_mass es (indices cs start) (indices_nodup cs start)). nia.
Qed.

(** Every actual component index fits the bit width of the component count plus one. *)
Theorem component_index_width r i :
  (Pos.to_nat i <= length (Scc.components r))%nat ->
    key_bits positive_encoding i <= component_width r.
Proof.
  intro Hindex. change (N.pos (Pos.size i) <= component_width r).
  unfold component_width. apply InternCost.bits_monotone, Pos2Nat.inj_le.
  rewrite SuccNat2Pos.id_succ. lia.
Qed.

Local Lemma component_member_valid {V E} (p : Prepared.t V E) scope roots r u :
  Scc.exact p scope roots r -> In u (concat (Scc.components r)) ->
    Prepared.valid_id p u.
Proof.
  intros Hexact Hu. apply (Scc.partition_complete _ _ _ _ Hexact) in Hu.
  destruct Hu as [root [es [_ Hpath]]]. induction Hpath; assumption.
Qed.

(** Exact scoped condensation has a numeric linear bound in all inspected work and both key widths. *)
Theorem cost {V E} (p : Prepared.t V E) scope roots r w :
  Prepared.ready p -> Scc.exact p scope roots r ->
  SearchCost.width_bound p [] w ->
    Cost.ticks (Condense.of_scc_c p scope r) <= condense_k * size p r w.
Proof.
  intros Hready Hexact Hwidth.
  assert (Hnodekeys : forall u, In u (concat (Scc.components r)) ->
    key_bits positive_encoding u <= w /\
    forall e v, In (e, v) (Prepared.succ_edges p u) ->
      key_bits positive_encoding v <= w).
  { intros u Hu. pose proof (component_member_valid p scope roots r u Hexact Hu) as Hvalid.
    split; [apply Hwidth; now left|].
    intros e v He. apply Hwidth. left.
    exact (proj2 (SearchInvariant.successor_arc p u e v Hready Hvalid He)). }
  assert (Hpairs : forall ev, In ev (Condense.cross_edges p r) ->
    key_bits positive_encoding (fst ev) <= component_width r /\
    key_bits positive_encoding (snd ev) <= component_width r).
  { intros [i j] He. apply (Condense.cross_edges_spec p scope roots r i j Hready Hexact) in He.
    destruct He as [_ [u [e [v [_ [Hi Hj]]]]]]. split; apply component_index_width.
    - exact (proj2 (Condense.owner_member p scope roots r u i Hexact Hi)).
    - exact (proj2 (Condense.owner_member p scope roots r v j Hexact Hj)). }
  pose proof (cross_cost p r w Hnodekeys) as Hcross.
  pose proof (cross_length p r) as Hlength.
  pose proof (IndexCost.group_by_cost Map.cost_laws_hold positive_encoding positive_encoding_laws
    (fun ev : positive * positive => Cost.ret (fst ev)) (Condense.cross_edges p r)
    (component_width r) (component_width r) 0) as Hgroup.
  assert (Hgroupkeys : forall ev, In ev (Condense.cross_edges p r) ->
    Cost.ticks (Cost.ret (fst ev)) <= 0 /\
    Cost.ticks (encode_c positive_encoding (Cost.value (Cost.ret (fst ev)))) <=
      component_width r /\
    key_bits positive_encoding (Cost.value (Cost.ret (fst ev))) <= component_width r).
  { intros ev He. split; [reflexivity|]. cbn [Cost.value].
    split; [|exact (proj1 (Hpairs ev He))].
    change (Cost.ticks (encode_c positive_encoding (fst ev)) <= component_width r).
    eapply N.le_trans; [exact (encode_cost_bound positive_encoding_cost_laws (fst ev))|].
    rewrite N.mul_1_l. exact (proj1 (Hpairs ev He)). }
  specialize (Hgroup Hgroupkeys).
  pose proof (rows_cost (Scc.components r) 1%positive (Condense.cross_edges p r)
    (component_width r)) as Hrows.
  assert (Hindices : forall i, In i (indices (Scc.components r) 1%positive) ->
    key_bits positive_encoding i <= component_width r).
  { intros i Hi. apply component_index_width.
    pose proof (indices_range (Scc.components r) 1%positive i Hi) as Hrange.
    cbn in Hrange. lia. }
  specialize (Hrows Hindices ltac:(intros ev He; exact (proj2 (Hpairs ev He)))).
  unfold Condense.of_scc_c. autorewrite with galois_cost.
  fold (Condense.cross_edges p r).
  rewrite Index.group_by_c_value.
  change (Cost.ticks (Condense.cross_edges_c p r) +
    (Cost.ticks (Index.group_by_c positive_encoding
      (fun ev : positive * positive => Cost.ret (fst ev)) (Condense.cross_edges p r)) +
    (Cost.ticks (Condense.rows_c (Scc.components r) 1%positive
      (Index.group_by positive_encoding fst (Condense.cross_edges p r))) +
    (N.of_nat (length (Scc.components r)) + 0))) <= condense_k * size p r w).
  unfold condense_k, size, id_cost in *. nia.
Qed.

End TarjanCondenseCost.
