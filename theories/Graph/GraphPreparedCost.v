(** * Preparation and reversal cost bounds

    Bounds retain all primitive callback, trie, list and unary conversion work.
    For example, duplicate and unknown entry occurrences still incur lookup charges.
    Builds on: GraphPrepared, BaseInternCost and BaseIndexCost. *)

From Stdlib Require Import List PArith NArith Arith Lia.
From Galois.Cost Require Import CostMonad CostList CostBound.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseIntern BaseInternCost BaseIndex
  BaseIndexCost.
From Galois.Graph Require Import GraphModel GraphPrepared.
Import List.ListNotations Cost.Notations.

Module PreparedCost.
Local Open Scope N_scope.

(** Cost erasure returns the existing public preparation on its full arbitrary-input domain. *)
Theorem prepare_c_value {V E} enc (g : Graph.t V E) :
  Cost.value (Prepared.prepare_c enc g) = Prepared.prepare enc g.
Proof.
  reflexivity.
Qed.

(** Present mapping retains the traversal tick, callback overhead and complete callee charge. *)
Theorem present_cost {A B} (f : A -> Cost.t (option B)) xs :
  Cost.ticks (Prepared.present_c f xs) =
    fold_right (fun x n => 2 + Cost.ticks (f x) + n) 0 xs.
Proof.
  induction xs as [|x rest IH]; [reflexivity|].
  cbn [Prepared.present_c fold_right]. autorewrite with galois_cost.
  rewrite IH. lia.
Qed.

(** Erasing reverse costs preserves the existing full-domain reversed prepared view. *)
Theorem reverse_c_value {V E} (p : Prepared.t V E) exits :
  Cost.value (Prepared.reverse_c p exits) = Prepared.reverse p exits.
Proof.
  reflexivity.
Qed.

(** Reversal pays every exit occurrence and its actual inverse lookup, including unknown IDs. *)
Theorem reverse_cost {V E} (p : Prepared.t V E) exits :
  Cost.ticks (Prepared.reverse_c p exits) =
    fold_right (fun i n => 2 + Cost.ticks (Prepared.name_of_c p i) + n) 0 exits.
Proof.
  rewrite Prepared.reverse_c_equation. autorewrite with galois_cost.
  rewrite present_cost. lia.
Qed.

(** A supplied width bound gives a linear bound without restricting duplicates or unknown exits. *)
Theorem reverse_cost_bound {V E} (p : Prepared.t V E) exits w :
  (forall i, In i exits -> key_bits positive_encoding i <= w) ->
    Cost.ticks (Prepared.reverse_c p exits) <= N.of_nat (length exits) * (3 + 2 * w).
Proof.
  intro Hwidth. rewrite reverse_cost.
  induction exits as [|i rest IH]; [cbn; lia|].
  cbn [fold_right length]. rewrite Nat2N.inj_succ.
  assert (Htail : forall j, In j rest -> key_bits positive_encoding j <= w).
  { intros j Hj. apply Hwidth. now right. }
  specialize (IH Htail).
  pose proof (Hwidth i (or_introl eq_refl)) as Hi.
  pose proof (encode_cost_bound positive_encoding_cost_laws i) as Hencode.
  unfold Prepared.name_of_c at 1. rewrite Intern.key_of_cost, Map.get_cost.
  fold (key_bits positive_encoding i). nia.
Qed.

Local Lemma present_cost_bound {A B} (f : A -> Cost.t (option B)) xs k :
  (forall x, In x xs -> Cost.ticks (f x) <= k) ->
    Cost.ticks (Prepared.present_c f xs) <= N.of_nat (length xs) * (2 + k).
Proof.
  intro Hf. rewrite present_cost. induction xs as [|x rest IH]; [cbn; lia|].
  cbn [fold_right length]. rewrite Nat2N.inj_succ.
  pose proof (Hf x (or_introl eq_refl)).
  assert (Htail : forall y, In y rest -> Cost.ticks (f y) <= k).
  { intros y Hy. apply Hf. now right. }
  specialize (IH Htail). nia.
Qed.

(** Tagging charges every endpoint callback and lookup at its actual returned client key. *)
Theorem tagged_cost {V E} enc table (endpoint : E -> Cost.t V) es e b c :
  (forall edge, In edge es ->
    Cost.ticks (endpoint edge) <= c /\
    Cost.ticks (encode_c enc (Cost.value (endpoint edge))) <= e /\
    key_bits enc (Cost.value (endpoint edge)) <= b) ->
    Cost.ticks (Prepared.tagged_c enc table endpoint es) <=
      N.of_nat (length es) * (4 + c + e + b).
Proof.
  intro Hkeys. unfold Prepared.tagged_c.
  eapply N.le_trans; [apply present_cost_bound with (k := 2 + c + e + b)|]; [|nia].
  intros edge Hin. destruct (Hkeys edge Hin) as [Hcallee [Hencode Hbits]].
  autorewrite with galois_cost.
  rewrite Intern.find_cost, Map.get_cost.
  fold (key_bits enc (Cost.value (endpoint edge))). nia.
Qed.

(** Entry conversion retains repeated and unknown entry lookup costs. *)
Theorem ids_cost {V} enc (table : Intern.t V) vs e b :
  (forall v, In v vs -> Cost.ticks (encode_c enc v) <= e /\ key_bits enc v <= b) ->
    Cost.ticks (Prepared.ids_c enc table vs) <= N.of_nat (length vs) * (3 + e + b).
Proof.
  intro Hkeys. unfold Prepared.ids_c.
  eapply N.le_trans; [apply present_cost_bound with (k := 1 + e + b)|]; [|nia].
  intros v Hin. destruct (Hkeys v Hin) as [Hencode Hbits].
  rewrite Intern.find_cost, Map.get_cost. fold (key_bits enc v). lia.
Qed.

Local Lemma positive_set_cost {A} i (a : A) m :
  Cost.ticks (Map.set_c positive_encoding i a m) = 2 + key_bits positive_encoding i.
Proof.
  rewrite Map.set_cost.
  assert (Hcharge : Cost.ticks (encode_c positive_encoding i) = 1) by apply of_pure_cost.
  fold (key_bits positive_encoding i). lia.
Qed.

(** Node indexing retains every reached callback and bounds dense-ID insertion by supplied width. *)
Theorem index_nodes_cost {V A} enc (table : Intern.t V) (f : V -> Cost.t A) vs e b d
    (q : V -> N) :
  (forall v, In v vs -> Cost.ticks (encode_c enc v) <= e /\ key_bits enc v <= b) ->
  (forall v i, In v vs -> Intern.find enc v table = Some i ->
    key_bits positive_encoding i <= d) ->
  (forall v, In v vs -> Cost.ticks (f v) <= q v) ->
    Cost.ticks (Prepared.index_nodes_c enc table f vs) <=
      fold_right (fun v n => 5 + e + b + d + q v + n) 0 vs.
Proof.
  intros Hkeys Hids Hf. induction vs as [|v rest IH]; [reflexivity|].
  assert (Htailkeys : forall x, In x rest ->
    Cost.ticks (encode_c enc x) <= e /\ key_bits enc x <= b).
  { intros x Hx. apply Hkeys. now right. }
  assert (Htailids : forall x i, In x rest -> Intern.find enc x table = Some i ->
    key_bits positive_encoding i <= d).
  { intros x i Hx Hi. apply (Hids x i); [now right|exact Hi]. }
  assert (Htailf : forall x, In x rest -> Cost.ticks (f x) <= q x).
  { intros x Hx. apply Hf. now right. }
  specialize (IH Htailkeys Htailids Htailf).
  destruct (Hkeys v (or_introl eq_refl)) as [Hencode Hbits].
  pose proof (Hf v (or_introl eq_refl)) as Hcallback.
  cbn [Prepared.index_nodes_c fold_right]. autorewrite with galois_cost.
  fold (Intern.find enc v table).
  destruct (Intern.find enc v table) as [i|] eqn:Hfind; autorewrite with galois_cost.
  - rewrite positive_set_cost, Intern.find_cost, Map.get_cost.
    fold (key_bits enc v). pose proof (Hids v i (or_introl eq_refl) Hfind). nia.
  - rewrite Intern.find_cost, Map.get_cost. fold (key_bits enc v). nia.
Qed.

Definition mass {A B} (f : A -> list B) xs :=
  fold_right (fun x n => N.of_nat (length (f x)) + n) 0 xs.

Local Lemma sum_weighted_le {A} (q f : A -> N) xs base k :
  (forall x, In x xs -> q x <= base + k * f x) ->
  fold_right (fun x n => q x + n) 0 xs <=
    N.of_nat (length xs) * base + k * fold_right (fun x n => f x + n) 0 xs.
Proof.
  intro Hq. induction xs as [|x rest IH]; [cbn; nia|].
  cbn [fold_right length]. rewrite Nat2N.inj_succ.
  pose proof (Hq x (or_introl eq_refl)).
  assert (Htail : forall y, In y rest -> q y <= base + k * f y).
  { intros y Hy. apply Hq. now right. }
  specialize (IH Htail). nia.
Qed.

Local Lemma outgoing_mass {V E} (g : Graph.t V E) :
  mass (Graph.out g) (Graph.nodes g) = N.of_nat (edge_count g) /\
    length (Prepared.all_edges g) = edge_count g.
Proof.
  unfold mass, edge_count, Prepared.all_edges.
  induction (Graph.nodes g) as [|v rest [IHmass IHedges]]; cbn [fold_right flat_map];
    [auto|].
  rewrite Nat2N.inj_add, length_app, IHmass, IHedges. auto.
Qed.

(** Flattening pays outgoing callees and every copied edge occurrence. *)
Theorem all_edges_cost {V E} (g : Graph.t V E) ko :
  (forall v, In v (Graph.nodes g) -> Cost.ticks (Graph.out_c g v) <= ko) ->
    Cost.ticks (Prepared.all_edges_c g) <=
      N.of_nat (length (Graph.nodes g)) * (2 + ko) + N.of_nat (edge_count g).
Proof.
  intro Hout. unfold Prepared.all_edges_c.
  assert (Hcost : forall vs,
    Cost.ticks (fold_right_c (fun v tail =>
      Cost.step ;; let* es := Graph.out_c g v in app_c es tail) [] vs) =
      fold_right (fun v n => (2 + Cost.ticks (Graph.out_c g v) +
        N.of_nat (length (Graph.out g v))) + n) 0 vs).
  { intro vs.
    rewrite (ticks_fold_right_c_sum _
      (fun v => 1 + Cost.ticks (Graph.out_c g v) + N.of_nat (length (Graph.out g v)))).
    - induction vs as [|v rest IH]; [reflexivity|].
      cbn [fold_right]. rewrite IH. lia.
    - intros v tail. autorewrite with galois_cost. fold (Graph.out g v). lia. }
  rewrite Hcost.
  rewrite <- (proj1 (outgoing_mass g)).
  eapply N.le_trans; [apply (sum_weighted_le
    (fun v => 2 + Cost.ticks (Graph.out_c g v) + N.of_nat (length (Graph.out g v)))
    (fun v => N.of_nat (length (Graph.out g v))) (Graph.nodes g) (2 + ko) 1)|].
  - intros v Hv. pose proof (Hout v Hv). nia.
  - unfold mass. nia.
Qed.

(** Fuel edge counting retains its repeated outgoing accesses and length traversals. *)
Theorem edge_count_cost {V E} (g : Graph.t V E) ko :
  (forall v, In v (Graph.nodes g) -> Cost.ticks (Graph.out_c g v) <= ko) ->
    Cost.ticks (Prepared.edge_count_c g) <=
      N.of_nat (length (Graph.nodes g)) * (2 + ko) + N.of_nat (edge_count g).
Proof.
  intro Hout. unfold Prepared.edge_count_c.
  assert (Hcost : forall vs,
    Cost.ticks (fold_right_c (fun v n =>
      Cost.step ;; let* es := Graph.out_c g v in
      let* m := length_c es in Cost.ret (m + n)%nat) 0%nat vs) =
      fold_right (fun v n => (2 + Cost.ticks (Graph.out_c g v) +
        N.of_nat (length (Graph.out g v))) + n) 0 vs).
  { intro vs.
    rewrite (ticks_fold_right_c_sum _
      (fun v => 1 + Cost.ticks (Graph.out_c g v) + N.of_nat (length (Graph.out g v)))).
    - induction vs as [|v rest IH]; [reflexivity|].
      cbn [fold_right]. rewrite IH. lia.
    - intros v count. autorewrite with galois_cost. fold (Graph.out g v). lia. }
  rewrite Hcost. rewrite <- (proj1 (outgoing_mass g)).
  eapply N.le_trans; [apply (sum_weighted_le
    (fun v => 2 + Cost.ticks (Graph.out_c g v) + N.of_nat (length (Graph.out g v)))
    (fun v => N.of_nat (length (Graph.out g v))) (Graph.nodes g) (2 + ko) 1)|].
  - intros v Hv. pose proof (Hout v Hv). nia.
  - unfold mass. nia.
Qed.

Local Lemma matching_absent {K} enc (HE : encoding_laws enc) (x : K) ks :
  ~ In x ks -> fold_right (fun k n => if eqb enc x k then 1 + n else n) 0 ks = 0.
Proof.
  induction ks as [|k rest IH]; intro Habsent; [reflexivity|].
  cbn [fold_right]. destruct (eqb_spec enc HE x k) as [->|Hne].
  - exfalso. apply Habsent. now left.
  - apply IH. intro Hin. apply Habsent. now right.
Qed.

Local Lemma matching_once {K} enc (HE : encoding_laws enc) (x : K) ks :
  NoDup ks -> fold_right (fun k n => if eqb enc x k then 1 + n else n) 0 ks <= 1.
Proof.
  intro Hnodup. induction Hnodup as [|k rest Hnot Hnodup IH]; [cbn; lia|].
  cbn [fold_right]. destruct (eqb_spec enc HE x k) as [->|Hne].
  - rewrite (matching_absent enc HE k rest Hnot). lia.
  - exact IH.
Qed.

Local Lemma filter_mass_cons {K A} enc (key : A -> K) x xs ks :
  mass (fun k => filter (fun a => eqb enc (key a) k) (x :: xs)) ks =
    mass (fun k => filter (fun a => eqb enc (key a) k) xs) ks +
    fold_right (fun k n => if eqb enc (key x) k then 1 + n else n) 0 ks.
Proof.
  unfold mass. induction ks as [|k rest IH]; [reflexivity|].
  cbn [fold_right]. rewrite IH. cbn [filter].
  destruct (eqb enc (key x) k); cbn [length]; rewrite ?Nat2N.inj_succ; lia.
Qed.

Local Lemma filter_mass_bound {K A} enc (HE : encoding_laws enc) (key : A -> K) xs ks :
  NoDup ks ->
    mass (fun k => filter (fun a => eqb enc (key a) k) xs) ks <= N.of_nat (length xs).
Proof.
  intro Hnodup. induction xs as [|x rest IH].
  - unfold mass. clear Hnodup.
    induction ks as [|k ks IHks]; cbn [fold_right filter length].
    + reflexivity.
    + exact IHks.
  - rewrite filter_mass_cons. cbn [length]. rewrite Nat2N.inj_succ.
    pose proof (matching_once enc HE (key x) ks Hnodup). lia.
Qed.

(** Distinct node keys pull at most one copy of each incoming edge occurrence in total. *)
Theorem incoming_mass {V E} enc (HE : encoding_laws enc) (g : Graph.t V E) :
  NoDup (Graph.nodes g) ->
    mass (fun v => Index.find enc v
      (Index.group_by enc (Graph.target g) (Prepared.all_edges g))) (Graph.nodes g) <=
      N.of_nat (edge_count g).
Proof.
  intro Hnodes.
  assert (Hmass : forall vs,
    mass (fun v => Index.find enc v
      (Index.group_by enc (Graph.target g) (Prepared.all_edges g))) vs =
    mass (fun v => filter (fun edge => eqb enc (Graph.target g edge) v)
      (Prepared.all_edges g)) vs).
  { unfold mass. induction vs as [|v rest IH]; [reflexivity|].
    cbn [fold_right]. now rewrite Index.find_group_by, IH. }
  rewrite Hmass, <- (proj2 (outgoing_mass g)).
  now apply filter_mass_bound.
Qed.

(** Primitive budgets concern actual finite client keys, edge occurrences and graph callbacks. *)
Record prepare_bounds {V E} enc (g : Graph.t V E) ek b ko ks kt : Prop := {
  node_keys : forall v, In v (Graph.nodes g) ->
    Cost.ticks (encode_c enc v) <= ek /\ key_bits enc v <= b;
  entry_keys : forall v, In v (Graph.entries g) ->
    Cost.ticks (encode_c enc v) <= ek /\ key_bits enc v <= b;
  out_calls : forall v, In v (Graph.nodes g) -> Cost.ticks (Graph.out_c g v) <= ko;
  edge_calls : forall edge, In edge (Prepared.all_edges g) ->
    Cost.ticks (Graph.source_c g edge) <= ks /\
    Cost.ticks (Graph.target_c g edge) <= kt /\
    Cost.ticks (encode_c enc (Graph.source g edge)) <= ek /\
    key_bits enc (Graph.source g edge) <= b /\
    Cost.ticks (encode_c enc (Graph.target g edge)) <= ek /\
    key_bits enc (Graph.target g edge) <= b
}.

Definition id_width {V E} (g : Graph.t V E) :=
  N.pos (Pos.size (Pos.of_succ_nat (length (Graph.nodes g)))).

(** Interning cannot allocate more bindings than its actual node input occurrences. *)
Theorem table_size {V E} enc (HE : encoding_laws enc) (g : Graph.t V E) :
  (Intern.size (Intern.of_list enc (Graph.nodes g)) <= length (Graph.nodes g))%nat.
Proof.
  rewrite Intern.size_equation.
  pose proof (Intern.wf_of_list enc HE (Graph.nodes g)) as Hwf.
  apply (Map.size_support_bound enc HE (Graph.nodes g)).
  - exact (proj1 (Intern.wf_maps enc _ Hwf)).
  - intros v i Hget. apply (proj2 (Intern.intern_list_spec enc HE (Graph.nodes g) v)).
    exists i. now rewrite Intern.find_equation.
Qed.

(** Every allocated ID used by preparation fits within the input length-plus-one width. *)
Theorem table_id_width {V E} enc (HE : encoding_laws enc) (g : Graph.t V E) v i :
  Intern.find enc v (Intern.of_list enc (Graph.nodes g)) = Some i ->
    key_bits positive_encoding i <= id_width g.
Proof.
  intro Hfind.
  pose proof (InternCost.dense_id_bits enc HE v i _
    (Intern.wf_of_list enc HE (Graph.nodes g)) Hfind) as Hbits.
  eapply N.le_trans; [exact Hbits|]. unfold id_width.
  apply InternCost.bits_monotone, Pos2Nat.inj_le.
  rewrite !SuccNat2Pos.id_succ. pose proof (table_size enc HE g). lia.
Qed.

Local Lemma index_nodes_weighted {V A B} enc table (f : V -> Cost.t A)
    (items : V -> list B) vs ek b d q k :
  (forall v, In v vs -> Cost.ticks (encode_c enc v) <= ek /\ key_bits enc v <= b) ->
  (forall v i, In v vs -> Intern.find enc v table = Some i ->
    key_bits positive_encoding i <= d) ->
  (forall v, In v vs -> Cost.ticks (f v) <= q + k * N.of_nat (length (items v))) ->
    Cost.ticks (Prepared.index_nodes_c enc table f vs) <=
      N.of_nat (length vs) * (5 + ek + b + d + q) + k * mass items vs.
Proof.
  intros Hkeys Hids Hf.
  pose proof (index_nodes_cost enc table f vs ek b d
    (fun v => q + k * N.of_nat (length (items v))) Hkeys Hids Hf) as Hindex.
  eapply N.le_trans; [exact Hindex|].
  apply (sum_weighted_le
    (fun v => 5 + ek + b + d + (q + k * N.of_nat (length (items v))))
    (fun v => N.of_nat (length (items v))) vs (5 + ek + b + d + q) k).
  intros v Hv. nia.
Qed.

(** Outgoing indexing pays one tagging pass over each actual outgoing occurrence. *)
Theorem outgoing_index_cost {V E} enc (HE : encoding_laws enc) (g : Graph.t V E)
    ek b ko ks kt :
  prepare_bounds enc g ek b ko ks kt ->
  Cost.ticks (Prepared.index_nodes_c enc (Intern.of_list enc (Graph.nodes g))
    (fun v => Cost.step ;; let* es := Graph.out_c g v in
      Prepared.tagged_c enc (Intern.of_list enc (Graph.nodes g)) (Graph.target_c g) es)
    (Graph.nodes g)) <=
    N.of_nat (length (Graph.nodes g)) * (6 + ek + b + id_width g + ko) +
      N.of_nat (edge_count g) * (4 + kt + ek + b).
Proof.
  intro Hbounds.
  eapply N.le_trans; [apply (index_nodes_weighted enc _ _ (Graph.out g)
    (Graph.nodes g) ek b (id_width g) (1 + ko) (4 + kt + ek + b))|].
  - exact (node_keys _ _ _ _ _ _ _ Hbounds).
  - intros v i Hv Hi. exact (table_id_width enc HE g v i Hi).
  - intros v Hv. autorewrite with galois_cost. fold (Graph.out g v).
    pose proof (out_calls _ _ _ _ _ _ _ Hbounds v Hv) as Hout.
    assert (Htag : Cost.ticks (Prepared.tagged_c enc (Intern.of_list enc (Graph.nodes g))
      (Graph.target_c g) (Graph.out g v)) <=
        N.of_nat (length (Graph.out g v)) * (4 + kt + ek + b)).
    { apply tagged_cost. intros edge Hedge.
      assert (Hin : In edge (Prepared.all_edges g)).
      { unfold Prepared.all_edges. apply in_flat_map. now exists v. }
      destruct (edge_calls _ _ _ _ _ _ _ Hbounds edge Hin)
        as [_ [Htarget [_ [_ [Hencode Hbits]]]]]. auto. }
    nia.
  - rewrite (proj1 (outgoing_mass g)). nia.
Qed.

(** Incoming indexing pulls each distinct target bucket once and charges its source callbacks. *)
Theorem incoming_index_cost {V E} enc (HE : encoding_laws enc) (g : Graph.t V E)
    ek b ko ks kt :
  NoDup (Graph.nodes g) -> prepare_bounds enc g ek b ko ks kt ->
  let idx := Index.group_by enc (Graph.target g) (Prepared.all_edges g) in
  Cost.ticks (Prepared.index_nodes_c enc (Intern.of_list enc (Graph.nodes g))
    (fun v => let* es := Index.find_c enc v idx in
      Prepared.tagged_c enc (Intern.of_list enc (Graph.nodes g)) (Graph.source_c g) es)
    (Graph.nodes g)) <=
    N.of_nat (length (Graph.nodes g)) * (6 + 2 * ek + 2 * b + id_width g) +
      N.of_nat (edge_count g) * (4 + ks + ek + b).
Proof.
  intros Hnodes Hbounds idx.
  eapply N.le_trans; [apply (index_nodes_weighted enc _ _ (fun v => Index.find enc v idx)
    (Graph.nodes g) ek b (id_width g) (1 + ek + b) (4 + ks + ek + b))|].
  - exact (node_keys _ _ _ _ _ _ _ Hbounds).
  - intros v i Hv Hi. exact (table_id_width enc HE g v i Hi).
  - intros v Hv. rewrite Cost.ticks_bind. fold (Index.find enc v idx).
    destruct (node_keys _ _ _ _ _ _ _ Hbounds v Hv) as [Hencode Hbits].
    pose proof (IndexCost.find_cost Map.cost_laws_hold enc v idx) as Hfind.
    assert (Htag : Cost.ticks (Prepared.tagged_c enc (Intern.of_list enc (Graph.nodes g))
      (Graph.source_c g) (Index.find enc v idx)) <=
        N.of_nat (length (Index.find enc v idx)) * (4 + ks + ek + b)).
    { apply tagged_cost. intros edge Hedge. unfold idx in Hedge.
      rewrite Index.find_group_by in Hedge. apply filter_In in Hedge.
      destruct (edge_calls _ _ _ _ _ _ _ Hbounds edge (proj1 Hedge))
        as [Hsource [_ [Hsourcekey [Hsourcebits _]]]]. auto. }
    nia.
  - pose proof (incoming_mass enc HE g Hnodes) as Hmass. fold idx in Hmass. nia.
Qed.

(** Preparation retains all callback, list, indexing and unary fuel-conversion work. *)
Theorem prepare_credit_cost {V E} enc (HE : encoding_laws enc) (g : Graph.t V E)
    ek b ko ks kt :
  NoDup (Graph.nodes g) -> prepare_bounds enc g ek b ko ks kt ->
  Cost.ticks (Prepared.prepare_c enc g) <=
    2 +
    N.of_nat (length (Graph.nodes g)) *
      (20 + InternCost.intern_k + 5 * ek + 5 * b + 3 * id_width g + 3 * ko) +
    N.of_nat (edge_count g) * (17 + 4 * ek + 6 * b + ks + 2 * kt) +
    N.of_nat (length (Graph.entries g)) * (3 + ek + b).
Proof.
  intros Hnodes Hbounds.
  pose proof (InternCost.of_list_cost Map.cost_laws_hold enc (Graph.nodes g) ek b
    (node_keys _ _ _ _ _ _ _ Hbounds)) as Hintern.
  pose proof (all_edges_cost g ko (out_calls _ _ _ _ _ _ _ Hbounds)) as Hall.
  pose proof (edge_count_cost g ko (out_calls _ _ _ _ _ _ _ Hbounds)) as Hcount.
  pose proof (outgoing_index_cost enc HE g ek b ko ks kt Hbounds) as Hout.
  pose proof (incoming_index_cost enc HE g ek b ko ks kt Hnodes Hbounds) as Hin.
  pose proof (ids_cost enc (Intern.of_list enc (Graph.nodes g)) (Graph.entries g) ek b
    (entry_keys _ _ _ _ _ _ _ Hbounds)) as Hentries.
  assert (Hkeys : forall edge, In edge (Prepared.all_edges g) ->
    Cost.ticks (Graph.target_c g edge) <= kt /\
    Cost.ticks (encode_c enc (Cost.value (Graph.target_c g edge))) <= ek /\
    key_bits enc (Cost.value (Graph.target_c g edge)) <= b).
  { intros edge Hedge.
    destruct (edge_calls _ _ _ _ _ _ _ Hbounds edge Hedge)
      as [_ [Htarget [_ [_ [Hencode Hbits]]]]]. auto. }
  pose proof (IndexCost.group_by_cost Map.cost_laws_hold enc HE (Graph.target_c g)
    (Prepared.all_edges g) ek b kt Hkeys) as Hgroup.
  rewrite (proj2 (outgoing_mass g)) in Hgroup.
  unfold Prepared.prepare_c. autorewrite with galois_cost.
  fold (Intern.of_list enc (Graph.nodes g)).
  rewrite Prepared.all_edges_c_value, Index.group_by_c_value, Prepared.edge_count_c_value.
  rewrite Prepared.budget_cost.
  fold (Graph.target g).
  fold (id_width g) in Hintern.
  cbn beta iota zeta in Hin.
  rewrite !Nat2N.inj_add, !Nat2N.inj_mul.
  nia.
Qed.

Definition prepare_k : N := 32 + InternCost.intern_k.

(** Size counts every raw node, edge and entry occurrence, callback budget and dense-ID width. *)
Definition prepare_size {V E} (g : Graph.t V E) ek b ko ks kt :=
  1 + (N.of_nat (length (Graph.nodes g)) + N.of_nat (edge_count g) +
    N.of_nat (length (Graph.entries g))) * (1 + ek + b + id_width g + ko + ks + kt).

(** Lawful keys and distinct source nodes give linear preparation, including repeated entries. *)
Theorem prepare_cost {V E} enc (HE : encoding_laws enc) (g : Graph.t V E)
    ek b ko ks kt :
  NoDup (Graph.nodes g) -> prepare_bounds enc g ek b ko ks kt ->
    Cost.ticks (Prepared.prepare_c enc g) <= prepare_k * prepare_size g ek b ko ks kt.
Proof.
  intros Hnodes Hbounds.
  pose proof (prepare_credit_cost enc HE g ek b ko ks kt Hnodes Hbounds).
  unfold prepare_k, prepare_size. nia.
Qed.

(** The concrete preparation bound gives a size-based asymptotic corollary for input families. *)
Theorem prepare_bigO {X V E} enc (HE : encoding_laws enc) (g : X -> Graph.t V E)
    ek b ko ks kt :
  (forall x, NoDup (Graph.nodes (g x))) ->
  (forall x, prepare_bounds enc (g x) (ek x) (b x) (ko x) (ks x) (kt x)) ->
    bigO (fun x => prepare_size (g x) (ek x) (b x) (ko x) (ks x) (kt x))
      (fun x => Cost.ticks (Prepared.prepare_c enc (g x))).
Proof.
  intros Hnodes Hbounds. exists prepare_k. intro x.
  pose proof (prepare_cost enc HE (g x) (ek x) (b x) (ko x) (ks x) (kt x)
    (Hnodes x) (Hbounds x)).
  unfold prepare_k in *. nia.
Qed.

End PreparedCost.
