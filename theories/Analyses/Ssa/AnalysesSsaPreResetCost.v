(** * Primitive costs of shared PRE reset queries

    Bounds price source dictionaries, canonical inventories and the existing scoped search driver.
    For example, operand gates retain their incoming-edge encoding and real-use lookup costs.
    Builds on: AnalysesSsaPreReset, BaseCode, BaseIndexCost and GraphPreparedCost. *)

From Stdlib Require Import List Bool NArith PArith Arith Lia Permutation.
From Galois.Cost Require Import CostMonad CostList CostBound.
From Galois.Base Require Import BaseEncoding BaseCode BaseEq BaseMap BaseSet BaseIndex
  BaseMapCost BaseTrieCost BaseIndexCost BaseIntern BaseInternCost.
From Galois.Graph Require Import GraphModel GraphPrepared GraphPreparedCost GraphVisitor
  GraphSearch GraphSearchSpec GraphSearchCost.
From Galois.Analyses.Ssa Require Import AnalysesSsaPreContext AnalysesSsaPreFrg
  AnalysesSsaPreReset.
Import List.ListNotations Cost.Notations.
Local Open Scope N_scope.

Module PreResetCost.

(** A primitive dictionary budget covers its callback and every emitted key bit. *)
Definition key_bound {X} (enc : encoding X) x w : Prop :=
  Cost.ticks (encode_c enc x) + key_bits enc x <= w.
Definition pair_price a b := 3 + a + b + (1 + encode_k) * (7 + 2 * a + 2 * b).
Definition sum_price a b := 2 + a + b + (1 + encode_k) * (8 + 2 * a + 2 * b).
Definition phi_price w := pair_price w w.
Definition link_price w := pair_price (phi_price w) w.
Definition vertex_price w := sum_price (phi_price w) (link_price w).
Definition arc_price w := pair_price (vertex_price w) (vertex_price w).

Local Lemma sequence_bounds a b c d e f g h i j k aa bc ee ff ij kk :
  a <= aa -> b + c <= bc -> e <= ee -> f <= ff -> i + j <= ij -> k <= kk ->
  a + b + c + d + e + f + g + h + i + j + k <=
    aa + bc + d + ee + ff + g + h + ij + kk.
Proof.
  intros. lia.
Qed.

Lemma sum_bound {X} (q : X -> N) xs k :
  (forall x, In x xs -> q x <= k) ->
  fold_right (fun x n => q x + n) 0 xs <= N.of_nat (length xs) * k.
Proof.
  intro Hq. induction xs as [|x rest IH]; [cbn; lia|].
  cbn [fold_right length]. rewrite Nat2N.inj_succ.
  specialize (IH (fun y Hy => Hq y (or_intror Hy))).
  specialize (Hq x (or_introl eq_refl)). nia.
Qed.

Lemma get_key_cost {X Y} (enc : encoding X) x (m : Map.t X Y) w :
  key_bound enc x w -> Cost.ticks (Map.get_c enc x m) <= 1 + w.
Proof.
  intro Hkey. rewrite Map.get_cost. fold (key_bits enc x).
  unfold key_bound in Hkey. lia.
Qed.

Lemma pair_work {X Y} (ex : encoding X) (ey : encoding Y) x y a b :
  key_bound ex x a -> key_bound ey y b ->
  key_bound (pair_encoding ex ey) (x, y) (pair_price a b).
Proof.
  intros Hx Hy. pose proof (pair_encoding_cost ex ey x y) as Hcost.
  unfold key_bound, pair_price in *. rewrite pair_encoding_bits in *.
  nia.
Qed.

Lemma sum_work {X Y} (ex : encoding X) (ey : encoding Y) xy a b :
  (match xy with inl x => key_bound ex x a | inr y => key_bound ey y b end) ->
  key_bound (sum_encoding ex ey) xy (sum_price a b).
Proof.
  intro Hkey. pose proof (sum_encoding_cost ex ey xy) as Hcost.
  unfold key_bound, sum_price in *. rewrite sum_encoding_bits in *.
  destruct xy; cbn beta iota in *; nia.
Qed.

Lemma set_members {X} (enc : encoding X) (HE : encoding_laws enc) xs x :
  In x (FinSet.elements (FinSet.of_list enc xs)) <-> In x xs.
Proof.
  rewrite (FinSet.elements_spec enc HE x _ (FinSet.wf_of_list enc xs)).
  rewrite FinSet.mem_of_list, existsb_exists. split.
  - intros [y [Hin Heq]]. apply (eqb_true_iff enc HE) in Heq. now subst y.
  - intro Hin. exists x. split; [exact Hin|apply eqb_refl].
Qed.

Lemma canonical_length {X} (enc : encoding X) (HE : encoding_laws enc) xs :
  (length (FinSet.elements (FinSet.of_list enc xs)) <= length xs)%nat.
Proof.
  apply NoDup_incl_length.
  - apply (FinSet.elements_nodup enc), FinSet.wf_of_list.
  - intros x Hin. now apply (set_members enc HE xs x) in Hin.
Qed.

Lemma map_enumeration {X Y} (enc : encoding X) (m : Map.t X Y) w :
  Map.wf enc m ->
  (forall x y, Map.get enc x m = Some y -> key_bits enc x <= w) ->
  Cost.ticks (Map.elements_c m) <=
    TrieCost.trie_k * (1 + N.of_nat (length (Map.elements m)) * w).
Proof.
  intros Hwf Hkeys.
  pose proof (MapCost.elements_numeric_cost enc m w Hwf Hkeys).
  now rewrite Map.size_elements in H.
Qed.

Lemma set_enumeration {X} (enc : encoding X) (s : FinSet.t X) w :
  FinSet.wf enc s ->
  (forall x, FinSet.mem enc x s = true -> key_bits enc x <= w) ->
  Cost.ticks (FinSet.elements_c s) <=
    TrieCost.trie_k * (1 + N.of_nat (length (FinSet.elements s)) * w) +
      N.of_nat (length (FinSet.elements s)).
Proof.
  intros Hwf Hkeys.
  pose proof (MapCost.elements_numeric_cost enc s w Hwf) as Hmap.
  assert (Hstored : forall x y, Map.get enc x s = Some y -> key_bits enc x <= w).
  { intros x [] Hget. apply Hkeys, FinSet.mem_spec. exact Hget. }
  specialize (Hmap Hstored). rewrite FinSet.elements_cost_equation.
  rewrite <- FinSet.size_backend, FinSet.size_elements in Hmap.
  rewrite FinSet.size_elements. lia.
Qed.

Definition set_bound n w := n * (3 + 2 * w) + TrieCost.trie_k * (1 + n * w) + n.

Lemma set_bound_monotone a b w :
  a <= b -> set_bound a w <= set_bound b w.
Proof.
  intro Hab.
  assert (Hbuild : a * (3 + 2 * w) <= b * (3 + 2 * w)) by nia.
  assert (Hmass : a * w <= b * w) by nia.
  assert (Htrie : TrieCost.trie_k * (1 + a * w) <=
    TrieCost.trie_k * (1 + b * w)) by nia.
  unfold set_bound. lia.
Qed.

Lemma canonical_enumeration {X} (enc : encoding X) (HE : encoding_laws enc) xs w :
  (forall x, In x xs -> key_bound enc x w) ->
  Cost.ticks (FinSet.elements_c (FinSet.of_list enc xs)) <=
    TrieCost.trie_k * (1 + N.of_nat (length xs) * w) + N.of_nat (length xs).
Proof.
  intro Hkeys.
  pose proof (canonical_length enc HE xs) as Hlength.
  assert (Hcost : Cost.ticks (FinSet.elements_c (FinSet.of_list enc xs)) <=
    TrieCost.trie_k *
      (1 + N.of_nat (length (FinSet.elements (FinSet.of_list enc xs))) * w) +
    N.of_nat (length (FinSet.elements (FinSet.of_list enc xs)))).
  { apply (set_enumeration enc _ w); [apply FinSet.wf_of_list|].
    intros x Hmem.
    apply (proj2 (FinSet.elements_spec enc HE x _ (FinSet.wf_of_list enc xs))) in Hmem.
    apply (set_members enc HE xs x) in Hmem.
    specialize (Hkeys x Hmem). unfold key_bound in Hkeys. lia. }
  assert (Hmass : N.of_nat (length (FinSet.elements (FinSet.of_list enc xs))) * w <=
    N.of_nat (length xs) * w) by nia.
  assert (Htrie : TrieCost.trie_k *
      (1 + N.of_nat (length (FinSet.elements (FinSet.of_list enc xs))) * w) <=
    TrieCost.trie_k * (1 + N.of_nat (length xs) * w)) by nia.
  lia.
Qed.

Lemma canonical_cost {X} (enc : encoding X) (HE : encoding_laws enc) xs w :
  (forall x, In x xs -> key_bound enc x w) ->
  Cost.ticks (FinSet.of_list_c enc xs) +
    Cost.ticks (FinSet.elements_c (FinSet.of_list enc xs)) <=
      set_bound (N.of_nat (length xs)) w.
Proof.
  intro Hkeys.
  pose proof (canonical_enumeration enc HE xs w Hkeys) as Henumeration.
  pose proof (FinSet.of_list_numeric_cost Map.cost_laws_hold enc xs w w) as Hconstruction.
  assert (Hduties : forall x, In x xs ->
    Cost.ticks (encode_c enc x) <= w /\ key_bits enc x <= w).
  { intros x Hin. specialize (Hkeys x Hin). unfold key_bound in Hkeys. split; lia. }
  specialize (Hconstruction Hduties). unfold set_bound. lia.
Qed.

Section Context.
Context {B BE N E V K G C U : Type}.
Variable c : Pre.ctx B BE N E V K G C U.
Variable f : PreFrg.frg B BE E U.

Local Abbreviation site_enc := (PreFrg.phi_encoding c).
Local Abbreviation link_enc := (PreFrg.link_encoding c).
Local Abbreviation vertex_enc := (PreReset.vertex_encoding c).
Local Abbreviation arc_enc := (PreReset.arc_encoding c).
Local Abbreviation vertex := (PreReset.vertex (B := B) (BE := BE) (U := U)).

Definition links := N.of_nat (length (Map.elements (PreFrg.operands f))).
Definition phis := N.of_nat (length (FinSet.elements (PreFrg.phis f))).
Definition unsafe := N.of_nat (length (FinSet.elements (PreFrg.unsafe f))).
Definition arcs := N.of_nat (length (PreReset.edge_inventory c f)).
Definition nodes := N.of_nat (length (PreReset.node_inventory c f)).
Definition width := PreparedCost.id_width (PreReset.graph c f).
Definition edges := N.of_nat (edge_count (PreReset.graph c f)).

(** Primitive duties concern source components occurring in the finite input index inventory. *)
Record primitive_bounds w : Prop := PrimitiveBounds {
  site_components : forall b u,
    In (inl (b, u)) (PreReset.node_inventory c f) ->
    key_bound (Pre.eb (Pre.keys c)) b w /\ key_bound (Pre.eu (Pre.keys c)) u w;
  link_components : forall b u be,
    In (inr ((b, u), be)) (PreReset.node_inventory c f) ->
    key_bound (Pre.eb (Pre.keys c)) b w /\
    key_bound (Pre.eu (Pre.keys c)) u w /\
    key_bound (Pre.ebe (Pre.keys c)) be w
}.

Hypothesis Hlaw : Pre.laws c.
Hypothesis Hphi : FinSet.wf site_enc (PreFrg.phis f).
Hypothesis Hlinks : Map.wf link_enc (PreFrg.operands f).
Hypothesis Hunsafe : FinSet.wf site_enc (PreFrg.unsafe f).

Lemma site_work w k :
  primitive_bounds w -> In (inl k) (PreReset.node_inventory c f) ->
  key_bound site_enc k (phi_price w).
Proof.
  intros Hprimitive Hin. destruct k as [b u].
  destruct (site_components w Hprimitive b u Hin) as [Hb Hu].
  apply pair_work; assumption.
Qed.

Lemma link_work w key :
  primitive_bounds w -> In (inr key) (PreReset.node_inventory c f) ->
  key_bound link_enc key (link_price w).
Proof.
  intros Hprimitive Hin. destruct key as [[b u] be].
  destruct (link_components w Hprimitive b u be Hin) as [Hb [Hu Hbe]].
  apply pair_work; [apply pair_work; assumption|exact Hbe].
Qed.

Lemma vertex_work w v :
  primitive_bounds w -> In v (PreReset.node_inventory c f) ->
  key_bound vertex_enc v (vertex_price w).
Proof.
  intros Hprimitive Hin. apply sum_work.
  destruct v as [k|key].
  - apply site_work; assumption.
  - apply link_work; assumption.
Qed.

Lemma graph_nodes :
  Graph.nodes (PreReset.graph c f) = PreReset.node_inventory c f.
Proof.
  rewrite PreReset.graph_equation. reflexivity.
Qed.

Lemma endpoint_nodes ab :
  In ab (PreReset.incidence f) ->
  In (fst ab) (PreReset.node_inventory c f) /\
    In (snd ab) (PreReset.node_inventory c f).
Proof.
  destruct ab as [x y]. intro Hin.
  pose proof (PreReset.incidence_nodes c f x y Hlaw Hin) as Hnodes.
  now rewrite graph_nodes in Hnodes.
Qed.

Lemma arc_work w ab :
  primitive_bounds w -> In ab (PreReset.incidence f) ->
  key_bound arc_enc ab (arc_price w).
Proof.
  intros Hprimitive Hin.
  destruct (endpoint_nodes ab Hin) as [Hx Hy].
  destruct ab. apply pair_work; apply vertex_work; assumption.
Qed.

Lemma operand_nodes key op :
  Map.get link_enc key (PreFrg.operands f) = Some op ->
  In (inr key) (PreReset.node_inventory c f) /\
    In (inl (fst key)) (PreReset.node_inventory c f).
Proof.
  intro Hget. apply (endpoint_nodes (inr key, inl (fst key))).
  apply (PreReset.operand_owner_arc c f key op); assumption.
Qed.

Lemma phi_nodes k :
  FinSet.mem site_enc k (PreFrg.phis f) = true ->
  In (inl k) (PreReset.node_inventory c f).
Proof.
  intro Hmem. apply PreReset.node_inventory_exact; [exact Hlaw|].
  left. exists k. split; [reflexivity|]. left.
  apply (FinSet.elements_spec _ (PreFrg.phi_encoding_laws c Hlaw)); assumption.
Qed.

Lemma unsafe_nodes k :
  FinSet.mem site_enc k (PreFrg.unsafe f) = true ->
  In (inl k) (PreReset.node_inventory c f).
Proof.
  intro Hmem. apply PreReset.node_inventory_exact; [exact Hlaw|].
  left. exists k. split; [reflexivity|]. right.
  apply (FinSet.elements_spec _ (PreFrg.phi_encoding_laws c Hlaw)); assumption.
Qed.

Definition link_enumeration w := TrieCost.trie_k * (1 + links * link_price w).
Definition phi_enumeration w := TrieCost.trie_k * (1 + phis * phi_price w) + phis.
Definition unsafe_enumeration w := TrieCost.trie_k * (1 + unsafe * phi_price w) + unsafe.

Lemma links_cost w :
  primitive_bounds w -> Cost.ticks (Map.elements_c (PreFrg.operands f)) <= link_enumeration w.
Proof.
  intro Hprimitive. apply (map_enumeration link_enc (PreFrg.operands f) (link_price w));
    [exact Hlinks|].
  intros key op Hget. pose proof (link_work w key Hprimitive
    (proj1 (operand_nodes key op Hget))).
  unfold key_bound in H. lia.
Qed.

Lemma phis_cost w :
  primitive_bounds w ->
  Cost.ticks (FinSet.elements_c (PreFrg.phis f)) <= phi_enumeration w.
Proof.
  intro Hprimitive. apply (set_enumeration site_enc (PreFrg.phis f) (phi_price w));
    [exact Hphi|].
  intros k Hmem. pose proof (site_work w k Hprimitive (phi_nodes k Hmem)).
  unfold key_bound in H. lia.
Qed.

Lemma unsafe_cost w :
  primitive_bounds w ->
  Cost.ticks (FinSet.elements_c (PreFrg.unsafe f)) <= unsafe_enumeration w.
Proof.
  intro Hprimitive. apply (set_enumeration site_enc (PreFrg.unsafe f) (phi_price w));
    [exact Hunsafe|].
  intros k Hmem. pose proof (site_work w k Hprimitive (unsafe_nodes k Hmem)).
  unfold key_bound in H. lia.
Qed.

(** The incidence pass charges every original operand and copies at most two arcs per operand. *)
Theorem incidence_cost w :
  primitive_bounds w ->
  Cost.ticks (PreReset.incidence_c f) <= link_enumeration w + 4 * links.
Proof.
  intro Hprimitive. pose proof (links_cost w Hprimitive) as Henumeration.
  rewrite PreReset.incidence_ticks.
  assert (Hsum : forall bs : list (((B * U) * BE) * PreFrg.operand B E U),
    fold_right (fun binding n => 2 + N.of_nat (length (PreReset.link_arcs binding)) + n)
      0 bs <= 4 * N.of_nat (length bs)).
  { intro bs. induction bs as [|[key op] rest IH]; [cbn; lia|].
    cbn [fold_right length]. rewrite Nat2N.inj_succ.
    pose proof (PreReset.link_arcs_length (key, op)) as Hlength.
    lia. }
  specialize (Hsum (Map.elements (PreFrg.operands f))).
  unfold links in *. lia.
Qed.

Lemma incidence_length :
  N.of_nat (length (PreReset.incidence f)) <= 2 * links.
Proof.
  rewrite PreReset.incidence_equation.
  assert (Hlength : forall bs : list (((B * U) * BE) * PreFrg.operand B E U),
    N.of_nat (length (flat_map PreReset.link_arcs bs)) <= 2 * N.of_nat (length bs)).
  { intro bs. induction bs as [|binding rest IH]; [cbn; lia|].
    cbn [flat_map]. rewrite length_app, Nat2N.inj_add.
    cbn [length]. rewrite Nat2N.inj_succ.
    pose proof (PreReset.link_arcs_length binding). lia. }
  apply Hlength.
Qed.

Definition node_input :=
  map (fun k => inl k : vertex)
    (FinSet.elements (PreFrg.phis f) ++ FinSet.elements (PreFrg.unsafe f)) ++
    flat_map (fun ab => [fst ab; snd ab]) (PreReset.edge_inventory c f).

Lemma node_input_length :
  N.of_nat (length node_input) = phis + unsafe + 2 * arcs.
Proof.
  unfold node_input. rewrite length_app, length_map, length_app, !Nat2N.inj_add.
  assert (Hends : forall es : list (vertex * vertex),
    N.of_nat (length (flat_map (fun ab => [fst ab; snd ab]) es)) =
      2 * N.of_nat (length es)).
  { intro es. induction es; cbn [flat_map app length];
      rewrite ?Nat2N.inj_succ, ?IHes; lia. }
  rewrite Hends. reflexivity.
Qed.

Lemma node_input_work w v :
  primitive_bounds w -> In v node_input -> key_bound vertex_enc v (vertex_price w).
Proof.
  intros Hprimitive Hin. apply vertex_work; [exact Hprimitive|].
  rewrite PreReset.node_inventory_equation. apply set_members.
  - apply PreReset.vertex_encoding_laws; exact Hlaw.
  - exact Hin.
Qed.

Definition graph_bound w :=
  link_enumeration w + 4 * links + set_bound (2 * links) (arc_price w) + arcs +
  phi_enumeration w + unsafe_enumeration w + phis + 2 * (phis + unsafe) +
  set_bound (phis + unsafe + 2 * arcs) (vertex_price w) +
  1 + arcs * (7 + 6 * vertex_price w).

(** The graph setup bound expands all owned traversals and canonical index construction. *)
Theorem graph_cost w :
  primitive_bounds w -> Cost.ticks (PreReset.graph_c c f) <= graph_bound w.
Proof.
  intro Hprimitive.
  pose proof (incidence_cost w Hprimitive) as Hincidence.
  pose proof (phis_cost w Hprimitive) as Hphis.
  pose proof (unsafe_cost w Hprimitive) as Hunsafe_cost.
  pose proof (canonical_cost arc_enc
    (pair_encoding_laws _ _ (PreReset.vertex_encoding_laws c Hlaw)
      (PreReset.vertex_encoding_laws c Hlaw))
    (PreReset.incidence f) (arc_price w)
    (fun ab Hin => arc_work w ab Hprimitive Hin)) as Hedges.
  change (Cost.ticks (FinSet.of_list_c arc_enc (PreReset.incidence f)) +
    Cost.ticks (FinSet.elements_c (FinSet.of_list arc_enc (PreReset.incidence f))) <=
    set_bound (N.of_nat (length (PreReset.incidence f))) (arc_price w)) in Hedges.
  pose proof (canonical_cost vertex_enc (PreReset.vertex_encoding_laws c Hlaw)
    node_input (vertex_price w) (fun v Hin => node_input_work w v Hprimitive Hin)) as Hnodes.
  change (Cost.ticks (FinSet.of_list_c vertex_enc node_input) +
    Cost.ticks (FinSet.elements_c (FinSet.of_list vertex_enc node_input)) <=
    set_bound (N.of_nat (length node_input)) (vertex_price w)) in Hnodes.
  rewrite node_input_length in Hnodes.
  pose proof (IndexCost.group_by_cost Map.cost_laws_hold vertex_enc
    (PreReset.vertex_encoding_laws c Hlaw)
    (Cost.lift (fun _ => 1) (@fst vertex vertex)) (PreReset.edge_inventory c f)
    (vertex_price w) (vertex_price w) 1) as Hgroup.
  assert (Hgroup_keys : forall ab, In ab (PreReset.edge_inventory c f) ->
    Cost.ticks (Cost.lift (fun _ => 1) (@fst vertex vertex) ab) <= 1 /\
    Cost.ticks (encode_c vertex_enc
      (Cost.value (Cost.lift (fun _ => 1) (@fst vertex vertex) ab))) <= vertex_price w /\
    key_bits vertex_enc
      (Cost.value (Cost.lift (fun _ => 1) (@fst vertex vertex) ab)) <= vertex_price w).
  { intros ab Hin. apply (PreReset.edge_inventory_exact c f ab Hlaw) in Hin.
    pose proof (vertex_work w (fst ab) Hprimitive (proj1 (endpoint_nodes ab Hin))) as Hwork.
    change (Cost.ticks (encode_c vertex_enc (fst ab)) + key_bits vertex_enc (fst ab) <=
      vertex_price w) in Hwork.
    rewrite Cost.ticks_lift, !Cost.value_lift.
    split; [reflexivity|]. split.
    - exact (N.le_trans _ _ _ (N.le_add_r _ _) Hwork).
    - exact (N.le_trans _ _ _ (N.le_add_l _ _) Hwork). }
  specialize (Hgroup Hgroup_keys).
  replace (6 + 1 + 2 * vertex_price w + 4 * vertex_price w)
    with (7 + 6 * vertex_price w) in Hgroup by lia.
  pose proof incidence_length as Hraw.
  assert (Hset : set_bound (N.of_nat (length (PreReset.incidence f))) (arc_price w) <=
    set_bound (2 * links) (arc_price w)).
  { apply set_bound_monotone. exact Hraw. }
  rewrite PreReset.graph_ticks.
  fold (PreReset.edge_inventory c f).
  fold node_input.
  rewrite length_app, Nat2N.inj_add.
  change (Cost.ticks (PreReset.incidence_c f) +
    Cost.ticks (FinSet.of_list_c arc_enc (PreReset.incidence f)) +
    Cost.ticks (FinSet.elements_c (FinSet.of_list arc_enc (PreReset.incidence f))) + arcs +
    Cost.ticks (FinSet.elements_c (PreFrg.phis f)) +
    Cost.ticks (FinSet.elements_c (PreFrg.unsafe f)) + phis + 2 * (phis + unsafe) +
    Cost.ticks (FinSet.of_list_c vertex_enc node_input) +
    Cost.ticks (FinSet.elements_c (FinSet.of_list vertex_enc node_input)) +
    Cost.ticks (Index.group_by_c vertex_enc
      (Cost.lift (fun _ => 1) (@fst vertex vertex)) (PreReset.edge_inventory c f)) <=
    graph_bound w).
  fold arcs in Hgroup.
  eapply N.le_trans with (m :=
    (link_enumeration w + 4 * links) + set_bound (2 * links) (arc_price w) + arcs +
      phi_enumeration w + unsafe_enumeration w + phis + 2 * (phis + unsafe) +
      set_bound (phis + unsafe + 2 * arcs) (vertex_price w) +
      (1 + arcs * (7 + 6 * vertex_price w))).
  - apply sequence_bounds.
    + exact Hincidence.
    + exact (N.le_trans _ _ _ Hedges Hset).
    + exact Hphis.
    + exact Hunsafe_cost.
    + exact Hnodes.
    + exact Hgroup.
  - unfold graph_bound. rewrite N.add_assoc. reflexivity.
Qed.

Lemma arcs_dictionary :
  Prepared.node_enc (PreReset.arcs c f) = vertex_enc.
Proof.
  rewrite PreReset.arcs_equation, Prepared.prepare_equation. reflexivity.
Qed.

Lemma arcs_names :
  Prepared.names (PreReset.arcs c f) =
    Intern.of_list vertex_enc (Graph.nodes (PreReset.graph c f)).
Proof.
  rewrite PreReset.arcs_equation, Prepared.prepare_names. reflexivity.
Qed.

Lemma lookup_cost w v :
  primitive_bounds w -> In v (PreReset.node_inventory c f) ->
  Cost.ticks (Prepared.id_of_c (PreReset.arcs c f) v) <= 1 + vertex_price w.
Proof.
  intros Hprimitive Hin.
  assert (Hlookup : Cost.ticks (Prepared.id_of_c (PreReset.arcs c f) v) <=
    1 + Cost.ticks (encode_c (Prepared.node_enc (PreReset.arcs c f)) v) +
      key_bits (Prepared.node_enc (PreReset.arcs c f)) v).
  { exact (InternCost.find_cost Map.cost_laws_hold _ v (Prepared.names (PreReset.arcs c f))). }
  rewrite arcs_dictionary in Hlookup.
  pose proof (vertex_work w v Hprimitive Hin) as Hwork.
  change (Cost.ticks (encode_c vertex_enc v) + key_bits vertex_enc v <= vertex_price w) in Hwork.
  lia.
Qed.

Lemma id_width v id :
  Prepared.id_of (PreReset.arcs c f) v = Some id ->
  key_bits positive_encoding id <= width.
Proof.
  intro Hid.
  rewrite Prepared.id_of_equation, arcs_dictionary, arcs_names in Hid.
  exact (PreparedCost.table_id_width vertex_enc (PreReset.vertex_encoding_laws c Hlaw)
    (PreReset.graph c f) v id Hid).
Qed.

Lemma dense_membership_cost reset v id :
  Prepared.id_of (PreReset.arcs c f) v = Some id ->
  Cost.ticks (FinSet.mem_c positive_encoding id reset) <= SearchCost.id_cost width.
Proof.
  intro Hid. apply SearchCost.id_membership_cost. exact (id_width v id Hid).
Qed.

Lemma flag_cost w base k :
  primitive_bounds w -> In (inl k) (PreReset.node_inventory c f) ->
  Cost.ticks (PreReset.flag_c c base k) <= 1 + phi_price w.
Proof.
  intros Hprimitive Hin. rewrite PreReset.flag_ticks.
  apply get_key_cost, site_work; assumption.
Qed.

Definition flags_bound w :=
  phis * (4 + vertex_price w + 2 * phi_price w + SearchCost.id_cost width).

(** Materialisation charges each original phi key, its dense membership and both dictionary reads. *)
Theorem flags_cost w base use_base reset :
  primitive_bounds w ->
  Cost.ticks (PreReset.flags_c c (PreReset.arcs c f)
    (FinSet.elements (PreFrg.phis f)) base use_base reset) <= flags_bound w.
Proof.
  intro Hprimitive. rewrite PreReset.flags_ticks.
  apply sum_bound. intros k Hin.
  assert (Hnode : In (inl k) (PreReset.node_inventory c f)).
  { apply phi_nodes. apply (FinSet.elements_spec _ (PreFrg.phi_encoding_laws c Hlaw));
      assumption. }
  pose proof (lookup_cost w (inl k) Hprimitive Hnode) as Hlookup.
  pose proof (flag_cost w base k Hprimitive Hnode) as Hflag.
  pose proof (site_work w k Hprimitive Hnode) as Hkey.
  change (Cost.ticks (encode_c site_enc k) + key_bits site_enc k <= phi_price w) in Hkey.
  change (2 + Cost.ticks (Prepared.id_of_c (PreReset.arcs c f) (inl k : vertex)) +
    (match Prepared.id_of (PreReset.arcs c f) (inl k : vertex) with
     | None => 0
     | Some id => Cost.ticks (FinSet.mem_c positive_encoding id reset)
     end) +
    (if use_base then Cost.ticks (PreReset.flag_c c base k) else 0) +
    Cost.ticks (encode_c site_enc k) + key_bits site_enc k <=
    4 + vertex_price w + 2 * phi_price w + SearchCost.id_cost width).
  destruct (Prepared.id_of (PreReset.arcs c f) (inl k)) as [id|] eqn:Hid.
  - pose proof (dense_membership_cost reset (inl k) id Hid) as Hmem.
    destruct use_base; lia.
  - destruct use_base; lia.
Qed.

Lemma seed_cost w which down can binding :
  primitive_bounds w -> In binding (Map.elements (PreFrg.operands f)) ->
  Cost.ticks (PreReset.seed_c c which down can binding) <= 1 + phi_price w.
Proof.
  intros Hprimitive Hin. destruct binding as [key op].
  apply (Map.elements_spec link_enc (PreFrg.link_encoding_laws c Hlaw) _ _ _ Hlinks) in Hin.
  pose proof (proj2 (operand_nodes key op Hin)) as Hnode.
  pose proof (flag_cost w down (fst key) Hprimitive Hnode) as Hdown.
  pose proof (flag_cost w can (fst key) Hprimitive Hnode) as Hcan.
  rewrite (PreReset.seed_ticks c which down can (key, op)).
  destruct which, (PreFrg.operand_version op), (PreFrg.real_use op); assumption || lia.
Qed.

Definition seeds_bound w :=
  unsafe_enumeration w + link_enumeration w + links * (3 + phi_price w).
Definition roots := unsafe + links.

Lemma seeds_length which down can :
  N.of_nat (length (PreReset.seeds c f which down can)) <= roots.
Proof.
  assert (Hfilter : forall pred,
    N.of_nat (length (filter pred (Map.elements (PreFrg.operands f)))) <= links).
  { intro pred. pose proof (filter_length_le pred (Map.elements (PreFrg.operands f))).
    unfold links. lia. }
  rewrite PreReset.seeds_equation. destruct which.
  - change (unsafe <= unsafe + links). apply N.le_add_r.
  - rewrite length_map. eapply N.le_trans; [apply Hfilter|unfold roots; lia].
  - rewrite length_map. eapply N.le_trans; [apply Hfilter|unfold roots; lia].
Qed.

(** Each seed phase pays the original canonical inventory and all guarded callback decisions. *)
Theorem seeds_cost w which down can :
  primitive_bounds w ->
  Cost.ticks (PreReset.seeds_c c f which down can) <= seeds_bound w.
Proof.
  intro Hprimitive.
  pose proof (unsafe_cost w Hprimitive) as Hunsafe_cost.
  pose proof (links_cost w Hprimitive) as Hlink_cost.
  assert (Hphase : forall phase,
    Cost.ticks (Map.elements_c (PreFrg.operands f)) +
      fold_right (fun binding n => 1 +
        Cost.ticks (PreReset.seed_c c phase down can binding) + n)
        0 (Map.elements (PreFrg.operands f)) +
      N.of_nat (length (filter
        (fun binding => Cost.value (PreReset.seed_c c phase down can binding))
        (Map.elements (PreFrg.operands f)))) <=
      link_enumeration w + links * (3 + phi_price w)).
  { intro phase.
    assert (Hfilter : fold_right (fun binding n => 1 +
      Cost.ticks (PreReset.seed_c c phase down can binding) + n)
      0 (Map.elements (PreFrg.operands f)) <= links * (2 + phi_price w)).
    { apply sum_bound. intros binding Hin.
      pose proof (seed_cost w phase down can binding Hprimitive Hin). lia. }
    pose proof (filter_length_le
      (fun binding => Cost.value (PreReset.seed_c c phase down can binding))
      (Map.elements (PreFrg.operands f))) as Hlength.
    unfold links in *. nia. }
  rewrite PreReset.seeds_ticks.
  destruct which.
  - unfold seeds_bound. lia.
  - specialize (Hphase PreReset.Cannot). unfold seeds_bound. lia.
  - specialize (Hphase PreReset.Later). unfold seeds_bound. lia.
Qed.

Lemma graph_incidence ab :
  In ab (Prepared.all_edges (PreReset.graph c f)) -> In ab (PreReset.incidence f).
Proof.
  intro Hin. apply Prepared.all_edges_spec in Hin.
  destruct Hin as [v [Hv Hout]].
  apply (PreReset.graph_out c f v ab Hlaw) in Hout.
  apply (PreReset.edge_inventory_exact c f ab Hlaw). exact (proj1 Hout).
Qed.

Lemma preparation_bounds w :
  primitive_bounds w ->
  PreparedCost.prepare_bounds vertex_enc (PreReset.graph c f)
    (vertex_price w) (vertex_price w) (1 + vertex_price w) 1 1.
Proof.
  intro Hprimitive.
  assert (Hkeys : forall v, In v (Graph.nodes (PreReset.graph c f)) ->
    Cost.ticks (encode_c vertex_enc v) <= vertex_price w /\ key_bits vertex_enc v <= vertex_price w).
  { intros v Hin. rewrite graph_nodes in Hin.
    pose proof (vertex_work w v Hprimitive Hin) as Hwork.
    change (Cost.ticks (encode_c vertex_enc v) + key_bits vertex_enc v <= vertex_price w) in Hwork.
    split.
    - exact (N.le_trans _ _ _ (N.le_add_r _ _) Hwork).
    - exact (N.le_trans _ _ _ (N.le_add_l _ _) Hwork). }
  constructor.
  - exact Hkeys.
  - intros v Hin. rewrite PreReset.graph_equation in Hin. contradiction.
  - intros v Hin.
    change (In v (Graph.nodes (PreReset.graph c f))) in Hin.
    rewrite graph_nodes in Hin.
    pose proof (vertex_work w v Hprimitive Hin) as Hwork.
    change (Cost.ticks (Graph.out_c (PreReset.graph c f) v) <= 1 + vertex_price w).
    rewrite PreReset.graph_equation.
    eapply N.le_trans; [apply IndexCost.find_cost, Map.cost_laws_hold|].
    change (1 + Cost.ticks (encode_c vertex_enc v) + key_bits vertex_enc v <= 1 + vertex_price w).
    change (Cost.ticks (encode_c vertex_enc v) + key_bits vertex_enc v <= vertex_price w) in Hwork.
    lia.
  - intros ab Hin.
    destruct (endpoint_nodes ab (graph_incidence ab Hin)) as [Hsource Htarget].
    rewrite <- graph_nodes in Hsource, Htarget.
    destruct (Hkeys (fst ab) Hsource) as [Hse Hsb].
    destruct (Hkeys (snd ab) Htarget) as [Hte Htb].
    destruct (PreReset.graph_endpoints c f ab) as [Hs Ht].
    change (Cost.ticks (Graph.source_c (PreReset.graph c f) ab) <= 1 /\
      Cost.ticks (Graph.target_c (PreReset.graph c f) ab) <= 1 /\
      Cost.ticks (encode_c vertex_enc (Graph.source (PreReset.graph c f) ab)) <= vertex_price w /\
      key_bits vertex_enc (Graph.source (PreReset.graph c f) ab) <= vertex_price w /\
      Cost.ticks (encode_c vertex_enc (Graph.target (PreReset.graph c f) ab)) <= vertex_price w /\
      key_bits vertex_enc (Graph.target (PreReset.graph c f) ab) <= vertex_price w).
    rewrite Hs, Ht.
    split.
    + rewrite PreReset.graph_equation.
      change (Cost.ticks (Cost.lift (fun _ => 1) (@fst vertex vertex) ab) <= 1).
      rewrite Cost.ticks_lift. reflexivity.
    + split.
      * rewrite PreReset.graph_equation.
        change (Cost.ticks (Cost.lift (fun _ => 1) (@snd vertex vertex) ab) <= 1).
        rewrite Cost.ticks_lift. reflexivity.
      * repeat split; assumption.
Qed.

Definition preparation_bound w :=
  2 + nodes *
    (20 + InternCost.intern_k + 10 * vertex_price w + 3 * width + 3 * (1 + vertex_price w)) +
    edges * (20 + 10 * vertex_price w).
Definition setup_bound w := graph_bound w + preparation_bound w.

(** Shared preparation derives all node, edge, callback and unary driver-construction costs. *)
Theorem preparation_cost w :
  primitive_bounds w ->
  Cost.ticks (Prepared.prepare_c vertex_enc (PreReset.graph c f)) <= preparation_bound w.
Proof.
  intro Hprimitive.
  pose proof (PreparedCost.prepare_credit_cost vertex_enc
    (PreReset.vertex_encoding_laws c Hlaw) (PreReset.graph c f)
    (vertex_price w) (vertex_price w) (1 + vertex_price w) 1 1
    (nodes_nodup (proj1 (PreReset.graph_ready c f Hlaw)))
    (preparation_bounds w Hprimitive)) as Hcost.
  change (Cost.ticks (Prepared.prepare_c vertex_enc (PreReset.graph c f)) <=
    2 + N.of_nat (length (Graph.nodes (PreReset.graph c f))) *
      (20 + InternCost.intern_k + 5 * vertex_price w + 5 * vertex_price w +
        3 * width + 3 * (1 + vertex_price w)) +
    edges * (17 + 4 * vertex_price w + 6 * vertex_price w + 1 + 2 * 1) +
    N.of_nat (length (Graph.entries (PreReset.graph c f))) *
      (3 + vertex_price w + vertex_price w)) in Hcost.
  assert (Hentries : Graph.entries (PreReset.graph c f) = []).
  { rewrite PreReset.graph_equation. reflexivity. }
  rewrite Hentries in Hcost. cbn [length] in Hcost.
  rewrite graph_nodes in Hcost. fold nodes edges width in Hcost.
  assert (Hcoefficients : forall n m v d ik : BinNums.N,
    2 + n * (20 + ik + 5 * v + 5 * v + 3 * d + 3 * (1 + v)) +
      m * (17 + 4 * v + 6 * v + 1 + 2 * 1) + 0 * (3 + v + v) =
    2 + n * (20 + ik + 10 * v + 3 * d + 3 * (1 + v)) + m * (20 + 10 * v)).
  { intros. ring. }
  change (Cost.ticks (Prepared.prepare_c vertex_enc (PreReset.graph c f)) <=
    2 + nodes * (20 + InternCost.intern_k + 5 * vertex_price w + 5 * vertex_price w +
      3 * width + 3 * (1 + vertex_price w)) +
      edges * (17 + 4 * vertex_price w + 6 * vertex_price w + 1 + 2 * 1) +
      0 * (3 + vertex_price w + vertex_price w)) in Hcost.
  rewrite Hcoefficients in Hcost. exact Hcost.
Qed.

(** Setup composes the fully priced incidence graph with the single public preparation call. *)
Theorem setup_cost w :
  primitive_bounds w -> Cost.ticks (PreReset.arcs_c c f) <= setup_bound w.
Proof.
  intro Hprimitive. rewrite PreReset.arcs_ticks.
  pose proof (graph_cost w Hprimitive).
  pose proof (preparation_cost w Hprimitive). unfold setup_bound. lia.
Qed.

Lemma admission_cost w which down can v :
  primitive_bounds w -> In v (PreReset.node_inventory c f) ->
  Cost.ticks (PreReset.admits_c c f which down can v) <=
    1 + phi_price w + link_price w.
Proof.
  intros Hprimitive Hin. rewrite PreReset.admits_ticks. destruct v as [k|key].
  - pose proof (flag_cost w down k Hprimitive Hin).
    pose proof (flag_cost w can k Hprimitive Hin).
    destruct which; lia.
  - pose proof (get_key_cost link_enc key (PreFrg.operands f) (link_price w)
      (link_work w key Hprimitive Hin)).
    destruct which; lia.
Qed.

Definition scope_bound w :=
  nodes * (7 + phi_price w + link_price w + vertex_price w + 2 * width).

(** Blocking a query charges its full scan and only the resulting finite dense-ID inventory. *)
Theorem scope_cost w which down can :
  primitive_bounds w ->
  Cost.ticks (PreReset.scope_c c (PreReset.arcs c f) f which down can) <= scope_bound w.
Proof.
  intro Hprimitive. rewrite PreReset.scope_ticks.
  set (callback := fun v => Cost.value
    (Cost.step ;; let* keep := PreReset.admits_c c f which down can v in
      if keep then Cost.ret None else Prepared.id_of_c (PreReset.arcs c f) v)).
  set (vs := Graph.nodes (Prepared.graph (PreReset.arcs c f))).
  set (denied := filter_map callback vs).
  assert (Hnodes : vs = PreReset.node_inventory c f).
  { change (Graph.nodes (Prepared.graph (PreReset.arcs c f)) = PreReset.node_inventory c f).
    rewrite PreReset.arcs_equation, Prepared.prepare_graph.
    exact graph_nodes. }
  pose proof (filter_map_length callback vs) as Hlength.
  change (length denied <= length vs)%nat in Hlength.
  assert (Hscan : fold_right (fun v n => 2 +
    Cost.ticks (PreReset.admits_c c f which down can v) +
    (if PreReset.admits c f which down can v then 0
      else Cost.ticks (Prepared.id_of_c (PreReset.arcs c f) v)) + n)
    0 vs <= nodes * (4 + phi_price w + link_price w + vertex_price w)).
  { rewrite Hnodes. apply sum_bound. intros v Hin.
    pose proof (admission_cost w which down can v Hprimitive Hin) as Hguard.
    pose proof (lookup_cost w v Hprimitive Hin) as Hlookup.
    destruct (PreReset.admits c f which down can v); lia. }
  pose proof (FinSet.of_list_numeric_cost Map.cost_laws_hold positive_encoding
    denied width width) as Hbuild.
  assert (Hkeys : forall id, In id denied ->
    Cost.ticks (encode_c positive_encoding id) <= width /\ key_bits positive_encoding id <= width).
  { intros id Hin. apply filter_map_spec in Hin. destruct Hin as [v [Hv Hout]].
    unfold callback in Hout. rewrite !Cost.value_bind in Hout.
    fold (PreReset.admits c f which down can v) in Hout.
    destruct (PreReset.admits c f which down can v); [discriminate|].
    change (Prepared.id_of (PreReset.arcs c f) v = Some id) in Hout.
    pose proof (id_width v id Hout) as Hwidth. split; [|exact Hwidth].
    pose proof (encode_cost_bound positive_encoding_cost_laws id) as Hencode.
    exact (N.le_trans _ _ _ Hencode Hwidth). }
  specialize (Hbuild Hkeys).
  assert (Hcount : N.of_nat (length denied) <= nodes).
  { assert (Hsize : N.of_nat (length vs) = nodes).
    { rewrite Hnodes. reflexivity. }
    rewrite <- Hsize. lia. }
  assert (Hconstruction : Cost.ticks (FinSet.of_list_c positive_encoding denied) <=
    nodes * (3 + 2 * width)).
  { eapply N.le_trans; [exact Hbuild|]. nia. }
  change (fold_right (fun v n => 2 +
    Cost.ticks (PreReset.admits_c c f which down can v) +
    (if PreReset.admits c f which down can v then 0
      else Cost.ticks (Prepared.id_of_c (PreReset.arcs c f) v)) + n)
    0 vs + Cost.ticks (FinSet.of_list_c positive_encoding denied) <= scope_bound w).
  unfold scope_bound. nia.
Qed.

Lemma arcs_graph :
  Prepared.graph (PreReset.arcs c f) = PreReset.graph c f.
Proof.
  rewrite PreReset.arcs_equation, Prepared.prepare_graph. reflexivity.
Qed.

Lemma seeds_nodes which down can k :
  In k (PreReset.seeds c f which down can) ->
  In (inl k) (PreReset.node_inventory c f).
Proof.
  rewrite PreReset.seeds_equation. destruct which.
  - intro Hin. apply unsafe_nodes.
    apply (FinSet.elements_spec _ (PreFrg.phi_encoding_laws c Hlaw)); assumption.
  - rewrite in_map_iff. intros [[key op] [Heq Hin]].
    apply filter_In in Hin. destruct Hin as [Hin Hguard].
    apply (Map.elements_spec link_enc (PreFrg.link_encoding_laws c Hlaw) _ _ _ Hlinks) in Hin.
    rewrite <- Heq. exact (proj2 (operand_nodes key op Hin)).
  - rewrite in_map_iff. intros [[key op] [Heq Hin]].
    apply filter_In in Hin. destruct Hin as [Hin Hguard].
    apply (Map.elements_spec link_enc (PreFrg.link_encoding_laws c Hlaw) _ _ _ Hlinks) in Hin.
    rewrite <- Heq. exact (proj2 (operand_nodes key op Hin)).
Qed.

Definition query_ids which down can :=
  Prepared.present (Prepared.id_of (PreReset.arcs c f))
    (map (fun k => inl k : vertex) (PreReset.seeds c f which down can)).

Lemma query_ids_length which down can :
  N.of_nat (length (query_ids which down can)) <= roots.
Proof.
  pose proof (Prepared.present_length (Prepared.id_of (PreReset.arcs c f))
    (map (fun k => inl k : vertex) (PreReset.seeds c f which down can))) as Hpresent.
  rewrite length_map in Hpresent.
  pose proof (seeds_length which down can) as Hseeds.
  unfold query_ids. lia.
Qed.

Lemma oriented_inventory which :
  length (Graph.nodes (Prepared.graph (PreReset.directed (PreReset.arcs c f) which))) =
    length (PreReset.node_inventory c f) /\
  edge_count (Prepared.graph (PreReset.directed (PreReset.arcs c f) which)) =
    edge_count (PreReset.graph c f) /\
  Prepared.fuel (PreReset.directed (PreReset.arcs c f) which) =
    Prepared.fuel (PreReset.arcs c f).
Proof.
  pose proof (PreReset.arcs_ready c f Hlaw) as Hp.
  pose proof (PreReset.directed_ready _ which Hp) as Hdirected.
  assert (Hmembers : forall v,
    In v (Graph.nodes (Prepared.graph (PreReset.directed (PreReset.arcs c f) which))) <->
    In v (Graph.nodes (Prepared.graph (PreReset.arcs c f)))).
  { intro v. rewrite (Prepared.ids_domain _ (proj2 (proj2 Hdirected))),
      (Prepared.ids_domain _ (proj2 (proj2 Hp))).
    split; intros [id Hid]; exists id.
    - rewrite PreReset.directed_id in Hid. exact Hid.
    - rewrite PreReset.directed_id. exact Hid. }
  assert (Hlength :
    length (Graph.nodes (Prepared.graph (PreReset.directed (PreReset.arcs c f) which))) =
    length (Graph.nodes (Prepared.graph (PreReset.arcs c f)))).
  { apply Permutation_length, NoDup_Permutation.
    - exact (nodes_nodup (proj1 Hdirected)).
    - exact (nodes_nodup (proj1 Hp)).
    - exact Hmembers. }
  rewrite arcs_graph in Hlength.
  change (length (Graph.nodes (Prepared.graph (PreReset.directed (PreReset.arcs c f) which))) =
    length (Graph.nodes (PreReset.graph c f))) in Hlength.
  rewrite graph_nodes in Hlength. split; [exact Hlength|].
  destruct which.
  - change (edge_count (Prepared.graph (Prepared.reverse (PreReset.arcs c f) [])) =
      edge_count (PreReset.graph c f) /\
      Prepared.fuel (Prepared.reverse (PreReset.arcs c f) []) = Prepared.fuel (PreReset.arcs c f)).
    rewrite Prepared.reverse_equation. split.
    + change (edge_count (Prepared.reverse_graph (PreReset.arcs c f) []) =
        edge_count (PreReset.graph c f)).
      rewrite Prepared.reverse_edge_count by exact Hp. now rewrite arcs_graph.
    + reflexivity.
  - split; [change (edge_count (Prepared.graph (PreReset.arcs c f)) =
      edge_count (PreReset.graph c f)); now rewrite arcs_graph|reflexivity].
  - split; [change (edge_count (Prepared.graph (PreReset.arcs c f)) =
      edge_count (PreReset.graph c f)); now rewrite arcs_graph|reflexivity].
Qed.

Definition fuel_width :=
  N.pos (Pos.size (Pos.of_succ_nat
    (2 * length (PreReset.node_inventory c f) + edge_count (PreReset.graph c f) + 1))).

Lemma driver_width :
  N.pos (Pos.size (Prepared.fuel (PreReset.arcs c f))) = fuel_width.
Proof.
  pose proof (Prepared.fuel_value _ (proj2 (proj2 (PreReset.arcs_ready c f Hlaw)))) as Hfuel.
  change (Pos.to_nat (Prepared.fuel (PreReset.arcs c f)) =
    2 * length (Graph.nodes (Prepared.graph (PreReset.arcs c f))) +
      edge_count (Prepared.graph (PreReset.arcs c f)) + 2)%nat in Hfuel.
  rewrite arcs_graph in Hfuel.
  change (Pos.to_nat (Prepared.fuel (PreReset.arcs c f)) =
    2 * length (Graph.nodes (PreReset.graph c f)) +
      edge_count (PreReset.graph c f) + 2)%nat in Hfuel.
  rewrite graph_nodes in Hfuel.
  assert (Heq : Prepared.fuel (PreReset.arcs c f) = Pos.of_succ_nat
    (2 * length (PreReset.node_inventory c f) + edge_count (PreReset.graph c f) + 1)).
  { apply Pos2Nat.inj. rewrite SuccNat2Pos.id_succ.
    etransitivity; [exact Hfuel|].
    assert (Harithmetic : forall n m : nat, (2 * n + m + 2 = S (2 * n + m + 1))%nat)
      by (intros; lia).
    apply Harithmetic. }
  rewrite Heq. reflexivity.
Qed.

Lemma search_width which down can :
  SearchCost.width_bound (PreReset.directed (PreReset.arcs c f) which)
    (query_ids which down can) width.
Proof.
  intros id [Hvalid|Hroot].
  - destruct Hvalid as [v [Hin Hid]].
    rewrite PreReset.directed_id in Hid. exact (id_width v id Hid).
  - apply Prepared.present_spec in Hroot. destruct Hroot as [v [Hin Hid]].
    exact (id_width v id Hid).
Qed.

Definition search_bound :=
  SearchCost.step_k width 1 * (nodes + edges) +
  roots * (SearchCost.root_k width 1 + fuel_width + 1) + 2 * nodes.

(** The existing search driver pays the shared graph inventory, all roots and binary fuel descent. *)
Theorem search_cost which down can :
  Cost.ticks (SearchRun.run_c (PreReset.directed (PreReset.arcs c f) which)
    Visitor.noop (PreReset.scope c (PreReset.arcs c f) f which down can)
    (query_ids which down can) tt) <= search_bound.
Proof.
  pose proof (PreReset.arcs_ready c f Hlaw) as Hp.
  pose proof (SearchCost.search_credit_cost
    (PreReset.directed (PreReset.arcs c f) which) Visitor.noop (fun _ : unit => 0)
    1 (PreReset.scope c (PreReset.arcs c f) f which down can)
    (query_ids which down can) width tt
    (PreReset.directed_ready _ which Hp) (search_width which down can)
    (Visitor.noop_amortised (fun _ : unit => 0))) as Hcost.
  destruct (oriented_inventory which) as [Hnodes [Hedges Hfuel]].
  rewrite Hnodes, Hedges, Hfuel, driver_width in Hcost.
  fold nodes edges in Hcost.
  pose proof (query_ids_length which down can) as Hroots.
  assert (Hroot_cost : N.of_nat (length (query_ids which down can)) *
    (SearchCost.root_k width 1 + fuel_width + 1) <=
    roots * (SearchCost.root_k width 1 + fuel_width + 1)) by nia.
  unfold search_bound. lia.
Qed.

Lemma root_conversion_cost w which down can :
  primitive_bounds w ->
  Cost.ticks (Prepared.present_c (Prepared.id_of_c (PreReset.arcs c f))
    (map (fun k => inl k : vertex) (PreReset.seeds c f which down can))) <=
    roots * (3 + vertex_price w).
Proof.
  intro Hprimitive. rewrite PreparedCost.present_cost.
  pose proof (seeds_length which down can) as Hroots.
  assert (Hcost : fold_right (fun v n => 2 +
    Cost.ticks (Prepared.id_of_c (PreReset.arcs c f) v) + n)
    0 (map (fun k => inl k : vertex) (PreReset.seeds c f which down can)) <=
    N.of_nat (length (map (fun k => inl k : vertex)
      (PreReset.seeds c f which down can))) * (3 + vertex_price w)).
  { apply sum_bound. intros v Hin.
    apply in_map_iff in Hin. destruct Hin as [k [<- Hk]].
    pose proof (lookup_cost w (inl k) Hprimitive (seeds_nodes which down can k Hk)).
    lia. }
  rewrite length_map in Hcost. eapply N.le_trans; [exact Hcost|]. nia.
Qed.

Definition query_bound w :=
  seeds_bound w + roots * (4 + vertex_price w) + scope_bound w + search_bound.

(** A complete reset query is bounded by primitive seed, conversion, blocking and driver prices. *)
Theorem query_cost w which down can :
  primitive_bounds w ->
  Cost.ticks (PreReset.reset_closure_c c (PreReset.arcs c f) f which down can) <= query_bound w.
Proof.
  intro Hprimitive. rewrite PreReset.reset_closure_ticks.
  pose proof (seeds_cost w which down can Hprimitive) as Hseeds.
  pose proof (seeds_length which down can) as Hroots.
  pose proof (root_conversion_cost w which down can Hprimitive) as Hconversion.
  pose proof (scope_cost w which down can Hprimitive) as Hscope.
  pose proof (search_cost which down can) as Hsearch.
  rewrite PreReset.directed_ticks.
  change (Cost.ticks (PreReset.seeds_c c f which down can) +
    N.of_nat (length (PreReset.seeds c f which down can)) +
    Cost.ticks (Prepared.present_c (Prepared.id_of_c (PreReset.arcs c f))
      (map (fun k => inl k : vertex) (PreReset.seeds c f which down can))) +
    Cost.ticks (PreReset.scope_c c (PreReset.arcs c f) f which down can) + 0 +
    Cost.ticks (SearchRun.run_c (PreReset.directed (PreReset.arcs c f) which)
      Visitor.noop (PreReset.scope c (PreReset.arcs c f) f which down can)
      (query_ids which down can) tt) <= query_bound w).
  unfold query_bound. nia.
Qed.

Definition solve_bound w :=
  setup_bound w + phi_enumeration w + 3 * query_bound w + 3 * flags_bound w.

(** Solve has a primitive numeric bound for one setup, three indexed searches and materialisations. *)
Theorem solve_cost w :
  primitive_bounds w -> Cost.ticks (PreReset.solve_c c f) <= solve_bound w.
Proof.
  intro Hprimitive. rewrite PreReset.solve_ticks.
  pose proof (setup_cost w Hprimitive) as Hsetup.
  pose proof (phis_cost w Hprimitive) as Hphis.
  pose proof (query_cost w PreReset.Down Map.empty Map.empty Hprimitive) as Hdown.
  pose proof (flags_cost w Map.empty false
    (PreReset.reset_closure c (PreReset.arcs c f) f PreReset.Down Map.empty Map.empty)
    Hprimitive) as Hdown_flags.
  set (down := Cost.value (PreReset.flags_c c (PreReset.arcs c f)
    (FinSet.elements (PreFrg.phis f)) Map.empty false
    (PreReset.reset_closure c (PreReset.arcs c f) f PreReset.Down Map.empty Map.empty))).
  pose proof (query_cost w PreReset.Cannot down Map.empty Hprimitive) as Hcan.
  pose proof (flags_cost w Map.empty false
    (PreReset.reset_closure c (PreReset.arcs c f) f PreReset.Cannot down Map.empty)
    Hprimitive) as Hcan_flags.
  set (can := Cost.value (PreReset.flags_c c (PreReset.arcs c f)
    (FinSet.elements (PreFrg.phis f)) Map.empty false
    (PreReset.reset_closure c (PreReset.arcs c f) f PreReset.Cannot down Map.empty))).
  pose proof (query_cost w PreReset.Later down can Hprimitive) as Hlater.
  pose proof (flags_cost w can true
    (PreReset.reset_closure c (PreReset.arcs c f) f PreReset.Later down can)
    Hprimitive) as Hlater_flags.
  fold down can.
  unfold solve_bound. lia.
Qed.

End Context.

Section Uniform.
Context {X B BE N E V K G C U : Type}.
Variable contexts : X -> Pre.ctx B BE N E V K G C U.
Variable graphs : X -> PreFrg.frg B BE E U.
Variable prices : X -> BinNums.N.
Hypothesis Hlaws : forall x, Pre.laws (contexts x).
Hypothesis Hindexes : forall x,
  FinSet.wf (PreFrg.phi_encoding (contexts x)) (PreFrg.phis (graphs x)) /\
  Map.wf (PreFrg.link_encoding (contexts x)) (PreFrg.operands (graphs x)) /\
  FinSet.wf (PreFrg.phi_encoding (contexts x)) (PreFrg.unsafe (graphs x)).
Hypothesis Hprimitives : forall x, primitive_bounds (contexts x) (graphs x) (prices x).

(** One constant bounds solve uniformly while contexts, index inventories and primitive prices vary. *)
Theorem solve_bigO :
  bigO (fun x => solve_bound (contexts x) (graphs x) (prices x))
    (fun x => Cost.ticks (PreReset.solve_c (contexts x) (graphs x))).
Proof.
  exists 1. intro x.
  destruct (Hindexes x) as [Hphi [Hlinks Hunsafe]].
  pose proof (solve_cost (contexts x) (graphs x) (Hlaws x) Hphi Hlinks Hunsafe
    (prices x) (Hprimitives x)) as Hcost.
  lia.
Qed.

End Uniform.

End PreResetCost.
