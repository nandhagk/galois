(** * Raw-input support for PRE finalization

    These proofs bound finalization from its raw graph, trie and order inputs, including
    persistent scopes and generated argument rows. For example, visiting a point twice
    charges both visits while every saved version still comes from the original support.
    Builds on: AnalysesAuditPrePlan and AnalysesAuditSourceAdequacy. *)

From Stdlib Require Import Arith Bool Decimal List PArith ZArith Lia.
From Galois.Analyses Require Import AnalysesAuditPrePlan AnalysesAuditSourceAdequacy
  AnalysesAvailable AnalysesSsaLiveQuery AnalysesSsaPre AnalysesSsaPreGraph.
From Galois.Collections Require Import CollectionsAuditCost CollectionsEncoding CollectionsFinSet
  CollectionsMap CollectionsTrie.
From Galois.Graph Require Import GraphCore GraphDominators GraphPrepare.
From Galois.Views Require Import ViewsGraph ViewsSsaPoints.
Import List.ListNotations.

(** * Collection and compositional support *)

(** This invariant ranges over positions, so it also covers malformed stored keys. *)
Definition pre_support_map {K V} (P : V -> Prop) (table : Map.t K V) : Prop :=
  forall p k v, Trie.get p table = Some (k,v) -> P v.

Lemma pre_support_empty K V (P : V -> Prop) : pre_support_map P (@Map.empty K V).
Proof.
  intros p k v Hget. unfold Map.empty in Hget.
  rewrite Trie.get_empty in Hget. discriminate.
Qed.

Lemma pre_support_set K V (EK : encoding K) (P : V -> Prop) table key value :
  pre_support_map P table -> P value -> pre_support_map P (Map.set EK key value table).
Proof.
  intros Htable Hvalue p k v Hget. unfold Map.set in Hget.
  destruct (Pos.eq_dec (encode EK key) p) as [Hequal|Hdifferent].
  - subst p. rewrite Trie.get_set_same in Hget. inversion Hget; subst v. exact Hvalue.
  - rewrite Trie.get_set_other in Hget by exact Hdifferent. eapply Htable; exact Hget.
Qed.

Lemma pre_support_get K V (EK : encoding K) (P : V -> Prop) table key value :
  pre_support_map P table -> Map.get EK key table = Some value -> P value.
Proof.
  intros Htable. unfold Map.get, Map.code_get.
  destruct (Trie.get (encode EK key) table) as [[stored actual]|] eqn:Hget;
    cbn; intro Hequal; try discriminate.
  inversion Hequal; subst actual. eapply Htable; exact Hget.
Qed.

Lemma pre_support_elements K V (P : V -> Prop) (table : Map.t K V) :
  (forall row, In row (Map.elements table) -> P (snd row)) -> pre_support_map P table.
Proof.
  intros Hrows p k v Hget. apply (Hrows (k,v)).
  unfold Map.elements. apply in_map_iff. exists (p,(k,v)). split; [reflexivity|].
  apply Trie.elements_complete. exact Hget.
Qed.

Lemma pre_support_lookup_origin K V (EK : encoding K) table key (value : V) :
  Map.get EK key table = Some value -> exists stored, In (stored,value) (Map.elements table).
Proof.
  unfold Map.get, Map.code_get.
  destruct (Trie.get (encode EK key) table) as [[stored actual]|] eqn:Hget;
    cbn; intro Hequal; try discriminate.
  inversion Hequal; subst actual. exists stored.
  unfold Map.elements. apply in_map_iff. exists (encode EK key,(stored,value)).
  split; [reflexivity|]. apply Trie.elements_complete. exact Hget.
Qed.

Lemma pre_support_max A (weight : A -> nat) xs x :
  In x xs -> weight x <= fold_right Nat.max 0 (map weight xs).
Proof.
  induction xs as [|first rest IH]; cbn; intro Hin; [contradiction|].
  destruct Hin as [Hequal|Hin].
  - subst first. apply Nat.le_max_l.
  - eapply Nat.le_trans; [apply IH; exact Hin|apply Nat.le_max_r].
Qed.

Lemma pre_support_flat_length A B (f : A -> list B) xs x :
  In x xs -> length (f x) <= length (flat_map f xs).
Proof.
  induction xs as [|first rest IH]; cbn; intro Hin; [contradiction|].
  rewrite length_app. destruct Hin as [Hequal|Hin]; [subst; lia|].
  specialize (IH Hin). lia.
Qed.

Lemma pre_support_elements_length K V (table : Map.t K V) :
  length (Map.elements table) <= exact_trie_nodes table.
Proof.
  unfold Map.elements. rewrite length_map, <- Trie.size_elements.
  destruct table as [|node]; [cbn; lia|].
  unfold Trie.size, exact_trie_nodes.
  assert (Hcount : forall acc, Trie.count_ne node acc <= acc + exact_ne_nodes node).
  { induction node as [r IH|v|v r IH|l IH|l IHl r IHr|l IH v|l IHl v r IHr];
      intro acc; cbn [Trie.count_ne exact_ne_nodes];
      try (pose proof (IH acc)); try (pose proof (IH (S acc)));
      try (pose proof (IHl acc); pose proof (IHr (Trie.count_ne l acc)));
      try (pose proof (IHl acc); pose proof (IHr (S (Trie.count_ne l acc)))); lia. }
  specialize (Hcount 0). lia.
Qed.

Lemma pre_support_pair_size A B (EA : encoding A) (EB : encoding B) a b :
  Pos.size_nat (encode (pair_encoding EA EB) (a,b)) =
    1 + 2 * (Pos.size_nat (encode EA a) + Pos.size_nat (encode EB b)).
Proof.
  change (Pos.size_nat (stream_positive
    (emit_code (encode EA a) (emit_code (encode EB b) []))) =
    1 + 2 * (Pos.size_nat (encode EA a) + Pos.size_nat (encode EB b))).
  rewrite source_stream_size, !source_emit_length. cbn [length]. lia.
Qed.

Lemma pre_support_positive_bits p : audit_z_bits (Z.pos p) = Pos.size_nat p.
Proof.
  assert (Hsize : forall q, Pos.to_nat (Pos.size q) = Pos.size_nat q).
  { induction q as [q IH|q IH|]; cbn [Pos.size Pos.size_nat];
      rewrite ?Pos2Nat.inj_succ, ?IH; reflexivity. }
  unfold audit_z_bits. destruct p as [p|p|];
    cbn [Z.abs Z.log2 Z.to_nat Pos.size_nat];
    rewrite ?Hsize; reflexivity.
Qed.

Lemma pre_support_get_cost Call K V (inject : exact_map_call K V -> Call) EK body key table :
  exact_units (exact_get inject EK body key table) =
    194 + 34 * Pos.size_nat (encode EK key) + body key.
Proof.
  unfold exact_get, exact_encode, exact_bind, exact_call, audit_encoding_weight,
    audit_get_weight, audit_key_bits_weight. cbn. lia.
Qed.

Lemma pre_support_set_cost Call K V (inject : exact_map_call K V -> Call) EK body key value table :
  exact_units (exact_set inject EK body key value table) =
    194 + 67 * Pos.size_nat (encode EK key) + body key.
Proof.
  unfold exact_set, exact_encode, exact_bind, exact_call, audit_encoding_weight,
    audit_set_weight, audit_key_bits_weight. cbn. lia.
Qed.

Lemma pre_support_append Call A site (xs ys : list A) :
  @exact_value Call _ (exact_append site xs ys) = xs ++ ys /\
  exact_units (@exact_append Call A site xs ys) = 128 + 192 * length xs.
Proof.
  split; [apply exact_append_erases|].
  induction xs as [|x rest IH]; cbn [exact_append exact_case exact_bind exact_return
    exact_units length]; lia.
Qed.

(** A state invariant is preserved at every occurrence, with no uniqueness requirement. *)
Lemma pre_support_fold Call A State site (step : State -> A -> exact_counted Call State)
    (P : State -> Prop) (Q : A -> Prop) cost xs state :
  P state -> Forall Q xs ->
  (forall state x, P state -> Q x ->
    P (exact_value (step state x)) /\ exact_units (step state x) <= cost) ->
  P (exact_value (exact_fold_left site step xs state)) /\
  exact_units (exact_fold_left site step xs state) <= 128 + length xs * (128 + cost).
Proof.
  revert state. induction xs as [|x rest IH]; intros state Hstate Hxs Hstep;
    cbn [exact_fold_left exact_case exact_return exact_bind exact_value exact_units length].
  - split; [exact Hstate|lia].
  - inversion Hxs as [|? ? Hx Hrest]; subst.
    destruct (Hstep state x Hstate Hx) as [Hnext Hcost].
    destruct (IH _ Hnext Hrest Hstep) as [Hfinal Htail]. split; [exact Hfinal|nia].
Qed.

(** The flat-map charge includes copying every actual callback result into its suffix. *)
Lemma pre_support_flat Call A B site (f : A -> exact_counted Call (list B))
    (P : A -> Prop) (Q : B -> Prop) xs cost width :
  Forall P xs ->
  (forall x, P x -> Forall Q (exact_value (f x)) /\
    length (exact_value (f x)) <= width /\ exact_units (f x) <= cost) ->
  Forall Q (exact_value (exact_flat_map site f xs)) /\
  length (exact_value (exact_flat_map site f xs)) <= length xs * width /\
  exact_units (exact_flat_map site f xs) <=
    128 + length xs * (320 + cost + 256 * width).
Proof.
  intros Hxs Hf. induction Hxs as [|x rest Hx Hrest IH].
  - cbn [exact_flat_map exact_case exact_return exact_value exact_units].
    split; [constructor|]. cbn. lia.
  - destruct (Hf x Hx) as [Hout [Hlength Hcost]].
    destruct IH as [Htail [Htail_length Htail_cost]].
    cbn [exact_flat_map exact_case exact_bind exact_value exact_units].
    destruct (pre_support_append Call B site (exact_value (f x))
      (exact_value (exact_flat_map site f rest))) as [Hvalue Happend].
    rewrite Hvalue, Happend, length_app. split.
    + apply Forall_app. split; assumption.
    + split; cbn [length]; nia.
Qed.

(** * The exact raw support used by the public budget *)

Lemma pre_support_project Call Key Value site (xs : list (Key * Value)) :
  exact_value (@exact_map Call _ _ site (fun row => exact_return site (fst row)) xs) =
    map fst xs /\
  exact_units (@exact_map Call _ _ site (fun row => exact_return site (fst row)) xs) =
    128 + 320 * length xs.
Proof.
  split; [apply exact_map_erases|].
  induction xs as [|x rest IH];
    cbn [exact_map exact_bind exact_case exact_return exact_units length]; lia.
Qed.

Lemma pre_support_coefficient : 128 * 4096 <= Nat.of_num_uint 16777216%uint.
Proof.
  apply Nat.leb_le. vm_compute. reflexivity.
Qed.

Lemma pre_support_scale c d x y : c * x * (d * y) = (c * d) * x * y.
Proof.
  ring.
Qed.

Lemma pre_support_whole_arithmetic g h nv no cp ca ci cl :
  1 <= g -> 4096 <= h -> nv <= g -> no <= g ->
  cp <= 16 * g ^ 2 * h -> ca <= 16 * g ^ 2 * h ->
  ci <= 128 + nv * (128 + 2 * h) ->
  cl <= 128 + no * (128 + 70 * g * h) ->
  cp + 64 + (ca + 64 + (ci + 64 + (cl + 64 + 64))) <= 128 * g ^ 2 * h.
Proof.
  intros Hg Hh Hnv Hno Hcp Hca Hci Hcl.
  assert (Hinitial : ci <= 4 * g * h).
  { eapply Nat.le_trans; [exact Hci|].
    pose proof (Nat.mul_le_mono_r _ _ (128 + 2 * h) Hnv). nia. }
  assert (Hloop : cl <= 72 * g ^ 2 * h).
  { eapply Nat.le_trans; [exact Hcl|].
    assert (Hcoefficient : 128 + 70 * g * h <= 71 * g * h) by nia.
    pose proof (Nat.mul_le_mono _ _ _ _ Hno Hcoefficient).
    cbn [Nat.pow]. nia. }
  clear Hnv Hno Hci Hcl.
  assert (Hpadding : 320 + 4 * g * h <= 24 * g ^ 2 * h).
  { cbn [Nat.pow]. nia. }
  cbn [Nat.pow] in *. nia.
Qed.

Lemma pre_support_set_enumeration Call Key (inject : exact_map_call Key unit -> Call) table :
  exact_value (exact_set_elements inject table) = FinSet.elements table /\
  exact_units (exact_set_elements inject table) <=
    257 + 32 * (Datatypes.S (exact_trie_nodes table)) ^ 2 +
      328 * exact_trie_nodes table.
Proof.
  unfold exact_set_elements.
  cbn [exact_bind exact_elements exact_call exact_value exact_units].
  destruct (pre_support_project Call Key unit 5 (Map.elements table)) as [Hvalue Hcost].
  rewrite Hvalue, Hcost. split; [reflexivity|].
  pose proof (pre_support_elements_length _ _ table). lia.
Qed.

(** Inserting one row adds one occurrence even when the point or payload repeats. *)
Lemma pre_support_row_set Key Value (EK : encoding Key) (P : Value -> Prop)
    rows key value count :
  pre_support_map (fun xs => Forall P xs /\ length xs <= count) rows -> P value ->
  pre_support_map (fun xs => Forall P xs /\ length xs <= Datatypes.S count)
    (Map.set EK key (value ::
      match Map.get EK key rows with
      | Some xs =>
        xs
      | None =>
        []
      end)
      rows).
Proof.
  intros Hrows Hvalue. apply pre_support_set.
  - intros p k xs Hget. destruct (Hrows p k xs Hget) as [Hall Hlength].
    split; [exact Hall|lia].
  - destruct (Map.get EK key rows) as [xs|] eqn:Hget; cbn [length].
    + destruct (pre_support_get _ _ EK _ _ _ _ Hrows Hget) as [Hall Hlength].
      split; [constructor; assumption|lia].
    + split; [constructor; [exact Hvalue|constructor]|lia].
Qed.

Lemma pre_support_row_lookup Key Value (EK : encoding Key) (P : Value -> Prop)
    rows key count :
  pre_support_map (fun xs => Forall P xs /\ length xs <= count) rows ->
  let xs :=
    match Map.get EK key rows with
    | Some xs =>
      xs
    | None =>
      []
    end in
  Forall P xs /\ length xs <= count.
Proof.
  intro Hrows. destruct (Map.get EK key rows) as [xs|] eqn:Hget.
  - exact (pre_support_get _ _ EK _ rows key xs Hrows Hget).
  - cbn. split; [constructor|lia].
Qed.

(** The row bound grows with processed occurrences, independently of collisions. *)
Lemma pre_support_row_fold Call Key Value (EK : encoding Key) site
    (step : Map.t Key (list Value) -> Key * Value -> exact_counted Call (Map.t Key (list Value)))
    (P : Key * Value -> Prop) (Q : Value -> Prop) cost items :
  Forall P items ->
  (forall rows item, P item -> Q (snd item) /\
    exact_value (step rows item) = Map.set EK (fst item)
      (snd item ::
        match Map.get EK (fst item) rows with
        | Some xs =>
          xs
        | None =>
          []
        end) rows /\
    exact_units (step rows item) <= cost) ->
  forall rows count,
  pre_support_map (fun xs => Forall Q xs /\ length xs <= count) rows ->
  pre_support_map (fun xs => Forall Q xs /\ length xs <= count + length items)
    (exact_value (exact_fold_left site step items rows)) /\
  exact_units (exact_fold_left site step items rows) <= 128 + length items * (128 + cost).
Proof.
  intros Hitems Hstep. induction Hitems as [|item rest Hitem Hrest IH];
    intros rows count Hrows.
  - cbn [exact_fold_left exact_case exact_return exact_value exact_units length].
    split; [now rewrite Nat.add_0_r|lia].
  - destruct (Hstep rows item Hitem) as [Hvalue [Hequal Hcost]].
    assert (Hnext : pre_support_map
      (fun xs => Forall Q xs /\ length xs <= Datatypes.S count) (exact_value (step rows item))).
    { rewrite Hequal. apply pre_support_row_set; assumption. }
    destruct (IH _ _ Hnext) as [Hfinal Htail].
    cbn [exact_fold_left exact_case exact_bind exact_units exact_value length]. split.
    + replace (count + Datatypes.S (length rest)) with
        (Datatypes.S count + length rest) by lia. exact Hfinal.
    + nia.
Qed.

Section PreFinalizeOrderBound.

Context {S O B BE N E V K C U : Type}
  (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
  (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
  (block_body : B -> nat) (block_edge_body : BE -> nat) (point_body : N -> nat)
  (edge_body : E -> nat) (expr_body : U -> nat).

Section RawInputs.

Variables (f : factored_redundancy_graph B BE E U) (facts : ssapre_facts B U)
  (tree : dom_tree N)
  (points : prepared EN (live_graph (point_model (pre_ssa_points a)))) (order : list N).

Let pg := live_graph (point_model (pre_ssa_points a)).

Let eg := cfg (gkview (pre_genkill (pre_expression a))).

Let keys := FinSet.elements (frg_phi_index f).

Let links := Map.elements (frg_phi_operands f).

Let definitions := frg_versions f ++ map snd (Map.elements (frg_occurrence_index f)) ++
  map (fun row => frg_operand_version (snd row)) links.

Let blocks := Graph.nodes (block_graph (pre_ssa_points a)) ++ map fst keys ++
  map (fun row => fst (fst (fst row))) links ++
  flat_map (fun d =>
    match d with
    | FrPhi b _ =>
      [b]
    | _ =>
      []
    end) definitions.

Let edges := edges_of pg ++ flat_map snd (Map.elements (out_index points)) ++
  map (parameter_edge (pre_ssa_points a)) blocks ++
  flat_map (fun d =>
    match d with
    | FrFresh e _ =>
      [e]
    | _ =>
      []
    end) definitions.

Let exprs := map frg_version_expr definitions ++ map snd keys ++
  flat_map (fun row => let '(((b,u),be),_) := row in
    u ::
      match pre_phi_translate a be u with
      | Some value =>
        [value]
      | None =>
        []
      end) links ++
  flat_map (fun e =>
    match pre_recomputed (pre_expression a) e with
    | Some u =>
      [u]
    | None =>
      []
    end) edges.

Let block_edges := map (fun row => snd (fst row)) links ++
  flat_map (fun e =>
    match block_edge_of (pre_ssa_points a) e with
    | Some be =>
      [be]
    | None =>
      []
    end) edges.

Let nodes := Graph.nodes pg ++ Graph.entries pg ++ Graph.entries eg ++ order ++
  flat_map (fun row => [fst row;snd row]) (Map.elements (idom tree)) ++
  flat_map (fun e => [Graph.source pg e;Graph.target pg e;Graph.target eg e]) edges.

Let width := fold_right Nat.max 0
    (map (fun b => block_body b + Pos.size_nat (encode EB b)) blocks) +
  fold_right Nat.max 0
    (map (fun be => block_edge_body be + Pos.size_nat (encode EBE be)) block_edges) +
  fold_right Nat.max 0
    (map (fun n => point_body n + Pos.size_nat (encode EN n)) nodes) +
  fold_right Nat.max 0
    (map (fun e => edge_body e + Pos.size_nat (encode EE e)) edges) +
  fold_right Nat.max 0
    (map (fun u => expr_body u + Pos.size_nat (encode EU u)) exprs) +
  fold_right Nat.max 0 (map (fun row => Pos.size_nat (snd row))
    (Map.elements (tin tree) ++ Map.elements (tout tree))).

Let w := Datatypes.S width.

Let g := 1 + length order + length blocks + length block_edges + length nodes +
  length edges + length exprs + length definitions + length keys + length links +
  exact_trie_nodes (frg_occurrence_index f) + exact_trie_nodes (frg_phi_operands f) +
  exact_trie_nodes (frg_phi_index f) + exact_trie_nodes (idom tree) +
  exact_trie_nodes (tin tree) + exact_trie_nodes (tout tree) + exact_trie_nodes (out_index points).

Let GoodB b := In b blocks.

Let GoodBE be := In be block_edges.

Let GoodN n := In n nodes.

Let GoodE e := In e edges.

Let GoodU u := In u exprs.

Let GoodD d := GoodU (frg_version_expr d) /\
  match d with
  | FrPhi b _ =>
    GoodB b
  | FrFresh e _ =>
    GoodE e
  | _ =>
    True
  end.

Let GoodV v := GoodU (pre_version_expr v) /\
  match v with
  | PreInitial _ =>
    True
  | PreComputed e _ | PreInserted e _ | PreMerged e _ =>
    GoodE e
  end.

Let ScopeGood := @pre_support_map (frg_version B E U) (pre_version E U) GoodV.

Let PlanGood (plan : pre_plan E U) :=
  pre_support_map GoodV (pre_reload_versions plan) /\
  pre_support_map GoodV (pre_phi_versions plan).

Let GoodKey (key : B * U) := GoodB (fst key) /\ GoodU (snd key).

Let GoodArg (arg : pre_finalize_argument B BE E U) :=
  GoodKey (pre_arg_block arg,pre_arg_expression arg) /\ GoodE (pre_arg_point_edge arg) /\
  GoodD (frg_operand_version (pre_arg_operand arg)) /\
  forall value, pre_phi_translate a (pre_arg_block_edge arg) (pre_arg_expression arg) =
    Some value -> GoodU value.

Lemma pre_support_dimensions :
  1 <= g /\ 1 <= w /\ length order <= g /\ length keys <= g /\ length links <= g /\
  length definitions <= g /\ length edges <= g /\ length nodes <= g /\
  exact_trie_nodes (frg_phi_index f) <= g /\
  exact_trie_nodes (frg_phi_operands f) <= g.
Proof.
  unfold g, w. repeat split; lia.
Qed.

Lemma pre_support_block_width b : GoodB b -> block_body b + Pos.size_nat (encode EB b) <= w.
Proof.
  intro Hin. pose proof (pre_support_max _
    (fun b => block_body b + Pos.size_nat (encode EB b)) blocks b Hin) as Hmax. cbn beta in Hmax.
  unfold w, width. lia.
Qed.

Lemma pre_support_block_edge_width be :
  GoodBE be -> block_edge_body be + Pos.size_nat (encode EBE be) <= w.
Proof.
  intro Hin. pose proof (pre_support_max _
    (fun be => block_edge_body be + Pos.size_nat (encode EBE be)) block_edges be Hin) as Hmax.
  cbn beta in Hmax.
  unfold w, width. lia.
Qed.

Lemma pre_support_point_width n : GoodN n -> point_body n + Pos.size_nat (encode EN n) <= w.
Proof.
  intro Hin. pose proof (pre_support_max _
    (fun n => point_body n + Pos.size_nat (encode EN n)) nodes n Hin) as Hmax. cbn beta in Hmax.
  unfold w, width. lia.
Qed.

Lemma pre_support_edge_width e : GoodE e -> edge_body e + Pos.size_nat (encode EE e) <= w.
Proof.
  intro Hin. pose proof (pre_support_max _
    (fun e => edge_body e + Pos.size_nat (encode EE e)) edges e Hin) as Hmax. cbn beta in Hmax.
  unfold w, width. lia.
Qed.

Lemma pre_support_expr_width u : GoodU u -> expr_body u + Pos.size_nat (encode EU u) <= w.
Proof.
  intro Hin. pose proof (pre_support_max _
    (fun u => expr_body u + Pos.size_nat (encode EU u)) exprs u Hin) as Hmax. cbn beta in Hmax.
  unfold w, width. lia.
Qed.

Lemma pre_support_definition d : In d definitions -> GoodD d.
Proof.
  intro Hin. split.
  - unfold GoodU, exprs. apply in_or_app. left. apply in_map. exact Hin.
  - destruct d as [u|u|e u|b u]; cbn; try exact I.
    + unfold GoodE, edges. repeat (apply in_or_app; right).
      apply in_flat_map. exists (FrFresh e u). split; [exact Hin|cbn; auto].
    + unfold GoodB, blocks. repeat (apply in_or_app; right).
      apply in_flat_map. exists (FrPhi b u). split; [exact Hin|cbn; auto].
Qed.

Lemma pre_support_keys key : In key keys -> GoodKey key.
Proof.
  intro Hin. split.
  - unfold GoodB, blocks. apply in_or_app. right. apply in_or_app. left.
    apply in_map. exact Hin.
  - unfold GoodU, exprs. apply in_or_app. right. apply in_or_app. left.
    apply in_map. exact Hin.
Qed.

Lemma pre_support_parameter b : GoodB b -> GoodE (parameter_edge (pre_ssa_points a) b).
Proof.
  intro Hin. unfold GoodE, edges. apply in_or_app. right. apply in_or_app. right.
  apply in_or_app. left. apply in_map. exact Hin.
Qed.

Lemma pre_support_endpoints e : GoodE e ->
  GoodN (Graph.source pg e) /\ GoodN (Graph.target pg e) /\ GoodN (Graph.target eg e).
Proof.
  intro Hin. unfold GoodN, nodes.
  assert (Hrow : forall n, In n [Graph.source pg e;Graph.target pg e;Graph.target eg e] ->
    In n (flat_map (fun e => [Graph.source pg e;Graph.target pg e;Graph.target eg e]) edges)).
  { intros n Hn. apply in_flat_map. exists e. auto. }
  repeat split; repeat (apply in_or_app; right); apply Hrow; cbn; auto.
Qed.

Lemma pre_support_recomputed e u :
  GoodE e -> pre_recomputed (pre_expression a) e = Some u -> GoodU u.
Proof.
  intros Hin Hresult. unfold GoodU, exprs. repeat (apply in_or_app; right).
  apply in_flat_map. exists e. split; [exact Hin|]. rewrite Hresult. cbn. auto.
Qed.

Lemma pre_support_occurrence e d : Map.get EE e (frg_occurrence_index f) = Some d -> GoodD d.
Proof.
  intro Hget. destruct (pre_support_lookup_origin _ _ EE _ _ _ Hget) as [stored Hin].
  apply pre_support_definition. unfold definitions. apply in_or_app. right.
  apply in_or_app. left. apply in_map_iff. exists (stored,d). auto.
Qed.

Lemma pre_support_parent n parent : Map.get EN n (idom tree) = Some parent -> GoodN parent.
Proof.
  intro Hget. destruct (pre_support_lookup_origin _ _ EN _ _ _ Hget) as [stored Hin].
  unfold GoodN, nodes. do 4 (apply in_or_app; right). apply in_or_app. left.
  apply in_flat_map. exists (stored,parent). split; [exact Hin|cbn; auto].
Qed.

Lemma pre_support_time table n p :
  (table = tin tree \/ table = tout tree) -> Map.get EN n table = Some p -> Pos.size_nat p <= w.
Proof.
  intros Htable Hget.
  destruct (pre_support_lookup_origin _ _ EN _ _ _ Hget) as [stored Hin].
  assert (Hrow : In (stored,p) (Map.elements (tin tree) ++ Map.elements (tout tree))).
  { destruct Htable as [Hequal|Hequal]; subst table; apply in_or_app; auto. }
  pose proof (pre_support_max _ (fun row : N * positive => Pos.size_nat (snd row))
    _ (stored,p) Hrow). cbn [snd] in *. unfold w, width. lia.
Qed.

Lemma pre_support_out n es : Map.get EN n (out_index points) = Some es ->
  Forall GoodE es /\ length es <= g.
Proof.
  intro Hget. destruct (pre_support_lookup_origin _ _ EN _ _ _ Hget) as [stored Hin].
  assert (Hlength := pre_support_flat_length _ _ snd _ (stored,es) Hin).
  cbn [snd] in Hlength. unfold g, edges in *. rewrite !length_app in *. split; [|lia].
  apply Forall_forall. intros e He. unfold GoodE, edges.
  apply in_or_app. right. apply in_or_app. left.
  apply in_flat_map. exists (stored,es). auto.
Qed.

(** * Scalar bounds for the actual helper bodies *)

Let h := 4096 * w.

Lemma pre_support_positive : 1 <= w /\ 4096 <= h /\ 1 <= g.
Proof.
  unfold h, w, g. repeat split; lia.
Qed.

Lemma pre_support_base_get Call Key Value (inject : exact_map_call Key Value -> Call)
    EK body key table :
  body key + Pos.size_nat (encode EK key) <= w ->
  exact_units (exact_get inject EK body key table) <= h.
Proof.
  intro Hkey. rewrite pre_support_get_cost. unfold h.
  pose proof pre_support_positive as [Hw _]. nia.
Qed.

Lemma pre_support_base_set Call Key Value (inject : exact_map_call Key Value -> Call)
    EK body key value table :
  body key + Pos.size_nat (encode EK key) <= w ->
  exact_units (exact_set inject EK body key value table) <= h.
Proof.
  intro Hkey. rewrite pre_support_set_cost. unfold h.
  pose proof pre_support_positive as [Hw _]. nia.
Qed.

Lemma pre_support_flag_cost Call Value (inject : exact_map_call (B * U) Value -> Call)
    key table : GoodKey key ->
  exact_units (exact_get inject (pair_encoding EB EU)
    (pre_flag_body EB EU block_body expr_body) key table) <= h.
Proof.
  destruct key as [b u]. intros [Hb Hu].
  pose proof (pre_support_block_width b Hb). pose proof (pre_support_expr_width u Hu).
  rewrite pre_support_get_cost. unfold pre_flag_body. cbn [fst snd].
  rewrite pre_support_pair_size. unfold h. pose proof pre_support_positive as [Hw _]. nia.
Qed.

Lemma pre_support_scope_cost Call Value (inject : exact_map_call (frg_version B E U) Value -> Call)
    d table : GoodD d ->
  exact_units (exact_get inject (frg_version_encoding EB EE EU)
    (pre_scope_body EB EE EU block_body edge_body expr_body) d table) <= h /\
  forall value, exact_units (exact_set inject (frg_version_encoding EB EE EU)
    (pre_scope_body EB EE EU block_body edge_body expr_body) d value table) <= h.
Proof.
  intros [Hu Hd].
  pose proof (pre_support_expr_width (frg_version_expr d) Hu) as Hexpr.
  pose proof pre_support_positive as [Hw _].
  split; [rewrite pre_support_get_cost|intro value; rewrite pre_support_set_cost];
    unfold pre_scope_body; destruct d as [u|u|e u|b u];
    cbn [frg_version_expr] in Hexpr;
    cbn [frg_version_encoding AnalysesSsaPreGraph.frg_version_key encode sum_encoding
      Pos.size_nat];
    try rewrite pre_support_pair_size;
    try (pose proof (pre_support_edge_width e Hd));
    try (pose proof (pre_support_block_width b Hd)); unfold h; nia.
Qed.

Lemma pre_support_phi_cost Call (inject : exact_map_call ((E * E) * U) (pre_version E U) -> Call)
    parameter incoming u version table : GoodE parameter -> GoodE incoming -> GoodU u ->
  exact_units (exact_set inject (pair_encoding (pair_encoding EE EE) EU)
    (pre_phi_body EE EU edge_body expr_body) ((parameter,incoming),u) version table) <= h.
Proof.
  intros Hp Hi Hu. pose proof (pre_support_edge_width parameter Hp).
  pose proof (pre_support_edge_width incoming Hi). pose proof (pre_support_expr_width u Hu).
  rewrite pre_support_set_cost. unfold pre_phi_body. cbn [fst snd].
  rewrite !pre_support_pair_size. unfold h. pose proof pre_support_positive as [Hw _]. nia.
Qed.

Lemma pre_support_will key : GoodKey key ->
  exact_units (pre_will_counted (BE:=BE) (N:=N) (E:=E)
    EB EU block_body expr_body facts key) <= 3 * h.
Proof.
  intro Hkey.
  pose proof (pre_support_flag_cost _ _ (@PfFlags B BE N E U) key
    (ssapre_can_available facts) Hkey).
  pose proof (pre_support_flag_cost _ _ (@PfFlags B BE N E U) key
    (ssapre_later facts) Hkey).
  unfold pre_will_counted, pre_flag_get_counted.
  cbn [exact_bind exact_case exact_return exact_units].
  pose proof pre_support_positive as [_ [Hh _]]. lia.
Qed.

Lemma pre_support_insert operand : GoodD (frg_operand_version operand) ->
  exact_units (pre_insert_operand_counted (BE:=BE) (N:=N)
    EB EU block_body expr_body facts operand) <= 4 * h.
Proof.
  intros [Hu Hd]. unfold pre_insert_operand_counted.
  destruct (frg_operand_version operand) as [u|u|e u|b u] eqn:Hversion;
    cbn [exact_case exact_return exact_bind exact_units].
  - pose proof pre_support_positive as [_ [Hh _]]. lia.
  - pose proof pre_support_positive as [_ [Hh _]]. lia.
  - pose proof pre_support_positive as [_ [Hh _]]. lia.
  - pose proof (pre_support_will (b,u) (conj Hd Hu)).
    pose proof pre_support_positive as [_ [Hh _]]. lia.
Qed.

Lemma pre_support_dominates d n : GoodN d -> GoodN n ->
  exact_units (pre_dominates_counted (B:=B) (BE:=BE) (E:=E) (U:=U)
    EN point_body tree d n) <= 8 * h.
Proof.
  intros Hd Hn.
  pose proof (pre_support_point_width d Hd) as Hdw.
  pose proof (pre_support_point_width n Hn) as Hnw.
  pose proof (pre_support_base_get _ _ _ (@PfDom B BE N E U) EN point_body d (tin tree) Hdw).
  pose proof (pre_support_base_get _ _ _ (@PfDom B BE N E U) EN point_body n (tin tree) Hnw).
  pose proof (pre_support_base_get _ _ _ (@PfDom B BE N E U) EN point_body d (tout tree) Hdw).
  pose proof (pre_support_base_get _ _ _ (@PfDom B BE N E U) EN point_body n (tout tree) Hnw).
  unfold pre_dominates_counted.
  cbn [exact_bind exact_get exact_encode exact_call exact_value exact_units] in *.
  fold (Map.get EN d (tin tree)) (Map.get EN n (tin tree))
    (Map.get EN d (tout tree)) (Map.get EN n (tout tree)).
  destruct (Map.get EN d (tin tree)) as [x|] eqn:Hx;
    [|cbn [exact_case exact_return exact_bind exact_units]; unfold h; lia].
  cbn [exact_case exact_bind exact_get exact_encode exact_call exact_value exact_units].
  fold (Map.get EN n (tin tree)).
  destruct (Map.get EN n (tin tree)) as [y|] eqn:Hy;
    [|cbn [exact_case exact_return exact_bind exact_units]; unfold h; lia].
  cbn [exact_case exact_bind exact_get exact_encode exact_call exact_value exact_units].
  fold (Map.get EN d (tout tree)).
  destruct (Map.get EN d (tout tree)) as [z|] eqn:Hz;
    [|cbn [exact_case exact_return exact_bind exact_units]; unfold h; lia].
  cbn [exact_case exact_bind exact_get exact_encode exact_call exact_value exact_units].
  fold (Map.get EN n (tout tree)).
  destruct (Map.get EN n (tout tree)) as [v|] eqn:Hv;
    cbn [exact_case exact_return exact_bind exact_call exact_units].
  - pose proof (pre_support_time _ d x (or_introl eq_refl) Hx).
    pose proof (pre_support_time _ n y (or_introl eq_refl) Hy).
    pose proof (pre_support_time _ d z (or_intror eq_refl) Hz).
    pose proof (pre_support_time _ n v (or_intror eq_refl) Hv).
    unfold audit_binary_weight. rewrite !pre_support_positive_bits.
    unfold h. pose proof pre_support_positive as [Hw _]. nia.
  - unfold h. pose proof pre_support_positive as [Hw _]. nia.
Qed.

Lemma pre_support_version_point version : GoodV version ->
  (forall n, exact_value (pre_version_point_counted a version) = Some n -> GoodN n) /\
  exact_units (pre_version_point_counted a version) <= 256.
Proof.
  intros [Hu He]. destruct version as [u|e u|e u|e u];
    cbn [pre_version_point_counted exact_case exact_bind exact_return exact_call exact_units
      exact_value]; split; try lia; intros n Hpoint.
  - apply nth_error_In in Hpoint. unfold GoodN, nodes.
    do 2 (apply in_or_app; right). apply in_or_app. left. exact Hpoint.
  - inversion Hpoint; subst n. exact (proj2 (proj2 (pre_support_endpoints e He))).
  - inversion Hpoint; subst n. exact (proj2 (proj2 (pre_support_endpoints e He))).
  - inversion Hpoint; subst n. exact (proj2 (proj2 (pre_support_endpoints e He))).
Qed.

(** Availability retains the actual saved version and checks both expression identities. *)
Lemma pre_support_available scope definition u n :
  ScopeGood scope -> GoodD definition -> GoodU u -> GoodN n ->
  (forall version, exact_value (pre_available_counted EB EN EE EU a block_body point_body
    edge_body expr_body tree scope definition u n) = Some version -> GoodV version) /\
  exact_units (pre_available_counted EB EN EE EU a block_body point_body edge_body expr_body
    tree scope definition u n) <= 16 * h.
Proof.
  intros Hscope Hd Hu Hn.
  pose proof (proj1 (pre_support_scope_cost _ _ (@PfScope B BE N E U)
    definition scope Hd)) as Hlookup.
  pose proof pre_support_positive as [Hw [Hh Hg]].
  unfold pre_available_counted.
  cbn [exact_bind exact_value exact_units]. rewrite exact_get_erases.
  destruct (Map.get (frg_version_encoding EB EE EU) definition scope)
    as [saved|] eqn:Hsaved.
  - assert (Hversion : GoodV saved).
    { eapply pre_support_get; [exact Hscope|exact Hsaved]. }
    pose proof (pre_support_expr_width (pre_version_expr saved) (proj1 Hversion)) as Hsw.
    pose proof (pre_support_expr_width u Hu) as Huw.
    cbn [exact_case exact_bind exact_encode exact_call exact_value exact_units].
    destruct (Pos.eqb (encode EU (pre_version_expr saved)) (encode EU u)) eqn:Hsame;
      cbn [exact_case exact_bind exact_return exact_value exact_units].
    + destruct (pre_support_version_point saved Hversion) as [Hpoint Hpoint_cost].
      destruct (exact_value (pre_version_point_counted a saved)) as [q|] eqn:Hq;
        cbn [exact_case exact_bind exact_return exact_value exact_units].
      * pose proof (pre_support_dominates q n (Hpoint q eq_refl) Hn) as Hdom.
        split.
        -- intros version Hequal.
           destruct (exact_value (pre_dominates_counted (B:=B) (BE:=BE) (E:=E) (U:=U)
             EN point_body tree q n)); inversion Hequal; subst; exact Hversion.
        -- unfold audit_encoding_weight, audit_binary_weight.
           rewrite !pre_support_positive_bits. unfold h in *. nia.
      * split; [intros version Hequal; discriminate|].
        unfold audit_encoding_weight, audit_binary_weight.
        rewrite !pre_support_positive_bits. unfold h in *. nia.
    + split; [intros version Hequal; discriminate|].
      unfold audit_encoding_weight, audit_binary_weight.
      rewrite !pre_support_positive_bits. unfold h in *. nia.
  - cbn [exact_case exact_return exact_value exact_units].
    split; [intros version Hequal; discriminate|]. lia.
Qed.

Lemma pre_support_select plan parameter incoming u version :
  PlanGood plan -> GoodE parameter -> GoodE incoming -> GoodU u -> GoodV version ->
  PlanGood (exact_value (pre_select_counted (B:=B) (BE:=BE) (N:=N)
    EE EU edge_body expr_body plan parameter incoming u version)) /\
  exact_units (pre_select_counted (B:=B) (BE:=BE) (N:=N)
    EE EU edge_body expr_body plan parameter incoming u version) <= 2 * h.
Proof.
  intros [Hreload Hphi] Hp Hi Hu Hv.
  pose proof (pre_support_phi_cost _ (@PfPhi B BE N E U)
    parameter incoming u version (pre_phi_versions plan) Hp Hi Hu) as Hcost.
  unfold pre_select_counted.
  cbn [exact_bind exact_return exact_value exact_units pre_reload_versions pre_phi_versions].
  rewrite exact_set_erases. split.
  - split; [exact Hreload|]. apply pre_support_set; assumption.
  - pose proof pre_support_positive as [_ [Hh _]]. lia.
Qed.

Lemma pre_support_define scope key : ScopeGood scope -> GoodKey key ->
  ScopeGood (exact_value (pre_define_phi_counted EB EE EU a block_body edge_body expr_body
    scope key)) /\
  exact_units (pre_define_phi_counted EB EE EU a block_body edge_body expr_body scope key) <= 2 * h.
Proof.
  destruct key as [b u]. intros Hscope [Hb Hu].
  assert (Hd : GoodD (FrPhi b u)) by (split; assumption).
  pose proof (proj2 (pre_support_scope_cost _ _ (@PfScope B BE N E U)
    (FrPhi b u) scope Hd) (PreMerged (parameter_edge (pre_ssa_points a) b) u)) as Hcost.
  unfold pre_define_phi_counted.
  cbn [fst snd exact_bind exact_call exact_value exact_units]. rewrite exact_set_erases.
  split.
  - apply pre_support_set; [exact Hscope|]. split; [exact Hu|].
    apply pre_support_parameter. exact Hb.
  - pose proof pre_support_positive as [_ [Hh _]]. lia.
Qed.

Lemma pre_support_initial :
  ScopeGood (exact_value (pre_initial_scope_counted EB EE EU a block_body edge_body expr_body
    (frg_versions f))) /\
  exact_units (pre_initial_scope_counted EB EE EU a block_body edge_body expr_body
    (frg_versions f)) <= 128 + length (frg_versions f) * (128 + 2 * h).
Proof.
  unfold pre_initial_scope_counted. apply pre_support_fold with (Q:=GoodD).
  - apply pre_support_empty.
  - apply Forall_forall. intros d Hd. apply pre_support_definition.
    unfold definitions. apply in_or_app. left. exact Hd.
  - intros scope d Hscope [Hu Hd]. destruct d as [u|u|e u|b u];
      cbn [exact_case exact_bind exact_call exact_return exact_value exact_units];
      try (split; [exact Hscope|pose proof pre_support_positive as [_ [Hh _]]; lia]).
    assert (Hinitial : GoodD (FrInitial u)) by (split; [exact Hu|exact I]).
    pose proof (proj2 (pre_support_scope_cost _ _ (@PfScope B BE N E U)
      (FrInitial u) scope Hinitial) (PreInitial u)) as Hcost.
    destruct (pre_initial_available a u);
      cbn [exact_case exact_return exact_units exact_value].
    + rewrite exact_set_erases. split.
      * apply pre_support_set; [exact Hscope|]. split; [exact Hu|exact I].
      * pose proof pre_support_positive as [_ [Hh _]]. lia.
    + split; [exact Hscope|pose proof pre_support_positive as [_ [Hh _]]; lia].
Qed.

(** Each occurrence either reuses a supported version or saves its own supported computation. *)
Lemma pre_support_occurrence_step scope plan edge :
  ScopeGood scope -> PlanGood plan -> GoodE edge ->
  let run := pre_occurrence_counted EB EN EE EU a block_body point_body edge_body expr_body
    f tree (scope,plan) edge in
  (ScopeGood (fst (exact_value run)) /\ PlanGood (snd (exact_value run))) /\
  exact_units run <= 20 * h.
Proof.
  intros Hscope Hplan He. cbv zeta.
  pose proof pre_support_positive as [Hw [Hh Hg]].
  pose proof (pre_support_base_get _ _ _ (@PfOccurrence B BE N E U)
    EE edge_body edge (frg_occurrence_index f) (pre_support_edge_width edge He)) as Hlookup.
  unfold pre_occurrence_counted.
  fold pg.
  cbn [exact_bind exact_call exact_case exact_return exact_value exact_units fst snd].
  destruct (pre_recomputed (pre_expression a) edge) as [u|] eqn:Hu;
    cbn [exact_bind exact_call exact_case exact_return exact_value exact_units fst snd].
  - rewrite exact_get_erases.
    destruct (Map.get EE edge (frg_occurrence_index f)) as [d|] eqn:Hd;
      cbn [exact_bind exact_call exact_case exact_return exact_value exact_units fst snd].
    + assert (Hdefinition := pre_support_occurrence edge d Hd).
      assert (Hexpression := pre_support_recomputed edge u He Hu).
      destruct (pre_total_pure (pre_expression a) u);
        cbn [exact_bind exact_call exact_case exact_return exact_value exact_units fst snd].
      * pose proof (pre_support_available scope d u (Graph.source pg edge)
          Hscope Hdefinition Hexpression (proj1 (pre_support_endpoints edge He)))
          as [Havailable Hcost].
        destruct (exact_value (pre_available_counted EB EN EE EU a block_body point_body
          edge_body expr_body tree scope d u (Graph.source pg edge))) as [version|] eqn:Hfound;
          cbn [exact_bind exact_case exact_return exact_value exact_units fst snd].
        -- pose proof (pre_support_base_set _ _ _ (@PfReload B BE N E U)
             EE edge_body edge version (pre_reload_versions plan)
             (pre_support_edge_width edge He)) as Hset.
           rewrite exact_set_erases. split; [|lia]. split; [exact Hscope|].
           split; cbn [pre_reload_versions pre_phi_versions]; [|exact (proj2 Hplan)].
           apply pre_support_set; [exact (proj1 Hplan)|]. apply Havailable. reflexivity.
        -- pose proof (proj2 (pre_support_scope_cost _ _ (@PfScope B BE N E U)
             d scope Hdefinition) (PreComputed edge u)) as Hset.
           rewrite exact_set_erases. split; [|lia]. split; [|exact Hplan].
           apply pre_support_set; [exact Hscope|]. split; assumption.
      * split; [auto|lia].
    + split; [auto|lia].
  - split; [auto|lia].
Qed.

(** Argument selection preserves both plan version maps on every translation branch. *)
Lemma pre_support_argument scope plan argument :
  ScopeGood scope -> PlanGood plan -> GoodArg argument ->
  PlanGood (exact_value (pre_argument_counted EB EN EE EU a block_body point_body edge_body
    expr_body facts tree scope plan argument)) /\
  exact_units (pre_argument_counted EB EN EE EU a block_body point_body edge_body expr_body
    facts tree scope plan argument) <= 32 * h.
Proof.
  intros Hscope Hplan [Hkey [Hedge [Hdefinition Htranslate]]].
  pose proof pre_support_positive as [Hw [Hh Hg]].
  pose proof (pre_support_will _ Hkey) as Hwill.
  pose proof (pre_support_insert (pre_arg_operand argument) Hdefinition) as Hinsert.
  assert (Hparameter : GoodE (parameter_edge (pre_ssa_points a) (pre_arg_block argument))).
  { apply pre_support_parameter. exact (proj1 Hkey). }
  unfold pre_argument_counted.
  fold pg.
  cbn [exact_bind exact_call exact_value exact_units].
  destruct (exact_value (pre_will_counted (BE:=BE) (N:=N) (E:=E)
    EB EU block_body expr_body facts (pre_arg_block argument,pre_arg_expression argument)));
    cbn [exact_case exact_bind exact_call exact_return exact_value exact_units];
    [|split; [exact Hplan|lia]].
  destruct (pre_phi_translate a (pre_arg_block_edge argument) (pre_arg_expression argument))
    as [value|] eqn:Htranslated;
    cbn [exact_case exact_bind exact_call exact_return exact_value exact_units];
    [|split; [exact Hplan|lia]].
  assert (Hvalue := Htranslate value eq_refl).
  destruct (exact_value (pre_insert_operand_counted (BE:=BE) (N:=N)
    EB EU block_body expr_body facts (pre_arg_operand argument)));
    cbn [exact_case exact_bind exact_call exact_return exact_value exact_units].
  - destruct (pre_total_pure (pre_expression a) value &&
      negb (kill (pre_genkill (pre_expression a)) (pre_arg_point_edge argument) value));
      cbn [exact_case exact_return exact_value exact_units].
    + destruct (pre_support_select plan _ _ _ (PreInserted (pre_arg_point_edge argument) value)
        Hplan Hparameter Hedge (proj2 Hkey) (conj Hvalue Hedge)) as [Hnext Hcost].
      cbn [fst snd] in Hnext, Hcost.
      split; [exact Hnext|lia].
    + split; [exact Hplan|lia].
  - destruct (pre_support_available scope _ value (Graph.source pg (pre_arg_point_edge argument))
      Hscope Hdefinition Hvalue (proj1 (pre_support_endpoints _ Hedge))) as [Hsaved Hcost].
    destruct (exact_value (pre_available_counted EB EN EE EU a block_body point_body edge_body
      expr_body tree scope (frg_operand_version (pre_arg_operand argument)) value
      (Graph.source pg (pre_arg_point_edge argument)))) as [saved|] eqn:Hfound;
      cbn [exact_case exact_return exact_value exact_units].
    + destruct (pre_support_select plan _ _ _ saved Hplan Hparameter Hedge (proj2 Hkey)
        (Hsaved saved eq_refl)) as [Hnext Hselect].
      cbn [fst snd] in Hnext, Hselect. split; [exact Hnext|lia].
    + split; [exact Hplan|lia].
Qed.

(** * Generated indexes and row growth *)

Lemma pre_support_graph_nodes :
  Forall GoodN (Graph.nodes pg) /\ length (Graph.nodes pg) <= g.
Proof.
  split.
  - apply Forall_forall. intros n Hin. unfold GoodN, nodes. apply in_or_app. auto.
  - unfold g, nodes. rewrite !length_app. lia.
Qed.

Lemma pre_support_graph_out n : In n (Graph.nodes pg) ->
  Forall GoodE (Graph.out pg n) /\ length (Graph.out pg n) <= g.
Proof.
  intro Hn. pose proof (pre_support_flat_length _ _ (Graph.out pg) (Graph.nodes pg) n Hn)
    as Hlength.
  split.
  - apply Forall_forall. intros e He. unfold GoodE, edges. apply in_or_app. left.
    unfold edges_of. apply in_flat_map. exists n. auto.
  - unfold g, edges, edges_of. rewrite !length_app. lia.
Qed.

Lemma pre_support_block_edge e be :
  GoodE e -> block_edge_of (pre_ssa_points a) e = Some be -> GoodBE be.
Proof.
  intros He Hbe. unfold GoodBE, block_edges. apply in_or_app. right.
  apply in_flat_map. exists e. split; [exact He|]. rewrite Hbe. cbn. auto.
Qed.

Let graph_edge_scan : exact_counted (pre_rows_call B BE N E U) (list E) :=
  exact_flat_map 1300 (fun n =>
    exact_call (PrOut n (Graph.out pg n)) 0 (Graph.out pg n)) (Graph.nodes pg).

Lemma pre_support_graph_edge_scan : Forall GoodE (exact_value graph_edge_scan) /\
  length (exact_value graph_edge_scan) <= g ^ 2 /\
  exact_units graph_edge_scan <= 768 * g ^ 2.
Proof.
  pose proof pre_support_positive as [Hw [Hh Hg]].
  unfold graph_edge_scan. destruct (pre_support_flat (pre_rows_call B BE N E U) _ _ 1300
    (fun n => exact_call (PrOut n (Graph.out pg n)) 0 (Graph.out pg n))
    (fun n => In n (Graph.nodes pg)) GoodE (Graph.nodes pg) 64 g)
    as [Hvalues [Hlength Hcost]].
  - apply Forall_forall. auto.
  - intros n Hn. destruct (pre_support_graph_out n Hn) as [Hall Hlen].
    cbn [exact_call exact_value exact_units]. auto.
  - split; [exact Hvalues|]. pose proof (proj2 pre_support_graph_nodes).
    cbn [Nat.pow] in *. split; nia.
Qed.

Let index_row_item (edge : E) : exact_counted (pre_rows_call B BE N E U) (list (BE * E)) :=
  exact_bind 1302 (exact_call (PrBlockEdge edge (block_edge_of (pre_ssa_points a) edge)) 0
    (block_edge_of (pre_ssa_points a) edge)) (fun found =>
    match found with
    | None =>
      exact_case 1303 (exact_return 1303 [])
    | Some be =>
      exact_case 1304 (exact_return 1304 [(be,edge)])
    end).

Lemma pre_support_index_row_scan :
  let scan := exact_flat_map 1301 index_row_item (exact_value graph_edge_scan) in
  Forall (fun row => GoodBE (fst row) /\ GoodE (snd row)) (exact_value scan) /\
  length (exact_value scan) <= g ^ 2 /\ exact_units scan <= 1024 * g ^ 2.
Proof.
  cbv zeta. pose proof pre_support_positive as [Hw [Hh Hg]].
  destruct pre_support_graph_edge_scan as [Hedges [Hlength Hcost]].
  destruct (pre_support_flat (pre_rows_call B BE N E U) _ _ 1301 index_row_item GoodE
    (fun row : BE * E => GoodBE (fst row) /\ GoodE (snd row))
    (exact_value graph_edge_scan) 256 1 Hedges) as [Hall [Hlen Hwork]].
  - intros edge He. unfold index_row_item. cbn [exact_bind exact_call exact_value exact_units].
    destruct (block_edge_of (pre_ssa_points a) edge) as [be|] eqn:Hbe;
      cbn [exact_case exact_return exact_value exact_units length].
    + split.
      * constructor; [split; [eapply pre_support_block_edge; eassumption|exact He]|constructor].
      * split; lia.
    + split; [constructor|]. split; lia.
  - split; [exact Hall|]. cbn [Nat.pow] in *. split; nia.
Qed.

Let index_rows_scan := exact_flat_map 1301 index_row_item (exact_value graph_edge_scan).

Lemma pre_support_index_build :
  let build := exact_fold_left 1305 (fun table row =>
    exact_set (@PrPointIndex B BE N E U) EBE block_edge_body (fst row) (snd row) table)
    (exact_value index_rows_scan) Map.empty in
  pre_support_map GoodE (exact_value build) /\
  exact_units build <= 128 + g ^ 2 * (128 + h).
Proof.
  cbv zeta. destruct pre_support_index_row_scan as [Hall [Hlen Hcost]].
  fold index_rows_scan in Hall, Hlen, Hcost.
  destruct (pre_support_fold (pre_rows_call B BE N E U) _ _ 1305
    (fun table row => exact_set PrPointIndex EBE block_edge_body (fst row) (snd row) table)
    (pre_support_map GoodE) (fun row : BE * E => GoodBE (fst row) /\ GoodE (snd row)) h
    (exact_value index_rows_scan) Map.empty (pre_support_empty _ _ GoodE) Hall)
    as [Hvalues Hwork].
  - intros table [be edge] Htable [Hbe He]. cbn [fst snd] in *.
    split; [rewrite exact_set_erases; apply pre_support_set; assumption|].
    apply pre_support_base_set. apply pre_support_block_edge_width. exact Hbe.
  - split; [exact Hvalues|]. cbn [Nat.pow] in *. nia.
Qed.

Lemma pre_support_point_index :
  pre_support_map GoodE (exact_value (pre_point_index_counted EBE a block_edge_body)) /\
  exact_units (pre_point_index_counted EBE a block_edge_body) <= 4 * g ^ 2 * h.
Proof.
  pose proof pre_support_positive as [Hw [Hh Hg]].
  destruct pre_support_graph_edge_scan as [_ [Hlength Hscan]].
  destruct pre_support_index_row_scan as [_ [Hrows_length Hrows]].
  fold index_rows_scan in Hrows_length, Hrows.
  destruct pre_support_index_build as [Hvalues Hcost].
  unfold pre_point_index_counted. fold pg graph_edge_scan.
  cbn [exact_bind exact_value exact_units]. fold index_row_item index_rows_scan.
  split; [exact Hvalues|]. cbn [Nat.pow] in *. nia.
Qed.

Let GoodPhiItem (item : N * (B * U)) := GoodN (fst item) /\ GoodKey (snd item).

Let GoodArgItem (item : N * pre_finalize_argument B BE E U) :=
  GoodN (fst item) /\ GoodArg (snd item).

Lemma pre_support_add_phi rows item : GoodPhiItem item ->
  GoodKey (snd item) /\
  exact_value (pre_add_phi_row_counted (BE:=BE) (E:=E) EN point_body rows item) =
    Map.set EN (fst item)
      (snd item ::
        match Map.get EN (fst item) rows with
        | Some xs =>
          xs
        | None =>
          []
        end) rows /\
  exact_units (pre_add_phi_row_counted (BE:=BE) (E:=E) EN point_body rows item) <= 3 * h.
Proof.
  intros [Hn Hkey].
  pose proof (pre_support_base_get _ _ _ (fun c => PrFinalize (@PfNodeRows B BE N E U c))
    EN point_body (fst item) rows (pre_support_point_width _ Hn)) as Hget.
  assert (Hset : forall xs, exact_units (exact_set
    (fun c => PrFinalize (@PfNodeRows B BE N E U c)) EN point_body (fst item) xs rows) <= h).
  { intro xs. apply pre_support_base_set. apply pre_support_point_width. exact Hn. }
  unfold pre_add_phi_row_counted.
  cbn [exact_bind exact_case exact_return exact_value exact_units].
  rewrite exact_get_erases, exact_set_erases. split; [exact Hkey|].
  split; [reflexivity|]. specialize (Hset (snd item ::
    match Map.get EN (fst item) rows with
    | Some xs =>
      xs
    | None =>
      []
    end)).
  pose proof pre_support_positive as [_ [Hh _]]. lia.
Qed.

Lemma pre_support_add_argument rows item : GoodArgItem item ->
  GoodArg (snd item) /\
  exact_value (pre_add_argument_row_counted EN point_body rows item) =
    Map.set EN (fst item)
      (snd item ::
        match Map.get EN (fst item) rows with
        | Some xs =>
          xs
        | None =>
          []
        end) rows /\
  exact_units (pre_add_argument_row_counted EN point_body rows item) <= 3 * h.
Proof.
  intros [Hn Harg].
  pose proof (pre_support_base_get _ _ _ (fun c => PrFinalize (@PfArguments B BE N E U c))
    EN point_body (fst item) rows (pre_support_point_width _ Hn)) as Hget.
  assert (Hset : forall xs, exact_units (exact_set
    (fun c => PrFinalize (@PfArguments B BE N E U c)) EN point_body (fst item) xs rows) <= h).
  { intro xs. apply pre_support_base_set. apply pre_support_point_width. exact Hn. }
  unfold pre_add_argument_row_counted.
  cbn [exact_bind exact_case exact_return exact_value exact_units].
  rewrite exact_get_erases, exact_set_erases. split; [exact Harg|].
  split; [reflexivity|]. specialize (Hset (snd item ::
    match Map.get EN (fst item) rows with
    | Some xs =>
      xs
    | None =>
      []
    end)).
  pose proof pre_support_positive as [_ [Hh _]]. lia.
Qed.

Let phi_item (key : B * U) : exact_counted (pre_rows_call B BE N E U) (list (N * (B * U))) :=
  exact_bind 1322 (exact_lift PrFinalize
    (pre_will_counted (BE:=BE) (N:=N) (E:=E) EB EU block_body expr_body facts key)) (fun will =>
    if will then exact_case 1323
      (let edge := parameter_edge (pre_ssa_points a) (fst key) in
      exact_bind 1324 (exact_call (PrFinalize (PfParameter (fst key) edge)) 0 edge) (fun edge =>
      let point := Graph.target pg edge in
      exact_bind 1325 (exact_call (PrFinalize (PfTarget edge point)) 0 point)
        (fun point => exact_return 1326 [(point,key)])))
    else exact_case 1327 (exact_return 1327 [])).

Lemma pre_support_phi_items key : In key keys ->
  Forall GoodPhiItem (exact_value (phi_item key)) /\ length (exact_value (phi_item key)) <= 1 /\
    exact_units (phi_item key) <= 4 * h.
Proof.
  intro Hkey. unfold phi_item. pose proof (pre_support_keys key Hkey) as Hgood.
  pose proof (pre_support_will key Hgood) as Hwill.
  pose proof pre_support_positive as [_ [Hh _]].
  cbn [exact_bind exact_lift exact_value exact_units].
  destruct (exact_value (pre_will_counted (BE:=BE) (N:=N) (E:=E)
    EB EU block_body expr_body facts key));
    cbn [exact_bind exact_case exact_call exact_return exact_value exact_units length].
  - split.
    + constructor; [split|constructor].
      * exact (proj1 (proj2 (pre_support_endpoints _ (pre_support_parameter _ (proj1 Hgood))))).
      * exact Hgood.
    + split; lia.
  - split; [constructor|]. split; lia.
Qed.

Lemma pre_support_phi_rows :
  pre_support_map (fun xs => Forall GoodKey xs /\ length xs <= g)
    (exact_value (pre_phi_rows_counted EB EN EU a block_body point_body expr_body f facts)) /\
  exact_units (pre_phi_rows_counted EB EN EU a block_body point_body expr_body f facts)
    <= 16 * g ^ 2 * h.
Proof.
  pose proof pre_support_positive as [Hw [Hh Hg]].
  destruct pre_support_dimensions as [_ [_ [_ [Hkeys [_ [_ [_ [_ [Hnodes _]]]]]]]]].
  destruct (pre_support_set_enumeration (pre_rows_call B BE N E U) (B * U)%type PrPhis
    (frg_phi_index f)) as [Henum Henum_cost].
  unfold pre_phi_rows_counted. fold pg.
  cbn [exact_bind exact_value exact_units]. rewrite Henum. fold keys.
  fold phi_item. set (scan := exact_flat_map 1321 phi_item keys).
  assert (Hscan : Forall GoodPhiItem (exact_value scan) /\
    length (exact_value scan) <= g /\ exact_units scan <= 6 * g * h).
  { unfold scan. destruct (pre_support_flat (pre_rows_call B BE N E U) _ _ 1321 phi_item
      (fun key => In key keys) GoodPhiItem keys (4 * h) 1) as [Hall [Hlen Hcost]].
    - apply Forall_forall. auto.
    - exact pre_support_phi_items.
    - split; [exact Hall|]. split; nia. }
  destruct Hscan as [Hitems [Hlength Hscan]].
  destruct (pre_support_row_fold _ _ _ EN 1328
    (pre_add_phi_row_counted (BE:=BE) (E:=E) EN point_body) GoodPhiItem GoodKey (3 * h)
    (exact_value scan) Hitems pre_support_add_phi Map.empty 0 (pre_support_empty _ _ _))
    as [Hrows Hcost].
  split.
  - intros p k xs Hget. destruct (Hrows p k xs Hget) as [Hall Hlen].
    split; [exact Hall|lia].
  - cbn [Nat.pow] in *. nia.
Qed.

Lemma pre_support_link b u be operand : In (((b,u),be),operand) links ->
  GoodKey (b,u) /\ GoodBE be /\ GoodD (frg_operand_version operand) /\
  (forall value, pre_phi_translate a be u = Some value -> GoodU value).
Proof.
  intro Hin. split.
  - split.
    + unfold GoodB, blocks. apply in_or_app. right. apply in_or_app. right.
      apply in_or_app. left. apply in_map_iff. exists (((b,u),be),operand). auto.
    + unfold GoodU, exprs. do 2 (apply in_or_app; right). apply in_or_app. left.
      apply in_flat_map. exists (((b,u),be),operand). split; [exact Hin|cbn; auto].
  - split.
    + unfold GoodBE, block_edges. apply in_or_app. left. apply in_map_iff.
      exists (((b,u),be),operand). auto.
    + split.
      * apply pre_support_definition. unfold definitions. do 2 (apply in_or_app; right).
        apply in_map_iff. exists (((b,u),be),operand). auto.
      * intros value Hvalue. unfold GoodU, exprs. do 2 (apply in_or_app; right).
        apply in_or_app. left. apply in_flat_map. exists (((b,u),be),operand).
        split; [exact Hin|]. cbn. rewrite Hvalue. cbn. auto.
Qed.

Let argument_item (table : Map.t BE E) (link : ((B * U) * BE) * frg_operand B E U)
    : exact_counted (pre_rows_call B BE N E U)
      (list (N * pre_finalize_argument B BE E U)) :=
  let '(((b,u),be),op) := link in
  exact_bind 1343 (exact_get PrPointIndex EBE block_edge_body be table) (fun found =>
    match found with
    | None =>
      exact_case 1344 (exact_return 1344 [])
    | Some edge =>
      exact_case 1345
        (let point := Graph.source pg edge in
        exact_bind 1346 (exact_call (PrFinalize (PfSource edge point)) 0 point)
          (fun point => exact_return 1347 [(point,PreFinalizeArgument b u be edge op)]))
    end).

Lemma pre_support_argument_items table link : pre_support_map GoodE table -> In link links ->
  Forall GoodArgItem (exact_value (argument_item table link)) /\
  length (exact_value (argument_item table link)) <= 1 /\
  exact_units (argument_item table link) <= 2 * h.
Proof.
  destruct link as [[[b u] be] operand]. intros Htable Hin.
  destruct (pre_support_link b u be operand Hin) as [Hkey [Hbe [Hd Htranslate]]].
  pose proof (pre_support_base_get _ _ _ (@PrPointIndex B BE N E U)
    EBE block_edge_body be table (pre_support_block_edge_width be Hbe)) as Hget_cost.
  pose proof pre_support_positive as [_ [Hh _]].
  unfold argument_item. cbn [exact_bind exact_value exact_units]. rewrite exact_get_erases.
  destruct (Map.get EBE be table) as [edge|] eqn:Hget;
    cbn [exact_bind exact_case exact_call exact_return exact_units exact_value length].
  - assert (He : GoodE edge) by (eapply pre_support_get; eassumption).
    split.
    + constructor; [|constructor]. split.
      * exact (proj1 (pre_support_endpoints edge He)).
      * split; [exact Hkey|]. split; [exact He|]. split; assumption.
    + split; lia.
  - split; [constructor|]. split; lia.
Qed.

Lemma pre_support_argument_rows :
  pre_support_map (fun xs => Forall GoodArg xs /\ length xs <= g)
    (exact_value (pre_argument_rows_counted EBE EN a block_edge_body point_body f)) /\
  exact_units (pre_argument_rows_counted EBE EN a block_edge_body point_body f)
    <= 16 * g ^ 2 * h.
Proof.
  pose proof pre_support_positive as [Hw [Hh Hg]].
  destruct pre_support_dimensions as [_ [_ [_ [_ [Hlinks [_ [_ [_ [_ Hnodes]]]]]]]]].
  destruct pre_support_point_index as [Hindex Hindex_cost].
  set (index := exact_value (pre_point_index_counted EBE a block_edge_body)) in *.
  set (scan := exact_flat_map 1342 (argument_item index) links).
  assert (Hscan : Forall GoodArgItem (exact_value scan) /\
    length (exact_value scan) <= g /\ exact_units scan <= 4 * g * h).
  { unfold scan. destruct (pre_support_flat (pre_rows_call B BE N E U) _ _ 1342
      (argument_item index) (fun link => In link links) GoodArgItem links (2 * h) 1)
      as [Hall [Hlen Hcost]].
    - apply Forall_forall. auto.
    - intros link Hin. apply pre_support_argument_items; assumption.
    - split; [exact Hall|]. split; nia. }
  destruct Hscan as [Hitems [Hlen Hscan_cost]].
  destruct (pre_support_row_fold _ _ _ EN 1348
    (pre_add_argument_row_counted EN point_body) GoodArgItem GoodArg (3 * h)
    (exact_value scan) Hitems pre_support_add_argument Map.empty 0 (pre_support_empty _ _ _))
    as [Hrows Hrows_cost].
  unfold pre_argument_rows_counted. fold pg.
  cbn [exact_bind exact_elements exact_call exact_value exact_units]. fold links index.
  fold argument_item. fold scan.
  split.
  - intros p k xs Hget. destruct (Hrows p k xs Hget) as [Hall Hlength].
    split; [exact Hall|lia].
  - pose proof (pre_support_elements_length _ _ (frg_phi_operands f)) as Hlength.
    change (exact_units (pre_point_index_counted EBE a block_edge_body) + 64 +
      (exact_units (exact_elements (@PrLinks B BE N E U) (frg_phi_operands f)) + 64 +
      (exact_units scan + 64 + exact_units (exact_fold_left 1348
        (pre_add_argument_row_counted EN point_body) (exact_value scan) Map.empty))) <=
      16 * g ^ 2 * h).
    cbn [exact_elements exact_call exact_units]. fold links. fold links in Hlength.
    cbn [Nat.pow] in *. nia.
Qed.

(** * Persistent node scopes and the arbitrary ordered loop *)

Lemma pre_support_node phis arguments scope plan n :
  pre_support_map (fun xs => Forall GoodKey xs /\ length xs <= g) phis ->
  pre_support_map (fun xs => Forall GoodArg xs /\ length xs <= g) arguments ->
  ScopeGood scope -> PlanGood plan -> GoodN n ->
  let run := pre_node_counted EB EN EE EU a block_body point_body edge_body expr_body
    f facts tree points phis arguments (scope,plan) n in
  (ScopeGood (fst (exact_value run)) /\ PlanGood (snd (exact_value run))) /\
  exact_units run <= 64 * g * h.
Proof.
  intros Hphis Harguments Hscope Hplan Hn. cbv zeta.
  pose proof pre_support_positive as [Hw [Hh Hg]].
  set (ks :=
    match Map.get EN n phis with
    | Some xs =>
      xs
    | None =>
      []
    end).
  set (args :=
    match Map.get EN n arguments with
    | Some xs =>
      xs
    | None =>
      []
    end).
  set (es :=
    match Map.get EN n (out_index points) with
    | Some xs =>
      xs
    | None =>
      []
    end).
  destruct (pre_support_row_lookup _ _ EN GoodKey phis n g Hphis) as [Hkeys Hkeys_len].
  destruct (pre_support_row_lookup _ _ EN GoodArg arguments n g Harguments)
    as [Hargs Hargs_len]. fold ks in Hkeys, Hkeys_len. fold args in Hargs, Hargs_len.
  assert (Hes : Forall GoodE es /\ length es <= g).
  { unfold es. destruct (Map.get EN n (out_index points)) as [xs|] eqn:Hget.
    - apply pre_support_out with (n:=n). exact Hget.
    - cbn. split; [constructor|lia]. }
  destruct Hes as [Hedges Hedges_len].
  destruct (pre_support_fold _ _ _ 812
    (pre_define_phi_counted EB EE EU a block_body edge_body expr_body) ScopeGood GoodKey
    (2 * h) ks scope Hscope Hkeys pre_support_define) as [Hscope1 Hdefine_cost].
  set (scope1 := exact_value (exact_fold_left 812
    (pre_define_phi_counted EB EE EU a block_body edge_body expr_body) ks scope)) in *.
  destruct (pre_support_fold _ _ _ 815
    (pre_argument_counted EB EN EE EU a block_body point_body edge_body expr_body facts tree scope1)
    PlanGood GoodArg (32 * h) args plan Hplan Hargs)
    as [Hplan1 Hargument_cost].
  - intros current arg Hcurrent Harg. apply pre_support_argument; assumption.
  - set (plan1 := exact_value (exact_fold_left 815
      (pre_argument_counted EB EN EE EU a block_body point_body edge_body expr_body
        facts tree scope1) args plan)) in *.
    destruct (pre_support_fold _ _ _ 818
      (pre_occurrence_counted EB EN EE EU a block_body point_body edge_body expr_body f tree)
      (fun work => ScopeGood (fst work) /\ PlanGood (snd work)) GoodE (20 * h)
      es (scope1,plan1) (conj Hscope1 Hplan1) Hedges) as [Hfinal Hoccurrence_cost].
    + intros [current current_plan] edge [current_scope_good current_plan_good] Hedge.
      apply pre_support_occurrence_step; assumption.
    + pose proof (pre_support_point_width n Hn) as Hwidth.
      pose proof (pre_support_base_get _ _ _ (@PfNodeRows B BE N E U)
        EN point_body n phis Hwidth) as Hget_phis.
      pose proof (pre_support_base_get _ _ _ (@PfArguments B BE N E U)
        EN point_body n arguments Hwidth) as Hget_arguments.
      pose proof (pre_support_base_get _ _ _ (@PfEdges B BE N E U)
        EN point_body n (out_index points) Hwidth) as Hget_edges.
      unfold pre_node_counted.
      cbn [exact_bind exact_case exact_return exact_value exact_units].
      rewrite !exact_get_erases. fold ks args es scope1 plan1.
      split; [exact Hfinal|].
      change (exact_units (exact_get (@PfNodeRows B BE N E U) EN point_body n phis) + 64 +
        (128 + 64 + (exact_units (exact_fold_left 812
          (pre_define_phi_counted EB EE EU a block_body edge_body expr_body) ks scope) + 64 +
        (exact_units (exact_get (@PfArguments B BE N E U) EN point_body n arguments) + 64 +
        (128 + 64 + (exact_units (exact_fold_left 815
          (pre_argument_counted EB EN EE EU a block_body point_body edge_body expr_body
            facts tree scope1) args plan) + 64 +
        (exact_units (exact_get (@PfEdges B BE N E U) EN point_body n (out_index points)) + 64 +
        (128 + 64 + exact_units (exact_fold_left 818
          (pre_occurrence_counted EB EN EE EU a block_body point_body edge_body expr_body f tree)
          es (scope1,plan1))))))))) <= 64 * g * h).
      clearbody g h.
      nia.
Qed.

Let input_scope (initial : Map.t (frg_version B E U) (pre_version E U))
    (outputs : Map.t N (Map.t (frg_version B E U) (pre_version E U))) (parent : option N)
    : exact_counted (pre_finalize_call B BE N E U)
      (Map.t (frg_version B E U) (pre_version E U)) :=
  match parent with
  | None =>
    exact_case 821 (exact_return 821 initial)
  | Some parent =>
    exact_case 822 (exact_bind 823
      (exact_get PfOutputs EN point_body parent outputs)
      (fun found => exact_case 824 (exact_return 824
        (match found with
        | Some scope =>
          scope
        | None =>
          initial
        end))))
  end.

Lemma pre_support_input_scope initial outputs parent :
  ScopeGood initial -> pre_support_map ScopeGood outputs ->
  (forall p, parent = Some p -> GoodN p) ->
  ScopeGood (exact_value (input_scope initial outputs parent)) /\
  exact_units (input_scope initial outputs parent) <= 2 * h.
Proof.
  intros Hinitial Houtputs Hparent. pose proof pre_support_positive as [_ [Hh _]].
  destruct parent as [p|]; unfold input_scope;
    cbn [exact_bind exact_case exact_return exact_value exact_units].
  - rewrite exact_get_erases.
    pose proof (pre_support_base_get _ _ _ (@PfOutputs B BE N E U) EN point_body p outputs
      (pre_support_point_width p (Hparent p eq_refl))) as Hget_cost.
    destruct (Map.get EN p outputs) as [scope|] eqn:Hget; split; try lia.
    + eapply pre_support_get; [exact Houtputs|exact Hget].
    + exact Hinitial.
  - split; [exact Hinitial|lia].
Qed.

Lemma pre_support_table phis arguments initial outputs plan n :
  pre_support_map (fun xs => Forall GoodKey xs /\ length xs <= g) phis ->
  pre_support_map (fun xs => Forall GoodArg xs /\ length xs <= g) arguments ->
  ScopeGood initial -> pre_support_map ScopeGood outputs -> PlanGood plan -> GoodN n ->
  let run := pre_table_step_counted EB EN EE EU a block_body point_body edge_body expr_body
    f facts tree points phis arguments initial (outputs,plan) n in
  (pre_support_map ScopeGood (fst (exact_value run)) /\ PlanGood (snd (exact_value run))) /\
  exact_units run <= 70 * g * h.
Proof.
  intros Hphis Hargs Hinitial Houtputs Hplan Hn. cbv zeta.
  pose proof pre_support_positive as [Hw [Hh Hg]].
  set (parent := Map.get EN n (idom tree)).
  assert (Hparent : forall p, parent = Some p -> GoodN p).
  { intros p Hp. apply pre_support_parent with (n:=n). exact Hp. }
  destruct (pre_support_input_scope initial outputs parent Hinitial Houtputs Hparent)
    as [Hscope Hscope_cost].
  set (scope := exact_value (input_scope initial outputs parent)) in *.
  destruct (pre_support_node phis arguments scope plan n Hphis Hargs Hscope Hplan Hn)
    as [Hresult Hnode_cost].
  set (node_run := pre_node_counted EB EN EE EU a block_body point_body edge_body expr_body
    f facts tree points phis arguments (scope,plan) n) in *.
  destruct (exact_value node_run) as [scope1 plan1] eqn:Hnode_value.
  cbn [fst snd] in Hresult. destruct Hresult as [Hscope1 Hplan1].
  pose proof (pre_support_point_width n Hn) as Hwidth.
  pose proof (pre_support_base_get _ _ _ (@PfIdom B BE N E U) EN point_body n
    (idom tree) Hwidth) as Hget_cost.
  pose proof (pre_support_base_set _ _ _ (@PfOutputs B BE N E U) EN point_body n
    scope1 outputs Hwidth) as Hset_cost.
  unfold pre_table_step_counted.
  cbn [exact_bind exact_return exact_units exact_value]. rewrite exact_get_erases.
  fold parent. fold (input_scope initial outputs parent). fold scope node_run.
  rewrite Hnode_value. cbn [exact_bind exact_return exact_units exact_value fst snd].
  rewrite exact_set_erases. split; [|nia]. split; [|exact Hplan1].
  apply pre_support_set; assumption.
Qed.

Lemma pre_support_order_cost :
  exact_units (pre_finalize_order_counted EB EBE EN EE EU a block_body block_edge_body
    point_body edge_body expr_body f facts tree points order) <= 128 * g ^ 2 * h.
Proof.
  pose proof pre_support_positive as [Hw [Hh Hg]].
  destruct pre_support_phi_rows as [Hphis Hphis_cost].
  destruct pre_support_argument_rows as [Harguments Harguments_cost].
  destruct pre_support_initial as [Hinitial Hinitial_cost].
  set (phis := exact_value (pre_phi_rows_counted EB EN EU a block_body point_body expr_body
    f facts)) in *.
  set (arguments := exact_value (pre_argument_rows_counted EBE EN a block_edge_body
    point_body f)) in *.
  set (initial := exact_value (pre_initial_scope_counted EB EE EU a block_body edge_body
    expr_body (frg_versions f))) in *.
  assert (Horder : Forall GoodN order).
  { apply Forall_forall. intros n Hin. unfold GoodN, nodes.
    do 3 (apply in_or_app; right). apply in_or_app. left. exact Hin. }
  set (step := fun work n => exact_lift PrFinalize
    (pre_table_step_counted EB EN EE EU a block_body point_body edge_body expr_body f facts
      tree points phis arguments initial work n)).
  destruct (pre_support_fold (pre_rows_call B BE N E U) _ _ 1353 step
    (fun work => pre_support_map ScopeGood (fst work) /\ PlanGood (snd work))
    GoodN (70 * g * h) order (Map.empty,PrePlan Map.empty Map.empty Map.empty Map.empty))
    as [Hfinal Hloop_cost].
  - split; [apply pre_support_empty|]. split; apply pre_support_empty.
  - exact Horder.
  - intros [outputs plan] n [Houtputs Hplan] Hn.
    unfold step. cbn [exact_lift exact_value exact_units fst snd].
    apply pre_support_table; assumption.
  - assert (Hversions : length (frg_versions f) <= g).
    { unfold g, definitions. rewrite !length_app. lia. }
    assert (Horder_len : length order <= g) by (unfold g; lia).
    unfold pre_finalize_order_counted.
    cbn [exact_bind exact_lift exact_return exact_units exact_value].
    fold phis arguments initial step.
    change (exact_units (pre_phi_rows_counted EB EN EU a block_body point_body expr_body f facts)
      + 64 + (exact_units (pre_argument_rows_counted EBE EN a block_edge_body point_body f)
      + 64 + (exact_units (pre_initial_scope_counted EB EE EU a block_body edge_body expr_body
        (frg_versions f)) + 64 + (exact_units (exact_fold_left 1353 step order
        (Map.empty,PrePlan Map.empty Map.empty Map.empty Map.empty)) + 64 + 64))) <=
      128 * g ^ 2 * h).
    apply pre_support_whole_arithmetic with
      (nv := length (frg_versions f)) (no := length order); assumption.
Qed.

(** The actual finalizer fits the fixed raw-input budget without a well-formedness premise. *)
Theorem pre_finalize_order_bound :
  exact_units (pre_finalize_order_counted EB EBE EN EE EU a block_body block_edge_body
    point_body edge_body expr_body f facts tree points order) <=
  pre_finalize_order_input_budget EB EBE EN EE EU a block_body block_edge_body point_body
    edge_body expr_body f facts tree points order.
Proof.
  eapply Nat.le_trans; [exact pre_support_order_cost|].
  change (128 * g ^ 2 * h <= Nat.of_num_uint 16777216%uint * g ^ 32 * w ^ 16).
  pose proof pre_support_positive as [Hw [_ Hg]].
  assert (Hgpower : g ^ 2 <= g ^ 32) by (apply Nat.pow_le_mono_r; lia).
  assert (Hwpower : w <= w ^ 16).
  { replace w with (w ^ 1) at 1 by (cbn [Nat.pow]; lia).
    apply Nat.pow_le_mono_r; lia. }
  unfold h.
  eapply Nat.le_trans with (m := Nat.of_num_uint 16777216%uint * g ^ 2 * w).
  - rewrite pre_support_scale.
    apply Nat.mul_le_mono_r. apply Nat.mul_le_mono_r. exact pre_support_coefficient.
  - apply Nat.mul_le_mono; [apply Nat.mul_le_mono_l; exact Hgpower|exact Hwpower].
Qed.

End RawInputs.

End PreFinalizeOrderBound.
