(** * Interned reference preparation

    Preparation assigns dense IDs and materialises outgoing and incoming adjacency.
    For example, an absent client node has no ID and an absent ID has no adjacency.
    Builds on: GraphModel, BaseIntern, BaseMap and BaseIndex. *)

From Stdlib Require Import List Bool PArith NArith Arith Lia Permutation.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseIntern BaseIndex.
From Galois.Graph Require Import GraphModel.
Import List.ListNotations Cost.Notations.

Module Prepared.
Local Open Scope nat_scope.

(** The encoding travels with the table so all observations use the same key identity. *)
Record t (V E : Type) := Make {
  graph : Graph.t V E;
  node_enc : encoding V;
  names : Intern.t V;
  succ : Map.t positive (list (E * positive));
  pred : Map.t positive (list (E * positive));
  entry_ids : list positive;
  fuel : positive
}.
Arguments Make {V E}.
Arguments graph {V E}.
Arguments node_enc {V E}.
Arguments names {V E}.
Arguments succ {V E}.
Arguments pred {V E}.
Arguments entry_ids {V E}.
Arguments fuel {V E}.

Definition id_of_c {V E} (p : t V E) v := Intern.find_c (node_enc p) v (names p).
Definition id_of {V E} (p : t V E) v := Cost.value (id_of_c p v).
Definition name_of_c {V E} (p : t V E) i := Intern.key_of_c i (names p).
Definition name_of {V E} (p : t V E) i := Cost.value (name_of_c p i).
Definition succ_edges_c {V E} (p : t V E) i := Index.find_c positive_encoding i (succ p).
Definition succ_edges {V E} (p : t V E) i := Cost.value (succ_edges_c p i).
Definition pred_edges_c {V E} (p : t V E) i := Index.find_c positive_encoding i (pred p).
Definition pred_edges {V E} (p : t V E) i := Cost.value (pred_edges_c p i).

(** Forward lookup delegates to the table's own dictionary. *)
Theorem id_of_equation {V E} (p : t V E) v :
  id_of p v = Intern.find (node_enc p) v (names p).
Proof.
  reflexivity.
Qed.

(** Inverse lookup delegates to the table's positive-ID observation. *)
Theorem name_of_equation {V E} (p : t V E) i :
  name_of p i = Intern.key_of i (names p).
Proof.
  reflexivity.
Qed.

(** Successor lookup defaults to an empty list at an absent ID. *)
Theorem succ_edges_equation {V E} (p : t V E) i :
  succ_edges p i = Index.find positive_encoding i (succ p).
Proof.
  reflexivity.
Qed.

(** Predecessor lookup defaults to an empty list at an absent ID. *)
Theorem pred_edges_equation {V E} (p : t V E) i :
  pred_edges p i = Index.find positive_encoding i (pred p).
Proof.
  reflexivity.
Qed.

(** Reference option mapping preserves input order and drops absent endpoints. *)
Fixpoint present {A B} (f : A -> option B) (xs : list A) : list B :=
  match xs with
  | [] => []
  | x :: rest =>
    match f x with
    | None => present f rest
    | Some y => y :: present f rest
    end
  end.

Definition all_edges {V E} (g : Graph.t V E) := flat_map (Graph.out g) (Graph.nodes g).

Definition incoming {V E} enc (g : Graph.t V E) v :=
  filter (fun e => eqb enc (Graph.target g e) v) (all_edges g).

Definition tagged {V E} enc table (endpoint : E -> V) es :=
  present (fun e => option_map (fun i => (e, i)) (Intern.find enc (endpoint e) table)) es.

Definition ids {V} enc (table : Intern.t V) vs := present (fun v => Intern.find enc v table) vs.

(** Index nodes by their interned ID using public map insertion alone. *)
Fixpoint index_nodes {V A} enc (table : Intern.t V) (f : V -> A) vs : Map.t positive A :=
  match vs with
  | [] => Map.empty
  | v :: rest =>
    match Intern.find enc v table with
    | None => index_nodes enc table f rest
    | Some i => Map.set positive_encoding i (f v) (index_nodes enc table f rest)
    end
  end.

(** Present mapping retains the callback charge for every input occurrence. *)
Fixpoint present_c {A B} (f : A -> Cost.t (option B)) (xs : list A)
    : Cost.t (list B) :=
  match xs with
  | [] => Cost.ret []
  | x :: rest =>
    Cost.step ;;
    Cost.step ;;
    let* y := f x in
    let* ys := present_c f rest in
    Cost.ret (match y with None => ys | Some y => y :: ys end)
  end.

(** Costed present mapping has the same order and missing-value behavior as the reference. *)
Theorem present_c_value {A B} (f : A -> Cost.t (option B)) xs :
  Cost.value (present_c f xs) = present (fun x => Cost.value (f x)) xs.
Proof.
  induction xs as [|x rest IH]; [reflexivity|].
  cbn [present_c present]. autorewrite with galois_cost.
  rewrite IH. destruct (Cost.value (f x)); reflexivity.
Qed.

(** Flattening retains each outgoing callback and each copied edge occurrence. *)
Definition all_edges_c {V E} (g : Graph.t V E) :=
  fold_right_c (fun v tail =>
    Cost.step ;;
    let* es := Graph.out_c g v in app_c es tail) [] (Graph.nodes g).

(** Flattening observes the original node and edge order even on malformed graphs. *)
Theorem all_edges_c_value {V E} (g : Graph.t V E) :
  Cost.value (all_edges_c g) = all_edges g.
Proof.
  unfold all_edges_c, all_edges. rewrite value_fold_right_c.
  induction (Graph.nodes g) as [|v rest IH]; cbn [fold_right flat_map].
  - reflexivity.
  - autorewrite with galois_cost. rewrite IH. reflexivity.
Qed.

(** Tagging retains endpoint callbacks and the interning lookup for each edge. *)
Definition tagged_c {V E} enc table (endpoint : E -> Cost.t V) es :=
  present_c (fun e =>
    Cost.step ;;
    let* v := endpoint e in
    let* i := Intern.find_c enc v table in Cost.ret (option_map (fun i => (e, i)) i)) es.

(** Pointwise equal option observations preserve every retained occurrence and its order. *)
Theorem present_ext {A B} (f g : A -> option B) xs :
  (forall x, f x = g x) -> present f xs = present g xs.
Proof.
  intro Hfg. induction xs as [|x rest IH]; [reflexivity|].
  cbn [present]. rewrite Hfg, IH. reflexivity.
Qed.

(** Dropping absent option results cannot increase the number of input occurrences. *)
Theorem present_length {A B} (f : A -> option B) xs :
  (length (present f xs) <= length xs)%nat.
Proof.
  induction xs as [|x rest IH]; [reflexivity|].
  cbn [present]. destruct (f x); cbn [length]; lia.
Qed.

(** Tagging preserves labels, order and absent-endpoint filtering. *)
Theorem tagged_c_value {V E} enc table (endpoint : E -> Cost.t V) es :
  Cost.value (tagged_c enc table endpoint es) =
    tagged enc table (fun e => Cost.value (endpoint e)) es.
Proof.
  unfold tagged_c, tagged. rewrite present_c_value.
  apply present_ext. intro e. reflexivity.
Qed.

(** Node indexing keeps right-fold overwrite behavior and skips absent node IDs. *)
Fixpoint index_nodes_c {V A} enc (table : Intern.t V) (f : V -> Cost.t A) vs
    : Cost.t (Map.t positive A) :=
  match vs with
  | [] => Cost.ret Map.empty
  | v :: rest =>
    Cost.step ;;
    let* tail := index_nodes_c enc table f rest in
    let* i := Intern.find_c enc v table in
    match i with
    | None => Cost.ret tail
    | Some i =>
      Cost.step ;;
      let* a := f v in Map.set_c positive_encoding i a tail
    end
  end.

(** Costed node indexing returns the original raw map for arbitrary tables and callbacks. *)
Theorem index_nodes_c_value {V A} enc (table : Intern.t V) (f : V -> Cost.t A) vs :
  Cost.value (index_nodes_c enc table f vs) =
    index_nodes enc table (fun v => Cost.value (f v)) vs.
Proof.
  induction vs as [|v rest IH]; [reflexivity|].
  cbn [index_nodes_c index_nodes]. autorewrite with galois_cost.
  rewrite IH. fold (Intern.find enc v table).
  destruct (Intern.find enc v table); autorewrite with galois_cost; reflexivity.
Qed.

Local Lemma index_nodes_ext {V A} enc (table : Intern.t V) (f g : V -> A) vs :
  (forall v, f v = g v) -> index_nodes enc table f vs = index_nodes enc table g vs.
Proof.
  intro Hfg. induction vs as [|v rest IH]; [reflexivity|].
  cbn [index_nodes]. rewrite IH, Hfg. reflexivity.
Qed.

(** Root conversion preserves repeated and missing entries in the original order. *)
Definition ids_c {V} enc (table : Intern.t V) vs :=
  present_c (fun v => Intern.find_c enc v table) vs.

(** Root conversion returns precisely the successful original entry lookups. *)
Theorem ids_c_value {V} enc (table : Intern.t V) vs :
  Cost.value (ids_c enc table vs) = ids enc table vs.
Proof.
  apply present_c_value.
Qed.

(** Edge counting retains outgoing callback and list-length charges at every node. *)
Definition edge_count_c {V E} (g : Graph.t V E) :=
  fold_right_c (fun v n =>
    Cost.step ;;
    let* es := Graph.out_c g v in
    let* m := length_c es in Cost.ret (m + n)) 0 (Graph.nodes g).

(** Costed edge counting agrees on every graph, including repeated node occurrences. *)
Theorem edge_count_c_value {V E} (g : Graph.t V E) :
  Cost.value (edge_count_c g) = edge_count g.
Proof.
  unfold edge_count_c, edge_count. rewrite value_fold_right_c.
  induction (Graph.nodes g) as [|v rest IH]; cbn [fold_right]; [reflexivity|].
  autorewrite with galois_cost. rewrite IH. reflexivity.
Qed.

(** Unary-to-positive budget conversion charges every traversed natural-number successor. *)
Fixpoint budget_c (n : nat) : Cost.t positive :=
  match n with
  | O => Cost.ret 1%positive
  | S rest =>
    Cost.step ;;
    let* p := budget_c rest in Cost.ret (Pos.succ p)
  end.

(** Charged budget construction preserves the original one-more-than-input positive value. *)
Theorem budget_value n : Cost.value (budget_c n) = Pos.of_succ_nat n.
Proof.
  induction n as [|n IH]; [reflexivity|].
  cbn [budget_c]. autorewrite with galois_cost.
  rewrite IH, SuccNat2Pos.inj_succ. reflexivity.
Qed.

(** Budget construction retains its full linear unary conversion work. *)
Theorem budget_cost n : Cost.ticks (budget_c n) = N.of_nat n.
Proof.
  induction n as [|n IH]; [reflexivity|].
  cbn [budget_c]. autorewrite with galois_cost.
  rewrite IH, Nat2N.inj_succ. lia.
Qed.

(** Preparation retains all accessor, interning, indexing and list traversal charges. *)
Definition prepare_c {V E} (enc : encoding V) (g : Graph.t V E) : Cost.t (t V E) :=
  let* table := Intern.of_list_c enc (Graph.nodes g) in
  let* edges := all_edges_c g in
  let* incoming_index := Index.group_by_c enc (Graph.target_c g) edges in
  let* outgoing := index_nodes_c enc table (fun v =>
    Cost.step ;;
    let* es := Graph.out_c g v in tagged_c enc table (Graph.target_c g) es)
    (Graph.nodes g) in
  let* incoming := index_nodes_c enc table (fun v =>
    let* es := Index.find_c enc v incoming_index in
    tagged_c enc table (Graph.source_c g) es) (Graph.nodes g) in
  let* entries := ids_c enc table (Graph.entries g) in
  let* n := length_c (Graph.nodes g) in
  let* m := edge_count_c g in
  let* budget := budget_c (2 * n + m + 1) in
  Cost.ret (Make g enc table outgoing incoming entries budget).

(** The public preparation is the value projection of its single costed implementation. *)
Definition prepare {V E} (enc : encoding V) (g : Graph.t V E) : t V E :=
  Cost.value (prepare_c enc g).

(** Preparation preserves its original record values and occurrence-sensitive reference equation. *)
Theorem prepare_equation {V E} enc (g : Graph.t V E) :
  prepare enc g =
    let table := Intern.of_list enc (Graph.nodes g) in
    let incoming_index := Index.group_by enc (Graph.target g) (all_edges g) in
    Make g enc table
      (index_nodes enc table (fun v => tagged enc table (Graph.target g) (Graph.out g v))
        (Graph.nodes g))
      (index_nodes enc table (fun v => tagged enc table (Graph.source g)
        (Index.find enc v incoming_index))
        (Graph.nodes g))
      (ids enc table (Graph.entries g))
      (Pos.of_succ_nat (2 * length (Graph.nodes g) + edge_count g + 1)).
Proof.
  unfold prepare, prepare_c. autorewrite with galois_cost.
  rewrite all_edges_c_value, Index.group_by_c_value.
  change (Cost.value (Intern.of_list_c enc (Graph.nodes g))) with
    (Intern.of_list enc (Graph.nodes g)).
  rewrite !index_nodes_c_value, ids_c_value, edge_count_c_value, budget_value.
  f_equal; apply index_nodes_ext; intro v; autorewrite with galois_cost;
    rewrite tagged_c_value; reflexivity.
Qed.

(** Readiness connects IDs, domains, adjacency, duplicates and the exact reference fuel. *)
Record laws {V E} (p : t V E) : Prop := {
  encoding_valid : encoding_laws (node_enc p);
  names_wf : Intern.wf (node_enc p) (names p);
  ids_domain : forall v, In v (Graph.nodes (graph p)) <-> exists i, id_of p v = Some i;
  ids_dense : forall i, (i < Intern.next (names p))%positive <->
    exists v, id_of p v = Some i;
  ids_inverse : forall v i, id_of p v = Some i <-> name_of p i = Some v;
  succ_wf : Map.wf positive_encoding (succ p);
  pred_wf : Map.wf positive_encoding (pred p);
  succ_agrees : forall v i, id_of p v = Some i ->
    map fst (succ_edges p i) = Graph.out (graph p) v;
  succ_targets : forall i e j, In (e, j) (succ_edges p i) ->
    id_of p (Graph.target (graph p) e) = Some j;
  pred_agrees : forall v i e j, id_of p v = Some i ->
    (In (e, j) (pred_edges p i) <->
      In (Graph.source (graph p) e) (Graph.nodes (graph p)) /\
      In e (Graph.out (graph p) (Graph.source (graph p) e)) /\
      Graph.target (graph p) e = v /\ id_of p (Graph.source (graph p) e) = Some j);
  succ_domain : forall i, name_of p i = None -> succ_edges p i = [];
  pred_domain : forall i, name_of p i = None -> pred_edges p i = [];
  pred_nodup : forall i, NoDup (map fst (pred_edges p i));
  entries_agree : entry_ids p = ids (node_enc p) (names p) (Graph.entries (graph p));
  fuel_value : Pos.to_nat (fuel p) =
    2 * length (Graph.nodes (graph p)) + edge_count (graph p) + 2
}.

(** Graph invariants and prepared laws are evidence separate from computational data. *)
Definition ready {V E} (p : t V E) :=
  graph_wf (graph p) /\ (forall v, NoDup (Graph.out (graph p) v)) /\ laws p.

(** Present mapping contains exactly the successful callback results of input occurrences. *)
Theorem present_spec {A B} (f : A -> option B) xs y :
  In y (present f xs) <-> exists x, In x xs /\ f x = Some y.
Proof.
  induction xs as [|x rest IH]; cbn [present].
  - split; [contradiction|intros [a [Hfalse _]]; contradiction].
  - destruct (f x) as [b|] eqn:Hx; cbn [In]; rewrite IH.
    + split.
      * intros [->|[a [Hin Ha]]]; [exists x; auto|exists a; auto].
      * intros [a [[<-|Hin] Ha]]; [left; congruence|right; exists a; auto].
    + split.
      * intros [a [Hin Ha]]. exists a. auto.
      * intros [a [[<-|Hin] Ha]]; [congruence|exists a; auto].
Qed.

Local Lemma tagged_spec {V E} enc table (endpoint : E -> V) es e i :
  In (e, i) (tagged enc table endpoint es) <->
    In e es /\ Intern.find enc (endpoint e) table = Some i.
Proof.
  unfold tagged. rewrite present_spec. split.
  - intros [a [Hin Ha]].
    destruct (Intern.find enc (endpoint a) table) as [j|] eqn:Hfind;
      cbn in Ha; inversion Ha; subst. auto.
  - intros [Hin Hfind]. exists e. rewrite Hfind. auto.
Qed.

Local Lemma tagged_fst {V E} enc table (endpoint : E -> V) es :
  (forall e, In e es -> exists i, Intern.find enc (endpoint e) table = Some i) ->
  map fst (tagged enc table endpoint es) = es.
Proof.
  induction es as [|e rest IH]; intro Hall; [reflexivity|].
  destruct (Hall e (or_introl eq_refl)) as [i Hi].
  cbn [tagged present]. rewrite Hi. cbn.
  f_equal. apply IH. intros a Ha. apply Hall. now right.
Qed.

Local Lemma nodup_app {A} (xs ys : list A) :
  NoDup xs -> NoDup ys -> (forall x, In x xs -> ~ In x ys) -> NoDup (xs ++ ys).
Proof.
  intros Hxs Hys Hdis. induction Hxs as [|x xs Hnot Hxs IH]; cbn; [exact Hys|].
  constructor.
  - rewrite in_app_iff. intros [Hin|Hin]; [contradiction|].
    eapply Hdis; [left; reflexivity|exact Hin].
  - apply IH. intros y Hin. apply Hdis. now right.
Qed.

Local Lemma edges_nodup {V E} (g : Graph.t V E) vs :
  NoDup vs -> (forall v, NoDup (Graph.out g v)) ->
  (forall v e, In e (Graph.out g v) -> Graph.source g e = v) ->
  NoDup (flat_map (Graph.out g) vs).
Proof.
  intros Hnodes Hedges Hsource.
  induction Hnodes as [|v vs Hnot Hnodes IH]; cbn; [constructor|].
  apply nodup_app; [apply Hedges|exact IH|].
  intros e He Hin. apply in_flat_map in Hin. destruct Hin as [u [Hu Heu]].
  apply Hnot. assert (Heq : u = v) by (rewrite <- (Hsource u e Heu); auto).
  now subst u.
Qed.

Local Lemma incoming_spec {V E} enc (HE : encoding_laws enc) (g : Graph.t V E) v e :
  graph_wf g ->
  (In e (incoming enc g v) <->
    In (Graph.source g e) (Graph.nodes g) /\
    In e (Graph.out g (Graph.source g e)) /\ Graph.target g e = v).
Proof.
  intro Hwf. unfold incoming, all_edges.
  rewrite filter_In, (eqb_true_iff enc HE), in_flat_map. split.
  - intros [[u [Hu He]] Htarget].
    rewrite (out_source Hwf u e He). auto.
  - intros [Hsource [Hedge Htarget]].
    split; [exists (Graph.source g e); auto|exact Htarget].
Qed.

Local Lemma index_wf {V A} enc (table : Intern.t V) (f : V -> A) vs :
  Map.wf positive_encoding (index_nodes enc table f vs).
Proof.
  induction vs as [|v rest IH]; cbn [index_nodes].
  - apply Map.wf_empty.
  - destruct (Intern.find enc v table); [now apply Map.wf_set|exact IH].
Qed.

Local Lemma find_injective {V} enc (table : Intern.t V) a b i :
  Intern.wf enc table ->
  Intern.find enc a table = Some i -> Intern.find enc b table = Some i -> a = b.
Proof.
  intros Hwf Ha Hb.
  pose proof (Intern.key_of_find enc a i table Hwf Ha) as Hka.
  pose proof (Intern.key_of_find enc b i table Hwf Hb) as Hkb. congruence.
Qed.

Local Lemma index_at {V A} enc (table : Intern.t V) (f : V -> A) vs v i :
  Intern.wf enc table -> In v vs -> Intern.find enc v table = Some i ->
  Map.get positive_encoding i (index_nodes enc table f vs) = Some (f v).
Proof.
  intros Hwf. induction vs as [|a rest IH]; intros Hin Hv; [contradiction|].
  cbn [index_nodes]. destruct (Intern.find enc a table) as [j|] eqn:Ha.
  - destruct (Pos.eq_dec i j) as [Heq|Hne].
    + subst j. assert (Heq : a = v) by (eapply find_injective; eauto). subst a.
      apply Map.get_set_same, index_wf.
    + rewrite (Map.get_set_other positive_encoding positive_encoding_laws)
        by (try apply index_wf; exact Hne).
      apply IH; [destruct Hin as [<-|Hin]; [congruence|exact Hin]|exact Hv].
  - apply IH; [destruct Hin as [<-|Hin]; [congruence|exact Hin]|exact Hv].
Qed.

Local Lemma index_missing {V A} enc (table : Intern.t V) (f : V -> A) vs i :
  (forall v, In v vs -> Intern.find enc v table <> Some i) ->
  Map.get positive_encoding i (index_nodes enc table f vs) = None.
Proof.
  induction vs as [|v rest IH]; intro Hmissing; cbn [index_nodes].
  - apply Map.get_empty.
  - destruct (Intern.find enc v table) as [j|] eqn:Hv.
    + rewrite (Map.get_set_other positive_encoding positive_encoding_laws).
      * apply IH. intros a Ha. apply Hmissing. now right.
      * apply index_wf.
      * intro Heq. subst j. apply (Hmissing v (or_introl eq_refl)). exact Hv.
    + apply IH. intros a Ha. apply Hmissing. now right.
Qed.

Local Lemma inverse_find {V} enc (table : Intern.t V) v i :
  Intern.wf enc table ->
  (Intern.find enc v table = Some i <-> Intern.key_of i table = Some v).
Proof.
  intro Hwf. split.
  - exact (Intern.key_of_find enc v i table Hwf).
  - exact (Intern.find_key_of enc v i table Hwf).
Qed.

Local Lemma index_lookup {V A} enc (HE : encoding_laws enc) vs (f : V -> A) i :
  Map.get positive_encoding i (index_nodes enc (Intern.of_list enc vs) f vs) =
    option_map f (Intern.key_of i (Intern.of_list enc vs)).
Proof.
  pose proof (Intern.wf_of_list enc HE vs) as Hwf.
  destruct (Intern.key_of i (Intern.of_list enc vs)) as [v|] eqn:Hname.
  - cbn [option_map]. apply index_at; [exact Hwf| |].
    + apply (Intern.intern_list_spec enc HE). exists i. now apply (inverse_find enc).
    + now apply (inverse_find enc).
  - cbn [option_map]. apply index_missing. intros v Hv Hfind.
    pose proof (Intern.key_of_find enc v i _ Hwf Hfind). congruence.
Qed.

Local Lemma prepared_lookup {V E} enc (HE : encoding_laws enc) (g : Graph.t V E) i :
  succ_edges (prepare enc g) i =
    match Intern.key_of i (Intern.of_list enc (Graph.nodes g)) with
    | Some v => tagged enc (Intern.of_list enc (Graph.nodes g)) (Graph.target g) (Graph.out g v)
    | None => []
    end /\
  pred_edges (prepare enc g) i =
    match Intern.key_of i (Intern.of_list enc (Graph.nodes g)) with
    | Some v => tagged enc (Intern.of_list enc (Graph.nodes g)) (Graph.source g)
        (incoming enc g v)
    | None => []
    end.
Proof.
  rewrite succ_edges_equation, pred_edges_equation, !Index.find_equation.
  rewrite !prepare_equation. cbn [succ pred]. rewrite !index_lookup by exact HE.
  destruct (Intern.key_of i (Intern.of_list enc (Graph.nodes g))); cbn [option_map].
  - rewrite Index.find_group_by. split; reflexivity.
  - split; reflexivity.
Qed.

(** Reference preparation establishes dense IDs, exact adjacency and the traversal fuel formula. *)
Theorem prepare_ready {V E} (enc : encoding V) (HE : encoding_laws enc) (g : Graph.t V E) :
  graph_wf g -> (forall v, NoDup (Graph.out g v)) -> ready (prepare enc g).
Proof.
  intros Hwf Hnodup. rewrite prepare_equation.
  split; [exact Hwf|]. split; [exact Hnodup|].
  pose proof (prepared_lookup enc HE g) as Hlookup.
  rewrite prepare_equation in Hlookup.
  pose proof (Intern.wf_of_list enc HE (Graph.nodes g)) as Htable.
  assert (Hdomain : forall v, In v (Graph.nodes g) <->
    exists i, Intern.find enc v (Intern.of_list enc (Graph.nodes g)) = Some i).
  { apply Intern.intern_list_spec. exact HE. }
  constructor.
  - exact HE.
  - exact Htable.
  - exact Hdomain.
  - intro i. apply Intern.ids_dense. exact Htable.
  - intros v i. apply inverse_find. exact Htable.
  - apply index_wf.
  - apply index_wf.
  - intros v i Hfind.
    rewrite (proj1 (Hlookup i)).
    change (Intern.find enc v (Intern.of_list enc (Graph.nodes g)) = Some i) in Hfind.
    rewrite (Intern.key_of_find enc v i _ Htable Hfind).
    apply tagged_fst. intros e He. apply Hdomain.
    apply (out_target_in Hwf v e); [apply Hdomain; now exists i|exact He].
  - intros i e j Hin. rewrite (proj1 (Hlookup i)) in Hin.
    destruct (Intern.key_of i (Intern.of_list enc (Graph.nodes g))) as [v|];
      [apply tagged_spec in Hin; exact (proj2 Hin)|contradiction].
  - intros v i e j Hfind. rewrite (proj2 (Hlookup i)).
    change (Intern.find enc v (Intern.of_list enc (Graph.nodes g)) = Some i) in Hfind.
    rewrite (Intern.key_of_find enc v i _ Htable Hfind).
    rewrite tagged_spec, (incoming_spec enc HE g v e Hwf). tauto.
  - intros i Hname.
    change (Intern.key_of i (Intern.of_list enc (Graph.nodes g)) = None) in Hname.
    rewrite (proj1 (Hlookup i)), Hname. reflexivity.
  - intros i Hname.
    change (Intern.key_of i (Intern.of_list enc (Graph.nodes g)) = None) in Hname.
    rewrite (proj2 (Hlookup i)), Hname. reflexivity.
  - intro i. rewrite (proj2 (Hlookup i)).
    destruct (Intern.key_of i (Intern.of_list enc (Graph.nodes g))) as [v|].
    + rewrite tagged_fst.
      * apply NoDup_filter. apply edges_nodup.
        -- exact (nodes_nodup Hwf).
        -- exact Hnodup.
        -- exact (out_source Hwf).
      * intros e He. apply (incoming_spec enc HE g v e Hwf) in He.
        apply Hdomain. tauto.
    + constructor.
  - reflexivity.
  - cbn [prepare fuel graph]. rewrite SuccNat2Pos.id_succ. lia.
Qed.

(** The inverse and forward observations agree under prepared laws. *)
Theorem id_of_name_of {V E} (p : t V E) i v :
  laws p -> name_of p i = Some v -> id_of p v = Some i.
Proof.
  intros Hp. apply (ids_inverse _ Hp).
Qed.

(** Forward lookup recovers the same client name through inverse lookup. *)
Theorem name_of_id_of {V E} (p : t V E) v i :
  laws p -> id_of p v = Some i -> name_of p i = Some v.
Proof.
  intros Hp. apply (ids_inverse _ Hp).
Qed.

(** Entry IDs name exactly the entries whose forward lookup succeeds. *)
Theorem entry_ids_spec {V E} (p : t V E) i :
  laws p ->
  (In i (entry_ids p) <->
    exists v, In v (Graph.entries (graph p)) /\ id_of p v = Some i).
Proof.
  intro Hp; rewrite (entries_agree p Hp).
  unfold ids; rewrite present_spec.
  split; intros [v [Hin Hv]]; exists v; split; [exact Hin| |exact Hin|].
  - rewrite id_of_equation; exact Hv.
  - rewrite id_of_equation in Hv; exact Hv.
Qed.

(** Valid IDs denote actual nodes of the client graph. *)
Definition valid_id {V E} (p : t V E) i :=
  exists v, In v (Graph.nodes (graph p)) /\ id_of p v = Some i.

(** ID arcs are interpreted through the client graph, independently of its cached indexes. *)
Definition arc {V E} (p : t V E) u e v :=
  exists a b, In a (Graph.nodes (graph p)) /\
    id_of p a = Some u /\ id_of p b = Some v /\
    Graph.source (graph p) e = a /\ Graph.target (graph p) e = b /\
    In e (Graph.out (graph p) a).

(** Every successor pair records precisely an outgoing edge and its target ID. *)
Theorem succ_spec {V E} (p : t V E) v i e j :
  laws p -> id_of p v = Some i ->
  (In (e, j) (succ_edges p i) <->
    In e (Graph.out (graph p) v) /\ id_of p (Graph.target (graph p) e) = Some j).
Proof.
  intros Hp Hi. split.
  - intro Hin. split.
    + rewrite <- (succ_agrees p Hp v i Hi). apply in_map with (f := fst) in Hin. exact Hin.
    + exact (succ_targets p Hp i e j Hin).
  - intros [He Hj]. rewrite <- (succ_agrees p Hp v i Hi) in He.
    apply in_map_iff in He. destruct He as [[a k] [Ha Hin]]. cbn in Ha. subst a.
    pose proof (succ_targets p Hp i e k Hin). assert (k = j) by congruence.
    now subst k.
Qed.

(** Incoming and outgoing indexes describe the same labelled ID arcs. *)
Theorem adjacency_dual {V E} (p : t V E) i e j :
  ready p -> (In (e, j) (succ_edges p i) <-> In (e, i) (pred_edges p j)).
Proof.
  intros [Hwf [_ Hp]]. split.
  - intro Hin.
    destruct (name_of p i) as [v|] eqn:Hname.
    + pose proof (id_of_name_of p i v Hp Hname) as Hi.
      apply (succ_spec p v i e j Hp Hi) in Hin. destruct Hin as [He Hj].
      apply (pred_agrees p Hp (Graph.target (graph p) e) j e i Hj).
      rewrite (out_source Hwf v e He). split.
      * apply (ids_domain p Hp). now exists i.
      * auto.
    + rewrite (succ_domain p Hp i Hname) in Hin. contradiction.
  - intro Hin.
    destruct (name_of p j) as [v|] eqn:Hname.
    + pose proof (id_of_name_of p j v Hp Hname) as Hj.
      apply (pred_agrees p Hp v j e i Hj) in Hin.
      destruct Hin as [Hsource [He [Htarget Hi]]].
      apply (succ_spec p (Graph.source (graph p) e) i e j Hp Hi).
      split; [exact He|now rewrite Htarget].
    + rewrite (pred_domain p Hp j Hname) in Hin. contradiction.
Qed.

Fixpoint edge_labels_c {E} (es : list (E * positive)) : Cost.t (list E) :=
  match es with
  | [] => Cost.ret []
  | (e, _) :: rest =>
    Cost.bind Cost.step (fun _ =>
      Cost.bind (edge_labels_c rest) (fun es => Cost.ret (e :: es)))
  end.

Local Lemma edge_labels_value {E} (es : list (E * positive)) :
  Cost.value (edge_labels_c es) = map fst es.
Proof.
  induction es as [|[e i] rest IH]; cbn [edge_labels_c];
    autorewrite with galois_cost; cbn; now rewrite ?IH.
Qed.

Definition incoming_c {V E} (p : t V E) v :=
  Cost.bind (id_of_c p v) (fun id =>
    match id with
    | None => Cost.ret []
    | Some i =>
      Cost.bind (pred_edges_c p i) edge_labels_c
    end).

(** Reversed outgoing callbacks read the predecessor index and retain all lookup charges. *)
Theorem incoming_equation {V E} (p : t V E) v :
  Cost.value (incoming_c p v) =
    match id_of p v with
    | None => []
    | Some i => map fst (pred_edges p i)
    end.
Proof.
  unfold incoming_c. rewrite Cost.value_bind.
  change (Cost.value
    (match id_of p v with
    | None => Cost.ret []
    | Some i => Cost.bind (pred_edges_c p i) edge_labels_c
    end) =
    match id_of p v with
    | None => []
    | Some i => map fst (pred_edges p i)
    end).
  destruct (id_of p v); autorewrite with galois_cost;
    [apply edge_labels_value|reflexivity].
Qed.

Definition reverse_graph {V E} (p : t V E) exits :=
  Graph.reverse_with (graph p) (present (name_of p) exits) (incoming_c p).

(** Reversal charges every exit occurrence and inverse lookup while sharing the existing indexes. *)
Definition reverse_c {V E} (p : t V E) exits : Cost.t (t V E) :=
  let* entries := present_c (name_of_c p) exits in
  Cost.ret (Make (Graph.reverse_with (graph p) entries (incoming_c p))
    (node_enc p) (names p) (pred p) (succ p) exits (fuel p)).

(** The public reversal is the value projection of its costed implementation. *)
Definition reverse {V E} (p : t V E) exits := Cost.value (reverse_c p exits).

(** Reversal changes neither names nor the binary traversal budget. *)
Theorem reverse_equation {V E} (p : t V E) exits :
  reverse p exits =
    Make (reverse_graph p exits) (node_enc p) (names p) (pred p) (succ p) exits (fuel p).
Proof.
  unfold reverse, reverse_c. rewrite Cost.value_bind, present_c_value. reflexivity.
Qed.

(** Costed reversal only converts exits and constructs the shared reversed view. *)
Theorem reverse_c_equation {V E} (p : t V E) exits :
  reverse_c p exits =
    let* entries := present_c (name_of_c p) exits in
    Cost.ret (Make (Graph.reverse_with (graph p) entries (incoming_c p))
      (node_enc p) (names p) (pred p) (succ p) exits (fuel p)).
Proof.
  reflexivity.
Qed.

Local Lemma reverse_out {V E} (p : t V E) exits v :
  Graph.out (reverse_graph p exits) v =
    match id_of p v with
    | None => []
    | Some i => map fst (pred_edges p i)
    end.
Proof.
  apply incoming_equation.
Qed.

Local Lemma reverse_wf {V E} (p : t V E) exits :
  ready p -> graph_wf (reverse_graph p exits).
Proof.
  intros [Hwf [Hnodup Hp]]. constructor.
  - exact (nodes_nodup Hwf).
  - intros v Hin. apply present_spec in Hin. destruct Hin as [i [Hi Hname]].
    apply (ids_domain p Hp). exists i. now apply (id_of_name_of p).
  - intros v e Hin. rewrite reverse_out in Hin.
    destruct (id_of p v) as [i|] eqn:Hi; [|contradiction].
    apply in_map_iff in Hin. destruct Hin as [[a j] [Ha Hin]]. cbn in Ha. subst a.
    apply (pred_agrees p Hp v i e j Hi) in Hin. exact (proj1 (proj2 (proj2 Hin))).
  - intros v e Hv Hin. rewrite reverse_out in Hin.
    destruct (id_of p v) as [i|] eqn:Hi; [|contradiction].
    apply in_map_iff in Hin. destruct Hin as [[a j] [Ha Hin]]. cbn in Ha. subst a.
    apply (pred_agrees p Hp v i e j Hi) in Hin. exact (proj1 Hin).
Qed.

Local Lemma reverse_nodup {V E} (p : t V E) exits :
  ready p -> forall v, NoDup (Graph.out (reverse_graph p exits) v).
Proof.
  intros [_ [_ Hp]] v. rewrite reverse_out.
  destruct (id_of p v); [apply (pred_nodup p Hp)|constructor].
Qed.

Local Lemma reverse_edges {V E} (p : t V E) exits e :
  ready p ->
  (In e (all_edges (reverse_graph p exits)) <-> In e (all_edges (graph p))).
Proof.
  intros [Hwf [Hnodup Hp]]. unfold all_edges. rewrite !in_flat_map. split.
  - intros [v [Hv Hin]]. rewrite reverse_out in Hin.
    destruct (id_of p v) as [i|] eqn:Hi; [|contradiction].
    apply in_map_iff in Hin. destruct Hin as [[a j] [Ha Hin]]. cbn in Ha. subst a.
    apply (pred_agrees p Hp v i e j Hi) in Hin.
    exists (Graph.source (graph p) e). tauto.
  - intros [u [Hu Hin]].
    destruct (proj1 (ids_domain p Hp u) Hu) as [i Hi].
    assert (Hv : In (Graph.target (graph p) e) (Graph.nodes (graph p))).
    { eapply out_target_in; eauto. }
    destruct (proj1 (ids_domain p Hp _) Hv) as [j Hj].
    exists (Graph.target (graph p) e). split; [exact Hv|].
    rewrite reverse_out, Hj. apply in_map_iff. exists (e, i). split; [reflexivity|].
    apply (pred_agrees p Hp _ j e i Hj).
    rewrite (out_source Hwf u e Hin). auto.
Qed.

Local Lemma count_edges {V E} (g : Graph.t V E) : edge_count g = length (all_edges g).
Proof.
  unfold edge_count, all_edges. induction (Graph.nodes g) as [|v rest IH]; cbn.
  - reflexivity.
  - rewrite length_app, IH. reflexivity.
Qed.

Local Lemma reverse_edge_count {V E} (p : t V E) exits :
  ready p -> edge_count (reverse_graph p exits) = edge_count (graph p).
Proof.
  intro Hready. rewrite !count_edges. apply Permutation_length, NoDup_Permutation.
  - apply edges_nodup.
    + exact (nodes_nodup (reverse_wf p exits Hready)).
    + exact (reverse_nodup p exits Hready).
    + exact (out_source (reverse_wf p exits Hready)).
  - destruct Hready as [Hwf [Hnodup Hp]].
    apply edges_nodup; [exact (nodes_nodup Hwf)|exact Hnodup|exact (out_source Hwf)].
  - intro e. apply reverse_edges. exact Hready.
Qed.

Local Lemma reverse_ids {V E} (p : t V E) exits :
  laws p -> (forall i, In i exits -> valid_id p i) ->
  ids (node_enc p) (names p) (present (name_of p) exits) = exits.
Proof.
  intros Hp Hvalid. induction exits as [|i rest IH]; [reflexivity|].
  destruct (Hvalid i (or_introl eq_refl)) as [v [Hv Hi]].
  pose proof (name_of_id_of p v i Hp Hi) as Hname.
  cbn [present]. rewrite Hname. cbn [ids present].
  change (Intern.find (node_enc p) v (names p) = Some i) in Hi. rewrite Hi.
  f_equal. apply IH. intros j Hj. apply Hvalid. now right.
Qed.

Local Lemma reverse_pred_agrees {V E} (p : t V E) exits v i e j :
  ready p -> id_of p v = Some i ->
  (In (e, j) (succ_edges p i) <->
    In (Graph.target (graph p) e) (Graph.nodes (graph p)) /\
    In e (Graph.out (reverse_graph p exits) (Graph.target (graph p) e)) /\
    Graph.source (graph p) e = v /\ id_of p (Graph.target (graph p) e) = Some j).
Proof.
  intros Hready Hi. pose proof Hready as [Hwf [Hnodup Hp]].
  rewrite (succ_spec p v i e j Hp Hi). split.
  - intros [He Hj]. split.
    + apply (out_target_in Hwf v e); [|exact He].
      apply (ids_domain p Hp v). now exists i.
    + split.
      * rewrite reverse_out, Hj. apply in_map_iff. exists (e, i).
        split; [reflexivity|]. apply (adjacency_dual p i e j Hready).
        apply (succ_spec p v i e j Hp Hi). auto.
      * split; [exact (out_source Hwf v e He)|exact Hj].
  - intros [Ht [He [Hsource Hj]]]. split; [|exact Hj].
    rewrite reverse_out, Hj in He.
    apply in_map_iff in He. destruct He as [[a k] [Ha Hin]]. cbn in Ha. subst a.
    apply (pred_agrees p Hp _ j e k Hj) in Hin.
    rewrite <- Hsource. tauto.
Qed.

(** Reversal preserves readiness when every requested exit denotes a graph node. *)
Theorem reverse_ready {V E} (p : t V E) exits :
  ready p -> (forall i, In i exits -> valid_id p i) -> ready (reverse p exits).
Proof.
  intros Hready Hvalid. rewrite reverse_equation.
  pose proof Hready as [Hwf [Hnodup Hp]].
  split; [exact (reverse_wf p exits Hready)|].
  split; [exact (reverse_nodup p exits Hready)|].
  constructor.
  - exact (encoding_valid p Hp).
  - exact (names_wf p Hp).
  - exact (ids_domain p Hp).
  - exact (ids_dense p Hp).
  - exact (ids_inverse p Hp).
  - exact (pred_wf p Hp).
  - exact (succ_wf p Hp).
  - intros v i Hi. change (id_of p v = Some i) in Hi.
    change (map fst (pred_edges p i) = Graph.out (reverse_graph p exits) v).
    rewrite reverse_out, Hi. reflexivity.
  - intros i e j Hin.
    change (In (e, j) (pred_edges p i)) in Hin.
    destruct (name_of p i) as [v|] eqn:Hname.
    + pose proof (id_of_name_of p i v Hp Hname) as Hi.
      apply (pred_agrees p Hp v i e j Hi) in Hin. exact (proj2 (proj2 (proj2 Hin))).
    + rewrite (pred_domain p Hp i Hname) in Hin. contradiction.
  - intros v i e j Hi.
    change (id_of p v = Some i) in Hi.
    change (In (e, j) (succ_edges p i) <->
      In (Graph.target (graph p) e) (Graph.nodes (graph p)) /\
      In e (Graph.out (reverse_graph p exits) (Graph.target (graph p) e)) /\
      Graph.source (graph p) e = v /\ id_of p (Graph.target (graph p) e) = Some j).
    now apply reverse_pred_agrees.
  - exact (pred_domain p Hp).
  - exact (succ_domain p Hp).
  - intro i. change (NoDup (map fst (succ_edges p i))).
    destruct (name_of p i) as [v|] eqn:Hname.
    + rewrite (succ_agrees p Hp v i (id_of_name_of p i v Hp Hname)). apply Hnodup.
    + rewrite (succ_domain p Hp i Hname). constructor.
  - change (exits = ids (node_enc p) (names p) (present (name_of p) exits)).
    symmetry. now apply reverse_ids.
  - change (Pos.to_nat (fuel p) =
      2 * length (Graph.nodes (graph p)) + edge_count (reverse_graph p exits) + 2).
    rewrite reverse_edge_count by exact Hready. exact (fuel_value p Hp).
Qed.

(** Preparation exposes its source graph without requiring implementation unfolding. *)
Theorem prepare_graph {V E} enc (g : Graph.t V E) : graph (prepare enc g) = g.
Proof.
  rewrite prepare_equation. reflexivity.
Qed.

(** Preparation interns precisely the listed nodes in first-occurrence order. *)
Theorem prepare_names {V E} enc (g : Graph.t V E) :
  names (prepare enc g) = Intern.of_list enc (Graph.nodes g).
Proof.
  rewrite prepare_equation. reflexivity.
Qed.

Arguments prepare {V E} enc g : simpl never.
Arguments reverse {V E} p exits : simpl never.
Arguments reverse_c {V E} p exits : simpl never.
Arguments id_of {V E} p v : simpl never.
Arguments id_of_c {V E} p v : simpl never.
Arguments name_of {V E} p i : simpl never.
Arguments name_of_c {V E} p i : simpl never.
Arguments succ_edges {V E} p i : simpl never.
Arguments succ_edges_c {V E} p i : simpl never.
Arguments pred_edges {V E} p i : simpl never.
Arguments pred_edges_c {V E} p i : simpl never.

End Prepared.
