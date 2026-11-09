(** * A shared virtual-root boundary

    A fresh root turns all entry paths into paths from one entry.
    For example, two entries sharing a successor become children of the same fresh root.
    Builds on: GraphDomSpec, GraphPrepared, BaseCode and BaseSet. *)

From Stdlib Require Import List Bool PArith NArith Lia Permutation.
From Stdlib.Relations Require Import Relation_Operators Operators_Properties.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseCode BaseEq BaseMap BaseSet BaseIntern.
From Galois.Graph Require Import GraphModel GraphPrepared GraphDomSpec.
Import List.ListNotations Cost.Notations.

Module DomVirtual.

(** Option tags use the encoding-only sum construction and require no client decoder. *)
Definition node_encoding {V} (enc : encoding V) : encoding (option V) :=
  Encoding (fun v =>
    Cost.step ;;
    encode_c (sum_encoding enc unit_encoding)
      (match v with
      | Some v => inl v
      | None => inr tt
      end)).

(** The option dictionary uses disjoint sum tags for real nodes and the root. *)
Theorem node_encoding_equation {V} (enc : encoding V) v :
  encode (node_encoding enc) v =
    encode (sum_encoding enc unit_encoding)
      (match v with
      | Some v => inl v
      | None => inr tt
      end).
Proof.
  reflexivity.
Qed.

(** Injective client encodings give injective virtual-node encodings. *)
Theorem node_encoding_laws {V} (enc : encoding V) :
  encoding_laws enc -> encoding_laws (node_encoding enc).
Proof.
  intro Henc. constructor. intros [v|] [w|] Hcode;
    rewrite !node_encoding_equation in Hcode;
    apply (encode_injective (sum_encoding_laws enc unit_encoding Henc unit_encoding_laws))
      in Hcode; inversion Hcode; reflexivity.
Qed.

(** Entry deduplication charges every supplied occurrence and every selected encoder call. *)
Fixpoint entries_from_c {V} (enc : encoding V) (seen : FinSet.t V) (xs : list V)
    : Cost.t (list V) :=
  match xs with
  | [] => Cost.ret []
  | v :: rest =>
    Cost.step ;;
    let* old := FinSet.mem_c enc v seen in
    if old then entries_from_c enc seen rest
    else
      let* seen' := FinSet.add_c enc v seen in
      Cost.map (cons v) (entries_from_c enc seen' rest)
  end.

Definition entries_from {V} enc seen (xs : list V) :=
  Cost.value (entries_from_c enc seen xs).

(** Entry order is first occurrence order, including the cost of skipped duplicates. *)
Theorem entries_from_equation {V} enc seen (xs : list V) :
  entries_from enc seen xs =
    match xs with
    | [] => []
    | v :: rest =>
      if FinSet.mem enc v seen then entries_from enc seen rest
      else v :: entries_from enc (FinSet.add enc v seen) rest
    end.
Proof.
  destruct xs as [|v rest]; [reflexivity|].
  unfold entries_from at 1. cbn [entries_from_c].
  autorewrite with galois_cost. fold (FinSet.mem enc v seen).
  destruct (FinSet.mem enc v seen); autorewrite with galois_cost; reflexivity.
Qed.

Local Lemma entries_from_spec {V} (enc : encoding V) (Henc : encoding_laws enc) xs :
  forall seen, FinSet.wf enc seen -> forall v,
  In v (entries_from enc seen xs) <-> In v xs /\ FinSet.mem enc v seen = false.
Proof.
  induction xs as [|x rest IH]; intros seen Hseen v; rewrite entries_from_equation.
  - cbn [In]. tauto.
  - destruct (FinSet.mem enc x seen) eqn:Hx.
    + rewrite IH by exact Hseen. cbn [In]. split.
      * intros [Hin Hfree]. auto.
      * intros [[<-|Hin] Hfree]; [congruence|auto].
    + cbn [In]. rewrite IH by now apply FinSet.wf_add.
      rewrite <- not_true_iff_false, FinSet.mem_add by exact Hseen.
      rewrite orb_true_iff, (eqb_true_iff enc Henc).
      split.
      * intros [<-|[Hin Hfree]]; [auto|].
        split; [now right|]. apply not_true_iff_false. tauto.
      * intros [[<-|Hin] Hfree]; [now left|].
        destruct (eqb_dec enc Henc v x) as [->|Hne]; [now left|].
        right. split; [exact Hin|]. intros [Heq|Hpresent]; [congruence|congruence].
Qed.

Local Lemma entries_from_nodup {V} enc (Henc : encoding_laws enc) (xs : list V) :
  forall seen, FinSet.wf enc seen -> NoDup (entries_from enc seen xs).
Proof.
  induction xs as [|x rest IH]; intros seen Hseen; rewrite entries_from_equation.
  - constructor.
  - destruct (FinSet.mem enc x seen).
    + now apply IH.
    + constructor.
      * rewrite entries_from_spec by (try exact Henc; now apply FinSet.wf_add).
        intros [_ Hfree].
        assert (Hmem : FinSet.mem enc x (FinSet.add enc x seen) = true).
        { rewrite FinSet.mem_add by exact Hseen. rewrite eqb_refl. reflexivity. }
        congruence.
      * apply IH. now apply FinSet.wf_add.
Qed.

Definition entries {V E} enc (g : Graph.t V E) :=
  entries_from enc FinSet.empty (Graph.entries g).

(** Synthetic edges retain the first occurrence of each entry and cover all entries. *)
Theorem entries_exact {V E} enc (g : Graph.t V E) :
  encoding_laws enc ->
  NoDup (entries enc g) /\ forall v, In v (entries enc g) <-> In v (Graph.entries g).
Proof.
  intro Henc. split.
  - apply entries_from_nodup; [exact Henc|apply FinSet.wf_empty].
  - intro v. unfold entries.
    rewrite entries_from_spec by (try exact Henc; apply FinSet.wf_empty).
    rewrite FinSet.mem_empty. tauto.
Qed.

(** Entry deduplication has a primitive upper bound independent of the seen-set representation. *)
Theorem entries_from_cost {V} (enc : encoding V) xs seen :
  (Cost.ticks (entries_from_c enc seen xs) <=
    3 * fold_right
      (fun v n => 1 + Cost.ticks (encode_c enc v) + key_bits enc v + n)%N 0%N xs)%N.
Proof.
  revert seen. induction xs as [|v rest IH]; intro seen.
  - cbn [entries_from_c fold_right]. autorewrite with galois_cost. lia.
  - cbn [entries_from_c]. autorewrite with galois_cost.
    fold (FinSet.mem enc v seen).
    destruct (FinSet.mem enc v seen); autorewrite with galois_cost.
    + rewrite FinSet.mem_cost.
      pose proof (IH seen) as Htail.
      cbn [fold_right]. unfold key_bits in *. nia.
    + rewrite FinSet.mem_cost, FinSet.add_cost.
      pose proof (IH (FinSet.add enc v seen)) as Htail.
      fold (FinSet.add enc v seen).
      cbn [fold_right]. unfold key_bits in *. nia.
Qed.

(** Uniform finite callback and width bounds give an occurrence-sensitive numeric bound. *)
Theorem entries_numeric_cost {V} (enc : encoding V) xs seen k w :
  (forall v, In v xs -> (Cost.ticks (encode_c enc v) <= k)%N) ->
  (forall v, In v xs -> (key_bits enc v <= w)%N) ->
  (Cost.ticks (entries_from_c enc seen xs) <=
    3 * N.of_nat (length xs) * (1 + k + w))%N.
Proof.
  intros Hencoding Hwidth.
  pose proof (entries_from_cost enc xs seen) as Hcost.
  assert (Hwork :
    (fold_right (fun v n =>
      1 + Cost.ticks (encode_c enc v) + key_bits enc v + n)%N 0%N xs <=
      N.of_nat (length xs) * (1 + k + w))%N).
  { clear Hcost. revert Hencoding Hwidth.
    induction xs as [|v rest IH]; intros Hencoding Hwidth.
    - change (0 <= 0)%N. reflexivity.
    - pose proof (Hencoding v (or_introl eq_refl)) as Hencode.
      pose proof (Hwidth v (or_introl eq_refl)) as Hbits.
      specialize (IH ltac:(intros x Hx; apply Hencoding; now right)
        ltac:(intros x Hx; apply Hwidth; now right)).
      cbn [fold_right length].
      rewrite Nat2N.inj_succ. nia. }
  nia.
Qed.

Definition out_c {V E} (g : Graph.t V E) (roots : list (E + V)) (v : option V) :=
  match v with
  | None => Cost.ret roots
  | Some v =>
    Cost.step ;;
    let* es := Graph.out_c g v in
    map_c (fun e => Cost.ret (@inl E V e)) es
  end.

Definition source_c {V E} (g : Graph.t V E) (e : E + V) :=
  match e with
  | inl e => Cost.step ;; Cost.map (@Some V) (Graph.source_c g e)
  | inr _ => Cost.ret None
  end.

Definition target_c {V E} (g : Graph.t V E) (e : E + V) :=
  match e with
  | inl e => Cost.step ;; Cost.map (@Some V) (Graph.target_c g e)
  | inr v => Cost.ret (Some v)
  end.

(** Virtual construction materialises the tagged nodes and distinct synthetic edges once. *)
Definition graph_c {V E} enc (g : Graph.t V E) : Cost.t (Graph.t (option V) (E + V)) :=
  let* distinct := entries_from_c enc FinSet.empty (Graph.entries g) in
  let* roots := map_c (fun v => Cost.ret (@inr E V v)) distinct in
  let* real := map_c (fun v => Cost.ret (Some v)) (Graph.nodes g) in
  let* nodes := app_c real [None] in
  Cost.ret (Graph.Make [None] nodes (out_c g roots) (source_c g) (target_c g)).

Definition graph {V E} enc (g : Graph.t V E) := Cost.value (graph_c enc g).

(** The root is listed after the real nodes and synthetic edges follow distinct-entry order. *)
Theorem graph_equation {V E} enc (g : Graph.t V E) :
  graph enc g =
    Graph.Make [None] (map (@Some V) (Graph.nodes g) ++ [None])
      (out_c g (map (@inr E V) (entries enc g))) (source_c g) (target_c g).
Proof.
  unfold graph, graph_c. autorewrite with galois_cost.
  reflexivity.
Qed.

(** Real outgoing occurrences retain their labels and order. *)
Theorem out_real {V E} enc (g : Graph.t V E) v :
  Graph.out (graph enc g) (Some v) = map (@inl E V) (Graph.out g v).
Proof.
  rewrite graph_equation, Graph.make_out. cbn [out_c].
  autorewrite with galois_cost. reflexivity.
Qed.

(** Root outgoing occurrences correspond to the distinct-entry list. *)
Theorem out_root {V E} enc (g : Graph.t V E) :
  Graph.out (graph enc g) None = map (@inr E V) (entries enc g).
Proof.
  rewrite graph_equation, Graph.make_out. reflexivity.
Qed.

(** Tagged original edges retain their source endpoint. *)
Theorem source_real {V E} enc (g : Graph.t V E) e :
  Graph.source (graph enc g) (inl e) = Some (Graph.source g e).
Proof.
  rewrite graph_equation, Graph.make_source. reflexivity.
Qed.

(** Tagged original edges retain their target endpoint. *)
Theorem target_real {V E} enc (g : Graph.t V E) e :
  Graph.target (graph enc g) (inl e) = Some (Graph.target g e).
Proof.
  rewrite graph_equation, Graph.make_target. reflexivity.
Qed.

(** Synthetic edges all start at the root. *)
Theorem source_entry {V E} enc (g : Graph.t V E) v :
  Graph.source (graph enc g) (inr v) = None.
Proof.
  rewrite graph_equation, Graph.make_source. reflexivity.
Qed.

(** A synthetic edge targets its named original entry. *)
Theorem target_entry {V E} enc (g : Graph.t V E) v :
  Graph.target (graph enc g) (inr v) = Some v.
Proof.
  rewrite graph_equation, Graph.make_target. reflexivity.
Qed.

Local Lemma nodup_map_injective {A B} (f : A -> B) xs :
  (forall x y, f x = f y -> x = y) -> NoDup xs -> NoDup (map f xs).
Proof.
  intros Hinjective Hnodup. induction Hnodup as [|x xs Hfresh Hrest IH].
  - constructor.
  - cbn [map]. constructor; [|exact IH].
    intro Hin. apply in_map_iff in Hin. destruct Hin as [y [Heq Hin]].
    apply Hinjective in Heq. subst y. contradiction.
Qed.

Local Lemma real_node {V E} enc (g : Graph.t V E) v :
  In (Some v) (Graph.nodes (graph enc g)) <-> In v (Graph.nodes g).
Proof.
  rewrite graph_equation. cbn [Graph.nodes]. rewrite in_app_iff. split.
  - intros [Hin|[Heq|Hfalse]]; [|discriminate|contradiction].
    apply in_map_iff in Hin. destruct Hin as [x [Heq Hin]].
    inversion Heq. now subst x.
  - intro Hin. left. now apply in_map.
Qed.

Local Lemma nodup_real_root {V} (xs : list V) :
  NoDup xs -> NoDup (map (@Some V) xs ++ [None]).
Proof.
  intro Hnodes. induction Hnodes as [|x rest Hfresh Hrest IH].
  - cbn. constructor; [tauto|constructor].
  - cbn [map app]. constructor; [|exact IH].
    rewrite in_app_iff. intros [Hin|[Hfalse|Hfalse]]; [|discriminate|contradiction].
    apply in_map_iff in Hin. destruct Hin as [v [Heq Hin]].
    injection Heq as <-. contradiction.
Qed.

(** Adding the root preserves graph closure and outgoing-label uniqueness. *)
Theorem graph_ready {V E} enc (g : Graph.t V E) :
  encoding_laws enc -> graph_wf g -> (forall v, NoDup (Graph.out g v)) ->
  graph_wf (graph enc g) /\ forall v, NoDup (Graph.out (graph enc g) v).
Proof.
  intros Henc Hwf Hout.
  destruct (entries_exact enc g Henc) as [Hentries Hentries_spec].
  split.
  - constructor.
    + rewrite graph_equation. cbn [Graph.nodes].
      apply nodup_real_root. exact (nodes_nodup Hwf).
    + intros v Hin. rewrite graph_equation in Hin |- *. cbn [Graph.entries Graph.nodes] in *.
      destruct Hin as [<-|Hfalse]; [|contradiction].
      apply in_or_app. right. now left.
    + intros [v|] [e|s] Hin.
      * rewrite out_real in Hin. apply in_map_iff in Hin.
        destruct Hin as [a [Heq Hin]]. injection Heq as <-.
        rewrite source_real, (out_source Hwf v a Hin). reflexivity.
      * rewrite out_real in Hin. apply in_map_iff in Hin.
        destruct Hin as [a [Hfalse _]]. discriminate.
      * rewrite out_root in Hin. apply in_map_iff in Hin.
        destruct Hin as [a [Hfalse _]]. discriminate.
      * apply source_entry.
    + intros [v|] [e|s] Hv Hin.
      * rewrite out_real in Hin. apply in_map_iff in Hin.
        destruct Hin as [a [Heq Hin]]. injection Heq as <-.
        rewrite target_real, real_node.
        eapply out_target_in; [exact Hwf|exact (proj1 (real_node enc g v) Hv)|exact Hin].
      * rewrite out_real in Hin. apply in_map_iff in Hin.
        destruct Hin as [a [Hfalse _]]. discriminate.
      * rewrite out_root in Hin. apply in_map_iff in Hin.
        destruct Hin as [a [Hfalse _]]. discriminate.
      * rewrite out_root in Hin. apply in_map_iff in Hin.
        destruct Hin as [a [Heq Hin]]. injection Heq as <-.
        rewrite target_entry, real_node.
        apply (entries_in Hwf). now apply Hentries_spec.
  - intros [v|].
    + rewrite out_real. apply nodup_map_injective.
      * intros x y Heq. now injection Heq.
      * apply Hout.
    + rewrite out_root. apply nodup_map_injective.
      * intros x y Heq. now injection Heq.
      * exact Hentries.
Qed.

(** Preparation is charged and uses the same virtual graph for every downstream phase. *)
Definition virtual_c {V E} (p : Prepared.t V E) :=
  let* g := graph_c (Prepared.node_enc p) (Prepared.graph p) in
  Prepared.prepare_c (node_encoding (Prepared.node_enc p)) g.

Definition virtual {V E} (p : Prepared.t V E) := Cost.value (virtual_c p).

(** Virtual preparation is the public prepared constructor applied to the tagged graph. *)
Theorem virtual_equation {V E} (p : Prepared.t V E) :
  virtual p =
    Prepared.prepare (node_encoding (Prepared.node_enc p))
      (graph (Prepared.node_enc p) (Prepared.graph p)).
Proof.
  reflexivity.
Qed.

(** Virtual preparation retains the tagged graph as its semantic graph. *)
Theorem prepared_graph {V E} (p : Prepared.t V E) :
  Prepared.graph (virtual p) = graph (Prepared.node_enc p) (Prepared.graph p).
Proof.
  rewrite virtual_equation. apply Prepared.prepare_graph.
Qed.

(** Ready input graphs produce ready single-entry virtual graphs. *)
Theorem virtual_ready {V E} (p : Prepared.t V E) :
  Prepared.ready p -> Prepared.ready (virtual p).
Proof.
  intros [Hwf [Hout Hp]]. rewrite virtual_equation.
  pose proof (Prepared.encoding_valid p Hp) as Henc.
  destruct (graph_ready _ _ Henc Hwf Hout) as [Hgraph Hlabels].
  apply Prepared.prepare_ready; [now apply node_encoding_laws|exact Hgraph|exact Hlabels].
Qed.

(** The virtual root receives exactly one plus the count of original nodes. *)
Theorem root_id {V E} (p : Prepared.t V E) :
  Prepared.ready p ->
  Prepared.id_of (virtual p) None =
    Some (Pos.of_succ_nat (length (Graph.nodes (Prepared.graph p)))).
Proof.
  intros [Hwf [_ Hp]].
  rewrite virtual_equation, Prepared.prepare_equation, Prepared.id_of_equation.
  cbn [Prepared.node_enc Prepared.names].
  rewrite graph_equation. cbn [Graph.nodes].
  rewrite <- length_map with (f := @Some V).
  apply Intern.of_list_fresh_last.
  - apply node_encoding_laws. exact (Prepared.encoding_valid p Hp).
  - apply nodup_map_injective; [intros x y Heq; now injection Heq|].
    exact (nodes_nodup Hwf).
  - intro Hin. apply in_map_iff in Hin. destruct Hin as [v [Hfalse _]]. discriminate.
Qed.

(** Readiness identifies interner cardinality with node-list cardinality without any order premise. *)
Theorem size_nodes {V E} (p : Prepared.t V E) :
  Prepared.ready p -> Intern.size (Prepared.names p) = length (Graph.nodes (Prepared.graph p)).
Proof.
  intros [Hwf [_ Hp]]. rewrite Intern.size_equation, Map.size_elements, <- length_map
    with (f := @fst V positive).
  apply Permutation_length. apply NoDup_Permutation.
  - apply (Map.elements_nodup (Prepared.node_enc p)).
    exact (proj1 (Intern.wf_maps _ _ (Prepared.names_wf p Hp))).
  - exact (nodes_nodup Hwf).
  - intro v. rewrite in_map_iff. split.
    + intros [[a i] [Heq Hin]]. cbn [fst] in Heq. subst a.
      apply (Map.elements_spec (Prepared.node_enc p) (Prepared.encoding_valid p Hp)
        v i _ (proj1 (Intern.wf_maps _ _ (Prepared.names_wf p Hp)))) in Hin.
      apply (Prepared.ids_domain p Hp). exists i.
      rewrite Prepared.id_of_equation, Intern.find_equation. exact Hin.
    + intro Hin. destruct (proj1 (Prepared.ids_domain p Hp v) Hin) as [i Hi].
      exists (v, i). split; [reflexivity|].
      apply (Map.elements_spec (Prepared.node_enc p) (Prepared.encoding_valid p Hp)
        v i _ (proj1 (Intern.wf_maps _ _ (Prepared.names_wf p Hp)))).
      rewrite Prepared.id_of_equation, Intern.find_equation in Hi. exact Hi.
Qed.

(** The root ID is the original dense frontier, independently of the original name order. *)
Theorem root_id_frontier {V E} (p : Prepared.t V E) :
  Prepared.ready p ->
  Prepared.id_of (virtual p) None = Some (Intern.next (Prepared.names p)).
Proof.
  intro Hready. rewrite root_id by exact Hready.
  f_equal. apply Pos2Nat.inj. rewrite SuccNat2Pos.id_succ.
  rewrite (Intern.next_size (Prepared.node_enc p)
    (Prepared.encoding_valid p (proj2 (proj2 Hready))) _
    (Prepared.names_wf p (proj2 (proj2 Hready)))).
  now rewrite size_nodes.
Qed.

Local Lemma path_nil_inv {V E} (g : Graph.t V E) s n :
  path g s [] n -> s = n.
Proof.
  intro Hpath. inversion Hpath. reflexivity.
Qed.

Local Lemma path_cons_inv {V E} (g : Graph.t V E) s e es n :
  path g s (e :: es) n ->
  s = Graph.source g e /\ In e (Graph.out g (Graph.source g e)) /\
    path g (Graph.target g e) es n.
Proof.
  intro Hpath. inversion Hpath; subst. auto.
Qed.

(** Lifting an original path keeps every original edge occurrence in order. *)
Theorem path_lift {V E} enc (g : Graph.t V E) s es n :
  path g s es n ->
  path (graph enc g) (Some s) (map (@inl E V) es) (Some n).
Proof.
  intro Hpath. induction Hpath as [v|e es n Hedge Hpath IH]; cbn [map].
  - constructor.
  - rewrite <- (source_real enc g e).
    apply path_cons; [rewrite source_real, out_real; now apply in_map|].
    now rewrite target_real.
Qed.

(** A path between real nodes has no synthetic edge occurrences. *)
Theorem path_lower {V E} enc (g : Graph.t V E) :
  forall ves s n, path (graph enc g) (Some s) ves (Some n) ->
    exists es, ves = map (@inl E V) es /\ path g s es n.
Proof.
  induction ves as [|[e|entry] ves IH]; intros s n Hpath.
  - apply path_nil_inv in Hpath. injection Hpath as <-.
    exists []. split; [reflexivity|constructor].
  - apply path_cons_inv in Hpath. destruct Hpath as [Hs [He Htail]].
    rewrite source_real in Hs, He. rewrite out_real in He.
    rewrite target_real in Htail. injection Hs as Hs. subst s.
    apply in_map_iff in He. destruct He as [a [Heq He]].
    injection Heq as <-.
    destruct (IH _ _ Htail) as [es [Hes Horiginal]].
    exists (a :: es). split; [cbn [map]; now rewrite Hes|now constructor].
  - apply path_cons_inv in Hpath. destruct Hpath as [Hsource _].
    rewrite source_entry in Hsource. discriminate.
Qed.

(** A root-to-real path starts with exactly one entry edge. *)
Theorem root_path {V E} enc (g : Graph.t V E) :
  encoding_laws enc -> forall ves n, path (graph enc g) None ves (Some n) ->
  exists s es, ves = inr s :: map (@inl E V) es /\
    In s (Graph.entries g) /\ path g s es n.
Proof.
  intros Henc [|[e|s] ves] n Hpath.
  - apply path_nil_inv in Hpath. discriminate.
  - apply path_cons_inv in Hpath. destruct Hpath as [Hs _].
    rewrite source_real in Hs. discriminate.
  - apply path_cons_inv in Hpath. destruct Hpath as [_ [He Htail]].
    rewrite source_entry, out_root in He. rewrite target_entry in Htail.
    apply in_map_iff in He. destruct He as [a [Heq He]].
    injection Heq as <-.
    destruct (path_lower enc g ves a n Htail) as [es [Hes Horiginal]].
    exists a, es. split; [now rewrite Hes|].
    split; [apply (proj2 (entries_exact enc g Henc)); exact He|exact Horiginal].
Qed.

(** Every original entry path lifts after one synthetic entry edge. *)
Theorem entry_path {V E} enc (g : Graph.t V E) s es n :
  encoding_laws enc -> In s (Graph.entries g) -> path g s es n ->
  path (graph enc g) None (inr s :: map (@inl E V) es) (Some n).
Proof.
  intros Henc Hentry Hpath. rewrite <- (source_entry enc g s).
  apply path_cons.
  - rewrite source_entry, out_root. apply in_map.
    apply (proj2 (entries_exact enc g Henc)). exact Hentry.
  - rewrite target_entry. now apply path_lift.
Qed.

(** Reachability of real nodes is unchanged, including graphs without entries. *)
Theorem virtual_reachable_iff {V E} enc (g : Graph.t V E) n :
  encoding_laws enc -> (reachable (graph enc g) (Some n) <-> reachable g n).
Proof.
  intro Henc. split; intro Hreach; apply reachable_iff_path in Hreach;
    destruct Hreach as [s [es [Hentry Hpath]]].
  - rewrite graph_equation in Hentry. cbn [Graph.entries] in Hentry.
    destruct Hentry as [<-|Hfalse]; [|contradiction].
    destruct (root_path enc g Henc es n Hpath) as [a [original [_ [Ha Horiginal]]]].
    apply reachable_iff_path. exists a, original. auto.
  - apply reachable_iff_path. exists None, (inr s :: map (@inl E V) es).
    split.
    + rewrite graph_equation. now left.
    + now apply entry_path.
Qed.

Local Lemma path_occurrence {V E} enc (g : Graph.t V E) d s es :
  (exists e, In e (inr s :: map (@inl E V) es) /\
    Graph.target (graph enc g) e = Some d) <->
  d = s \/ exists e, In e es /\ Graph.target g e = d.
Proof.
  split.
  - intros [e [[<-|Hin] Htarget]].
    + rewrite target_entry in Htarget. injection Htarget as <-. now left.
    + apply in_map_iff in Hin. destruct Hin as [a [<- Hin]].
      rewrite target_real in Htarget. injection Htarget as Htarget.
      right. exists a. auto.
  - intros [->|[e [Hin Htarget]]].
    + exists (inr s). split; [now left|apply target_entry].
    + exists (inl e). split; [right; now apply in_map|].
      rewrite target_real, Htarget. reflexivity.
Qed.

(** Real-node dominance is unchanged for every semantic query, including unreachable nodes. *)
Theorem virtual_dominates_iff {V E} enc (g : Graph.t V E) d n :
  encoding_laws enc ->
  (dominates g d n <-> dominates (graph enc g) (Some d) (Some n)).
Proof.
  intro Henc. split.
  - intros Hdom root ves Hentry Hpath.
    rewrite graph_equation in Hentry. cbn [Graph.entries] in Hentry.
    destruct Hentry as [<-|Hfalse]; [|contradiction].
    destruct (root_path enc g Henc ves n Hpath) as [s [es [-> [Hs Horiginal]]]].
    right. apply path_occurrence. now apply Hdom.
  - intros Hdom s es Hentry Hpath.
    pose proof (entry_path enc g s es n Henc Hentry Hpath) as Hvirtual.
    assert (Hroot : In None (Graph.entries (graph enc g))).
    { rewrite graph_equation. now left. }
    destruct (Hdom None _ Hroot Hvirtual) as [Hfalse|Hoccurs]; [discriminate|].
    now apply path_occurrence in Hoccurs.
Qed.

(** The fresh root dominates every virtual node because it is the sole entry. *)
Theorem root_dominates {V E} enc (g : Graph.t V E) n :
  dominates (graph enc g) None n.
Proof.
  intros s es Hentry Hpath. rewrite graph_equation in Hentry.
  cbn [Graph.entries] in Hentry. destruct Hentry as [<-|Hfalse]; [now left|contradiction].
Qed.

(** Real immediate dominators coincide on both sides of the virtual-root boundary. *)
Theorem virtual_immediate_iff {V E} enc (g : Graph.t V E) d n :
  encoding_laws enc ->
  (immediately_dominates g d n <->
    immediately_dominates (graph enc g) (Some d) (Some n)).
Proof.
  intro Henc. split.
  - intros [[Hdom Hdistinct] Hnearest]. split.
    + split; [now apply virtual_dominates_iff|congruence].
    + intros [x|] [Hx Hdistinctx]; [|apply root_dominates].
      apply virtual_dominates_iff; [exact Henc|].
      apply Hnearest. split; [apply (proj2 (virtual_dominates_iff enc g x n Henc)); exact Hx|].
      congruence.
  - intros [[Hdom Hdistinct] Hnearest]. split.
    + split; [apply (proj2 (virtual_dominates_iff enc g d n Henc)); exact Hdom|congruence].
    + intros x [Hx Hdistinctx].
      apply (proj2 (virtual_dominates_iff enc g x d Henc)).
      apply Hnearest. split; [now apply virtual_dominates_iff|congruence].
Qed.

End DomVirtual.
