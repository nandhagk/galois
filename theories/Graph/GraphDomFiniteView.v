(** * Finite graph views of arbitrary prepared storage

    A charged view indexes the reference universe and filters cached adjacency through that universe.
    For example, an unlisted target in malformed prepared storage cannot enter the normalized graph.
    Builds on: GraphPrepared, GraphReach and the public indexed search preparation boundary. *)

From Stdlib Require Import List Bool PArith.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet BaseIndex.
From Galois.Graph Require Import GraphModel GraphPrepared GraphReach.
Import List.ListNotations Cost.Notations.

Module DomFiniteView.

Record data := Data {
  members : FinSet.t positive;
  vertices : list positive;
  entries : list positive;
  rows : Map.t positive (FinSet.t positive)
}.

Definition targets_c {V E} (p : Prepared.t V E) all u :=
  let* outgoing := Prepared.succ_edges_c p u in
  let* targets := map_c (fun ev => Cost.ret (snd ev)) outgoing in
  let* valid := filter_c (fun v => FinSet.mem_c positive_encoding v all) targets in
  FinSet.of_list_c positive_encoding valid.

Definition data_c {V E} (p : Prepared.t V E) roots :=
  let* ids := Prepared.present_c (Prepared.id_of_c p) (Graph.nodes (Prepared.graph p)) in
  let* all := FinSet.of_list_c positive_encoding ids in
  let* vertices := FinSet.elements_c all in
  let* entries := filter_c (fun v => FinSet.mem_c positive_encoding v all) roots in
  let* rows := fold_right_c (fun u rows =>
    let* targets := targets_c p all u in
    Map.set_c positive_encoding u targets rows) Map.empty vertices in
  Cost.ret (Data all vertices entries rows).

Definition view {V E} (p : Prepared.t V E) roots := Cost.value (data_c p roots).

Definition outgoing_c (rows : Map.t positive (FinSet.t positive)) u :=
  let* targets := Map.get_c positive_encoding u rows in
  match targets with
  | None => Cost.ret []
  | Some targets =>
    let* listed := FinSet.elements_c targets in
    map_c (fun v => Cost.ret (u, v)) listed
  end.

Definition graph (d : data) :=
  Graph.Make (entries d) (vertices d) (outgoing_c (rows d))
    (fun uv => Cost.ret (fst uv)) (fun uv => Cost.ret (snd uv)).

(** The normalized view is prepared once and every later search can reuse the returned dictionary. *)
Definition prepare_c {V E} (p : Prepared.t V E) roots :=
  let* d := data_c p roots in
  Prepared.prepare_c positive_encoding (graph d).

Definition prepared {V E} (p : Prepared.t V E) roots := Cost.value (prepare_c p roots).

Definition universe_set {V E} (p : Prepared.t V E) :=
  FinSet.of_list positive_encoding
    (Prepared.present (Prepared.id_of p) (Graph.nodes (Prepared.graph p))).

(** Every supplied adjacency occurrence is inspected before target filtering and canonicalization. *)
Theorem targets_value {V E} (p : Prepared.t V E) all u :
  Cost.value (targets_c p all u) =
    FinSet.of_list positive_encoding
      (filter (fun v => FinSet.mem positive_encoding v all)
        (map snd (Prepared.succ_edges p u))).
Proof.
  unfold targets_c. autorewrite with galois_cost. reflexivity.
Qed.

(** The normalized universe is the same finite set as the raw reference universe. *)
Theorem universe_members {V E} (p : Prepared.t V E) v :
  FinSet.mem positive_encoding v (universe_set p) = true <-> In v (Reach.universe p).
Proof.
  unfold universe_set, Reach.universe.
  rewrite FinSet.mem_of_list, existsb_exists, nodup_In. split.
  - intros [u [Hu Heq]]. apply (eqb_true_iff _ positive_encoding_laws) in Heq.
    now subst u.
  - intro Hv. exists v. split; [exact Hv|apply eqb_refl].
Qed.

(** The view retains the actual canonical universe set. *)
Theorem view_members {V E} (p : Prepared.t V E) roots :
  members (view p roots) = universe_set p.
Proof.
  unfold view, data_c. autorewrite with galois_cost.
  rewrite Prepared.present_c_value. reflexivity.
Qed.

(** Canonical enumeration may reorder the reference universe and retains precisely its members. *)
Theorem view_vertices {V E} (p : Prepared.t V E) roots :
  vertices (view p roots) = FinSet.elements (universe_set p).
Proof.
  unfold view, data_c. autorewrite with galois_cost.
  rewrite Prepared.present_c_value. reflexivity.
Qed.

(** The view keeps every supplied root occurrence whose ID belongs to the raw finite universe. *)
Theorem view_entries {V E} (p : Prepared.t V E) roots :
  entries (view p roots) =
    filter (fun v => FinSet.mem positive_encoding v (universe_set p)) roots.
Proof.
  unfold view, data_c. autorewrite with galois_cost.
  rewrite Prepared.present_c_value. reflexivity.
Qed.

(** Row storage is the charged fold over that same canonical finite universe. *)
Theorem view_rows {V E} (p : Prepared.t V E) roots :
  rows (view p roots) =
    fold_right (fun u rows =>
      Map.set positive_encoding u (Cost.value (targets_c p (universe_set p) u)) rows)
      Map.empty (FinSet.elements (universe_set p)).
Proof.
  unfold view, data_c. autorewrite with galois_cost.
  rewrite Prepared.present_c_value. reflexivity.
Qed.

Local Lemma rows_wf {V E} (p : Prepared.t V E) all xs :
  Map.wf positive_encoding
    (fold_right (fun u rows =>
      Map.set positive_encoding u (Cost.value (targets_c p all u)) rows) Map.empty xs).
Proof.
  induction xs as [|u rest IH]; [apply Map.wf_empty|].
  cbn [fold_right]. now apply Map.wf_set.
Qed.

Local Lemma rows_get {V E} (p : Prepared.t V E) all xs u :
  In u xs ->
  Map.get positive_encoding u
    (fold_right (fun u rows =>
      Map.set positive_encoding u (Cost.value (targets_c p all u)) rows) Map.empty xs) =
    Some (Cost.value (targets_c p all u)).
Proof.
  induction xs as [|v rest IH]; intro Hin; [contradiction|].
  cbn [fold_right]. destruct (Pos.eq_dec u v) as [->|Hne].
  - apply Map.get_set_same. apply rows_wf.
  - rewrite Map.get_set_other by
      (try exact positive_encoding_laws; try apply rows_wf; exact Hne).
    apply IH. destruct Hin as [Heq|Hin]; [congruence|exact Hin].
Qed.

Local Lemma rows_none {V E} (p : Prepared.t V E) all xs u :
  ~ In u xs ->
  Map.get positive_encoding u
    (fold_right (fun u rows =>
      Map.set positive_encoding u (Cost.value (targets_c p all u)) rows) Map.empty xs) = None.
Proof.
  induction xs as [|v rest IH]; intro Hnot; [apply Map.get_empty|].
  cbn [fold_right]. rewrite Map.get_set_other by
    (try exact positive_encoding_laws; try apply rows_wf; intro Heq; subst u; apply Hnot; now left).
  apply IH. intro Hin. apply Hnot. now right.
Qed.

Local Lemma vertex_spec {V E} (p : Prepared.t V E) roots v :
  In v (vertices (view p roots)) <-> In v (Reach.universe p).
Proof.
  rewrite view_vertices,
    (FinSet.elements_spec positive_encoding positive_encoding_laws) by apply FinSet.wf_of_list.
  apply universe_members.
Qed.

Local Lemma outgoing_value rows u :
  Cost.value (outgoing_c rows u) =
    match Map.get positive_encoding u rows with
    | None => []
    | Some targets => map (pair u) (FinSet.elements targets)
    end.
Proof.
  unfold outgoing_c. rewrite Cost.value_bind.
  fold (Map.get positive_encoding u rows).
  destruct (Map.get positive_encoding u rows); autorewrite with galois_cost; reflexivity.
Qed.

(** A target is retained exactly when a cached occurrence names a member of the supplied universe. *)
Theorem targets_members {V E} (p : Prepared.t V E) all u v :
  FinSet.mem positive_encoding v (Cost.value (targets_c p all u)) = true <->
    FinSet.mem positive_encoding v all = true /\
      exists e, In (e, v) (Prepared.succ_edges p u).
Proof.
  rewrite targets_value, FinSet.mem_of_list, existsb_exists. split.
  - intros [w [Hin Heq]]. apply (eqb_true_iff _ positive_encoding_laws) in Heq.
    subst w. apply filter_In in Hin. destruct Hin as [Hin Hvalid]. split; [exact Hvalid|].
    apply in_map_iff in Hin. destruct Hin as [[e target] [Heq Hin]].
    cbn [snd] in Heq. subst target. now exists e.
  - intros [Hvalid [e Hin]]. exists v. split; [|apply eqb_refl].
    apply filter_In. split; [|exact Hvalid].
    apply in_map_iff. exists (e, v). auto.
Qed.

(** Normalized graph edges are exactly the raw cached occurrences with both endpoints in the universe. *)
Theorem graph_edge {V E} (p : Prepared.t V E) roots u uv :
  In uv (Graph.out (graph (view p roots)) u) <->
    fst uv = u /\ In u (Reach.universe p) /\ In (snd uv) (Reach.universe p) /\
      exists e, In (e, snd uv) (Prepared.succ_edges p u).
Proof.
  unfold graph. rewrite Graph.make_out, outgoing_value, view_rows.
  destruct (in_dec Pos.eq_dec u (FinSet.elements (universe_set p))) as [Hu|Hu].
  - rewrite rows_get by exact Hu.
    rewrite in_map_iff.
    assert (Hlive : In u (Reach.universe p)).
    { apply universe_members. apply (FinSet.elements_spec positive_encoding positive_encoding_laws);
        [apply FinSet.wf_of_list|exact Hu]. }
    split.
    + intros [v [Heq Hin]].
      apply (FinSet.elements_spec positive_encoding positive_encoding_laws) in Hin;
        [|rewrite targets_value; apply FinSet.wf_of_list].
      apply targets_members in Hin. destruct Hin as [Hvalid Hedge].
      apply universe_members in Hvalid. subst uv. cbn [fst snd]. auto.
    + intros [Hsource [_ [Htarget [e Hedge]]]].
      exists (snd uv). split.
      * destruct uv as [a b]. cbn [fst snd] in *. now subst a.
      * apply (FinSet.elements_spec positive_encoding positive_encoding_laws);
          [rewrite targets_value; apply FinSet.wf_of_list|].
        apply targets_members. split; [now apply universe_members|now exists e].
  - rewrite rows_none by exact Hu. cbn [In]. split; [contradiction|].
    intros [_ [Hlive _]]. apply Hu.
    apply (FinSet.elements_spec positive_encoding positive_encoding_laws);
      [apply FinSet.wf_of_list|now apply universe_members].
Qed.

(** Normalized entries retain supplied multiplicity and recognize the same finite root membership. *)
Theorem graph_entries {V E} (p : Prepared.t V E) roots u :
  In u (Graph.entries (graph (view p roots))) <->
    In u roots /\ In u (Reach.universe p).
Proof.
  cbn [graph Graph.entries]. rewrite view_entries, filter_In, universe_members. reflexivity.
Qed.

(** Normalized graph nodes are precisely the raw reference universe. *)
Theorem graph_nodes {V E} (p : Prepared.t V E) roots u :
  In u (Graph.nodes (graph (view p roots))) <-> In u (Reach.universe p).
Proof.
  apply vertex_spec.
Qed.

(** Finite normalization establishes graph invariants without any law on the original prepared input. *)
Theorem graph_well_formed {V E} (p : Prepared.t V E) roots :
  graph_wf (graph (view p roots)).
Proof.
  constructor.
  - cbn [graph Graph.nodes]. rewrite view_vertices.
    apply (FinSet.elements_nodup positive_encoding). apply FinSet.wf_of_list.
  - intros u Hu. apply graph_entries in Hu. apply graph_nodes. exact (proj2 Hu).
  - intros u uv Hedge. apply graph_edge in Hedge.
    change (fst uv = u). exact (proj1 Hedge).
  - intros u uv Hu Hedge. apply graph_edge in Hedge.
    change (In (snd uv) (Graph.nodes (graph (view p roots)))).
    apply graph_nodes. exact (proj1 (proj2 (proj2 Hedge))).
Qed.

Local Lemma pairs_nodup (u : positive) (xs : list positive) :
  NoDup xs -> NoDup (map (pair u) xs).
Proof.
  intro Hnodup. induction Hnodup as [|v rest Hfresh Hrest IH]; cbn [map].
  - constructor.
  - constructor; [|exact IH].
    intro Hin. apply in_map_iff in Hin. destruct Hin as [w [Heq Hw]].
    injection Heq as Heq. subst w. contradiction.
Qed.

(** Canonical target sets give duplicate-free outgoing labels after all occurrences have been charged. *)
Theorem graph_out_nodup {V E} (p : Prepared.t V E) roots u :
  NoDup (Graph.out (graph (view p roots)) u).
Proof.
  unfold graph. rewrite Graph.make_out, outgoing_value.
  rewrite view_rows.
  destruct (in_dec Pos.eq_dec u (FinSet.elements (universe_set p))) as [Hu|Hu].
  - rewrite rows_get by exact Hu.
    apply pairs_nodup. apply (FinSet.elements_nodup positive_encoding).
    rewrite targets_value. apply FinSet.wf_of_list.
  - rewrite rows_none by exact Hu. constructor.
Qed.

(** The actual prepared normalized view denotes its actual charged normalized graph. *)
Theorem prepared_equation {V E} (p : Prepared.t V E) roots :
  prepared p roots = Prepared.prepare positive_encoding (graph (view p roots)).
Proof.
  reflexivity.
Qed.

(** The normalized dictionary retains its own finite graph rather than the original interpreted graph. *)
Theorem prepared_graph {V E} (p : Prepared.t V E) roots :
  Prepared.graph (prepared p roots) = graph (view p roots).
Proof.
  rewrite prepared_equation. apply Prepared.prepare_graph.
Qed.

(** Every raw computational input yields a ready normalized view with its own proved sufficient fuel. *)
Theorem prepared_ready {V E} (p : Prepared.t V E) roots :
  Prepared.ready (prepared p roots).
Proof.
  rewrite prepared_equation. apply Prepared.prepare_ready.
  - exact positive_encoding_laws.
  - apply graph_well_formed.
  - apply graph_out_nodup.
Qed.

End DomFiniteView.
