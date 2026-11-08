(** * Charged component condensation

    Condensation groups cross-component arcs and removes duplicate targets in each bucket.
    For example, parallel labels between two components produce one successor.
    Builds on: GraphSccSpec, GraphPrepared and BaseIndex. *)

From Stdlib Require Import List Bool PArith NArith Lia Relation_Operators.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet BaseIndex.
From Galois.Graph Require Import GraphPrepared GraphVisitor GraphSearchSpec GraphSearchInvariant
  GraphSccSpec.
Import List.ListNotations Cost.Notations.

Module Condense.

(** Mapping an inspected occurrence retains it exactly when both owners exist and differ. *)
Definition target_c {E} (r : Scc.result) i (ev : E * positive) :=
  let* owner := Map.get_c positive_encoding (snd ev) (Scc.comp_of r) in
  match owner with
  | None => Cost.ret None
  | Some j => Cost.ret (if Pos.eqb i j then None else Some (i, j))
  end.

Definition target {E} r i (ev : E * positive) := Cost.value (target_c r i ev).

(** Target filtering distinguishes missing ownership from a self edge. *)
Theorem target_equation {E} r i (ev : E * positive) :
  target r i ev =
    match Map.get positive_encoding (snd ev) (Scc.comp_of r) with
    | None => None
    | Some j => if Pos.eqb i j then None else Some (i, j)
    end.
Proof.
  unfold target, target_c. autorewrite with galois_cost.
  fold (Map.get positive_encoding (snd ev) (Scc.comp_of r)).
  destruct (Map.get positive_encoding (snd ev) (Scc.comp_of r)); reflexivity.
Qed.

(** Each owned vertex reads its prepared adjacency once and charges every inspected occurrence. *)
Definition vertex_c {V E} (p : Prepared.t V E) (r : Scc.result) u :=
  let* owner := Map.get_c positive_encoding u (Scc.comp_of r) in
  match owner with
  | None => Cost.ret []
  | Some i =>
    let* es := Prepared.succ_edges_c p u in
    Prepared.present_c (target_c r i) es
  end.

Definition vertex {V E} (p : Prepared.t V E) r u := Cost.value (vertex_c p r u).

(** The vertex equation preserves outgoing occurrence order while excluding missing owners. *)
Theorem vertex_equation {V E} (p : Prepared.t V E) r u :
  vertex p r u =
    match Map.get positive_encoding u (Scc.comp_of r) with
    | None => []
    | Some i =>
      Prepared.present (fun ev =>
        match Map.get positive_encoding (snd ev) (Scc.comp_of r) with
        | None => None
        | Some j => if Pos.eqb i j then None else Some (i, j)
        end) (Prepared.succ_edges p u)
    end.
Proof.
  unfold vertex, vertex_c. autorewrite with galois_cost.
  fold (Map.get positive_encoding u (Scc.comp_of r)).
  destruct (Map.get positive_encoding u (Scc.comp_of r)); [|reflexivity].
  autorewrite with galois_cost. rewrite Prepared.present_c_value.
  apply Prepared.present_ext. intro ev. apply target_equation.
Qed.

Definition vertices_c {V E} (p : Prepared.t V E) r vs :=
  fold_right_c (fun u tail =>
    let* es := vertex_c p r u in app_c es tail) [] vs.

Definition vertices {V E} (p : Prepared.t V E) r vs := Cost.value (vertices_c p r vs).

(** Vertex concatenation visits only supplied component members. *)
Theorem vertices_equation {V E} (p : Prepared.t V E) r vs :
  vertices p r vs = flat_map (vertex p r) vs.
Proof.
  unfold vertices, vertices_c. rewrite value_fold_right_c.
  induction vs as [|u rest IH]; [reflexivity|].
  cbn [fold_right flat_map]. autorewrite with galois_cost. now rewrite IH.
Qed.

Definition cross_edges_c {V E} (p : Prepared.t V E) r :=
  fold_right_c (fun vs tail =>
    let* es := vertices_c p r vs in app_c es tail) [] (Scc.components r).

Definition cross_edges {V E} (p : Prepared.t V E) r := Cost.value (cross_edges_c p r).

(** Cross-edge collection scans components directly and performs no global preparation pass. *)
Theorem cross_edges_equation {V E} (p : Prepared.t V E) r :
  cross_edges p r = flat_map (vertex p r) (concat (Scc.components r)).
Proof.
  unfold cross_edges, cross_edges_c. rewrite value_fold_right_c.
  induction (Scc.components r) as [|vs rest IH]; [reflexivity|].
  cbn [fold_right concat]. autorewrite with galois_cost.
  fold (vertices p r vs).
  rewrite vertices_equation, IH, flat_map_app. reflexivity.
Qed.

(** A set records every retained target, preserving the first occurrence in each bucket. *)
Fixpoint unique_c (xs : list (positive * positive)) (seen : FinSet.t positive)
    : Cost.t (list positive) :=
  match xs with
  | [] => Cost.ret []
  | (_, j) :: rest =>
    Cost.step ;;
    let* present := FinSet.mem_c positive_encoding j seen in
    if present then unique_c rest seen else
    let* seen' := FinSet.add_c positive_encoding j seen in
    let* ys := unique_c rest seen' in Cost.ret (j :: ys)
  end.

Definition unique xs seen := Cost.value (unique_c xs seen).

(** Deduplication performs exactly the charged membership and insertion decisions. *)
Theorem unique_equation xs seen :
  unique xs seen =
    match xs with
    | [] => []
    | (_, j) :: rest =>
      if FinSet.mem positive_encoding j seen then unique rest seen else
      j :: unique rest (FinSet.add positive_encoding j seen)
    end.
Proof.
  destruct xs as [|[i j] rest]; [reflexivity|].
  unfold unique at 1. cbn [unique_c]. autorewrite with galois_cost.
  fold (FinSet.mem positive_encoding j seen).
  destruct (FinSet.mem positive_encoding j seen); reflexivity.
Qed.

(** Rows enumerate actual component indices and retain an empty successor list for sinks. *)
Fixpoint rows_c (cs : list (list positive)) i
    (buckets : Index.t positive (positive * positive))
    : Cost.t (Map.t positive (list positive)) :=
  match cs with
  | [] => Cost.ret Map.empty
  | _ :: rest =>
    Cost.step ;;
    let* tail := rows_c rest (Pos.succ i) buckets in
    let* xs := Index.find_c positive_encoding i buckets in
    let* ys := unique_c xs FinSet.empty in
    Map.set_c positive_encoding i ys tail
  end.

Definition rows cs i buckets := Cost.value (rows_c cs i buckets).

(** Row construction advances an explicit index without converting unary list lengths to keys. *)
Theorem rows_equation cs i buckets :
  rows cs i buckets =
    match cs with
    | [] => Map.empty
    | _ :: rest =>
      Map.set positive_encoding i (unique (Index.find positive_encoding i buckets) FinSet.empty)
        (rows rest (Pos.succ i) buckets)
    end.
Proof.
  destruct cs; reflexivity.
Qed.

(** Condensation retains every owned arc regardless of the redundant producer scope argument. *)
Definition of_scc_c {V E} (p : Prepared.t V E) (_scope : Scope.t) r :=
  let* es := cross_edges_c p r in
  let* buckets := Index.group_by_c positive_encoding
    (fun ev => Cost.ret (fst ev)) es in
  let* successors := rows_c (Scc.components r) 1%positive buckets in
  let* count := length_c (Scc.components r) in
  Cost.ret (Condensation.Make count successors).

Definition of_scc {V E} (p : Prepared.t V E) scope r := Cost.value (of_scc_c p scope r).

(** Condensation has stable grouped buckets and a natural component count, including zero. *)
Theorem of_scc_equation {V E} (p : Prepared.t V E) scope r :
  of_scc p scope r =
    Condensation.Make (length (Scc.components r))
      (rows (Scc.components r) 1%positive
        (Index.group_by positive_encoding fst (cross_edges p r))).
Proof.
  unfold of_scc, of_scc_c. autorewrite with galois_cost.
  rewrite Index.group_by_c_value. reflexivity.
Qed.

(** Collected pairs correspond to inspected outgoing occurrences between existing distinct owners. *)
Theorem vertex_spec {V E} (p : Prepared.t V E) r u i j :
  In (i, j) (vertex p r u) <->
    Map.get positive_encoding u (Scc.comp_of r) = Some i /\
    i <> j /\ exists e v, In (e, v) (Prepared.succ_edges p u) /\
      Map.get positive_encoding v (Scc.comp_of r) = Some j.
Proof.
  rewrite vertex_equation.
  destruct (Map.get positive_encoding u (Scc.comp_of r)) as [a|] eqn:Hu.
  - rewrite Prepared.present_spec. split.
    + intros [[e v] [He Hpair]]. cbn [snd] in Hpair.
      destruct (Map.get positive_encoding v (Scc.comp_of r)) as [b|] eqn:Hv;
        [|discriminate].
      destruct (Pos.eqb a b) eqn:Hne; [discriminate|].
      inversion Hpair; subst a b. split; [reflexivity|].
      split; [now apply Pos.eqb_neq|]. exists e, v. auto.
    + intros [Heq [Hne [e [v [He Hv]]]]]. inversion Heq; subst a.
      exists (e, v). split; [exact He|]. cbn [snd].
      rewrite Hv, (proj2 (Pos.eqb_neq i j) Hne). reflexivity.
  - split; [contradiction|intros [Hfalse _]; discriminate].
Qed.

(** Exact ownership locates each binding in its actual one-based component. *)
Theorem owner_member {V E} (p : Prepared.t V E) scope roots r u i :
  Scc.exact p scope roots r ->
  Map.get positive_encoding u (Scc.comp_of r) = Some i ->
    In u (concat (Scc.components r)) /\
      (Pos.to_nat i <= length (Scc.components r))%nat.
Proof.
  intros Hexact Howner.
  apply (Scc.owners_exact _ _ _ _ Hexact) in Howner.
  destruct Howner as [c [Hnth Hu]]. split.
  - apply in_concat. exists c. split; [now apply nth_error_In in Hnth|exact Hu].
  - pose proof (proj1 (nth_error_Some (Scc.components r) (Nat.pred (Pos.to_nat i)))
      ltac:(rewrite Hnth; discriminate)) as Hlength.
    pose proof (Pos2Nat.is_pos i). lia.
Qed.

Local Lemma member_valid {V E} (p : Prepared.t V E) scope roots r u :
  Scc.exact p scope roots r -> In u (concat (Scc.components r)) ->
    Prepared.valid_id p u.
Proof.
  intros Hexact Hu. apply (Scc.partition_complete _ _ _ _ Hexact) in Hu.
  destruct Hu as [root [es [_ Hpath]]]. induction Hpath; assumption.
Qed.

(** Cross-edge collection is exact for arbitrary scopes whenever the supplied partition is exact. *)
Theorem cross_edges_spec {V E} (p : Prepared.t V E) scope roots r i j :
  Prepared.ready p -> Scc.exact p scope roots r ->
  (In (i, j) (cross_edges p r) <->
    i <> j /\ exists u e v, Prepared.arc p u e v /\
      Map.get positive_encoding u (Scc.comp_of r) = Some i /\
      Map.get positive_encoding v (Scc.comp_of r) = Some j).
Proof.
  intros Hready Hexact. rewrite cross_edges_equation, in_flat_map. split.
  - intros [u [Hu Hpair]]. apply vertex_spec in Hpair.
    destruct Hpair as [Hi [Hne [e [v [He Hj]]]]].
    split; [exact Hne|]. exists u, e, v. split; [|auto].
    exact (proj1 (SearchInvariant.successor_arc p u e v Hready
      (member_valid p scope roots r u Hexact Hu) He)).
  - intros [Hne [u [e [v [Harc [Hi Hj]]]]]].
    exists u. split.
    + exact (proj1 (owner_member p scope roots r u i Hexact Hi)).
    + apply vertex_spec. split; [exact Hi|]. split; [exact Hne|].
      exists e, v. split; [now apply SearchInvariant.arc_successor|exact Hj].
Qed.

(** Set deduplication retains exactly targets that were absent from the initial seen set. *)
Theorem unique_spec xs seen j :
  FinSet.wf positive_encoding seen ->
  (In j (unique xs seen) <->
    In j (map snd xs) /\ FinSet.mem positive_encoding j seen = false).
Proof.
  revert seen. induction xs as [|[i k] rest IH]; intros seen Hwf;
    rewrite unique_equation; cbn [map snd In].
  - tauto.
  - destruct (FinSet.mem positive_encoding k seen) eqn:Hseen.
    + rewrite IH by exact Hwf. intuition congruence.
    + cbn [In]. rewrite IH by now apply FinSet.wf_add.
      rewrite FinSet.mem_add by exact Hwf.
      destruct (eqb_spec positive_encoding positive_encoding_laws j k) as [Heq|Hne].
      * subst j. rewrite Hseen. cbn. tauto.
      * destruct (FinSet.mem positive_encoding j seen); cbn; intuition congruence.
Qed.

(** Deduplication produces a duplicate-free successor list for every well-formed seen set. *)
Theorem unique_nodup xs seen :
  FinSet.wf positive_encoding seen -> NoDup (unique xs seen).
Proof.
  revert seen. induction xs as [|[i j] rest IH]; intros seen Hwf; rewrite unique_equation.
  - constructor.
  - destruct (FinSet.mem positive_encoding j seen); [now apply IH|].
    constructor; [|apply IH; now apply FinSet.wf_add].
    rewrite unique_spec by now apply FinSet.wf_add.
    rewrite FinSet.mem_add, eqb_refl by exact Hwf. cbn. intuition discriminate.
Qed.

(** Explicit row construction always returns canonical map storage. *)
Theorem rows_wf cs i buckets : Map.wf positive_encoding (rows cs i buckets).
Proof.
  revert i. induction cs as [|c rest IH]; intro i; rewrite rows_equation.
  - apply Map.wf_empty.
  - apply Map.wf_set, IH.
Qed.

(** Row lookup is present precisely on the contiguous range of actual component indices. *)
Theorem rows_spec cs start buckets i xs :
  Map.get positive_encoding i (rows cs start buckets) = Some xs <->
    (Pos.to_nat start <= Pos.to_nat i < Pos.to_nat start + length cs)%nat /\
    xs = unique (Index.find positive_encoding i buckets) FinSet.empty.
Proof.
  revert start. induction cs as [|c rest IH]; intro start; rewrite rows_equation.
  - rewrite Map.get_empty. cbn [length]. split; [discriminate|intros [Hfalse _]; lia].
  - rewrite Map.get_set by apply rows_wf.
    destruct (eqb_spec positive_encoding positive_encoding_laws i start) as [->|Hne].
    + split.
      * intro Heq. inversion Heq; subst xs. split; [cbn [length]; lia|reflexivity].
      * intros [_ ->]. reflexivity.
    + rewrite IH, Pos2Nat.inj_succ. cbn [length].
      assert (Hnat : Pos.to_nat i <> Pos.to_nat start) by
        (intro Heq; apply Hne; now apply Pos2Nat.inj).
      split; intros [Hrange Hxs]; split; [lia|exact Hxs|lia|exact Hxs].
Qed.

(** A grouped row contains precisely the target endpoints paired with its source index. *)
Theorem grouped_members es i j :
  In j (unique (Index.find positive_encoding i
    (Index.group_by positive_encoding fst es)) FinSet.empty) <-> In (i, j) es.
Proof.
  rewrite unique_spec by apply FinSet.wf_empty.
  rewrite FinSet.mem_empty, Index.find_group_by, in_map_iff. split.
  - intros [[[a b] [Heq Hin]] _]. cbn [snd] in Heq. subst b.
    apply filter_In in Hin. destruct Hin as [Hin Hsame].
    apply (eqb_true_iff positive_encoding positive_encoding_laws) in Hsame.
    cbn [fst] in Hsame. now subst a.
  - intro Hin. split; [|reflexivity]. exists (i, j). split; [reflexivity|].
    apply filter_In. split; [exact Hin|apply eqb_refl].
Qed.

(** Condensation preserves the SCC count and has exactly the distinct cross-component successors. *)
Theorem condensation_correct {V E} (p : Prepared.t V E) scope roots r :
  Prepared.ready p -> Scc.exact p scope roots r ->
    Condensation.exact p r (of_scc p scope r).
Proof.
  intros Hready Hexact. rewrite of_scc_equation. constructor.
  - reflexivity.
  - apply rows_wf.
  - intros i xs Hget. apply rows_spec in Hget. cbn in Hget |- *. lia.
  - intros i xs Hget. apply rows_spec in Hget. destruct Hget as [_ ->].
    apply unique_nodup, FinSet.wf_empty.
  - intros i j. split.
    + intros [xs [Hget Hin]]. apply rows_spec in Hget. destruct Hget as [_ ->].
      apply grouped_members in Hin. now apply (cross_edges_spec p scope roots r i j).
    + intro Hedge. pose proof Hedge as Hpair.
      apply (proj2 (cross_edges_spec p scope roots r i j Hready Hexact)) in Hpair.
      destruct Hedge as [_ [u [e [v [_ [Hi _]]]]]].
      exists (unique (Index.find positive_encoding i
        (Index.group_by positive_encoding fst (cross_edges p r))) FinSet.empty).
      split; [|now apply grouped_members].
      apply rows_spec. split; [|reflexivity].
      pose proof (proj2 (owner_member p scope roots r u i Hexact Hi)).
      pose proof (Pos2Nat.is_pos i). cbn. lia.
Qed.

(** Every condensation successor strictly decreases the SCC's reverse-topological index. *)
Theorem successor_decreases {V E} (p : Prepared.t V E) scope roots r i j xs :
  Prepared.ready p -> Scc.exact p scope roots r ->
  Map.get positive_encoding i (Condensation.succs (of_scc p scope r)) = Some xs ->
  In j xs -> (j < i)%positive.
Proof.
  intros Hready Hexact Hget Hin.
  pose proof (condensation_correct p scope roots r Hready Hexact) as Hcondensation.
  destruct (proj1 (Condensation.successors_exact _ _ _ Hcondensation i j)
    (ex_intro _ xs (conj Hget Hin))) as [Hne [u [e [v [Harc [Hi Hj]]]]]].
  exact (Scc.reverse_topological _ _ _ _ Hexact u e v i j Harc Hi Hj Hne).
Qed.

(** A nonempty condensation walk cannot return to its starting index. *)
Theorem condensation_acyclic {V E} (p : Prepared.t V E) scope roots r :
  Prepared.ready p -> Scc.exact p scope roots r ->
  forall i,
    ~ clos_trans positive
      (fun a b => exists xs,
        Map.get positive_encoding a (Condensation.succs (of_scc p scope r)) = Some xs /\
        In b xs) i i.
Proof.
  intros Hready Hexact i Hcycle.
  assert (Hdecreases : forall a b,
    clos_trans positive
      (fun a b => exists xs,
        Map.get positive_encoding a (Condensation.succs (of_scc p scope r)) = Some xs /\
        In b xs) a b -> (b < a)%positive).
  { intros a b Hpath. induction Hpath as [a b [xs [Hget Hin]]|a b c Hab IHfirst Hbc IHlast].
    - eapply successor_decreases; eassumption.
    - eapply Pos.lt_trans; eassumption. }
  exact (Pos.lt_irrefl i (Hdecreases i i Hcycle)).
Qed.

End Condense.
