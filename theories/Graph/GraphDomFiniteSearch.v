(** * Reusable indexed searches of normalized finite views

    Scope translation charges admission and ID conversion before calling the existing search kernel.
    For example, a blocked raw ID is interpreted in the normalized dictionary's own dense ID space.
    Builds on: GraphDomFiniteView, GraphSearch and the public exactness contract. *)

From Stdlib Require Import List Bool PArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor GraphSearchSpec
  GraphSearch GraphSearchExact GraphDomFiniteView.
Import Cost.Notations.

Module DomFiniteSearch.

(** Finite translation retains exactly the dense IDs of admitted names in the normalized graph. *)
Definition translate_c {E} (q : Prepared.t positive E) scope :=
  let* ids := Prepared.present_c (fun v =>
    let* allowed := Scope.admits_c scope v in
    if allowed then Prepared.id_of_c q v else Cost.ret None) (Graph.nodes (Prepared.graph q)) in
  let* allowed := FinSet.of_list_c positive_encoding ids in
  Cost.ret (Scope.Make FinSet.empty (Some allowed)).

Definition translate {E} (q : Prepared.t positive E) scope :=
  Cost.value (translate_c q scope).

(** Translation's equation exposes the same admission decisions and successful ID conversions. *)
Theorem translate_equation {E} (q : Prepared.t positive E) scope :
  translate q scope =
    Scope.Make FinSet.empty
      (Some (FinSet.of_list positive_encoding
        (Prepared.present (fun v => if Scope.admits scope v then Prepared.id_of q v else None)
          (Graph.nodes (Prepared.graph q))))).
Proof.
  unfold translate, translate_c. rewrite Cost.value_bind, Prepared.present_c_value.
  assert (Hids :
    Prepared.present (fun x =>
      Cost.value (let* allowed := Scope.admits_c scope x in
        if allowed then Prepared.id_of_c q x else Cost.ret None))
      (Graph.nodes (Prepared.graph q)) =
    Prepared.present (fun v => if Scope.admits scope v then Prepared.id_of q v else None)
      (Graph.nodes (Prepared.graph q))).
  { apply Prepared.present_ext. intro v. rewrite Cost.value_bind.
    fold (Scope.admits scope v). destruct (Scope.admits scope v); reflexivity. }
  rewrite Hids. reflexivity.
Qed.

Local Lemma names_injective {E} (q : Prepared.t positive E) :
  Prepared.ready q ->
  forall u v i, Prepared.id_of q u = Some i -> Prepared.id_of q v = Some i -> u = v.
Proof.
  intros Hready u v i Hu Hv.
  pose proof (Prepared.name_of_id_of q u i (proj2 (proj2 Hready)) Hu).
  pose proof (Prepared.name_of_id_of q v i (proj2 (proj2 Hready)) Hv). congruence.
Qed.

(** Admission commutes with scope translation at every actual normalized dictionary binding. *)
Theorem translated_admits {E} (q : Prepared.t positive E) scope v i :
  Prepared.ready q -> Prepared.id_of q v = Some i ->
  Scope.admits (translate q scope) i = Scope.admits scope v.
Proof.
  intros Hready Hi. rewrite translate_equation, Scope.admits_equation.
  cbn [Scope.blocked Scope.within]. rewrite FinSet.mem_empty.
  cbn [negb andb]. rewrite FinSet.mem_of_list.
  apply Bool.eq_true_iff_eq. rewrite existsb_exists. split.
  - intros [j [Hin Heq]]. apply (eqb_true_iff _ positive_encoding_laws) in Heq.
    subst j. apply Prepared.present_spec in Hin. destruct Hin as [u [Hu Huid]].
    destruct (Scope.admits scope u) eqn:Hallowed; [|discriminate].
    assert (u = v) by (eapply names_injective; eassumption).
    now subst u.
  - intro Hallowed. exists i. split; [|apply eqb_refl].
    apply Prepared.present_spec. exists v. split.
    + apply (Prepared.ids_domain q (proj2 (proj2 Hready))). now exists i.
    + now rewrite Hallowed.
Qed.

(** Every query reuses its supplied normalized prepared view and the one existing indexed kernel. *)
Definition run_c {E} (q : Prepared.t positive E) scope :=
  let* translated := translate_c q scope in
  Cost.map fst (SearchRun.run_c q Visitor.noop translated (Prepared.entry_ids q) tt).

Definition run {E} (q : Prepared.t positive E) scope := Cost.value (run_c q scope).

(** The result is the actual search of the translated scope in the same supplied view. *)
Theorem run_equation {E} (q : Prepared.t positive E) scope :
  run q scope =
    fst (Cost.value
      (SearchRun.run_c q Visitor.noop (translate q scope) (Prepared.entry_ids q) tt)).
Proof.
  reflexivity.
Qed.

(** Ready indexed views discharge search exactness independently of any original raw graph law. *)
Theorem run_exact {E} (q : Prepared.t positive E) scope :
  Prepared.ready q ->
  Search.exact q (translate q scope) (Prepared.entry_ids q) (run q scope).
Proof.
  intro Hready. rewrite run_equation. now apply SearchExact.run_exact.
Qed.

(** Normalization discharges the kernel's readiness and fuel duties for arbitrary original records. *)
Theorem normalized_run_exact {V E} (p : Prepared.t V E) roots scope :
  Search.exact (DomFiniteView.prepared p roots)
    (translate (DomFiniteView.prepared p roots) scope)
    (Prepared.entry_ids (DomFiniteView.prepared p roots))
    (run (DomFiniteView.prepared p roots) scope).
Proof.
  apply run_exact. apply DomFiniteView.prepared_ready.
Qed.

(** Original-ID membership pays its actual forward lookup and selected dense-set query. *)
Definition member_c {E L} (q : Prepared.t positive E) (r : Search.result L) v :=
  let* id := Prepared.id_of_c q v in
  match id with
  | None => Cost.ret false
  | Some id => FinSet.mem_c positive_encoding id (Search.visited r)
  end.

(** A present normalized binding makes indexed membership equivalent to translated scoped reachability. *)
Theorem member_reachable {E} (q : Prepared.t positive E) scope v i :
  Prepared.ready q -> Prepared.id_of q v = Some i ->
  (Cost.value (member_c q (run q scope) v) = true <->
    Search.scoped_reachable q (translate q scope) (Prepared.entry_ids q) i).
Proof.
  intros Hready Hi.
  change (Cost.value
    (match Prepared.id_of q v with
    | None => Cost.ret false
    | Some id => FinSet.mem_c positive_encoding id (Search.visited (run q scope))
    end) = true <->
      Search.scoped_reachable q (translate q scope) (Prepared.entry_ids q) i).
  rewrite Hi.
  change (FinSet.mem positive_encoding i (Search.visited (run q scope)) = true <->
    Search.scoped_reachable q (translate q scope) (Prepared.entry_ids q) i).
  rewrite (Search.visited_complete _ _ _ _ (run_exact q scope Hready)),
    (Search.pre_complete _ _ _ _ (run_exact q scope Hready)). reflexivity.
Qed.

End DomFiniteSearch.
