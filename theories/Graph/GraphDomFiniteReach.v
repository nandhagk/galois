(** * Original-ID materialization of indexed finite reachability

    A normalized view is reused while each query materializes the existing kernel's visited names.
    For example, a blocked query returns canonical original IDs without leaking normalized dense IDs.
    Builds on: GraphDomFiniteTransport and public set extensionality. *)

From Stdlib Require Import List Bool PArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet.
From Galois.Graph Require Import GraphModel GraphPrepared GraphSearchSpec GraphReach
  GraphDomFiniteView GraphDomFiniteSearch GraphDomFiniteTransport.
Import Cost.Notations.

Module DomFiniteReach.

(** Each query uses one existing indexed search and charges all inverse conversion and set insertion work. *)
Definition reach_c {E} (q : Prepared.t positive E) scope :=
  let* result := DomFiniteSearch.run_c q scope in
  let* names := Prepared.present_c (Prepared.name_of_c q) (Search.preorder result) in
  FinSet.of_list_c positive_encoding names.

(** Materialization uses exactly the actual discovered names and constructs canonical storage. *)
Theorem reach_equation {E} (q : Prepared.t positive E) scope :
  Cost.value (reach_c q scope) =
    FinSet.of_list positive_encoding
      (Prepared.present (Prepared.name_of q) (Search.preorder (DomFiniteSearch.run q scope))).
Proof.
  unfold reach_c. rewrite !Cost.value_bind, Prepared.present_c_value. reflexivity.
Qed.

(** Materialized sets have valid storage independently of view readiness. *)
Theorem reach_wf {E} (q : Prepared.t positive E) scope :
  FinSet.wf positive_encoding (Cost.value (reach_c q scope)).
Proof.
  rewrite reach_equation. apply FinSet.wf_of_list.
Qed.

(** A ready dictionary materializes the same original-ID membership as its charged indexed query. *)
Theorem reach_member {E} (q : Prepared.t positive E) scope v :
  Prepared.ready q ->
  FinSet.mem positive_encoding v (Cost.value (reach_c q scope)) =
    Cost.value (DomFiniteSearch.member_c q (DomFiniteSearch.run q scope) v).
Proof.
  intro Hready. rewrite reach_equation, FinSet.mem_of_list.
  apply Bool.eq_true_iff_eq. rewrite existsb_exists.
  assert (Hnames :
    (exists x, In x (Prepared.present (Prepared.name_of q)
      (Search.preorder (DomFiniteSearch.run q scope))) /\ eqb positive_encoding v x = true) <->
    exists i, In i (Search.preorder (DomFiniteSearch.run q scope)) /\
      Prepared.id_of q v = Some i).
  { split.
    - intros [x [Hin Heq]]. apply (eqb_true_iff _ positive_encoding_laws) in Heq. subst x.
      apply Prepared.present_spec in Hin. destruct Hin as [i [Hi Hname]].
      exists i. split; [exact Hi|].
      exact (Prepared.id_of_name_of q i v (proj2 (proj2 Hready)) Hname).
    - intros [i [Hin Hi]]. exists v. split; [|apply eqb_refl].
      apply Prepared.present_spec. exists i. split; [exact Hin|].
      exact (Prepared.name_of_id_of q v i (proj2 (proj2 Hready)) Hi). }
  rewrite Hnames.
  change ((exists i, In i (Search.preorder (DomFiniteSearch.run q scope)) /\
    Prepared.id_of q v = Some i) <->
    Cost.value
      (match Prepared.id_of q v with
      | None => Cost.ret false
      | Some i => FinSet.mem_c positive_encoding i (Search.visited (DomFiniteSearch.run q scope))
      end) = true).
  destruct (Prepared.id_of q v) as [i|] eqn:Hi.
  - change ((exists j, In j (Search.preorder (DomFiniteSearch.run q scope)) /\ Some i = Some j) <->
      FinSet.mem positive_encoding i (Search.visited (DomFiniteSearch.run q scope)) = true).
    rewrite (Search.visited_complete _ _ _ _ (DomFiniteSearch.run_exact q scope Hready)).
    split; [intros [j [Hj Heq]]; now injection Heq as <-|intro Hin; now exists i].
  - split; [intros [i [_ Hfalse]]; discriminate|discriminate].
Qed.

(** The actual indexed query returns exactly the raw compatibility set for every computational input. *)
Theorem reach_value {V E} (p : Prepared.t V E) roots scope :
  Cost.value (reach_c (DomFiniteView.prepared p roots) scope) = Reach.set p scope roots.
Proof.
  apply (FinSet.ext positive_encoding positive_encoding_laws).
  - apply reach_wf.
  - apply Reach.set_wf.
  - intro v. rewrite reach_member by apply DomFiniteView.prepared_ready.
    apply DomFiniteTransport.member_value.
Qed.

End DomFiniteReach.
