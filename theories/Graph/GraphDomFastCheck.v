(** * Indexed independent dominance checking

    One normalized view serves all blocked searches and each bounded candidate chain is cached once.
    For example, early domain rejection avoids ancestry construction for unrelated stored bindings.
    Builds on: GraphDomFiniteReach, GraphDomAncestorIndex and the preserved raw checker. *)

From Stdlib Require Import List Bool PArith NArith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor GraphDomSpec GraphReach
  GraphCheckDom GraphCheckDomCost GraphDomFiniteView GraphDomFiniteReach GraphDomAncestorIndex.
Import Cost.Notations.

Module DomFastCheck.

Definition pair_c index avoiding d n :=
  let* ancestor := DomAncestorIndex.contains_c index d n in
  let* reachable := FinSet.mem_c positive_encoding n avoiding in
  Cost.ret (Bool.eqb ancestor (negb reachable)).

(** Every blocked query charges its singleton before reusing the same normalized prepared view. *)
Definition avoiding_c {E} (q : Prepared.t positive E) d :=
  let* blocked := FinSet.add_c positive_encoding d FinSet.empty in
  DomFiniteReach.reach_c q (Scope.Make blocked None).

(** The checker prepares one finite view, rejects bad domains or cycles early, and caches each raw chain. *)
Definition check_c {V E} (p : Prepared.t V E) parents :=
  let* q := DomFiniteView.prepare_c p (Prepared.entry_ids p) in
  let* seen := DomFiniteReach.reach_c q Reach.unrestricted in
  let* nodes := FinSet.elements_c seen in
  let* bindings := Map.elements_c parents in
  let* domains := forallb_c (DomCheckCost.binding_ok_c seen) bindings in
  if domains then
    let* size := Map.size_c parents in
    let* forests := forallb_c (DomCheckCost.ends_c (S size) parents) nodes in
    if forests then
      let* index := DomAncestorIndex.build_with_c size parents nodes in
      forallb_c (fun d =>
        let* avoiding := avoiding_c q d in
        forallb_c (pair_c index avoiding d) nodes) nodes
    else Cost.ret false
  else Cost.ret false.

(** Normalized blocked search materialization agrees with the raw closure on all computational inputs. *)
Theorem avoiding_value {V E} (p : Prepared.t V E) roots d :
  Cost.value (avoiding_c (DomFiniteView.prepared p roots) d) =
    Reach.set p (Reach.blocked d) roots.
Proof.
  unfold avoiding_c. rewrite Cost.value_bind. fold (FinSet.add positive_encoding d FinSet.empty).
  rewrite Reach.blocked_equation. apply DomFiniteReach.reach_value.
Qed.

Local Lemma forallb_on {A} (f g : A -> bool) xs :
  (forall x, In x xs -> f x = g x) -> forallb f xs = forallb g xs.
Proof.
  induction xs as [|x rest IH]; intro Hsame; [reflexivity|].
  cbn [forallb]. rewrite (Hsame x (or_introl eq_refl)).
  rewrite IH; [reflexivity|intros y Hy; apply Hsame; now right].
Qed.

Local Lemma pair_value parents nodes avoiding d n :
  In n nodes ->
  Cost.value (pair_c (DomAncestorIndex.build parents nodes) avoiding d n) =
    Bool.eqb (DomCheck.ancestor_b parents d n)
      (negb (FinSet.mem positive_encoding n avoiding)).
Proof.
  intro Hn. unfold pair_c. autorewrite with galois_cost.
  rewrite DomAncestorIndex.contains_value by exact Hn. reflexivity.
Qed.

(** Fast checking returns the preserved raw Boolean without readiness, storage or success premises. *)
Theorem check_c_value {V E} (p : Prepared.t V E) parents :
  Cost.value (check_c p parents) = DomCheck.check p parents.
Proof.
  unfold check_c. rewrite !Cost.value_bind.
  fold (DomFiniteView.prepared p (Prepared.entry_ids p)).
  rewrite DomFiniteReach.reach_value.
  fold (FinSet.elements (Reach.set p Reach.unrestricted (Prepared.entry_ids p))).
  fold (Map.elements parents).
  rewrite value_forallb_c.
  set (seen := Reach.set p Reach.unrestricted (Prepared.entry_ids p)).
  set (nodes := FinSet.elements seen).
  set (domains := forallb (fun binding =>
    Cost.value (DomCheckCost.binding_ok_c seen binding)) (Map.elements parents)).
  assert (Hdomains : domains = forallb (fun binding =>
    FinSet.mem positive_encoding (fst binding) seen &&
      FinSet.mem positive_encoding (snd binding) seen) (Map.elements parents)).
  { unfold domains. apply forallb_on. intros binding Hin. reflexivity. }
  rewrite DomCheck.check_equation. cbn zeta. fold seen nodes. rewrite <- Hdomains.
  destruct domains.
  - rewrite !Cost.value_bind. fold (Map.size parents).
    rewrite value_forallb_c.
    assert (Hforests : forallb (fun n =>
      Cost.value (DomCheckCost.ends_c (S (Map.size parents)) parents n)) nodes =
      forallb (DomCheck.ends (S (Map.size parents)) parents) nodes).
    { apply forallb_on. intros n Hn. apply DomCheckCost.ends_c_value. }
    rewrite Hforests.
    destruct (forallb (DomCheck.ends (S (Map.size parents)) parents) nodes).
    + rewrite Cost.value_bind, DomAncestorIndex.build_with_value, value_forallb_c.
      cbn [andb]. apply forallb_on. intros d Hd.
      rewrite Cost.value_bind, avoiding_value, value_forallb_c.
      apply forallb_on. intros n Hn. now apply pair_value.
    + reflexivity.
  - reflexivity.
Qed.

(** Indexed acceptance retains the separate candidate-storage and graph-readiness duties. *)
Theorem checked_exact {V E} (p : Prepared.t V E) parents :
  Prepared.ready p -> Map.wf positive_encoding parents ->
  Cost.value (check_c p parents) = true ->
  Dom.exact p (DomCheck.of_parents p parents).
Proof.
  intros Hready Hparents Hcheck.
  apply (DomCheck.check_sound p parents Hready Hparents).
  now rewrite <- check_c_value.
Qed.

(** Successful domain validation bounds actual candidate cardinality by live support before later checks. *)
Theorem domains_cardinality seen parents :
  FinSet.wf positive_encoding seen -> Map.wf positive_encoding parents ->
  Cost.value (forallb_c (DomCheckCost.binding_ok_c seen) (Map.elements parents)) = true ->
  (Map.size parents <= length (FinSet.elements seen))%nat.
Proof.
  intros Hseen Hparents Hdomains. rewrite value_forallb_c in Hdomains.
  apply (Map.size_support_bound positive_encoding positive_encoding_laws); [exact Hparents|].
  intros v u Hget.
  apply (Map.elements_spec positive_encoding positive_encoding_laws v u parents Hparents) in Hget.
  apply forallb_forall with (x := (v, u)) in Hdomains; [|exact Hget].
  change (FinSet.mem positive_encoding v seen && FinSet.mem positive_encoding u seen = true)
    in Hdomains.
  apply andb_true_iff in Hdomains.
  apply (FinSet.elements_spec positive_encoding positive_encoding_laws); [exact Hseen|].
  exact (proj1 Hdomains).
Qed.

End DomFastCheck.
