(** * External dominator-candidate certification

    Backend records compute parent data and certification handles external candidates.
    For example, a line candidate that parents the tail directly at the entry is rejected.
    Builds on: GraphCheckDom, GraphDomSpec and BaseCertify. *)

From Stdlib Require Import List Bool PArith NArith.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet BaseCertify.
From Galois.Graph Require Import GraphModel GraphPrepared GraphDomSpec GraphCheckDom
  GraphDomSemi GraphDomLt GraphDomNca GraphDomNumber GraphDomPath GraphDomCut
  GraphDomLtProof GraphDomNcaProof GraphDomOutput GraphReach GraphFrontierSweep GraphDomFastCheck.
Import Cost.Notations.

Module DomBackend.

(** Computational backends select a finisher independently of any semantic or readiness evidence. *)
Record backend := Backend {
  finish_c : forall V E, DomSemi.semi V E -> Cost.t (Map.t positive positive)
}.
Arguments finish_c _ {V E}.

Definition lt := Backend (@DomLt.finish_c).
Definition semi_nca := Backend (@DomNca.finish_c).

(** Backend laws certify storage on raw inputs and exact strict-cut parents on the actual ready prologue. *)
Record backend_laws (b : backend) : Prop := {
  finish_storage : forall V E (shared : DomSemi.semi V E),
    Map.wf positive_encoding (Cost.value (finish_c b shared));
  finish_sound : forall V E (p : Prepared.t V E), Prepared.ready p ->
    forall v a, Map.get positive_encoding v (Cost.value (finish_c b (DomSemi.compute p))) = Some a ->
      DomPath.vertex (DomSemi.compute p) v /\ v <> 1%positive /\ DomCut.parent_property p v a;
  finish_total : forall V E (p : Prepared.t V E), Prepared.ready p ->
    forall v, DomPath.vertex (DomSemi.compute p) v -> v <> 1%positive ->
      exists a, Map.get positive_encoding v (Cost.value (finish_c b (DomSemi.compute p))) = Some a
}.

(** The actual LT bucket and correction proofs establish every builtin LT backend law. *)
Theorem lt_laws : backend_laws lt.
Proof.
  constructor.
  - intros V E shared. apply DomLt.finish_wf.
  - intros V E p Hready. exact (proj1 (DomLtProof.finish_parents p Hready)).
  - intros V E p Hready. exact (proj2 (DomLtProof.finish_parents p Hready)).
Qed.

(** The actual Semi-NCA threshold-walk proof establishes every builtin Semi-NCA backend law. *)
Theorem semi_nca_laws : backend_laws semi_nca.
Proof.
  constructor.
  - intros V E shared. apply DomNca.finish_wf.
  - intros V E p Hready. exact (proj1 (DomNcaProof.finish_parents p Hready)).
  - intros V E p Hready. exact (proj2 (DomNcaProof.finish_parents p Hready)).
Qed.

(** Every lawful custom finisher agrees with actual LT by independently proved strict-parent uniqueness. *)
Theorem finish_agrees_lt {V E} b (p : Prepared.t V E) :
  backend_laws b -> Prepared.ready p ->
  Cost.value (finish_c b (DomSemi.compute p)) = DomLt.finish (DomSemi.compute p).
Proof.
  intros Hlaws Hready.
  destruct (DomLtProof.finish_parents p Hready) as [Hsound Htotal].
  apply (Map.ext positive_encoding positive_encoding_laws).
  - exact (finish_storage _ Hlaws V E (DomSemi.compute p)).
  - apply DomLt.finish_wf.
  - intro v. destruct (Map.get positive_encoding v (Cost.value (finish_c b (DomSemi.compute p))))
      as [a|] eqn:Hget.
    + destruct (finish_sound _ Hlaws V E p Hready v a Hget) as [Hv [Hnonroot Hproperty]].
      destruct (Htotal v Hv Hnonroot) as [parent Hparent]. rewrite Hparent.
      f_equal. apply (DomCut.parent_unique p v a parent Hready Hproperty).
      exact (proj2 (proj2 (Hsound v parent Hparent))).
    + destruct (Map.get positive_encoding v (DomLt.finish (DomSemi.compute p))) as [a|] eqn:Hlt;
        [|reflexivity].
      destruct (Hsound v a Hlt) as [Hv [Hnonroot Hproperty]].
      destruct (finish_total _ Hlaws V E p Hready v Hv Hnonroot) as [parent Hparent].
      congruence.
Qed.

(** Parent computation shares one prologue and erases through its own constructed inverse map. *)
Definition parents_c {V E} (b : backend) (p : Prepared.t V E) :=
  let* shared := DomSemi.semi_c p in
  Cost.step ;;
  let* ranked_parents := finish_c b shared in
  DomSemi.erase_c shared ranked_parents.

Definition parents {V E} b (p : Prepared.t V E) := Cost.value (parents_c b p).

(** The returned map is the selected finisher's actual output after shared-prologue erasure. *)
Theorem parents_equation {V E} b (p : Prepared.t V E) :
  parents b p =
    DomSemi.erase (DomSemi.compute p) (Cost.value (finish_c b (DomSemi.compute p))).
Proof.
  reflexivity.
Qed.

(** Parent computation always constructs canonical storage without assuming backend correctness. *)
Theorem parents_wf {V E} b (p : Prepared.t V E) :
  Map.wf positive_encoding (parents b p).
Proof.
  rewrite parents_equation. apply DomSemi.erase_wf.
Qed.

(** Tree construction shares the parent prologue and then searches only the resulting parent forest. *)
Definition compute_c {V E} (b : backend) (p : Prepared.t V E) :=
  let* shared := DomSemi.semi_c p in
  Cost.step ;;
  let* ranked_parents := finish_c b shared in
  let* parents := DomSemi.erase_c shared ranked_parents in
  let* ranks := rev_c (DomSemi.reverse_order (DomSemi.ranked shared)) in
  let* live := Prepared.present_c
    (fun rank => Map.get_c positive_encoding rank
      (DomSemi.real_ids (DomSemi.ranked shared))) ranks in
  DomNumber.of_parents_c live parents.

Definition compute {V E} b (p : Prepared.t V E) := Cost.value (compute_c b p).

(** Tree construction numbers the actual erased parents using the shared discovery-order real IDs. *)
Theorem compute_equation {V E} b (p : Prepared.t V E) :
  compute b p =
    let shared := DomSemi.compute p in
    let ranked_parents := Cost.value (finish_c b shared) in
    let parents := DomSemi.erase shared ranked_parents in
    let ranks := rev (DomSemi.reverse_order (DomSemi.ranked shared)) in
    let live := Prepared.present
      (fun rank => Map.get positive_encoding rank
        (DomSemi.real_ids (DomSemi.ranked shared))) ranks in
    DomNumber.of_parents live parents.
Proof.
  unfold compute, compute_c. autorewrite with galois_cost.
  rewrite Prepared.present_c_value.
  reflexivity.
Qed.

(** Numbering retains the map actually produced by the selected finisher and its erasure. *)
Theorem compute_parents {V E} b (p : Prepared.t V E) :
  Dom.idom (compute b p) = parents b p.
Proof.
  reflexivity.
Qed.

(** Tree construction establishes canonical map storage for arbitrary computational backends. *)
Theorem compute_maps_wf {V E} b (p : Prepared.t V E) :
  Map.wf positive_encoding (Dom.idom (compute b p)) /\
    Map.wf positive_encoding (Dom.tin (compute b p)) /\
    Map.wf positive_encoding (Dom.tout (compute b p)).
Proof.
  rewrite compute_equation. apply DomNumber.of_parents_wf. apply DomSemi.erase_wf.
Qed.

(** Every lawful backend's actual shared erasure and forest numbering form an exact public tree. *)
Theorem compute_exact {V E} b (p : Prepared.t V E) :
  backend_laws b -> Prepared.ready p -> Dom.exact p (compute b p).
Proof.
  intros Hlaws Hready. rewrite compute_equation. cbv zeta.
  rewrite (finish_agrees_lt b p Hlaws Hready).
  exact (DomOutput.numbered_exact p Hready).
Qed.

(** Lawful backend selection changes neither the actual parent map nor its actual forest annotations. *)
Theorem lawful_backends_agree {V E} first second (p : Prepared.t V E) :
  backend_laws first -> backend_laws second -> Prepared.ready p ->
  compute first p = compute second p.
Proof.
  intros Hfirst Hsecond Hready. rewrite !compute_equation. cbv zeta.
  rewrite (finish_agrees_lt first p Hfirst Hready), (finish_agrees_lt second p Hsecond Hready).
  reflexivity.
Qed.

(** The actual LT and Semi-NCA public trees agree completely on every ready input. *)
Theorem backends_agree {V E} (p : Prepared.t V E) :
  Prepared.ready p -> compute lt p = compute semi_nca p.
Proof.
  intro Hready. exact (lawful_backends_agree lt semi_nca p lt_laws semi_nca_laws Hready).
Qed.

(** Accepted external parents are numbered through charged reachability, enumeration and forest annotation. *)
Definition checked_candidate_c {V E} (p : Prepared.t V E) m :=
  let* reachable := FrontierSweep.reach_c p Reach.unrestricted (Prepared.entry_ids p) in
  let* listed := FinSet.elements_c reachable in
  DomNumber.of_parents_c listed m.

(** The accepted candidate keeps its actual parent map and enumerates the actual public reachable IDs. *)
Theorem checked_candidate_value {V E} (p : Prepared.t V E) m :
  Cost.value (checked_candidate_c p m) =
    DomNumber.of_parents
      (FinSet.elements (Reach.set p Reach.unrestricted (Prepared.entry_ids p))) m.
Proof.
  unfold checked_candidate_c. autorewrite with galois_cost.
  now rewrite FrontierSweep.reach_value.
Qed.

(** Boolean acceptance certifies charged candidate numbering only with separate parent-storage validity. *)
Theorem checked_candidate_exact {V E} (p : Prepared.t V E) m :
  Prepared.ready p -> Map.wf positive_encoding m -> DomCheck.check p m = true ->
  Dom.exact p (Cost.value (checked_candidate_c p m)).
Proof.
  intros Hready Hmap Hcheck. rewrite checked_candidate_value.
  pose proof (DomCheck.check_sound p m Hready Hmap Hcheck) as Htree.
  pose proof (DomOutput.renumber_exact p (DomCheck.of_parents p m)
    (FinSet.elements (Reach.set p Reach.unrestricted (Prepared.entry_ids p)))
    Hready Htree (FinSet.elements_nodup positive_encoding _ (Reach.set_wf p _ _))
    (fun v => DomOutput.reachable_ids_spec p v Hready)) as Hresult.
  now rewrite DomCheck.of_parents_idom in Hresult.
Qed.

(** Rejection runs the actual selected backend, retaining its full prologue, finisher and annotation work. *)
Definition compute_checked_c {V E} b (p : Prepared.t V E) (candidate : Dom.tree) :=
  let* accepted := DomFastCheck.check_c p (Dom.idom candidate) in
  if accepted then checked_candidate_c p (Dom.idom candidate) else compute_c b p.

(** Checked computation chooses actual charged candidate annotation or the actual selected fallback. *)
Theorem compute_checked_value {V E} b (p : Prepared.t V E) candidate :
  Cost.value (compute_checked_c b p candidate) =
    if DomCheck.check p (Dom.idom candidate)
    then Cost.value (checked_candidate_c p (Dom.idom candidate)) else compute b p.
Proof.
  unfold compute_checked_c. rewrite Cost.value_bind, DomFastCheck.check_c_value.
  destruct (DomCheck.check p (Dom.idom candidate)); reflexivity.
Qed.

(** Checked computation is exact for lawful fallback backends and representation-valid external parents. *)
Theorem compute_checked_exact {V E} b (p : Prepared.t V E) candidate :
  backend_laws b -> Prepared.ready p -> Map.wf positive_encoding (Dom.idom candidate) ->
  Dom.exact p (Cost.value (compute_checked_c b p candidate)).
Proof.
  intros Hlaws Hready Hmap. rewrite compute_checked_value.
  destruct (DomCheck.check p (Dom.idom candidate)) eqn:Hcheck.
  - exact (checked_candidate_exact p _ Hready Hmap Hcheck).
  - exact (compute_exact b p Hlaws Hready).
Qed.

(** Certification refines the single charged computation using explicit input and fallback duties. *)
Definition compute_checked {V E} b (p : Prepared.t V E) candidate
    (Hlaws : backend_laws b) (Hready : Prepared.ready p)
    (Hmap : Map.wf positive_encoding (Dom.idom candidate))
    : Cost.t {result : Dom.tree | Dom.exact p result} :=
  Cost.refine (compute_checked_c b p candidate)
    (compute_checked_exact b p candidate Hlaws Hready Hmap).

(** Erasing the certified proof returns the same actual checked computation's tree. *)
Theorem compute_checked_projection {V E} b (p : Prepared.t V E) candidate Hlaws Hready Hmap :
  proj1_sig (Cost.value (compute_checked b p candidate Hlaws Hready Hmap)) =
    Cost.value (compute_checked_c b p candidate).
Proof.
  reflexivity.
Qed.

(** The certified computation carries exactness for its actual accepted or fallback tree. *)
Theorem compute_checked_result_exact {V E} b (p : Prepared.t V E) candidate Hlaws Hready Hmap :
  Dom.exact p (proj1_sig (Cost.value (compute_checked b p candidate Hlaws Hready Hmap))).
Proof.
  exact (proj2_sig (Cost.value (compute_checked b p candidate Hlaws Hready Hmap))).
Qed.

(** Accepted parents select the charged canonical annotation without running the fallback. *)
Theorem compute_checked_accepted {V E} b (p : Prepared.t V E) candidate :
  DomCheck.check p (Dom.idom candidate) = true ->
  compute_checked_c b p candidate =
    (DomFastCheck.check_c p (Dom.idom candidate) ;;
      checked_candidate_c p (Dom.idom candidate)).
Proof.
  intro Hcheck. unfold compute_checked_c.
  apply Cost.ext.
  - rewrite !Cost.value_bind, DomFastCheck.check_c_value, Hcheck. reflexivity.
  - rewrite !Cost.ticks_bind, DomFastCheck.check_c_value, Hcheck. reflexivity.
Qed.

(** Rejection retains one checker followed by the same selected backend computation. *)
Theorem compute_checked_rejected {V E} b (p : Prepared.t V E) candidate :
  DomCheck.check p (Dom.idom candidate) = false ->
  compute_checked_c b p candidate =
    (DomFastCheck.check_c p (Dom.idom candidate) ;; compute_c b p).
Proof.
  intro Hcheck. unfold compute_checked_c.
  apply Cost.ext.
  - rewrite !Cost.value_bind, DomFastCheck.check_c_value, Hcheck. reflexivity.
  - rewrite !Cost.ticks_bind, DomFastCheck.check_c_value, Hcheck. reflexivity.
Qed.

(** Candidate interval maps affect neither returned values nor charges at the checked boundary. *)
Theorem compute_checked_ignores_intervals {V E} b (p : Prepared.t V E) first second :
  Dom.idom first = Dom.idom second ->
  compute_checked_c b p first = compute_checked_c b p second.
Proof.
  intro Hparents. unfold compute_checked_c. now rewrite Hparents.
Qed.

(** Accepted-candidate accounting retains every reachability, enumeration and annotation charge. *)
Theorem checked_candidate_cost_equation {V E} (p : Prepared.t V E) m :
  Cost.ticks (checked_candidate_c p m) =
    (Cost.ticks (FrontierSweep.reach_c p Reach.unrestricted (Prepared.entry_ids p)) +
      Cost.ticks (FinSet.elements_c (Reach.set p Reach.unrestricted (Prepared.entry_ids p))) +
      Cost.ticks (DomNumber.of_parents_c
        (FinSet.elements (Reach.set p Reach.unrestricted (Prepared.entry_ids p))) m))%N.
Proof.
  unfold checked_candidate_c. rewrite !Cost.ticks_bind, FrontierSweep.reach_value.
  autorewrite with galois_cost. rewrite N.add_assoc. reflexivity.
Qed.

(** Checked accounting includes one actual checker and the full selected branch, including rejection fallback. *)
Theorem compute_checked_cost_equation {V E} b (p : Prepared.t V E) candidate :
  Cost.ticks (compute_checked_c b p candidate) =
    (Cost.ticks (DomFastCheck.check_c p (Dom.idom candidate)) +
      if DomCheck.check p (Dom.idom candidate)
      then Cost.ticks (checked_candidate_c p (Dom.idom candidate))
      else Cost.ticks (compute_c b p))%N.
Proof.
  unfold compute_checked_c. rewrite Cost.ticks_bind, DomFastCheck.check_c_value.
  destruct (DomCheck.check p (Dom.idom candidate)); reflexivity.
Qed.

(** Proof refinement retains the checker and every charge of the selected branch. *)
Theorem compute_checked_ticks {V E} b (p : Prepared.t V E) candidate Hlaws Hready Hmap :
  Cost.ticks (compute_checked b p candidate Hlaws Hready Hmap) =
    (Cost.ticks (DomFastCheck.check_c p (Dom.idom candidate)) +
      if DomCheck.check p (Dom.idom candidate)
      then Cost.ticks (checked_candidate_c p (Dom.idom candidate))
      else Cost.ticks (compute_c b p))%N.
Proof.
  unfold compute_checked. rewrite Cost.ticks_refine. apply compute_checked_cost_equation.
Qed.

(** A candidate's semantic certificate is about canonical numbering of its actual parent map. *)
Definition candidate_exact {V E} (p : Prepared.t V E) (m : Map.t positive positive) :=
  Dom.exact p (DomCheck.of_parents p m).

(** Certification receives storage validity separately from the boolean graph checks. *)
Definition accept {V E} (p : Prepared.t V E) (t : Dom.tree)
    (Hready : Prepared.ready p)
    (Hmap : Map.wf positive_encoding (Dom.idom t))
    : option {result : Dom.tree | Dom.exact p result} :=
  let candidate := exist (Map.wf positive_encoding) (Dom.idom t) Hmap in
  match certify
    (fun m => candidate_exact p (proj1_sig m))
    (fun m => DomCheck.check p (proj1_sig m))
    (fun m Hcheck => DomCheck.check_sound p (proj1_sig m) Hready (proj2_sig m) Hcheck)
    candidate with
  | Some certified =>
    Some (exist (Dom.exact p) (DomCheck.of_parents p (proj1_sig (proj1_sig certified)))
      (proj2_sig certified))
  | None => None
  end.

(** Rejected candidates return no certificate and do not turn storage evidence into graph evidence. *)
Theorem accept_rejected {V E} (p : Prepared.t V E) t Hready Hmap :
  DomCheck.check p (Dom.idom t) = false -> accept p t Hready Hmap = None.
Proof.
  intro Hreject. unfold accept. rewrite certify_equation. cbn [proj1_sig proj2_sig].
  destruct (Bool.bool_dec (DomCheck.check p (Dom.idom t)) true) as [Haccept|Haccept].
  - congruence.
  - reflexivity.
Qed.

(** Certification succeeds precisely when the actual candidate parent map passes the checker. *)
Theorem accept_some_iff {V E} (p : Prepared.t V E) t Hready Hmap :
  (exists result, accept p t Hready Hmap = Some result) <->
    DomCheck.check p (Dom.idom t) = true.
Proof.
  unfold accept. rewrite certify_equation. cbn [proj1_sig proj2_sig].
  destruct (Bool.bool_dec (DomCheck.check p (Dom.idom t)) true) as [Haccept|Haccept].
  - split; [intros _; exact Haccept|intros _; eexists; reflexivity].
  - split; [intros [result Hfalse]; discriminate|intro Hcheck; contradiction].
Qed.

(** An accepted certificate keeps the supplied parent map and replaces untrusted interval data. *)
Theorem accept_parents {V E} (p : Prepared.t V E) t Hready Hmap result :
  accept p t Hready Hmap = Some result -> Dom.idom (proj1_sig result) = Dom.idom t.
Proof.
  unfold accept. rewrite certify_equation. cbn [proj1_sig proj2_sig].
  destruct (Bool.bool_dec (DomCheck.check p (Dom.idom t)) true) as [Haccept|Haccept].
  - intro Heq. injection Heq as Heq. subst result.
    apply DomCheck.of_parents_idom.
  - discriminate.
Qed.

End DomBackend.
