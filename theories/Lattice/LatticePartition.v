(** * Equality partitions with an unreachable bottom

    Representation-valid forests describe reached partitions in reverse equality inclusion.
    For example, joining a three-key class with a two-key class retains their shared equality.
    Builds on: BaseUnionFind, BaseIndex, BaseCode, LatticePartitionGroup and LatticeConcrete. *)

From Stdlib Require Import List Bool PArith NArith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseEq BaseCode BaseIndex BaseUnionFind.
From Galois.Lattice Require Import LatticeCore LatticeConcrete LatticeAdjoin LatticePartitionGroup.
Import List.ListNotations Cost.Notations.

(** Valid reached forests retain the encoding-dependent forest and stored Map invariants. *)
Definition partition_forest {K} (E : encoding K) :=
  {u : UnionFind.t K | UnionFind.wf E u}.

(** None is unreachable and Some carries a representation-valid reached partition. *)
Definition partition_t {K} (E : encoding K) := option (partition_forest E).

(** The legacy-style carrier name retains its encoding argument. *)
Definition partition {K} (E : encoding K) := partition_t E.

(** Unreachable partitions entail every equality while reached partitions compare roots. *)
Definition partition_equiv {K} (E : encoding K) (p : partition_t E) (a b : K) : Prop :=
  match p with
  | None => True
  | Some u => UnionFind.equiv E (proj1_sig u) a b
  end.

(** A forest representative is observed through the public find operation. *)
Definition partition_rep {K} (E : encoding K) (u : UnionFind.t K) x :=
  fst (UnionFind.find E x u).

(** A pair of representative codes is a label for equality intersection. *)
Definition partition_label_c {K} (E : encoding K) (u v : UnionFind.t K) x :=
  let* ru := UnionFind.find_c E x u in
  let* rv := UnionFind.find_c E x v in
  Cost.step ;;
  let* a := encode_c E (fst ru) in
  Cost.step ;;
  let* b := encode_c E (fst rv) in
  Cost.ret (a, b).

(** Pair labels use the public codec for two positive codes. *)
Definition partition_label_encoding :=
  codec_enc (pair_codec positive_codec positive_codec).

(** Pair labelling retains both find calls and both encoding callbacks with invocation overhead. *)
Theorem partition_label_cost {K} (E : encoding K) u v x :
  Cost.ticks (partition_label_c E u v x) =
    (2 + Cost.ticks (UnionFind.find_c E x u) + Cost.ticks (UnionFind.find_c E x v) +
      Cost.ticks (encode_c E (partition_rep E u x)) +
      Cost.ticks (encode_c E (partition_rep E v x)))%N.
Proof.
  unfold partition_label_c, partition_rep; autorewrite with galois_cost.
  fold (UnionFind.find E x u); fold (UnionFind.find E x v); lia.
Qed.

(** The pair-label encoding is injective independently of the client key encoding. *)
Theorem partition_label_encoding_laws : encoding_laws partition_label_encoding.
Proof.
  apply codec_laws_injective, pair_codec_laws; apply positive_codec_laws.
Qed.

(** Two pair labels agree exactly when both forests equate the two keys. *)
Theorem partition_label_spec {K} (E : encoding K) (HE : encoding_laws E) u v a b :
  Cost.value (partition_label_c E u v a) = Cost.value (partition_label_c E u v b) <->
  UnionFind.equiv E u a b /\ UnionFind.equiv E v a b.
Proof.
  unfold partition_label_c; autorewrite with galois_cost.
  change ((encode E (partition_rep E u a), encode E (partition_rep E v a)) =
    (encode E (partition_rep E u b), encode E (partition_rep E v b)) <->
    UnionFind.equiv E u a b /\ UnionFind.equiv E v a b).
  rewrite !UnionFind.equiv_equation; unfold partition_rep.
  split.
  - intro Hpair; injection Hpair as Hu Hv; split; apply (encode_injective HE); assumption.
  - intros [Hu Hv]; now rewrite Hu, Hv.
Qed.

(** A non-reflexive equality has both endpoints in the finite support. *)
Theorem partition_support_pair {K} (E : encoding K) (HE : encoding_laws E) u a b :
  UnionFind.wf E u -> UnionFind.equiv E u a b -> a <> b ->
  In a (UnionFind.keys E u) /\ In b (UnionFind.keys E u).
Proof.
  intros Hu Hab Hne; split.
  - destruct (in_dec (fun x y => eqb_dec E HE x y) a (UnionFind.keys E u)) as [Ha|Ha].
    + exact Ha.
    + exfalso; apply Hne; symmetry; exact (UnionFind.keys_support E HE u a b Hu Ha Hab).
  - destruct (in_dec (fun x y => eqb_dec E HE x y) b (UnionFind.keys E u)) as [Hb|Hb].
    + exact Hb.
    + exfalso; apply Hne; apply (UnionFind.keys_support E HE u b a Hu Hb).
      rewrite UnionFind.equiv_equation in *; symmetry; exact Hab.
Qed.

(** Intersection enumerates one support and builds one pair-label index for the result. *)
Definition partition_intersection_raw_c {K} (E : encoding K)
    (u v : UnionFind.t K) :=
  let* keys := UnionFind.keys_c E u in
  partition_group_c E partition_label_encoding (partition_label_c E u v) keys.

(** The raw intersection result is observed without its representation certificate. *)
Definition partition_intersection_raw {K} (E : encoding K) u v :=
  Cost.value (partition_intersection_raw_c E u v).

(** Intersection reconstruction satisfies the representation invariant. *)
Theorem partition_intersection_wf {K} (E : encoding K) (HE : encoding_laws E) u v :
  UnionFind.wf E (partition_intersection_raw E u v).
Proof.
  apply (partition_group_wf E _ _ HE).
Qed.

(** Refinement attaches the preservation certificate without changing computation or ticks. *)
Definition partition_intersection_c {K} (E : encoding K) (HE : encoding_laws E)
    (u v : partition_forest E) : Cost.t (partition_forest E) :=
  Cost.refine (partition_intersection_raw_c E (proj1_sig u) (proj1_sig v))
    (partition_intersection_wf E HE _ _).

(** The valid intersection is the value of the refined computation. *)
Definition partition_intersection {K} (E : encoding K) (HE : encoding_laws E) u v :=
  Cost.value (partition_intersection_c E HE u v).

(** Intersection retains precisely the equalities shared by its two valid inputs. *)
Theorem partition_intersection_equiv {K} (E : encoding K) (HE : encoding_laws E) u v a b :
  UnionFind.equiv E (proj1_sig (partition_intersection E HE u v)) a b <->
  UnionFind.equiv E (proj1_sig u) a b /\ UnionFind.equiv E (proj1_sig v) a b.
Proof.
  unfold partition_intersection, partition_intersection_c.
  rewrite Cost.value_refine; cbn [proj1_sig].
  change (UnionFind.equiv E
    (partition_group E partition_label_encoding
      (partition_label_c E (proj1_sig u) (proj1_sig v))
      (UnionFind.keys E (proj1_sig u))) a b <->
    UnionFind.equiv E (proj1_sig u) a b /\ UnionFind.equiv E (proj1_sig v) a b).
  rewrite (partition_group_equiv E _ _ HE partition_label_encoding_laws).
  rewrite partition_label_spec by exact HE.
  split.
  - intros [Heq|[_ [_ Hab]]]; [subst b; split; apply UnionFind.equiv_equation; reflexivity|].
    exact Hab.
  - intros [Hu Hv]; destruct (eqb_dec E HE a b) as [Heq|Hne]; [now left|].
    destruct (partition_support_pair E HE _ _ _ (proj2_sig u) Hu Hne) as [Ha Hb].
    right; tauto.
Qed.

(** Order scans one forest and checks that each key equals its classmate in the other. *)
Fixpoint partition_scan_c {K} (E : encoding K) (keys : list K)
    (u v : UnionFind.t K) : Cost.t bool :=
  match keys with
  | [] => Cost.ret true
  | x :: rest =>
    Cost.step ;;
    let* found := UnionFind.find_c E x v in
    let* tested := UnionFind.equivb_c E x (fst found) u in
    if fst tested then partition_scan_c E rest (snd tested) (snd found)
    else Cost.ret false
  end.

(** The pure scan is the value projection of its compressed traversal. *)
Definition partition_scan {K} (E : encoding K) keys u v :=
  Cost.value (partition_scan_c E keys u v).

(** The scan equation exposes the two public UnionFind calls at each key. *)
Theorem partition_scan_equation {K} (E : encoding K) keys u v :
  partition_scan E keys u v =
  match keys with
  | [] => true
  | x :: rest =>
    let found := UnionFind.find E x v in
    let tested := UnionFind.equivb E x (fst found) u in
    if fst tested then partition_scan E rest (snd tested) (snd found) else false
  end.
Proof.
  destruct keys as [|x rest]; [reflexivity|].
  unfold partition_scan at 1; cbn [partition_scan_c]; autorewrite with galois_cost.
  fold (UnionFind.find E x v).
  fold (UnionFind.equivb E x (fst (UnionFind.find E x v)) u).
  destruct (fst (UnionFind.equivb E x (fst (UnionFind.find E x v)) u)); reflexivity.
Qed.

(** Scanning recognises equality to every visited representative of the right forest. *)
Theorem partition_scan_correct {K} (E : encoding K) (HE : encoding_laws E) keys u v :
  UnionFind.wf E u -> UnionFind.wf E v ->
  (partition_scan E keys u v = true <-> forall x, In x keys ->
    UnionFind.equiv E u x (partition_rep E v x)).
Proof.
  revert u v; induction keys as [|x rest IH]; intros u v Hu Hv.
  - rewrite partition_scan_equation; cbn; split; [intros _ a Ha; contradiction|reflexivity].
  - rewrite partition_scan_equation.
    pose proof (UnionFind.wf_find E HE v x Hv) as Hv'.
    pose proof (UnionFind.find_rep_stable E HE v) as Hstable.
    destruct (UnionFind.equivb_correct E HE u x (fst (UnionFind.find E x v)) Hu)
      as [Htest [Hu' Hagrees]].
    destruct (UnionFind.find E x v) as [r v'] eqn:Hfind;
      cbn [fst snd] in Hv', Htest, Hu', Hagrees |- *.
    destruct (UnionFind.equivb E x r u) as [ok u'] eqn:Htested;
      cbn [fst snd] in Htest, Hu', Hagrees |- *.
    assert (Htail : partition_scan E rest u' v' = true <->
      forall a, In a rest -> UnionFind.equiv E u a (partition_rep E v a)).
    { rewrite (IH u' v' Hu' Hv'); split; intros Hall a Ha.
      - apply (proj1 (Hagrees _ _)); specialize (Hall a Ha).
        unfold partition_rep in *.
        pose proof (Hstable a x Hv) as Hrep; rewrite Hfind in Hrep; cbn [snd] in Hrep.
        now rewrite <- Hrep.
      - apply (proj2 (Hagrees _ _)); specialize (Hall a Ha).
        unfold partition_rep in *.
        pose proof (Hstable a x Hv) as Hrep; rewrite Hfind in Hrep; cbn [snd] in Hrep.
        now rewrite Hrep. }
    assert (Hhead : ok = true <-> UnionFind.equiv E u x (partition_rep E v x)).
    { unfold partition_rep; rewrite Hfind; exact Htest. }
    destruct ok.
    + rewrite Htail; split.
      * intros Hall a [Heq|Ha]; [subst a; apply Hhead; reflexivity|now apply Hall].
      * intros Hall a Ha; apply Hall; now right.
    + split; [discriminate|]; intro Hall.
      assert (Hfalse : false = true) by (apply Hhead; apply Hall; now left).
      discriminate.
Qed.

(** Reached comparison enumerates the support of the less constrained right input. *)
Definition partition_forest_leb_c {K} (E : encoding K) (u v : partition_forest E) :=
  let* keys := UnionFind.keys_c E (proj1_sig v) in
  partition_scan_c E keys (proj1_sig u) (proj1_sig v).

(** Reached comparison observes the costed support scan. *)
Definition partition_forest_leb {K} (E : encoding K) u v :=
  Cost.value (partition_forest_leb_c E u v).

(** Reached comparison decides reverse inclusion of equalities. *)
Theorem partition_forest_leb_spec {K} (E : encoding K) (HE : encoding_laws E) u v :
  partition_forest_leb E u v = true <->
  forall a b, UnionFind.equiv E (proj1_sig v) a b -> UnionFind.equiv E (proj1_sig u) a b.
Proof.
  unfold partition_forest_leb, partition_forest_leb_c; rewrite Cost.value_bind.
  change (partition_scan E (UnionFind.keys E (proj1_sig v)) (proj1_sig u) (proj1_sig v) =
    true <-> forall a b, UnionFind.equiv E (proj1_sig v) a b ->
      UnionFind.equiv E (proj1_sig u) a b).
  rewrite (partition_scan_correct E HE) by apply proj2_sig.
  split.
  - intros Hall a b Hab; destruct (eqb_dec E HE a b) as [Heq|Hne].
    + subst b; apply UnionFind.equiv_equation; reflexivity.
    + destruct (partition_support_pair E HE _ _ _ (proj2_sig v) Hab Hne) as [Ha Hb].
      specialize (Hall a Ha) as Har; specialize (Hall b Hb) as Hbr.
      rewrite UnionFind.equiv_equation in Hab, Har, Hbr |- *.
      unfold partition_rep in *; rewrite <- Hab in Hbr; congruence.
  - intros Hall a _; apply Hall; apply (proj1 (UnionFind.find_equiv E HE _ _ (proj2_sig v))).
Qed.

(** Total comparison handles the unreachable cases directly without a reached bottom. *)
Definition partition_leb_c {K} (E : encoding K) (p q : partition_t E) : Cost.t bool :=
  Cost.step ;;
  match p, q with
  | None, _ => Cost.ret true
  | Some u, Some v => partition_forest_leb_c E u v
  | Some _, None => Cost.ret false
  end.

(** Partition comparison is the pure observation of its costed operation. *)
Definition partition_leb {K} (E : encoding K) p q := Cost.value (partition_leb_c E p q).

(** Join intersects reached equalities and ignores an unreachable input. *)
Definition partition_join_c {K} (E : encoding K) (HE : encoding_laws E)
    (p q : partition_t E) : Cost.t (partition_t E) :=
  Cost.step ;;
  match p, q with
  | None, _ => Cost.ret q
  | _, None => Cost.ret p
  | Some u, Some v => Cost.map (@Some _) (partition_intersection_c E HE u v)
  end.

(** The pure join observes the costed intersection. *)
Definition partition_join {K} (E : encoding K) HE p q :=
  Cost.value (partition_join_c E HE p q).

(** The direct option lattice has no alleged least reached forest. *)
Definition partition_lattice {K} (E : encoding K) (HE : encoding_laws E) :
    lattice (partition_t E) :=
  {| leb_c := partition_leb_c E;
     join_c := partition_join_c E HE;
     widen_c := partition_join_c E HE;
     narrow_c := fun p _ => Cost.ret p;
     bot := None |}.

Section Laws.
Context {K : Type} (E : encoding K) (HE : encoding_laws E).

(** The join keeps exactly the equalities shared by its inputs, including None cases. *)
Theorem partition_join_spec a b p q :
  partition_equiv E (partition_join E HE p q) a b <->
  partition_equiv E p a b /\ partition_equiv E q a b.
Proof.
  destruct p as [u|], q as [v|]; cbn [partition_join partition_join_c partition_equiv];
    autorewrite with galois_cost; cbn [partition_equiv].
  - apply partition_intersection_equiv.
  - tauto.
  - tauto.
  - tauto.
Qed.

(** Comparison entails reverse equality inclusion for every total partition. *)
Theorem partition_leb_sound p q : partition_leb E p q = true ->
  forall a b, partition_equiv E q a b -> partition_equiv E p a b.
Proof.
  destruct p as [u|], q as [v|]; cbn [partition_leb partition_leb_c partition_equiv];
    autorewrite with galois_cost; try discriminate; try tauto.
  apply (partition_forest_leb_spec E HE).
Qed.

Local Lemma partition_leb_refl p : partition_leb E p p = true.
Proof.
  destruct p as [u|]; [apply (partition_forest_leb_spec E HE); tauto|reflexivity].
Qed.

Local Lemma partition_leb_trans p q r :
  partition_leb E p q = true -> partition_leb E q r = true -> partition_leb E p r = true.
Proof.
  destruct p as [u|], q as [v|], r as [w|]; cbn [partition_leb partition_leb_c];
    autorewrite with galois_cost; intros Huv Hvw; try discriminate; try reflexivity.
  change (partition_forest_leb E u v = true) in Huv.
  change (partition_forest_leb E v w = true) in Hvw.
  change (partition_forest_leb E u w = true).
  apply (partition_forest_leb_spec E HE).
  pose proof (proj1 (partition_forest_leb_spec E HE u v) Huv) as Huv'.
  pose proof (proj1 (partition_forest_leb_spec E HE v w) Hvw) as Hvw'.
  intros a b Hab; apply Huv'; now apply Hvw'.
Qed.

Local Lemma partition_join_upper p q :
  partition_leb E p (partition_join E HE p q) = true /\
  partition_leb E q (partition_join E HE p q) = true.
Proof.
  destruct p as [u|], q as [v|]; cbn [partition_join partition_join_c];
    autorewrite with galois_cost.
  - split; apply (partition_forest_leb_spec E HE); intros a b Hab;
      apply (partition_intersection_equiv E HE) in Hab; tauto.
  - split; [apply partition_leb_refl|reflexivity].
  - split; [reflexivity|apply partition_leb_refl].
  - split; reflexivity.
Qed.

(** Direct None cases and reached reverse inclusion establish all total weak laws. *)
Theorem partition_laws : lattice_laws (partition_lattice E HE).
Proof.
  constructor.
  - apply partition_leb_refl.
  - apply partition_leb_trans.
  - intro p; reflexivity.
  - intros p q; apply (proj1 (partition_join_upper p q)).
  - intros p q; apply (proj2 (partition_join_upper p q)).
  - intros p q; apply (proj1 (partition_join_upper p q)).
  - intros p q; apply (proj2 (partition_join_upper p q)).
  - intros p q _; apply partition_leb_refl.
  - intros p q Hqp; exact Hqp.
Qed.

(** Intersection is the least upper bound in the total option order. *)
Theorem partition_lub : lub_laws (partition_lattice E HE).
Proof.
  constructor; intros [u|] [v|] [w|];
    cbn [leb join partition_lattice partition_leb_c partition_join_c];
    autorewrite with galois_cost; intros Huw Hvw;
    try discriminate; try assumption; try reflexivity.
  pose proof (proj1 (partition_forest_leb_spec E HE u w) Huw) as Huw'.
  pose proof (proj1 (partition_forest_leb_spec E HE v w) Hvw) as Hvw'.
  apply (partition_forest_leb_spec E HE); intros a b Hab.
  apply (partition_intersection_equiv E HE); split; [apply Huw'|apply Hvw']; exact Hab.
Qed.

(** The discrete empty forest is top because unknown keys are singleton classes. *)
Definition partition_top : top (partition_lattice E HE).
Proof.
  refine (@Top _ (partition_lattice E HE)
    (Some (exist _ UnionFind.make (UnionFind.wf_make E))) _).
  intros [u|]; [|reflexivity].
  change (partition_forest_leb E u
    (exist _ UnionFind.make (UnionFind.wf_make E)) = true).
  apply (partition_forest_leb_spec E HE); intros a b Hab.
  apply UnionFind.make_equiv in Hab; subst b.
  apply UnionFind.equiv_equation; reflexivity.
Defined.

(** Reached meanings contain valuations respecting every equality. *)
Definition partition_reached_gamma {V} : concretisation (partition_forest E) (K -> V) :=
  {| gamma := fun u s => forall a b, UnionFind.equiv E (proj1_sig u) a b -> s a = s b |}.

(** The public option meaning uses the true empty-bottom meaning helper. *)
Definition partition_gamma {V} : concretisation (partition_t E) (K -> V) :=
  lift_bot_gamma partition_reached_gamma.

(** Losing equalities preserves every valuation of a reached partition. *)
Theorem partition_gamma_laws {V} :
  concretisation_laws (partition_lattice E HE) (@partition_gamma V).
Proof.
  constructor; intros [u|] [v|] s Hle Hs; try contradiction; try discriminate.
  intros a b Hab; apply Hs.
  exact (partition_leb_sound (Some u) (Some v) Hle a b Hab).
Qed.

(** No valuation belongs to the fresh unreachable bottom. *)
Theorem partition_bot_empty {V} :
  bottom_empty (partition_lattice E HE) (@partition_gamma V).
Proof.
  constructor; intros s Hs; exact Hs.
Qed.

(** Every valuation respects the discrete top partition. *)
Theorem partition_top_full {V} : top_full partition_top (@partition_gamma V).
Proof.
  constructor; intros s a b Hab; apply UnionFind.make_equiv in Hab; now subst b.
Qed.
End Laws.

(** Each visited key contributes one scan traversal tick. *)
Definition partition_scan_k : N := 1.

(** A proof-only scan account records visited keys and the actual compressed callee charges. *)
Fixpoint partition_scan_account {K} (E : encoding K) keys u v
    (visited : nat) (charge : N) : Prop :=
  match keys with
  | [] => visited = O /\ charge = 0%N
  | x :: rest =>
    let found := UnionFind.find E x v in
    let tested := UnionFind.equivb E x (fst found) u in
    let calls := (Cost.ticks (UnionFind.find_c E x v) +
      Cost.ticks (UnionFind.equivb_c E x (fst found) u))%N in
    if fst tested then
      exists n c, partition_scan_account E rest (snd tested) (snd found) n c /\
        visited = S n /\ charge = (calls + c)%N
    else visited = 1 /\ charge = calls
  end.

(** Every scan has an account even when it stops at the first failed classmate check. *)
Theorem partition_scan_account_exists {K} (E : encoding K) keys u v :
  exists n c, partition_scan_account E keys u v n c.
Proof.
  revert u v; induction keys as [|x rest IH]; intros u v.
  - exists O, 0%N; split; reflexivity.
  - cbn [partition_scan_account].
    destruct (fst (UnionFind.equivb E x (fst (UnionFind.find E x v)) u)).
    + destruct (IH (snd (UnionFind.equivb E x (fst (UnionFind.find E x v)) u))
        (snd (UnionFind.find E x v))) as [n [c Htail]].
      eexists; eexists; exists n, c; repeat split; try exact Htail; reflexivity.
    + eexists; eexists; split; reflexivity.
Qed.

(** A scan visits at most the enumerated support length, including early rejection. *)
Theorem partition_scan_visited_bound {K} (E : encoding K) keys u v n c :
  partition_scan_account E keys u v n c -> n <= length keys.
Proof.
  revert u v n c; induction keys as [|x rest IH]; intros u v n c Haccount.
  - destruct Haccount as [-> _]; reflexivity.
  - cbn [partition_scan_account] in Haccount.
    destruct (fst (UnionFind.equivb E x (fst (UnionFind.find E x v)) u)).
    + destruct Haccount as [n' [c' [Htail [-> _]]]].
      specialize (IH _ _ _ _ Htail); cbn [length]; lia.
    + destruct Haccount as [-> _]; cbn [length]; lia.
Qed.

(** Scan cost is exactly traversal overhead plus the account's actual callee sum. *)
Theorem partition_scan_cost {K} (E : encoding K) keys u v n c :
  partition_scan_account E keys u v n c ->
  Cost.ticks (partition_scan_c E keys u v) =
    (partition_scan_k * N.of_nat n + c)%N.
Proof.
  revert u v n c; induction keys as [|x rest IH]; intros u v n c Haccount.
  - destruct Haccount as [-> ->]; reflexivity.
  - cbn [partition_scan_account] in Haccount.
    cbn [partition_scan_c]; autorewrite with galois_cost.
    fold (UnionFind.find E x v).
    fold (UnionFind.equivb E x (fst (UnionFind.find E x v)) u).
    destruct (fst (UnionFind.equivb E x (fst (UnionFind.find E x v)) u)).
    + destruct Haccount as [n' [c' [Htail [-> ->]]]].
      rewrite (IH _ _ _ _ Htail), Nat2N.inj_succ; unfold partition_scan_k; lia.
    + destruct Haccount as [-> ->]; autorewrite with galois_cost.
      unfold partition_scan_k; lia.
Qed.

(** Reached comparison retains support enumeration, visited traversal and actual find/test calls. *)
Theorem partition_leb_cost {K} (E : encoding K) (u v : partition_forest E) n c :
  partition_scan_account E (UnionFind.keys E (proj1_sig v))
    (proj1_sig u) (proj1_sig v) n c ->
  Cost.ticks (partition_leb_c E (Some u) (Some v)) =
    (1 + Cost.ticks (UnionFind.keys_c E (proj1_sig v)) +
      partition_scan_k * N.of_nat n + c)%N.
Proof.
  intro Haccount; unfold partition_leb_c, partition_forest_leb_c.
  autorewrite with galois_cost.
  fold (UnionFind.keys E (proj1_sig v)).
  rewrite (partition_scan_cost _ _ _ _ _ _ Haccount); lia.
Qed.

(** An unreachable comparison case costs its single option-case tick. *)
Theorem partition_leb_unreached_cost {K} (E : encoding K) p :
  Cost.ticks (partition_leb_c E None p) = 1%N /\
  Cost.ticks (partition_leb_c E p None) = 1%N.
Proof.
  destruct p; split; reflexivity.
Qed.

(** Join retains its key enumeration, one group-by index and indexed reconstruction charges. *)
Theorem partition_join_cost {K} (E : encoding K) (HE : encoding_laws E)
    (u v : partition_forest E) charge :
  let keys := UnionFind.keys E (proj1_sig u) in
  let label := partition_label_c E (proj1_sig u) (proj1_sig v) in
  partition_rebuild_account E partition_label_encoding label keys
    (Index.group_by partition_label_encoding (fun k => Cost.value (label k)) keys) charge ->
  Cost.ticks (partition_join_c E HE (Some u) (Some v)) =
    (1 + Cost.ticks (UnionFind.keys_c E (proj1_sig u)) +
      Cost.ticks (Index.group_by_c partition_label_encoding label keys) +
      partition_group_k * N.of_nat (length keys) + charge)%N.
Proof.
  cbn zeta; intro Haccount.
  unfold partition_join_c, partition_intersection_c, partition_intersection_raw_c.
  autorewrite with galois_cost.
  fold (UnionFind.keys E (proj1_sig u)).
  rewrite (partition_group_cost _ _ _ _ _ Haccount); lia.
Qed.

(** An unreachable join case costs its single option-case tick. *)
Theorem partition_join_unreached_cost {K} (E : encoding K) (HE : encoding_laws E) p :
  Cost.ticks (partition_join_c E HE None p) = 1%N /\
  Cost.ticks (partition_join_c E HE p None) = 1%N.
Proof.
  destruct p; split; reflexivity.
Qed.
