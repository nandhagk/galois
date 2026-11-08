(** * Labelled control dependence

    Reversed frontier events retain each controlling edge label.
    For example, the two branch labels of a diamond control different arms.
    Builds on: GraphFrontierSweep and prepared reversal. *)

From Stdlib Require Import List Bool PArith NArith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet.
From Galois.Graph Require Import GraphModel GraphPrepared GraphDomSpec GraphFrontierSpec
  GraphPreparedCost GraphReach GraphFrontierSweep.
Import List.ListNotations Cost.Notations.

Module FrontierControl.

(** Exit coverage applies to every listed graph node,
    including components unreachable from entries. *)
Definition exits_cover {V E} (g : Graph.t V E) exits :=
  forall v, In v (Graph.nodes g) -> exists es z, path g v es z /\ In z exits.

Local Lemma reverse_out_spec {V E} (p : Prepared.t V E) exits v e :
  Prepared.ready p ->
  (In e (Graph.out (Prepared.graph (Prepared.reverse p exits)) v) <->
    In (Graph.source (Prepared.graph p) e) (Graph.nodes (Prepared.graph p)) /\
    In e (Graph.out (Prepared.graph p) (Graph.source (Prepared.graph p) e)) /\
    Graph.target (Prepared.graph p) e = v).
Proof.
  intros Hready. pose proof (proj2 (proj2 Hready)) as Hp.
  change (In e (Cost.value (Prepared.incoming_c p v)) <->
    In (Graph.source (Prepared.graph p) e) (Graph.nodes (Prepared.graph p)) /\
    In e (Graph.out (Prepared.graph p) (Graph.source (Prepared.graph p) e)) /\
    Graph.target (Prepared.graph p) e = v).
  rewrite Prepared.incoming_equation.
  destruct (Prepared.id_of p v) as [i|] eqn:Hi.
  - rewrite in_map_iff. split.
    + intros [[a j] [Heq Hin]]. cbn in Heq. subst a.
      apply (Prepared.pred_agrees p Hp v i e j Hi) in Hin. tauto.
    + intros [Hs [He Ht]].
      destruct (proj1 (Prepared.ids_domain p Hp _) Hs) as [j Hj].
      exists (e, j). split; [reflexivity|].
      apply (Prepared.pred_agrees p Hp v i e j Hi). auto.
  - split; [contradiction|]. intros [Hs [He Ht]].
    assert (Hv : In v (Graph.nodes (Prepared.graph p))).
    { rewrite <- Ht. eapply out_target_in; [exact (proj1 Hready)|exact Hs|exact He]. }
    destruct (proj1 (Prepared.ids_domain p Hp v) Hv) as [i Hi']. congruence.
Qed.

Local Lemma path_snoc {V E} (g : Graph.t V E) s es v e :
  path g s es v -> v = Graph.source g e -> In e (Graph.out g v) ->
  path g s (es ++ [e]) (Graph.target g e).
Proof.
  intro Hpath. induction Hpath as [v|a rest v Ha Hpath IH]; intros Hsource He.
  - subst v. cbn. constructor; [exact He|constructor].
  - cbn. constructor; [exact Ha|now apply IH].
Qed.

Local Lemma path_reverse {V E} (p : Prepared.t V E) exits s es z :
  Prepared.ready p -> In s (Graph.nodes (Prepared.graph p)) ->
  path (Prepared.graph p) s es z ->
  path (Prepared.graph (Prepared.reverse p exits)) z (rev es) s.
Proof.
  intros Hready Hs Hpath. revert Hs.
  induction Hpath as [s|e rest z He Hpath IH]; intro Hs; cbn [rev].
  - constructor.
  - eapply path_snoc.
    + apply IH. eapply out_target_in; [exact (proj1 Hready)|exact Hs|exact He].
    + reflexivity.
    + apply reverse_out_spec; [exact Hready|]. auto.
Qed.

Local Lemma path_unreverse {V E} (p : Prepared.t V E) exits z es s :
  Prepared.ready p -> path (Prepared.graph (Prepared.reverse p exits)) z es s ->
  path (Prepared.graph p) s (rev es) z.
Proof.
  intros Hready Hpath. induction Hpath as [z|e rest s He Hpath IH]; cbn [rev].
  - constructor.
  - change (In e (Graph.out (Prepared.graph (Prepared.reverse p exits))
      (Graph.target (Prepared.graph p) e))) in He.
    apply (reverse_out_spec p exits _ e Hready) in He.
    destruct He as [Hs [He Ht]].
    eapply path_snoc; [exact IH|reflexivity|exact He].
Qed.

Local Lemma exists_cons {A B} (f : A -> B) e es d :
  (exists a, In a (e :: es) /\ f a = d) <->
    f e = d \/ exists a, In a es /\ f a = d.
Proof.
  cbn [In]. split.
  - intros [a [[<-|Ha] Hd]]; [auto|right; now exists a].
  - intros [Hd|[a [Ha Hd]]]; [exists e; auto|exists a; auto].
Qed.

Local Lemma path_occurrences {V E} (g : Graph.t V E) s es z :
  path g s es z -> forall d,
  (d = s \/ exists e, In e es /\ Graph.target g e = d) <->
    (d = z \/ exists e, In e es /\ Graph.source g e = d).
Proof.
  intro Hpath. induction Hpath as [s|e rest z He Hpath IH]; intro d.
  - cbn [In]. firstorder.
  - rewrite !exists_cons. pose proof (IH d) as Hoccurs.
    split.
    + intros [Hs|[Ht|Htail]].
      * right. left. symmetry. exact Hs.
      * destruct (proj1 Hoccurs (or_introl (eq_sym Ht))) as [Hz|Hrest];
          [now left|right; now right].
      * destruct (proj1 Hoccurs (or_intror Htail)) as [Hz|Hrest];
          [now left|right; now right].
    + intros [Hz|[Hs|Htail]].
      * destruct (proj2 Hoccurs (or_introl Hz)) as [Ht|Hrest].
        -- right. left. symmetry. exact Ht.
        -- right. now right.
      * left. symmetry. exact Hs.
      * destruct (proj2 Hoccurs (or_intror Htail)) as [Ht|Hrest].
        -- right. left. symmetry. exact Ht.
        -- right. now right.
Qed.

Local Lemma reverse_occurrences {V E} (p : Prepared.t V E) exits s es z d :
  path (Prepared.graph p) s es z ->
  (d = s \/ exists e, In e es /\ Graph.target (Prepared.graph p) e = d) <->
    (d = z \/ exists e, In e (rev es) /\
      Graph.target (Prepared.graph (Prepared.reverse p exits)) e = d).
Proof.
  intro Hpath. rewrite (path_occurrences _ _ _ _ Hpath d).
  change ((d = z \/ exists e, In e es /\ Graph.source (Prepared.graph p) e = d) <->
    (d = z \/ exists e, In e (rev es) /\ Graph.source (Prepared.graph p) e = d)).
  split; intros [Hz|[e [He Hd]]]; [now left| |now left|].
  - right. exists e. split; [exact (proj1 (in_rev es e) He)|exact Hd].
  - right. exists e. split; [exact (proj2 (in_rev es e) He)|exact Hd].
Qed.

(** Post-dominance equals reverse dominance for a listed starting node. *)
Theorem post_is_reverse {V E} (p : Prepared.t V E) exits d v :
  Prepared.ready p -> In v (Graph.nodes (Prepared.graph p)) ->
  (post_dominates (Prepared.graph p) (Prepared.present (Prepared.name_of p) exits) d v <->
    dominates (Prepared.graph (Prepared.reverse p exits)) d v).
Proof.
  intros Hready Hv. split.
  - intros Hpost z es Hz Hpath.
    rewrite Prepared.reverse_equation in Hz.
    pose proof (path_unreverse p exits z es v Hready Hpath) as Hforward.
    pose proof (Hpost z (rev es) Hz Hforward) as Hoccurs.
    apply (proj1 (reverse_occurrences p exits v (rev es) z d Hforward)) in Hoccurs.
    now rewrite rev_involutive in Hoccurs.
  - intros Hdom z es Hz Hpath.
    pose proof (path_reverse p exits v es z Hready Hv Hpath) as Hreverse.
    assert (Hentry : In z (Graph.entries (Prepared.graph (Prepared.reverse p exits)))).
    { rewrite Prepared.reverse_equation. exact Hz. }
    pose proof (Hdom z (rev es) Hentry Hreverse) as Hoccurs.
    now apply (proj2 (reverse_occurrences p exits v es z d Hpath)).
Qed.

Local Lemma reverse_reachable {V E} (p : Prepared.t V E) exits v :
  Prepared.ready p ->
  exits_cover (Prepared.graph p) (Prepared.present (Prepared.name_of p) exits) ->
  In v (Graph.nodes (Prepared.graph p)) ->
  reachable (Prepared.graph (Prepared.reverse p exits)) v.
Proof.
  intros Hready Hcover Hv. destruct (Hcover v Hv) as [es [z [Hpath Hz]]].
  apply reachable_iff_path. exists z, (rev es).
  split; [rewrite Prepared.reverse_equation; exact Hz|].
  now apply path_reverse.
Qed.

Definition add_c {E} (m : Map.t positive (list E)) (event : positive * (E * positive)) :=
  let '(n, (e, _)) := event in
  let* old := Map.find_or_c positive_encoding [] n m in
  Cost.step ;;
  Map.set_c positive_encoding n (e :: old) m.

Definition add {E} m (event : positive * (E * positive)) := Cost.value (add_c m event).

(** Control observations preserve label identity and multiplicity in list-valued rows. *)
Definition control_at {E} (m : Map.t positive (list E)) n e :=
  exists row, Map.get positive_encoding n m = Some row /\ In e row.

Local Lemma add_equation {E} m n (e : E) v :
  add m (n, (e, v)) = Map.set positive_encoding n
    (e :: Map.find_or positive_encoding [] n m) m.
Proof.
  unfold add, add_c. autorewrite with galois_cost. reflexivity.
Qed.

Local Lemma add_wf {E} m (event : positive * (E * positive)) :
  Map.wf positive_encoding m -> Map.wf positive_encoding (add m event).
Proof.
  intro Hmap. destruct event as [n [e v]].
  unfold add, add_c. autorewrite with galois_cost. apply Map.wf_set, Hmap.
Qed.

Local Lemma add_spec {E} m (event : positive * (E * positive)) n e :
  Map.wf positive_encoding m ->
  (control_at (add m event) n e <->
    (n = fst event /\ e = fst (snd event)) \/ control_at m n e).
Proof.
  intro Hmap. destruct event as [a [b v]]. rewrite add_equation.
  unfold control_at. cbn [fst snd].
  rewrite Map.get_set by exact Hmap. rewrite Map.find_or_equation.
  destruct (Pos.eq_dec n a) as [->|Hne].
  - rewrite (proj2 (eqb_true_iff _ positive_encoding_laws a a) eq_refl).
    destruct (Map.get positive_encoding a m) as [old|].
    + split.
      * intros [row [Heq Hin]]. inversion Heq; subst row.
        destruct Hin as [<-|Hin]; [auto|right; now exists old].
      * intros [[_ ->]|[row [Heq Hin]]].
        -- exists (b :: old). split; [reflexivity|now left].
        -- inversion Heq; subst row. exists (b :: old).
           split; [reflexivity|now right].
    + split.
      * intros [row [Heq Hin]]. inversion Heq; subst row.
        destruct Hin as [<-|Hfalse]; [auto|contradiction].
      * intros [[_ ->]|[row [Hfalse _]]];
          [exists [b]; split; [reflexivity|now left]|discriminate].
  - rewrite (proj2 (eqb_false_iff _ positive_encoding_laws n a) Hne).
    split; [auto|intros [[Heq _]|H]; [congruence|exact H]].
Qed.

Local Lemma fold_wf {E} es (m : Map.t positive (list E)) :
  Map.wf positive_encoding m -> Map.wf positive_encoding (fold_left add es m).
Proof.
  revert m. induction es as [|e rest IH]; intros m Hmap; [exact Hmap|].
  cbn [fold_left]. now apply IH, add_wf.
Qed.

Local Lemma fold_spec {E} es (m : Map.t positive (list E)) n e :
  Map.wf positive_encoding m ->
  (control_at (fold_left add es m) n e <->
    (exists v, In (n, (e, v)) es) \/ control_at m n e).
Proof.
  revert m. induction es as [|[a [b v]] rest IH]; intros m Hmap; cbn [fold_left].
  - split; [auto|intros [[v Hfalse]|H]; [contradiction|exact H]].
  - rewrite IH by now apply add_wf.
    rewrite add_spec by exact Hmap. cbn [fst snd].
    split.
    + intros [[x Hin]|[[-> ->]|H]]; [left; exists x; now right| |auto].
      left. exists v. now left.
    + intros [[x [Heq|Hin]]|H].
      * inversion Heq; subst a b. right. left. auto.
      * left. now exists x.
      * right. right. exact H.
Qed.

(** Control construction consumes reversed sweep events without a second graph traversal. *)
Definition control_deps_c {V E} (p : Prepared.t V E) exits t_post :=
  let* reversed := Prepared.reverse_c p exits in
  let* es := FrontierSweep.events_c reversed t_post in
  fold_left_c add_c es Map.empty.

Definition control_deps {V E} (p : Prepared.t V E) exits t_post :=
  Cost.value (control_deps_c p exits t_post).

Local Lemma add_cost {E} m n (e : E) v :
  Cost.ticks (add_c m (n, (e, v))) = (2 * FrontierSweep.key_charge n + 1)%N.
Proof.
  unfold add_c. autorewrite with galois_cost.
  rewrite Map.find_or_cost, Map.get_cost, Map.set_cost.
  change ((2 + N.pos (Pos.size n) + (1 + (2 + N.pos (Pos.size n)))) =
    2 * FrontierSweep.key_charge n + 1)%N.
  unfold FrontierSweep.key_charge. lia.
Qed.

Local Lemma accumulation_cost {E} (es : list (positive * (E * positive))) m :
  Cost.ticks (fold_left_c add_c es m) =
    fold_right (fun event n => 2 * FrontierSweep.key_charge (fst event) + 2 + n)%N 0%N es.
Proof.
  revert m. induction es as [|[d [e v]] rest IH]; intro m; [reflexivity|].
  rewrite ticks_fold_left_c_cons, IH, add_cost. cbn [fold_right fst]. lia.
Qed.

(** Control accounting retains the reversed sweep and every labelled list insertion. *)
Theorem control_deps_cost {V E} (p : Prepared.t V E) exits t_post :
  Cost.ticks (control_deps_c p exits t_post) =
    (Cost.ticks (Prepared.reverse_c p exits) +
      (Cost.ticks (FrontierSweep.events_c (Prepared.reverse p exits) t_post) +
      fold_right (fun event n => 2 * FrontierSweep.key_charge (fst event) + 2 + n)%N 0%N
        (FrontierSweep.events (Prepared.reverse p exits) t_post)))%N.
Proof.
  unfold control_deps_c. rewrite !Cost.ticks_bind, PreparedCost.reverse_c_value,
    accumulation_cost. reflexivity.
Qed.

(** A controlling label occurs exactly when its reversed frontier sweep emits that label. *)
Theorem control_is_reverse_frontier {V E} (p : Prepared.t V E) exits t_post n e :
  control_at (control_deps p exits t_post) n e <->
    exists v, In (n, (e, v)) (FrontierSweep.events (Prepared.reverse p exits) t_post).
Proof.
  unfold control_deps, control_deps_c.
  rewrite Cost.value_bind, PreparedCost.reverse_c_value, Cost.value_bind, value_fold_left_c.
  change (control_at (fold_left add
    (FrontierSweep.events (Prepared.reverse p exits) t_post) Map.empty) n e <->
    exists v, In (n, (e, v)) (FrontierSweep.events (Prepared.reverse p exits) t_post)).
  rewrite fold_spec by apply Map.wf_empty.
  unfold control_at. rewrite Map.get_empty.
  split; [intros [H|[row [Hfalse _]]]; [exact H|discriminate]|auto].
Qed.

(** Covered exits and a supplied exact post tree give control dependence on listed-source edges. *)
Theorem control_deps_exact {V E} (p : Prepared.t V E) exits t_post n i e :
  Prepared.ready p -> (forall j, In j exits -> Prepared.valid_id p j) ->
  exits_cover (Prepared.graph p) (Prepared.present (Prepared.name_of p) exits) ->
  Dom.exact (Prepared.reverse p exits) t_post ->
  Prepared.id_of p n = Some i ->
  In (Graph.source (Prepared.graph p) e) (Graph.nodes (Prepared.graph p)) ->
  (control_at (control_deps p exits t_post) i e <->
    control_dependent (Prepared.graph p) (Prepared.present (Prepared.name_of p) exits) e n).
Proof.
  intros Hready Hexits Hcover Htree Hn Hsource.
  assert (Hr := Prepared.reverse_ready p exits Hready Hexits).
  destruct (proj1 (Prepared.ids_domain p (proj2 (proj2 Hready)) _) Hsource) as [j Hj].
  rewrite control_is_reverse_frontier. split.
  - intros [k Hin].
    assert (Hk : k = j).
    { rewrite FrontierSweep.events_equation in Hin.
      (* The target tag of every reversed edge names its original source. *)
      apply in_flat_map in Hin. destruct Hin as [u [_ Hin]].
      apply in_flat_map in Hin. destruct Hin as [[a v] [Hedge Hin]].
      destruct (FinSet.mem positive_encoding u
        (Reach.set (Prepared.reverse p exits) Reach.unrestricted
          (Prepared.entry_ids (Prepared.reverse p exits)))); [|contradiction].
      apply in_map_iff in Hin. destruct Hin as [d [Heq _]].
      inversion Heq; subst a v.
      pose proof (Prepared.succ_targets _ (proj2 (proj2 Hr)) u e k Hedge) as Htag.
      change (Prepared.id_of p (Graph.source (Prepared.graph p) e) = Some k) in Htag.
      congruence. }
    subst k.
    apply (FrontierSweep.events_exact (Prepared.reverse p exits) t_post n
      (Graph.source (Prepared.graph p) e) i j e Hr Htree Hn Hj) in Hin.
    change (reachable (Prepared.graph (Prepared.reverse p exits))
      (Graph.target (Prepared.graph p) e) /\
      In e (Graph.out (Prepared.graph (Prepared.reverse p exits))
        (Graph.target (Prepared.graph p) e)) /\
      Graph.source (Prepared.graph p) e = Graph.source (Prepared.graph p) e /\
      dominates (Prepared.graph (Prepared.reverse p exits)) n
        (Graph.target (Prepared.graph p) e) /\
      ~ strictly_dominates (Prepared.graph (Prepared.reverse p exits)) n
        (Graph.source (Prepared.graph p) e)) in Hin.
    destruct Hin as [_ [He [_ [Hdom Hnot]]]].
    apply (reverse_out_spec p exits _ e Hready) in He.
    destruct He as [_ [He _]].
    unfold control_dependent. split; [exact He|].
    assert (Htarget : In (Graph.target (Prepared.graph p) e) (Graph.nodes (Prepared.graph p)))
      by (exact (out_target_in (proj1 Hready) _ e Hsource He)).
    rewrite !post_is_reverse by assumption. exact (conj Hdom Hnot).
  - intros [He [Hdom Hnot]]. exists j.
    apply (FrontierSweep.events_exact (Prepared.reverse p exits) t_post n
      (Graph.source (Prepared.graph p) e) i j e Hr Htree Hn Hj).
    assert (Htarget : In (Graph.target (Prepared.graph p) e) (Graph.nodes (Prepared.graph p)))
      by (exact (out_target_in (proj1 Hready) _ e Hsource He)).
    change (reachable (Prepared.graph (Prepared.reverse p exits))
      (Graph.target (Prepared.graph p) e) /\
      In e (Graph.out (Prepared.graph (Prepared.reverse p exits))
        (Graph.target (Prepared.graph p) e)) /\
      Graph.source (Prepared.graph p) e = Graph.source (Prepared.graph p) e /\
      dominates (Prepared.graph (Prepared.reverse p exits)) n
        (Graph.target (Prepared.graph p) e) /\
      ~ strictly_dominates (Prepared.graph (Prepared.reverse p exits)) n
        (Graph.source (Prepared.graph p) e)).
    split; [now apply reverse_reachable|].
    split; [apply reverse_out_spec; [exact Hready|auto]|].
    split; [reflexivity|].
    unfold strictly_dominates.
    rewrite <- !post_is_reverse by assumption. exact (conj Hdom Hnot).
Qed.

End FrontierControl.
