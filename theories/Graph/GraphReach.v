(** * Reference reachability

    A finite work stack computes scoped reachability independently of search producers.
    For example, blocking a diamond's join removes the join from the result.
    Builds on: GraphPrepared, GraphVisitor, GraphSearchSpec and BaseSet. *)

From Stdlib Require Import List Bool PArith Arith Lia.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor GraphSearchSpec
  GraphDomSpec.
Import List.ListNotations.

Module Reach.

Definition member (v : positive) xs := existsb (Pos.eqb v) xs.

Local Lemma member_spec v xs : member v xs = true <-> In v xs.
Proof.
  unfold member. rewrite existsb_exists. split.
  - intros [x [Hin Heq]]. apply Pos.eqb_eq in Heq. now subst x.
  - intro Hin. exists v. split; [exact Hin|apply Pos.eqb_refl].
Qed.

Definition universe {V E} (p : Prepared.t V E) :=
  nodup Pos.eq_dec (Prepared.present (Prepared.id_of p) (Graph.nodes (Prepared.graph p))).

Definition successors {V E} (p : Prepared.t V E) scope v :=
  filter (fun x => Scope.admits scope x && member x (universe p))
    (map snd (Prepared.succ_edges p v)).

Definition roots_in {V E} (p : Prepared.t V E) scope roots :=
  filter (fun x => member x roots && Scope.admits scope x) (universe p).

(** The closure uses admitted roots and successors, without invoking a producer. *)
Inductive closure (next : positive -> list positive) (roots : list positive) :
    positive -> Prop :=
  | root : forall v, In v roots -> closure next roots v
  | edge : forall u v, closure next roots u -> In v (next u) -> closure next roots v.

Fixpoint credit (next : positive -> list positive) (unseen : list positive) : nat :=
  match unseen with
  | [] => 0
  | x :: rest => S (length (next x)) + credit next rest
  end.

(** Each fresh node spends its adjacency credit once, including repeated successor IDs. *)
Fixpoint loop (next : positive -> list positive) fuel pending unseen seen
    : list positive * list positive :=
  match pending, fuel with
  | [], _ => ([], seen)
  | _, O => (pending, seen)
  | x :: todo, S fuel =>
    if member x unseen
    then loop next fuel (next x ++ todo) (remove Pos.eq_dec x unseen) (x :: seen)
    else loop next fuel todo unseen seen
  end.

Local Lemma remove_spec x y xs :
  In y (remove Pos.eq_dec x xs) <-> In y xs /\ y <> x.
Proof.
  induction xs as [|a rest IH]; cbn; [tauto|].
  destruct (Pos.eq_dec x a) as [->|Hne]; cbn; rewrite IH; intuition congruence.
Qed.

Local Lemma remove_nodup x xs : NoDup xs -> NoDup (remove Pos.eq_dec x xs).
Proof.
  intro H. induction H as [|a rest Hnot Hrest IH]; cbn; [constructor|].
  destruct (Pos.eq_dec x a); [exact IH|]. constructor; [|exact IH].
  intro Hin. apply remove_spec in Hin. tauto.
Qed.

Local Lemma remove_credit next x xs :
  NoDup xs -> In x xs ->
  credit next xs = S (length (next x)) + credit next (remove Pos.eq_dec x xs).
Proof.
  intro H. induction H as [|a rest Hnot Hrest IH]; intro Hin; [contradiction|].
  cbn [credit remove]. destruct (Pos.eq_dec x a) as [->|Hne].
  - assert (Hremove : remove Pos.eq_dec a rest = rest).
    { clear Hrest IH Hin. induction rest as [|b tail IHtail]; cbn; [reflexivity|].
      destruct (Pos.eq_dec a b) as [->|Hab].
      - exfalso. apply Hnot. now left.
      - f_equal. apply IHtail. intro Hb. apply Hnot. now right. }
    now rewrite Hremove.
  - destruct Hin as [Heq|Hin]; [congruence|].
    cbn [credit]. rewrite (IH Hin). lia.
Qed.

(** Pending items are reachable and account for every unprocessed root or successor. *)
Record invariant next roots all unseen seen pending : Prop := {
  unseen_unique : NoDup unseen;
  support : forall v, In v all -> In v unseen \/ In v seen;
  seen_sound : forall v, In v seen -> closure next roots v;
  pending_sound : forall v, In v pending -> closure next roots v;
  pending_domain : incl pending all;
  roots_pending : forall v, In v roots -> In v seen \/ In v pending;
  edges_pending : forall u v, In u seen -> In v (next u) ->
    In v seen \/ In v pending
}.

Local Lemma fresh_invariant next roots all unseen seen x todo :
  (forall u, incl (next u) all) ->
  invariant next roots all unseen seen (x :: todo) -> In x unseen ->
  invariant next roots all (remove Pos.eq_dec x unseen) (x :: seen) (next x ++ todo).
Proof.
  intros Hnext Hinv Hx. destruct Hinv as [Hnd Hsupport Hseen Hpending Hdomain Hr He].
  constructor.
  - now apply remove_nodup.
  - intros v Hv. destruct (Pos.eq_dec v x) as [->|Hne]; [right; now left|].
    destruct (Hsupport v Hv) as [Hu|Hs].
    + left. apply remove_spec. auto.
    + right. now right.
  - intros v [<-|Hv]; [apply Hpending; now left|apply Hseen; exact Hv].
  - intros v Hv. apply in_app_iff in Hv. destruct Hv as [Hv|Hv].
    + eapply edge; [apply Hpending; now left|exact Hv].
    + apply Hpending. now right.
  - intros v Hv. apply in_app_iff in Hv. destruct Hv as [Hv|Hv].
    + apply Hnext with (u := x). exact Hv.
    + apply Hdomain. now right.
  - intros v Hv. destruct (Hr v Hv) as [Hs|[<-|Ht]].
    + left. now right.
    + left. now left.
    + right. apply in_or_app. now right.
  - intros u v [<-|Hu] Hv.
    + right. apply in_or_app. now left.
    + destruct (He u v Hu Hv) as [Hs|[<-|Ht]].
      * left. now right.
      * left. now left.
      * right. apply in_or_app. now right.
Qed.

Local Lemma skip_invariant next roots all unseen seen x todo :
  invariant next roots all unseen seen (x :: todo) -> ~ In x unseen ->
  invariant next roots all unseen seen todo.
Proof.
  intros Hinv Hx. destruct Hinv as [Hnd Hsupport Hseen Hpending Hdomain Hr He].
  assert (Hxseen : In x seen).
  { destruct (Hsupport x (Hdomain x (or_introl eq_refl))); tauto. }
  constructor; try assumption.
  - intros v Hv. apply Hpending. now right.
  - intros v Hv. apply Hdomain. now right.
  - intros v Hv. destruct (Hr v Hv) as [Hs|[<-|Ht]]; auto.
  - intros u v Hu Hv. destruct (He u v Hu Hv) as [Hs|[<-|Ht]]; auto.
Qed.

Local Lemma loop_correct next roots all fuel :
  (forall u, incl (next u) all) ->
  forall unseen seen pending,
  invariant next roots all unseen seen pending ->
  credit next unseen + length pending <= fuel ->
  fst (loop next fuel pending unseen seen) = [] /\
  invariant next roots all unseen (snd (loop next fuel pending unseen seen)) [].
Proof.
  intros Hnext. induction fuel as [|fuel IH]; intros unseen seen pending Hinv Hfuel.
  - destruct pending as [|x todo]; [cbn [loop fst snd]; auto|cbn in Hfuel; lia].
  - destruct pending as [|x todo]; [cbn [loop fst snd]; auto|].
    cbn [loop]. destruct (member x unseen) eqn:Hx.
    + apply member_spec in Hx.
      pose proof (remove_credit next x unseen (unseen_unique _ _ _ _ _ _ Hinv) Hx) as Hcredit.
      destruct (IH _ _ _ (fresh_invariant next roots all unseen seen x todo Hnext Hinv Hx)
        ltac:(rewrite length_app; cbn in Hfuel; lia)) as [Hdone Hfinal].
      split; [exact Hdone|].
      destruct Hfinal as [Hnd Hsupport Hseen Hpending Hdomain Hr He].
      constructor; try assumption.
      * exact (unseen_unique _ _ _ _ _ _ Hinv).
      * intros v Hv. destruct (Hsupport v Hv) as [Hu|Hs]; [left|now right].
        apply remove_spec in Hu. tauto.
    + assert (Hnot : ~ In x unseen) by (intro Hin; apply member_spec in Hin; congruence).
      apply IH.
      * now apply (skip_invariant next roots all unseen seen x todo).
      * cbn in Hfuel. lia.
Qed.

Definition set {V E} (p : Prepared.t V E) scope roots : FinSet.t positive :=
  let all := universe p in
  let next := successors p scope in
  let initial := roots_in p scope roots in
  FinSet.of_list positive_encoding
    (snd (loop next (credit next all + length initial) initial all [])).

(** The computed budget always empties the work stack, independently of graph readiness. *)
Theorem fuel_adequate {V E} (p : Prepared.t V E) scope roots :
  let all := universe p in
  let next := successors p scope in
  let initial := roots_in p scope roots in
  fst (loop next (credit next all + length initial) initial all []) = [].
Proof.
  cbn zeta.
  assert (Hnext : forall u, incl (successors p scope u) (universe p)).
  { intros u x Hx. unfold successors in Hx. apply filter_In in Hx.
    destruct Hx as [_ Hx]. apply andb_true_iff in Hx. apply member_spec. tauto. }
  assert (Hinitial : invariant (successors p scope) (roots_in p scope roots)
    (universe p) (universe p) [] (roots_in p scope roots)).
  { constructor.
    - apply NoDup_nodup.
    - auto.
    - intros x Hin. contradiction.
    - intros x Hin. now apply root.
    - intros x Hin. apply filter_In in Hin. tauto.
    - auto.
    - intros u x Hin. contradiction. }
  exact (proj1 (loop_correct _ _ _ _ Hnext _ _ _ Hinitial (Nat.le_refl _))).
Qed.

(** The reference result is a well-formed finite set for arbitrary computational inputs. *)
Theorem set_wf {V E} (p : Prepared.t V E) scope roots :
  FinSet.wf positive_encoding (set p scope roots).
Proof.
  unfold set. apply FinSet.wf_of_list.
Qed.

Local Lemma set_closure {V E} (p : Prepared.t V E) scope roots v :
  FinSet.mem positive_encoding v (set p scope roots) = true <->
  closure (successors p scope) (roots_in p scope roots) v.
Proof.
  unfold set. rewrite FinSet.mem_of_list.
  assert (Hmem : forall x xs, existsb (eqb positive_encoding x) xs = true <-> In x xs).
  { intros x xs. rewrite existsb_exists. split.
    - intros [y [Hy Hxy]]. apply (eqb_true_iff _ positive_encoding_laws) in Hxy.
      now subst y.
    - intro Hx. exists x. split; [exact Hx|apply eqb_refl]. }
  rewrite Hmem.
  assert (Hnext : forall u, incl (successors p scope u) (universe p)).
  { intros u x Hx. apply filter_In in Hx. destruct Hx as [_ Hx].
    apply andb_true_iff in Hx. apply member_spec. tauto. }
  assert (Hinitial : invariant (successors p scope) (roots_in p scope roots)
    (universe p) (universe p) [] (roots_in p scope roots)).
  { constructor.
    - apply NoDup_nodup.
    - auto.
    - intros x Hin. contradiction.
    - intros x Hin. now apply root.
    - intros x Hin. apply filter_In in Hin. tauto.
    - auto.
    - intros u x Hin. contradiction. }
  destruct (loop_correct _ _ _ _ Hnext _ _ _ Hinitial (Nat.le_refl _))
    as [_ Hfinal].
  split.
  - apply (seen_sound _ _ _ _ _ _ Hfinal).
  - intro Hreach. induction Hreach as [x Hx|u x Hu IH Hux].
    + destruct (roots_pending _ _ _ _ _ _ Hfinal x Hx); [assumption|contradiction].
    + destruct (edges_pending _ _ _ _ _ _ Hfinal u x IH Hux);
        [assumption|contradiction].
Qed.

Local Lemma present_spec {A B} (f : A -> option B) xs y :
  In y (Prepared.present f xs) <-> exists x, In x xs /\ f x = Some y.
Proof.
  induction xs as [|x rest IH]; cbn [Prepared.present]; [firstorder|].
  destruct (f x) as [a|] eqn:Hx; cbn; rewrite IH; split.
  - intros [<-|[b [Hb Hfb]]]; [exists x; auto|exists b; auto].
  - intros [b [[<-|Hb] Hfb]]; [left; congruence|right; exists b; auto].
  - intros [b [Hb Hfb]]. exists b. auto.
  - intros [b [[<-|Hb] Hfb]]; [congruence|exists b; auto].
Qed.

(** The reference universe contains exactly valid prepared IDs, even before readiness. *)
Theorem universe_spec {V E} (p : Prepared.t V E) v :
  In v (universe p) <-> Prepared.valid_id p v.
Proof.
  unfold universe, Prepared.valid_id. rewrite nodup_In, present_spec. reflexivity.
Qed.

Local Lemma successors_spec {V E} (p : Prepared.t V E) scope u v :
  Prepared.ready p -> Prepared.valid_id p u ->
  (In v (successors p scope u) <->
    Scope.admits scope v = true /\ exists e, Prepared.arc p u e v).
Proof.
  intros [Hwf [_ Hp]] [a [Ha Hu]].
  unfold successors. rewrite filter_In, andb_true_iff, member_spec, universe_spec.
  split.
  - intros [Hin [Hallowed Hvalid]].
    apply in_map_iff in Hin. destruct Hin as [[e j] [Heq Hedge]].
    cbn in Heq. subst j.
    apply (Prepared.succ_spec p a u e v Hp Hu) in Hedge. destruct Hedge as [He Hv].
    split; [exact Hallowed|]. exists e, a, (Graph.target (Prepared.graph p) e).
    repeat split; auto. exact (out_source Hwf a e He).
  - intros [Hallowed [e [a' [b [Ha' [Hu' [Hv [Hs [Ht He]]]]]]]]].
    assert (Hnames : a' = a).
    { pose proof (Prepared.name_of_id_of p a u Hp Hu).
      pose proof (Prepared.name_of_id_of p a' u Hp Hu'). congruence. }
    rewrite Hnames in He. split.
    + apply in_map_iff. exists (e, v). split; [reflexivity|].
      apply (Prepared.succ_spec p a u e v Hp Hu). split; [exact He|now rewrite Ht].
    + split; [exact Hallowed|]. exists b. split; [|exact Hv].
      rewrite <- Ht. exact (out_target_in Hwf a e Ha He).
Qed.

Local Lemma scoped_endpoint {V E} (p : Prepared.t V E) scope a es b :
  Search.scoped_path p scope a es b ->
  Prepared.valid_id p b /\ Scope.admits scope b = true.
Proof.
  intro H. induction H; auto.
Qed.

Local Lemma scoped_start {V E} (p : Prepared.t V E) scope a es b :
  Search.scoped_path p scope a es b ->
  Prepared.valid_id p a /\ Scope.admits scope a = true.
Proof.
  intro H. destruct H; auto.
Qed.

Local Lemma scoped_snoc {V E} (p : Prepared.t V E) scope a es b e c :
  Search.scoped_path p scope a es b -> Prepared.arc p b e c ->
  Prepared.valid_id p c -> Scope.admits scope c = true ->
  Search.scoped_path p scope a (es ++ [e]) c.
Proof.
  intros Hpath Hedge Hvalid Hallowed.
  induction Hpath as [v Hv Ha|u f v tail z Hu Ha Hf Htail IH]; cbn.
  - econstructor; [exact Hv|exact Ha|exact Hedge|now constructor].
  - econstructor; eauto.
Qed.

Local Lemma closure_scoped {V E} (p : Prepared.t V E) scope roots v :
  Prepared.ready p ->
  (closure (successors p scope) (roots_in p scope roots) v <->
    Search.scoped_reachable p scope roots v).
Proof.
  intro Hready. split.
  - intro H. induction H as [v Hv|u v Hu IH Huv].
    + apply filter_In in Hv. destruct Hv as [Hv Hroot].
      apply andb_true_iff in Hroot. destruct Hroot as [Hr Ha].
      apply member_spec in Hr. exists v, []. split; [exact Hr|].
      constructor; [now apply universe_spec|exact Ha].
    + destruct IH as [r [es [Hr Hpath]]].
      destruct (scoped_endpoint _ _ _ _ _ Hpath) as [Hvalid _].
      apply (successors_spec p scope u v Hready Hvalid) in Huv.
      destruct Huv as [Ha [e He]].
      exists r, (es ++ [e]). split; [exact Hr|].
      apply scoped_snoc with (b := u); try assumption.
      destruct He as [a [b [Ha' [Hi [Hj [Hs [Ht Hedge]]]]]]].
      exists b. split; [|exact Hj].
      rewrite <- Ht. eapply out_target_in; [exact (proj1 Hready)|exact Ha'|exact Hedge].
  - intros [r [es [Hr Hpath]]].
    assert (Hroot : closure (successors p scope) (roots_in p scope roots) r).
    { inversion Hpath as [x Hv Ha|x e y tail z Hv Ha He Htail]; subst.
      - apply root. apply filter_In. split; [now apply universe_spec|].
        apply andb_true_iff. split; [now apply member_spec|exact Ha].
      - apply root. apply filter_In. split; [now apply universe_spec|].
        apply andb_true_iff. split; [now apply member_spec|exact Ha]. }
    clear Hr. induction Hpath as [x Hv Ha|u e x tail z Hu Ha He Htail IH].
    + exact Hroot.
    + apply IH. eapply edge; [exact Hroot|].
      apply (successors_spec p scope u x Hready Hu).
      split; [exact (proj2 (scoped_start _ _ _ _ _ Htail))|now exists e].
Qed.

(** Membership is precisely reachability from the supplied roots through admitted valid IDs. *)
Theorem exact {V E} (p : Prepared.t V E) scope roots v :
  Prepared.ready p ->
  (FinSet.mem positive_encoding v (set p scope roots) = true <->
    Search.scoped_reachable p scope roots v).
Proof.
  intro Hready. rewrite set_closure. now apply closure_scoped.
Qed.

Definition unrestricted := Scope.Make FinSet.empty None.

Definition blocked d := Scope.Make (FinSet.add positive_encoding d FinSet.empty) None.

(** The blocked scope stores exactly the singleton produced by the public set constructor. *)
Theorem blocked_equation d :
  blocked d = Scope.Make (FinSet.add positive_encoding d FinSet.empty) None.
Proof.
  reflexivity.
Qed.

(** Every ID is admitted by the unrestricted scope. *)
Theorem admits_unrestricted v : Scope.admits unrestricted v = true.
Proof.
  rewrite Scope.admits_equation.
  cbn [unrestricted Scope.blocked Scope.within].
  rewrite FinSet.mem_empty. reflexivity.
Qed.

Local Lemma admits_blocked d v :
  Scope.admits (blocked d) v = true <-> v <> d.
Proof.
  rewrite Scope.admits_equation. cbn [blocked Scope.blocked Scope.within].
  rewrite andb_true_r, negb_true_iff, <- not_true_iff_false.
  rewrite FinSet.mem_add by apply FinSet.wf_empty.
  rewrite FinSet.mem_empty, orb_false_r, (eqb_true_iff _ positive_encoding_laws).
  reflexivity.
Qed.

Local Lemma id_injective {V E} (p : Prepared.t V E) a b i :
  Prepared.laws p ->
  Prepared.id_of p a = Some i -> Prepared.id_of p b = Some i -> a = b.
Proof.
  intros Hp Ha Hb.
  pose proof (Prepared.name_of_id_of p a i Hp Ha).
  pose proof (Prepared.name_of_id_of p b i Hp Hb). congruence.
Qed.

Local Lemma entries_spec {V E} (p : Prepared.t V E) i :
  Prepared.laws p ->
  (In i (Prepared.entry_ids p) <->
    exists a, In a (Graph.entries (Prepared.graph p)) /\ Prepared.id_of p a = Some i).
Proof.
  intro Hp. rewrite (Prepared.entries_agree p Hp).
  unfold Prepared.ids. apply present_spec.
Qed.

Local Lemma lower_path {V E} (p : Prepared.t V E) scope i es j :
  Prepared.laws p -> Search.scoped_path p scope i es j ->
  forall a b, Prepared.id_of p a = Some i -> Prepared.id_of p b = Some j ->
    path (Prepared.graph p) a es b.
Proof.
  intros Hp Hpath. induction Hpath as [v Hv Ha|u e v tail z Hu Ha He Htail IH];
    intros a b Hi Hj.
  - assert (a = b) by (eapply id_injective; eauto). subst b. constructor.
  - destruct He as [x [y [Hx [Hix [Hiy [Hs [Ht Hedge]]]]]]].
    assert (a = x) by (eapply id_injective; eauto). subst a.
    rewrite <- Hs. constructor.
    + now rewrite Hs.
    + rewrite Ht. apply IH; assumption.
Qed.

Local Lemma lift_path {V E} (p : Prepared.t V E) a es b :
  Prepared.ready p -> path (Prepared.graph p) a es b ->
  forall i j, In a (Graph.nodes (Prepared.graph p)) ->
  Prepared.id_of p a = Some i -> Prepared.id_of p b = Some j ->
  Search.scoped_path p unrestricted i es j.
Proof.
  intros [Hwf [Hout Hp]] Hpath.
  induction Hpath as [v|e tail z Hedge Htail IH]; intros i j Ha Hi Hj.
  - assert (i = j) by congruence. subst j. constructor.
    + now exists v.
    + apply admits_unrestricted.
  - assert (Ht : In (Graph.target (Prepared.graph p) e)
        (Graph.nodes (Prepared.graph p))) by (eapply out_target_in; eauto).
    destruct (proj1 (Prepared.ids_domain p Hp _) Ht) as [k Hk].
    eapply Search.scoped_cons with (v := k).
    + now exists (Graph.source (Prepared.graph p) e).
    + apply admits_unrestricted.
    + exists (Graph.source (Prepared.graph p) e), (Graph.target (Prepared.graph p) e).
      repeat split; try reflexivity; assumption.
    + apply IH; assumption.
Qed.

(** The entry-rooted unrestricted ID closure agrees with source-graph reachability. *)
Theorem entries_exact {V E} (p : Prepared.t V E) n i :
  Prepared.ready p -> Prepared.id_of p n = Some i ->
  (FinSet.mem positive_encoding i (set p unrestricted (Prepared.entry_ids p)) = true <->
    reachable (Prepared.graph p) n).
Proof.
  intros Hready Hi. rewrite exact by exact Hready.
  destruct Hready as [Hwf [Hout Hp]]. split.
  - intros [r [es [Hr Hpath]]]. apply (entries_spec p r Hp) in Hr.
    destruct Hr as [a [Ha Hia]]. apply reachable_iff_path.
    exists a, es. split; [exact Ha|eapply lower_path; eauto].
  - intro Hreach. apply reachable_iff_path in Hreach.
    destruct Hreach as [a [es [Ha Hpath]]].
    destruct (proj1 (Prepared.ids_domain p Hp _) (entries_in Hwf a Ha)) as [r Hr].
    exists r, es. split.
    + apply (entries_spec p r Hp). now exists a.
    + eapply lift_path.
      * exact (conj Hwf (conj Hout Hp)).
      * exact Hpath.
      * exact (entries_in Hwf a Ha).
      * exact Hr.
      * exact Hi.
Qed.

Local Lemma lower_blocked_path {V E} (p : Prepared.t V E) d u i es j :
  Prepared.laws p -> Prepared.id_of p d = Some u ->
  Search.scoped_path p (blocked u) i es j ->
  forall a b, Prepared.id_of p a = Some i -> Prepared.id_of p b = Some j ->
    path (without (eqb_c (Prepared.node_enc p)) d (Prepared.graph p)) a es b.
Proof.
  intros Hp Hd Hpath.
  induction Hpath as [v Hv Ha|v e w tail z Hv Ha He Htail IH]; intros a b Hi Hj.
  - assert (a = b) by (eapply id_injective; eauto). subst b. constructor.
  - destruct He as [x [y [Hx [Hix [Hiy [Hs [Ht Hedge]]]]]]].
    assert (a = x) by (eapply id_injective; eauto). subst a.
    rewrite <- Hs.
    refine (@path_cons V E
      (without (eqb_c (Prepared.node_enc p)) d (Prepared.graph p)) e tail b _ _).
    + rewrite without_out. apply filter_In. split.
      * change (In e (Graph.out (Prepared.graph p) (Graph.source (Prepared.graph p) e))).
        now rewrite Hs.
      * apply negb_true_iff, (eqb_false_iff _ (Prepared.encoding_valid p Hp)).
        intro Hdy. rewrite Ht in Hdy.
        pose proof (proj2 (scoped_start _ _ _ _ _ Htail)) as Hfree.
        apply admits_blocked in Hfree. apply Hfree. congruence.
    + change (path (without (eqb_c (Prepared.node_enc p)) d (Prepared.graph p))
        (Graph.target (Prepared.graph p) e) tail b).
      rewrite Ht. apply IH; assumption.
Qed.

Local Lemma lift_blocked_path {V E} (p : Prepared.t V E) d u a es b :
  Prepared.ready p -> Prepared.id_of p d = Some u ->
  path (without (eqb_c (Prepared.node_enc p)) d (Prepared.graph p)) a es b ->
  forall i j, In a (Graph.nodes (Prepared.graph p)) ->
  Prepared.id_of p a = Some i -> Prepared.id_of p b = Some j -> i <> u ->
  Search.scoped_path p (blocked u) i es j.
Proof.
  intros [Hwf [Hout Hp]] Hd Hpath.
  induction Hpath as [v|e tail z Hedge Htail IH]; intros i j Ha Hi Hj Hfree.
  - assert (i = j) by congruence. subst j. constructor.
    + now exists v.
    + now apply admits_blocked.
  - rewrite without_out in Hedge. apply filter_In in Hedge.
    destruct Hedge as [Hedge Htarget]. apply negb_true_iff in Htarget.
    apply (eqb_false_iff _ (Prepared.encoding_valid p Hp)) in Htarget.
    change (In e (Graph.out (Prepared.graph p) (Graph.source (Prepared.graph p) e))) in Hedge.
    assert (Ht : In (Graph.target (Prepared.graph p) e) (Graph.nodes (Prepared.graph p))).
    { eapply out_target_in; eauto. }
    destruct (proj1 (Prepared.ids_domain p Hp _) Ht) as [k Hk].
    eapply Search.scoped_cons with (v := k).
    + now exists (Graph.source (Prepared.graph p) e).
    + now apply admits_blocked.
    + exists (Graph.source (Prepared.graph p) e), (Graph.target (Prepared.graph p) e).
      repeat split; try reflexivity; assumption.
    + apply IH; try assumption.
      intro Heq. subst k. apply Htarget. eapply id_injective; eauto.
Qed.

Local Lemma deleted_exact {V E} (p : Prepared.t V E) d n u v :
  Prepared.ready p -> Prepared.id_of p d = Some u -> Prepared.id_of p n = Some v ->
  (Search.scoped_reachable p (blocked u) (Prepared.entry_ids p) v <->
    reachable (without (eqb_c (Prepared.node_enc p)) d (Prepared.graph p)) n).
Proof.
  intros Hready Hd Hn. destruct Hready as [Hwf [Hout Hp]]. split.
  - intros [r [es [Hr Hpath]]]. apply (entries_spec p r Hp) in Hr.
    destruct Hr as [a [Ha Hi]]. apply reachable_iff_path.
    exists a, es. split.
    + change (In a (filter (fun x => negb (eqb (Prepared.node_enc p) x d))
        (Graph.entries (Prepared.graph p)))).
      apply filter_In. split; [exact Ha|].
      apply negb_true_iff, (eqb_false_iff _ (Prepared.encoding_valid p Hp)).
      intro Heq. subst a.
      pose proof (proj2 (scoped_start _ _ _ _ _ Hpath)) as Hfree.
      apply admits_blocked in Hfree. apply Hfree. congruence.
    + eapply lower_blocked_path; eauto.
  - intro Hreach. apply reachable_iff_path in Hreach.
    destruct Hreach as [a [es [Ha Hpath]]].
    change (In a (filter (fun x => negb (eqb (Prepared.node_enc p) x d))
      (Graph.entries (Prepared.graph p)))) in Ha.
    apply filter_In in Ha. destruct Ha as [Ha Hfree].
    apply negb_true_iff in Hfree.
    apply (eqb_false_iff _ (Prepared.encoding_valid p Hp)) in Hfree.
    destruct (proj1 (Prepared.ids_domain p Hp _) (entries_in Hwf a Ha)) as [r Hr].
    exists r, es. split.
    + apply (entries_spec p r Hp). now exists a.
    + eapply lift_blocked_path; eauto.
      * exact (conj Hwf (conj Hout Hp)).
      * eapply entries_in; eauto.
      * intro Heq. subst r. apply Hfree. eapply id_injective; eauto.
Qed.

(** Deleting a named ID removes precisely its dominated nodes from entry reachability. *)
Theorem avoiding {V E} (p : Prepared.t V E) d n u v :
  Prepared.ready p -> Prepared.id_of p d = Some u -> Prepared.id_of p n = Some v ->
  (dominates (Prepared.graph p) d n <->
    FinSet.mem positive_encoding v (set p (blocked u) (Prepared.entry_ids p)) = false).
Proof.
  intros Hready Hd Hn. rewrite <- not_true_iff_false.
  rewrite exact by exact Hready. rewrite (deleted_exact p d n u v Hready Hd Hn).
  apply dominates_iff_unreachable_without.
  exact (Prepared.encoding_valid p (proj2 (proj2 Hready))).
Qed.

Arguments set {V E} p scope roots : simpl never.

End Reach.
