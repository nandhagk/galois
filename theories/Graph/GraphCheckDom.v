(** * Independent immediate-dominator validation

    Parent paths receive nested intervals and are checked against dominance by deletion.
    For example, both arms of a diamond have the entry as parent.
    Soundness requires a separate Map.wf certificate for the supplied parent representation.
    A future certificate constructor must retain that premise or validate the representation.
    Builds on: GraphDomSpec, GraphReach and BaseMap. *)

From Stdlib Require Import List Bool PArith NArith Arith Lia.
From Stdlib.Relations Require Import Relation_Operators.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet BaseIntern.
From Galois.Graph Require Import GraphModel GraphPrepared GraphSearchSpec GraphDomSpec GraphReach.
Import List.ListNotations Dom.

Module DomCheck.

Definition parent (m : Map.t positive positive) v := Map.get positive_encoding v m.

Fixpoint chain fuel m v :=
  v :: match fuel with
  | O => []
  | S fuel =>
    match parent m v with
    | None => []
    | Some u => chain fuel m u
    end
  end.

Fixpoint ends fuel m v :=
  match fuel with
  | O => false
  | S fuel =>
    match parent m v with
    | None => true
    | Some u => ends fuel m u
    end
  end.

Definition ancestor_b m d n := existsb (Pos.eqb d) (chain (Map.size m) m n).

Local Lemma ancestor_cases m d n :
  idom_ancestor m d n ->
  d = n \/ exists u, parent m n = Some u /\ idom_ancestor m d u.
Proof.
  intro H. induction H as [u v Huv|v|u w v Huw IHuw Hwv IHwv].
  - right. exists u. split; [exact Huv|apply rt_refl].
  - now left.
  - destruct IHwv as [->|[p [Hp Hup]]].
    + exact IHuw.
    + right. exists p. split; [exact Hp|]. eapply rt_trans; eassumption.
Qed.

Local Lemma chain_sound fuel m n d :
  In d (chain fuel m n) -> idom_ancestor m d n.
Proof.
  revert n. induction fuel as [|fuel IH]; intros n Hin; cbn [chain] in Hin.
  - destruct Hin as [<-|Hin]; [apply rt_refl|contradiction].
  - destruct Hin as [<-|Hin]; [apply rt_refl|].
    destruct (parent m n) as [u|] eqn:Hu; [|contradiction].
    eapply rt_trans; [apply IH; exact Hin|apply rt_step; exact Hu].
Qed.

Local Lemma ends_ancestor fuel m n :
  ends (S fuel) m n = true ->
  forall d, idom_ancestor m d n -> In d (chain fuel m n).
Proof.
  revert n. induction fuel as [|fuel IH]; intros n Hends d Hanc;
    apply ancestor_cases in Hanc; destruct Hanc as [->|[u [Hu Hanc]]].
  - now left.
  - cbn [ends] in Hends. rewrite Hu in Hends. discriminate.
  - now left.
  - cbn [ends] in Hends. rewrite Hu in Hends.
    cbn [chain]. rewrite Hu. right. apply IH; assumption.
Qed.

Local Lemma ends_acc fuel m n :
  ends fuel m n = true -> Acc (fun u v => parent m v = Some u) n.
Proof.
  revert n. induction fuel as [|fuel IH]; intros n Hends; [discriminate|].
  cbn [ends] in Hends. constructor. intros u Hu.
  rewrite Hu in Hends. now apply IH.
Qed.

Local Lemma acc_no_return m n :
  Acc (fun u v => parent m v = Some u) n ->
  forall v, parent m v = Some n -> ~ idom_ancestor m v n.
Proof.
  intro Hacc. induction Hacc as [n Hacc IH]. intros v Hnv Hanc.
  apply ancestor_cases in Hanc. destruct Hanc as [Heq|[p [Hp Hvp]]].
  - subst v. apply (IH n Hnv n Hnv). apply rt_refl.
  - apply (IH p Hp n Hp). eapply rt_trans; [apply rt_step; exact Hnv|exact Hvp].
Qed.

Local Lemma chain_nodup fuel m :
  well_founded (fun u v => parent m v = Some u) ->
  forall n, NoDup (chain fuel m n).
Proof.
  intro Hwf. induction fuel as [|fuel IH]; intro n; cbn [chain].
  - constructor; [tauto|constructor].
  - constructor.
    + destruct (parent m n) as [u|] eqn:Hu; [|tauto].
      intro Hin. apply (acc_no_return m u (Hwf u) n Hu).
      now apply (chain_sound fuel m u n).
    + destruct (parent m n); [apply IH|constructor].
Qed.

Local Lemma not_ends fuel m n :
  ends (S fuel) m n = false ->
  length (chain fuel m n) = S fuel /\
  forall v, In v (chain fuel m n) -> exists u, parent m v = Some u.
Proof.
  revert n. induction fuel as [|fuel IH]; intros n Hends.
  - cbn [ends] in Hends. destruct (parent m n) as [u|] eqn:Hu; [|discriminate].
    split; [reflexivity|]. intros v [<-|Hin]; [now exists u|contradiction].
  - cbn [ends] in Hends. destruct (parent m n) as [u|] eqn:Hu; [|discriminate].
    destruct (IH u Hends) as [Hlength Hdomain].
    cbn [chain]. rewrite Hu. split; [cbn; now rewrite Hlength|].
    intros v [<-|Hin]; [now exists u|now apply Hdomain].
Qed.

(** A well-founded parent map terminates every chain within its binding-count budget. *)
Theorem ends_complete m :
  Map.wf positive_encoding m ->
  well_founded (fun u v => parent m v = Some u) ->
  forall n, ends (S (Map.size m)) m n = true.
Proof.
  intros Hmap Hwf n. destruct (ends (S (Map.size m)) m n) eqn:Hends; [reflexivity|].
  destruct (not_ends _ _ _ Hends) as [Hlength Hdomain]. exfalso.
  assert (Hincl : incl (chain (Map.size m) m n) (map fst (Map.elements m))).
  { intros v Hv. destruct (Hdomain v Hv) as [u Hu].
    apply in_map_iff. exists (v, u). split; [reflexivity|].
    apply (Map.elements_spec positive_encoding positive_encoding_laws); assumption. }
  pose proof (NoDup_incl_length (chain_nodup _ _ Hwf n) Hincl) as Hbound.
  rewrite length_map, <- Map.size_elements, Hlength in Hbound. lia.
Qed.

(** The bounded parent walk recognizes exactly ancestry when the child's chain terminates. *)
Theorem ancestor_b_spec m d n :
  ends (S (Map.size m)) m n = true ->
  (ancestor_b m d n = true <-> idom_ancestor m d n).
Proof.
  intro Hends. unfold ancestor_b. rewrite existsb_exists. split.
  - intros [u [Hu Hdu]]. apply Pos.eqb_eq in Hdu. subst u. now apply chain_sound in Hu.
  - intro Hanc. exists d. split; [now apply ends_ancestor|apply Pos.eqb_refl].
Qed.

Local Lemma chain_length fuel m n : (length (chain fuel m n) <= S fuel)%nat.
Proof.
  revert n. induction fuel as [|fuel IH]; intro n; cbn [chain]; [cbn; lia|].
  destruct (parent m n) as [u|]; cbn [length]; [pose proof (IH u); lia|lia].
Qed.

Local Lemma chain_agrees f g m n :
  ends (S f) m n = true -> ends (S g) m n = true ->
  chain f m n = chain g m n.
Proof.
  revert g n. induction f as [|f IH]; intros [|g] n Hf Hg;
    cbn [ends] in Hf, Hg; cbn [chain];
    destruct (parent m n) as [u|] eqn:Hu; try reflexivity; try discriminate.
  f_equal. apply IH; assumption.
Qed.

Definition root_path m n := rev (chain (Map.size m) m n).

Local Lemma chain_self fuel m n : In n (chain fuel m n).
Proof.
  destruct fuel; cbn [chain]; now left.
Qed.

(** Prefixes describe membership in the same root-to-node parent path. *)
Definition prefix {A} (xs ys : list A) := exists tail, ys = xs ++ tail.

Local Lemma chain_suffix m :
  (forall n, ends (S (Map.size m)) m n = true) ->
  forall fuel n, ends (S fuel) m n = true ->
  forall u, In u (chain fuel m n) ->
  exists pre, chain fuel m n = pre ++ chain (Map.size m) m u.
Proof.
  intros Hend. induction fuel as [|fuel IH]; intros n Hends u Hin.
  - cbn [chain] in Hin. destruct Hin as [<-|Hin]; [|contradiction].
    exists []. exact (chain_agrees 0 (Map.size m) m n Hends (Hend n)).
  - cbn [chain] in Hin. destruct Hin as [<-|Hin].
    + exists []. exact (chain_agrees (S fuel) (Map.size m) m n Hends (Hend n)).
    + cbn [ends] in Hends. destruct (parent m n) as [v|] eqn:Hv; [|contradiction].
      destruct (IH v Hends u Hin) as [pre Hpre].
      exists (n :: pre). cbn [chain]. rewrite Hv. cbn. now rewrite Hpre.
Qed.

Local Lemma root_prefix m :
  (forall n, ends (S (Map.size m)) m n = true) ->
  forall d n, prefix (root_path m d) (root_path m n) <-> idom_ancestor m d n.
Proof.
  intros Hend d n. split.
  - intros [tail Heq]. apply (chain_sound (Map.size m) m n d).
    apply (proj2 (in_rev _ _)). change (In d (root_path m n)).
    rewrite Heq. apply in_or_app. left. unfold root_path.
    apply (proj1 (in_rev _ _)). apply chain_self.
  - intro Hanc. pose proof (ends_ancestor _ _ _ (Hend n) d Hanc) as Hin.
    destruct (chain_suffix m Hend _ n (Hend n) d Hin) as [pre Hpre].
    exists (rev pre). unfold root_path. rewrite Hpre, rev_app_distr. reflexivity.
Qed.

Section PrefixIntervals.
Variable radix : N.
Hypothesis Hradix : (1 < radix)%N.

Fixpoint width depth : N :=
  match depth with
  | O => 1%N
  | S depth => (radix * width depth)%N
  end.

Fixpoint interval depth (xs : list positive) : N * N :=
  match xs, depth with
  | [], _ => (0%N, (width depth - 1)%N)
  | x :: rest, S depth =>
    let '(lo, hi) := interval depth rest in
    ((N.pos x * width depth + lo)%N, (N.pos x * width depth + hi)%N)
  | _ :: _, O => (0%N, 0%N)
  end.

Local Lemma width_positive depth : (0 < width depth)%N.
Proof.
  induction depth; cbn [width]; nia.
Qed.

Local Lemma interval_bounds depth xs :
  (length xs <= depth)%nat -> Forall (fun x => (N.pos x < radix)%N) xs ->
  (fst (interval depth xs) <= snd (interval depth xs) < width depth)%N.
Proof.
  revert xs. induction depth as [|depth IH]; intros [|x rest] Hlength Hdigits;
    cbn [length] in Hlength; try solve [exfalso; lia].
  - cbn [interval width fst snd]. lia.
  - cbn [interval fst snd]. pose proof (width_positive (S depth)). lia.
  - inversion Hdigits as [|a tail Hx Hrest]; subst.
    specialize (IH rest ltac:(lia) Hrest).
    destruct (interval depth rest) as [lo hi] eqn:Hint. cbn [fst snd] in IH.
    cbn [interval]. rewrite Hint.
    pose proof (width_positive depth). cbn [fst snd width]. nia.
Qed.

Local Lemma prefix_cons {A} (x y : A) xs ys :
  prefix (x :: xs) (y :: ys) <-> x = y /\ prefix xs ys.
Proof.
  split.
  - intros [tail Heq]. cbn in Heq. injection Heq as <- Hrest.
    split; [reflexivity|exists tail; exact Hrest].
  - intros [-> [tail Htail]]. exists tail. cbn. now rewrite Htail.
Qed.

Local Lemma interval_prefix depth xs ys :
  (length xs <= depth)%nat -> (length ys <= depth)%nat ->
  Forall (fun x => (N.pos x < radix)%N) xs ->
  Forall (fun x => (N.pos x < radix)%N) ys ->
  ((fst (interval depth xs) <= fst (interval depth ys) /\
      snd (interval depth ys) <= snd (interval depth xs))%N <-> prefix xs ys).
Proof.
  revert xs ys. induction depth as [|depth IH]; intros [|x xs] [|y ys] Hxlen Hylen Hxs Hys;
    cbn [length] in Hxlen, Hylen; try solve [exfalso; lia].
  - cbn [interval width fst snd]. split; [intros _; exists []; reflexivity|intros _; lia].
  - cbn [interval fst snd]. split.
    + intros _. exists []. reflexivity.
    + intros _. pose proof (width_positive (S depth)). lia.
  - split.
    + intros _. exists (y :: ys). reflexivity.
    + intros _. pose proof (interval_bounds (S depth) (y :: ys) Hylen Hys) as Hb.
      change ((0 <= fst (interval (S depth) (y :: ys)) /\
        snd (interval (S depth) (y :: ys)) <= width (S depth) - 1)%N).
      lia.
  - split.
    + intro Hcontain.
      destruct (interval depth xs) as [lo hi] eqn:Hinterval.
      cbn [interval] in Hcontain. rewrite Hinterval in Hcontain.
      cbn [fst snd] in Hcontain.
      pose proof (width_positive depth).
      assert (0 < N.pos x)%N by lia. nia.
    + intros [tail Heq]. discriminate.
  - inversion Hxs as [|a tail Hxd Hxt]; subst.
    inversion Hys as [|a tail Hyd Hyt]; subst.
    pose proof (interval_bounds depth xs ltac:(lia) Hxt) as Hxb.
    pose proof (interval_bounds depth ys ltac:(lia) Hyt) as Hyb.
    specialize (IH xs ys ltac:(lia) ltac:(lia) Hxt Hyt).
    destruct (interval depth xs) as [xl xh] eqn:Hx.
    destruct (interval depth ys) as [yl yh] eqn:Hy.
    cbn [fst snd] in Hxb, Hyb, IH.
    cbn [interval]. rewrite Hx, Hy. cbn [fst snd]. rewrite prefix_cons.
    destruct (Pos.eq_dec x y) as [->|Hne].
    + rewrite <- IH. lia.
    + split; [|intros [Heq _]; contradiction].
      intros [Hlo Hhi]. exfalso.
      pose proof (width_positive depth).
      assert (Hcodes : N.pos x <> N.pos y) by congruence.
      assert (Horder : (N.pos x < N.pos y \/ N.pos y < N.pos x)%N) by lia.
      destruct Horder; nia.
Qed.

End PrefixIntervals.

Definition radix {V E} (p : Prepared.t V E) := N.succ (N.pos (Intern.next (Prepared.names p))).

Definition labels {V E} (p : Prepared.t V E) m v :=
  let '(lo, hi) := interval (radix p) (S (Map.size m)) (root_path m v) in
  (N.succ_pos lo, N.succ_pos hi).

Fixpoint number_map (f : positive -> positive) vs : Map.t positive positive :=
  match vs with
  | [] => Map.empty
  | v :: rest => Map.set positive_encoding v (f v) (number_map f rest)
  end.

Definition live {V E} (p : Prepared.t V E) :=
  FinSet.elements (Reach.set p Reach.unrestricted (Prepared.entry_ids p)).

(** Number the supplied forest by nested radix intervals of its root-to-node paths. *)
Definition of_parents {V E} (p : Prepared.t V E) m : tree :=
  Tree m (number_map (fun v => fst (labels p m v)) (live p))
    (number_map (fun v => snd (labels p m v)) (live p)).

(** Numbering retains the supplied parent map as the exact computational value. *)
Theorem of_parents_idom {V E} (p : Prepared.t V E) m : idom (of_parents p m) = m.
Proof.
  reflexivity.
Qed.

Definition dominates_b t d n :=
  match Map.get positive_encoding d (tin t), Map.get positive_encoding n (tin t),
    Map.get positive_encoding n (tout t), Map.get positive_encoding d (tout t) with
  | Some a, Some b, Some c, Some e => Pos.leb a b && Pos.leb c e
  | _, _, _, _ => false
  end.

Local Lemma live_spec {V E} (p : Prepared.t V E) n i :
  Prepared.ready p -> Prepared.id_of p n = Some i ->
  (In i (live p) <-> reachable (Prepared.graph p) n).
Proof.
  intros Hready Hi. unfold live.
  rewrite (FinSet.elements_spec positive_encoding positive_encoding_laws)
    by apply Reach.set_wf.
  now apply Reach.entries_exact.
Qed.

Local Lemma live_named {V E} (p : Prepared.t V E) i :
  Prepared.ready p -> In i (live p) ->
  exists n, Prepared.id_of p n = Some i /\ reachable (Prepared.graph p) n.
Proof.
  intros Hready Hin.
  assert (Hreach : Search.scoped_reachable p Reach.unrestricted (Prepared.entry_ids p) i).
  { apply Reach.exact; [exact Hready|].
    apply (FinSet.elements_spec positive_encoding positive_encoding_laws);
      [apply Reach.set_wf|exact Hin]. }
  destruct Hreach as [r [es [_ Hpath]]].
  assert (Hvalid : Prepared.valid_id p i) by (induction Hpath; auto).
  destruct Hvalid as [n [Hnode Hi]]. exists n. split; [exact Hi|].
  apply (live_spec p n i Hready Hi). exact Hin.
Qed.

Local Lemma number_map_wf f vs : Map.wf positive_encoding (number_map f vs).
Proof.
  induction vs as [|v rest IH]; cbn [number_map].
  - apply Map.wf_empty.
  - now apply Map.wf_set.
Qed.

Local Lemma number_map_get f vs v :
  In v vs -> Map.get positive_encoding v (number_map f vs) = Some (f v).
Proof.
  induction vs as [|u rest IH]; intro Hin; [contradiction|].
  cbn [number_map]. destruct (Pos.eq_dec v u) as [->|Hne].
  - apply Map.get_set_same, number_map_wf.
  - rewrite (Map.get_set_other positive_encoding positive_encoding_laws)
      by (try apply number_map_wf; exact Hne).
    apply IH. destruct Hin; [congruence|assumption].
Qed.

(** A parent forest has reachable endpoints and no infinite ascending parent chain. *)
Definition forest {V E} (p : Prepared.t V E) m :=
  (forall v u, parent m v = Some u -> In v (live p) /\ In u (live p)) /\
  well_founded (fun u v => parent m v = Some u).

Local Lemma ancestor_live {V E} (p : Prepared.t V E) m :
  (forall v u, parent m v = Some u -> In v (live p) /\ In u (live p)) ->
  forall d n, idom_ancestor m d n -> In n (live p) -> In d (live p).
Proof.
  intros Hdomain d n Hanc. induction Hanc as [u v Huv|v|u w v Huw IHuw Hwv IHwv];
    intro Hn.
  - exact (proj2 (Hdomain v u Huv)).
  - exact Hn.
  - apply IHuw, IHwv. exact Hn.
Qed.

Local Lemma root_digits {V E} (p : Prepared.t V E) m n :
  Prepared.ready p ->
  (forall v u, parent m v = Some u -> In v (live p) /\ In u (live p)) ->
  In n (live p) ->
  Forall (fun x => (N.pos x < radix p)%N) (root_path m n).
Proof.
  intros Hready Hdomain Hn. apply Forall_forall. intros x Hx.
  unfold root_path in Hx. apply (proj2 (in_rev _ _)) in Hx.
  pose proof (chain_sound _ _ _ _ Hx) as Hanc.
  destruct (live_named p x Hready (ancestor_live p m Hdomain x n Hanc Hn))
    as [a [Ha _]].
  pose proof (proj2 (Prepared.ids_dense p (proj2 (proj2 Hready)) x)
    (ex_intro _ a Ha)) as Hbound.
  change (N.pos x < N.pos (Intern.next (Prepared.names p)))%N in Hbound.
  unfold radix. lia.
Qed.

Local Lemma succ_pos_value n : N.pos (N.succ_pos n) = N.succ n.
Proof.
  destruct n; reflexivity.
Qed.

Local Lemma positive_le_N a b : (a <= b)%positive <-> (N.pos a <= N.pos b)%N.
Proof.
  reflexivity.
Qed.

Local Lemma labels_spec {V E} (p : Prepared.t V E) m d n :
  Prepared.ready p -> Map.wf positive_encoding m -> forest p m ->
  In d (live p) -> In n (live p) ->
  ((fst (labels p m d) <= fst (labels p m n) /\
    snd (labels p m n) <= snd (labels p m d))%positive <-> idom_ancestor m d n).
Proof.
  intros Hready Hmap [Hdomain Hwf] Hd Hn.
  pose proof (ends_complete m Hmap Hwf) as Hend.
  rewrite <- (root_prefix m Hend).
  pose proof (interval_prefix (radix p) ltac:(unfold radix; lia) (S (Map.size m))
    (root_path m d) (root_path m n)
    ltac:(unfold root_path; rewrite length_rev; apply chain_length)
    ltac:(unfold root_path; rewrite length_rev; apply chain_length)
    (root_digits p m d Hready Hdomain Hd) (root_digits p m n Hready Hdomain Hn)) as Hint.
  unfold labels.
  destruct (interval (radix p) (S (Map.size m)) (root_path m d)) as [dl dh].
  destruct (interval (radix p) (S (Map.size m)) (root_path m n)) as [nl nh].
  cbn [fst snd] in Hint |- *.
  rewrite !positive_le_N, !succ_pos_value. rewrite <- Hint. lia.
Qed.

(** Any well-formed finite reachable parent forest receives exact ancestry intervals. *)
Theorem of_parents_numbering {V E} (p : Prepared.t V E) m :
  Prepared.ready p -> Map.wf positive_encoding m -> forest p m ->
  forall n d v u, reachable (Prepared.graph p) n -> reachable (Prepared.graph p) d ->
  Prepared.id_of p n = Some v -> Prepared.id_of p d = Some u ->
  exists a b c e, Map.get positive_encoding u (tin (of_parents p m)) = Some a /\
    Map.get positive_encoding v (tin (of_parents p m)) = Some b /\
    Map.get positive_encoding v (tout (of_parents p m)) = Some c /\
    Map.get positive_encoding u (tout (of_parents p m)) = Some e /\
    ((a <= b /\ c <= e)%positive <-> idom_ancestor m u v).
Proof.
  intros Hready Hmap Hforest n d v u Hn Hd Hv Hu.
  assert (Hvl : In v (live p)) by (apply (live_spec p n v Hready Hv); exact Hn).
  assert (Hul : In u (live p)) by (apply (live_spec p d u Hready Hu); exact Hd).
  exists (fst (labels p m u)), (fst (labels p m v)),
    (snd (labels p m v)), (snd (labels p m u)).
  cbn [of_parents tin tout].
  split; [now apply number_map_get|].
  split; [now apply number_map_get|].
  split; [now apply number_map_get|].
  split; [now apply number_map_get|].
  now apply labels_spec.
Qed.

Local Lemma path_reachable_targets {V E} (g : Graph.t V E) a es b :
  path g a es b -> reachable g a ->
  forall e, In e es -> reachable g (Graph.target g e).
Proof.
  intro Hpath. induction Hpath as [v|e rest z Hedge Htail IH]; intros Ha f Hin.
  - contradiction.
  - assert (Ht : reachable g (Graph.target g e)) by (eapply reachable_step; eauto).
    destruct Hin as [<-|Hin]; [exact Ht|now apply IH].
Qed.

(** Every dominator of a reachable node is reachable in the same arbitrary graph. *)
Theorem dominator_reachable {V E} (g : Graph.t V E) d n :
  reachable g n -> dominates g d n -> reachable g d.
Proof.
  intros Hn Hdom. apply reachable_iff_path in Hn.
  destruct Hn as [a [es [Ha Hpath]]].
  destruct (Hdom a es Ha Hpath) as [->|[e [He Htarget]]].
  - now apply reachable_entry.
  - rewrite <- Htarget. eapply path_reachable_targets; [exact Hpath| |exact He].
    now apply reachable_entry.
Qed.

Local Lemma id_injective {V E} (p : Prepared.t V E) a b i :
  Prepared.laws p ->
  Prepared.id_of p a = Some i -> Prepared.id_of p b = Some i -> a = b.
Proof.
  intros Hp Ha Hb.
  pose proof (Prepared.name_of_id_of p a i Hp Ha).
  pose proof (Prepared.name_of_id_of p b i Hp Hb). congruence.
Qed.

Local Lemma reachable_id {V E} (p : Prepared.t V E) n :
  Prepared.ready p -> reachable (Prepared.graph p) n ->
  exists i, Prepared.id_of p n = Some i.
Proof.
  intros [Hwf [_ Hp]] Hn. apply (Prepared.ids_domain p Hp).
  now apply (reachable_in_nodes _ _ Hwf).
Qed.

Local Lemma exact_domain {V E} (p : Prepared.t V E) t :
  Prepared.ready p -> exact p t ->
  forall v u, parent (idom t) v = Some u -> In v (live p) /\ In u (live p).
Proof.
  intros Hready Ht v u Hget.
  destruct (idom_domain p t Ht v u Hget) as [n [d [Hv [Hu [Hn Hd]]]]].
  pose proof (Prepared.id_of_name_of p v n (proj2 (proj2 Hready)) Hv) as Hiv.
  pose proof (Prepared.id_of_name_of p u d (proj2 (proj2 Hready)) Hu) as Hiu.
  split; [now apply (live_spec p n v Hready Hiv)|now apply (live_spec p d u Hready Hiu)].
Qed.

Local Lemma exact_ancestor_sound {V E} (p : Prepared.t V E) t :
  Prepared.ready p -> exact p t ->
  forall u v, idom_ancestor (idom t) u v ->
  forall n d, reachable (Prepared.graph p) n ->
    Prepared.id_of p n = Some v -> Prepared.id_of p d = Some u ->
    dominates (Prepared.graph p) d n.
Proof.
  intros Hready Ht u v Hanc.
  induction Hanc as [u v Hget|v|u w v Huw IHuw Hwv IHwv]; intros n d Hn Hv Hu.
  - apply (proj1 (proj1 (idom_sound p t Ht v u n d Hget
      (Prepared.name_of_id_of p n v (proj2 (proj2 Hready)) Hv)
      (Prepared.name_of_id_of p d u (proj2 (proj2 Hready)) Hu)))).
  - assert (d = n).
    { eapply id_injective; [exact (proj2 (proj2 Hready))|exact Hu|exact Hv]. }
    subst d. apply dominates_refl.
  - assert (Hvl : In v (live p)) by (now apply (live_spec p n v Hready Hv)).
    destruct (live_named p w Hready
      (ancestor_live p (idom t) (exact_domain p t Hready Ht) w v Hwv Hvl))
      as [b [Hb Hbr]].
    eapply dominates_trans; [apply IHuw; eassumption|apply IHwv; eassumption].
Qed.

Local Lemma exact_ancestor_complete {V E} (p : Prepared.t V E) t :
  Prepared.ready p -> exact p t ->
  forall v n d u, reachable (Prepared.graph p) n ->
    Prepared.id_of p n = Some v -> Prepared.id_of p d = Some u ->
    dominates (Prepared.graph p) d n -> idom_ancestor (idom t) u v.
Proof.
  intros Hready Ht.
  refine (well_founded_induction (parent_finite p t Ht)
    (fun v => forall n d u, reachable (Prepared.graph p) n ->
      Prepared.id_of p n = Some v -> Prepared.id_of p d = Some u ->
      dominates (Prepared.graph p) d n -> idom_ancestor (idom t) u v) _).
  intros v IH n d u Hn Hv Hu Hdom.
  destruct (Pos.eq_dec u v) as [->|Hne]; [apply rt_refl|].
  assert (Hstrict : strictly_dominates (Prepared.graph p) d n).
  { split; [exact Hdom|intro Heq; subst d; congruence]. }
  destruct (parent (idom t) v) as [w|] eqn:Hw.
  - destruct (idom_domain p t Ht v w Hw) as [n' [b [Hnv [Hwb [Hnr Hbr]]]]].
    pose proof (Prepared.id_of_name_of p w b (proj2 (proj2 Hready)) Hwb) as Hb.
    pose proof (idom_sound p t Ht v w n b Hw
      (Prepared.name_of_id_of p n v (proj2 (proj2 Hready)) Hv) Hwb) as Himmediate.
    eapply rt_trans.
    + eapply IH; [exact Hw|exact Hbr|exact Hb|exact Hu|].
      exact (proj2 Himmediate d Hstrict).
    + apply rt_step. exact Hw.
  - exfalso. apply (proj1 (idom_complete p t Ht n v Hn Hv) Hw d Hstrict).
Qed.

(** Exact candidate trees identify semantic dominance with their parent ancestry. *)
Theorem ancestry_spec {V E} (p : Prepared.t V E) t n d v u :
  Prepared.ready p -> exact p t -> reachable (Prepared.graph p) n ->
  Prepared.id_of p n = Some v -> Prepared.id_of p d = Some u ->
  (idom_ancestor (idom t) u v <-> dominates (Prepared.graph p) d n).
Proof.
  intros Hready Ht Hn Hv Hu. split.
  - intro Hanc. eapply exact_ancestor_sound; eauto.
  - intro Hdom. eapply exact_ancestor_complete; eauto.
Qed.

Local Lemma ancestor_antisym m :
  well_founded (fun u v => parent m v = Some u) ->
  forall u v, idom_ancestor m u v -> idom_ancestor m v u -> u = v.
Proof.
  intros Hforest u v Huv Hvu.
  destruct (ancestor_cases m u v Huv) as [Heq|[q [Hparent Huq]]]; [exact Heq|].
  exfalso. apply (acc_no_return m q (Hforest q) v Hparent).
  eapply rt_trans; [exact Hvu|exact Huq].
Qed.

(** Mutual dominance identifies reachable named nodes through the exact finite parent forest. *)
Theorem dominates_antisym {V E} (p : Prepared.t V E) t d n u v :
  Prepared.ready p -> exact p t ->
  reachable (Prepared.graph p) d -> reachable (Prepared.graph p) n ->
  Prepared.id_of p d = Some u -> Prepared.id_of p n = Some v ->
  dominates (Prepared.graph p) d n -> dominates (Prepared.graph p) n d ->
  d = n.
Proof.
  intros Hready Htree Hd Hn Hu Hv Hdn Hnd.
  pose proof (proj2 (ancestry_spec p t n d v u Hready Htree Hn Hv Hu) Hdn) as Huv.
  pose proof (proj2 (ancestry_spec p t d n u v Hready Htree Hd Hu Hv) Hnd) as Hvu.
  assert (Heq : u = v).
  { eapply ancestor_antisym; [exact (parent_finite p t Htree)|exact Huv|exact Hvu]. }
  subst v. eapply id_injective; [exact (proj2 (proj2 Hready))|exact Hu|exact Hv].
Qed.

(** Interval dominance is exact on the reachable named domain of an exact candidate tree. *)
Theorem dominates_b_spec {V E} (p : Prepared.t V E) t n d v u :
  Prepared.ready p -> exact p t ->
  reachable (Prepared.graph p) n -> reachable (Prepared.graph p) d ->
  Prepared.id_of p n = Some v -> Prepared.id_of p d = Some u ->
  (dominates_b t u v = true <-> dominates (Prepared.graph p) d n).
Proof.
  intros Hready Ht Hn Hd Hv Hu.
  destruct (numbering p t Ht n d v u Hn Hd Hv Hu)
    as [a [b [c [e [Ha [Hb [Hc [He Hnumber]]]]]]]].
  unfold dominates_b. rewrite Ha, Hb, Hc, He, andb_true_iff, !Pos.leb_le, Hnumber.
  now apply (ancestry_spec p t n d v u).
Qed.

Definition live_b {V E} (p : Prepared.t V E) v :=
  FinSet.mem positive_encoding v (Reach.set p Reach.unrestricted (Prepared.entry_ids p)).

Local Lemma live_b_spec {V E} (p : Prepared.t V E) v :
  live_b p v = true <-> In v (live p).
Proof.
  unfold live_b, live.
  symmetry. apply (FinSet.elements_spec positive_encoding positive_encoding_laws).
  apply Reach.set_wf.
Qed.

(** Validate reachable bindings, terminating chains and all-pairs dominance by deletion.
    This checks semantic parent data. Representation well-formedness is a separate premise. *)
Definition check {V E} (p : Prepared.t V E) m :=
  let seen := Reach.set p Reach.unrestricted (Prepared.entry_ids p) in
  let vs := FinSet.elements seen in
  forallb (fun vu => FinSet.mem positive_encoding (fst vu) seen &&
    FinSet.mem positive_encoding (snd vu) seen) (Map.elements m) &&
  forallb (ends (S (Map.size m)) m) vs &&
  forallb (fun d =>
    let avoiding := Reach.set p (Reach.blocked d) (Prepared.entry_ids p) in
    forallb (fun n => Bool.eqb (ancestor_b m d n)
      (negb (FinSet.mem positive_encoding n avoiding))) vs) vs.

Local Lemma checked_domain {V E} (p : Prepared.t V E) m :
  Map.wf positive_encoding m -> check p m = true ->
  forall v u, parent m v = Some u -> In v (live p) /\ In u (live p).
Proof.
  intros Hmap Hcheck v u Hget. unfold check in Hcheck.
  apply andb_true_iff in Hcheck. destruct Hcheck as [Hcheck _].
  apply andb_true_iff in Hcheck. destruct Hcheck as [Hbindings _].
  rewrite forallb_forall in Hbindings.
  specialize (Hbindings (v, u)
    (proj2 (Map.elements_spec positive_encoding positive_encoding_laws v u m Hmap) Hget)).
  change (live_b p v && live_b p u = true) in Hbindings.
  now rewrite andb_true_iff, !live_b_spec in Hbindings.
Qed.

Local Lemma checked_ends {V E} (p : Prepared.t V E) m :
  check p m = true -> forall v, In v (live p) -> ends (S (Map.size m)) m v = true.
Proof.
  intro Hcheck. unfold check in Hcheck.
  apply andb_true_iff in Hcheck. destruct Hcheck as [Hcheck _].
  apply andb_true_iff in Hcheck. destruct Hcheck as [_ Hends].
  now rewrite forallb_forall in Hends.
Qed.

Local Lemma checked_forest {V E} (p : Prepared.t V E) m :
  Map.wf positive_encoding m -> check p m = true -> forest p m.
Proof.
  intros Hmap Hcheck. split; [now apply checked_domain|].
  intro v. destruct (parent m v) as [u|] eqn:Hget.
  - apply (ends_acc (S (Map.size m)) m v).
    apply (checked_ends p m Hcheck v).
    exact (proj1 (checked_domain p m Hmap Hcheck v u Hget)).
  - constructor. intros u Hu. congruence.
Qed.

Local Lemma checked_dominance {V E} (p : Prepared.t V E) m n d v u :
  Prepared.ready p -> check p m = true ->
  reachable (Prepared.graph p) n -> reachable (Prepared.graph p) d ->
  Prepared.id_of p n = Some v -> Prepared.id_of p d = Some u ->
  (idom_ancestor m u v <-> dominates (Prepared.graph p) d n).
Proof.
  intros Hready Hcheck Hn Hd Hv Hu.
  assert (Hvl : In v (live p)) by (now apply (live_spec p n v Hready Hv)).
  assert (Hul : In u (live p)) by (now apply (live_spec p d u Hready Hu)).
  rewrite <- (ancestor_b_spec m u v (checked_ends p m Hcheck v Hvl)).
  unfold check in Hcheck. apply andb_true_iff in Hcheck.
  destruct Hcheck as [_ Hpairs]. rewrite forallb_forall in Hpairs.
  specialize (Hpairs u Hul). rewrite forallb_forall in Hpairs.
  specialize (Hpairs v Hvl). apply Bool.eqb_prop in Hpairs.
  rewrite Hpairs, negb_true_iff. symmetry. now apply Reach.avoiding.
Qed.

Local Lemma checked_strict {V E} (p : Prepared.t V E) m v u n d :
  Prepared.ready p -> Map.wf positive_encoding m -> check p m = true ->
  parent m v = Some u -> Prepared.name_of p v = Some n -> Prepared.name_of p u = Some d ->
  strictly_dominates (Prepared.graph p) d n.
Proof.
  intros Hready Hmap Hcheck Hget Hv Hu.
  pose proof (Prepared.id_of_name_of p v n (proj2 (proj2 Hready)) Hv) as Hiv.
  pose proof (Prepared.id_of_name_of p u d (proj2 (proj2 Hready)) Hu) as Hiu.
  destruct (checked_domain p m Hmap Hcheck v u Hget) as [Hvl Hul].
  assert (Hn : reachable (Prepared.graph p) n) by
    (now apply (live_spec p n v Hready Hiv)).
  assert (Hd : reachable (Prepared.graph p) d) by
    (now apply (live_spec p d u Hready Hiu)).
  split.
  - apply (proj1 (checked_dominance p m n d v u Hready Hcheck Hn Hd Hiv Hiu)).
    apply rt_step. exact Hget.
  - intro Heq. subst d. assert (u = v) by congruence. subst u.
    pose proof (proj2 (checked_forest p m Hmap Hcheck) v) as Hacc.
    apply (acc_no_return m v Hacc v Hget). apply rt_refl.
Qed.

Local Lemma checked_immediate {V E} (p : Prepared.t V E) m v u n d :
  Prepared.ready p -> Map.wf positive_encoding m -> check p m = true ->
  parent m v = Some u -> Prepared.name_of p v = Some n -> Prepared.name_of p u = Some d ->
  immediately_dominates (Prepared.graph p) d n.
Proof.
  intros Hready Hmap Hcheck Hget Hv Hu.
  split; [eapply checked_strict; eauto|].
  intros x [Hxn Hne].
  pose proof (Prepared.id_of_name_of p v n (proj2 (proj2 Hready)) Hv) as Hiv.
  pose proof (Prepared.id_of_name_of p u d (proj2 (proj2 Hready)) Hu) as Hiu.
  destruct (checked_domain p m Hmap Hcheck v u Hget) as [Hvl Hul].
  assert (Hn : reachable (Prepared.graph p) n) by
    (now apply (live_spec p n v Hready Hiv)).
  assert (Hd : reachable (Prepared.graph p) d) by
    (now apply (live_spec p d u Hready Hiu)).
  pose proof (dominator_reachable _ x n Hn Hxn) as Hx.
  destruct (reachable_id p x Hready Hx) as [i Hi].
  pose proof (proj2 (checked_dominance p m n x v i Hready Hcheck Hn Hx Hiv Hi) Hxn)
    as Hanc.
  apply ancestor_cases in Hanc. destruct Hanc as [Heq|[w [Hw Hiw]]].
  - subst i. exfalso. apply Hne.
    eapply id_injective; [exact (proj2 (proj2 Hready))|exact Hi|exact Hiv].
  - assert (w = u) by congruence. subst w.
    apply (proj1 (checked_dominance p m d x u i Hready Hcheck Hd Hx Hiu Hi)). exact Hiw.
Qed.

Local Lemma checked_absent {V E} (p : Prepared.t V E) m n v :
  Prepared.ready p -> Map.wf positive_encoding m -> check p m = true ->
  reachable (Prepared.graph p) n -> Prepared.id_of p n = Some v ->
  (parent m v = None <-> forall d, ~ strictly_dominates (Prepared.graph p) d n).
Proof.
  intros Hready Hmap Hcheck Hn Hv. split.
  - intros Hnone d [Hdom Hne].
    pose proof (dominator_reachable _ d n Hn Hdom) as Hd.
    destruct (reachable_id p d Hready Hd) as [u Hu].
    pose proof (proj2 (checked_dominance p m n d v u Hready Hcheck Hn Hd Hv Hu) Hdom)
      as Hanc.
    apply ancestor_cases in Hanc. destruct Hanc as [Heq|[w [Hw _]]].
    + subst u. apply Hne.
      eapply id_injective; [exact (proj2 (proj2 Hready))|exact Hu|exact Hv].
    + congruence.
  - intro Hno. destruct (parent m v) as [u|] eqn:Hget; [|reflexivity].
    exfalso. destruct (live_named p u Hready
      (proj2 (checked_domain p m Hmap Hcheck v u Hget))) as [d [Hu Hd]].
    apply (Hno d). eapply checked_strict; try eassumption.
    + exact (Prepared.name_of_id_of p n v (proj2 (proj2 Hready)) Hv).
    + exact (Prepared.name_of_id_of p d u (proj2 (proj2 Hready)) Hu).
Qed.

(** Accepted semantic parents yield an exact tree when the supplied representation is certified.
    Map.wf is mandatory at this boundary and is not inferred from the boolean graph checks. *)
Theorem check_sound {V E} (p : Prepared.t V E) m :
  Prepared.ready p -> Map.wf positive_encoding m -> check p m = true ->
  exact p (of_parents p m).
Proof.
  intros Hready Hmap Hcheck. pose proof (checked_forest p m Hmap Hcheck) as Hforest.
  constructor.
  - cbn [of_parents idom tin tout]. split; [exact Hmap|].
    split; apply number_map_wf.
  - cbn [of_parents idom]. intros v u n d Hget Hv Hu.
    eapply checked_immediate; eauto.
  - cbn [of_parents idom]. intros n v Hn Hv. now apply checked_absent.
  - cbn [of_parents idom]. intros v u Hget.
    destruct (proj1 Hforest v u Hget) as [Hvl Hul].
    destruct (live_named p v Hready Hvl) as [n [Hv Hn]].
    destruct (live_named p u Hready Hul) as [d [Hu Hd]].
    exists n, d. split.
    + exact (Prepared.name_of_id_of p n v (proj2 (proj2 Hready)) Hv).
    + split.
      * exact (Prepared.name_of_id_of p d u (proj2 (proj2 Hready)) Hu).
      * auto.
  - exact (proj2 Hforest).
  - cbn [of_parents idom]. now apply of_parents_numbering.
Qed.

(** Every exact candidate map passes and its witness supplies the representation certificate. *)
Theorem check_complete {V E} (p : Prepared.t V E) m :
  Prepared.ready p -> (exists t, exact p t /\ idom t = m) -> check p m = true.
Proof.
  intros Hready [t [Ht <-]].
  pose proof (proj1 (maps_wf p t Ht)) as Hmap.
  pose proof (ends_complete (idom t) Hmap (parent_finite p t Ht)) as Hend.
  unfold check. apply andb_true_iff. split.
  - apply andb_true_iff. split.
    + apply forallb_forall. intros [v u] Hin.
      apply (Map.elements_spec positive_encoding positive_encoding_laws v u (idom t) Hmap)
        in Hin.
      change (live_b p v && live_b p u = true). rewrite andb_true_iff, !live_b_spec.
      now apply (exact_domain p t Hready Ht).
    + apply forallb_forall. intros v Hv. apply Hend.
  - apply forallb_forall. intros u Hul. apply forallb_forall. intros v Hvl.
    destruct (live_named p u Hready Hul) as [d [Hu Hd]].
    destruct (live_named p v Hready Hvl) as [n [Hv Hn]].
    apply Bool.eqb_true_iff, eq_true_iff_eq.
    rewrite (ancestor_b_spec (idom t) u v (Hend v)), negb_true_iff.
    rewrite <- (Reach.avoiding p d n u v Hready Hu Hv).
    now apply (ancestry_spec p t n d v u).
Qed.

Arguments of_parents {V E} p m : simpl never.
Arguments check {V E} p m : simpl never.
Arguments ancestor_b m d n : simpl never.
Arguments dominates_b t d n : simpl never.

End DomCheck.
