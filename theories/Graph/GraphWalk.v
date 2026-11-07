(** * Bounded parent-chain walks

    A walk records nodes before the first stop and reports exhaustion separately.
    For example, stopping at 2 on the chain 3 -> 2 -> 1 returns [3].
    Builds on: CostLoop, CostList, GraphDomSpec and GraphCheckDom. *)

From Stdlib Require Import List Bool PArith NArith Nnat Lia.
From Stdlib.Relations Require Import Relation_Operators.
From Galois.Cost Require Import CostMonad CostLoop CostList.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Graph Require Import GraphDomSpec GraphCheckDom GraphReach.
Import List.ListNotations Cost.Notations.

Module Walk.

Definition state := (positive * list positive)%type.

(** A stopped result contains the reverse trace; a continuation retains the next node. *)
Definition step_c (next : positive -> Cost.t (option positive))
    (stop : positive -> Cost.t bool) (s : state) : Cost.t (state + list positive) :=
  let '(v, seen) := s in
  Cost.step ;;
  let* blocked := stop v in
  if blocked then Cost.ret (inr seen) else
  Cost.step ;;
  let* parent := next v in
  Cost.step ;;
  match parent with
  | None => Cost.ret (inr (v :: seen))
  | Some u => Cost.ret (inl (u, v :: seen))
  end.

Definition run_c next stop fuel start :=
  iterate (step_c next stop) fuel (start, []).

Definition trace_of (r : state + list positive) :=
  match r with
  | inl (_, seen) => seen
  | inr seen => seen
  end.

(** The value-only interface returns the visited prefix even when fuel is exhausted. *)
Definition until_c next stop fuel start : Cost.t (list positive) :=
  let* r := run_c next stop fuel start in
  rev_c (trace_of r).

Definition until next stop fuel start := Cost.value (until_c next stop fuel start).

(** The reference trace uses at most the numeric budget and excludes the first stop node. *)
Fixpoint prefix (next : positive -> option positive) (stop : positive -> bool)
    fuel start : list positive :=
  match fuel with
  | O => []
  | S fuel =>
    if stop start then [] else
    start :: match next start with
    | None => []
    | Some u => prefix next stop fuel u
    end
  end.

Local Lemma run_prefix next stop n s r :
  runs (step_c next stop) n s r ->
  rev (trace_of r) =
    rev (snd s) ++ prefix (fun v => Cost.value (next v))
      (fun v => Cost.value (stop v)) n (fst s).
Proof.
  intro Hrun. induction Hrun as [s|n [v seen] result Hstop|
    n [v seen] [u seen'] r Hnext Hrun IH].
  - cbn [trace_of prefix]. now rewrite app_nil_r.
  - cbn [step_c] in Hstop. autorewrite with galois_cost in Hstop.
    cbn [fst snd prefix].
    destruct (Cost.value (stop v)) eqn:Hblocked.
    + inversion Hstop; subst result. cbn [trace_of]. now rewrite app_nil_r.
    + autorewrite with galois_cost in Hstop.
      destruct (Cost.value (next v)); inversion Hstop; subst result.
      cbn [trace_of rev]. reflexivity.
  - cbn [step_c] in Hnext. autorewrite with galois_cost in Hnext.
    destruct (Cost.value (stop v)) eqn:Hblocked; [discriminate|].
    autorewrite with galois_cost in Hnext.
    destruct (Cost.value (next v)) as [p|] eqn:Hparent; [|discriminate].
    inversion Hnext; subst u seen'. rewrite IH.
    cbn [snd fst prefix]. rewrite Hblocked, Hparent.
    cbn [rev]. now rewrite <- app_assoc.
Qed.

(** Every returned list is the actual bounded prefix, including on exhaustion and cycles. *)
Theorem until_spec next stop fuel start :
  until next stop fuel start =
    prefix (fun v => Cost.value (next v)) (fun v => Cost.value (stop v))
      (Pos.to_nat fuel) start.
Proof.
  unfold until, until_c. rewrite Cost.value_bind, value_rev_c.
  exact (run_prefix next stop _ _ _ (iterate_value _ fuel (start, []))).
Qed.

(** Exhaustion witnesses exactly the supplied number of continuation transitions. *)
Theorem until_exhausted next stop fuel start s :
  Cost.value (run_c next stop fuel start) = inl s ->
  exists states, length states = Pos.to_nat fuel /\
    (fix follows (xs : list state) (current : state) : Prop :=
      match xs with
      | [] => current = s
      | next_state :: rest =>
        Cost.value (step_c next stop current) = inl next_state /\
          follows rest next_state
      end) states (start, []).
Proof.
  apply iterate_inl_runs_out.
Qed.

Local Lemma prefix_length next stop n start :
  (length (prefix next stop n start) <= n)%nat.
Proof.
  revert start. induction n as [|n IH]; intro start; cbn [prefix length]; [lia|].
  destruct (stop start); [cbn; lia|].
  destruct (next start); cbn [length]; [pose proof (IH p); lia|lia].
Qed.

Local Lemma step_cost next stop k :
  (forall v, (Cost.ticks (stop v) + Cost.ticks (next v) <= k)%N) ->
  forall s, (Cost.ticks (step_c next stop s) <= k + 3)%N.
Proof.
  intros H [v seen]. cbn [step_c]. autorewrite with galois_cost.
  specialize (H v). destruct (Cost.value (stop v));
    autorewrite with galois_cost; [lia|].
  destruct (Cost.value (next v)); autorewrite with galois_cost; lia.
Qed.

(** The uniform bound retains both callbacks, construction, reversal and binary-driver work. *)
Theorem until_cost next stop k fuel start :
  (forall v, (Cost.ticks (stop v) + Cost.ticks (next v) <= k)%N) ->
  (Cost.ticks (until_c next stop fuel start) <= (k + 6) * N.pos fuel)%N.
Proof.
  intro Hcallbacks.
  pose proof (iterate_cost_amortised (step_c next stop) (fun _ => True)
    (fun _ => 0%N) (k + 3)%N) as Hcost.
  specialize (Hcost ltac:(intros s _;
    split; [destruct (Cost.value (step_c next stop s)); exact I|];
    unfold result_potential; destruct (Cost.value (step_c next stop s));
    pose proof (step_cost next stop k Hcallbacks s); cbn; lia) fuel (start, []) I).
  destruct Hcost as [_ Hcost].
  unfold until_c. rewrite Cost.ticks_bind, ticks_rev_c.
  assert (Hlength : (length (trace_of (Cost.value (run_c next stop fuel start))) <=
      Pos.to_nat fuel)%nat).
  { pose proof (run_prefix next stop _ _ _
      (iterate_value (step_c next stop) fuel (start, []))) as Htrace.
    cbn [snd rev app] in Htrace.
    apply (f_equal (@length positive)) in Htrace.
    rewrite length_rev in Htrace.
    unfold run_c. rewrite Htrace. apply prefix_length. }
  assert (HlengthN : (N.of_nat (length (trace_of
    (Cost.value (run_c next stop fuel start)))) <= N.pos fuel)%N).
  { rewrite <- (N2Nat.id (N.pos fuel)). cbn [N.to_nat]. lia. }
  unfold run_c in *. unfold result_potential in Hcost.
  destruct (Cost.value (iterate (step_c next stop) fuel (start, [])));
    cbn in Hcost; nia.
Qed.

Definition up_c (t : Dom.tree) v := Map.get_c positive_encoding v (Dom.idom t).

Local Lemma up_value t v :
  Cost.value (up_c t v) = Map.get positive_encoding v (Dom.idom t).
Proof.
  reflexivity.
Qed.

Local Lemma ancestor_cases m d n :
  idom_ancestor m d n ->
  d = n \/ exists u, Map.get positive_encoding n m = Some u /\ idom_ancestor m d u.
Proof.
  intro H. induction H as [u v Huv|v|u w v Huw IHuw Hwv IHwv].
  - right. exists u. split; [exact Huv|apply rt_refl].
  - now left.
  - destruct IHwv as [->|[p [Hp Hup]]].
    + exact IHuw.
    + right. exists p. split; [exact Hp|]. eapply rt_trans; eassumption.
Qed.

Local Lemma prefix_ancestors m stop :
  (forall d v, idom_ancestor m d v -> stop v = true -> stop d = true) ->
  forall n v, DomCheck.ends n m v = true ->
  forall d, (In d (prefix (fun v => Map.get positive_encoding v m) stop n v) <->
    idom_ancestor m d v /\ stop d = false).
Proof.
  intro Hup. induction n as [|n IH]; intros v Hends d; [discriminate|].
  cbn [prefix]. destruct (stop v) eqn:Hstop.
  - split; [contradiction|].
    intros [Hanc Hfree]. pose proof (Hup d v Hanc Hstop). congruence.
  - cbn [DomCheck.ends] in Hends. unfold DomCheck.parent in Hends.
    destruct (Map.get positive_encoding v m) as [u|] eqn:Hparent.
    + cbn [In]. rewrite (IH u Hends d). split.
      * intros [<-|[Hanc Hfree]].
        -- split; [apply rt_refl|exact Hstop].
        -- split; [eapply rt_trans; [exact Hanc|apply rt_step; exact Hparent]|exact Hfree].
      * intros [Hanc Hfree]. destruct (ancestor_cases m d v Hanc)
          as [->|[p [Hp Hdp]]]; [now left|].
        right. assert (p = u) by congruence. now subst p.
    + cbn [In]. split.
      * intros [<-|Hfalse]; [split; [apply rt_refl|exact Hstop]|contradiction].
      * intros [Hanc Hfree]. destruct (ancestor_cases m d v Hanc)
          as [->|[p [Hp _]]]; [now left|congruence].
Qed.

(** Finite forests give full-chain coverage from a proved binding-count fuel bound. *)
Theorem up_spec t stop start d :
  Map.wf positive_encoding (Dom.idom t) ->
  well_founded (fun u v => Map.get positive_encoding v (Dom.idom t) = Some u) ->
  (forall d v, idom_ancestor (Dom.idom t) d v ->
    Cost.value (stop v) = true -> Cost.value (stop d) = true) ->
  (In d (until (up_c t) stop (Pos.of_succ_nat (Map.size (Dom.idom t))) start) <->
    idom_ancestor (Dom.idom t) d start /\ Cost.value (stop d) = false).
Proof.
  intros Hmap Hforest Hup. rewrite until_spec, SuccNat2Pos.id_succ.
  apply prefix_ancestors; [exact Hup|].
  exact (DomCheck.ends_complete _ Hmap Hforest start).
Qed.

Local Lemma chain_agrees f g m v :
  DomCheck.ends (S f) m v = true -> DomCheck.ends (S g) m v = true ->
  DomCheck.chain f m v = DomCheck.chain g m v.
Proof.
  revert g v. induction f as [|f IH]; intros [|g] v Hf Hg;
    cbn [DomCheck.ends] in Hf, Hg; cbn [DomCheck.chain];
    unfold DomCheck.parent in *;
    destruct (Map.get positive_encoding v m) as [u|] eqn:Hu;
    try reflexivity; try discriminate.
  f_equal. apply IH; assumption.
Qed.

(** The chain-length rank counts actual parent nodes and does not inspect numeric intervals. *)
Definition chain_rank t v := length (DomCheck.chain (Map.size (Dom.idom t)) (Dom.idom t) v).

Local Lemma chain_rank_positive t v : (0 < chain_rank t v)%nat.
Proof.
  unfold chain_rank. destruct (Map.size (Dom.idom t)); cbn [DomCheck.chain length]; lia.
Qed.

Local Lemma chain_rank_parent t :
  Map.wf positive_encoding (Dom.idom t) ->
  well_founded (fun u v => Map.get positive_encoding v (Dom.idom t) = Some u) ->
  forall v u, Map.get positive_encoding v (Dom.idom t) = Some u ->
    chain_rank t v = S (chain_rank t u).
Proof.
  intros Hmap Hforest v u Hu.
  pose proof (DomCheck.ends_complete _ Hmap Hforest) as Hend.
  assert (Hlong : DomCheck.ends (S (S (Map.size (Dom.idom t)))) (Dom.idom t) v = true).
  { cbn [DomCheck.ends]. unfold DomCheck.parent. rewrite Hu. apply Hend. }
  unfold chain_rank.
  rewrite (chain_agrees (Map.size (Dom.idom t)) (S (Map.size (Dom.idom t)))
    (Dom.idom t) v (Hend v) Hlong).
  cbn [DomCheck.chain]. unfold DomCheck.parent. rewrite Hu. reflexivity.
Qed.

Local Lemma prefix_rank t stop :
  Map.wf positive_encoding (Dom.idom t) ->
  well_founded (fun u v => Map.get positive_encoding v (Dom.idom t) = Some u) ->
  forall n v, (length (prefix (fun v => Map.get positive_encoding v (Dom.idom t))
    stop n v) <= chain_rank t v)%nat.
Proof.
  intros Hmap Hforest. induction n as [|n IH]; intro v; cbn [prefix length]; [lia|].
  destruct (stop v); [cbn; lia|].
  destruct (Map.get positive_encoding v (Dom.idom t)) as [u|] eqn:Hu; cbn [length].
  - rewrite (chain_rank_parent t Hmap Hforest v u Hu). specialize (IH u). lia.
  - pose proof (chain_rank_positive t v). lia.
Qed.

(** A forest walk pays its full parent-chain length times callback work plus binary fuel descent. *)
Theorem until_chain_cost t stop k fuel start :
  Map.wf positive_encoding (Dom.idom t) ->
  well_founded (fun u v => Map.get positive_encoding v (Dom.idom t) = Some u) ->
  (forall v, idom_ancestor (Dom.idom t) v start ->
    (Cost.ticks (stop v) + Cost.ticks (up_c t v) <= k)%N) ->
  (Cost.ticks (until_c (up_c t) stop fuel start) <=
    (k + 6) * (N.of_nat (chain_rank t start) + 1) +
      2 * N.pos (Pos.size fuel))%N.
Proof.
  intros Hmap Hforest Hcallbacks.
  assert (Hstep : forall s : state, idom_ancestor (Dom.idom t) (fst s) start ->
    (Cost.ticks (step_c (up_c t) stop s) <= k + 3)%N /\
      match Cost.value (step_c (up_c t) stop s) with
      | inl s' => idom_ancestor (Dom.idom t) (fst s') start /\
        (N.of_nat (chain_rank t (fst s')) < N.of_nat (chain_rank t (fst s)))%N
      | inr _ => True
      end).
  { intros [v seen] Hanc. cbn [fst] in Hanc |- *.
    pose proof (Hcallbacks v Hanc) as Hcb.
    cbn [step_c]. autorewrite with galois_cost.
    destruct (Cost.value (stop v)); autorewrite with galois_cost;
      [split; [lia|exact I]|].
    rewrite up_value.
    destruct (Map.get positive_encoding v (Dom.idom t)) as [u|] eqn:Hu;
      autorewrite with galois_cost.
    - split; [lia|]. cbn [fst]. split.
      + eapply rt_trans; [apply rt_step; exact Hu|exact Hanc].
      + rewrite (chain_rank_parent t Hmap Hforest v u Hu). lia.
    - split; [lia|exact I]. }
  pose proof (iterate_cost (step_c (up_c t) stop)
    (fun s => idom_ancestor (Dom.idom t) (fst s) start)
    (fun s => N.of_nat (chain_rank t (fst s))) (k + 3)%N fuel (start, [])
    Hstep (rt_refl _ _ start)) as Hcost.
  assert (Hlength : (length (until (up_c t) stop fuel start) <= chain_rank t start)%nat).
  { rewrite until_spec. apply prefix_rank; assumption. }
  unfold until, until_c in Hlength. rewrite Cost.value_bind, value_rev_c, length_rev in Hlength.
  unfold until_c. rewrite Cost.ticks_bind, ticks_rev_c.
  unfold run_c in *. cbn [fst] in Hcost. nia.
Qed.

(** A finite closure driver shares the binary iteration machinery with parent walks. *)
Definition closure_state := (list positive * list positive * list positive)%type.

Definition closure_step_c (next : positive -> Cost.t (list positive))
    (member : positive -> list positive -> Cost.t bool)
    (remove : positive -> list positive -> Cost.t (list positive))
    (s : closure_state) : Cost.t (closure_state + closure_state) :=
  let '(pending, unseen, seen) := s in
  match pending with
  | [] => Cost.ret (inr s)
  | v :: rest =>
    Cost.step ;;
    let* fresh := member v unseen in
    if fresh then
      Cost.step ;;
      let* children := next v in
      let* pending' := app_c children rest in
      Cost.step ;;
      let* unseen' := remove v unseen in
      Cost.step ;;
      Cost.ret (inl (pending', unseen', v :: seen))
    else Cost.ret (inl (rest, unseen, seen))
  end.

Definition closure_result (r : closure_state + closure_state) :=
  match r with
  | inl s => s
  | inr s => s
  end.

Definition closure_c next member remove fuel pending unseen seen :=
  Cost.map (fun r => let '(pending', _, seen') := closure_result r in (pending', seen'))
    (iterate (closure_step_c next member remove) fuel (pending, unseen, seen)).

Local Lemma closure_runs next member remove :
  (forall v xs, Cost.value (member v xs) = Reach.member v xs) ->
  (forall v xs, Cost.value (remove v xs) = List.remove Pos.eq_dec v xs) ->
  forall n s r, runs (closure_step_c next member remove) n s r ->
  let '(pending, unseen, seen) := s in
  let '(pending', _, seen') := closure_result r in
  (pending', seen') =
    Reach.loop (fun v => Cost.value (next v)) n pending unseen seen.
Proof.
  intros Hmember Hremove n s r Hrun.
  induction Hrun as [s|n [[pending unseen] seen] result Hstop|
    n [[pending unseen] seen] s' r Hnext Hrun IH].
  - destruct s as [[pending unseen] seen]. destruct pending; reflexivity.
  - destruct pending as [|v rest].
    + cbn [closure_step_c] in Hstop. inversion Hstop; subst result. reflexivity.
    + cbn [closure_step_c] in Hstop. autorewrite with galois_cost in Hstop.
      rewrite Hmember in Hstop. destruct (Reach.member v unseen);
        autorewrite with galois_cost in Hstop; discriminate.
  - destruct pending as [|v rest]; [discriminate|].
    cbn [closure_step_c] in Hnext. autorewrite with galois_cost in Hnext.
    rewrite Hmember in Hnext. cbn [Reach.loop].
    destruct (Reach.member v unseen).
    + autorewrite with galois_cost in Hnext. rewrite Hremove in Hnext.
      inversion Hnext; subst s'. exact IH.
    + inversion Hnext; subst s'. exact IH.
Qed.

(** The shared closure driver agrees with the checker's bounded reference execution. *)
Theorem closure_spec next member remove fuel pending unseen seen :
  (forall v xs, Cost.value (member v xs) = Reach.member v xs) ->
  (forall v xs, Cost.value (remove v xs) = List.remove Pos.eq_dec v xs) ->
  Cost.value (closure_c next member remove fuel pending unseen seen) =
    Reach.loop (fun v => Cost.value (next v)) (Pos.to_nat fuel) pending unseen seen.
Proof.
  intros Hmember Hremove.
  unfold closure_c. rewrite Cost.value_map.
  pose proof (closure_runs next member remove Hmember Hremove _ _ _
    (iterate_value (closure_step_c next member remove) fuel (pending, unseen, seen))) as Hrun.
  cbn beta iota zeta in Hrun.
  destruct (closure_result (Cost.value
    (iterate (closure_step_c next member remove) fuel (pending, unseen, seen))))
    as [[pending' unseen'] seen'] in Hrun |- *.
  exact Hrun.
Qed.

Local Lemma member_spec v xs : Reach.member v xs = true <-> In v xs.
Proof.
  unfold Reach.member. rewrite existsb_exists. split.
  - intros [x [Hx Heq]]. apply Pos.eqb_eq in Heq. now subst x.
  - intro Hx. exists v. split; [exact Hx|apply Pos.eqb_refl].
Qed.

Local Lemma remove_spec x y xs :
  In y (remove Pos.eq_dec x xs) <-> In y xs /\ y <> x.
Proof.
  induction xs as [|a rest IH]; cbn; [tauto|].
  destruct (Pos.eq_dec x a) as [->|Hne]; cbn; rewrite IH; intuition congruence.
Qed.

Local Lemma remove_credit next x xs :
  NoDup xs -> In x xs ->
  Reach.credit next xs =
    (S (length (next x)) + Reach.credit next (remove Pos.eq_dec x xs))%nat.
Proof.
  intro H. induction H as [|a rest Hnot Hrest IH]; intro Hin; [contradiction|].
  cbn [Reach.credit remove]. destruct (Pos.eq_dec x a) as [->|Hne].
  - assert (Hremove : remove Pos.eq_dec a rest = rest).
    { clear Hrest IH Hin. induction rest as [|b tail IHtail]; cbn; [reflexivity|].
      destruct (Pos.eq_dec a b) as [->|Hab].
      - exfalso. apply Hnot. now left.
      - f_equal. apply IHtail. intro Hb. apply Hnot. now right. }
    now rewrite Hremove.
  - destruct Hin as [Heq|Hin]; [congruence|].
    cbn [Reach.credit]. rewrite (IH Hin). lia.
Qed.

Local Lemma fresh_invariant next roots all unseen seen x todo :
  (forall u, incl (next u) all) ->
  Reach.invariant next roots all unseen seen (x :: todo) -> In x unseen ->
  Reach.invariant next roots all (remove Pos.eq_dec x unseen) (x :: seen) (next x ++ todo).
Proof.
  intros Hnext Hinv Hx. destruct Hinv as [Hnd Hsupport Hseen Hpending Hdomain Hr He].
  constructor.
  - clear Hsupport Hseen Hpending Hdomain Hr He Hx.
    induction Hnd as [|a rest Hnot Hrest IH]; cbn; [constructor|].
    destruct (Pos.eq_dec x a); [exact IH|]. constructor; [|exact IH].
    intro Hin. apply remove_spec in Hin. tauto.
  - intros v Hv. destruct (Pos.eq_dec v x) as [->|Hne]; [right; now left|].
    destruct (Hsupport v Hv) as [Hu|Hs].
    + left. apply remove_spec. auto.
    + right. now right.
  - intros v [<-|Hv]; [apply Hpending; now left|apply Hseen; exact Hv].
  - intros v Hv. apply in_app_iff in Hv. destruct Hv as [Hv|Hv].
    + eapply Reach.edge; [apply Hpending; now left|exact Hv].
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
  Reach.invariant next roots all unseen seen (x :: todo) -> ~ In x unseen ->
  Reach.invariant next roots all unseen seen todo.
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
  Reach.invariant next roots all unseen seen pending ->
  (Reach.credit next unseen + length pending <= fuel)%nat ->
  fst (Reach.loop next fuel pending unseen seen) = [] /\
  Reach.invariant next roots all unseen
    (snd (Reach.loop next fuel pending unseen seen)) [].
Proof.
  intros Hnext. induction fuel as [|fuel IH]; intros unseen seen pending Hinv Hfuel.
  - destruct pending as [|x todo];
      [cbn [Reach.loop fst snd]; auto|cbn in Hfuel; lia].
  - destruct pending as [|x todo]; [cbn [Reach.loop fst snd]; auto|].
    cbn [Reach.loop]. destruct (Reach.member x unseen) eqn:Hx.
    + apply member_spec in Hx.
      pose proof (remove_credit next x unseen (Reach.unseen_unique _ _ _ _ _ _ Hinv) Hx)
        as Hcredit.
      destruct (IH _ _ _ (fresh_invariant next roots all unseen seen x todo Hnext Hinv Hx)
        ltac:(rewrite length_app; cbn in Hfuel; lia)) as [Hdone Hfinal].
      split; [exact Hdone|].
      destruct Hfinal as [Hnd Hsupport Hseen Hpending Hdomain Hr He].
      constructor; try assumption.
      * exact (Reach.unseen_unique _ _ _ _ _ _ Hinv).
      * intros v Hv. destruct (Hsupport v Hv) as [Hu|Hs]; [left|now right].
        apply remove_spec in Hu. tauto.
    + assert (Hnot : ~ In x unseen) by (intro Hin; apply member_spec in Hin; congruence).
      apply IH.
      * now apply (skip_invariant next roots all unseen seen x todo).
      * cbn in Hfuel. lia.
Qed.

(** A finite closed universe supplies enough fuel for every seed and successor obligation. *)
Theorem closure_complete next all roots fuel :
  NoDup all -> incl roots all -> (forall u, incl (next u) all) ->
  (Reach.credit next all + length roots <= fuel)%nat ->
  fst (Reach.loop next fuel roots all []) = [] /\
  forall v, In v (snd (Reach.loop next fuel roots all [])) <-> Reach.closure next roots v.
Proof.
  intros Hnodup Hroots Hnext Hfuel.
  assert (Hinitial : Reach.invariant next roots all all [] roots).
  { constructor.
    - exact Hnodup.
    - auto.
    - intros v Hv. contradiction.
    - intros v Hv. now apply Reach.root.
    - exact Hroots.
    - auto.
    - intros u v Hu. contradiction. }
  destruct (loop_correct next roots all fuel Hnext all [] roots Hinitial Hfuel)
    as [Hdone Hfinal].
  split; [exact Hdone|]. intro v. split.
  - apply (Reach.seen_sound _ _ _ _ _ _ Hfinal).
  - intro Hreach. induction Hreach as [x Hx|u x Hu IH Hux].
    + destruct (Reach.roots_pending _ _ _ _ _ _ Hfinal x Hx);
        [assumption|contradiction].
    + destruct (Reach.edges_pending _ _ _ _ _ _ Hfinal u x IH Hux);
        [assumption|contradiction].
Qed.

End Walk.
