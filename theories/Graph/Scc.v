(** * Strongly connected components

    Tarjan's visitor tracks discovery numbers and pending components.
    For example, closing a cycle root emits its pending vertices together.
    Builds on: depth-first search and the SCC signature. *)

From Stdlib Require Import List NArith PArith Arith Lia Sorting.Permutation.
From Argent Require Import Time Tactics Std BigO.
From Galois.Base Require Import Trie.
From Galois.Graph Require Import Data Spec DigraphSig SearchSig Search SccSig.
Import List.ListNotations.

Module Pos.
  TimeFun Pos.min.
End Pos.

Definition tarjan_initial := TarjanState Empty Empty [] Empty [] [] Empty 1%positive 1%positive.
TimeFun tarjan_initial.

Fixpoint tarjan_pop (root index : positive) (pending : list positive)
    (low : ptrie positive) (active : ptrie bool) (owners : ptrie positive)
    : list positive * list positive * ptrie positive * ptrie bool * ptrie positive :=
  match pending with
  | [] => ([], [], low, active, owners)
  | v :: rest =>
    let low' := PTrieCode.remove v low in
    let active' := PTrieCode.remove v active in
    let owners' := PTrieCode.set v index owners in
    if Pos.eqb v root then ([v], rest, low', active', owners') else
    let '(members, tail, low'', active'', owners'') :=
      tarjan_pop root index rest low' active' owners' in
    (v :: members, tail, low'', active'', owners'')
  end.
TimeFun tarjan_pop.

(** Popping updates precisely the consumed prefix, even when pending keys repeat. *)
Lemma tarjan_pop_lookup root index pending low active owners
    members tail low' active' owners' :
  tarjan_pop root index pending low active owners = (members, tail, low', active', owners') ->
  pending = members ++ tail /\ forall v,
    trie_get v low' =
      (if existsb (Pos.eqb v) members then None else trie_get v low) /\
    trie_get v active' =
      (if existsb (Pos.eqb v) members then None else trie_get v active) /\
    trie_get v owners' =
      (if existsb (Pos.eqb v) members then Some index else trie_get v owners).
Proof.
  revert low active owners members tail low' active' owners'.
  induction pending as [|u rest IH];
    intros low active owners members tail low' active' owners' Hpop.
  - cbn [tarjan_pop] in Hpop. inversion Hpop; subst.
    split; [reflexivity|]. intros v. cbn. repeat split; reflexivity.
  - cbn [tarjan_pop] in Hpop. destruct (Pos.eqb u root) eqn:Hroot.
    + inversion Hpop; subst. split; [reflexivity|]. intros v. cbn [existsb].
      destruct (Pos.eqb v u) eqn:Hsame; cbn.
      * apply Pos.eqb_eq in Hsame. subst v.
        rewrite !PTrie.get_remove_same, PTrie.get_set_same. repeat split; reflexivity.
      * apply Pos.eqb_neq in Hsame.
        rewrite !PTrie.get_remove_other, PTrie.get_set_other by exact Hsame.
        repeat split; reflexivity.
    + destruct (tarjan_pop root index rest (PTrieCode.remove u low)
        (PTrieCode.remove u active) (PTrieCode.set u index owners))
        as [[[[popped remaining] lows] actives] assigned] eqn:Hrest.
      inversion Hpop; subst members tail low' active' owners'.
      destruct (IH _ _ _ _ _ _ _ _ Hrest) as [Hprefix Hlookup].
      split; [cbn; now rewrite Hprefix|]. intros v.
      specialize (Hlookup v). cbn [existsb].
      destruct (Pos.eqb v u) eqn:Hsame; cbn.
      * apply Pos.eqb_eq in Hsame. subst v.
        rewrite !PTrie.get_remove_same, PTrie.get_set_same in Hlookup.
        destruct (existsb (Pos.eqb u) popped); exact Hlookup.
      * apply Pos.eqb_neq in Hsame.
        rewrite !PTrie.get_remove_other, PTrie.get_set_other in Hlookup by exact Hsame.
        exact Hlookup.
Qed.

(** Each consumed pending cell pays its trie updates and equality test. *)
Lemma tarjan_pop_credit w root index pending low active owners
    members tail low' active' owners' :
  Forall (fun v => Pos.size_nat v <= w) pending ->
  tarjan_pop root index pending low active owners = (members, tail, low', active', owners') ->
  (T_tarjan_pop root index pending low active owners +
      4096 * N.of_nat (w + 1) * N.of_nat (length tail) <=
    4096 * N.of_nat (w + 1) * N.of_nat (length pending) + 1)%N.
Proof.
  revert low active owners members tail low' active' owners'.
  induction pending as [|v pending IH];
    intros low active owners members tail low' active' owners' Hwidth Hpop.
  - cbn [tarjan_pop] in Hpop. inversion Hpop; subst.
    time_unfold @T_tarjan_pop. cbn [length]. nia.
  - inversion Hwidth as [|v' pending' Hv Hrest]; subst v' pending'.
    pose proof (PTrieT.T_remove_le positive v low) as Hlow.
    pose proof (PTrieT.T_remove_le bool v active) as Hactive.
    pose proof (PTrieT.T_set_le positive v index owners) as Howners.
    change (PTrieCode.T_remove v low <= 1024 * N.of_nat (Pos.size_nat v + 1))%N in Hlow.
    change (PTrieCode.T_remove v active <= 1024 * N.of_nat (Pos.size_nat v + 1))%N in Hactive.
    change (PTrieCode.T_set v index owners <=
      1024 * N.of_nat (Pos.size_nat v + 1))%N in Howners.
    pose proof (Std.Pos.T_eqb_le v root) as Hcompare.
    assert (Hbits : (N.of_nat (Pos.size_nat v + 1) <= N.of_nat (w + 1))%N) by lia.
    assert (Hcell : (1 + PTrieCode.T_remove v low + PTrieCode.T_remove v active +
      PTrieCode.T_set v index owners + Std.Pos.T_eqb v root <=
      4096 * N.of_nat (w + 1))%N) by nia.
    cbn [tarjan_pop] in Hpop. time_unfold @T_tarjan_pop.
    destruct (Pos.eqb v root) eqn:Hroot.
    + inversion Hpop; subst. cbn [length]. rewrite Nat2N.inj_succ. nia.
    + destruct (tarjan_pop root index pending (PTrieCode.remove v low)
        (PTrieCode.remove v active) (PTrieCode.set v index owners))
        as [[[[popped remaining] lows] actives] assigned] eqn:Hrec.
      inversion Hpop; subst members tail low' active' owners'.
      specialize (IH _ _ _ _ _ _ _ _ Hrest Hrec).
      cbn [length]. rewrite Nat2N.inj_succ. nia.
Qed.

Module TarjanVisitor <: VISITOR_OPS.
  Definition state := tarjan_state.

  Definition enter (v : positive) (s : state) : state :=
    TarjanState (PTrieCode.set v (tarjan_clock s) (tarjan_disc s))
      (PTrieCode.set v (tarjan_clock s) (tarjan_low s)) (v :: tarjan_pending s)
      (PTrieCode.set v true (tarjan_active s)) (v :: tarjan_frames s)
      (tarjan_emitted s) (tarjan_owners s) (Pos.succ (tarjan_clock s)) (tarjan_next s).
  TimeFun enter.

  Definition lower (v n : positive) (s : state) : state :=
    match trie_get v (tarjan_low s) with
    | None => s
    | Some old => TarjanState (tarjan_disc s) (PTrieCode.set v (Pos.min old n) (tarjan_low s))
        (tarjan_pending s) (tarjan_active s) (tarjan_frames s) (tarjan_emitted s)
        (tarjan_owners s) (tarjan_clock s) (tarjan_next s)
    end.
  TimeFun lower.

  Definition edge (kind : edge_kind) (u v : positive) (s : state) : state :=
    match kind with
    | Tree => s
    | _ => match trie_get v (tarjan_active s), trie_get v (tarjan_disc s) with
           | Some true, Some n => lower u n s
           | _, _ => s
           end
    end.
  TimeFun edge.

  Definition leave (v : positive) (s : state) : state :=
    let frames := match tarjan_frames s with [] => [] | _ :: rest => rest end in
    let s' := TarjanState (tarjan_disc s) (tarjan_low s) (tarjan_pending s)
      (tarjan_active s) frames (tarjan_emitted s) (tarjan_owners s)
      (tarjan_clock s) (tarjan_next s) in
    match trie_get v (tarjan_low s), trie_get v (tarjan_disc s) with
    | Some l, Some d =>
      if Pos.eqb l d then
        let '(members, tail, low, active, owners) :=
          tarjan_pop v (tarjan_next s) (tarjan_pending s) (tarjan_low s)
            (tarjan_active s) (tarjan_owners s) in
        TarjanState (tarjan_disc s) low tail active frames
          (members :: tarjan_emitted s) owners (tarjan_clock s) (Pos.succ (tarjan_next s))
      else match frames with [] => s' | parent :: _ => lower parent l s' end
    | _, _ => s'
    end.
  TimeFun leave.
End TarjanVisitor.

(** Present low-link entries always refer to pending vertices; emitted blocks are nonempty. *)
Definition tarjan_nonempty_state (s : tarjan_state) : Prop :=
  (forall v i, trie_get v (tarjan_low s) = Some i -> In v (tarjan_pending s)) /\
  Forall (fun block => block <> []) (tarjan_emitted s).

(** A nonempty pending stack always contributes a nonempty popped prefix. *)
Lemma tarjan_pop_nonempty root index pending low active owners
    members tail low' active' owners' :
  tarjan_pop root index pending low active owners = (members, tail, low', active', owners') ->
  pending <> [] -> members <> [].
Proof.
  intros Hpop Hpending. destruct pending as [|v pending]; [contradiction|].
  cbn [tarjan_pop] in Hpop. destruct (Pos.eqb v root).
  - inversion Hpop; discriminate.
  - destruct (tarjan_pop root index pending (PTrieCode.remove v low)
      (PTrieCode.remove v active) (PTrieCode.set v index owners))
      as [[[[popped remaining] lows] actives] assigned].
    inversion Hpop; discriminate.
Qed.

(** Popping retains low-link support only in the surviving pending suffix. *)
Lemma tarjan_pop_low_domain root index pending low active owners
    members tail low' active' owners' :
  (forall v i, trie_get v low = Some i -> In v pending) ->
  tarjan_pop root index pending low active owners = (members, tail, low', active', owners') ->
  forall v i, trie_get v low' = Some i -> In v tail.
Proof.
  intros Hdomain Hpop v i Hlookup.
  destruct (tarjan_pop_lookup _ _ _ _ _ _ _ _ _ _ _ Hpop) as [Hsplit Hkeys].
  destruct (Hkeys v) as [Hlow _]. rewrite Hlow in Hlookup.
  destruct (existsb (Pos.eqb v) members) eqn:Hmember; [discriminate Hlookup|].
  apply Hdomain in Hlookup. rewrite Hsplit in Hlookup.
  apply in_app_or in Hlookup. destruct Hlookup as [Hin|Hin]; [|exact Hin].
  assert (Hyes : existsb (Pos.eqb v) members = true).
  { apply existsb_exists. exists v. split; [exact Hin|apply Pos.eqb_refl]. }
  congruence.
Qed.

(** The initial visitor state has no low-link entries or emitted components. *)
Lemma tarjan_nonempty_initial : tarjan_nonempty_state tarjan_initial.
Proof.
  split; [|constructor]. intros v i Hlookup.
  cbn [tarjan_initial tarjan_low] in Hlookup. rewrite PTrie.get_empty in Hlookup.
  discriminate Hlookup.
Qed.

(** Entry puts its new low-link key directly on the pending stack. *)
Local Lemma tarjan_nonempty_enter v s :
  tarjan_nonempty_state s -> tarjan_nonempty_state (TarjanVisitor.enter v s).
Proof.
  intros [Hdomain Hemitted]. split; [|exact Hemitted].
  intros u i Hlookup. cbn [TarjanVisitor.enter tarjan_low] in Hlookup.
  cbn [TarjanVisitor.enter tarjan_pending].
  destruct (Pos.eq_dec u v) as [Heq|Hneq].
  - subst u. now left.
  - rewrite PTrie.get_set_other in Hlookup by exact Hneq.
    right. now apply (Hdomain u i).
Qed.

(** Lowering changes an existing low-link value without changing its support. *)
Local Lemma tarjan_nonempty_lower v n s :
  tarjan_nonempty_state s -> tarjan_nonempty_state (TarjanVisitor.lower v n s).
Proof.
  intros Hstate. unfold TarjanVisitor.lower.
  destruct (trie_get v (tarjan_low s)) as [old|] eqn:Hlow; [|exact Hstate].
  destruct Hstate as [Hdomain Hemitted]. split; [|exact Hemitted].
  intros u i Hlookup. cbn [tarjan_low] in Hlookup. cbn [tarjan_pending].
  destruct (Pos.eq_dec u v) as [Heq|Hneq].
  - subst u. now apply (Hdomain v old).
  - rewrite PTrie.get_set_other in Hlookup by exact Hneq.
    now apply (Hdomain u i).
Qed.

(** Edge callbacks preserve pending support and the existing component list. *)
Local Lemma tarjan_nonempty_edge kind u v s :
  tarjan_nonempty_state s -> tarjan_nonempty_state (TarjanVisitor.edge kind u v s).
Proof.
  intros Hstate. destruct kind; cbn [TarjanVisitor.edge]; try exact Hstate.
  all: destruct (trie_get v (tarjan_active s)) as [[|]|]; try exact Hstate.
  all: destruct (trie_get v (tarjan_disc s)); try exact Hstate.
  all: now apply tarjan_nonempty_lower.
Qed.

(** A component-closing leave has a present low link and therefore a nonempty stack. *)
Local Lemma tarjan_nonempty_leave v s :
  tarjan_nonempty_state s -> tarjan_nonempty_state (TarjanVisitor.leave v s).
Proof.
  intros [Hdomain Hemitted]. unfold TarjanVisitor.leave.
  destruct (trie_get v (tarjan_low s)) as [low|] eqn:Hlow;
    [|split; assumption].
  destruct (trie_get v (tarjan_disc s)) as [disc|] eqn:Hdisc;
    [|split; assumption].
  destruct (Pos.eqb low disc).
  - destruct (tarjan_pop v (tarjan_next s) (tarjan_pending s) (tarjan_low s)
      (tarjan_active s) (tarjan_owners s))
      as [[[[members tail] lows] actives] owners] eqn:Hpop.
    split; cbn [tarjan_low tarjan_pending tarjan_emitted].
    + eapply tarjan_pop_low_domain; eassumption.
    + constructor; [|exact Hemitted]. eapply tarjan_pop_nonempty; [exact Hpop|].
      intros Hempty. pose proof (Hdomain v low Hlow) as Hin.
      now rewrite Hempty in Hin.
  - destruct (match tarjan_frames s with [] => [] | _ :: rest => rest end).
    + split; assumption.
    + apply tarjan_nonempty_lower. split; assumption.
Qed.

(** Arbitrary event folds retain low-link support and nonempty emitted components. *)
Lemma tarjan_nonempty_fold es s : tarjan_nonempty_state s ->
  tarjan_nonempty_state
    (fold_events TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge es s).
Proof.
  unfold fold_events. revert s. induction es as [|e es IH]; intros s Hstate;
    cbn [fold_left]; [exact Hstate|].
  apply IH. destruct e; cbn [visit_event].
  - now apply tarjan_nonempty_enter.
  - now apply tarjan_nonempty_leave.
  - now apply tarjan_nonempty_edge.
Qed.

(** Every component emitted from the initial visitor state has a member. *)
Lemma tarjan_emitted_nonempty es :
  Forall (fun block => block <> [])
    (tarjan_emitted
      (fold_events TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge es tarjan_initial)).
Proof.
  exact (proj2 (tarjan_nonempty_fold es tarjan_initial tarjan_nonempty_initial)).
Qed.

(** Pending vertices and emitted components together retain the complete entered inventory. *)
Definition tarjan_bag (s : tarjan_state) : list positive :=
  tarjan_pending s ++ concat (tarjan_emitted s).

Local Lemma tarjan_bag_lower v n s :
  tarjan_bag (TarjanVisitor.lower v n s) = tarjan_bag s.
Proof.
  unfold TarjanVisitor.lower. destruct (trie_get v (tarjan_low s)); reflexivity.
Qed.

Local Lemma tarjan_bag_edge kind u v s :
  tarjan_bag (TarjanVisitor.edge kind u v s) = tarjan_bag s.
Proof.
  destruct kind; cbn [TarjanVisitor.edge]; try reflexivity.
  all: destruct (trie_get v (tarjan_active s)) as [[|]|]; try reflexivity.
  all: destruct (trie_get v (tarjan_disc s)); try reflexivity.
  all: apply tarjan_bag_lower.
Qed.

Local Lemma tarjan_bag_leave v s :
  Permutation (tarjan_bag (TarjanVisitor.leave v s)) (tarjan_bag s).
Proof.
  unfold TarjanVisitor.leave.
  destruct (trie_get v (tarjan_low s)) as [low|]; [|reflexivity].
  destruct (trie_get v (tarjan_disc s)) as [disc|]; [|reflexivity].
  destruct (Pos.eqb low disc).
  - destruct (tarjan_pop v (tarjan_next s) (tarjan_pending s) (tarjan_low s)
      (tarjan_active s) (tarjan_owners s))
      as [[[[members tail] lows] actives] owners] eqn:Hpop.
    pose proof (proj1 (tarjan_pop_lookup _ _ _ _ _ _ _ _ _ _ _ Hpop)) as Hsplit.
    unfold tarjan_bag. cbn [tarjan_pending tarjan_emitted concat]. rewrite Hsplit.
    rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm.
  - destruct (match tarjan_frames s with [] => [] | _ :: rest => rest end).
    + reflexivity.
    + rewrite tarjan_bag_lower. reflexivity.
Qed.

(** Entry adds its vertex, while edge and leave callbacks only rearrange the inventory. *)
Lemma tarjan_bag_event e s :
  Permutation
    (tarjan_bag (visit_event TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge s e))
    (entered [e] ++ tarjan_bag s).
Proof.
  destruct e; cbn [visit_event entered app].
  - reflexivity.
  - apply tarjan_bag_leave.
  - rewrite tarjan_bag_edge. reflexivity.
Qed.

(** An arbitrary visitor fold adds exactly its entering events to the initial inventory. *)
Lemma tarjan_bag_fold es s :
  Permutation
    (tarjan_bag (fold_events TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge es s))
    (rev (entered es) ++ tarjan_bag s).
Proof.
  unfold fold_events. revert s. induction es as [|e es IH]; intros s.
  - reflexivity.
  - cbn [fold_left]. eapply Permutation_trans; [apply IH|].
    eapply Permutation_trans.
    + apply Permutation_app_head. apply tarjan_bag_event.
    + destruct e; cbn [entered rev app]; [rewrite <- app_assoc| |]; reflexivity.
Qed.

(** From the initial state, pending and emitted vertices partition all entries with multiplicity. *)
Lemma tarjan_bag_inventory es :
  Permutation
    (tarjan_bag
      (fold_events TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge es tarjan_initial))
    (entered es).
Proof.
  pose proof (tarjan_bag_fold es tarjan_initial) as Hfold.
  cbn [tarjan_bag tarjan_initial tarjan_pending tarjan_emitted concat app] in Hfold.
  rewrite app_nil_r in Hfold. eapply Permutation_trans; [exact Hfold|].
  apply Permutation_sym. apply Permutation_rev.
Qed.

(** A trace with unique entries yields disjoint, duplicate-free emitted components. *)
Lemma tarjan_emitted_unique es : NoDup (entered es) ->
  NoDup (concat (tarjan_emitted
    (fold_events TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge es tarjan_initial))).
Proof.
  intros Hunique. pose proof (tarjan_bag_inventory es) as Hbag.
  apply Permutation_sym in Hbag. apply (Permutation_NoDup Hbag) in Hunique.
  unfold tarjan_bag in Hunique. now apply NoDup_app_remove_l in Hunique.
Qed.

(** Emitted vertices never exceed the number of entering events. *)
Lemma tarjan_emitted_length es :
  length (concat (tarjan_emitted
    (fold_events TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge es tarjan_initial))) <=
  length (entered es).
Proof.
  pose proof (Permutation_length (tarjan_bag_inventory es)) as Hlength.
  unfold tarjan_bag in Hlength. rewrite length_app in Hlength. lia.
Qed.

(** A proof-only maximum bounds the values of all keys in an entered list. *)
Definition tarjan_max_key (xs : list positive) : positive := fold_right Pos.max 1%positive xs.

Local Lemma tarjan_max_key_member xs v : In v xs ->
  Pos.to_nat v <= Pos.to_nat (tarjan_max_key xs).
Proof.
  unfold tarjan_max_key. induction xs as [|u xs IH]; [contradiction|].
  intros [Heq|Hin]; cbn [fold_right]; rewrite Pos2Nat.inj_max.
  - subst u. apply Nat.le_max_l.
  - eapply Nat.le_trans; [now apply IH|apply Nat.le_max_r].
Qed.

Local Lemma tarjan_max_key_width w xs :
  Forall (fun v => Pos.size_nat v <= w) xs ->
  Pos.size_nat (tarjan_max_key xs) <= Nat.max 1 w.
Proof.
  unfold tarjan_max_key. intros Hwidth.
  induction Hwidth as [|v xs Hv Hwidth IH].
  - cbn [fold_right Pos.size_nat]. apply Nat.le_max_l.
  - cbn [fold_right]. unfold Pos.max at 1.
    destruct (Pos.compare v (fold_right Pos.max 1%positive xs)); try exact IH;
      eapply Nat.le_trans; [exact Hv|apply Nat.le_max_r].
Qed.

(** Distinct positive identifiers bounded by an integer have at most that many members. *)
Lemma tarjan_positive_cardinality xs upper : NoDup xs ->
  (forall v, In v xs -> Pos.to_nat v <= upper) -> length xs <= upper.
Proof.
  intros Hunique Hupper.
  assert (Hmap : NoDup (map Pos.to_nat xs)).
  { clear Hupper. induction Hunique as [|v xs Hfresh Hunique IH]; [constructor|].
    constructor; [|exact IH]. intros Hin. apply in_map_iff in Hin.
    destruct Hin as [u [Heq Hu]]. apply Pos2Nat.inj in Heq. subst u. contradiction. }
  assert (Hrange : incl (map Pos.to_nat xs) (seq 1 upper)).
  { intros value Hin. apply in_map_iff in Hin. destruct Hin as [v [Heq Hv]].
    subst value. apply in_seq. specialize (Hupper v Hv).
    pose proof (Pos2Nat.is_pos v). lia. }
  pose proof (NoDup_incl_length Hmap Hrange) as Hlength.
  now rewrite length_map, length_seq in Hlength.
Qed.

Local Lemma tarjan_size_nat_le p q : Pos.to_nat p <= Pos.to_nat q ->
  Pos.size_nat p <= Pos.size_nat q.
Proof.
  intros Hle. destruct (Nat.eq_dec (Pos.to_nat p) (Pos.to_nat q)) as [Heq|Hneq].
  - apply Pos2Nat.inj in Heq. now subst q.
  - apply Pos.size_nat_monotone. apply Pos2Nat.inj_lt. lia.
Qed.

(** A counter bounded by one plus a distinct-key count needs at most one extra key bit. *)
Lemma tarjan_counter_width w xs p :
  NoDup xs -> Forall (fun v => Pos.size_nat v <= w) xs ->
  Pos.to_nat p <= S (length xs) -> Pos.size_nat p <= w + 1.
Proof.
  intros Hunique Hwidth Hcount. destruct xs as [|v xs].
  - cbn [length] in Hcount. assert (Heq : p = 1%positive).
    { apply Pos2Nat.inj. change (Pos.to_nat p = 1). pose proof (Pos2Nat.is_pos p). lia. }
    subst p. cbn [Pos.size_nat]. lia.
  - pose proof (tarjan_max_key_width w (v :: xs) Hwidth) as Hmaximum.
    assert (Hw : 1 <= w).
    { inversion Hwidth as [|v' xs' Hv Hrest]; subst v' xs'.
      destruct v; cbn [Pos.size_nat] in Hv; lia. }
    rewrite Nat.max_r in Hmaximum by exact Hw.
    pose proof (tarjan_positive_cardinality (v :: xs)
      (Pos.to_nat (tarjan_max_key (v :: xs))) Hunique
      (fun u Hin => tarjan_max_key_member (v :: xs) u Hin)) as Hvertices.
    assert (Hnumeric : Pos.to_nat p <= Pos.to_nat (xO (tarjan_max_key (v :: xs)))).
    { rewrite Pos2Nat.inj_xO. pose proof (Pos2Nat.is_pos (tarjan_max_key (v :: xs))). lia. }
    eapply Nat.le_trans; [apply tarjan_size_nat_le; exact Hnumeric|].
    cbn [Pos.size_nat]. lia.
Qed.


(** Lowering preserves every counter and the frame and component lists. *)
Local Lemma tarjan_lower_metadata v n s :
  tarjan_clock (TarjanVisitor.lower v n s) = tarjan_clock s /\
  tarjan_next (TarjanVisitor.lower v n s) = tarjan_next s /\
  tarjan_emitted (TarjanVisitor.lower v n s) = tarjan_emitted s /\
  tarjan_frames (TarjanVisitor.lower v n s) = tarjan_frames s.
Proof.
  unfold TarjanVisitor.lower. destruct (trie_get v (tarjan_low s)); repeat split; reflexivity.
Qed.

Local Lemma tarjan_edge_metadata kind u v s :
  tarjan_clock (TarjanVisitor.edge kind u v s) = tarjan_clock s /\
  tarjan_next (TarjanVisitor.edge kind u v s) = tarjan_next s /\
  tarjan_emitted (TarjanVisitor.edge kind u v s) = tarjan_emitted s /\
  tarjan_frames (TarjanVisitor.edge kind u v s) = tarjan_frames s.
Proof.
  destruct kind; cbn [TarjanVisitor.edge]; try (repeat split; reflexivity).
  all: destruct (trie_get v (tarjan_active s)) as [[|]|]; try (repeat split; reflexivity).
  all: destruct (trie_get v (tarjan_disc s)); try (repeat split; reflexivity).
  all: apply tarjan_lower_metadata.
Qed.

(** Each event accounts exactly for its counter increments and frame operation. *)
Lemma tarjan_event_metadata e s :
  let next := visit_event TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge s e in
  Pos.to_nat (tarjan_clock next) = length (entered [e]) + Pos.to_nat (tarjan_clock s) /\
  Pos.to_nat (tarjan_next next) + length (tarjan_emitted s) =
    Pos.to_nat (tarjan_next s) + length (tarjan_emitted next) /\
  tarjan_frames next = match e with
    | Enter v => v :: tarjan_frames s
    | Leave _ => tl (tarjan_frames s)
    | Edge _ _ _ => tarjan_frames s
    end.
Proof.
  destruct e as [v|v|kind u v]; cbn [visit_event entered length].
  - cbn [TarjanVisitor.enter tarjan_clock tarjan_next tarjan_emitted tarjan_frames].
    rewrite Pos2Nat.inj_succ. repeat split; try reflexivity; lia.
  - unfold TarjanVisitor.leave.
    destruct (trie_get v (tarjan_low s)) as [low|];
      [|repeat split; reflexivity].
    destruct (trie_get v (tarjan_disc s)) as [disc|];
      [|repeat split; reflexivity].
    destruct (Pos.eqb low disc).
    + destruct (tarjan_pop v (tarjan_next s) (tarjan_pending s) (tarjan_low s)
        (tarjan_active s) (tarjan_owners s))
        as [[[[members tail] lows] actives] owners].
      cbn [tarjan_clock tarjan_next tarjan_emitted tarjan_frames length].
      rewrite Pos2Nat.inj_succ. repeat split; try reflexivity; lia.
    + destruct (tarjan_frames s) as [|frame frames]; cbn [tl].
      * repeat split; reflexivity.
      * destruct frames as [|parent frames]; [repeat split; reflexivity|].
        destruct (tarjan_lower_metadata parent low
          (TarjanState (tarjan_disc s) (tarjan_low s) (tarjan_pending s)
            (tarjan_active s) (parent :: frames) (tarjan_emitted s)
            (tarjan_owners s) (tarjan_clock s) (tarjan_next s)))
          as [Hclock [Hnext [Hemitted Hframes]]].
        rewrite Hclock, Hnext, Hemitted, Hframes. repeat split; reflexivity.
  - destruct (tarjan_edge_metadata kind u v s) as [Hclock [Hnext [Hemitted Hframes]]].
    rewrite Hclock, Hnext, Hemitted, Hframes. repeat split; reflexivity.
Qed.

(** Discovery increments count entering events, and owner increments count emitted blocks. *)
Lemma tarjan_fold_metadata es s :
  let final := fold_events TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge es s in
  Pos.to_nat (tarjan_clock final) = length (entered es) + Pos.to_nat (tarjan_clock s) /\
  Pos.to_nat (tarjan_next final) + length (tarjan_emitted s) =
    Pos.to_nat (tarjan_next s) + length (tarjan_emitted final).
Proof.
  unfold fold_events. revert s. induction es as [|e es IH]; intros s.
  - cbn [fold_left entered length]. split; reflexivity.
  - cbn [fold_left].
    destruct (IH (visit_event TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge s e))
      as [Hclock Hnext].
    destruct (tarjan_event_metadata e s) as [Hstep_clock [Hstep_next Hframes]].
    split; [destruct e; cbn [entered length] in *; lia|lia].
Qed.

(** Starting at one gives the next discovery number after all entries. *)
Lemma tarjan_clock_count es :
  Pos.to_nat (tarjan_clock
    (fold_events TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge es tarjan_initial)) =
  S (length (entered es)).
Proof.
  pose proof (proj1 (tarjan_fold_metadata es tarjan_initial)) as Hclock.
  cbn [tarjan_initial tarjan_clock Pos.to_nat] in Hclock. lia.
Qed.

(** Starting at one gives the next component number after all emissions. *)
Lemma tarjan_next_count es :
  Pos.to_nat (tarjan_next
    (fold_events TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge es tarjan_initial)) =
  S (length (tarjan_emitted
    (fold_events TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge es tarjan_initial))).
Proof.
  pose proof (proj2 (tarjan_fold_metadata es tarjan_initial)) as Hnext.
  cbn [tarjan_initial tarjan_next tarjan_emitted Pos.to_nat length] in Hnext. lia.
Qed.

Local Lemma tarjan_nonempty_count blocks : Forall (fun block : list positive => block <> []) blocks ->
  length blocks <= length (concat blocks).
Proof.
  intros Hblocks. induction Hblocks as [|block blocks Hnonempty Hblocks IH]; [reflexivity|].
  destruct block; [contradiction|]. cbn [concat length]. rewrite length_app. cbn [length]. lia.
Qed.

(** Nonempty emitted blocks cannot outnumber the entered vertices they contain. *)
Lemma tarjan_emitted_count es :
  length (tarjan_emitted
    (fold_events TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge es tarjan_initial)) <=
  length (entered es).
Proof.
  eapply Nat.le_trans; [apply tarjan_nonempty_count; apply tarjan_emitted_nonempty|].
  apply tarjan_emitted_length.
Qed.

(** Frames only retain keys from their initial stack and entering events. *)
Lemma tarjan_frames_domain (P : positive -> Prop) es s :
  Forall P (entered es) -> Forall P (tarjan_frames s) ->
  Forall P (tarjan_frames
    (fold_events TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge es s)).
Proof.
  unfold fold_events. revert s. induction es as [|e es IH]; intros s Hentries Hframes;
    cbn [fold_left]; [exact Hframes|].
  destruct (tarjan_event_metadata e s) as [_ [_ Hstep]].
  apply IH; destruct e; cbn [entered] in Hentries; try exact Hentries;
    try (now inversion Hentries).
  all: rewrite Hstep.
  - inversion Hentries; subst. now constructor.
  - destruct (tarjan_frames s); [constructor|now inversion Hframes].
  - exact Hframes.
Qed.


(** Every stored discovery number and low link remains below the discovery counter. *)
Definition tarjan_values_below_clock (s : tarjan_state) : Prop :=
  (forall v i, trie_get v (tarjan_disc s) = Some i ->
    Pos.to_nat i < Pos.to_nat (tarjan_clock s)) /\
  (forall v i, trie_get v (tarjan_low s) = Some i ->
    Pos.to_nat i < Pos.to_nat (tarjan_clock s)).

Local Lemma tarjan_values_set v clock values :
  (forall u i, trie_get u values = Some i -> Pos.to_nat i < Pos.to_nat clock) ->
  forall u i, trie_get u (PTrieCode.set v clock values) = Some i ->
    Pos.to_nat i < Pos.to_nat (Pos.succ clock).
Proof.
  intros Hvalues u i Hlookup. rewrite Pos2Nat.inj_succ.
  destruct (Pos.eq_dec u v) as [Heq|Hneq].
  - subst u. rewrite PTrie.get_set_same in Hlookup. injection Hlookup as Heq. subst i. lia.
  - rewrite PTrie.get_set_other in Hlookup by exact Hneq.
    specialize (Hvalues u i Hlookup). lia.
Qed.

Local Lemma tarjan_values_enter v s :
  tarjan_values_below_clock s -> tarjan_values_below_clock (TarjanVisitor.enter v s).
Proof.
  intros [Hdisc Hlow]. split; cbn [TarjanVisitor.enter tarjan_disc tarjan_low tarjan_clock];
    apply tarjan_values_set; assumption.
Qed.

Local Lemma tarjan_values_lower v n s :
  tarjan_values_below_clock s -> tarjan_values_below_clock (TarjanVisitor.lower v n s).
Proof.
  intros Hvalues. unfold TarjanVisitor.lower.
  destruct (trie_get v (tarjan_low s)) as [old|] eqn:Hlookup; [|exact Hvalues].
  destruct Hvalues as [Hdisc Hlow]. split; [exact Hdisc|].
  intros u i Hget. cbn [tarjan_low] in Hget. cbn [tarjan_clock].
  destruct (Pos.eq_dec u v) as [Heq|Hneq].
  - subst u. rewrite PTrie.get_set_same in Hget. injection Hget as Heq. subst i.
    rewrite Pos2Nat.inj_min. eapply Nat.le_lt_trans; [apply Nat.le_min_l|].
    now apply (Hlow v old).
  - rewrite PTrie.get_set_other in Hget by exact Hneq. now apply (Hlow u i).
Qed.

Local Lemma tarjan_values_edge kind u v s :
  tarjan_values_below_clock s -> tarjan_values_below_clock (TarjanVisitor.edge kind u v s).
Proof.
  intros Hvalues. destruct kind; cbn [TarjanVisitor.edge]; try exact Hvalues.
  all: destruct (trie_get v (tarjan_active s)) as [[|]|]; try exact Hvalues.
  all: destruct (trie_get v (tarjan_disc s)); try exact Hvalues.
  all: now apply tarjan_values_lower.
Qed.

Local Lemma tarjan_values_leave v s :
  tarjan_values_below_clock s -> tarjan_values_below_clock (TarjanVisitor.leave v s).
Proof.
  intros [Hdisc Hlow]. unfold TarjanVisitor.leave.
  destruct (trie_get v (tarjan_low s)) as [low|]; [|split; assumption].
  destruct (trie_get v (tarjan_disc s)) as [disc|]; [|split; assumption].
  destruct (Pos.eqb low disc).
  - destruct (tarjan_pop v (tarjan_next s) (tarjan_pending s) (tarjan_low s)
      (tarjan_active s) (tarjan_owners s))
      as [[[[members tail] lows] actives] owners] eqn:Hpop.
    split; [exact Hdisc|]. intros u i Hlookup.
    cbn [tarjan_low] in Hlookup. cbn [tarjan_clock].
    destruct (proj2 (tarjan_pop_lookup _ _ _ _ _ _ _ _ _ _ _ Hpop) u)
      as [Hget _]. rewrite Hget in Hlookup.
    destruct (existsb (Pos.eqb u) members); [discriminate|now apply (Hlow u i)].
  - destruct (match tarjan_frames s with [] => [] | _ :: rest => rest end).
    + split; assumption.
    + apply tarjan_values_lower. split; assumption.
Qed.

(** The stored-value bound is preserved by arbitrary event folds. *)
Lemma tarjan_values_fold es s : tarjan_values_below_clock s ->
  tarjan_values_below_clock
    (fold_events TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge es s).
Proof.
  unfold fold_events. revert s. induction es as [|e es IH]; intros s Hvalues;
    cbn [fold_left]; [exact Hvalues|].
  apply IH. destruct e; cbn [visit_event].
  - now apply tarjan_values_enter.
  - now apply tarjan_values_leave.
  - now apply tarjan_values_edge.
Qed.

Lemma tarjan_values_initial : tarjan_values_below_clock tarjan_initial.
Proof.
  split; intros v i Hlookup;
    cbn [tarjan_initial tarjan_disc tarjan_low] in Hlookup;
    rewrite PTrie.get_empty in Hlookup; discriminate Hlookup.
Qed.

(** Unique bounded entry keys bound the operational state, regardless of other event order. *)
Lemma tarjan_fold_width w es :
  NoDup (entered es) -> Forall (fun v => Pos.size_nat v <= w) (entered es) ->
  let final := fold_events TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge es tarjan_initial in
  Forall (fun v => Pos.size_nat v <= w) (tarjan_pending final) /\
  Forall (fun v => Pos.size_nat v <= w) (tarjan_frames final) /\
  Pos.size_nat (tarjan_clock final) <= w + 1 /\
  Pos.size_nat (tarjan_next final) <= w + 1 /\
  (forall v i, trie_get v (tarjan_disc final) = Some i -> Pos.size_nat i <= w + 1) /\
  (forall v i, trie_get v (tarjan_low final) = Some i -> Pos.size_nat i <= w + 1).
Proof.
  intros Hunique Hwidth. cbn zeta.
  pose proof (tarjan_clock_count es) as Hclock.
  pose proof (tarjan_next_count es) as Hnext.
  pose proof (tarjan_emitted_count es) as Hemitted.
  destruct (tarjan_values_fold es tarjan_initial tarjan_values_initial) as [Hdisc Hlow].
  split.
  - pose proof (Permutation_Forall (Permutation_sym (tarjan_bag_inventory es)) Hwidth) as Hbag.
    unfold tarjan_bag in Hbag. rewrite Forall_app in Hbag. exact (proj1 Hbag).
  - split.
    + apply tarjan_frames_domain; [exact Hwidth|constructor].
    + split.
      * eapply tarjan_counter_width; [exact Hunique|exact Hwidth|lia].
      * split.
        -- eapply tarjan_counter_width; [exact Hunique|exact Hwidth|lia].
        -- split; intros v i Hlookup.
           ++ specialize (Hdisc v i Hlookup).
              eapply tarjan_counter_width; [exact Hunique|exact Hwidth|lia].
           ++ specialize (Hlow v i Hlookup).
              eapply tarjan_counter_width; [exact Hunique|exact Hwidth|lia].
Qed.


Module TarjanSearchCode := SearchCode TarjanVisitor.
Module TarjanSearch.
  Include TarjanSearchCode.
  TimeFun dfs.
End TarjanSearch.

(** Rebuild the search graph from listed rows and exclude every unlisted successor. *)
Definition scc_graph (g : prepared) : prepared :=
  let vs := nodes g in
  let listed := fold_left (fun acc v => PTrieCode.set v true acc) vs Empty in
  let rows := fold_left (fun acc v => PTrieCode.set v
    (filter (fun u => match trie_get u listed with Some _ => true | None => false end)
      (succs (base g) v)) acc) vs Empty in
  let b := Digraph vs rows in
  Prepared b Empty (N.of_nat (graph_n b)) (N.of_nat (graph_e b)).
TimeFun scc_graph.

(** Repeated row keys retain the same row function at every occurrence. *)
Lemma scc_rows_lookup {A} (row : positive -> A) vs initial v :
  trie_get v (fold_left (fun acc u => PTrieCode.set u (row u) acc) vs initial) =
    if existsb (Pos.eqb v) vs then Some (row v) else trie_get v initial.
Proof.
  revert initial. induction vs as [|u vs IH]; intro initial.
  - reflexivity.
  - cbn [fold_left existsb]. rewrite IH.
    destruct (Pos.eqb v u) eqn:Heq; destruct (existsb (Pos.eqb v) vs); cbn.
    + reflexivity.
    + apply Pos.eqb_eq in Heq. subst u. apply PTrie.get_set_same.
    + reflexivity.
    + apply PTrie.get_set_other. now apply Pos.eqb_neq.
Qed.

(** A finite listed-vertex table records precisely list membership, including duplicates. *)
Lemma scc_listed_lookup vs v :
  (exists b, trie_get v
    (fold_left (fun acc u => PTrieCode.set u true acc) vs Empty) = Some b) <-> In v vs.
Proof.
  rewrite (scc_rows_lookup (fun _ => true)), PTrie.get_empty.
  destruct (existsb (Pos.eqb v) vs) eqn:Hmember.
  - split; [intros _|intros _; now exists true].
    apply existsb_exists in Hmember. destruct Hmember as [u [Hin Heq]].
    apply Pos.eqb_eq in Heq. now subst u.
  - split.
    + intros [b Hget]. discriminate.
    + intro Hin. assert (Hexists : existsb (Pos.eqb v) vs = true).
      { apply existsb_exists. exists v. split; [exact Hin|apply Pos.eqb_refl]. }
      congruence.
Qed.

(** The executable listed test agrees with the list's Boolean membership test. *)
Lemma scc_listed_test vs v :
  (match trie_get v
    (fold_left (fun acc u => PTrieCode.set u true acc) vs Empty) with
   | Some _ => true | None => false end) = existsb (Pos.eqb v) vs.
Proof.
  rewrite (scc_rows_lookup (fun _ => true)), PTrie.get_empty.
  destruct (existsb (Pos.eqb v) vs); reflexivity.
Qed.

(** Filtering preserves the source vertex list, including its multiplicities. *)
Lemma scc_graph_nodes g : nodes (scc_graph g) = nodes g.
Proof.
  destruct g as [[vs rows] predecessors vertices edges]. reflexivity.
Qed.

(** Filtering computes both count caches from its rebuilt graph. *)
Lemma scc_graph_counts g : counts_ok (scc_graph g).
Proof.
  unfold counts_ok, scc_graph. split; reflexivity.
Qed.

(** Filtered rows keep exactly the listed successor occurrences, in their original order. *)
Lemma scc_graph_succs g v :
  succs (base (scc_graph g)) v =
    if existsb (Pos.eqb v) (nodes g) then
      filter (fun u => existsb (Pos.eqb u) (nodes g)) (succs (base g) v)
    else [].
Proof.
  unfold scc_graph. cbn [base succs]. rewrite scc_rows_lookup, PTrie.get_empty.
  destruct (existsb (Pos.eqb v) (nodes g)); [|reflexivity].
  apply filter_ext. intro u. apply scc_listed_test.
Qed.

(** A listed source has the filtered original row. *)
Lemma scc_graph_succs_listed g v : In v (nodes g) ->
  succs (base (scc_graph g)) v =
    filter (fun u => existsb (Pos.eqb u) (nodes g)) (succs (base g) v).
Proof.
  intro Hin. rewrite scc_graph_succs.
  assert (Hexists : existsb (Pos.eqb v) (nodes g) = true).
  { apply existsb_exists. exists v. split; [exact Hin|apply Pos.eqb_refl]. }
  now rewrite Hexists.
Qed.

(** Every successor of a filtered row is a listed source vertex. *)
Lemma scc_graph_closed g u v : edge (base (scc_graph g)) u v -> In v (nodes g).
Proof.
  unfold edge. rewrite scc_graph_succs.
  destruct (existsb (Pos.eqb u) (nodes g)); [|contradiction].
  intro Hin. apply filter_In in Hin. destruct Hin as [_ Hlisted].
  apply existsb_exists in Hlisted. destruct Hlisted as [w [Hin Heq]].
  apply Pos.eqb_eq in Heq. now subst w.
Qed.

(** Distinct source vertices suffice for well-formedness after filtering. *)
Lemma scc_graph_wf g : NoDup (nodes g) -> wf_graph (base (scc_graph g)).
Proof.
  intro Hdistinct. split.
  - change (NoDup (nodes (scc_graph g))). now rewrite scc_graph_nodes.
  - intros u v _ Hedge. change (In v (nodes (scc_graph g))).
    rewrite scc_graph_nodes. now apply (scc_graph_closed g u).
Qed.

(** Filtering does not remove any successor of a well-formed listed source. *)
Lemma scc_graph_agrees g v : wf_graph (base g) -> In v (nodes g) ->
  succs (base (scc_graph g)) v = succs (base g) v.
Proof.
  assert (Hnodes : nodes g = verts (base g)).
  { destruct g as [[vs rows] predecessors vertices edges]. reflexivity. }
  intros [_ Hclosed] Hin. rewrite scc_graph_succs_listed by exact Hin.
  rewrite <- (filter_true (succs (base g) v)) at 2.
  apply filter_ext_in. intros u Hu. apply existsb_exists. exists u.
  split.
  - rewrite Hnodes. apply (Hclosed v u); [now rewrite <- Hnodes|exact Hu].
  - apply Pos.eqb_refl.
Qed.

(** The filtered traversal reads neither predecessor nor count caches of its input. *)
Definition scc_trace (g : prepared) : list event :=
  let ready := scc_graph g in
  prepared_search_trace ready (nodes ready).
TimeFun scc_trace.

Local Opaque prepared_search_trace.

(** Filtering gives successor closure with respect to its own listed vertices. *)
Lemma scc_search_closed g u v :
  In u (nodes (scc_graph g)) -> edge (base (scc_graph g)) u v ->
  In v (nodes (scc_graph g)).
Proof.
  intros Hu Hedge. rewrite scc_graph_nodes. now apply (scc_graph_closed g u v).
Qed.

(** Filtered traversal enters each key at most once, including duplicate input rows. *)
Lemma scc_trace_unique g : NoDup (entered (scc_trace g)).
Proof.
  unfold scc_trace. apply prepared_search_unique_raw.
Qed.

(** Recomputed counts complete the filtered traversal and close its active stack. *)
Lemma scc_trace_nested g : trace_stack [] (scc_trace g) [].
Proof.
  unfold scc_trace. apply prepared_search_nested_closed.
  - apply scc_graph_counts.
  - apply scc_search_closed.
  - auto.
Qed.

(** Every listed vertex is a root, and filtering prevents any unlisted entry. *)
Lemma scc_trace_entered g v : In v (entered (scc_trace g)) <-> In v (nodes g).
Proof.
  unfold scc_trace.
  rewrite (prepared_search_reach_closed (scc_graph g) (nodes (scc_graph g))
    (scc_graph_counts g) (scc_search_closed g) (fun r Hin => Hin) v).
  split.
  - intros Hreach. apply search_reach_origin in Hreach.
    destruct Hreach as [Hroot|[u [Hreach Hedge]]].
    + now rewrite scc_graph_nodes in Hroot.
    + now apply (scc_graph_closed g u v).
  - intros Hin. exists v, [v]. split; [now rewrite scc_graph_nodes|constructor].
Qed.

(** Filtered traversal emits precisely two vertex events and each visited row occurrence. *)
Lemma scc_trace_length g :
  length (scc_trace g) = 2 * length (entered (scc_trace g)) +
    fold_right (fun v n => length (succs (base (scc_graph g)) v) + n) 0
      (entered (scc_trace g)).
Proof.
  pose proof (prepared_search_event_exact (scc_graph g) (nodes (scc_graph g))
    (scc_graph_counts g) (scc_search_closed g) (fun r Hin => Hin)) as Hlength.
  rewrite search_event_supply_entered in Hlength. exact Hlength.
Qed.

Local Lemma scc_weight_app {A} (weight : A -> nat) first last :
  fold_right (fun v n => weight v + n) 0 (first ++ last) =
    fold_right (fun v n => weight v + n) 0 first +
    fold_right (fun v n => weight v + n) 0 last.
Proof.
  induction first as [|v first IH]; cbn [app fold_right]; lia.
Qed.

(** Distinct included keys consume at most the weighted occurrences of the containing list. *)
Lemma scc_weight_incl {A} (weight : A -> nat) first last :
  NoDup first -> incl first last ->
  fold_right (fun v n => weight v + n) 0 first <=
    fold_right (fun v n => weight v + n) 0 last.
Proof.
  intros Hunique. revert last. induction Hunique as [|v first Hfresh Hunique IH];
    intros last Hincl; [cbn; lia|].
  destruct (in_split v last (Hincl v (or_introl eq_refl))) as [before [after Heq]].
  subst last. assert (Hrest : incl first (before ++ after)).
  { intros u Hu. specialize (Hincl u (or_intror Hu)). apply in_app_or in Hincl.
    apply in_or_app. destruct Hincl as [Hbefore|[Heq|Hafter]].
    - now left.
    - subst u. contradiction.
    - now right. }
  specialize (IH (before ++ after) Hrest).
  rewrite scc_weight_app in IH. rewrite scc_weight_app. cbn [fold_right]. lia.
Qed.

(** Filtering a successor row never increases its occurrence count. *)
Lemma scc_graph_row_length g v :
  length (succs (base (scc_graph g)) v) <= length (succs (base g) v).
Proof.
  rewrite scc_graph_succs. destruct (existsb (Pos.eqb v) (nodes g));
    [apply filter_length_le|cbn; lia].
Qed.

(** Duplicate listed vertices and filtered edges can only enlarge the input size budget. *)
Lemma scc_trace_size g :
  length (scc_trace g) <= 2 * graph_n (base g) + graph_e (base g).
Proof.
  assert (Hincluded : incl (entered (scc_trace g)) (nodes g)).
  { intros v Hin. now apply scc_trace_entered in Hin. }
  pose proof (scc_trace_unique g) as Hunique.
  pose proof (NoDup_incl_length Hunique Hincluded) as Hvertices.
  pose proof (scc_weight_incl (fun v => length (succs (base g) v))
    _ _ Hunique Hincluded) as Hrows.
  cbn beta in Hrows.
  assert (Hfiltered :
    fold_right (fun v n => length (succs (base (scc_graph g)) v) + n) 0
      (entered (scc_trace g)) <=
    fold_right (fun v n => length (succs (base g) v) + n) 0 (entered (scc_trace g))).
  { clear Hvertices Hrows Hunique Hincluded.
    induction (entered (scc_trace g)) as [|v rest IH]; cbn [fold_right]; [lia|].
    pose proof (scc_graph_row_length g v). lia. }
  assert (Hnodes : length (nodes g) = graph_n (base g)).
  { destruct g as [[vertices adjacency] predecessors n e]. reflexivity. }
  assert (Hedges : fold_right (fun v n => length (succs (base g) v) + n) 0 (nodes g) =
      graph_e (base g)).
  { destruct g as [[vertices adjacency] predecessors n e]. reflexivity. }
  rewrite Hnodes in Hvertices. rewrite Hedges in Hrows. rewrite scc_trace_length. lia.
Qed.

Local Lemma scc_weight_permutation {A} (weight : A -> nat) first last :
  Permutation first last ->
  fold_right (fun v n => weight v + n) 0 first =
    fold_right (fun v n => weight v + n) 0 last.
Proof.
  intros Hperm. induction Hperm; cbn [fold_right]; lia.
Qed.

Local Lemma scc_weight_ext {A} (first second : A -> nat) xs :
  (forall v, In v xs -> first v = second v) ->
  fold_right (fun v n => first v + n) 0 xs =
    fold_right (fun v n => second v + n) 0 xs.
Proof.
  induction xs as [|v xs IH]; intros Hagree; [reflexivity|].
  cbn [fold_right]. rewrite (Hagree v (or_introl eq_refl)).
  rewrite IH; [reflexivity|]. intros u Hin. apply Hagree. now right.
Qed.

(** For a well-formed listed graph, the entered list permutes every supplied vertex once. *)
Lemma scc_trace_partition g : wf_graph (base g) ->
  Permutation (entered (scc_trace g)) (nodes g).
Proof.
  intros Hwf. apply NoDup_Permutation.
  - apply scc_trace_unique.
  - destruct g as [[vertices adjacency] predecessors n e]. exact (proj1 Hwf).
  - intros v. apply scc_trace_entered.
Qed.

(** Well-formed inputs retain every row and attain the exact vertex-and-edge event count. *)
Lemma scc_trace_size_exact g : wf_graph (base g) ->
  length (scc_trace g) = 2 * graph_n (base g) + graph_e (base g).
Proof.
  intros Hwf. pose proof (scc_trace_partition g Hwf) as Hperm.
  pose proof (Permutation_length Hperm) as Hvertices.
  pose proof (scc_weight_permutation (fun v => length (succs (base g) v))
    _ _ Hperm) as Hrows. cbn beta in Hrows.
  assert (Hfiltered :
    fold_right (fun v n => length (succs (base (scc_graph g)) v) + n) 0
      (entered (scc_trace g)) =
    fold_right (fun v n => length (succs (base g) v) + n) 0 (entered (scc_trace g))).
  { apply scc_weight_ext. intros v Hin. f_equal. apply scc_graph_agrees; [exact Hwf|].
    now apply scc_trace_entered in Hin. }
  assert (Hnodes : length (nodes g) = graph_n (base g)).
  { destruct g as [[vertices adjacency] predecessors n e]. reflexivity. }
  assert (Hedges : fold_right (fun v n => length (succs (base g) v) + n) 0 (nodes g) =
      graph_e (base g)).
  { destruct g as [[vertices adjacency] predecessors n e]. reflexivity. }
  rewrite Hnodes in Hvertices. rewrite Hedges in Hrows.
  now rewrite scc_trace_length, Hfiltered, Hvertices, Hrows.
Qed.

(** A leave event refers either to an initially active vertex or to an earlier entry. *)
Lemma scc_stack_leave_member stack es final v :
  trace_stack stack es final -> In (Leave v) es -> In v stack \/ In (Enter v) es.
Proof.
  intros Hstack. induction Hstack as
    [stack|stack u rest final Hrest IH|stack u rest final Hrest IH|
      stack kind u target rest final Hrest IH]; intros Hin.
  - contradiction.
  - cbn [In] in Hin |- *. destruct Hin as [Hbad|Hin]; [discriminate Hbad|].
    destruct (IH Hin) as [[Heq|Hactive]|Henter].
    + right. left. now subst u.
    + now left.
    + right. now right.
  - cbn [In] in Hin |- *. destruct Hin as [Heq|Hin].
    + injection Heq as Heq. left. now left.
    + destruct (IH Hin) as [Hactive|Henter].
      * left. now right.
      * right. now right.
  - cbn [In] in Hin |- *. destruct Hin as [Hbad|Hin]; [discriminate Hbad|].
    destruct (IH Hin) as [Hactive|Henter].
    + now left.
    + right. now right.
Qed.

(** Completed filtered traversal retains exactly the filtered successor rows. *)
Lemma scc_trace_rows g : search_trace_rows (base (scc_graph g)) (scc_trace g).
Proof.
  unfold scc_trace. apply prepared_search_rows_closed.
  - apply scc_graph_counts.
  - apply scc_search_closed.
  - auto.
Qed.

(** Every key mentioned by an actual Tarjan event is a listed input vertex. *)
Lemma scc_trace_listed g :
  Forall (fun e => match e with
    | Enter v | Leave v => In v (nodes g)
    | Edge _ u v => In u (nodes g) /\ In v (nodes g)
    end) (scc_trace g).
Proof.
  apply Forall_forall. intros [v|v|kind u v] Hin.
  - apply scc_trace_entered. now apply search_entered_member.
  - destruct (scc_stack_leave_member [] _ [] v (scc_trace_nested g) Hin)
      as [Hnil|Henter]; [contradiction|].
    apply scc_trace_entered. now apply search_entered_member.
  - destruct (search_trace_rows_edge _ _ kind u v (scc_trace_rows g) Hin) as [Henter Hedge].
    split; [now apply scc_trace_entered in Henter|now apply (scc_graph_closed g u v)].
Qed.

(** The input graph width bounds every listed vertex key. *)
Lemma scc_node_width g v : In v (nodes g) -> Pos.size_nat v <= graph_width (base g).
Proof.
  destruct g as [[vertices adjacency] predecessors n e].
  cbn [nodes base graph_width]. intros Hin. rewrite search_graph_max.
  eapply Nat.le_trans; [apply search_vertex_width_member; exact Hin|apply Nat.le_max_l].
Qed.

(** All actual Tarjan callback keys have the input graph's identifier width. *)
Lemma scc_trace_event_width g :
  Forall (fun e => match e with
    | Enter v | Leave v => Pos.size_nat v <= graph_width (base g)
    | Edge _ u v => Pos.size_nat u <= graph_width (base g) /\
        Pos.size_nat v <= graph_width (base g)
    end) (scc_trace g).
Proof.
  pose proof (scc_trace_listed g) as Hlisted. rewrite Forall_forall in Hlisted.
  apply Forall_forall. intros e Hin. specialize (Hlisted e Hin).
  destruct e; cbn in *; [now apply scc_node_width|now apply scc_node_width|].
  destruct Hlisted as [Hu Hv]. split; now apply scc_node_width.
Qed.

(** Every actual prefix retains unique entering events. *)
Lemma scc_trace_prefix_unique g prefix suffix : scc_trace g = prefix ++ suffix ->
  NoDup (entered prefix).
Proof.
  intros Heq. pose proof (scc_trace_unique g) as Hunique.
  rewrite Heq, search_entered_app in Hunique. now apply NoDup_app_remove_r in Hunique.
Qed.

(** Every actual prefix retains the callback key-width domain. *)
Lemma scc_trace_prefix_width g prefix suffix : scc_trace g = prefix ++ suffix ->
  Forall (fun e => match e with
    | Enter v | Leave v => Pos.size_nat v <= graph_width (base g)
    | Edge _ u v => Pos.size_nat u <= graph_width (base g) /\
        Pos.size_nat v <= graph_width (base g)
    end) prefix.
Proof.
  intros Heq. pose proof (scc_trace_event_width g) as Hwidth.
  rewrite Heq, Forall_app in Hwidth. exact (proj1 Hwidth).
Qed.

Module SccCode <: SCC_OPS.
  Definition run (g : prepared) : scc :=
    let result := fold_events TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge
      (scc_trace g) tarjan_initial in
    Scc (tarjan_owners result) (rev_append (tarjan_emitted result) []).
End SccCode.

Opaque search_trace.

Module Scc <: SCC.
  Include SccCode.
  Include SCC_SPEC.

  Lemma comp_spec : forall g, wf_graph (base g) -> forall u v,
    (exists i, trie_get u (comp (run g)) = Some i /\
      trie_get v (comp (run g)) = Some i) <->
    In u (nodes g) /\ In v (nodes g) /\ mutually_reachable (base g) u v.
  Proof. Admitted. (* CONVERT: GraphTarjan: filtered traversal requires the scoped proof. *)

  Lemma comps_partition : forall g, wf_graph (base g) ->
    NoDup (concat (comps (run g))) /\
    (forall v, In v (concat (comps (run g))) <-> In v (nodes g)).
  Proof. Admitted. (* CONVERT: GraphTarjan: filtered traversal requires the scoped proof. *)

  Lemma comps_nonempty : forall g, wf_graph (base g) ->
    Forall (fun vs => vs <> []) (comps (run g)).
  Proof.
    intros g Hwf. unfold run. cbn [comps].
    rewrite rev_append_rev, app_nil_r. apply Forall_rev. apply tarjan_emitted_nonempty.
  Qed.

  Lemma owners_spec : forall g, wf_graph (base g) -> forall v i,
    trie_get v (comp (run g)) = Some i <->
    exists vs, nth_error (comps (run g)) (Nat.pred (Pos.to_nat i)) = Some vs /\ In v vs.
  Proof. Admitted. (* CONVERT: GraphTarjan: filtered traversal requires the scoped proof. *)

  Lemma comps_order : forall g, wf_graph (base g) -> forall u v i j,
    edge (base g) u v -> trie_get u (comp (run g)) = Some i ->
    trie_get v (comp (run g)) = Some j -> (j <= i)%positive.
  Proof. Admitted. (* CONVERT: GraphTarjan: filtered traversal requires the scoped proof. *)
End Scc.

Transparent search_trace.

Module SccT <: SCC_ALL.
  Include Scc.
  TimeFun run.
  Definition c_scc : N := 1%N. (* STUB *)

  Lemma T_run_le : forall g,
    (T_run g <= c_scc * N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma run_bigO : bigO (fun _ => True)
    (fun g => N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
      (graph_width (base g) + 1))) T_run.
  Proof. Admitted. (* STUB *)

  Definition tarjan_initial := tarjan_initial.
  Definition tarjan_enter := TarjanVisitor.enter.
  TimeFun tarjan_enter.
  Definition tarjan_leave := TarjanVisitor.leave.
  TimeFun tarjan_leave.
  Definition tarjan_edge := TarjanVisitor.edge.
  TimeFun tarjan_edge.
  Definition tarjan_pop := tarjan_pop.
  TimeFun tarjan_pop.
  Definition tarjan_trace := scc_trace.
  TimeFun tarjan_trace.
  Definition k_pop : N := 4096%N.
  Definition k_callback : N := 1%N. (* STUB *)
  Definition k_result : N := 8%N.
  Definition k_search : N := 1%N. (* STUB *)

  Definition apply_event (s : tarjan_state) (e : event) : tarjan_state :=
    visit_event tarjan_enter tarjan_leave tarjan_edge s e.
  Definition callback_cost (e : event) (s : tarjan_state) : N :=
    match e with
    | Enter v => T_tarjan_enter v s
    | Leave v => T_tarjan_leave v s
    | Edge kind u v => T_tarjan_edge kind u v s
    end.
  Definition prefix_state (es : list event) : tarjan_state :=
    fold_events tarjan_enter tarjan_leave tarjan_edge es tarjan_initial.
  Definition pop_unit (w : nat) := (k_pop * N.of_nat (w + 1))%N.
  Definition potential (w : nat) (s : tarjan_state) : N :=
    (pop_unit w * N.of_nat (length (tarjan_pending s)) +
      k_result * N.of_nat (length (tarjan_emitted s)))%N.
  Definition event_domain (w : nat) (e : event) : Prop :=
    match e with
    | Enter v | Leave v => Pos.size_nat v <= w
    | Edge _ u v => Pos.size_nat u <= w /\ Pos.size_nat v <= w
    end.
  Definition width_domain (w : nat) (s : tarjan_state) : Prop :=
    Forall (fun v => Pos.size_nat v <= w) (tarjan_pending s) /\
    Forall (fun v => Pos.size_nat v <= w) (tarjan_frames s) /\
    Pos.size_nat (tarjan_clock s) <= w + 1 /\
    Pos.size_nat (tarjan_next s) <= w + 1 /\
    (forall v i, trie_get v (tarjan_disc s) = Some i -> Pos.size_nat i <= w + 1) /\
    (forall v i, trie_get v (tarjan_low s) = Some i -> Pos.size_nat i <= w + 1).
  Definition inventory (prefix : list event) (s : tarjan_state) : Prop :=
    NoDup (tarjan_pending s ++ concat (tarjan_emitted s)) /\
    Permutation (tarjan_pending s ++ concat (tarjan_emitted s)) (entered prefix) /\
    incl (tarjan_frames s) (tarjan_pending s) /\
    tarjan_clock s = Pos.of_succ_nat (length (entered prefix)) /\
    tarjan_next s = Pos.of_succ_nat (length (tarjan_emitted s)) /\
    (forall v, trie_get v (tarjan_active s) = Some true <-> In v (tarjan_pending s)) /\
    (forall v, (exists i, trie_get v (tarjan_low s) = Some i) <->
      In v (tarjan_pending s)) /\
    (forall v i, trie_get v (tarjan_disc s) = Some i <->
      exists n, nth_error (entered prefix) n = Some v /\ i = Pos.of_succ_nat n).
  Definition emitted_closed (g : digraph) (s : tarjan_state) : Prop :=
    Forall (fun block => block <> [] /\
      (forall u v, In u block -> In v block -> mutually_reachable g u v) /\
      (forall u v, In u block -> edge g u v -> In v (concat (tarjan_emitted s))))
      (tarjan_emitted s).
  Definition invariant g prefix s : Prop :=
    s = prefix_state prefix /\ inventory prefix s /\
    width_domain (graph_width (base g)) s /\ emitted_closed (base g) s.

  Lemma F1_trace : forall g, wf_graph (base g) ->
    NoDup (entered (tarjan_trace g)) /\
    (forall v, In v (entered (tarjan_trace g)) <-> In v (nodes g)) /\
    trace_stack [] (tarjan_trace g) [] /\
    length (tarjan_trace g) = 2 * graph_n (base g) + graph_e (base g).
  Proof.
    intros g Hwf. split; [apply scc_trace_unique|].
    split; [apply scc_trace_entered|].
    split; [apply scc_trace_nested|now apply scc_trace_size_exact].
  Qed.

  (** The filtered traversal is nested, duplicate-free and graph-sized on every input. *)
  Lemma F1b_trace_size : forall g,
    NoDup (entered (tarjan_trace g)) /\
    (forall v, In v (entered (tarjan_trace g)) -> In v (nodes g)) /\
    trace_stack [] (tarjan_trace g) [] /\
    length (tarjan_trace g) <= 2 * graph_n (base g) + graph_e (base g).
  Proof.
    intros g. split; [apply scc_trace_unique|]. split.
    - intros v Hin. now apply scc_trace_entered in Hin.
    - split; [apply scc_trace_nested|apply scc_trace_size].
  Qed.

  Lemma F2_run : forall g,
    run g = let result := prefix_state (tarjan_trace g) in
      Scc (tarjan_owners result) (rev (tarjan_emitted result)).
  Proof.
    intros g. unfold run, prefix_state, tarjan_trace.
    rewrite rev_append_rev, app_nil_r. reflexivity.
  Qed.

  Lemma F3_initial : forall g,
    invariant g [] tarjan_initial /\
    potential (graph_width (base g)) tarjan_initial = 0%N.
  Proof.
    intros g. split.
    - unfold invariant. split; [reflexivity|]. split.
      + unfold inventory, tarjan_initial. cbn.
        split; [constructor|]. split; [constructor|].
        split; [intros v Hfalse; contradiction|].
        split; [reflexivity|]. split; [reflexivity|]. split.
        * intros v. rewrite PTrie.get_empty. cbn. split; [discriminate|contradiction].
        * split.
          -- intros v. rewrite PTrie.get_empty. cbn. split.
             ++ intros [i Hfalse]. discriminate Hfalse.
             ++ contradiction.
          -- intros v i. rewrite PTrie.get_empty. split; [discriminate|].
             intros [n [Hnth Hi]]. destruct n; discriminate Hnth.
      + split.
        * unfold width_domain, tarjan_initial. cbn.
          split; [constructor|]. split; [constructor|].
          split; [lia|]. split; [lia|]. split;
            intros v i Hlookup; rewrite PTrie.get_empty in Hlookup; discriminate Hlookup.
        * unfold emitted_closed, tarjan_initial. constructor.
    - change ((pop_unit (graph_width (base g)) * 0 + k_result * 0)%N = 0%N).
      now rewrite !N.mul_0_r.
  Qed.

  Lemma F4_prefix : forall g prefix suffix,
    wf_graph (base g) -> tarjan_trace g = prefix ++ suffix ->
    invariant g prefix (prefix_state prefix).
  Proof. Admitted. (* STUB *)

  (** Actual prefixes keep the inventory and widths that the cost proof reads. *)
  Lemma F4b_prefix_cost : forall g prefix suffix,
    tarjan_trace g = prefix ++ suffix ->
    inventory prefix (prefix_state prefix) /\
    width_domain (graph_width (base g)) (prefix_state prefix).
  Proof. Admitted. (* STUB *)

  Lemma F5_pop : forall root index pending low active owners members tail low' active' owners',
    tarjan_pop root index pending low active owners =
      (members, tail, low', active', owners') ->
    pending = members ++ tail /\
    (forall v, In v members -> trie_get v low' = None /\
      trie_get v active' = None /\ trie_get v owners' = Some index).
  Proof.
    intros root index pending low active owners members tail low' active' owners' Hpop.
    unfold tarjan_pop in Hpop.
    destruct (tarjan_pop_lookup _ _ _ _ _ _ _ _ _ _ _ Hpop) as [Hprefix Hlookup].
    split; [exact Hprefix|]. intros v Hin. specialize (Hlookup v).
    assert (Hmember : existsb (Pos.eqb v) members = true).
    { apply existsb_exists. exists v. split; [exact Hin|apply Pos.eqb_refl]. }
    now rewrite Hmember in Hlookup.
  Qed.

  Lemma F6_final : forall g, wf_graph (base g) ->
    let result := prefix_state (tarjan_trace g) in
    tarjan_pending result = [] /\ tarjan_frames result = [] /\
    forall v i, trie_get v (tarjan_owners result) = Some i <->
      exists block, nth_error (rev (tarjan_emitted result))
        (Nat.pred (Pos.to_nat i)) = Some block /\ In v block.
  Proof. Admitted. (* STUB *)

  Lemma F7_components : forall g, wf_graph (base g) -> forall u v,
    (exists i, trie_get u (comp (run g)) = Some i /\ trie_get v (comp (run g)) = Some i) <->
    In u (nodes g) /\ In v (nodes g) /\ mutually_reachable (base g) u v.
  Proof. Admitted. (* STUB *)

  Lemma T1_pop : forall w root index pending low active owners members tail low' active' owners',
    Forall (fun v => Pos.size_nat v <= w) pending ->
    Pos.size_nat root <= w -> Pos.size_nat index <= w + 1 ->
    tarjan_pop root index pending low active owners = (members, tail, low', active', owners') ->
    (T_tarjan_pop root index pending low active owners + pop_unit w * N.of_nat (length tail) <=
      pop_unit w * N.of_nat (length pending) + k_pop * N.of_nat (w + 1))%N.
  Proof.
    intros w root index pending low active owners members tail low' active' owners'
      Hwidth Hroot Hindex Hpop.
    unfold tarjan_pop in Hpop.
    pose proof (tarjan_pop_credit _ _ _ _ _ _ _ _ _ _ _ _ Hwidth Hpop) as Hcredit.
    unfold pop_unit, k_pop. time_unfold @T_tarjan_pop. nia.
  Qed.

  (** The generic visitor width theorem applies to every actual raw prefix. *)
  Lemma prefix_width : forall g prefix suffix,
    tarjan_trace g = prefix ++ suffix ->
    width_domain (graph_width (base g)) (prefix_state prefix).
  Proof.
    intros g prefix suffix Htrace. unfold width_domain, prefix_state,
      tarjan_enter, tarjan_leave, tarjan_edge, tarjan_initial.
    apply tarjan_fold_width.
    - eapply scc_trace_prefix_unique; exact Htrace.
    - apply Forall_forall. intros v Hin. apply search_entered_member in Hin.
      pose proof (scc_trace_prefix_width g prefix suffix Htrace) as Hwidth.
      rewrite Forall_forall in Hwidth. exact (Hwidth (Enter v) Hin).
  Qed.

  Local Lemma lower_potential w v n s :
    potential w (TarjanVisitor.lower v n s) = potential w s.
  Proof.
    unfold TarjanVisitor.lower. destruct (trie_get v (tarjan_low s)); reflexivity.
  Qed.

  Local Lemma edge_potential w kind u v s :
    potential w (TarjanVisitor.edge kind u v s) = potential w s.
  Proof.
    destruct kind; cbn [TarjanVisitor.edge]; try reflexivity.
    all: destruct (trie_get v (tarjan_active s)) as [[|]|]; try reflexivity.
    all: destruct (trie_get v (tarjan_disc s)); try reflexivity.
    all: apply lower_potential.
  Qed.

  (** Lowering charges the key lookup and update and the old value's comparison width. *)
  Local Lemma lower_clock w v n s : Pos.size_nat v <= w ->
    (forall u i, trie_get u (tarjan_low s) = Some i -> Pos.size_nat i <= w + 1) ->
    (TarjanVisitor.T_lower v n s <= 4096 * N.of_nat (w + 1))%N.
  Proof.
    intros Hv Hvalues. time_unfold @TarjanVisitor.T_lower. time_simpl.
    rewrite PTrieT.trie_get_clock.
    destruct (trie_get v (tarjan_low s)) as [old|] eqn:Hlookup; [|lia].
    pose proof (Hvalues v old Hlookup) as Hold.
    pose proof (PTrieT.T_set_le positive v (Pos.min old n) (tarjan_low s)) as Hset.
    change (PTrieCode.T_set v (Pos.min old n) (tarjan_low s) <=
      1024 * N.of_nat (Pos.size_nat v + 1))%N in Hset.
    pose proof (Std.Pos.T_compare_le old n) as Hcompare.
    time_unfold @Pos.T_min. time_simpl. nia.
  Qed.

  Local Lemma enter_credit w v s : width_domain w s -> Pos.size_nat v <= w ->
    (TarjanVisitor.T_enter v s + potential w (TarjanVisitor.enter v s) <=
      16384 * N.of_nat (w + 1) + potential w s)%N.
  Proof.
    intros [_ [_ [Hclock _]]] Hv.
    pose proof (PTrieT.T_set_le positive v (tarjan_clock s) (tarjan_disc s)) as Hdisc.
    pose proof (PTrieT.T_set_le positive v (tarjan_clock s) (tarjan_low s)) as Hlow.
    pose proof (PTrieT.T_set_le bool v true (tarjan_active s)) as Hactive.
    change (PTrieCode.T_set v (tarjan_clock s) (tarjan_disc s) <=
      1024 * N.of_nat (Pos.size_nat v + 1))%N in Hdisc.
    change (PTrieCode.T_set v (tarjan_clock s) (tarjan_low s) <=
      1024 * N.of_nat (Pos.size_nat v + 1))%N in Hlow.
    change (PTrieCode.T_set v true (tarjan_active s) <=
      1024 * N.of_nat (Pos.size_nat v + 1))%N in Hactive.
    pose proof (Std.Pos.T_succ_le (tarjan_clock s)) as Hsucc.
    time_unfold @TarjanVisitor.T_enter. time_simpl.
    unfold potential, pop_unit, k_pop, k_result.
    cbn [TarjanVisitor.enter tarjan_pending tarjan_emitted length].
    rewrite Nat2N.inj_succ. nia.
  Qed.

  Local Lemma edge_clock w kind u v s : width_domain w s ->
    Pos.size_nat u <= w -> Pos.size_nat v <= w ->
    (TarjanVisitor.T_edge kind u v s <= 16384 * N.of_nat (w + 1))%N.
  Proof.
    intros [_ [_ [_ [_ [_ Hvalues]]]]] Hu Hv.
    time_unfold @TarjanVisitor.T_edge. time_simpl.
    destruct kind; [lia| |].
    all: rewrite PTrieT.trie_get_clock;
      destruct (trie_get v (tarjan_active s)) as [[|]|]; try lia.
    all: rewrite PTrieT.trie_get_clock;
      destruct (trie_get v (tarjan_disc s)) as [n|]; try lia.
    all: pose proof (lower_clock w u n s Hu Hvalues); lia.
  Qed.

  Local Lemma leave_credit w v s : width_domain w s -> Pos.size_nat v <= w ->
    (TarjanVisitor.T_leave v s + potential w (TarjanVisitor.leave v s) <=
      16384 * N.of_nat (w + 1) + potential w s)%N.
  Proof.
    intros [Hpending [Hframes [Hclock [Hnext [Hdisc Hlow]]]]] Hv.
    time_unfold @TarjanVisitor.T_leave. time_simpl. unfold TarjanVisitor.leave.
    rewrite PTrieT.trie_get_clock.
    destruct (trie_get v (tarjan_low s)) as [low|] eqn:Hlookup.
    2: { unfold potential. cbn [tarjan_pending tarjan_emitted]. lia. }
    pose proof (Hlow v low Hlookup) as Hlow_width.
    rewrite PTrieT.trie_get_clock.
    destruct (trie_get v (tarjan_disc s)) as [disc|] eqn:Hdiscovery.
    2: { unfold potential. cbn [tarjan_pending tarjan_emitted]. lia. }
    pose proof (Std.Pos.T_eqb_le low disc) as Hequal.
    destruct (Pos.eqb low disc) eqn:Hroot.
    - destruct (tarjan_pop v (tarjan_next s) (tarjan_pending s) (tarjan_low s)
        (tarjan_active s) (tarjan_owners s))
        as [[[[members tail] lows] actives] owners] eqn:Hpop.
      unfold tarjan_pop in Hpop.
      pose proof (tarjan_pop_credit _ _ _ _ _ _ _ _ _ _ _ _ Hpending Hpop) as Hpop_cost.
      pose proof (Std.Pos.T_succ_le (tarjan_next s)) as Hsucc.
      unfold potential, pop_unit, k_pop, k_result.
      rewrite Hpop. cbn [tarjan_pending tarjan_emitted length].
      rewrite Nat2N.inj_succ. nia.
    - destruct (tarjan_frames s) as [|frame frames] eqn:Hstack.
      + unfold potential. cbn [tarjan_pending tarjan_emitted]. lia.
      + destruct frames as [|parent frames].
        * unfold potential. cbn [tarjan_pending tarjan_emitted]. lia.
        * assert (Hparent : Pos.size_nat parent <= w).
          { inversion Hframes as [|frame' tail Hframe Htail]; subst frame' tail.
            now inversion Htail. }
          pose proof (lower_clock w parent low
            (TarjanState (tarjan_disc s) (tarjan_low s) (tarjan_pending s)
              (tarjan_active s) (parent :: frames) (tarjan_emitted s)
              (tarjan_owners s) (tarjan_clock s) (tarjan_next s)) Hparent Hlow) as Hlower.
          rewrite lower_potential. unfold potential. cbn [tarjan_pending tarjan_emitted]. lia.
  Qed.

  (** A callback leaves a strict constant margin for the event-fold driver. *)
  Lemma callback_credit w e s : width_domain w s -> event_domain w e ->
    (callback_cost e s + potential w (apply_event s e) <=
      32768 * N.of_nat (w + 1) + potential w s)%N.
  Proof.
    intros Hwidth Hevent. destruct e as [v|v|kind u v];
      cbn [callback_cost apply_event visit_event event_domain] in *.
    - pose proof (enter_credit w v s Hwidth Hevent) as Hcredit.
      time_unfold @T_tarjan_enter. unfold tarjan_enter. lia.
    - pose proof (leave_credit w v s Hwidth Hevent) as Hcredit.
      time_unfold @T_tarjan_leave. unfold tarjan_leave. lia.
    - destruct Hevent as [Hu Hv]. pose proof (edge_clock w kind u v s Hwidth Hu Hv) as Hcost.
      time_unfold @T_tarjan_edge. unfold tarjan_edge. rewrite edge_potential. lia.
  Qed.


  Lemma T2_callback : forall g prefix e suffix,
    tarjan_trace g = prefix ++ e :: suffix ->
    let w := graph_width (base g) in
    let s := prefix_state prefix in
    (callback_cost e s + potential w (apply_event s e) <=
      k_callback * N.of_nat (w + 1) + potential w s)%N.
  Proof. Admitted. (* STUB *)

  Lemma T3_fold : forall g,
    (T_fold_events tarjan_enter T_tarjan_enter tarjan_leave T_tarjan_leave
      tarjan_edge T_tarjan_edge (tarjan_trace g) tarjan_initial +
      potential (graph_width (base g)) (prefix_state (tarjan_trace g)) <=
    k_callback * N.of_nat (length (tarjan_trace g) + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T4_trace : forall g,
    (T_tarjan_trace g <= k_search * N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
  Proof. Admitted. (* STUB *)

  Local Opaque scc_trace prepared_search_trace.

  Local Lemma fold_left_clock_mono {A B} (f : A -> B -> A) first second es s :
    (forall state e, first state e <= second state e)%N ->
    (List.T_fold_left f first es s <= List.T_fold_left f second es s)%N.
  Proof.
    intros Hcost. revert s. induction es as [|e es IH]; intros s;
      time_unfold @List.T_fold_left.
    - lia.
    - specialize (IH (f s e)). specialize (Hcost s e). lia.
  Qed.

  Local Lemma fold_events_alias_time es s :
    (T_fold_events TarjanVisitor.enter (fun v s => TarjanVisitor.T_enter v s)
      TarjanVisitor.leave (fun v s => TarjanVisitor.T_leave v s)
      TarjanVisitor.edge (fun kind u v s => TarjanVisitor.T_edge kind u v s) es s <=
    T_fold_events tarjan_enter T_tarjan_enter tarjan_leave T_tarjan_leave
      tarjan_edge T_tarjan_edge es s)%N.
  Proof.
    time_unfold @T_fold_events. apply N.add_le_mono_l.
    apply fold_left_clock_mono. intros state e. destruct e;
      time_unfold @T_visit_event;
      try time_unfold @T_tarjan_enter; try time_unfold @T_tarjan_leave;
      try time_unfold @T_tarjan_edge; lia.
  Qed.

  Lemma T5_wrapper : forall g,
    (T_run g <= k_result * (T_tarjan_trace g +
      T_fold_events tarjan_enter T_tarjan_enter tarjan_leave T_tarjan_leave
        tarjan_edge T_tarjan_edge (tarjan_trace g) tarjan_initial +
      N.of_nat (length (tarjan_emitted (prefix_state (tarjan_trace g)))) + 1))%N.
  Proof.
    intros g.
    pose proof (List.T_rev_append_le
      (tarjan_emitted (prefix_state (tarjan_trace g))) []) as Hreverse.
    pose proof (fold_events_alias_time (tarjan_trace g) tarjan_initial) as Hfold.
    unfold prefix_state, tarjan_trace, tarjan_enter, tarjan_leave, tarjan_edge,
      tarjan_initial in *.
    unfold k_result. time_unfold @T_run. time_unfold @T_tarjan_trace.
    time_unfold @T_tarjan_owners. time_unfold @T_tarjan_emitted. time_cbn.
    set (events := scc_trace g) in *. clearbody events. nia.
  Qed.

  Lemma T6_public : forall g,
    (T_run g <= c_scc * N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
  Proof. Admitted. (* STUB *)
End SccT.
