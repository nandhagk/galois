(** * Strongly connected components

    Tarjan's visitor tracks discovery numbers and pending components.
    For example, closing a cycle root emits its pending vertices together.
    Builds on: depth-first search and the SCC signature. *)

From Stdlib Require Import List NArith PArith Arith Lia Sorting.Permutation.
From Argent Require Import Time Tactics Std BigO.
From Galois.Base Require Import Trie.
From Galois.Graph Require Import Data Spec DigraphSig Digraph SearchSig Search SccSig.
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


(** Frame order is retained inside the pending stack until each matching leave. *)
Inductive tarjan_embeds : list positive -> list positive -> Prop :=
  | tarjan_embeds_nil : forall ys, tarjan_embeds [] ys
  | tarjan_embeds_skip : forall x xs ys,
      tarjan_embeds xs ys -> tarjan_embeds xs (x :: ys)
  | tarjan_embeds_take : forall x xs ys,
      tarjan_embeds xs ys -> tarjan_embeds (x :: xs) (x :: ys).

Lemma tarjan_embeds_drop x xs ys :
  tarjan_embeds (x :: xs) ys -> tarjan_embeds xs ys.
Proof.
  intro Hembed. remember (x :: xs) as front eqn:Hfront.
  induction Hembed; inversion Hfront; subst; eauto using tarjan_embeds.
Qed.

Lemma tarjan_embeds_cons_inv x xs y ys :
  tarjan_embeds (x :: xs) (y :: ys) ->
  (x = y /\ tarjan_embeds xs ys) \/ tarjan_embeds (x :: xs) ys.
Proof.
  intro Hembed. inversion Hembed; subst; auto.
Qed.

Lemma tarjan_embeds_incl xs ys : tarjan_embeds xs ys -> incl xs ys.
Proof.
  intro Hembed. induction Hembed; intros v Hin; cbn [In] in *.
  - contradiction.
  - right. now apply IHHembed.
  - destruct Hin as [Heq|Hin]; [now left|right; now apply IHHembed].
Qed.

(** Removing a prefix through the current frame retains all older embedded frames. *)
Lemma tarjan_embeds_pop root index pending low active owners
    members tail low' active' owners' frames :
  tarjan_embeds (root :: frames) pending ->
  tarjan_pop root index pending low active owners = (members, tail, low', active', owners') ->
  tarjan_embeds frames tail.
Proof.
  revert low active owners members tail low' active' owners'.
  induction pending as [|v pending IH];
    intros low active owners members tail low' active' owners' Hembed Hpop.
  - inversion Hembed.
  - cbn [tarjan_pop] in Hpop. destruct (Pos.eqb v root) eqn:Heq.
    + apply Pos.eqb_eq in Heq. subst v.
      assert (Htail : tarjan_embeds frames pending).
      { destruct (tarjan_embeds_cons_inv root frames root pending Hembed)
          as [[_ Hinside]|Hinside]; [exact Hinside|now apply tarjan_embeds_drop in Hinside]. }
      inversion Hpop; subst. exact Htail.
    + destruct (tarjan_embeds_cons_inv root frames v pending Hembed)
        as [[Hequal _]|Htail].
      { subst v. rewrite Pos.eqb_refl in Heq. discriminate. }
      destruct (tarjan_pop root index pending (PTrieCode.remove v low)
        (PTrieCode.remove v active) (PTrieCode.set v index owners))
        as [[[[taken remaining] lows] actives] owned] eqn:Hrest.
      inversion Hpop; subst. eapply IH; eassumption.
Qed.

Definition tarjan_frames_embedded s : Prop :=
  tarjan_embeds (tarjan_frames s) (tarjan_pending s).

Lemma tarjan_embeds_enter v s :
  tarjan_frames_embedded s -> tarjan_frames_embedded (TarjanVisitor.enter v s).
Proof.
  intro Hembed. unfold tarjan_frames_embedded in *.
  cbn [TarjanVisitor.enter tarjan_frames tarjan_pending]. now constructor.
Qed.

Lemma tarjan_embeds_lower v n s :
  tarjan_frames_embedded s -> tarjan_frames_embedded (TarjanVisitor.lower v n s).
Proof.
  intro Hembed. unfold TarjanVisitor.lower.
  destruct (trie_get v (tarjan_low s)); exact Hembed.
Qed.

Lemma tarjan_embeds_edge kind u v s :
  tarjan_frames_embedded s -> tarjan_frames_embedded (TarjanVisitor.edge kind u v s).
Proof.
  intro Hembed. destruct kind; cbn [TarjanVisitor.edge]; try exact Hembed.
  all: destruct (trie_get v (tarjan_active s)) as [[|]|]; try exact Hembed.
  all: destruct (trie_get v (tarjan_disc s)); try exact Hembed.
  all: now apply tarjan_embeds_lower.
Qed.

Lemma tarjan_embeds_leave v frames s :
  tarjan_frames s = v :: frames -> tarjan_frames_embedded s ->
  tarjan_frames_embedded (TarjanVisitor.leave v s).
Proof.
  intros Hframes Hembed.
  assert (Htail : tarjan_embeds frames (tarjan_pending s)).
  { unfold tarjan_frames_embedded in Hembed. rewrite Hframes in Hembed.
    now apply tarjan_embeds_drop in Hembed. }
  unfold TarjanVisitor.leave. rewrite Hframes. cbn beta iota zeta.
  destruct (trie_get v (tarjan_low s)) as [low|]; [|exact Htail].
  destruct (trie_get v (tarjan_disc s)) as [disc|]; [|exact Htail].
  destruct (Pos.eqb low disc).
  - destruct (tarjan_pop v (tarjan_next s) (tarjan_pending s) (tarjan_low s)
      (tarjan_active s) (tarjan_owners s))
      as [[[[members remaining] lows] actives] owners] eqn:Hpop.
    unfold tarjan_frames_embedded. cbn [tarjan_frames tarjan_pending].
    eapply tarjan_embeds_pop; [|exact Hpop].
    unfold tarjan_frames_embedded in Hembed. now rewrite Hframes in Hembed.
  - destruct frames as [|parent frames]; [exact Htail|].
    apply tarjan_embeds_lower. exact Htail.
Qed.

(** A nested trace preserves the ordered embedding and records its final frame stack. *)
Lemma tarjan_embeds_fold initial es final : trace_stack initial es final ->
  forall s, tarjan_frames s = initial -> tarjan_frames_embedded s ->
  let result := fold_events TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge es s in
  tarjan_frames result = final /\ tarjan_frames_embedded result.
Proof.
  intro Hstack. induction Hstack; intros s Hframes Hembed; cbn zeta.
  - cbn [fold_events fold_left]. auto.
  - unfold fold_events at 1. cbn [fold_left visit_event].
    apply IHHstack.
    + cbn [TarjanVisitor.enter tarjan_frames]. now rewrite Hframes.
    + now apply tarjan_embeds_enter.
  - unfold fold_events at 1. cbn [fold_left visit_event].
    apply IHHstack.
    + pose proof (proj2 (proj2 (tarjan_event_metadata (Leave v) s))) as Hstep.
      cbn [visit_event] in Hstep. rewrite Hstep, Hframes. reflexivity.
    + eapply tarjan_embeds_leave; eassumption.
  - unfold fold_events at 1. cbn [fold_left visit_event].
    apply IHHstack.
    + pose proof (proj2 (proj2 (tarjan_event_metadata (Edge kind u v) s))) as Hstep.
      cbn [visit_event] in Hstep. now rewrite Hstep.
    + now apply tarjan_embeds_edge.
Qed.

Lemma tarjan_stack_prefix initial prefix suffix final :
  trace_stack initial (prefix ++ suffix) final ->
  exists middle, trace_stack initial prefix middle /\ trace_stack middle suffix final.
Proof.
  revert initial. induction prefix as [|e prefix IH]; intros initial Hstack.
  - exists initial. split; [constructor|exact Hstack].
  - destruct e as [v|v|kind u v]; cbn [app] in Hstack; inversion Hstack; subst;
      match goal with H : trace_stack _ (prefix ++ suffix) _ |- _ =>
        destruct (IH _ H) as [middle [Hprefix Hsuffix]]
      end; exists middle; split; try exact Hsuffix.
    + now apply stack_enter.
    + now apply stack_leave.
    + now apply stack_edge.
Qed.

(** Only an entering callback changes the discovery table. *)
Lemma tarjan_inventory_disc_lower v n s :
  tarjan_disc (TarjanVisitor.lower v n s) = tarjan_disc s.
Proof.
  unfold TarjanVisitor.lower. destruct (trie_get v (tarjan_low s)); reflexivity.
Qed.

Lemma tarjan_inventory_disc_event e s :
  tarjan_disc (visit_event TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge s e) =
    match e with Enter v => PTrieCode.set v (tarjan_clock s) (tarjan_disc s)
    | _ => tarjan_disc s end.
Proof.
  destruct e as [v|v|kind u v]; cbn [visit_event].
  - reflexivity.
  - unfold TarjanVisitor.leave.
    destruct (trie_get v (tarjan_low s)); [|reflexivity].
    destruct (trie_get v (tarjan_disc s)); [|reflexivity].
    destruct (Pos.eqb p p0).
    + destruct (tarjan_pop v (tarjan_next s) (tarjan_pending s) (tarjan_low s)
        (tarjan_active s) (tarjan_owners s)) as [[[[members tail] lows] active] owners].
      reflexivity.
    + destruct (match tarjan_frames s with [] => [] | _ :: rest => rest end);
        [reflexivity|rewrite tarjan_inventory_disc_lower; reflexivity].
  - destruct kind; cbn [TarjanVisitor.edge]; try reflexivity.
    all: destruct (trie_get v (tarjan_active s)) as [[|]|]; try reflexivity.
    all: destruct (trie_get v (tarjan_disc s)); try reflexivity.
    all: apply tarjan_inventory_disc_lower.
Qed.

Definition tarjan_discovery_rows vs (disc : ptrie positive) : Prop :=
  forall v i, trie_get v disc = Some i <->
    exists n, nth_error vs n = Some v /\ i = Pos.of_succ_nat n.

Lemma tarjan_discovery_append vs disc next v :
  ~ In v vs -> tarjan_discovery_rows vs disc -> next = Pos.of_succ_nat (length vs) ->
  tarjan_discovery_rows (vs ++ [v]) (PTrieCode.set v next disc).
Proof.
  intros Hfresh Hrows Hnext u i. destruct (Pos.eq_dec u v) as [Heq|Hne].
  - subst u. rewrite PTrie.get_set_same. split.
    + intro Hget. injection Hget as Hi. subst i.
      exists (length vs). split; [|exact Hnext].
      rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
    + intros [n [Hnth Hi]].
      assert (Heq : n = length vs).
      { destruct (lt_dec n (length vs)) as [Hlt|Hge].
        - rewrite nth_error_app1 in Hnth by exact Hlt.
          exfalso. apply Hfresh. eapply nth_error_In; exact Hnth.
        - rewrite nth_error_app2 in Hnth by lia.
          destruct (n - length vs) as [|k] eqn:Hminus; [lia|].
          cbn [nth_error] in Hnth. rewrite nth_error_nil in Hnth. discriminate. }
      subst n. congruence.
  - rewrite PTrie.get_set_other by exact Hne. rewrite (Hrows u i). split.
    + intros [n [Hnth Hi]]. exists n. split; [|exact Hi].
      rewrite nth_error_app1; [exact Hnth|].
      apply nth_error_Some. now rewrite Hnth.
    + intros [n [Hnth Hi]].
      destruct (lt_dec n (length vs)) as [Hlt|Hge].
      * exists n. split; [|exact Hi]. now rewrite nth_error_app1 in Hnth.
      * rewrite nth_error_app2 in Hnth by lia.
        destruct (n - length vs) as [|k] eqn:Hminus.
        -- cbn [nth_error] in Hnth. injection Hnth as Heq.
           exfalso. apply Hne. now symmetry.
        -- cbn [nth_error] in Hnth. rewrite nth_error_nil in Hnth. discriminate.
Qed.

(** Discovery numbers are exactly the one-based positions of unique entering events. *)
Lemma tarjan_discovery_rows_fold es : NoDup (entered es) ->
  tarjan_discovery_rows (entered es)
    (tarjan_disc (fold_events TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge
      es tarjan_initial)).
Proof.
  induction es as [|e es IH] using rev_ind; intro Hunique.
  - intros v i. cbn [fold_events fold_left entered tarjan_initial tarjan_disc].
    rewrite PTrie.get_empty. split; [discriminate|].
    intros [n [Hnth _]]. rewrite nth_error_nil in Hnth. discriminate.
  - assert (Hprefix : NoDup (entered es)).
    { rewrite search_entered_app in Hunique. now apply NoDup_app_remove_r in Hunique. }
    specialize (IH Hprefix).
    unfold fold_events at 1. rewrite fold_left_app.
    change (tarjan_discovery_rows (entered (es ++ [e]))
      (tarjan_disc (visit_event TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge
        (fold_events TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge
          es tarjan_initial) e))).
    rewrite tarjan_inventory_disc_event, search_entered_app.
    destruct e as [v|v|kind u v]; cbn [entered];
      try (rewrite app_nil_r; exact IH).
    apply tarjan_discovery_append; [|exact IH|].
    + rewrite search_entered_app in Hunique. cbn [entered] in Hunique.
      apply NoDup_rev in Hunique. rewrite rev_app_distr in Hunique.
      cbn [rev app] in Hunique. apply NoDup_cons_iff in Hunique.
      destruct Hunique as [Hfresh Hrest].
      intro Hin. apply Hfresh. now apply (proj1 (in_rev (entered es) v)).
    + apply Pos2Nat.inj. rewrite SuccNat2Pos.id_succ. apply tarjan_clock_count.
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

Lemma tarjan_prefix_frames g prefix suffix : scc_trace g = prefix ++ suffix ->
  incl (tarjan_frames (fold_events TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge
    prefix tarjan_initial))
    (tarjan_pending (fold_events TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge
      prefix tarjan_initial)).
Proof.
  intro Hprefix. pose proof (scc_trace_nested g) as Hnested. rewrite Hprefix in Hnested.
  destruct (tarjan_stack_prefix [] prefix suffix [] Hnested) as [middle [Hstack _]].
  destruct (tarjan_embeds_fold [] prefix middle Hstack tarjan_initial eq_refl
    (tarjan_embeds_nil [])) as [_ Hembed].
  now apply tarjan_embeds_incl.
Qed.

(** Owner bindings identify the chronological position of their emitted component. *)
Definition tarjan_owners_indexed (s : tarjan_state) : Prop :=
  forall v i, trie_get v (tarjan_owners s) = Some i <->
    exists block, nth_error (rev (tarjan_emitted s)) (Nat.pred (Pos.to_nat i)) = Some block /\
      In v block.

(** Appending a block adds exactly its next one-based output position. *)
Local Lemma tarjan_append_position (blocks : list (list positive)) next v i members :
  Pos.to_nat next = S (length blocks) ->
  ((exists block, nth_error (blocks ++ [members]) (Nat.pred (Pos.to_nat i)) = Some block /\
      In v block) <->
    (i = next /\ In v members) \/
    exists block, nth_error blocks (Nat.pred (Pos.to_nat i)) = Some block /\ In v block).
Proof.
  intro Hnext. set (n := Nat.pred (Pos.to_nat i)).
  assert (Hi : Pos.to_nat i = S n) by (unfold n; pose proof (Pos2Nat.is_pos i); lia).
  destruct (lt_dec n (length blocks)) as [Hlt|Hge].
  - rewrite nth_error_app1 by exact Hlt. split; [auto|].
    intros [[Heq _]|Hmember]; [subst i; lia|exact Hmember].
  - rewrite nth_error_app2 by lia.
    destruct (n - length blocks) as [|k] eqn:Hminus.
    + assert (Heq : i = next) by (apply Pos2Nat.inj; lia).
      cbn [nth_error]. split.
      * intros [block [Hblock Hin]]. inversion Hblock; subst block. now left.
      * intros [[_ Hin]|[block [Hnth _]]].
        -- exists members. auto.
        -- assert (Hlt : n < length blocks) by
             (apply nth_error_Some; rewrite Hnth; discriminate). lia.
    + cbn [nth_error]. rewrite nth_error_nil. split.
      * intros [block [Hfalse _]]. discriminate.
      * intros [[Heq _]|[block [Hnth _]]].
        -- subst i. lia.
        -- assert (Hlt : n < length blocks) by
             (apply nth_error_Some; rewrite Hnth; discriminate). lia.
Qed.

(** Duplicate freedom separates pending vertices from previously emitted vertices. *)
Local Lemma tarjan_nodup_disjoint {A} (first last : list A) :
  NoDup (first ++ last) -> forall v, In v first -> ~ In v last.
Proof.
  intro Hunique. induction first as [|u first IH]; intros v Hin; [contradiction|].
  inversion Hunique as [|u0 rest Hnot Htail]; subst u0 rest.
  destruct Hin as [Heq|Hin].
  - subst u. intro Hlast. apply Hnot. apply in_or_app. now right.
  - now apply IH.
Qed.

(** A popped prefix receives the new index without overwriting any emitted component. *)
Local Lemma tarjan_pop_owners_indexed root s members tail low active owners :
  NoDup (tarjan_bag s) ->
  Pos.to_nat (tarjan_next s) = S (length (tarjan_emitted s)) ->
  tarjan_owners_indexed s ->
  tarjan_pop root (tarjan_next s) (tarjan_pending s) (tarjan_low s)
    (tarjan_active s) (tarjan_owners s) = (members, tail, low, active, owners) ->
  forall v i, trie_get v owners = Some i <->
    exists block, nth_error (rev (members :: tarjan_emitted s))
      (Nat.pred (Pos.to_nat i)) = Some block /\ In v block.
Proof.
  intros Hunique Hnext Hindex Hpop v i.
  destruct (tarjan_pop_lookup _ _ _ _ _ _ _ _ _ _ _ Hpop) as [Hsplit Hlookup].
  assert (Hfresh : forall x, In x members -> ~ In x (concat (tarjan_emitted s))).
  { intros x Hin. apply (tarjan_nodup_disjoint _ _ Hunique x).
    rewrite Hsplit. apply in_or_app. now left. }
  destruct (Hlookup v) as [_ [_ Howners]]. cbn [rev].
  rewrite (tarjan_append_position (rev (tarjan_emitted s)) (tarjan_next s))
    by (rewrite length_rev; exact Hnext).
  rewrite Howners. destruct (existsb (Pos.eqb v) members) eqn:Hmember.
  - apply existsb_exists in Hmember. destruct Hmember as [x [Hin Heq]].
    apply Pos.eqb_eq in Heq. subst x. split.
    + intro Heq. injection Heq as Heq. subst i. now left.
    + intros [[Heq _]|[block [Hnth Hv]]]; [subst i; reflexivity|].
      exfalso. apply (Hfresh v Hin). apply in_concat. exists block. split; [|exact Hv].
      apply (proj2 (in_rev _ _)). now apply nth_error_In in Hnth.
  - rewrite (Hindex v i). split; [now right|].
    intros [[_ Hin]|Hold]; [|exact Hold].
    assert (Hyes : existsb (Pos.eqb v) members = true).
    { apply existsb_exists. exists v. split; [exact Hin|apply Pos.eqb_refl]. }
    congruence.
Qed.

(** Lowering a link leaves every owner and emitted block unchanged. *)
Local Lemma tarjan_owners_lower v n s :
  tarjan_owners_indexed s -> tarjan_owners_indexed (TarjanVisitor.lower v n s).
Proof.
  intro Hindex. unfold TarjanVisitor.lower.
  destruct (trie_get v (tarjan_low s)); exact Hindex.
Qed.

Local Lemma tarjan_owners_edge kind u v s :
  tarjan_owners_indexed s -> tarjan_owners_indexed (TarjanVisitor.edge kind u v s).
Proof.
  intro Hindex. destruct kind; cbn [TarjanVisitor.edge]; try exact Hindex.
  all: destruct (trie_get v (tarjan_active s)) as [[|]|]; try exact Hindex.
  all: destruct (trie_get v (tarjan_disc s)); try exact Hindex.
  all: now apply tarjan_owners_lower.
Qed.

(** Leaving either retains the owner relation or appends the newly popped component. *)
Local Lemma tarjan_owners_leave v s :
  NoDup (tarjan_bag s) ->
  Pos.to_nat (tarjan_next s) = S (length (tarjan_emitted s)) ->
  tarjan_owners_indexed s -> tarjan_owners_indexed (TarjanVisitor.leave v s).
Proof.
  intros Hunique Hnext Hindex. unfold TarjanVisitor.leave.
  destruct (trie_get v (tarjan_low s)) as [low|]; [|exact Hindex].
  destruct (trie_get v (tarjan_disc s)) as [disc|]; [|exact Hindex].
  destruct (Pos.eqb low disc).
  - destruct (tarjan_pop v (tarjan_next s) (tarjan_pending s) (tarjan_low s)
      (tarjan_active s) (tarjan_owners s))
      as [[[[members tail] lows] actives] owners] eqn:Hpop.
    unfold tarjan_owners_indexed. cbn [tarjan_owners tarjan_emitted].
    eapply tarjan_pop_owners_indexed; eassumption.
  - destruct (match tarjan_frames s with [] => [] | _ :: rest => rest end).
    + exact Hindex.
    + apply tarjan_owners_lower. exact Hindex.
Qed.

Local Lemma tarjan_owners_event e s :
  NoDup (tarjan_bag s) ->
  Pos.to_nat (tarjan_next s) = S (length (tarjan_emitted s)) ->
  tarjan_owners_indexed s ->
  tarjan_owners_indexed
    (visit_event TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge s e).
Proof.
  intros Hunique Hnext Hindex. destruct e; cbn [visit_event].
  - exact Hindex.
  - now apply tarjan_owners_leave.
  - now apply tarjan_owners_edge.
Qed.

(** Unique entries make every emitted owner agree with its chronological block index. *)
Lemma tarjan_owners_indexed_fold es : NoDup (entered es) ->
  tarjan_owners_indexed
    (fold_events TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge es tarjan_initial).
Proof.
  induction es as [|e es IH] using rev_ind; intro Hunique.
  - unfold tarjan_owners_indexed. intros v i.
    cbn [fold_events fold_left tarjan_initial tarjan_owners tarjan_emitted rev].
    rewrite PTrie.get_empty. split; [discriminate|].
    intros [block [Hnth _]]. rewrite nth_error_nil in Hnth. discriminate.
  - assert (Hprefix : NoDup (entered es)).
    { rewrite search_entered_app in Hunique. now apply NoDup_app_remove_r in Hunique. }
    specialize (IH Hprefix).
    pose proof (Permutation_NoDup (Permutation_sym (tarjan_bag_inventory es)) Hprefix) as Hbag.
    unfold fold_events at 1. rewrite fold_left_app.
    change (tarjan_owners_indexed
      (visit_event TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge
        (fold_events TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge
          es tarjan_initial) e)).
    apply tarjan_owners_event; [exact Hbag|apply tarjan_next_count|exact IH].
Qed.

(** Every present owner fits the width of the distinct entered keys plus one bit. *)
Lemma tarjan_owner_width w es v i :
  NoDup (entered es) -> Forall (fun u => Pos.size_nat u <= w) (entered es) ->
  trie_get v (tarjan_owners
    (fold_events TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge es tarjan_initial)) =
    Some i -> Pos.size_nat i <= w + 1.
Proof.
  intros Hunique Hwidth Howner.
  apply (tarjan_owners_indexed_fold es Hunique v i) in Howner.
  destruct Howner as [block [Hnth Hin]].
  pose proof (tarjan_emitted_count es) as Hcount.
  assert (Hposition : Nat.pred (Pos.to_nat i) < length (rev (tarjan_emitted
    (fold_events TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge es tarjan_initial)))).
  { apply nth_error_Some. rewrite Hnth. discriminate. }
  rewrite length_rev in Hposition.
  eapply tarjan_counter_width; [exact Hunique|exact Hwidth|].
  pose proof (Pos2Nat.is_pos i). lia.
Qed.

(** Bounding every key also bounds the fold used to measure an identifier list. *)
Lemma scc_vertex_width_bound w vertices :
  Forall (fun v => Pos.size_nat v <= w) vertices -> vertex_width vertices <= w.
Proof.
  unfold vertex_width. intros Hwidth. induction Hwidth; cbn [fold_right]; [lia|].
  rewrite search_graph_max. apply Nat.max_lub; assumption.
Qed.

(** Every filtered successor key belongs to the bounded input vertex list. *)
Lemma scc_filtered_row_width g v :
  vertex_width (succs (base (scc_graph g)) v) <= graph_width (base g).
Proof.
  apply scc_vertex_width_bound. apply Forall_forall. intros u Hin.
  apply scc_node_width. now apply (scc_graph_closed g v u).
Qed.

(** Filtering preserves vertex occurrences and can only remove edge occurrences. *)
Lemma scc_graph_size g :
  graph_n (base (scc_graph g)) = graph_n (base g) /\
  graph_e (base (scc_graph g)) <= graph_e (base g).
Proof.
  assert (Hnodes : forall h, graph_n (base h) = length (nodes h)).
  { intros [[vertices adjacency] predecessors n e]. reflexivity. }
  assert (Hedges : forall h, graph_e (base h) =
      fold_right (fun v n => length (succs (base h) v) + n) 0 (nodes h)).
  { intros [[vertices adjacency] predecessors n e]. reflexivity. }
  split.
  - rewrite !Hnodes, scc_graph_nodes. reflexivity.
  - rewrite !Hedges, scc_graph_nodes. induction (nodes g) as [|v vertices IH];
      cbn [fold_right]; [lia|]. pose proof (scc_graph_row_length g v). lia.
Qed.

(** Rebuilt graph identifiers never exceed the input identifier width. *)
Lemma scc_graph_width g : graph_width (base (scc_graph g)) <= graph_width (base g).
Proof.
  change (graph_max (vertex_width (nodes g))
    (fold_right (fun v w => graph_max (vertex_width (succs (base (scc_graph g)) v)) w)
      0 (nodes g)) <= graph_width (base g)).
  rewrite search_graph_max. apply Nat.max_lub.
  - apply scc_vertex_width_bound. apply Forall_forall. intros v Hin.
    now apply scc_node_width.
  - induction (nodes g) as [|v vertices IH]; cbn [fold_right]; [lia|].
    rewrite search_graph_max. apply Nat.max_lub; [apply scc_filtered_row_width|exact IH].
Qed.

(** The actual filtered run width is bounded even with repeated roots. *)
Lemma scc_trace_run_width g :
  search_trace_width (base (scc_graph g)) (nodes (scc_graph g)) (scc_trace g) <=
    graph_width (base g).
Proof.
  unfold search_trace_width. rewrite scc_graph_nodes, search_graph_max. apply Nat.max_lub.
  - apply scc_vertex_width_bound. apply Forall_forall. intros v Hin.
    now apply scc_node_width.
  - induction (entered (scc_trace g)) as [|v vertices IH]; cbn [fold_right]; [lia|].
    rewrite search_graph_max. apply Nat.max_lub; [apply scc_filtered_row_width|exact IH].
Qed.

Local Lemma scc_positive_size_value p : Pos.size_nat p <= Pos.to_nat p.
Proof.
  induction p; cbn [Pos.size_nat];
    [rewrite Pos2Nat.inj_xI|rewrite Pos2Nat.inj_xO|reflexivity];
    pose proof (Pos2Nat.is_pos p); lia.
Qed.

(** Recomputed cache bit lengths are bounded by their natural counts. *)
Lemma scc_cache_size n : N.size_nat (N.of_nat n) <= n.
Proof.
  assert (Hbinary : forall count, N.size_nat count <= N.to_nat count).
  { intros [|p]; [reflexivity|apply scc_positive_size_value]. }
  specialize (Hbinary (N.of_nat n)). now rewrite Nat2N.id in Hbinary.
Qed.

(** The filtered search's raw work fits the original vertex-and-edge size budget. *)
Lemma scc_trace_raw_work g :
  (search_trace_raw_work (scc_graph g) (nodes (scc_graph g)) <=
    4 * N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
Proof.
  pose proof (scc_trace_size g) as Hsize.
  pose proof (scc_trace_length g) as Hlength.
  pose proof (scc_trace_run_width g) as Hwidth.
  destruct (scc_graph_size g) as [Hvertices Hedges].
  assert (Hnodes : length (nodes g) = graph_n (base g)).
  { destruct g as [[vertices adjacency] predecessors n e]. reflexivity. }
  assert (Hmass : search_trace_mass (scc_graph g) (nodes (scc_graph g)) <=
      3 * graph_n (base g) + graph_e (base g) + 1).
  { unfold search_trace_mass. fold (scc_trace g). rewrite scc_graph_nodes, Hnodes. lia. }
  destruct (scc_graph_counts g) as [Hnv Hne].
  pose proof (scc_cache_size (graph_n (base (scc_graph g)))) as Hvertex_bits.
  pose proof (scc_cache_size (graph_e (base (scc_graph g)))) as Hedge_bits.
  unfold search_trace_raw_work. fold (scc_trace g). rewrite Hnv, Hne.
  assert (Hpositive : (1 <= N.of_nat (graph_width (base g) + 1))%N) by lia.
  nia.
Qed.

(** Traversal from listed roots enters only listed vertices. *)
Lemma scc_search_entered g roots :
  (forall r, In r roots -> In r (nodes g)) ->
  forall v, In v (entered (prepared_search_trace (scc_graph g) roots)) -> In v (nodes g).
Proof.
  intros Hroots v Hin.
  assert (Hready_roots : forall r, In r roots -> In r (nodes (scc_graph g))).
  { intros r Hr. rewrite scc_graph_nodes. now apply Hroots. }
  apply (proj1 (prepared_search_reach_closed (scc_graph g) roots
    (scc_graph_counts g) (scc_search_closed g) Hready_roots v)) in Hin.
  apply search_reach_origin in Hin. destruct Hin as [Hroot|[u [Hreach Hedge]]].
  - now apply Hroots.
  - now apply (scc_graph_closed g u v).
Qed.

(** Entered vertices and their filtered rows fit the input occurrence budgets. *)
Lemma scc_search_sizes g roots :
  (forall r, In r roots -> In r (nodes g)) ->
  length (entered (prepared_search_trace (scc_graph g) roots)) <= graph_n (base g) /\
  fold_right (fun v n => length (succs (base (scc_graph g)) v) + n) 0
    (entered (prepared_search_trace (scc_graph g) roots)) <= graph_e (base g).
Proof.
  intros Hroots. pose proof (scc_search_entered g roots Hroots) as Hincluded.
  pose proof (prepared_search_unique_raw (scc_graph g) roots) as Hunique.
  pose proof (NoDup_incl_length Hunique Hincluded) as Hvertices.
  pose proof (scc_weight_incl (fun v => length (succs (base g) v))
    _ _ Hunique Hincluded) as Hrows. cbn beta in Hrows.
  assert (Hfiltered :
    fold_right (fun v n => length (succs (base (scc_graph g)) v) + n) 0
      (entered (prepared_search_trace (scc_graph g) roots)) <=
    fold_right (fun v n => length (succs (base g) v) + n) 0
      (entered (prepared_search_trace (scc_graph g) roots))).
  { clear Hroots Hincluded Hunique Hvertices Hrows.
    induction (entered (prepared_search_trace (scc_graph g) roots)) as [|v vs IH];
      cbn [fold_right]; [lia|]. pose proof (scc_graph_row_length g v). lia. }
  assert (Hnodes : length (nodes g) = graph_n (base g)).
  { destruct g as [[vertices adjacency] predecessors n e]. reflexivity. }
  assert (Hedges : fold_right (fun v n => length (succs (base g) v) + n) 0 (nodes g) =
      graph_e (base g)).
  { destruct g as [[vertices adjacency] predecessors n e]. reflexivity. }
  rewrite Hnodes in Hvertices. rewrite Hedges in Hrows. split; lia.
Qed.

(** Any filtered row and every listed root obey the original key-width bound. *)
Lemma scc_search_width g roots es :
  (forall r, In r roots -> In r (nodes g)) ->
  search_trace_width (base (scc_graph g)) roots es <= graph_width (base g).
Proof.
  intros Hroots. unfold search_trace_width. rewrite search_graph_max. apply Nat.max_lub.
  - apply scc_vertex_width_bound. apply Forall_forall. intros v Hin.
    apply scc_node_width. now apply Hroots.
  - induction (entered es) as [|v vertices IH]; cbn [fold_right]; [lia|].
    rewrite search_graph_max. apply Nat.max_lub; [apply scc_filtered_row_width|exact IH].
Qed.

(** Every key in a completed traversal from listed roots is an original listed key. *)
Lemma scc_search_event_width g roots :
  (forall r, In r roots -> In r (nodes g)) ->
  Forall (fun e => match e with
    | Enter v | Leave v => Pos.size_nat v <= graph_width (base g)
    | Edge _ u v => Pos.size_nat u <= graph_width (base g) /\
        Pos.size_nat v <= graph_width (base g)
    end) (prepared_search_trace (scc_graph g) roots).
Proof.
  intros Hroots.
  assert (Hready_roots : forall r, In r roots -> In r (nodes (scc_graph g))).
  { intros r Hr. rewrite scc_graph_nodes. now apply Hroots. }
  pose proof (prepared_search_nested_closed (scc_graph g) roots
    (scc_graph_counts g) (scc_search_closed g) Hready_roots) as Hnested.
  pose proof (prepared_search_rows_closed (scc_graph g) roots
    (scc_graph_counts g) (scc_search_closed g) Hready_roots) as Hrows.
  pose proof (scc_search_entered g roots Hroots) as Hentered.
  apply Forall_forall. intros [v|v|kind u v] Hin.
  - apply scc_node_width. apply Hentered. now apply search_entered_member.
  - destruct (scc_stack_leave_member [] _ [] v Hnested Hin) as [Hnil|Henter];
      [contradiction|].
    apply scc_node_width. apply Hentered. now apply search_entered_member.
  - destruct (search_trace_rows_edge _ _ kind u v Hrows Hin) as [Henter Hedge].
    split; apply scc_node_width.
    + now apply Hentered.
    + now apply (scc_graph_closed g u v).
Qed.

(** Listed roots allow a raw work estimate without uniqueness assumptions on input nodes. *)
Lemma scc_search_raw_work g roots :
  (forall r, In r roots -> In r (nodes g)) ->
  (search_trace_raw_work (scc_graph g) roots <=
    2 * N.of_nat (graph_n (base g) + graph_e (base g) + length roots + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
Proof.
  intros Hroots. destruct (scc_search_sizes g roots Hroots) as [Hvertices Hrows].
  pose proof (scc_search_width g roots (prepared_search_trace (scc_graph g) roots) Hroots) as Hwidth.
  destruct (scc_graph_size g) as [Hnode_count Hedge_count].
  destruct (scc_graph_counts g) as [Hnv Hne].
  pose proof (scc_cache_size (graph_n (base (scc_graph g)))) as Hvertex_bits.
  pose proof (scc_cache_size (graph_e (base (scc_graph g)))) as Hedge_bits.
  unfold search_trace_raw_work, search_trace_mass. rewrite Hnv, Hne.
  assert (Hpositive : (1 <= N.of_nat (graph_width (base g) + 1))%N) by lia.
  nia.
Qed.

(** The generic raw search clock specializes to any supplied listed roots. *)
Lemma scc_search_time g roots :
  (forall r, In r roots -> In r (nodes g)) ->
  (1 + T_prepared_search_trace (scc_graph g) roots <=
    (2 * search_trace_coefficient) *
      N.of_nat (graph_n (base g) + graph_e (base g) + length roots + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
Proof.
  intros Hroots. pose proof (prepared_search_time (scc_graph g) roots) as Htime.
  pose proof (scc_search_raw_work g roots Hroots) as Hwork. nia.
Qed.


(** Every input successor occurrence is covered by the input graph width. *)
Lemma scc_input_row_width g v : In v (nodes g) ->
  Forall (fun u => Pos.size_nat u <= graph_width (base g)) (succs (base g) v).
Proof.
  intros Hin. apply Forall_forall. intros u Hedge.
  destruct g as [[vertices adjacency] predecessors n e].
  cbn [nodes base] in *. unfold graph_width. rewrite search_graph_max.
  eapply Nat.le_trans.
  - exact (search_row_width_member (Digraph vertices adjacency) vertices v u Hin Hedge).
  - apply Nat.le_max_r.
Qed.

Local Lemma scc_listed_fold_time w vertices listed :
  Forall (fun v => Pos.size_nat v <= w) vertices ->
  (List.T_fold_left (fun acc v => PTrieCode.set v true acc)
    (fun acc v => 1 + PTrieCode.T_set v true acc)%N vertices listed <=
    2048 * N.of_nat (length vertices + 1) * N.of_nat (w + 1))%N.
Proof.
  intros Hwidth. revert listed. induction Hwidth as [|v vertices Hv Hwidth IH]; intros listed.
  - time_unfold @List.T_fold_left. cbn [length]. lia.
  - pose proof (PTrieT.T_set_le bool v true listed) as Hset.
    change (PTrieCode.T_set v true listed <=
      1024 * N.of_nat (Pos.size_nat v + 1))%N in Hset.
    specialize (IH (PTrieCode.set v true listed)).
    time_unfold @List.T_fold_left. cbn beta. cbn [length].
    rewrite !Nat2N.inj_add, ?time_of_nat_succ in *. nia.
Qed.

Local Lemma scc_filter_time w (listed : ptrie bool) vertices :
  Forall (fun v => Pos.size_nat v <= w) vertices ->
  (List.T_filter (fun v => match trie_get v listed with Some _ => true | None => false end)
    (fun v => 1 + T_trie_get v listed)%N vertices <=
    4 * N.of_nat (length vertices + 1) * N.of_nat (w + 1))%N.
Proof.
  intros Hwidth. induction Hwidth as [|v vertices Hv Hwidth IH].
  - time_unfold @List.T_filter. cbn [length]. lia.
  - time_unfold @List.T_filter. cbn beta. rewrite PTrieT.trie_get_clock.
    destruct (trie_get v listed); time_cbn; cbn [length];
      rewrite !Nat2N.inj_add, ?time_of_nat_succ in *; nia.
Qed.

Local Lemma scc_row_time g w (listed : ptrie bool) v rows :
  Pos.size_nat v <= w -> Forall (fun u => Pos.size_nat u <= w) (succs g v) ->
  (1 + (((1 + T_succs g v) +
    List.T_filter (fun u => match trie_get u listed with Some _ => true | None => false end)
      (fun u => 1 + T_trie_get u listed)%N (succs g v)) +
    PTrieCode.T_set v
      (filter (fun u => match trie_get u listed with Some _ => true | None => false end)
        (succs g v)) rows) <=
    2048 * N.of_nat (length (succs g v) + 1) * N.of_nat (w + 1))%N.
Proof.
  intros Hv Hrow. pose proof (scc_filter_time w listed (succs g v) Hrow) as Hfilter.
  pose proof (search_succs_clock g v) as Hread.
  pose proof (PTrieT.T_set_le (list positive) v
    (filter (fun u => match trie_get u listed with Some _ => true | None => false end)
      (succs g v)) rows) as Hset.
  change (PTrieCode.T_set v
    (filter (fun u => match trie_get u listed with Some _ => true | None => false end)
      (succs g v)) rows <= 1024 * N.of_nat (Pos.size_nat v + 1))%N in Hset.
  rewrite !Nat2N.inj_add in *. nia.
Qed.

Local Lemma scc_rows_fold_time g w (listed : ptrie bool) vertices rows :
  Forall (fun v => Pos.size_nat v <= w /\
    Forall (fun u => Pos.size_nat u <= w) (succs g v)) vertices ->
  (List.T_fold_left
    (fun acc v => PTrieCode.set v
      (filter (fun u => match trie_get u listed with Some _ => true | None => false end)
        (succs g v)) acc)
    (fun acc v => 1 + (((1 + T_succs g v) +
      List.T_filter (fun u => match trie_get u listed with Some _ => true | None => false end)
        (fun u => 1 + T_trie_get u listed)%N (succs g v)) +
      PTrieCode.T_set v
        (filter (fun u => match trie_get u listed with Some _ => true | None => false end)
          (succs g v)) acc))%N vertices rows <=
    4096 * N.of_nat (length vertices +
      fold_right (fun v n => (length (succs g v) + n)%nat) 0%nat vertices + 1) * N.of_nat (w + 1))%N.
Proof.
  intros Hwidth. revert rows. induction Hwidth as [|v vertices [Hv Hrow] Hwidth IH]; intros rows.
  - time_unfold @List.T_fold_left. cbn [length fold_right]. lia.
  - pose proof (scc_row_time g w listed v rows Hv Hrow) as Hhead.
    specialize (IH (PTrieCode.set v
      (filter (fun u => match trie_get u listed with Some _ => true | None => false end)
        (succs g v)) rows)).
    time_unfold @List.T_fold_left. cbn beta. cbn [length fold_right].
    rewrite !Nat2N.inj_add, ?time_of_nat_succ in *. clear - IH Hhead. nia.
Qed.

(** Rebuilding membership, filtered rows, and both count caches has the input size cost. *)
Lemma scc_graph_time g :
  (T_scc_graph g <= 16384 * N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
    N.of_nat (graph_width (base g) + 1))%N.
Proof.
  assert (Hkeys : Forall (fun v => Pos.size_nat v <= graph_width (base g)) (nodes g)).
  { apply Forall_forall. intros v Hin. now apply scc_node_width. }
  assert (Hrows : Forall (fun v => Pos.size_nat v <= graph_width (base g) /\
      Forall (fun u => Pos.size_nat u <= graph_width (base g)) (succs (base g) v)) (nodes g)).
  { apply Forall_forall. intros v Hin. split.
    - now apply scc_node_width.
    - now apply scc_input_row_width. }
  pose proof (scc_listed_fold_time (graph_width (base g)) (nodes g) Empty Hkeys) as Hlisted_time.
  pose proof (scc_rows_fold_time (base g) (graph_width (base g))
    (fold_left (fun acc v => PTrieCode.set v true acc) (nodes g) Empty)
    (nodes g) Empty Hrows) as Hrows_time.
  pose proof (digraph_vertex_count_time (base (scc_graph g))) as Hvertices_time.
  pose proof (digraph_edge_count_time (base (scc_graph g))) as Hedges_time.
  pose proof (graph_of_nat_time (graph_n (base (scc_graph g)))) as Hvertices_conversion.
  pose proof (graph_of_nat_time (graph_e (base (scc_graph g)))) as Hedges_conversion.
  destruct (scc_graph_size g) as [Hvertices Hedges].
  pose proof (scc_graph_width g) as Hwidth.
  assert (Hnodes : length (nodes g) = graph_n (base g)).
  { destruct g as [[vertices adjacency] predecessors n e]. reflexivity. }
  assert (Hedge_sum : fold_right (fun v n => length (succs (base g) v) + n) 0 (nodes g) =
      graph_e (base g)).
  { destruct g as [[vertices adjacency] predecessors n e]. reflexivity. }
  rewrite Hnodes in Hlisted_time. rewrite Hnodes, Hedge_sum in Hrows_time.
  clear Hkeys Hrows Hnodes Hedge_sum.
  set (size := N.of_nat (graph_n (base g) + graph_e (base g) + 1)) in *.
  set (width := N.of_nat (graph_width (base g) + 1)) in *.
  set (budget := (size * width)%N).
  assert (Hwidth_positive : (1 <= width)%N) by (unfold width; lia).
  assert (Hsize_budget : (size <= budget)%N).
  { unfold budget. rewrite <- (N.mul_1_r size) at 1.
    apply N.mul_le_mono_l. exact Hwidth_positive. }
  assert (Hvertex_count : (N.of_nat (graph_n (base (scc_graph g)) + 1) <= size)%N).
  { unfold size. lia. }
  assert (Hedge_count : (N.of_nat (graph_e (base (scc_graph g)) + 1) <= size)%N).
  { unfold size. lia. }
  assert (Hlisted_product : (N.of_nat (graph_n (base g) + 1) * width <= budget)%N).
  { unfold budget. apply N.mul_le_mono_r. unfold size. lia. }
  assert (Hfiltered_product :
    (N.of_nat (graph_n (base (scc_graph g)) + graph_e (base (scc_graph g)) + 1) *
      N.of_nat (graph_width (base (scc_graph g)) + 1) <= budget)%N).
  { unfold budget, size, width. apply N.mul_le_mono; lia. }
  rewrite <- N.mul_assoc in Hlisted_time, Hrows_time, Hedges_time.
  assert (Hlisted_scale :
    (2048 * (N.of_nat (graph_n (base g) + 1) * width) <= 2048 * budget)%N).
  { apply N.mul_le_mono_l. exact Hlisted_product. }
  pose proof (N.le_trans _ _ _ Hlisted_time Hlisted_scale) as Hlisted_final.
  fold budget in Hrows_time.
  assert (Hedges_final : (T_graph_e (base (scc_graph g)) <= 16 * budget)%N).
  { eapply N.le_trans; [exact Hedges_time|].
    apply N.mul_le_mono_l. exact Hfiltered_product. }
  assert (Hvertices_final : (T_graph_n (base (scc_graph g)) <= 2 * budget)%N) by lia.
  assert (Hvertices_convert :
    (TimeHelpers.N.T_of_nat (graph_n (base (scc_graph g))) <= 3 * budget)%N) by lia.
  assert (Hedges_convert :
    (TimeHelpers.N.T_of_nat (graph_e (base (scc_graph g))) <= 3 * budget)%N) by lia.
  assert (Hpositive : (1 <= budget)%N).
  { eapply N.le_trans; [|exact Hsize_budget]. unfold size. lia. }
  assert (Hrebuilt :
    Digraph (nodes g)
      (fold_left (fun acc v => PTrieCode.set v
        (filter (fun u => match trie_get u
          (fold_left (fun table key => PTrieCode.set key true table) (nodes g) Empty) with
          | Some _ => true | None => false end) (succs (base g) v)) acc)
        (nodes g) Empty) = base (scc_graph g)) by reflexivity.
  time_unfold @T_scc_graph. unfold T_nodes, T_base. cbn beta iota zeta.
  rewrite Hrebuilt.
  rewrite <- N.mul_assoc. fold budget. clearbody budget.
  clear - Hlisted_final Hrows_time Hvertices_final Hedges_final
    Hvertices_convert Hedges_convert Hpositive.
  lia.
Qed.

(** Filtered trace construction includes preprocessing, root access, and the raw search clock. *)
Lemma scc_trace_time g :
  (1 + T_scc_trace g <= (8 * (search_trace_coefficient + 4096)) *
    N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
Proof.
  pose proof (scc_graph_time g) as Hgraph.
  pose proof (prepared_search_time (scc_graph g) (nodes (scc_graph g))) as Hsearch.
  pose proof (scc_trace_raw_work g) as Hwork.
  assert (Hscaled : (search_trace_coefficient *
      search_trace_raw_work (scc_graph g) (nodes (scc_graph g)) <=
      search_trace_coefficient * (4 *
        N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
        N.of_nat (graph_width (base g) + 1)))%N).
  { apply N.mul_le_mono_l. exact Hwork. }
  clear Hwork. time_unfold @T_scc_trace. unfold T_nodes. cbn beta iota zeta. nia.
Qed.


(** Every low link belongs to a discovered vertex and never exceeds its discovery number. *)
Definition tarjan_low_disc (s : tarjan_state) : Prop :=
  forall v low, trie_get v (tarjan_low s) = Some low ->
    exists disc, trie_get v (tarjan_disc s) = Some disc /\
      Pos.to_nat low <= Pos.to_nat disc.

Lemma tarjan_low_disc_enter v s :
  tarjan_low_disc s -> tarjan_low_disc (TarjanVisitor.enter v s).
Proof.
  intros Hbound u i Hlookup.
  cbn [TarjanVisitor.enter tarjan_low] in Hlookup.
  cbn [TarjanVisitor.enter tarjan_disc].
  destruct (Pos.eq_dec u v) as [Heq|Hneq].
  - subst u. rewrite PTrie.get_set_same in Hlookup. injection Hlookup as Heq. subst i.
    exists (tarjan_clock s). split; [apply PTrie.get_set_same|lia].
  - rewrite PTrie.get_set_other in Hlookup by exact Hneq.
    destruct (Hbound u i Hlookup) as [disc [Hdisc Hle]].
    exists disc. split; [now rewrite PTrie.get_set_other by exact Hneq|exact Hle].
Qed.

Lemma tarjan_low_disc_lower v n s :
  tarjan_low_disc s -> tarjan_low_disc (TarjanVisitor.lower v n s).
Proof.
  intros Hbound. unfold TarjanVisitor.lower.
  destruct (trie_get v (tarjan_low s)) as [old|] eqn:Hlookup; [|exact Hbound].
  intros u i Hget. cbn [tarjan_low] in Hget. cbn [tarjan_disc].
  destruct (Pos.eq_dec u v) as [Heq|Hneq].
  - subst u. rewrite PTrie.get_set_same in Hget. injection Hget as Heq. subst i.
    destruct (Hbound v old Hlookup) as [disc [Hdisc Hle]].
    exists disc. split; [exact Hdisc|]. rewrite Pos2Nat.inj_min.
    eapply Nat.le_trans; [apply Nat.le_min_l|exact Hle].
  - rewrite PTrie.get_set_other in Hget by exact Hneq. now apply (Hbound u i).
Qed.

Lemma tarjan_low_disc_edge kind u v s :
  tarjan_low_disc s -> tarjan_low_disc (TarjanVisitor.edge kind u v s).
Proof.
  intros Hbound. destruct kind; cbn [TarjanVisitor.edge]; try exact Hbound.
  all: destruct (trie_get v (tarjan_active s)) as [[|]|]; try exact Hbound.
  all: destruct (trie_get v (tarjan_disc s)); try exact Hbound.
  all: now apply tarjan_low_disc_lower.
Qed.

Lemma tarjan_low_disc_leave v s :
  tarjan_low_disc s -> tarjan_low_disc (TarjanVisitor.leave v s).
Proof.
  intros Hbound. unfold TarjanVisitor.leave.
  destruct (trie_get v (tarjan_low s)) as [low|]; [|exact Hbound].
  destruct (trie_get v (tarjan_disc s)) as [disc|]; [|exact Hbound].
  destruct (Pos.eqb low disc).
  - destruct (tarjan_pop v (tarjan_next s) (tarjan_pending s) (tarjan_low s)
      (tarjan_active s) (tarjan_owners s))
      as [[[[members tail] lows] actives] owners] eqn:Hpop.
    intros u i Hlookup. cbn [tarjan_low] in Hlookup. cbn [tarjan_disc].
    destruct (proj2 (tarjan_pop_lookup _ _ _ _ _ _ _ _ _ _ _ Hpop) u)
      as [Hget _]. rewrite Hget in Hlookup.
    destruct (existsb (Pos.eqb u) members); [discriminate|now apply (Hbound u i)].
  - destruct (match tarjan_frames s with [] => [] | _ :: rest => rest end).
    + exact Hbound.
    + apply tarjan_low_disc_lower. exact Hbound.
Qed.

(** Arbitrary event folds preserve the paired low/discovery relation. *)
Lemma tarjan_low_disc_fold es s : tarjan_low_disc s ->
  tarjan_low_disc
    (fold_events TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge es s).
Proof.
  unfold fold_events. revert s. induction es as [|e es IH]; intros s Hbound;
    cbn [fold_left]; [exact Hbound|].
  apply IH. destruct e; cbn [visit_event].
  - now apply tarjan_low_disc_enter.
  - now apply tarjan_low_disc_leave.
  - now apply tarjan_low_disc_edge.
Qed.

Lemma tarjan_low_disc_initial : tarjan_low_disc tarjan_initial.
Proof.
  intros v i Hlookup. cbn [tarjan_initial tarjan_low] in Hlookup.
  rewrite PTrie.get_empty in Hlookup. discriminate Hlookup.
Qed.

(** Active and low-link tables have exactly the current pending support. *)
Definition tarjan_pending_domains (s : tarjan_state) : Prop :=
  (forall v, trie_get v (tarjan_active s) = Some true <-> In v (tarjan_pending s)) /\
  (forall v, (exists i, trie_get v (tarjan_low s) = Some i) <-> In v (tarjan_pending s)).

Lemma tarjan_pending_domains_enter v s :
  tarjan_pending_domains s -> tarjan_pending_domains (TarjanVisitor.enter v s).
Proof.
  intros [Hactive Hlow]. split; intro u;
    cbn [TarjanVisitor.enter tarjan_active tarjan_low tarjan_pending];
    destruct (Pos.eq_dec u v) as [Heq|Hneq].
  - subst u. rewrite PTrie.get_set_same. cbn [In]. intuition.
  - rewrite PTrie.get_set_other by exact Hneq. rewrite (Hactive u).
    cbn [In]. intuition congruence.
  - subst u. rewrite PTrie.get_set_same. cbn [In]. split.
    + intros _. now left.
    + intros _. exists (tarjan_clock s). reflexivity.
  - rewrite PTrie.get_set_other by exact Hneq. rewrite (Hlow u).
    cbn [In]. intuition congruence.
Qed.

Lemma tarjan_pending_domains_lower v n s :
  tarjan_pending_domains s -> tarjan_pending_domains (TarjanVisitor.lower v n s).
Proof.
  intros Hdomains. unfold TarjanVisitor.lower.
  destruct (trie_get v (tarjan_low s)) as [old|] eqn:Hlookup; [|exact Hdomains].
  destruct Hdomains as [Hactive Hlow]. split; [exact Hactive|].
  intro u. cbn [tarjan_low tarjan_pending].
  destruct (Pos.eq_dec u v) as [Heq|Hneq].
  - subst u. rewrite PTrie.get_set_same. split.
    + intros _. apply (proj1 (Hlow v)). exists old. exact Hlookup.
    + intros _. exists (Pos.min old n). reflexivity.
  - rewrite PTrie.get_set_other by exact Hneq. apply Hlow.
Qed.

Lemma tarjan_pending_domains_edge kind u v s :
  tarjan_pending_domains s -> tarjan_pending_domains (TarjanVisitor.edge kind u v s).
Proof.
  intros Hdomains. destruct kind; cbn [TarjanVisitor.edge]; try exact Hdomains.
  all: destruct (trie_get v (tarjan_active s)) as [[|]|]; try exact Hdomains.
  all: destruct (trie_get v (tarjan_disc s)); try exact Hdomains.
  all: now apply tarjan_pending_domains_lower.
Qed.

Lemma tarjan_positive_existsb v xs :
  existsb (Pos.eqb v) xs = true <-> In v xs.
Proof.
  rewrite existsb_exists. split.
  - intros [u [Hin Heq]]. apply Pos.eqb_eq in Heq. now subst u.
  - intros Hin. exists v. split; [exact Hin|apply Pos.eqb_refl].
Qed.

Lemma tarjan_nodup_app_disjoint {A} (xs ys : list A) :
  NoDup (xs ++ ys) -> forall v, In v xs -> In v ys -> False.
Proof.
  induction xs as [|x xs IH]; intros Hunique v Hleft Hright; [contradiction|].
  cbn [app] in Hunique. inversion Hunique as [|x' xs' Hfresh Hrest]; subst x' xs'.
  destruct Hleft as [Heq|Hin].
  - subst v. apply Hfresh. apply in_or_app. now right.
  - exact (IH Hrest v Hin Hright).
Qed.

(** A pop removes precisely its prefix support from both live tables. *)
Lemma tarjan_pop_domains root index pending low active owners
    members tail low' active' owners' :
  NoDup pending ->
  (forall v, trie_get v active = Some true <-> In v pending) ->
  (forall v, (exists i, trie_get v low = Some i) <-> In v pending) ->
  tarjan_pop root index pending low active owners = (members, tail, low', active', owners') ->
  (forall v, trie_get v active' = Some true <-> In v tail) /\
  (forall v, (exists i, trie_get v low' = Some i) <-> In v tail).
Proof.
  intros Hunique Hactive Hlow Hpop.
  destruct (tarjan_pop_lookup _ _ _ _ _ _ _ _ _ _ _ Hpop) as [Hsplit Hlookups].
  assert (Hdisjoint : forall v, In v tail -> ~ In v members).
  { intros v Htail Hmember. eapply tarjan_nodup_app_disjoint.
    - rewrite <- Hsplit. exact Hunique.
    - exact Hmember.
    - exact Htail. }
  assert (Hretained : forall v, existsb (Pos.eqb v) members = false ->
      (In v pending <-> In v tail)).
  { intros v Hfalse. rewrite Hsplit, in_app_iff. split; [|now right].
    intros [Hmember|Htail]; [|exact Htail].
    apply (proj2 (tarjan_positive_existsb v members)) in Hmember. congruence. }
  split; intro v; destruct (Hlookups v) as [Hlow' [Hactive' Howners']].
  - rewrite Hactive'. destruct (existsb (Pos.eqb v) members) eqn:Hmember.
    + split; [discriminate|]. intro Htail. exfalso. apply (Hdisjoint v Htail).
      now apply (proj1 (tarjan_positive_existsb v members)).
    + rewrite (Hactive v). now apply Hretained.
  - rewrite Hlow'. destruct (existsb (Pos.eqb v) members) eqn:Hmember.
    + split; [intros [i Hfalse]; discriminate|]. intro Htail. exfalso.
      apply (Hdisjoint v Htail). now apply (proj1 (tarjan_positive_existsb v members)).
    + rewrite (Hlow v). now apply Hretained.
Qed.

Lemma tarjan_pending_domains_leave v s :
  NoDup (tarjan_pending s) -> tarjan_pending_domains s ->
  tarjan_pending_domains (TarjanVisitor.leave v s).
Proof.
  intros Hunique Hdomains. unfold TarjanVisitor.leave.
  destruct (trie_get v (tarjan_low s)) as [low|]; [|exact Hdomains].
  destruct (trie_get v (tarjan_disc s)) as [disc|]; [|exact Hdomains].
  destruct (Pos.eqb low disc).
  - destruct (tarjan_pop v (tarjan_next s) (tarjan_pending s) (tarjan_low s)
      (tarjan_active s) (tarjan_owners s))
      as [[[[members tail] lows] actives] owners] eqn:Hpop.
    destruct Hdomains as [Hactive Hlow].
    exact (tarjan_pop_domains _ _ _ _ _ _ _ _ _ _ _ Hunique Hactive Hlow Hpop).
  - destruct (match tarjan_frames s with [] => [] | _ :: rest => rest end).
    + exact Hdomains.
    + apply tarjan_pending_domains_lower. exact Hdomains.
Qed.

Lemma tarjan_pending_domains_initial : tarjan_pending_domains tarjan_initial.
Proof.
  split; intro v; cbn [tarjan_initial tarjan_active tarjan_low tarjan_pending In];
    rewrite PTrie.get_empty.
  - split; [discriminate|contradiction].
  - split; [intros [i Hfalse]; discriminate|contradiction].
Qed.

(** Unique entry traces retain exact pending support throughout the visitor fold. *)
Lemma tarjan_pending_domains_fold es : NoDup (entered es) ->
  tarjan_pending_domains
    (fold_events TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge es tarjan_initial).
Proof.
  induction es as [|e es IH] using rev_ind; intro Hunique.
  - apply tarjan_pending_domains_initial.
  - assert (Hprefix : NoDup (entered es)).
    { rewrite search_entered_app in Hunique. now apply NoDup_app_remove_r in Hunique. }
    specialize (IH Hprefix).
    pose proof (Permutation_NoDup (Permutation_sym (tarjan_bag_inventory es)) Hprefix) as Hbag.
    unfold tarjan_bag in Hbag. apply NoDup_app_remove_r in Hbag.
    unfold fold_events at 1. rewrite fold_left_app.
    change (tarjan_pending_domains
      (visit_event TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge
        (fold_events TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge es tarjan_initial) e)).
    destruct e; cbn [visit_event].
    + now apply tarjan_pending_domains_enter.
    + now apply tarjan_pending_domains_leave.
    + now apply tarjan_pending_domains_edge.
Qed.

(** The oldest pending vertex remains on the active frame stack and bounds all live numbers. *)
Definition tarjan_bottom (s : tarjan_state) : Prop :=
  forall prefix root, tarjan_pending s = prefix ++ [root] ->
    In root (tarjan_frames s) /\
    exists bound, trie_get root (tarjan_disc s) = Some bound /\
      (forall v disc, In v (tarjan_pending s) ->
        trie_get v (tarjan_disc s) = Some disc -> Pos.to_nat bound <= Pos.to_nat disc) /\
      (forall v low, trie_get v (tarjan_low s) = Some low ->
        Pos.to_nat bound <= Pos.to_nat low).

Lemma tarjan_bottom_enter v s :
  ~ In v (tarjan_pending s) -> tarjan_pending_domains s ->
  tarjan_values_below_clock s -> tarjan_bottom s ->
  tarjan_bottom (TarjanVisitor.enter v s).
Proof.
  intros Hfresh Hdomains Hvalues Hbottom prefix root Hpending.
  cbn [TarjanVisitor.enter tarjan_pending] in Hpending.
  destruct prefix as [|first prefix].
  - cbn [app] in Hpending. injection Hpending as Hroot Hempty. subst root.
    split; [cbn [TarjanVisitor.enter tarjan_frames In]; now left|].
    exists (tarjan_clock s). split.
    + cbn [TarjanVisitor.enter tarjan_disc]. apply PTrie.get_set_same.
    + split.
      * intros u i Hin Hget. cbn [TarjanVisitor.enter tarjan_pending] in Hin.
        rewrite Hempty in Hin. cbn [In] in Hin. destruct Hin as [Heq|Hfalse]; [subst u|contradiction].
        cbn [TarjanVisitor.enter tarjan_disc] in Hget.
        rewrite PTrie.get_set_same in Hget. injection Hget as Heq. subst i. lia.
      * intros u i Hget. cbn [TarjanVisitor.enter tarjan_low] in Hget.
        destruct (Pos.eq_dec u v) as [Heq|Hneq].
        -- subst u. rewrite PTrie.get_set_same in Hget. injection Hget as Heq. subst i. lia.
        -- rewrite PTrie.get_set_other in Hget by exact Hneq.
           assert (Hin : In u (tarjan_pending s)).
           { apply (proj1 ((proj2 Hdomains) u)). exists i. exact Hget. }
           rewrite Hempty in Hin. contradiction.
  - cbn [app] in Hpending. injection Hpending as Hfirst Htail. subst first.
    destruct (Hbottom prefix root Htail) as [Hframe [bound [Hroot [Hdisc Hlow]]]].
    assert (Hdifferent : root <> v).
    { intros Heq. subst root. apply Hfresh. rewrite Htail. apply in_or_app. right. now left. }
    pose proof ((proj1 Hvalues) root bound Hroot) as Hclock.
    split; [cbn [TarjanVisitor.enter tarjan_frames In]; now right|].
    exists bound. split.
    + cbn [TarjanVisitor.enter tarjan_disc]. now rewrite PTrie.get_set_other by exact Hdifferent.
    + split.
      * intros u i Hin Hget. cbn [TarjanVisitor.enter tarjan_pending] in Hin.
        cbn [TarjanVisitor.enter tarjan_disc] in Hget.
        destruct (Pos.eq_dec u v) as [Heq|Hneq].
        -- subst u. rewrite PTrie.get_set_same in Hget. injection Hget as Heq. subst i. lia.
        -- rewrite PTrie.get_set_other in Hget by exact Hneq.
           apply (Hdisc u i); [destruct Hin as [Heq|Hin]; [congruence|exact Hin]|exact Hget].
      * intros u i Hget. cbn [TarjanVisitor.enter tarjan_low] in Hget.
        destruct (Pos.eq_dec u v) as [Heq|Hneq].
        -- subst u. rewrite PTrie.get_set_same in Hget. injection Hget as Heq. subst i. lia.
        -- rewrite PTrie.get_set_other in Hget by exact Hneq. now apply (Hlow u i).
Qed.

(** Lowering preserves the pending minimum when the supplied number respects that minimum. *)
Lemma tarjan_bottom_lower v n s :
  tarjan_bottom s ->
  (forall prefix root bound, tarjan_pending s = prefix ++ [root] ->
    trie_get root (tarjan_disc s) = Some bound -> Pos.to_nat bound <= Pos.to_nat n) ->
  tarjan_bottom (TarjanVisitor.lower v n s).
Proof.
  intros Hbottom Hnumber. unfold TarjanVisitor.lower.
  destruct (trie_get v (tarjan_low s)) as [old|] eqn:Hlookup; [|exact Hbottom].
  intros prefix root Hpending. cbn [tarjan_pending] in Hpending.
  destruct (Hbottom prefix root Hpending) as [Hframe [bound [Hroot [Hdisc Hlow]]]].
  split; [exact Hframe|]. exists bound. split; [exact Hroot|]. split; [exact Hdisc|].
  intros u i Hget. cbn [tarjan_low] in Hget.
  destruct (Pos.eq_dec u v) as [Heq|Hneq].
  - subst u. rewrite PTrie.get_set_same in Hget. injection Hget as Heq. subst i.
    rewrite Pos2Nat.inj_min. apply Nat.min_glb.
    + exact (Hlow v old Hlookup).
    + exact (Hnumber prefix root bound Hpending Hroot).
  - rewrite PTrie.get_set_other in Hget by exact Hneq. now apply (Hlow u i).
Qed.

Lemma tarjan_bottom_edge kind u v s :
  tarjan_pending_domains s -> tarjan_bottom s ->
  tarjan_bottom (TarjanVisitor.edge kind u v s).
Proof.
  intros Hdomains Hbottom. destruct kind; cbn [TarjanVisitor.edge]; try exact Hbottom.
  all: destruct (trie_get v (tarjan_active s)) as [[|]|] eqn:Hactive; try exact Hbottom.
  all: destruct (trie_get v (tarjan_disc s)) as [disc|] eqn:Hlookup; try exact Hbottom.
  all: apply tarjan_bottom_lower; [exact Hbottom|].
  all: intros prefix root bound Hpending Hroot.
  all: destruct (Hbottom prefix root Hpending) as [Hframe [minimum [Hminimum [Hdisc Hlow]]]].
  all: assert (Heq : minimum = bound) by congruence; subst minimum.
  all: apply (Hdisc v disc); [now apply (proj1 ((proj1 Hdomains) v))|exact Hlookup].
Qed.

(** A present pop root occurs in the consumed prefix. *)
Lemma tarjan_pop_root_member root index pending low active owners
    members tail low' active' owners' :
  In root pending ->
  tarjan_pop root index pending low active owners = (members, tail, low', active', owners') ->
  In root members.
Proof.
  revert low active owners members tail low' active' owners'.
  induction pending as [|v pending IH];
    intros low active owners members tail low' active' owners' Hin Hpop; [contradiction|].
  cbn [tarjan_pop] in Hpop. destruct (Pos.eqb v root) eqn:Hsame.
  - apply Pos.eqb_eq in Hsame. subst v. inversion Hpop; subst. now left.
  - destruct (tarjan_pop root index pending (PTrieCode.remove v low)
      (PTrieCode.remove v active) (PTrieCode.set v index owners))
      as [[[[popped remaining] lows] actives] assigned] eqn:Hrest.
    inversion Hpop; subst members tail low' active' owners'. right.
    apply Pos.eqb_neq in Hsame. eapply IH; [|exact Hrest].
    destruct Hin as [Heq|Hin]; [congruence|exact Hin].
Qed.

(** Changing only frames needs only membership of each possible pending bottom. *)
Lemma tarjan_bottom_reframe s frames :
  tarjan_bottom s ->
  (forall prefix root, tarjan_pending s = prefix ++ [root] -> In root frames) ->
  tarjan_bottom
    (TarjanState (tarjan_disc s) (tarjan_low s) (tarjan_pending s) (tarjan_active s)
      frames (tarjan_emitted s) (tarjan_owners s) (tarjan_clock s) (tarjan_next s)).
Proof.
  intros Hbottom Hframes prefix root Hpending.
  cbn [tarjan_pending] in Hpending.
  destruct (Hbottom prefix root Hpending) as [_ [bound [Hroot [Hdisc Hlow]]]].
  split; [now apply (Hframes prefix root)|].
  exists bound. split; [exact Hroot|]. split; [exact Hdisc|exact Hlow].
Qed.

(** A matching leave preserves the pending bottom, or removes it in its own root pop. *)
Lemma tarjan_bottom_leave v frames s :
  tarjan_frames s = v :: frames -> NoDup (tarjan_pending s) ->
  tarjan_pending_domains s -> tarjan_low_disc s -> tarjan_bottom s ->
  tarjan_bottom (TarjanVisitor.leave v s).
Proof.
  intros Hframes Hunique Hdomains Hpaired Hbottom.
  unfold TarjanVisitor.leave. rewrite Hframes. cbn beta iota zeta.
  destruct (trie_get v (tarjan_low s)) as [low|] eqn:Hlow.
  2: {
    apply tarjan_bottom_reframe; [exact Hbottom|]. intros prefix root Hpending.
    destruct (Hbottom prefix root Hpending) as [Hmember Hnumbers].
    rewrite Hframes in Hmember. destruct Hmember as [Heq|Hin]; [|exact Hin].
    subst root. assert (Hin : In v (tarjan_pending s)).
    { rewrite Hpending. apply in_or_app. right. now left. }
    apply (proj2 ((proj2 Hdomains) v)) in Hin.
    destruct Hin as [i Hlookup]. congruence.
  }
  destruct (trie_get v (tarjan_disc s)) as [disc|] eqn:Hdisc.
  2: { destruct (Hpaired v low Hlow) as [i [Hlookup Hle]]. congruence. }
  destruct (Pos.eqb low disc) eqn:Hsame.
  - destruct (tarjan_pop v (tarjan_next s) (tarjan_pending s) (tarjan_low s)
      (tarjan_active s) (tarjan_owners s))
      as [[[[members tail] lows] actives] owners] eqn:Hpop.
    intros prefix root Htail. cbn [tarjan_pending] in Htail.
    destruct (tarjan_pop_lookup _ _ _ _ _ _ _ _ _ _ _ Hpop) as [Hsplit Hlookups].
    assert (Hpending : tarjan_pending s = (members ++ prefix) ++ [root]).
    { now rewrite Hsplit, Htail, app_assoc. }
    destruct (Hbottom (members ++ prefix) root Hpending)
      as [Hmember [bound [Hroot [Hdiscs Hlows]]]].
    assert (Hin_tail : In root tail).
    { rewrite Htail. apply in_or_app. right. now left. }
    assert (Hdifferent : root <> v).
    { intros Heq. subst root.
      assert (Hin_pending : In v (tarjan_pending s)).
      { apply (proj1 ((proj2 Hdomains) v)). exists low. exact Hlow. }
      pose proof (tarjan_pop_root_member _ _ _ _ _ _ _ _ _ _ _ Hin_pending Hpop) as Hin_members.
      eapply tarjan_nodup_app_disjoint; [rewrite <- Hsplit; exact Hunique|exact Hin_members|exact Hin_tail]. }
    split.
    + cbn [tarjan_frames]. rewrite Hframes in Hmember.
      destruct Hmember as [Heq|Hin]; [congruence|exact Hin].
    + exists bound. split; [exact Hroot|]. split.
      * intros u i Hin Hlookup. cbn [tarjan_pending] in Hin.
        apply (Hdiscs u i); [rewrite Hsplit; apply in_or_app; now right|exact Hlookup].
      * intros u i Hlookup. cbn [tarjan_low] in Hlookup.
        destruct (Hlookups u) as [Hget _]. rewrite Hget in Hlookup.
        destruct (existsb (Pos.eqb u) members); [discriminate|now apply (Hlows u i)].
  - assert (Hremaining : forall prefix root,
        tarjan_pending s = prefix ++ [root] -> In root frames).
    { intros prefix root Hpending.
      destruct (Hbottom prefix root Hpending) as [Hmember [bound [Hroot [Hdiscs Hlows]]]].
      rewrite Hframes in Hmember. destruct Hmember as [Heq|Hin]; [|exact Hin].
      subst root. rewrite Hdisc in Hroot. injection Hroot as Heq. subst bound.
      pose proof (Hlows v low Hlow) as Hfloor.
      destruct (Hpaired v low Hlow) as [number [Hnumber Hupper]].
      rewrite Hdisc in Hnumber. injection Hnumber as Heq. subst number.
      assert (Heq : low = disc) by (apply Pos2Nat.inj; lia).
      apply Pos.eqb_neq in Hsame. contradiction. }
    pose proof (tarjan_bottom_reframe s frames Hbottom Hremaining) as Hreframed.
    destruct frames as [|parent frames]; [exact Hreframed|].
    apply tarjan_bottom_lower; [exact Hreframed|].
    intros prefix root bound Hpending Hroot.
    cbn [tarjan_pending tarjan_disc] in Hpending, Hroot.
    destruct (Hbottom prefix root Hpending) as [_ [minimum [Hminimum [Hdiscs Hlows]]]].
    assert (Heq : minimum = bound) by congruence. subst minimum.
    exact (Hlows v low Hlow).
Qed.

Lemma tarjan_current_pending_unique es s :
  NoDup (rev (entered es) ++ tarjan_bag s) -> NoDup (tarjan_pending s).
Proof.
  intros Hunique. apply NoDup_app_remove_l in Hunique.
  unfold tarjan_bag in Hunique. now apply NoDup_app_remove_r in Hunique.
Qed.

(** One callback moves its entry from the remaining trace into the state inventory. *)
Lemma tarjan_future_unique e es s :
  NoDup (rev (entered (e :: es)) ++ tarjan_bag s) ->
  NoDup (rev (entered es) ++
    tarjan_bag (visit_event TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge s e)).
Proof.
  intros Hunique.
  assert (Hperm : Permutation
      (rev (entered es) ++
        tarjan_bag (visit_event TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge s e))
      (rev (entered (e :: es)) ++ tarjan_bag s)).
  { eapply Permutation_trans.
    - apply Permutation_app_head. apply tarjan_bag_event.
    - destruct e; cbn [entered rev app]; [rewrite <- app_assoc| |]; reflexivity. }
  eapply Permutation_NoDup; [apply Permutation_sym; exact Hperm|exact Hunique].
Qed.

Lemma tarjan_event_support e s :
  NoDup (tarjan_pending s) -> tarjan_pending_domains s ->
  tarjan_low_disc s -> tarjan_values_below_clock s ->
  let next := visit_event TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge s e in
  tarjan_pending_domains next /\ tarjan_low_disc next /\ tarjan_values_below_clock next.
Proof.
  intros Hunique Hdomains Hpaired Hvalues. cbn zeta. split.
  - destruct e; cbn [visit_event].
    + now apply tarjan_pending_domains_enter.
    + now apply tarjan_pending_domains_leave.
    + now apply tarjan_pending_domains_edge.
  - split.
    + change (tarjan_low_disc
        (fold_events TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge [e] s)).
      now apply tarjan_low_disc_fold.
    + change (tarjan_values_below_clock
        (fold_events TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge [e] s)).
      now apply tarjan_values_fold.
Qed.

(** Nested unique entries preserve the pending-bottom invariant and the exact frame stack. *)
Lemma tarjan_nested_bottom before es after : trace_stack before es after -> forall s,
  tarjan_frames s = before -> NoDup (rev (entered es) ++ tarjan_bag s) ->
  tarjan_pending_domains s -> tarjan_low_disc s -> tarjan_values_below_clock s ->
  tarjan_bottom s ->
  tarjan_bottom (fold_events TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge es s) /\
  tarjan_frames (fold_events TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge es s) = after.
Proof.
  intros Htrace. induction Htrace as
    [stack|stack v rest final Htrace IH|stack v rest final Htrace IH|
      stack kind u v rest final Htrace IH];
    intros s Hframes Hunique Hdomains Hpaired Hvalues Hbottom.
  - cbn [fold_events fold_left]. split; assumption.
  - assert (Hfresh : ~ In v (tarjan_pending s)).
    { intros Hin. pose proof Hunique as Hnew.
      cbn [entered rev] in Hnew. rewrite <- app_assoc in Hnew. cbn [app] in Hnew.
      apply NoDup_app_remove_l in Hnew.
      inversion Hnew as [|v' bag Habsent Htail]; subst v' bag.
      apply Habsent. unfold tarjan_bag. apply in_or_app. now left. }
    pose proof (tarjan_current_pending_unique _ _ Hunique) as Hpending_unique.
    destruct (tarjan_event_support (Enter v) s Hpending_unique Hdomains Hpaired Hvalues)
      as [Hdomains' [Hpaired' Hvalues']].
    cbn [fold_events fold_left visit_event]. apply IH.
    + cbn [TarjanVisitor.enter tarjan_frames]. now rewrite Hframes.
    + exact (tarjan_future_unique (Enter v) rest s Hunique).
    + exact Hdomains'.
    + exact Hpaired'.
    + exact Hvalues'.
    + now apply tarjan_bottom_enter.
  - pose proof (tarjan_current_pending_unique _ _ Hunique) as Hpending_unique.
    destruct (tarjan_event_support (Leave v) s Hpending_unique Hdomains Hpaired Hvalues)
      as [Hdomains' [Hpaired' Hvalues']].
    cbn [fold_events fold_left visit_event]. apply IH.
    + pose proof (proj2 (proj2 (tarjan_event_metadata (Leave v) s))) as Hnext.
      cbn [visit_event] in Hnext. now rewrite Hframes in Hnext.
    + exact (tarjan_future_unique (Leave v) rest s Hunique).
    + exact Hdomains'.
    + exact Hpaired'.
    + exact Hvalues'.
    + now apply (tarjan_bottom_leave v stack).
  - pose proof (tarjan_current_pending_unique _ _ Hunique) as Hpending_unique.
    destruct (tarjan_event_support (Edge kind u v) s Hpending_unique Hdomains Hpaired Hvalues)
      as [Hdomains' [Hpaired' Hvalues']].
    cbn [fold_events fold_left visit_event]. apply IH.
    + pose proof (proj2 (proj2 (tarjan_event_metadata (Edge kind u v) s))) as Hnext.
      cbn [visit_event] in Hnext. now rewrite Hframes in Hnext.
    + exact (tarjan_future_unique (Edge kind u v) rest s Hunique).
    + exact Hdomains'.
    + exact Hpaired'.
    + exact Hvalues'.
    + now apply tarjan_bottom_edge.
Qed.

Lemma tarjan_bottom_initial : tarjan_bottom tarjan_initial.
Proof.
  intros prefix root Hpending. cbn [tarjan_initial tarjan_pending] in Hpending.
  destruct prefix; discriminate Hpending.
Qed.

Lemma tarjan_last_split (xs : list positive) : xs <> [] ->
  exists prefix root, xs = prefix ++ [root].
Proof.
  induction xs as [|v xs IH]; intro Hnonempty; [contradiction|].
  destruct xs as [|u xs].
  - exists [], v. reflexivity.
  - destruct (IH ltac:(discriminate)) as [prefix [root Hsplit]].
    exists (v :: prefix), root. cbn [app]. now rewrite Hsplit.
Qed.

(** A complete nested trace with unique entries leaves neither pending vertices nor frames. *)
Lemma tarjan_complete_nested es : NoDup (entered es) -> trace_stack [] es [] ->
  let result := fold_events TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge es tarjan_initial in
  tarjan_pending result = [] /\ tarjan_frames result = [].
Proof.
  intros Hunique Htrace. cbn zeta.
  assert (Hfuture : NoDup (rev (entered es) ++ tarjan_bag tarjan_initial)).
  { cbn [tarjan_bag tarjan_initial tarjan_pending tarjan_emitted concat app].
    rewrite app_nil_r. now apply NoDup_rev. }
  destruct (tarjan_nested_bottom [] es [] Htrace tarjan_initial eq_refl Hfuture
    tarjan_pending_domains_initial tarjan_low_disc_initial tarjan_values_initial tarjan_bottom_initial)
    as [Hbottom Hframes].
  split; [|exact Hframes].
  destruct (tarjan_pending
    (fold_events TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge es tarjan_initial))
    as [|v pending] eqn:Hpending; [reflexivity|].
  destruct (tarjan_last_split (v :: pending) ltac:(discriminate)) as [prefix [root Hsplit]].
  assert (Hlast : tarjan_pending
      (fold_events TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge es tarjan_initial) =
      prefix ++ [root]) by now rewrite Hpending, Hsplit.
  destruct (Hbottom prefix root Hlast) as [Hin Hnumbers].
  rewrite Hframes in Hin. contradiction.
Qed.

(** Complete nested traces emit exactly their entries, in the public component ordering. *)
Lemma tarjan_complete_components es :
  NoDup (entered es) -> trace_stack [] es [] ->
  Permutation
    (concat (rev (tarjan_emitted
      (fold_events TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge es tarjan_initial))))
    (entered es).
Proof.
  intros Hunique Htrace.
  destruct (tarjan_complete_nested es Hunique Htrace) as [Hpending Hframes].
  pose proof (tarjan_bag_inventory es) as Hbag.
  unfold tarjan_bag in Hbag. rewrite Hpending in Hbag. cbn [app] in Hbag.
  eapply Permutation_trans; [|exact Hbag].
  change (Permutation
    (flat_map (fun c : list positive => c)
      (rev (tarjan_emitted
        (fold_events TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge es tarjan_initial))))
    (flat_map (fun c : list positive => c)
      (tarjan_emitted
        (fold_events TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge es tarjan_initial)))).
  apply Permutation_flat_map. apply Permutation_sym. apply Permutation_rev.
Qed.


(** Plain graph paths are sufficient for the semantic low-link invariant. *)
Definition tarjan_reaches (g : digraph) (u v : positive) : Prop :=
  exists vertices, path g u vertices v.

Lemma tarjan_reaches_refl g v : tarjan_reaches g v v.
Proof. exists [v]. constructor. Qed.

Lemma tarjan_reaches_edge g u v : edge g u v -> tarjan_reaches g u v.
Proof. intro Huv. exists [u; v]. econstructor; [exact Huv|constructor]. Qed.

Lemma tarjan_reaches_trans g u v w :
  tarjan_reaches g u v -> tarjan_reaches g v w -> tarjan_reaches g u w.
Proof.
  intros [first Hfirst]. revert w. induction Hfirst; intros destination [last Hlast].
  - now exists last.
  - destruct (IHHfirst destination (ex_intro _ last Hlast)) as [joined Hjoined].
    exists (u :: joined). econstructor; eassumption.
Qed.

(** Pending discoveries decrease from the newest vertex to the oldest. *)
Fixpoint tarjan_ordered (disc : ptrie positive) (vertices : list positive) : Prop :=
  match vertices with
  | [] => True
  | v :: rest => tarjan_ordered disc rest /\
      forall w a b, In w rest -> trie_get v disc = Some a ->
        trie_get w disc = Some b -> Pos.to_nat b < Pos.to_nat a
  end.
Definition tarjan_state_ordered s := tarjan_ordered (tarjan_disc s) (tarjan_pending s).

Lemma tarjan_ordered_lookup first second vertices :
  (forall v, In v vertices -> trie_get v first = trie_get v second) ->
  tarjan_ordered first vertices -> tarjan_ordered second vertices.
Proof.
  induction vertices as [|v rest IH]; intros Hlookup; cbn [tarjan_ordered]; [tauto|].
  intros [Htail Hhead]. split.
  - apply IH; [intros w Hin; apply Hlookup; now right|exact Htail].
  - intros w a b Hin Hv Hw. apply (Hhead w a b Hin).
    + rewrite Hlookup; [exact Hv|now left].
    + rewrite Hlookup; [exact Hw|now right].
Qed.

Lemma tarjan_ordered_suffix disc prefix suffix :
  tarjan_ordered disc (prefix ++ suffix) -> tarjan_ordered disc suffix.
Proof.
  induction prefix as [|v prefix IH]; cbn [app tarjan_ordered]; [tauto|].
  intros [Htail _]. now apply IH.
Qed.

Lemma tarjan_ordered_cross disc prefix suffix u v a b :
  tarjan_ordered disc (prefix ++ suffix) -> In u prefix -> In v suffix ->
  trie_get u disc = Some a -> trie_get v disc = Some b -> Pos.to_nat b < Pos.to_nat a.
Proof.
  induction prefix as [|w prefix IH]; cbn [app In tarjan_ordered]; [tauto|].
  intros [Htail Hhead] [Heq|Hin] Hv Hu Hvb.
  - subst w. apply (Hhead v a b); [apply in_or_app; now right|exact Hu|exact Hvb].
  - eapply IH; eassumption.
Qed.

Lemma tarjan_ordered_embeds disc first second :
  tarjan_embeds first second -> tarjan_ordered disc second -> tarjan_ordered disc first.
Proof.
  intro Hembed. induction Hembed; cbn [tarjan_ordered].
  - tauto.
  - intros [Htail _]. now apply IHHembed.
  - intros [Htail Hhead]. split; [now apply IHHembed|].
    intros w a b Hin Hx Hw. apply (Hhead w a b); [|exact Hx|exact Hw].
    now apply (tarjan_embeds_incl _ _ Hembed).
Qed.

Lemma tarjan_ordered_enter v s :
  ~ In v (tarjan_pending s) -> tarjan_values_below_clock s ->
  tarjan_state_ordered s -> tarjan_state_ordered (TarjanVisitor.enter v s).
Proof.
  intros Hfresh Hvalues Horder. unfold tarjan_state_ordered in *.
  cbn [TarjanVisitor.enter tarjan_disc tarjan_pending tarjan_ordered]. split.
  - eapply tarjan_ordered_lookup; [|exact Horder].
    intros w Hin. rewrite PTrie.get_set_other; [reflexivity|].
    intro Heq. subst w. contradiction.
  - intros w a b Hin Hv Hw. rewrite PTrie.get_set_same in Hv. injection Hv as Ha. subst a.
    rewrite PTrie.get_set_other in Hw by (intro Heq; subst w; contradiction).
    exact (proj1 Hvalues w b Hw).
Qed.

Lemma tarjan_ordered_lower v n s :
  tarjan_state_ordered s -> tarjan_state_ordered (TarjanVisitor.lower v n s).
Proof.
  intro Horder. unfold TarjanVisitor.lower.
  destruct (trie_get v (tarjan_low s)); exact Horder.
Qed.

Lemma tarjan_ordered_edge kind u v s :
  tarjan_state_ordered s -> tarjan_state_ordered (TarjanVisitor.edge kind u v s).
Proof.
  intro Horder. destruct kind; cbn [TarjanVisitor.edge]; try exact Horder.
  all: destruct (trie_get v (tarjan_active s)) as [[|]|]; try exact Horder.
  all: destruct (trie_get v (tarjan_disc s)); try exact Horder.
  all: now apply tarjan_ordered_lower.
Qed.

Lemma tarjan_ordered_leave v s :
  tarjan_state_ordered s -> tarjan_state_ordered (TarjanVisitor.leave v s).
Proof.
  intro Horder. unfold TarjanVisitor.leave.
  destruct (trie_get v (tarjan_low s)) as [low|]; [|exact Horder].
  destruct (trie_get v (tarjan_disc s)) as [disc|]; [|exact Horder].
  destruct (Pos.eqb low disc).
  - destruct (tarjan_pop v (tarjan_next s) (tarjan_pending s) (tarjan_low s)
      (tarjan_active s) (tarjan_owners s))
      as [[[[members remaining] lows] actives] owners] eqn:Hpop.
    pose proof (proj1 (tarjan_pop_lookup _ _ _ _ _ _ _ _ _ _ _ Hpop)) as Hsplit.
    unfold tarjan_state_ordered in *. cbn [tarjan_disc tarjan_pending].
    rewrite Hsplit in Horder. now apply tarjan_ordered_suffix in Horder.
  - destruct (match tarjan_frames s with [] => [] | _ :: rest => rest end)
      as [|parent frames]; [exact Horder|]. now apply tarjan_ordered_lower.
Qed.

Lemma tarjan_frame_number v frames s a da dv :
  tarjan_frames s = v :: frames -> tarjan_frames_embedded s ->
  tarjan_state_ordered s -> In a frames ->
  trie_get a (tarjan_disc s) = Some da -> trie_get v (tarjan_disc s) = Some dv ->
  Pos.to_nat da < Pos.to_nat dv.
Proof.
  intros Hframes Hembed Horder Ha Had Hvd.
  pose proof (tarjan_ordered_embeds _ _ _ Hembed Horder) as Hframes_order.
  rewrite Hframes in Hframes_order. exact (proj2 Hframes_order a dv da Ha Hvd Had).
Qed.

Lemma tarjan_ordered_events es : forall s,
  NoDup (rev (entered es) ++ tarjan_bag s) -> tarjan_values_below_clock s ->
  tarjan_state_ordered s ->
  tarjan_state_ordered (fold_events TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge es s).
Proof.
  induction es as [|e rest IH]; intros s Hunique Hvalues Horder.
  - exact Horder.
  - cbn [fold_events fold_left]. apply IH.
    + exact (tarjan_future_unique e rest s Hunique).
    + exact (tarjan_values_fold [e] s Hvalues).
    + destruct e as [v|v|kind u v]; cbn [visit_event].
      * apply tarjan_ordered_enter; [|exact Hvalues|exact Horder].
        intro Hin. cbn [entered rev] in Hunique. rewrite <- app_assoc in Hunique.
        cbn [app] in Hunique. apply NoDup_app_remove_l in Hunique.
        inversion Hunique as [|v' bag Hnot Htail]; subst v' bag.
        apply Hnot. unfold tarjan_bag. apply in_or_app. now left.
      * now apply tarjan_ordered_leave.
      * now apply tarjan_ordered_edge.
Qed.

(** Unique entry traces keep pending vertices in decreasing discovery order. *)
Lemma tarjan_ordered_fold es : NoDup (entered es) ->
  tarjan_state_ordered
    (fold_events TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge es tarjan_initial).
Proof.
  intro Hunique. apply tarjan_ordered_events; [|apply tarjan_values_initial|exact I].
  cbn [tarjan_bag tarjan_initial tarjan_pending tarjan_emitted concat app].
  rewrite app_nil_r. now apply NoDup_rev.
Qed.

(** Each low link has a reachable witness still present in the pending stack. *)
Definition tarjan_low_witness g s : Prop :=
  forall w low, trie_get w (tarjan_low s) = Some low ->
    exists disc witness, trie_get w (tarjan_disc s) = Some disc /\
      Pos.to_nat low <= Pos.to_nat disc /\ In witness (tarjan_pending s) /\
      trie_get witness (tarjan_disc s) = Some low /\ tarjan_reaches g w witness.

Definition tarjan_closed_low s : Prop :=
  forall w low disc, In w (tarjan_pending s) -> ~ In w (tarjan_frames s) ->
    trie_get w (tarjan_low s) = Some low -> trie_get w (tarjan_disc s) = Some disc ->
    Pos.to_nat low < Pos.to_nat disc.

Definition tarjan_pending_paths g s : Prop :=
  forall u v a b, In u (tarjan_pending s) -> In v (tarjan_pending s) ->
    trie_get u (tarjan_disc s) = Some a -> trie_get v (tarjan_disc s) = Some b ->
    Pos.to_nat a <= Pos.to_nat b -> tarjan_reaches g u v.

Lemma tarjan_pending_support g s :
  tarjan_pending_domains s -> tarjan_low_witness g s -> tarjan_closed_low s ->
  forall w disc, In w (tarjan_pending s) -> trie_get w (tarjan_disc s) = Some disc ->
    exists ancestor number, In ancestor (tarjan_frames s) /\ tarjan_reaches g w ancestor /\
      trie_get ancestor (tarjan_disc s) = Some number /\ Pos.to_nat number <= Pos.to_nat disc.
Proof.
  intros Hdomains Hlinks Hclosed.
  assert (Hsupport : forall n w disc, Pos.to_nat disc = n -> In w (tarjan_pending s) ->
      trie_get w (tarjan_disc s) = Some disc ->
      exists ancestor number, In ancestor (tarjan_frames s) /\ tarjan_reaches g w ancestor /\
        trie_get ancestor (tarjan_disc s) = Some number /\ Pos.to_nat number <= Pos.to_nat disc).
  { intro n. induction n as [n IH] using lt_wf_ind; intros w disc Hnumber Hw Hdisc.
    destruct (in_dec Pos.eq_dec w (tarjan_frames s)) as [Hframe|Hclosed_frame].
    - exists w, disc. split; [exact Hframe|]. split; [apply tarjan_reaches_refl|auto].
    - destruct (proj2 (proj2 Hdomains w) Hw) as [low Hlow].
      destruct (Hlinks w low Hlow) as [disc' [witness [Hdisc' [_ [Hwitness [Hnumber' Hpath]]]]]].
      pose proof (Hclosed w low disc Hw Hclosed_frame Hlow Hdisc) as Hstrict.
      destruct (IH (Pos.to_nat low) ltac:(lia) witness low eq_refl Hwitness Hnumber')
        as [ancestor [number [Hancestor [Hreach [Hget Hbound]]]]].
      exists ancestor, number. split; [exact Hancestor|]. split.
      + eapply tarjan_reaches_trans; eassumption.
      + split; [exact Hget|lia]. }
  intros w disc Hw Hdisc. exact (Hsupport (Pos.to_nat disc) w disc eq_refl Hw Hdisc).
Qed.

Lemma tarjan_pending_current g v frames s :
  tarjan_frames s = v :: frames -> tarjan_frames_embedded s -> tarjan_state_ordered s ->
  tarjan_pending_domains s -> tarjan_low_witness g s -> tarjan_closed_low s ->
  tarjan_pending_paths g s -> forall w, In w (tarjan_pending s) -> tarjan_reaches g w v.
Proof.
  intros Hframes Hembed Horder Hdomains Hlinks Hclosed Hpaths w Hw.
  assert (Hv : In v (tarjan_pending s)).
  { apply (tarjan_embeds_incl _ _ Hembed). rewrite Hframes. now left. }
  destruct (proj2 (proj2 Hdomains w) Hw) as [low Hlow].
  destruct (Hlinks w low Hlow) as [dw [_ [Hwd _]]].
  destruct (proj2 (proj2 Hdomains v) Hv) as [vl Hvl].
  destruct (Hlinks v vl Hvl) as [dv [_ [Hvd _]]].
  destruct (tarjan_pending_support g s Hdomains Hlinks Hclosed w dw Hw Hwd)
    as [ancestor [number [Hancestor [Hreach [Had Hbound]]]]].
  eapply tarjan_reaches_trans; [exact Hreach|].
  apply (Hpaths ancestor v number dv).
  - now apply (tarjan_embeds_incl _ _ Hembed).
  - exact Hv.
  - exact Had.
  - exact Hvd.
  - rewrite Hframes in Hancestor. destruct Hancestor as [Heq|Hancestor].
    + subst ancestor. rewrite Hvd in Had. injection Had as Heq. subst number. lia.
    + pose proof (tarjan_frame_number v frames s ancestor number dv
        Hframes Hembed Horder Hancestor Had Hvd). lia.
Qed.
Lemma tarjan_links_enter g v s :
  ~ In v (tarjan_pending s) -> tarjan_low_witness g s ->
  tarjan_low_witness g (TarjanVisitor.enter v s).
Proof.
  intros Hfresh Hlinks w low Hget.
  cbn [TarjanVisitor.enter tarjan_low tarjan_disc tarjan_pending] in Hget |- *.
  destruct (Pos.eq_dec w v) as [Heq|Hne].
  - subst w. rewrite PTrie.get_set_same in Hget. injection Hget as Heq. subst low.
    exists (tarjan_clock s), v. rewrite PTrie.get_set_same.
    split; [reflexivity|]. split; [lia|]. split; [now left|].
    split; [reflexivity|apply tarjan_reaches_refl].
  - rewrite PTrie.get_set_other in Hget by exact Hne.
    destruct (Hlinks w low Hget) as [disc [witness [Hdisc [Hbound [Hin [Hnumber Hpath]]]]]].
    assert (Hwitness : witness <> v) by (intro Heq; subst witness; contradiction).
    exists disc, witness. rewrite !PTrie.get_set_other by assumption.
    split; [exact Hdisc|]. split; [exact Hbound|]. split; [now right|auto].
Qed.

Lemma tarjan_closed_enter v s :
  tarjan_closed_low s -> tarjan_closed_low (TarjanVisitor.enter v s).
Proof.
  intros Hclosed w low disc Hin Hnot Hlow Hdisc.
  cbn [TarjanVisitor.enter tarjan_pending tarjan_frames tarjan_low tarjan_disc In]
    in Hin, Hnot, Hlow, Hdisc.
  assert (Hne : w <> v) by (intro Heq; subst w; apply Hnot; now left).
  destruct Hin as [Heq|Hin]; [congruence|].
  rewrite PTrie.get_set_other in Hlow, Hdisc by exact Hne.
  apply (Hclosed w low disc Hin); [|exact Hlow|exact Hdisc].
  intro Hframe. apply Hnot. now right.
Qed.

Lemma tarjan_paths_enter g v s :
  ~ In v (tarjan_pending s) -> tarjan_values_below_clock s ->
  tarjan_pending_paths g s ->
  (forall w, In w (tarjan_pending s) -> tarjan_reaches g w v) ->
  tarjan_pending_paths g (TarjanVisitor.enter v s).
Proof.
  intros Hfresh Hvalues Hpaths Hreach u w a b Hu Hw Hua Hwb Hab.
  cbn [TarjanVisitor.enter tarjan_pending tarjan_disc In] in Hu, Hw, Hua, Hwb.
  destruct Hu as [Hequ|Hu], Hw as [Heqw|Hw].
  - subst u w. apply tarjan_reaches_refl.
  - subst u. rewrite PTrie.get_set_same in Hua. injection Hua as Heq. subst a.
    rewrite PTrie.get_set_other in Hwb by (intro Heq; subst w; contradiction).
    pose proof (proj1 Hvalues w b Hwb). lia.
  - subst w. now apply Hreach.
  - rewrite PTrie.get_set_other in Hua by (intro Heq; subst u; contradiction).
    rewrite PTrie.get_set_other in Hwb by (intro Heq; subst w; contradiction).
    eapply Hpaths; eassumption.
Qed.

Lemma tarjan_links_lower g v number s :
  tarjan_low_witness g s ->
  (exists witness, In witness (tarjan_pending s) /\
    trie_get witness (tarjan_disc s) = Some number /\ tarjan_reaches g v witness) ->
  tarjan_low_witness g (TarjanVisitor.lower v number s).
Proof.
  intros Hlinks [witness [Hin [Hnumber Hreach]]]. unfold TarjanVisitor.lower.
  destruct (trie_get v (tarjan_low s)) as [old|] eqn:Hold; [|exact Hlinks].
  intros w low Hget. cbn [tarjan_low tarjan_disc tarjan_pending] in Hget |- *.
  destruct (Pos.eq_dec w v) as [Heq|Hne].
  - subst w. rewrite PTrie.get_set_same in Hget. injection Hget as Heq. subst low.
    destruct (Hlinks v old Hold) as [disc [prior [Hdisc [Hbound [Hprior [Hprior_number Hprior_path]]]]]].
    destruct (Pos.leb old number) eqn:Htest.
    + apply Pos.leb_le in Htest. rewrite Pos.min_l by exact Htest.
      exists disc, prior. repeat split; assumption.
    + apply Pos.leb_gt in Htest.
      assert (Hle : (number <= old)%positive) by now apply Pos.lt_le_incl.
      rewrite Pos.min_r by exact Hle. apply Pos2Nat.inj_le in Hle.
      exists disc, witness. repeat split; try assumption. lia.
  - rewrite PTrie.get_set_other in Hget by exact Hne. now apply Hlinks.
Qed.

Lemma tarjan_closed_lower v number s :
  tarjan_closed_low s -> tarjan_closed_low (TarjanVisitor.lower v number s).
Proof.
  intro Hclosed. unfold TarjanVisitor.lower.
  destruct (trie_get v (tarjan_low s)) as [old|] eqn:Hold; [|exact Hclosed].
  intros w low disc Hin Hnot Hlow Hdisc.
  cbn [tarjan_pending tarjan_frames tarjan_low tarjan_disc] in Hin, Hnot, Hlow, Hdisc.
  destruct (Pos.eq_dec w v) as [Heq|Hne].
  - subst w. rewrite PTrie.get_set_same in Hlow. injection Hlow as Heq. subst low.
    rewrite Pos2Nat.inj_min. eapply Nat.le_lt_trans; [apply Nat.le_min_l|].
    exact (Hclosed v old disc Hin Hnot Hold Hdisc).
  - rewrite PTrie.get_set_other in Hlow by exact Hne. eapply Hclosed; eassumption.
Qed.

Lemma tarjan_paths_lower g v number s :
  tarjan_pending_paths g s -> tarjan_pending_paths g (TarjanVisitor.lower v number s).
Proof.
  intro Hpaths. unfold TarjanVisitor.lower.
  destruct (trie_get v (tarjan_low s)); exact Hpaths.
Qed.

Lemma tarjan_links_edge g kind u v s :
  tarjan_pending_domains s -> tarjan_low_witness g s -> tarjan_reaches g u v ->
  tarjan_low_witness g (TarjanVisitor.edge kind u v s).
Proof.
  intros Hdomains Hlinks Hreach. destruct kind; cbn [TarjanVisitor.edge]; try exact Hlinks.
  all: destruct (trie_get v (tarjan_active s)) as [[|]|] eqn:Hactive; try exact Hlinks.
  all: destruct (trie_get v (tarjan_disc s)) as [number|] eqn:Hnumber; try exact Hlinks.
  all: apply tarjan_links_lower; [exact Hlinks|].
  all: exists v; split; [now apply (proj1 (proj1 Hdomains v))|auto].
Qed.

Lemma tarjan_closed_edge kind u v s :
  tarjan_closed_low s -> tarjan_closed_low (TarjanVisitor.edge kind u v s).
Proof.
  intro Hclosed. destruct kind; cbn [TarjanVisitor.edge]; try exact Hclosed.
  all: destruct (trie_get v (tarjan_active s)) as [[|]|]; try exact Hclosed.
  all: destruct (trie_get v (tarjan_disc s)); try exact Hclosed.
  all: now apply tarjan_closed_lower.
Qed.

Lemma tarjan_paths_edge g kind u v s :
  tarjan_pending_paths g s -> tarjan_pending_paths g (TarjanVisitor.edge kind u v s).
Proof.
  intro Hpaths. destruct kind; cbn [TarjanVisitor.edge]; try exact Hpaths.
  all: destruct (trie_get v (tarjan_active s)) as [[|]|]; try exact Hpaths.
  all: destruct (trie_get v (tarjan_disc s)); try exact Hpaths.
  all: now apply tarjan_paths_lower.
Qed.

(** Surviving low witnesses cannot lie in the newer popped prefix. *)
Lemma tarjan_links_pop g s root index members tail low active owners frames emitted clock next :
  tarjan_pending_domains s -> tarjan_state_ordered s -> tarjan_low_witness g s ->
  tarjan_pop root index (tarjan_pending s) (tarjan_low s) (tarjan_active s) (tarjan_owners s) =
    (members, tail, low, active, owners) ->
  tarjan_low_witness g
    (TarjanState (tarjan_disc s) low tail active frames emitted owners clock next).
Proof.
  intros Hdomains Horder Hlinks Hpop w number Hget.
  cbn [tarjan_low tarjan_disc tarjan_pending] in Hget |- *.
  destruct (tarjan_pop_lookup _ _ _ _ _ _ _ _ _ _ _ Hpop) as [Hsplit Hlookup].
  specialize (Hlookup w). rewrite (proj1 Hlookup) in Hget.
  destruct (existsb (Pos.eqb w) members) eqn:Hmember; [discriminate|].
  destruct (Hlinks w number Hget)
    as [disc [witness [Hdisc [Hbound [Hin [Hnumber Hpath]]]]]].
  exists disc, witness. split; [exact Hdisc|]. split; [exact Hbound|].
  split; [|auto]. rewrite Hsplit, in_app_iff in Hin.
  destruct Hin as [Hin|Hin]; [|exact Hin].
  assert (Hw : In w tail).
  { assert (Hpending : In w (tarjan_pending s)).
    { apply (proj1 (proj2 Hdomains w)). now exists number. }
    assert (Hnot : ~ In w members).
    { intro Hmem. apply tarjan_positive_existsb in Hmem. congruence. }
    rewrite Hsplit, in_app_iff in Hpending. tauto. }
  pose proof (tarjan_ordered_cross (tarjan_disc s) members tail witness w number disc
    ltac:(unfold tarjan_state_ordered in Horder; now rewrite <- Hsplit)
    Hin Hw Hnumber Hdisc). lia.
Qed.

Lemma tarjan_closed_pop v frames s members tail low active owners emitted clock next :
  tarjan_frames s = v :: frames -> tarjan_frames_embedded s ->
  NoDup (tarjan_pending s) -> tarjan_closed_low s ->
  tarjan_pop v (tarjan_next s) (tarjan_pending s) (tarjan_low s)
    (tarjan_active s) (tarjan_owners s) = (members, tail, low, active, owners) ->
  tarjan_closed_low
    (TarjanState (tarjan_disc s) low tail active frames emitted owners clock next).
Proof.
  intros Hframes Hembed Hunique Hclosed Hpop w number disc Hin Hnot Hlow Hdisc.
  cbn [tarjan_pending tarjan_frames tarjan_low tarjan_disc] in Hin, Hnot, Hlow, Hdisc.
  destruct (tarjan_pop_lookup _ _ _ _ _ _ _ _ _ _ _ Hpop) as [Hsplit Hlookup].
  assert (Hv : In v (tarjan_pending s)).
  { apply (tarjan_embeds_incl _ _ Hembed). rewrite Hframes. now left. }
  pose proof (tarjan_pop_root_member _ _ _ _ _ _ _ _ _ _ _ Hv Hpop) as Hmember.
  assert (Hne : w <> v).
  { intro Heq. subst w. rewrite Hsplit in Hunique.
    exact (tarjan_nodup_app_disjoint members tail Hunique v Hmember Hin). }
  specialize (Hlookup w). rewrite (proj1 Hlookup) in Hlow.
  destruct (existsb (Pos.eqb w) members); [discriminate|].
  apply (Hclosed w number disc); [rewrite Hsplit; apply in_or_app; now right| |exact Hlow|exact Hdisc].
  rewrite Hframes. intros [Heq|Hinside]; [congruence|contradiction].
Qed.

Lemma tarjan_paths_pop g s root index members tail low active owners frames emitted clock next :
  tarjan_pending_paths g s ->
  tarjan_pop root index (tarjan_pending s) (tarjan_low s) (tarjan_active s) (tarjan_owners s) =
    (members, tail, low, active, owners) ->
  tarjan_pending_paths g
    (TarjanState (tarjan_disc s) low tail active frames emitted owners clock next).
Proof.
  intros Hpaths Hpop u v a b Hu Hv Hua Hvb Hab.
  cbn [tarjan_pending tarjan_disc] in Hu, Hv, Hua, Hvb.
  pose proof (proj1 (tarjan_pop_lookup _ _ _ _ _ _ _ _ _ _ _ Hpop)) as Hsplit.
  apply (Hpaths u v a b); try assumption; rewrite Hsplit; apply in_or_app; now right.
Qed.

Lemma tarjan_links_leave g v frames s :
  tarjan_frames s = v :: frames -> tarjan_frames_embedded s ->
  tarjan_pending_domains s -> tarjan_state_ordered s -> tarjan_low_witness g s ->
  (match frames with [] => True | parent :: _ => tarjan_reaches g parent v end) ->
  tarjan_low_witness g (TarjanVisitor.leave v s).
Proof.
  intros Hframes Hembed Hdomains Horder Hlinks Hparent.
  assert (Hv : In v (tarjan_pending s)).
  { apply (tarjan_embeds_incl _ _ Hembed). rewrite Hframes. now left. }
  destruct (proj2 (proj2 Hdomains v) Hv) as [low Hlow].
  destruct (Hlinks v low Hlow)
    as [disc [witness [Hdisc [Hbound [Hin [Hnumber Hreach]]]]]].
  unfold TarjanVisitor.leave. rewrite Hframes, Hlow, Hdisc. cbn beta iota zeta.
  destruct (Pos.eqb low disc).
  - destruct (tarjan_pop v (tarjan_next s) (tarjan_pending s) (tarjan_low s)
      (tarjan_active s) (tarjan_owners s))
      as [[[[members tail] lows] actives] owners] eqn:Hpop.
    eapply tarjan_links_pop; eassumption.
  - destruct frames as [|parent frames]; [exact Hlinks|].
    apply tarjan_links_lower; [exact Hlinks|].
    exists witness. split; [exact Hin|]. split; [exact Hnumber|].
    eapply tarjan_reaches_trans; eassumption.
Qed.

Lemma tarjan_closed_leave g v frames s :
  tarjan_frames s = v :: frames -> tarjan_frames_embedded s ->
  NoDup (tarjan_pending s) -> tarjan_pending_domains s ->
  tarjan_low_witness g s -> tarjan_closed_low s ->
  tarjan_closed_low (TarjanVisitor.leave v s).
Proof.
  intros Hframes Hembed Hunique Hdomains Hlinks Hclosed.
  assert (Hv : In v (tarjan_pending s)).
  { apply (tarjan_embeds_incl _ _ Hembed). rewrite Hframes. now left. }
  destruct (proj2 (proj2 Hdomains v) Hv) as [low Hlow].
  destruct (Hlinks v low Hlow) as [disc [_ [Hdisc [Hbound _]]]].
  unfold TarjanVisitor.leave. rewrite Hframes, Hlow, Hdisc. cbn beta iota zeta.
  destruct (Pos.eqb low disc) eqn:Heq.
  - destruct (tarjan_pop v (tarjan_next s) (tarjan_pending s) (tarjan_low s)
      (tarjan_active s) (tarjan_owners s))
      as [[[[members tail] lows] actives] owners] eqn:Hpop.
    eapply tarjan_closed_pop; eassumption.
  - apply Pos.eqb_neq in Heq.
    assert (Hstrict : Pos.to_nat low < Pos.to_nat disc).
    { assert (Pos.to_nat low <> Pos.to_nat disc) by (intro Hsame; apply Heq; now apply Pos2Nat.inj).
      lia. }
    assert (Hbase : tarjan_closed_low
      (TarjanState (tarjan_disc s) (tarjan_low s) (tarjan_pending s) (tarjan_active s)
        frames (tarjan_emitted s) (tarjan_owners s) (tarjan_clock s) (tarjan_next s))).
    { intros w number d Hin Hnot Hwl Hwd.
      cbn [tarjan_pending tarjan_frames tarjan_low tarjan_disc] in Hin, Hnot, Hwl, Hwd.
      destruct (Pos.eq_dec w v) as [Hsame|Hne].
      - subst w. rewrite Hlow in Hwl. rewrite Hdisc in Hwd.
        injection Hwl as Heql. injection Hwd as Heqd. now subst number d.
      - apply (Hclosed w number d Hin); [|exact Hwl|exact Hwd].
        rewrite Hframes. intros [Hsame|Hinside]; [congruence|contradiction]. }
    destruct frames as [|parent frames]; [exact Hbase|]. now apply tarjan_closed_lower.
Qed.

Lemma tarjan_paths_leave g v s :
  tarjan_pending_paths g s -> tarjan_pending_paths g (TarjanVisitor.leave v s).
Proof.
  intro Hpaths. unfold TarjanVisitor.leave.
  destruct (trie_get v (tarjan_low s)) as [low|]; [|exact Hpaths].
  destruct (trie_get v (tarjan_disc s)) as [disc|]; [|exact Hpaths].
  destruct (Pos.eqb low disc).
  - destruct (tarjan_pop v (tarjan_next s) (tarjan_pending s) (tarjan_low s)
      (tarjan_active s) (tarjan_owners s))
      as [[[[members tail] lows] actives] owners] eqn:Hpop.
    eapply tarjan_paths_pop; eassumption.
  - destruct (match tarjan_frames s with [] => [] | _ :: rest => rest end)
      as [|parent frames]; [exact Hpaths|]. now apply tarjan_paths_lower.
Qed.
(** Every popped vertex is at least as new as the root of that pop. *)
Lemma tarjan_pop_number root index pending disc low active owners members tail lows actives assigned
    v root_number number :
  tarjan_ordered disc pending -> In root pending ->
  trie_get root disc = Some root_number -> trie_get v disc = Some number ->
  tarjan_pop root index pending low active owners = (members, tail, lows, actives, assigned) ->
  In v members -> Pos.to_nat root_number <= Pos.to_nat number.
Proof.
  revert low active owners members tail lows actives assigned.
  induction pending as [|head pending IH];
    intros low active owners members tail lows actives assigned Horder Hroot Hrootn Hnumber Hpop Hin.
  - contradiction.
  - cbn [tarjan_ordered] in Horder. destruct Horder as [Htail Hhead].
    cbn [tarjan_pop] in Hpop. destruct (Pos.eqb head root) eqn:Hsame.
    + apply Pos.eqb_eq in Hsame. subst head. inversion Hpop; subst.
      cbn [In] in Hin. destruct Hin as [Heq|Hfalse]; [subst v|contradiction].
      rewrite Hrootn in Hnumber. injection Hnumber as Heq. subst number. lia.
    + apply Pos.eqb_neq in Hsame.
      assert (Hroot_tail : In root pending) by (cbn [In] in Hroot; tauto).
      destruct (tarjan_pop root index pending (PTrieCode.remove head low)
        (PTrieCode.remove head active) (PTrieCode.set head index owners))
        as [[[[popped remaining] low'] active'] owners'] eqn:Hrec.
      inversion Hpop; subst members tail lows actives assigned. cbn [In] in Hin.
      destruct Hin as [Heq|Hin].
      * subst v. pose proof (Hhead root number root_number Hroot_tail Hnumber Hrootn). lia.
      * eapply IH; eassumption.
Qed.

Lemma tarjan_emission_strong g v frames s members tail lows actives owners :
  tarjan_frames s = v :: frames -> tarjan_frames_embedded s ->
  tarjan_state_ordered s -> tarjan_pending_domains s ->
  tarjan_low_witness g s -> tarjan_closed_low s -> tarjan_pending_paths g s ->
  tarjan_pop v (tarjan_next s) (tarjan_pending s) (tarjan_low s)
    (tarjan_active s) (tarjan_owners s) = (members, tail, lows, actives, owners) ->
  forall u w, In u members -> In w members ->
    tarjan_reaches g u w /\ tarjan_reaches g w u.
Proof.
  intros Hframes Hembed Horder Hdomains Hlinks Hclosed Hpaths Hpop.
  pose proof (proj1 (tarjan_pop_lookup _ _ _ _ _ _ _ _ _ _ _ Hpop)) as Hsplit.
  assert (Hv : In v (tarjan_pending s)).
  { apply (tarjan_embeds_incl _ _ Hembed). rewrite Hframes. now left. }
  destruct (proj2 (proj2 Hdomains v) Hv) as [low Hlow].
  destruct (Hlinks v low Hlow) as [dv [_ [Hvd _]]].
  assert (Hroot_paths : forall w, In w members -> tarjan_reaches g v w /\ tarjan_reaches g w v).
  { intros w Hw. assert (Hpending : In w (tarjan_pending s)).
    { rewrite Hsplit. apply in_or_app. now left. }
    destruct (proj2 (proj2 Hdomains w) Hpending) as [wl Hwl].
    destruct (Hlinks w wl Hwl) as [dw [_ [Hwd _]]]. split.
    - apply (Hpaths v w dv dw Hv Hpending Hvd Hwd).
      exact (tarjan_pop_number v (tarjan_next s) (tarjan_pending s) (tarjan_disc s)
        (tarjan_low s) (tarjan_active s) (tarjan_owners s) members tail lows actives owners
        w dv dw Horder Hv Hvd Hwd Hpop Hw).
    - exact (tarjan_pending_current g v frames s Hframes Hembed Horder Hdomains
        Hlinks Hclosed Hpaths w Hpending). }
  intros u w Hu Hw. destruct (Hroot_paths u Hu) as [Hvu Huv].
  destruct (Hroot_paths w Hw) as [Hvw Hwv].
  split; eapply tarjan_reaches_trans; eassumption.
Qed.

Definition tarjan_strong_output g s : Prop :=
  forall block, In block (tarjan_emitted s) -> forall u v,
    In u block -> In v block -> tarjan_reaches g u v /\ tarjan_reaches g v u.

Lemma tarjan_strong_enter g v s :
  tarjan_strong_output g s -> tarjan_strong_output g (TarjanVisitor.enter v s).
Proof. exact (fun H => H). Qed.

Lemma tarjan_strong_lower g v number s :
  tarjan_strong_output g s -> tarjan_strong_output g (TarjanVisitor.lower v number s).
Proof.
  intro Hstrong. unfold TarjanVisitor.lower.
  destruct (trie_get v (tarjan_low s)); exact Hstrong.
Qed.

Lemma tarjan_strong_edge g kind u v s :
  tarjan_strong_output g s -> tarjan_strong_output g (TarjanVisitor.edge kind u v s).
Proof.
  intro Hstrong. destruct kind; cbn [TarjanVisitor.edge]; try exact Hstrong.
  all: destruct (trie_get v (tarjan_active s)) as [[|]|]; try exact Hstrong.
  all: destruct (trie_get v (tarjan_disc s)); try exact Hstrong.
  all: now apply tarjan_strong_lower.
Qed.

Lemma tarjan_strong_leave g v frames s :
  tarjan_frames s = v :: frames -> tarjan_frames_embedded s ->
  tarjan_state_ordered s -> tarjan_pending_domains s ->
  tarjan_low_witness g s -> tarjan_closed_low s -> tarjan_pending_paths g s ->
  tarjan_strong_output g s -> tarjan_strong_output g (TarjanVisitor.leave v s).
Proof.
  intros Hframes Hembed Horder Hdomains Hlinks Hclosed Hpaths Hstrong.
  unfold TarjanVisitor.leave.
  destruct (trie_get v (tarjan_low s)) as [low|]; [|exact Hstrong].
  destruct (trie_get v (tarjan_disc s)) as [disc|]; [|exact Hstrong].
  destruct (Pos.eqb low disc).
  - destruct (tarjan_pop v (tarjan_next s) (tarjan_pending s) (tarjan_low s)
      (tarjan_active s) (tarjan_owners s))
      as [[[[members tail] lows] actives] owners] eqn:Hpop.
    intros block Hblock u w Hu Hw. cbn [tarjan_emitted In] in Hblock.
    destruct Hblock as [Heq|Hin].
    + subst block. eapply tarjan_emission_strong; eassumption.
    + eapply Hstrong; eassumption.
  - destruct (match tarjan_frames s with [] => [] | _ :: rest => rest end)
      as [|parent frames']; [exact Hstrong|]. now apply tarjan_strong_lower.
Qed.
(** A graph-valid nested walk retains the parent edge when entering a child. *)
Inductive tarjan_walk (g : digraph) : list positive -> list event -> list positive -> Prop :=
  | tarjan_walk_nil : forall stack, tarjan_walk g stack [] stack
  | tarjan_walk_enter : forall stack v rest final,
      (match stack with [] => True | parent :: _ => edge g parent v end) ->
      tarjan_walk g (v :: stack) rest final -> tarjan_walk g stack (Enter v :: rest) final
  | tarjan_walk_leave : forall stack v rest final,
      tarjan_walk g stack rest final -> tarjan_walk g (v :: stack) (Leave v :: rest) final
  | tarjan_walk_edge : forall stack kind u v rest final,
      edge g u v -> tarjan_walk g (u :: stack) rest final ->
      tarjan_walk g (u :: stack) (Edge kind u v :: rest) final.

Lemma tarjan_walk_app g initial first middle last final :
  tarjan_walk g initial first middle -> tarjan_walk g middle last final ->
  tarjan_walk g initial (first ++ last) final.
Proof.
  intros Hfirst Hlast. induction Hfirst; cbn [app]; eauto using tarjan_walk.
Qed.

Lemma tarjan_walk_stack g initial events final :
  tarjan_walk g initial events final -> trace_stack initial events final.
Proof. intro Hwalk. induction Hwalk; constructor; assumption. Qed.

Lemma tarjan_walk_prefix g initial prefix suffix final :
  tarjan_walk g initial (prefix ++ suffix) final ->
  exists middle, tarjan_walk g initial prefix middle /\ tarjan_walk g middle suffix final.
Proof.
  revert initial. induction prefix as [|e prefix IH]; intros initial Hwalk.
  - exists initial. split; [constructor|exact Hwalk].
  - cbn [app] in Hwalk. inversion Hwalk; subst.
    + match goal with H : tarjan_walk _ _ (prefix ++ suffix) _ |- _ =>
        destruct (IH _ H) as [middle [Hprefix Hsuffix]] end.
      exists middle. split; [eapply tarjan_walk_enter; eassumption|exact Hsuffix].
    + match goal with H : tarjan_walk _ _ (prefix ++ suffix) _ |- _ =>
        destruct (IH _ H) as [middle [Hprefix Hsuffix]] end.
      exists middle. split; [now apply tarjan_walk_leave|exact Hsuffix].
    + match goal with H : tarjan_walk _ _ (prefix ++ suffix) _ |- _ =>
        destruct (IH _ H) as [middle [Hprefix Hsuffix]] end.
      exists middle. split; [eapply tarjan_walk_edge; eassumption|exact Hsuffix].
Qed.

Lemma tarjan_walk_graph first second initial events final :
  (forall u v, edge first u v -> edge second u v) ->
  tarjan_walk first initial events final -> tarjan_walk second initial events final.
Proof.
  intros Hedges Hwalk. induction Hwalk.
  - constructor.
  - apply tarjan_walk_enter; [|exact IHHwalk]. destruct stack; [exact I|now apply Hedges].
  - now apply tarjan_walk_leave.
  - apply tarjan_walk_edge; [now apply Hedges|exact IHHwalk].
Qed.

Scheme tarjan_dfs_visit_ind := Induction for dfs_visit Sort Prop
with tarjan_dfs_rows_ind := Induction for dfs_rows Sort Prop.
Combined Scheme tarjan_dfs_mutual_ind from tarjan_dfs_visit_ind, tarjan_dfs_rows_ind.

Lemma tarjan_dfs_walk g :
  (forall active seen v es final, dfs_visit g active seen v es final ->
    (match active with [] => True | parent :: _ => edge g parent v end) ->
    tarjan_walk g active es active) /\
  (forall active seen u row es final, dfs_rows g active seen u row es final ->
    forall stack, active = u :: stack -> (forall v, In v row -> edge g u v) ->
    tarjan_walk g active es active).
Proof.
  apply tarjan_dfs_mutual_ind.
  - intros active seen v inside final Hfresh Hrows IH Hparent.
    apply tarjan_walk_enter; [exact Hparent|]. eapply tarjan_walk_app.
    + apply (IH active eq_refl). intros w Hin. exact Hin.
    + apply tarjan_walk_leave. constructor.
  - intros active seen u stack Hactive Hrow. constructor.
  - intros active seen u v rest inside middle outside final Hfresh Hvisit IHvisit Hrows IHrows
      stack Hactive Hrow. subst active.
    apply tarjan_walk_edge; [apply Hrow; now left|]. eapply tarjan_walk_app.
    + apply IHvisit. apply Hrow. now left.
    + apply (IHrows stack eq_refl). intros w Hin. apply Hrow. now right.
  - intros active seen u v rest kind outside final Hseen Hkind Hrows IH stack Hactive Hrow.
    subst active. apply tarjan_walk_edge; [apply Hrow; now left|].
    apply (IH stack eq_refl). intros w Hin. apply Hrow. now right.
Qed.

Lemma tarjan_dfs_roots_walk g seen roots es final :
  dfs_roots g seen roots es final -> tarjan_walk g [] es [].
Proof.
  intro Hroots. induction Hroots.
  - constructor.
  - exact IHHroots.
  - eapply tarjan_walk_app; [|exact IHHroots].
    eapply (proj1 (tarjan_dfs_walk g)); [eassumption|exact I].
Qed.

Lemma scc_trace_walk g : tarjan_walk (base g) [] (scc_trace g) [].
Proof.
  eapply tarjan_walk_graph with (first := base (scc_graph g)).
  - intros u v Huv. unfold edge in *. rewrite scc_graph_succs in Huv.
    destruct (existsb (Pos.eqb u) (nodes g)); [|contradiction].
    apply filter_In in Huv. tauto.
  - unfold scc_trace.
    destruct (prepared_search_depth_first_closed (scc_graph g) (nodes g)
      (scc_graph_counts g) (scc_search_closed g)
      ltac:(intros r Hr; now rewrite scc_graph_nodes)) as [final Hdfs].
    now apply tarjan_dfs_roots_walk in Hdfs.
Qed.

Fixpoint tarjan_frame_edges g frames : Prop :=
  match frames with
  | [] => True
  | v :: rest =>
      (match rest with [] => True | parent :: _ => edge g parent v end) /\
      tarjan_frame_edges g rest
  end.

Record tarjan_semantic (g : digraph) (s : tarjan_state) : Prop := TarjanSemantic {
  tarjan_semantic_domains : tarjan_pending_domains s;
  tarjan_semantic_order : tarjan_state_ordered s;
  tarjan_semantic_frames : tarjan_frames_embedded s;
  tarjan_semantic_values : tarjan_values_below_clock s;
  tarjan_semantic_links : tarjan_low_witness g s;
  tarjan_semantic_closed : tarjan_closed_low s;
  tarjan_semantic_paths : tarjan_pending_paths g s;
  tarjan_semantic_tree : tarjan_frame_edges g (tarjan_frames s);
  tarjan_semantic_output : tarjan_strong_output g s
}.

Lemma tarjan_semantic_initial g : tarjan_semantic g tarjan_initial.
Proof.
  constructor.
  - apply tarjan_pending_domains_initial.
  - exact I.
  - constructor.
  - apply tarjan_values_initial.
  - intros w low Hget. cbn [tarjan_initial tarjan_low] in Hget. rewrite PTrie.get_empty in Hget. discriminate.
  - intros w low disc Hfalse. contradiction.
  - intros u v a b Hfalse. contradiction.
  - exact I.
  - intros block Hfalse. contradiction.
Qed.

Lemma tarjan_semantic_enter g v s :
  tarjan_semantic g s -> ~ In v (tarjan_pending s) ->
  (match tarjan_frames s with [] => True | parent :: _ => edge g parent v end) ->
  tarjan_semantic g (TarjanVisitor.enter v s).
Proof.
  intros [Hdomains Horder Hembed Hvalues Hlinks Hclosed Hpaths Htree Hstrong] Hfresh Hparent.
  assert (Hreach : forall w, In w (tarjan_pending s) -> tarjan_reaches g w v).
  { intros w Hw. destruct (tarjan_frames s) as [|parent frames] eqn:Hframes.
    - destruct (proj2 (proj2 Hdomains w) Hw) as [low Hlow].
      destruct (Hlinks w low Hlow) as [disc [_ [Hdisc _]]].
      destruct (tarjan_pending_support g s Hdomains Hlinks Hclosed w disc Hw Hdisc)
        as [ancestor [number [Hancestor _]]]. rewrite Hframes in Hancestor. contradiction.
    - eapply tarjan_reaches_trans.
      + eapply tarjan_pending_current; eassumption.
      + apply tarjan_reaches_edge. exact Hparent. }
  constructor.
  - now apply tarjan_pending_domains_enter.
  - now apply tarjan_ordered_enter.
  - now apply tarjan_embeds_enter.
  - exact (tarjan_values_fold [Enter v] s Hvalues).
  - now apply tarjan_links_enter.
  - now apply tarjan_closed_enter.
  - now apply tarjan_paths_enter.
  - change ((match tarjan_frames s with [] => True | parent :: _ => edge g parent v end) /\
      tarjan_frame_edges g (tarjan_frames s)). auto.
  - now apply tarjan_strong_enter.
Qed.

Lemma tarjan_semantic_edge g kind u v s :
  tarjan_semantic g s -> edge g u v -> tarjan_semantic g (TarjanVisitor.edge kind u v s).
Proof.
  intros [Hdomains Horder Hembed Hvalues Hlinks Hclosed Hpaths Htree Hstrong] Huv.
  constructor.
  - now apply tarjan_pending_domains_edge.
  - now apply tarjan_ordered_edge.
  - now apply tarjan_embeds_edge.
  - exact (tarjan_values_fold [Edge kind u v] s Hvalues).
  - apply tarjan_links_edge; [exact Hdomains|exact Hlinks|now apply tarjan_reaches_edge].
  - now apply tarjan_closed_edge.
  - now apply tarjan_paths_edge.
  - pose proof (proj2 (proj2 (tarjan_event_metadata (Edge kind u v) s))) as Hframes.
    cbn [visit_event] in Hframes. now rewrite Hframes.
  - now apply tarjan_strong_edge.
Qed.

Lemma tarjan_semantic_leave g v frames s :
  tarjan_semantic g s -> tarjan_frames s = v :: frames -> NoDup (tarjan_pending s) ->
  tarjan_semantic g (TarjanVisitor.leave v s).
Proof.
  intros [Hdomains Horder Hembed Hvalues Hlinks Hclosed Hpaths Htree Hstrong] Hframes Hunique.
  assert (Hparent : match frames with [] => True | parent :: _ => tarjan_reaches g parent v end).
  { rewrite Hframes in Htree. cbn [tarjan_frame_edges] in Htree.
    destruct frames; [exact I|apply tarjan_reaches_edge; exact (proj1 Htree)]. }
  constructor.
  - now apply tarjan_pending_domains_leave.
  - now apply tarjan_ordered_leave.
  - eapply tarjan_embeds_leave; eassumption.
  - exact (tarjan_values_fold [Leave v] s Hvalues).
  - eapply tarjan_links_leave; eassumption.
  - eapply tarjan_closed_leave; eassumption.
  - now apply tarjan_paths_leave.
  - pose proof (proj2 (proj2 (tarjan_event_metadata (Leave v) s))) as Hnext.
    cbn [visit_event] in Hnext. rewrite Hnext, Hframes. cbn beta iota zeta.
    rewrite Hframes in Htree. exact (proj2 Htree).
  - eapply tarjan_strong_leave; eassumption.
Qed.

(** The future entry bag gives exactly the freshness needed at every prefix. *)
Lemma tarjan_walk_semantic g initial events final : tarjan_walk g initial events final ->
  forall s, tarjan_frames s = initial ->
  NoDup (rev (entered events) ++ tarjan_bag s) -> tarjan_semantic g s ->
  let result := fold_events TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge events s in
  tarjan_semantic g result /\ tarjan_frames result = final.
Proof.
  intro Hwalk. induction Hwalk; intros s Hframes Hunique Hsem; cbn zeta.
  - cbn [fold_events fold_left]. auto.
  - assert (Hfresh : ~ In v (tarjan_pending s)).
    { intros Hin. pose proof Hunique as Hnew.
      cbn [entered rev] in Hnew. rewrite <- app_assoc in Hnew. cbn [app] in Hnew.
      apply NoDup_app_remove_l in Hnew. inversion Hnew as [|v' bag Hnot Htail]; subst v' bag.
      apply Hnot. unfold tarjan_bag. apply in_or_app. now left. }
    cbn [fold_events fold_left visit_event]. apply IHHwalk.
    + cbn [TarjanVisitor.enter tarjan_frames]. now rewrite Hframes.
    + exact (tarjan_future_unique (Enter v) rest s Hunique).
    + apply tarjan_semantic_enter; [exact Hsem|exact Hfresh|now rewrite Hframes].
  - cbn [fold_events fold_left visit_event]. apply IHHwalk.
    + pose proof (proj2 (proj2 (tarjan_event_metadata (Leave v) s))) as Hnext.
      cbn [visit_event] in Hnext. now rewrite Hframes in Hnext.
    + exact (tarjan_future_unique (Leave v) rest s Hunique).
    + eapply tarjan_semantic_leave; [exact Hsem|exact Hframes|].
      exact (tarjan_current_pending_unique _ _ Hunique).
  - cbn [fold_events fold_left visit_event]. apply IHHwalk.
    + pose proof (proj2 (proj2 (tarjan_event_metadata (Edge kind u v) s))) as Hnext.
      cbn [visit_event] in Hnext. now rewrite Hframes in Hnext.
    + exact (tarjan_future_unique (Edge kind u v) rest s Hunique).
    + now apply tarjan_semantic_edge.
Qed.

Lemma scc_prefix_semantic g prefix suffix : scc_trace g = prefix ++ suffix ->
  tarjan_semantic (base g)
    (fold_events TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge prefix tarjan_initial).
Proof.
  intro Htrace. pose proof (scc_trace_walk g) as Hwalk. rewrite Htrace in Hwalk.
  destruct (tarjan_walk_prefix (base g) [] prefix suffix [] Hwalk)
    as [middle [Hprefix Hsuffix]].
  assert (Hfuture : NoDup (rev (entered prefix) ++ tarjan_bag tarjan_initial)).
  { cbn [tarjan_bag tarjan_initial tarjan_pending tarjan_emitted concat app].
    rewrite app_nil_r. apply NoDup_rev. now apply (scc_trace_prefix_unique g prefix suffix). }
  exact (proj1 (tarjan_walk_semantic (base g) [] prefix middle Hprefix
    tarjan_initial eq_refl Hfuture (tarjan_semantic_initial (base g)))).
Qed.

Lemma scc_final_owner_listed g v i :
  trie_get v (tarjan_owners
    (fold_events TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge
      (scc_trace g) tarjan_initial)) = Some i -> In v (nodes g).
Proof.
  intro Howner.
  apply (tarjan_owners_indexed_fold (scc_trace g) (scc_trace_unique g) v i) in Howner.
  destruct Howner as [block [Hblock Hin]].
  apply (proj1 (scc_trace_entered g v)).
  eapply Permutation_in; [apply tarjan_complete_components;
    [apply scc_trace_unique|apply scc_trace_nested]|].
  apply in_concat. exists block. split; [eapply nth_error_In; exact Hblock|exact Hin].
Qed.

Lemma scc_final_owner_present g v : In v (nodes g) ->
  exists i, trie_get v (tarjan_owners
    (fold_events TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge
      (scc_trace g) tarjan_initial)) = Some i.
Proof.
  intro Hin. apply (proj2 (scc_trace_entered g v)) in Hin.
  pose proof (tarjan_complete_components (scc_trace g)
    (scc_trace_unique g) (scc_trace_nested g)) as Hcomponents.
  assert (Hmember : In v (concat (rev (tarjan_emitted
    (fold_events TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge
      (scc_trace g) tarjan_initial))))).
  { eapply Permutation_in; [apply Permutation_sym; exact Hcomponents|exact Hin]. }
  apply in_concat in Hmember. destruct Hmember as [block [Hblock Hinblock]].
  apply In_nth_error in Hblock. destruct Hblock as [n Hnth].
  exists (Pos.of_succ_nat n).
  apply (tarjan_owners_indexed_fold (scc_trace g) (scc_trace_unique g) v (Pos.of_succ_nat n)).
  exists block. rewrite SuccNat2Pos.id_succ. cbn [Nat.pred]. auto.
Qed.

Lemma scc_same_owner_strong g u v i :
  trie_get u (tarjan_owners
    (fold_events TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge
      (scc_trace g) tarjan_initial)) = Some i ->
  trie_get v (tarjan_owners
    (fold_events TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge
      (scc_trace g) tarjan_initial)) = Some i ->
  mutually_reachable (base g) u v.
Proof.
  intros Hu Hv.
  apply (tarjan_owners_indexed_fold (scc_trace g) (scc_trace_unique g) u i) in Hu.
  apply (tarjan_owners_indexed_fold (scc_trace g) (scc_trace_unique g) v i) in Hv.
  destruct Hu as [block [Hblock Hin_u]]. destruct Hv as [other [Hother Hin_v]].
  rewrite Hblock in Hother. injection Hother as Heq. subst other.
  pose proof (scc_prefix_semantic g (scc_trace g) [] ltac:(now rewrite app_nil_r)) as Hsem.
  pose proof (tarjan_semantic_output _ _ Hsem) as Hstrong.
  apply (Hstrong block); [|exact Hin_u|exact Hin_v].
  assert (Hrev : Permutation
    (rev (tarjan_emitted (fold_events TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge
      (scc_trace g) tarjan_initial)))
    (tarjan_emitted (fold_events TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge
      (scc_trace g) tarjan_initial))) by (apply Permutation_sym; apply Permutation_rev).
  eapply Permutation_in; [exact Hrev|]. eapply nth_error_In; exact Hblock.
Qed.

Module SccCode <: SCC_OPS.
  Definition run (g : prepared) : scc :=
    let result := fold_events TarjanVisitor.enter TarjanVisitor.leave TarjanVisitor.edge
      (scc_trace g) tarjan_initial in
    Scc (tarjan_owners result) (rev_append (tarjan_emitted result) []).
End SccCode.

Module TarjanFrontierFacts.

(** Newer pending low links are represented by the source or a newer open witness. *)
Definition frontier open (s : tarjan_state) : Prop :=
  forall a w da dw la lw, In a open -> In w (tarjan_pending s) ->
    trie_get a (tarjan_disc s) = Some da -> trie_get w (tarjan_disc s) = Some dw ->
    trie_get a (tarjan_low s) = Some la -> trie_get w (tarjan_low s) = Some lw ->
    Pos.to_nat da <= Pos.to_nat dw ->
    Pos.to_nat la <= Pos.to_nat lw \/
    exists b db lb, In b open /\ Pos.to_nat da < Pos.to_nat db /\
      Pos.to_nat db <= Pos.to_nat dw /\ trie_get b (tarjan_disc s) = Some db /\
      trie_get b (tarjan_low s) = Some lb /\ Pos.to_nat lb <= Pos.to_nat lw.

Lemma initial_frontier : frontier [] tarjan_initial.
Proof. intros a w da dw la lw Hfalse. contradiction. Qed.

Lemma open_head_number v open s a da dv :
  tarjan_embeds (v :: open) (tarjan_pending s) -> tarjan_state_ordered s ->
  In a open -> trie_get a (tarjan_disc s) = Some da ->
  trie_get v (tarjan_disc s) = Some dv -> Pos.to_nat da < Pos.to_nat dv.
Proof.
  intros Hembed Horder Ha Had Hvd.
  pose proof (tarjan_ordered_embeds _ _ _ Hembed Horder) as Hframes.
  exact (proj2 Hframes a dv da Ha Hvd Had).
Qed.

Lemma top_bound v open s w dv dw lv lw :
  tarjan_embeds (v :: open) (tarjan_pending s) -> tarjan_state_ordered s ->
  frontier (v :: open) s -> In w (tarjan_pending s) ->
  trie_get v (tarjan_disc s) = Some dv -> trie_get w (tarjan_disc s) = Some dw ->
  trie_get v (tarjan_low s) = Some lv -> trie_get w (tarjan_low s) = Some lw ->
  Pos.to_nat dv <= Pos.to_nat dw -> Pos.to_nat lv <= Pos.to_nat lw.
Proof.
  intros Hembed Horder Hfrontier Hw Hvd Hwd Hvl Hwl Hbound.
  destruct (Hfrontier v w dv dw lv lw (or_introl eq_refl) Hw Hvd Hwd Hvl Hwl Hbound)
    as [Hle|[b [db [lb [Hb [Hvb [_ [Hbd _]]]]]]]]; [exact Hle|].
  destruct Hb as [Heq|Hb].
  - subst b. rewrite Hvd in Hbd. injection Hbd as Heq. subst db. lia.
  - pose proof (open_head_number v open s b db dv Hembed Horder Hb Hbd Hvd). lia.
Qed.

Lemma low_set_bound (links : ptrie positive) v old n b lb :
  trie_get v links = Some old -> trie_get b links = Some lb ->
  exists next, trie_get b (PTrieCode.set v (Pos.min old n) links) = Some next /\
    Pos.to_nat next <= Pos.to_nat lb.
Proof.
  intros Hold Hb. destruct (Pos.eq_dec b v) as [Heq|Hne].
  - subst b. rewrite Hold in Hb. injection Hb as Heq. subst lb.
    exists (Pos.min old n). rewrite PTrie.get_set_same.
    split; [reflexivity|]. rewrite Pos2Nat.inj_min. apply Nat.le_min_l.
  - exists lb. rewrite PTrie.get_set_other by exact Hne. split; [exact Hb|lia].
Qed.

Lemma low_set_inverse (links : ptrie positive) v old n a la :
  trie_get v links = Some old ->
  trie_get a (PTrieCode.set v (Pos.min old n) links) = Some la ->
  exists prior, trie_get a links = Some prior /\ Pos.to_nat la <= Pos.to_nat prior.
Proof.
  intros Hold Ha. destruct (Pos.eq_dec a v) as [Heq|Hne].
  - subst a. rewrite PTrie.get_set_same in Ha. injection Ha as Heq. subst la.
    exists old. split; [exact Hold|]. rewrite Pos2Nat.inj_min. apply Nat.le_min_l.
  - rewrite PTrie.get_set_other in Ha by exact Hne. exists la. split; [exact Ha|lia].
Qed.

Lemma lower_frontier v open s n :
  tarjan_embeds (v :: open) (tarjan_pending s) -> tarjan_state_ordered s ->
  frontier (v :: open) s -> frontier (v :: open) (TarjanVisitor.lower v n s).
Proof.
  intros Hembed Horder Hfrontier. unfold TarjanVisitor.lower.
  destruct (trie_get v (tarjan_low s)) as [old|] eqn:Hold; [|exact Hfrontier].
  intros a w da dw la lw Ha Hw Had Hwd Hal Hwl Hbound.
  cbn [tarjan_pending tarjan_disc tarjan_low] in *.
  destruct (Pos.eq_dec w v) as [Heq|Hwne].
  - subst w. rewrite PTrie.get_set_same in Hwl. injection Hwl as Heq. subst lw.
    destruct (Pos.eq_dec a v) as [Heq|Hane].
    + subst a. rewrite PTrie.get_set_same in Hal. injection Hal as Heq. subst la. left. lia.
    + right. exists v, dw, (Pos.min old n). split; [now left|]. split.
      * apply (open_head_number v open s a da dw Hembed Horder);
          [destruct Ha as [Heq|Ha]; [congruence|exact Ha]|exact Had|exact Hwd].
      * split; [lia|]. split; [exact Hwd|]. rewrite PTrie.get_set_same.
        split; [reflexivity|lia].
  - rewrite PTrie.get_set_other in Hwl by exact Hwne.
    destruct (Pos.eq_dec a v) as [Heq|Hane].
    + subst a. rewrite PTrie.get_set_same in Hal. injection Hal as Heq. subst la. left.
      rewrite Pos2Nat.inj_min. eapply Nat.le_trans; [apply Nat.le_min_l|].
      exact (top_bound v open s w da dw old lw Hembed Horder Hfrontier Hw
        Had Hwd Hold Hwl Hbound).
    + rewrite PTrie.get_set_other in Hal by exact Hane.
      destruct (Hfrontier a w da dw la lw Ha Hw Had Hwd Hal Hwl Hbound)
        as [Hle|[b [db [lb [Hb [Hab [Hbw [Hbd [Hbl Hle]]]]]]]]]; [now left|].
      destruct (low_set_bound _ v old n b lb Hold Hbl) as [next [Hnext Hnext_le]].
      right. exists b, db, next. repeat split; try assumption. lia.
Qed.

Lemma fresh_open open s v :
  tarjan_embeds open (tarjan_pending s) -> ~ In v (tarjan_pending s) -> ~ In v open.
Proof. intros Hembed Hfresh Hin. apply Hfresh. now apply (tarjan_embeds_incl _ _ Hembed). Qed.

Lemma enter_frontier open s v :
  tarjan_embeds open (tarjan_pending s) -> tarjan_values_below_clock s -> frontier open s ->
  ~ In v (tarjan_pending s) -> frontier (v :: open) (TarjanVisitor.enter v s).
Proof.
  intros Hembed Hvalues Hfrontier Hfresh a w da dw la lw Ha Hw Had Hwd Hal Hwl Hbound.
  cbn [TarjanVisitor.enter tarjan_pending tarjan_disc tarjan_low In] in *.
  destruct Hw as [Heqw|Hw], Ha as [Heqa|Ha].
  - subst w a. rewrite PTrie.get_set_same in Hal, Hwl.
    injection Hal as Heql. injection Hwl as Heqw. subst la lw. left. lia.
  - subst w. rewrite PTrie.get_set_same in Hwd, Hwl.
    injection Hwd as Heqd. injection Hwl as Heql. subst dw lw.
    assert (Hane : a <> v) by (intro Heq; subst a; exact (fresh_open open s v Hembed Hfresh Ha)).
    rewrite PTrie.get_set_other in Had by exact Hane.
    right. exists v, (tarjan_clock s), (tarjan_clock s). split; [now left|].
    split; [exact (proj1 Hvalues a da Had)|]. split; [lia|].
    rewrite !PTrie.get_set_same. repeat split; try reflexivity; lia.
  - subst a. rewrite PTrie.get_set_same in Had. injection Had as Heq. subst da.
    assert (Hwne : w <> v) by (intro Heq; subst w; contradiction).
    rewrite PTrie.get_set_other in Hwd by exact Hwne.
    pose proof (proj1 Hvalues w dw Hwd). lia.
  - assert (Hwne : w <> v) by (intro Heq; subst w; contradiction).
    assert (Hane : a <> v) by (intro Heq; subst a; exact (fresh_open open s v Hembed Hfresh Ha)).
    rewrite PTrie.get_set_other in Had, Hal by exact Hane.
    rewrite PTrie.get_set_other in Hwd, Hwl by exact Hwne.
    destruct (Hfrontier a w da dw la lw Ha Hw Had Hwd Hal Hwl Hbound)
      as [Hle|[b [db [lb [Hb [Hab [Hbw [Hbd [Hbl Hle]]]]]]]]]; [now left|].
    assert (Hbne : b <> v) by (intro Heq; subst b; exact (fresh_open open s v Hembed Hfresh Hb)).
    right. exists b, db, lb. rewrite !PTrie.get_set_other by exact Hbne.
    split; [now right|]. repeat split; assumption.
Qed.

Lemma nodup_disjoint {A} (prefix suffix : list A) :
  NoDup (prefix ++ suffix) -> forall x, In x prefix -> ~ In x suffix.
Proof.
  intro Hunique. induction prefix as [|head prefix IH]; intros x Hin; [contradiction|].
  inversion Hunique as [|head' rest Hnot Htail]; subst head' rest.
  destruct Hin as [Heq|Hin].
  - subst x. intro Hsuffix. apply Hnot. apply in_or_app. now right.
  - now apply IH.
Qed.

Lemma pop_tail_low root index pending low active owners members tail lows actives assigned x :
  NoDup pending ->
  tarjan_pop root index pending low active owners = (members, tail, lows, actives, assigned) ->
  In x tail -> trie_get x lows = trie_get x low.
Proof.
  intros Hunique Hpop Hx.
  destruct (tarjan_pop_lookup _ _ _ _ _ _ _ _ _ _ _ Hpop) as [Hsplit Hlookup].
  rewrite (proj1 (Hlookup x)). destruct (existsb (Pos.eqb x) members) eqn:Hmember; [|reflexivity].
  apply tarjan_positive_existsb in Hmember. rewrite Hsplit in Hunique.
  exfalso. exact (nodup_disjoint members tail Hunique x Hmember Hx).
Qed.

Lemma pop_frontier v open s members tail low active owners frames emitted clock next :
  tarjan_embeds (v :: open) (tarjan_pending s) -> tarjan_state_ordered s ->
  NoDup (tarjan_pending s) -> frontier (v :: open) s ->
  tarjan_pop v (tarjan_next s) (tarjan_pending s) (tarjan_low s)
    (tarjan_active s) (tarjan_owners s) = (members, tail, low, active, owners) ->
  In v members -> tarjan_embeds open tail ->
  frontier open (TarjanState (tarjan_disc s) low tail active frames emitted owners clock next).
Proof.
  intros Hembed Horder Hunique Hfrontier Hpop Hv Hremaining.
  pose proof (proj1 (tarjan_pop_lookup _ _ _ _ _ _ _ _ _ _ _ Hpop)) as Hsplit.
  intros a w da dw la lw Ha Hw Had Hwd Hal Hwl Hbound.
  cbn [tarjan_pending tarjan_disc tarjan_low] in *.
  assert (Hatail : In a tail) by now apply (tarjan_embeds_incl _ _ Hremaining).
  rewrite (pop_tail_low _ _ _ _ _ _ _ _ _ _ _ a Hunique Hpop Hatail) in Hal.
  rewrite (pop_tail_low _ _ _ _ _ _ _ _ _ _ _ w Hunique Hpop Hw) in Hwl.
  assert (Hwold : In w (tarjan_pending s)) by (rewrite Hsplit; apply in_or_app; now right).
  destruct (Hfrontier a w da dw la lw (or_intror Ha) Hwold Had Hwd Hal Hwl Hbound)
    as [Hle|[b [db [lb [Hb [Hab [Hbw [Hbd [Hbl Hle]]]]]]]]]; [now left|].
  destruct Hb as [Heq|Hb].
  - subst b. pose proof (tarjan_ordered_cross (tarjan_disc s) members tail v w db dw
      ltac:(unfold tarjan_state_ordered in Horder; now rewrite <- Hsplit)
      Hv Hw Hbd Hwd). lia.
  - right. exists b, db, lb. repeat split; try assumption.
    rewrite (pop_tail_low _ _ _ _ _ _ _ _ _ _ _ b Hunique Hpop).
    + exact Hbl.
    + now apply (tarjan_embeds_incl _ _ Hremaining).
Qed.

Lemma frontier_self v open s lows a da dv la lv :
  tarjan_embeds (v :: open) (tarjan_pending s) -> tarjan_state_ordered s ->
  In a (v :: open) -> trie_get a (tarjan_disc s) = Some da ->
  trie_get v (tarjan_disc s) = Some dv -> trie_get a lows = Some la ->
  trie_get v lows = Some lv ->
  Pos.to_nat la <= Pos.to_nat lv \/
  exists b db lb, In b (v :: open) /\ Pos.to_nat da < Pos.to_nat db /\
    Pos.to_nat db <= Pos.to_nat dv /\ trie_get b (tarjan_disc s) = Some db /\
    trie_get b lows = Some lb /\ Pos.to_nat lb <= Pos.to_nat lv.
Proof.
  intros Hembed Horder Ha Had Hvd Hal Hvl. destruct (Pos.eq_dec a v) as [Heq|Hne].
  - subst a. rewrite Hvl in Hal. injection Hal as Heq. subst la. left. lia.
  - right. exists v, dv, lv. split; [now left|]. split.
    + apply (open_head_number v open s a da dv Hembed Horder);
        [destruct Ha as [Heq|Ha]; [congruence|exact Ha]|exact Had|exact Hvd].
    + split; [lia|]. split; [exact Hvd|]. split; [exact Hvl|lia].
Qed.

Lemma parent_witness v parent open s a da dp dv dw lp l lw :
  tarjan_embeds (v :: parent :: open) (tarjan_pending s) -> tarjan_state_ordered s ->
  In a (parent :: open) -> a <> parent ->
  trie_get a (tarjan_disc s) = Some da -> trie_get parent (tarjan_disc s) = Some dp ->
  trie_get v (tarjan_disc s) = Some dv -> Pos.to_nat dv <= Pos.to_nat dw ->
  Pos.to_nat l <= Pos.to_nat lw ->
  exists b db lb, In b (parent :: open) /\ Pos.to_nat da < Pos.to_nat db /\
    Pos.to_nat db <= Pos.to_nat dw /\ trie_get b (tarjan_disc s) = Some db /\
    trie_get b (PTrieCode.set parent (Pos.min lp l) (tarjan_low s)) = Some lb /\
    Pos.to_nat lb <= Pos.to_nat lw.
Proof.
  intros Hembed Horder Ha Hne Had Hpd Hvd Hvw Hle.
  exists parent, dp, (Pos.min lp l). split; [now left|]. split.
  - apply (open_head_number parent open s a da dp
      (tarjan_embeds_drop _ _ _ Hembed) Horder);
      [destruct Ha as [Heq|Ha]; [congruence|exact Ha]|exact Had|exact Hpd].
  - split.
    + pose proof (open_head_number v (parent :: open) s parent dp dv
        Hembed Horder (or_introl eq_refl) Hpd Hvd). lia.
    + split; [exact Hpd|]. rewrite PTrie.get_set_same.
      split; [reflexivity|]. rewrite Pos2Nat.inj_min. lia.
Qed.

Lemma close_lower_frontier v parent open s l lp dp :
  tarjan_embeds (v :: parent :: open) (tarjan_pending s) -> tarjan_state_ordered s ->
  frontier (v :: parent :: open) s -> trie_get v (tarjan_low s) = Some l ->
  trie_get parent (tarjan_low s) = Some lp -> trie_get parent (tarjan_disc s) = Some dp ->
  frontier (parent :: open) (TarjanVisitor.lower parent l s).
Proof.
  intros Hembed Horder Hfrontier Hvl Hpl Hpd. unfold TarjanVisitor.lower. rewrite Hpl.
  intros a w da dw la lw Ha Hw Had Hwd Hal Hwl Hbound.
  cbn [tarjan_pending tarjan_disc tarjan_low] in *.
  destruct (Pos.eq_dec w parent) as [Heq|Hwne].
  - subst w. exact (frontier_self parent open s _ a da dw la lw
      (tarjan_embeds_drop _ _ _ Hembed) Horder Ha Had Hwd Hal Hwl).
  - rewrite PTrie.get_set_other in Hwl by exact Hwne.
    destruct (low_set_inverse _ parent lp l a la Hpl Hal) as [prior [Hal_prior Hla]].
    destruct (Hfrontier a w da dw prior lw (or_intror Ha) Hw Had Hwd Hal_prior Hwl Hbound)
      as [Hle|[b [db [lb [Hb [Hab [Hbw [Hbd [Hbl Hle]]]]]]]]].
    + left. lia.
    + destruct Hb as [Heq|Hb].
      * subst b. rewrite Hvl in Hbl. injection Hbl as Heq. subst lb.
        destruct (Pos.eq_dec a parent) as [Heq|Hane].
        -- subst a. rewrite PTrie.get_set_same in Hal. injection Hal as Heq. subst la.
           left. rewrite Pos2Nat.inj_min. lia.
        -- right. exact (parent_witness v parent open s a da dp db dw lp l lw
             Hembed Horder Ha Hane Had Hpd Hbd Hbw Hle).
      * destruct (low_set_bound _ parent lp l b lb Hpl Hbl) as [next [Hnext Hnext_le]].
        right. exists b, db, next. repeat split; try assumption. lia.
Qed.

Lemma leave_frontier v open s :
  tarjan_frames s = v :: open -> tarjan_embeds (v :: open) (tarjan_pending s) ->
  tarjan_state_ordered s -> NoDup (tarjan_pending s) -> tarjan_pending_domains s ->
  (forall w, In w (tarjan_pending s) -> exists d, trie_get w (tarjan_disc s) = Some d) ->
  frontier (v :: open) s -> frontier open (TarjanVisitor.leave v s).
Proof.
  intros Hframes Hembed Horder Hunique Hdomains Hdiscover Hfrontier.
  assert (Hv : In v (tarjan_pending s)) by
    (apply (tarjan_embeds_incl _ _ Hembed); now left).
  destruct (proj2 (proj2 Hdomains v) Hv) as [l Hvl].
  destruct (Hdiscover v Hv) as [d Hvd].
  unfold TarjanVisitor.leave. rewrite Hframes, Hvl, Hvd. cbn beta iota zeta.
  destruct (Pos.eqb l d).
  - destruct (tarjan_pop v (tarjan_next s) (tarjan_pending s) (tarjan_low s)
      (tarjan_active s) (tarjan_owners s))
      as [[[[members tail] low] active] owners] eqn:Hpop.
    eapply pop_frontier; try eassumption.
    + eapply tarjan_pop_root_member; eassumption.
    + eapply tarjan_embeds_pop; eassumption.
  - destruct open as [|parent open].
    + intros a w da dw la lw Hfalse. contradiction.
    + assert (Hp : In parent (tarjan_pending s)) by
        (apply (tarjan_embeds_incl _ _ Hembed); right; now left).
      destruct (proj2 (proj2 Hdomains parent) Hp) as [lp Hpl].
      destruct (Hdiscover parent Hp) as [dp Hpd].
      pose proof (close_lower_frontier v parent open s l lp dp
        Hembed Horder Hfrontier Hvl Hpl Hpd) as Hnext.
      unfold TarjanVisitor.lower in Hnext |- *. cbn [tarjan_low].
      rewrite Hpl in Hnext |- *. exact Hnext.
Qed.

Lemma edge_frontier kind u open s v :
  tarjan_embeds (u :: open) (tarjan_pending s) -> tarjan_state_ordered s ->
  frontier (u :: open) s -> frontier (u :: open) (TarjanVisitor.edge kind u v s).
Proof.
  intros Hembed Horder Hfrontier. destruct kind; cbn [TarjanVisitor.edge]; try exact Hfrontier.
  all: destruct (trie_get v (tarjan_active s)) as [[|]|]; try exact Hfrontier.
  all: destruct (trie_get v (tarjan_disc s)); try exact Hfrontier.
  all: now apply lower_frontier.
Qed.

End TarjanFrontierFacts.


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
  Proof.
    intros g Hwf. unfold run. cbn [comps].
    rewrite rev_append_rev, app_nil_r.
    pose proof (tarjan_complete_components (scc_trace g)
      (scc_trace_unique g) (scc_trace_nested g)) as Hcomponents.
    split.
    - eapply Permutation_NoDup; [apply Permutation_sym; exact Hcomponents|].
      apply scc_trace_unique.
    - intro v. rewrite <- (scc_trace_entered g v).
      split; intro Hin.
      + eapply Permutation_in; [exact Hcomponents|exact Hin].
      + eapply Permutation_in; [apply Permutation_sym; exact Hcomponents|exact Hin].
  Qed.

  Lemma comps_nonempty : forall g, wf_graph (base g) ->
    Forall (fun vs => vs <> []) (comps (run g)).
  Proof.
    intros g Hwf. unfold run. cbn [comps].
    rewrite rev_append_rev, app_nil_r. apply Forall_rev. apply tarjan_emitted_nonempty.
  Qed.

  Lemma owners_spec : forall g, wf_graph (base g) -> forall v i,
    trie_get v (comp (run g)) = Some i <->
    exists vs, nth_error (comps (run g)) (Nat.pred (Pos.to_nat i)) = Some vs /\ In v vs.
  Proof.
    intros g Hgraph v i. unfold run. cbn [comp comps].
    rewrite rev_append_rev, app_nil_r.
    exact (tarjan_owners_indexed_fold (scc_trace g) (scc_trace_unique g) v i).
  Qed.

  Lemma comps_order : forall g, wf_graph (base g) -> forall u v i j,
    edge (base g) u v -> trie_get u (comp (run g)) = Some i ->
    trie_get v (comp (run g)) = Some j -> (j <= i)%positive.
  Proof. Admitted. (* CONVERT: GraphTarjan: filtered traversal requires the scoped proof. *)
End Scc.

Transparent search_trace.

Module SccT <: SCC_ALL.
  Include Scc.
  TimeFun run.
  Definition c_scc : N :=
    (128 * (search_trace_coefficient + 65536 + 16384))%N.

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
  Definition k_callback : N := 65536%N.
  Definition k_result : N := 8%N.
  Definition k_search : N := (8 * (search_trace_coefficient + 4096))%N.

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
  Proof.
    intros g prefix suffix Htrace.
    change (scc_trace g = prefix ++ suffix) in Htrace.
    pose proof (scc_trace_prefix_unique g prefix suffix Htrace) as Hunique.
    pose proof (tarjan_bag_inventory prefix) as Hbag.
    pose proof (Permutation_NoDup (Permutation_sym Hbag) Hunique) as Hnodup.
    pose proof (tarjan_prefix_frames g prefix suffix Htrace) as Hframes.
    destruct (tarjan_pending_domains_fold prefix Hunique) as [Hactive Hlow].
    pose proof (tarjan_discovery_rows_fold prefix Hunique) as Hdisc.
    split.
    - unfold inventory, prefix_state, tarjan_enter, tarjan_leave, tarjan_edge, tarjan_initial.
      unfold tarjan_bag in Hbag, Hnodup.
      split; [exact Hnodup|]. split; [exact Hbag|]. split; [exact Hframes|].
      split.
      { apply Pos2Nat.inj. rewrite SuccNat2Pos.id_succ. apply tarjan_clock_count. }
      split.
      { apply Pos2Nat.inj. rewrite SuccNat2Pos.id_succ. apply tarjan_next_count. }
      split; [exact Hactive|]. split; [exact Hlow|exact Hdisc].
    - unfold width_domain, prefix_state, tarjan_enter, tarjan_leave, tarjan_edge, tarjan_initial.
      apply tarjan_fold_width; [exact Hunique|].
      apply Forall_forall. intros v Hin. apply search_entered_member in Hin.
      pose proof (scc_trace_prefix_width g prefix suffix Htrace) as Hwidth.
      rewrite Forall_forall in Hwidth. exact (Hwidth (Enter v) Hin).
  Qed.

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
  Proof.
    intros g Hwf. cbn zeta.
    unfold prefix_state, tarjan_trace, tarjan_initial,
      tarjan_enter, tarjan_leave, tarjan_edge.
    destruct (tarjan_complete_nested (scc_trace g)
      (scc_trace_unique g) (scc_trace_nested g)) as [Hpending Hframes].
    split; [exact Hpending|]. split; [exact Hframes|].
    apply tarjan_owners_indexed_fold, scc_trace_unique.
  Qed.

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
  Proof.
    intros g prefix e suffix Htrace. cbn zeta.
    assert (Hwidth : event_domain (graph_width (base g)) e).
    { pose proof (scc_trace_event_width g) as Hdomain.
      rewrite Forall_forall in Hdomain. apply Hdomain.
      change (scc_trace g = prefix ++ e :: suffix) in Htrace.
      rewrite Htrace. apply in_or_app. right. now left. }
    pose proof (callback_credit (graph_width (base g)) e (prefix_state prefix)
      (prefix_width g prefix (e :: suffix) Htrace) Hwidth) as Hcredit.
    unfold k_callback. lia.
  Qed.

  (** A state-dependent callback credit telescopes through the generated list-fold clock. *)
  Local Lemma fold_left_amortized {A B} (f : A -> B -> A) (T_f : A -> B -> N)
      (credit : A -> N) (budget : N) es s :
    (forall prefix e suffix, es = prefix ++ e :: suffix ->
      (T_f (fold_left f prefix s) e + credit (f (fold_left f prefix s) e) <=
        budget + credit (fold_left f prefix s))%N) ->
    (List.T_fold_left f T_f es s + credit (fold_left f es s) <=
      (budget + 1) * N.of_nat (length es) + 1 + credit s)%N.
  Proof.
    revert s. induction es as [|e es IH]; intros s Hcredit.
    - time_unfold @List.T_fold_left. cbn [fold_left length]. lia.
    - assert (Htail : forall prefix next suffix, es = prefix ++ next :: suffix ->
        (T_f (fold_left f prefix (f s e)) next +
          credit (f (fold_left f prefix (f s e)) next) <=
          budget + credit (fold_left f prefix (f s e)))%N).
      { intros prefix next suffix Hsplit.
        apply (Hcredit (e :: prefix) next suffix). cbn [app]. now rewrite Hsplit. }
      specialize (IH (f s e) Htail).
      specialize (Hcredit [] e es eq_refl). cbn [fold_left] in Hcredit.
      time_unfold @List.T_fold_left. cbn [fold_left length]. rewrite Nat2N.inj_succ. nia.
  Qed.

  Local Lemma fold_events_credit w es s :
    (forall prefix e suffix, es = prefix ++ e :: suffix ->
      let current := fold_events tarjan_enter tarjan_leave tarjan_edge prefix s in
      (callback_cost e current + potential w (apply_event current e) <=
        32768 * N.of_nat (w + 1) + potential w current)%N) ->
    (T_fold_events tarjan_enter T_tarjan_enter tarjan_leave T_tarjan_leave
        tarjan_edge T_tarjan_edge es s +
      potential w (fold_events tarjan_enter tarjan_leave tarjan_edge es s) <=
      (32768 * N.of_nat (w + 1) + 2) * N.of_nat (length es) + 2 + potential w s)%N.
  Proof.
    intros Hcredit.
    assert (Hfold :
      (List.T_fold_left (visit_event tarjan_enter tarjan_leave tarjan_edge)
        (fun state e => T_visit_event tarjan_enter T_tarjan_enter
          tarjan_leave T_tarjan_leave tarjan_edge T_tarjan_edge state e)
        es s + potential w
          (fold_left (visit_event tarjan_enter tarjan_leave tarjan_edge) es s) <=
        (32768 * N.of_nat (w + 1) + 2) * N.of_nat (length es) + 1 + potential w s)%N).
    { replace (32768 * N.of_nat (w + 1) + 2)%N with
        ((32768 * N.of_nat (w + 1) + 1) + 1)%N by lia.
      apply fold_left_amortized. intros prefix e suffix Hsplit.
      specialize (Hcredit prefix e suffix Hsplit). unfold fold_events in Hcredit.
      destruct e; cbn [callback_cost apply_event visit_event] in Hcredit;
        time_unfold @T_visit_event; cbn [visit_event]; lia. }
    time_unfold @T_fold_events. unfold fold_events. lia.
  Qed.

  (** A unique bounded event list has bounded operational state after its fold. *)
  Lemma event_fold_width w es : NoDup (entered es) -> Forall (event_domain w) es ->
    width_domain w (prefix_state es).
  Proof.
    intros Hunique Hwidth. unfold width_domain, prefix_state,
      tarjan_enter, tarjan_leave, tarjan_edge, tarjan_initial.
    apply tarjan_fold_width; [exact Hunique|].
    apply Forall_forall. intros v Hin. apply search_entered_member in Hin.
    rewrite Forall_forall in Hwidth. exact (Hwidth (Enter v) Hin).
  Qed.

  (** Every unique bounded event list pays the complete generated fold, including driver calls. *)
  Lemma fold_events_time w es : NoDup (entered es) -> Forall (event_domain w) es ->
    (T_fold_events tarjan_enter T_tarjan_enter tarjan_leave T_tarjan_leave
        tarjan_edge T_tarjan_edge es tarjan_initial + potential w (prefix_state es) <=
      k_callback * N.of_nat (length es + 1) * N.of_nat (w + 1))%N.
  Proof.
    intros Hunique Hwidth.
    assert (Hcredit : forall prefix e suffix, es = prefix ++ e :: suffix ->
      let current := fold_events tarjan_enter tarjan_leave tarjan_edge prefix tarjan_initial in
      (callback_cost e current + potential w (apply_event current e) <=
        32768 * N.of_nat (w + 1) + potential w current)%N).
    { intros prefix e suffix Hsplit. cbn zeta. apply callback_credit.
      - apply event_fold_width.
        + rewrite Hsplit, search_entered_app in Hunique.
          now apply NoDup_app_remove_r in Hunique.
        + rewrite Hsplit, Forall_app in Hwidth. exact (proj1 Hwidth).
      - rewrite Forall_forall in Hwidth. apply Hwidth.
        rewrite Hsplit. apply in_or_app. right. now left. }
    pose proof (fold_events_credit w es tarjan_initial Hcredit) as Hfold.
    assert (Hzero : potential w tarjan_initial = 0%N).
    { change ((pop_unit w * 0 + k_result * 0)%N = 0%N). now rewrite !N.mul_0_r. }
    rewrite Hzero in Hfold. unfold prefix_state. unfold k_callback. nia.
  Qed.


  Lemma T3_fold : forall g,
    (T_fold_events tarjan_enter T_tarjan_enter tarjan_leave T_tarjan_leave
      tarjan_edge T_tarjan_edge (tarjan_trace g) tarjan_initial +
      potential (graph_width (base g)) (prefix_state (tarjan_trace g)) <=
    k_callback * N.of_nat (length (tarjan_trace g) + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
  Proof.
    intros g. apply fold_events_time.
    - apply scc_trace_unique.
    - apply scc_trace_event_width.
  Qed.

  Lemma T4_trace : forall g,
    (T_tarjan_trace g <= k_search * N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
  Proof.
    intros g. unfold k_search. time_unfold @T_tarjan_trace. apply scc_trace_time.
  Qed.

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

  (** Direct visitor clocks inherit the amortized fold bound used by raw SCC clients. *)
  Lemma visitor_fold_time w es : NoDup (entered es) -> Forall (event_domain w) es ->
    (T_fold_events TarjanVisitor.enter (fun v s => TarjanVisitor.T_enter v s)
      TarjanVisitor.leave (fun v s => TarjanVisitor.T_leave v s)
      TarjanVisitor.edge (fun kind u v s => TarjanVisitor.T_edge kind u v s)
      es tarjan_initial <=
      k_callback * N.of_nat (length es + 1) * N.of_nat (w + 1))%N.
  Proof.
    intros Hunique Hwidth. pose proof (fold_events_time w es Hunique Hwidth) as Hfold.
    pose proof (fold_events_alias_time es tarjan_initial) as Halias. lia.
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
  Proof.
    intros g. pose proof (T5_wrapper g) as Hwrapper.
    pose proof (T3_fold g) as Hfold. pose proof (T4_trace g) as Htrace.
    pose proof (scc_trace_size g) as Hsize.
    change (length (tarjan_trace g) <= 2 * graph_n (base g) + graph_e (base g)) in Hsize.
    assert (Hresult : (N.of_nat (length (tarjan_emitted (prefix_state (tarjan_trace g)))) <=
        potential (graph_width (base g)) (prefix_state (tarjan_trace g)))%N).
    { unfold potential, k_result. nia. }
    set (events := tarjan_trace g) in *. clearbody events.
    set (result := prefix_state events) in *. clearbody result.
    assert (Hlength_product :
      (N.of_nat (length events + 1) * N.of_nat (graph_width (base g) + 1) <=
        2 * N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
          N.of_nat (graph_width (base g) + 1))%N).
    { apply N.mul_le_mono_r. lia. }
    unfold c_scc, k_search, k_callback, k_result in *.
    nia.
  Qed.

  Lemma T_run_le : forall g,
    (T_run g <= c_scc * N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
  Proof. exact T6_public. Qed.

  Lemma run_bigO : bigO (fun _ => True)
    (fun g => N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
      (graph_width (base g) + 1))) T_run.
  Proof.
    exists c_scc. intros g _.
    eapply N.le_trans; [apply T_run_le|].
    rewrite Nat2N.inj_mul. nia.
  Qed.
End SccT.
