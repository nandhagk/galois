(** * Priority queues

    A binomial forest indexes a live map and retains obsolete entries after decreases.
    For example, pushing priorities five and two for one key leaves priority two live.
    Builds on: HeapSig, MapSig and Argent time interfaces. *)

From Stdlib Require Import List Bool NArith PArith PeanoNat Lia Sorting.Permutation.
From Argent Require Import Time Tactics Std Loop BigO.
From Galois.Base Require Import HeapSig KeySig MapSig Trie Loop.
Import List.ListNotations.

Definition heap_entry := (N * positive)%type.
Scheme All for list.

Inductive heap_tree := HeapTree (root_entry : heap_entry) (children : list heap_tree).
Definition heap_forest := list (option heap_tree).
Record priority_queue := Queue {
  pending : heap_forest;
  live : PTrieCode.t N;
  live_count : N;
  pending_count : N
}.

Definition heap_pending (q : priority_queue) : heap_forest :=
  match q with Queue h _ _ _ => h end.
TimeFun heap_pending.

Definition heap_root (t : heap_tree) := match t with HeapTree e _ => e end.
TimeFun pending.
TimeFun live.
TimeFun live_count.
TimeFun pending_count.
TimeFun heap_root.

Definition heap_before (a b : heap_entry) :=
  if N.ltb (fst a) (fst b) then true
  else if N.eqb (fst a) (fst b) then Pos.leb (snd a) (snd b) else false.
TimeFun heap_before.
Definition heap_link (a b : heap_tree) :=
  match a, b with
  | HeapTree e cs, HeapTree e' cs' =>
    if heap_before e e' then HeapTree e (b :: cs) else HeapTree e' (a :: cs')
  end.
TimeFun heap_link.
Definition heap_digit (s : option heap_tree) (hs : heap_forest) :=
  match s, hs with None, [] => [] | _, _ => s :: hs end.
TimeFun heap_digit.
Fixpoint heap_insert (t : heap_tree) (h : heap_forest) : heap_forest :=
  match h with
  | [] => [Some t]
  | None :: hs => Some t :: hs
  | Some u :: hs => None :: heap_insert (heap_link t u) hs
  end.
TimeFun heap_insert.
Fixpoint heap_meld (a b : heap_forest) (carry : option heap_tree) {struct a} : heap_forest :=
  match a with
  | [] => match carry with None => b | Some t => heap_insert t b end
  | x :: xs =>
    match b with
    | [] => match carry with None => a | Some t => heap_insert t a end
    | y :: ys =>
      match x, y, carry with
      | None, None, c => heap_digit c (heap_meld xs ys None)
      | Some t, None, None | None, Some t, None => heap_digit (Some t) (heap_meld xs ys None)
      | Some t, Some u, None | Some t, None, Some u | None, Some t, Some u =>
        heap_digit None (heap_meld xs ys (Some (heap_link t u)))
      | Some t, Some u, Some c => heap_digit (Some c) (heap_meld xs ys (Some (heap_link t u)))
      end
    end
  end.
TimeFun heap_meld.
Fixpoint heap_select (h : heap_forest) : option (heap_tree * heap_forest) :=
  match h with
  | [] => None
  | x :: xs =>
    match heap_select xs with
    | None => match x with None => None | Some t => Some (t, []) end
    | Some (t, rest) =>
      match x with
      | None => Some (t, heap_digit None rest)
      | Some u => if heap_before (heap_root u) (heap_root t)
                  then Some (u, heap_digit None xs) else Some (t, heap_digit (Some u) rest)
      end
    end
  end.
TimeFun heap_select.
Definition heap_remove_min (h : heap_forest) : option (heap_entry * heap_forest) :=
  match heap_select h with
  | None => None
  | Some (HeapTree e cs, rest) =>
    Some (e, heap_meld (rev_append (map (@Some heap_tree) cs) []) rest None)
  end.
TimeFun heap_remove_min.
Fixpoint heap_fuel (h : heap_forest) : positive :=
  match h with [] => xH | _ :: rest => xO (heap_fuel rest) end.

TimeFun heap_fuel.

Module HeapCode <: PQ_OPS.
  Definition t := priority_queue.
  Definition empty : t := Queue [] PTrieCode.empty 0%N 0%N.
  Definition size (q : t) := live_count q.
  Definition enqueue (p : N) (k : positive) (q : t) (n : N) : t :=
    Queue (heap_insert (HeapTree (p, k) []) (pending q))
      (PTrieCode.set k p (live q)) n (N.succ (pending_count q)).
  Definition push (p : N) (k : positive) (q : t) : t :=
    match PTrieCode.get k (live q) with
    | None => enqueue p k q (N.succ (live_count q))
    | Some old => if N.ltb p old then enqueue p k q (live_count q) else q
    end.
  Definition heap_pop_step (m : PTrieCode.t N) (n : N) (s : heap_forest * N) :
      heap_forest * N + option (N * positive * t) :=
    let '(h, total) := s in
    match heap_remove_min h with
    | None => inr None
    | Some ((p, k), rest) =>
      match PTrieCode.get k m with
      | Some current =>
        if N.eqb p current then
          inr (Some (p, k, Queue rest (PTrieCode.remove k m) (N.pred n) (N.pred total)))
        else inl (rest, N.pred total)
      | None => inl (rest, N.pred total)
      end
    end.
  TimeFun heap_pop_step.
  Definition pop (q : t) : option (N * positive * t) :=
    match loopN (heap_pop_step (live q) (live_count q)) (N.pos (heap_fuel (pending q)))
      (pending q, pending_count q) with
    | inl _ => None
    | inr result => result
    end.
  TimeFun pop.
End HeapCode.

(** Entry traversal prepends each subtree to an already prepared suffix. *)
Fixpoint heap_tree_entries_into (tr : heap_tree) (acc : list heap_entry) : list heap_entry :=
  match tr with
  | HeapTree e cs =>
    e :: (fix children_into (children : list heap_tree) (suffix : list heap_entry) :=
      match children with
      | [] => suffix
      | child :: rest => heap_tree_entries_into child (children_into rest suffix)
      end) cs acc
  end.

Definition heap_tree_entries (tr : heap_tree) : list heap_entry :=
  heap_tree_entries_into tr [].

Definition heap_precedes (a b : heap_entry) : Prop :=
  (fst a < fst b)%N \/ (fst a = fst b /\ (snd a <= snd b)%positive).

Inductive heap_valid : nat -> heap_tree -> Prop :=
  | HeapValid_zero e : heap_valid 0 (HeapTree e [])
  | HeapValid_link r e cs b :
      heap_valid r (HeapTree e cs) -> heap_valid r b ->
      (forall x, In x (heap_tree_entries b) -> heap_precedes e x) ->
      heap_valid (S r) (HeapTree e (b :: cs)).

Fixpoint heap_entries (h : heap_forest) : list heap_entry :=
  match h with
  | [] => []
  | None :: hs => heap_entries hs
  | Some tr :: hs => heap_tree_entries_into tr (heap_entries hs)
  end.

Fixpoint heap_forest_valid (r : nat) (h : heap_forest) : Prop :=
  match h with
  | [] => True
  | s :: hs =>
    (match s with None => True | Some tr => heap_valid r tr end) /\
    heap_forest_valid (S r) hs /\ (s <> None \/ hs <> [])
  end.

Lemma heap_tree_entries_into_app (t : heap_tree) (acc : list heap_entry) :
  heap_tree_entries_into t acc = heap_tree_entries t ++ acc.
Proof.
  assert (Happ : forall tr xs ys,
    heap_tree_entries_into tr (xs ++ ys) = heap_tree_entries_into tr xs ++ ys).
  { fix IH 1. intros [e cs] xs ys. cbn [heap_tree_entries_into app]. f_equal.
    induction cs as [| child cs IHcs]; cbn.
    - reflexivity.
    - rewrite IHcs. apply IH. }
  exact (Happ t [] acc).
Qed.

Lemma heap_tree_entries_eq (e : heap_entry) (cs : list heap_tree) :
  heap_tree_entries (HeapTree e cs) = e :: flat_map heap_tree_entries cs.
Proof.
  unfold heap_tree_entries at 1. cbn [heap_tree_entries_into]. f_equal.
  induction cs as [| child cs IH]; cbn [flat_map].
  - reflexivity.
  - rewrite heap_tree_entries_into_app, IH. reflexivity.
Qed.

Lemma heap_entries_cons (t : heap_tree) (h : heap_forest) :
  heap_entries (Some t :: h) = heap_tree_entries t ++ heap_entries h.
Proof. apply heap_tree_entries_into_app. Qed.

Definition heap_slot_entries (s : option heap_tree) : list heap_entry :=
  match s with None => [] | Some t => heap_tree_entries t end.

Lemma heap_entries_slot (s : option heap_tree) (h : heap_forest) :
  heap_entries (s :: h) = heap_slot_entries s ++ heap_entries h.
Proof.
  destruct s as [t |]; [apply heap_entries_cons | reflexivity].
Qed.

Lemma heap_root_in (t : heap_tree) : In (heap_root t) (heap_tree_entries t).
Proof.
  destruct t as [e cs]. rewrite heap_tree_entries_eq. left; reflexivity.
Qed.

Lemma heap_before_spec (a b : heap_entry) :
  heap_before a b = true <-> heap_precedes a b.
Proof.
  unfold heap_before, heap_precedes.
  destruct (N.ltb (fst a) (fst b)) eqn:Hlt.
  - apply N.ltb_lt in Hlt. intuition.
  - apply N.ltb_ge in Hlt.
    destruct (N.eqb (fst a) (fst b)) eqn:Heq.
    + apply N.eqb_eq in Heq. rewrite Pos.leb_le. intuition lia.
    + apply N.eqb_neq in Heq. intuition lia.
Qed.

Lemma heap_precedes_refl (a : heap_entry) : heap_precedes a a.
Proof. right. split; [reflexivity | apply Pos.le_refl]. Qed.

Lemma heap_precedes_trans (a b c : heap_entry) :
  heap_precedes a b -> heap_precedes b c -> heap_precedes a c.
Proof.
  unfold heap_precedes. intros [Hab | [Hab Hkab]] [Hbc | [Hbc Hkbc]];
    try (left; lia); right; split; lia.
Qed.

Lemma heap_before_false (a b : heap_entry) :
  heap_before a b = false -> heap_precedes b a.
Proof.
  intro Hfalse.
  assert (Hnot : ~ heap_precedes a b)
    by (intro H; apply heap_before_spec in H; congruence).
  unfold heap_precedes in *. destruct (N.eq_dec (fst a) (fst b)); intuition lia.
Qed.

Lemma heap_precedes_prio (a b : heap_entry) :
  heap_precedes a b -> (fst a <= fst b)%N.
Proof. unfold heap_precedes. intros [H | [H _]]; lia. Qed.

Lemma heap_entries_digit (s : option heap_tree) (h : heap_forest) :
  heap_entries (heap_digit s h) = heap_slot_entries s ++ heap_entries h.
Proof.
  destruct s as [t |], h as [| x xs]; cbn [heap_digit heap_slot_entries heap_entries];
    try apply heap_tree_entries_into_app; reflexivity.
Qed.

Lemma heap_count_digit (s : option heap_tree) (h : heap_forest) :
  length (heap_entries (heap_digit s h)) =
    length (heap_slot_entries s) + length (heap_entries h).
Proof. rewrite heap_entries_digit, length_app. reflexivity. Qed.

Lemma heap_valid_digit r (s : option heap_tree) (h : heap_forest) :
  (match s with None => True | Some t => heap_valid r t end) ->
  heap_forest_valid (S r) h -> heap_forest_valid r (heap_digit s h).
Proof.
  destruct s as [t |], h as [| x xs]; cbn; intros Hs Hh.
  - split; [exact Hs |]; split; [exact I | left; discriminate].
  - split; [exact Hs |]; split; [exact Hh | left; discriminate].
  - exact I.
  - split; [exact I |]; split; [exact Hh | right; discriminate].
Qed.

Lemma heap_entries_link (a b : heap_tree) e :
  In e (heap_tree_entries (heap_link a b)) <->
    In e (heap_tree_entries a) \/ In e (heap_tree_entries b).
Proof.
  destruct a as [x xs], b as [y ys]. unfold heap_link.
  destruct (heap_before x y); rewrite !heap_tree_entries_eq; cbn [flat_map];
    rewrite ?heap_tree_entries_eq; cbn [In app]; rewrite in_app_iff;
    intuition congruence.
Qed.

Lemma heap_count_link (a b : heap_tree) :
  length (heap_tree_entries (heap_link a b)) =
    length (heap_tree_entries a) + length (heap_tree_entries b).
Proof.
  destruct a as [x xs], b as [y ys]. unfold heap_link.
  destruct (heap_before x y); rewrite !heap_tree_entries_eq; cbn [flat_map];
    rewrite ?heap_tree_entries_eq; cbn [length app]; rewrite length_app; lia.
Qed.

Lemma heap_valid_root r (t : heap_tree) :
  heap_valid r t -> forall e, In e (heap_tree_entries t) -> heap_precedes (heap_root t) e.
Proof.
  intro Hvalid.
  induction Hvalid as [e | r e cs b Hbase IH Hchild IHchild Hbefore]; intros a Hin;
    rewrite heap_tree_entries_eq in Hin; cbn [heap_root] in *.
  - destruct Hin as [Heq | Hfalse]; [subst; apply heap_precedes_refl | contradiction].
  - destruct Hin as [Heq | Hin]; [subst; apply heap_precedes_refl |].
    cbn [flat_map] in Hin. apply in_app_iff in Hin. destruct Hin as [Hin | Hin].
    + apply Hbefore; exact Hin.
    + apply IH. rewrite heap_tree_entries_eq. right; exact Hin.
Qed.

Lemma heap_valid_link r (a b : heap_tree) :
  heap_valid r a -> heap_valid r b -> heap_valid (S r) (heap_link a b).
Proof.
  intros Ha Hb. destruct a as [e cs], b as [e' cs']. unfold heap_link.
  destruct (heap_before e e') eqn:Hcmp; apply HeapValid_link; try assumption.
  - intros x Hin. eapply heap_precedes_trans.
    + apply heap_before_spec; exact Hcmp.
    + apply (heap_valid_root r (HeapTree e' cs') Hb); exact Hin.
  - intros x Hin. eapply heap_precedes_trans.
    + apply heap_before_false; exact Hcmp.
    + apply (heap_valid_root r (HeapTree e cs) Ha); exact Hin.
Qed.

Lemma heap_entries_insert (t : heap_tree) h e :
  In e (heap_entries (heap_insert t h)) <->
    In e (heap_tree_entries t) \/ In e (heap_entries h).
Proof.
  revert t. induction h as [| [u |] hs IH]; intro t; cbn [heap_insert].
  - rewrite heap_entries_cons. cbn [heap_entries]. rewrite app_nil_r. cbn; tauto.
  - change (In e (heap_entries (heap_insert (heap_link t u) hs)) <->
      In e (heap_tree_entries t) \/ In e (heap_entries (Some u :: hs))).
    rewrite IH, heap_entries_link, heap_entries_cons, in_app_iff. tauto.
  - rewrite heap_entries_cons. cbn [heap_entries]. rewrite in_app_iff. tauto.
Qed.

Lemma heap_count_insert (t : heap_tree) h :
  length (heap_entries (heap_insert t h)) =
    length (heap_tree_entries t) + length (heap_entries h).
Proof.
  revert t. induction h as [| [u |] hs IH]; intro t; cbn [heap_insert].
  - rewrite heap_entries_cons. cbn [heap_entries]. rewrite length_app. cbn; lia.
  - change (length (heap_entries (heap_insert (heap_link t u) hs)) =
      length (heap_tree_entries t) + length (heap_entries (Some u :: hs))).
    rewrite IH, heap_count_link, heap_entries_cons, length_app. lia.
  - rewrite heap_entries_cons. cbn [heap_entries]. rewrite length_app. reflexivity.
Qed.

Lemma heap_valid_insert r (t : heap_tree) h :
  heap_valid r t -> heap_forest_valid r h -> heap_forest_valid r (heap_insert t h).
Proof.
  revert r t. induction h as [| [u |] hs IH]; intros r t Ht Hh; cbn [heap_insert].
  - split; [exact Ht |]; split; [exact I | left; discriminate].
  - destruct Hh as [Hu [Hhs Hlast]]. split; [exact I |]; split.
    + apply IH; [apply heap_valid_link; assumption | exact Hhs].
    + right. destruct hs as [| [v |] hs]; cbn [heap_insert]; discriminate.
  - destruct Hh as [_ [Hhs Hlast]].
    split; [exact Ht |]; split; [exact Hhs | left; discriminate].
Qed.

Lemma heap_entries_meld (a b : heap_forest) c e :
  In e (heap_entries (heap_meld a b c)) <->
    In e (heap_entries a) \/ In e (heap_entries b) \/ In e (heap_slot_entries c).
Proof.
  revert b c. induction a as [| [x |] xs IH]; intros [| [y |] ys] [c |];
    cbn [heap_meld]; rewrite ?heap_entries_digit, ?heap_entries_insert;
    repeat rewrite heap_entries_slot;
    cbn [heap_slot_entries heap_entries app]; rewrite ?in_app_iff;
    try rewrite IH.
  all: cbn [heap_slot_entries]; rewrite ?heap_entries_link; cbn [In]; tauto.
Qed.

Lemma heap_count_meld (a b : heap_forest) c :
  length (heap_entries (heap_meld a b c)) =
    length (heap_entries a) + length (heap_entries b) + length (heap_slot_entries c).
Proof.
  revert b c. induction a as [| [x |] xs IH]; intros [| [y |] ys] [c |];
    cbn [heap_meld]; rewrite ?heap_count_digit, ?heap_count_insert;
    try rewrite IH.
  all: cbn [heap_slot_entries]; rewrite ?heap_count_link;
    repeat rewrite heap_entries_slot;
    cbn [heap_slot_entries heap_entries length app]; rewrite ?length_app; lia.
Qed.

Lemma heap_valid_meld (a b : heap_forest) c r :
  heap_forest_valid r a -> heap_forest_valid r b ->
  (match c with None => True | Some t => heap_valid r t end) ->
  heap_forest_valid r (heap_meld a b c).
Proof.
  revert b c r. induction a as [| [x |] xs IH]; intros b c r Ha Hb Hc;
    cbn [heap_meld].
  - destruct c; [apply heap_valid_insert |]; assumption.
  - destruct Ha as [Hx [Hxs Hlast]]. destruct b as [| [y |] ys].
    + destruct c; [apply heap_valid_insert |]; cbn; auto.
    + destruct Hb as [Hy [Hys Hlast']].
      destruct c; apply heap_valid_digit; auto; apply IH; auto;
        apply heap_valid_link; assumption.
    + destruct Hb as [_ [Hys Hlast']].
      destruct c; apply heap_valid_digit; auto; apply IH; auto;
        apply heap_valid_link; assumption.
  - destruct Ha as [_ [Hxs Hlast]]. destruct b as [| [y |] ys].
    + destruct c; [apply heap_valid_insert |]; cbn; auto.
    + destruct Hb as [Hy [Hys Hlast']].
      destruct c; apply heap_valid_digit; auto; apply IH; auto;
        apply heap_valid_link; assumption.
    + destruct Hb as [_ [Hys Hlast']].
      destruct c; apply heap_valid_digit; auto; apply IH; auto.
Qed.

Lemma heap_select_entries (h : heap_forest) :
  match heap_select h with
  | None => heap_entries h = []
  | Some (t, rest) =>
      (forall e, In e (heap_entries h) <->
        In e (heap_tree_entries t) \/ In e (heap_entries rest)) /\
      length (heap_entries h) = length (heap_tree_entries t) + length (heap_entries rest)
  end.
Proof.
  induction h as [| [u |] xs IH]; cbn [heap_select].
  - reflexivity.
  - destruct (heap_select xs) as [[t rest] |] eqn:Hselect.
    + destruct IH as [Hin Hcount]. destruct (heap_before (heap_root u) (heap_root t)); split.
      * intro e. rewrite heap_entries_digit, heap_entries_cons.
        cbn [heap_slot_entries app]. rewrite in_app_iff. tauto.
      * rewrite heap_entries_cons, length_app, heap_entries_digit.
        cbn [heap_slot_entries app]. reflexivity.
      * intro e. rewrite heap_entries_digit, heap_entries_cons.
        cbn [heap_slot_entries]. rewrite !in_app_iff, Hin. tauto.
      * rewrite heap_count_digit, heap_entries_cons, length_app.
        cbn [heap_slot_entries]. lia.
    + split.
      * intro e. rewrite heap_entries_cons, IH, app_nil_r. cbn [heap_entries In]. tauto.
      * rewrite heap_entries_cons, IH, app_nil_r. cbn [heap_entries length]. lia.
  - destruct (heap_select xs) as [[t rest] |] eqn:Hselect.
    + destruct IH as [Hin Hcount]. split.
      * intro e. rewrite heap_entries_digit. cbn [heap_entries heap_slot_entries app]. apply Hin.
      * change (length (heap_entries xs) =
          length (heap_tree_entries t) + length (heap_entries (heap_digit None rest))).
        rewrite heap_count_digit. cbn [heap_slot_entries length]. lia.
    + exact IH.
Qed.

Lemma heap_select_valid r (h : heap_forest) :
  heap_forest_valid r h ->
  match heap_select h with
  | None => h = []
  | Some (t, rest) => (exists rank, heap_valid rank t) /\ heap_forest_valid r rest
  end.
Proof.
  revert r. induction h as [| [u |] xs IH]; intros r Hh; cbn [heap_select].
  - reflexivity.
  - destruct Hh as [Hu [Hxs Hlast]].
    specialize (IH (S r) Hxs). destruct (heap_select xs) as [[t rest] |] eqn:Hselect.
    + destruct IH as [Ht Hrest]. destruct (heap_before (heap_root u) (heap_root t)); split.
      * exists r; exact Hu.
      * apply heap_valid_digit; [exact I | exact Hxs].
      * exact Ht.
      * apply heap_valid_digit; assumption.
    + split; [exists r; exact Hu | exact I].
  - destruct Hh as [_ [Hxs Hlast]].
    specialize (IH (S r) Hxs). destruct (heap_select xs) as [[t rest] |] eqn:Hselect.
    + destruct IH as [Ht Hrest]. split; [exact Ht |].
      apply heap_valid_digit; [exact I | exact Hrest].
    + subst xs. destruct Hlast; contradiction.
Qed.

Lemma heap_select_min r (h : heap_forest) t rest :
  heap_forest_valid r h -> heap_select h = Some (t, rest) ->
  forall e, In e (heap_entries h) -> heap_precedes (heap_root t) e.
Proof.
  revert r t rest. induction h as [| [u |] xs IH]; intros r t rest Hh Hselect e Hin;
    cbn [heap_select] in Hselect.
  - discriminate.
  - destruct Hh as [Hu [Hxs Hlast]].
    destruct (heap_select xs) as [[v tail] |] eqn:Htail.
    + destruct (heap_before (heap_root u) (heap_root v)) eqn:Hcmp;
        inversion Hselect; subst t rest.
      * rewrite heap_entries_cons in Hin. apply in_app_iff in Hin.
        destruct Hin as [Hin | Hin].
        -- apply (heap_valid_root r u Hu); exact Hin.
        -- eapply heap_precedes_trans; [apply heap_before_spec; exact Hcmp |].
           apply (IH (S r) v tail Hxs eq_refl); exact Hin.
      * rewrite heap_entries_cons in Hin. apply in_app_iff in Hin.
        destruct Hin as [Hin | Hin].
        -- eapply heap_precedes_trans; [apply heap_before_false; exact Hcmp |].
           apply (heap_valid_root r u Hu); exact Hin.
        -- apply (IH (S r) v tail Hxs eq_refl); exact Hin.
    + inversion Hselect; subst t rest.
      pose proof (heap_select_entries xs) as Hempty. rewrite Htail in Hempty.
      rewrite heap_entries_cons, Hempty, app_nil_r in Hin.
      apply (heap_valid_root r u Hu); exact Hin.
  - destruct Hh as [_ [Hxs Hlast]].
    destruct (heap_select xs) as [[v tail] |] eqn:Htail; [| discriminate].
    inversion Hselect; subst t rest. cbn [heap_entries] in Hin.
    apply (IH (S r) v tail Hxs eq_refl); exact Hin.
Qed.

Lemma heap_forest_append r (a b : heap_forest) :
  heap_forest_valid r a -> heap_forest_valid (r + length a) b ->
  heap_forest_valid r (a ++ b).
Proof.
  revert r. induction a as [| s xs IH]; intros r Ha Hb; cbn in *.
  - replace (r + 0) with r in Hb by lia. exact Hb.
  - destruct Ha as [Hs [Hxs Hlast]]. split; [exact Hs |]; split.
    + apply IH; [exact Hxs |].
      replace (S r + length xs) with (r + S (length xs)) by lia. exact Hb.
    + destruct Hlast as [Hsome | Htail]; [left; exact Hsome |].
      right. intro Heq. apply app_eq_nil in Heq. tauto.
Qed.

Lemma heap_children_eq (cs : list heap_tree) :
  rev_append (map (@Some heap_tree) cs) [] = map (@Some heap_tree) (rev cs).
Proof. rewrite <- rev_alt, <- map_rev. reflexivity. Qed.

Lemma heap_valid_children r (e : heap_entry) (cs : list heap_tree) :
  heap_valid r (HeapTree e cs) ->
  heap_forest_valid 0 (rev_append (map (@Some heap_tree) cs) []) /\ length cs = r.
Proof.
  revert e cs. induction r as [| r IH]; intros e cs Hvalid.
  - inversion Hvalid; subst. split; [exact I | reflexivity].
  - inversion Hvalid as [e0 | r0 e0 cs0 b Hbase Hchild Hbefore]; subst.
    destruct (IH _ _ Hbase) as [Hcs Hlength].
    rewrite heap_children_eq in Hcs |- *. cbn [rev]. rewrite map_app. cbn [map length].
    split.
    + apply heap_forest_append; [exact Hcs |].
      rewrite length_map, length_rev, Hlength. cbn.
      split; [exact Hchild |]; split; [exact I | left; discriminate].
    + lia.
Qed.

Lemma heap_entries_some (ts : list heap_tree) :
  heap_entries (map (@Some heap_tree) ts) = flat_map heap_tree_entries ts.
Proof.
  induction ts as [| t ts IH]; cbn [map flat_map]; [reflexivity |].
  rewrite heap_entries_cons, IH. reflexivity.
Qed.

Lemma heap_entries_children (e : heap_entry) (cs : list heap_tree) a :
  In a (heap_tree_entries (HeapTree e cs)) <->
    a = e \/ In a (heap_entries (rev_append (map (@Some heap_tree) cs) [])).
Proof.
  rewrite heap_tree_entries_eq, heap_children_eq, heap_entries_some.
  cbn [In]. rewrite !in_flat_map. split.
  - intros [Heq | [t [Ht Hin]]]; [left; congruence | right].
    exists t. split; [apply (proj1 (in_rev cs t)); exact Ht | exact Hin].
  - intros [Heq | [t [Ht Hin]]]; [left; congruence | right].
    exists t. split; [apply (proj2 (in_rev cs t)); exact Ht | exact Hin].
Qed.

Lemma heap_count_children (e : heap_entry) (cs : list heap_tree) :
  length (heap_tree_entries (HeapTree e cs)) =
    S (length (heap_entries (rev_append (map (@Some heap_tree) cs) []))).
Proof.
  rewrite heap_tree_entries_eq, heap_children_eq, heap_entries_some.
  cbn [length]. f_equal.
  induction cs as [| t cs IH]; cbn [flat_map rev]; [reflexivity |].
  rewrite flat_map_app, !length_app. cbn [flat_map]. rewrite app_nil_r. lia.
Qed.

Lemma heap_remove_min_correct (h : heap_forest) :
  heap_forest_valid 0 h ->
  match heap_remove_min h with
  | None => heap_entries h = []
  | Some (e, rest) =>
      heap_forest_valid 0 rest /\
      (forall a, In a (heap_entries h) <-> a = e \/ In a (heap_entries rest)) /\
      length (heap_entries h) = S (length (heap_entries rest)) /\
      (forall a, In a (heap_entries h) -> heap_precedes e a)
  end.
Proof.
  intro Hvalid. unfold heap_remove_min.
  pose proof (heap_select_entries h) as Hentries.
  pose proof (heap_select_valid 0 h Hvalid) as Hshape.
  destruct (heap_select h) as [[[e cs] rest] |] eqn:Hselect; [| exact Hentries].
  destruct Hentries as [Hin Hcount], Hshape as [[rank Htree] Hrest].
  split.
  - apply heap_valid_meld.
    + exact (proj1 (heap_valid_children rank e cs Htree)).
    + exact Hrest.
    + exact I.
  - split.
    + intro a. rewrite Hin, heap_entries_children, heap_entries_meld.
      cbn [heap_slot_entries In]. tauto.
    + split.
      * rewrite heap_count_meld. cbn [heap_slot_entries length].
        rewrite heap_count_children in Hcount. lia.
      * apply (heap_select_min 0 h (HeapTree e cs) rest Hvalid Hselect).
Qed.

Lemma heap_valid_size r tr :
  heap_valid r tr -> length (heap_tree_entries tr) = 2 ^ r.
Proof.
  intro Hvalid.
  induction Hvalid as [e|r e cs b Hbase IHbase Hchild IHchild Hbefore].
  - rewrite heap_tree_entries_eq. reflexivity.
  - rewrite !heap_tree_entries_eq in *.
    cbn [flat_map length] in *. rewrite length_app.
    rewrite Nat.pow_succ_r by lia. lia.
Qed.

(** A canonical forest's final occupied rank bounds its entry count from below. *)
Lemma heap_forest_height_bound r h :
  heap_forest_valid r h -> h <> [] ->
  2 ^ (r + length h) <= 2 * length (heap_entries h).
Proof.
  revert r. induction h as [|[tr|] hs IH]; intros r Hforest Hnonempty.
  - contradiction.
  - destruct Hforest as [Ht [Hhs Hlast]]. destruct hs as [|s ss].
    + cbn [length]. rewrite Nat.add_1_r, Nat.pow_succ_r by lia.
      rewrite heap_entries_cons. cbn [heap_entries]. rewrite app_nil_r.
      rewrite (heap_valid_size r tr Ht). lia.
    + specialize (IH (S r) Hhs ltac:(discriminate)).
      replace (S r + length (s :: ss)) with (r + length (Some tr :: s :: ss)) in IH
        by (cbn [length]; lia).
      rewrite heap_entries_cons, length_app. lia.
  - destruct Hforest as [_ [Hhs Hlast]]. destruct hs as [|s ss].
    + destruct Hlast; contradiction.
    + specialize (IH (S r) Hhs ltac:(discriminate)).
      replace (S r + length (s :: ss)) with (r + length (None :: s :: ss)) in IH
        by (cbn [length]; lia).
      exact IH.
Qed.

(** Canonical forests occupy logarithmically many rank positions. *)
Lemma heap_forest_width h :
  heap_forest_valid 0 h ->
  length h <= Nat.log2 (length (heap_entries h)) + 1.
Proof.
  intro Hvalid. destruct h as [|s hs]; [cbn [length]; lia|].
  pose proof (heap_forest_height_bound 0 (s :: hs) Hvalid
    ltac:(discriminate)) as Hheight.
  cbn [length Nat.add] in Hheight.
  rewrite Nat.pow_succ_r in Hheight by lia.
  assert (Hcount : 0 < length (heap_entries (s :: hs))).
  { pose proof (Nat.pow_nonzero 2 (length hs) ltac:(lia)). nia. }
  assert (Hpow : 2 ^ length hs <= length (heap_entries (s :: hs))) by nia.
  apply (proj1 (Nat.log2_le_pow2 (length (heap_entries (s :: hs)))
    (length hs) Hcount)) in Hpow.
  cbn [length]. lia.
Qed.

(** The occupied ranks fit strictly below the next binary capacity. *)
Lemma heap_forest_count_capacity start h :
  heap_forest_valid start h ->
  length (heap_entries h) + 2 ^ start <= 2 ^ (start + length h).
Proof.
  revert start. induction h as [|[tr|] rest IH]; intros start Hvalid.
  - cbn [length]. rewrite Nat.add_0_r. cbn [heap_entries length]. lia.
  - destruct Hvalid as [Ht [Hrest Hlast]]. specialize (IH (S start) Hrest).
    rewrite heap_entries_cons, length_app, (heap_valid_size start tr Ht).
    cbn [length]. replace (start + S (length rest)) with (S start + length rest) by lia.
    rewrite Nat.pow_succ_r in IH by lia. lia.
  - destruct Hvalid as [_ [Hrest Hlast]]. specialize (IH (S start) Hrest).
    cbn [heap_entries length].
    replace (start + S (length rest)) with (S start + length rest) by lia.
    rewrite Nat.pow_succ_r in IH by lia. lia.
Qed.

(** Fuel has one leading bit after its forest-position bits. *)
Lemma heap_fuel_size h : Pos.size_nat (heap_fuel h) = S (length h).
Proof.
  induction h as [|s hs IH]; cbn [heap_fuel Pos.size_nat length];
    rewrite ?IH; reflexivity.
Qed.

(** The constructed fuel is the next power of two above the forest's capacity. *)
Lemma heap_fuel_value h : Pos.to_nat (heap_fuel h) = 2 ^ length h.
Proof.
  induction h as [|s hs IH]; cbn [heap_fuel length]; [reflexivity|].
  rewrite Pos2Nat.inj_xO, IH, Nat.pow_succ_r by lia. lia.
Qed.

Lemma heap_fuel_capacity h :
  heap_forest_valid 0 h ->
  (N.of_nat (length (heap_entries h)) < N.pos (heap_fuel h))%N.
Proof.
  intro Hvalid. pose proof (heap_forest_count_capacity 0 h Hvalid) as Hcapacity.
  cbn [Nat.add Nat.pow] in Hcapacity. rewrite <- heap_fuel_value in Hcapacity. lia.
Qed.

(** Trimming a digit adds at most one rank position. *)
Lemma heap_digit_length s h : length (heap_digit s h) <= S (length h).
Proof.
  destruct s, h; cbn [heap_digit length]; lia.
Qed.

(** A valid tree's child spine records exactly its rank. *)
Lemma heap_valid_rank_children r e cs :
  heap_valid r (HeapTree e cs) -> length cs = r.
Proof.
  intro Hvalid. remember (HeapTree e cs) as tr eqn:Htr.
  revert e cs Htr. induction Hvalid as [a|r a xs b Hbase IH Hchild IHchild Hbefore];
    intros e cs Htr; inversion Htr; subst; [reflexivity|].
  cbn [length]. f_equal. eapply IH. reflexivity.
Qed.

(** Selecting a tree cannot lengthen the remaining forest. *)
Lemma heap_select_length h tr rest :
  heap_select h = Some (tr, rest) -> length rest <= length h.
Proof.
  revert tr rest. induction h as [|[u|] xs IH]; intros tr rest Hselect;
    cbn [heap_select] in Hselect; [discriminate| |].
  - destruct (heap_select xs) as [[v tail]|] eqn:Htail.
    + specialize (IH v tail eq_refl).
      destruct (heap_before (heap_root u) (heap_root v)).
      * inversion Hselect; subst tr rest. exact (heap_digit_length None xs).
      * inversion Hselect; subst tr rest.
        change (S (length tail) <= S (length xs)). lia.
    + inversion Hselect; subst tr rest. cbn [length]. lia.
  - destruct (heap_select xs) as [[v tail]|] eqn:Htail; [|discriminate].
    specialize (IH v tail eq_refl). inversion Hselect; subst tr rest.
    eapply Nat.le_trans; [exact (heap_digit_length None tail)|]. cbn [length]. lia.
Qed.

(** The selected tree occupies one of the input forest's valid rank positions. *)
Lemma heap_select_rank_bounds r h e cs rest :
  heap_forest_valid r h ->
  heap_select h = Some (HeapTree e cs, rest) ->
  r <= length cs /\ length cs < r + length h.
Proof.
  revert r e cs rest. induction h as [|[u|] xs IH]; intros r e cs rest Hvalid Hselect;
    cbn [heap_select] in Hselect; [discriminate| |].
  - destruct Hvalid as [Hu [Hxs Hlast]]. destruct u as [a us].
    pose proof (heap_valid_rank_children r a us Hu) as Hrank.
    destruct (heap_select xs) as [[[b vs] tail]|] eqn:Htail.
    + destruct (heap_before (heap_root (HeapTree a us)) (heap_root (HeapTree b vs)));
        inversion Hselect; subst e cs rest.
      * cbn [length]. lia.
      * specialize (IH (S r) b vs tail Hxs eq_refl). cbn [length]. lia.
    + inversion Hselect; subst e cs rest. cbn [length]. lia.
  - destruct Hvalid as [_ [Hxs Hlast]].
    destruct (heap_select xs) as [[[b vs] tail]|] eqn:Htail; [|discriminate].
    inversion Hselect; subst e cs rest.
    specialize (IH (S r) b vs tail Hxs eq_refl). cbn [length]. lia.
Qed.

(** A bounded binary counter fits within the bound's logarithmic bit width. *)
Lemma heap_counter_width (n : N) (P : nat) :
  N.to_nat n <= P -> N.size_nat n <= Nat.log2 P + 1.
Proof.
  destruct n as [|p]; intro Hbound; [cbn [N.size_nat]; lia |].
  change (Pos.to_nat p <= P) in Hbound.
  change (Pos.size_nat p <= Nat.log2 P + 1). apply Pos.size_nat_least.
  pose proof (Pos2Nat.is_pos p) as Hpositive.
  pose proof (proj2 (Nat.log2_spec P ltac:(lia))) as Hpower.
  replace (Nat.log2 P + 1) with (S (Nat.log2 P)) by lia. lia.
Qed.

Module Heap <: PQ.
  Include HeapCode.
  Definition prio (q : t) (x : positive) := PTrieCode.get x (live q).
  Definition wf (q : t) : Prop :=
    heap_forest_valid 0 (pending q) /\
    (forall k p, prio q k = Some p -> In (p, k) (heap_entries (pending q))) /\
    live_count q = N.of_nat (length (PTrieCode.elements (live q))) /\
    pending_count q = N.of_nat (length (heap_entries (pending q))).
  Definition pending (q : t) : nat := N.to_nat (pending_count q).
  Lemma wf_empty : wf empty.
  Proof.
    split; [exact I|]; split.
    - intros k p Hget; unfold prio, empty in Hget; cbn in Hget.
      rewrite PTrie.get_empty in Hget; discriminate.
    - split; reflexivity.
  Qed.
  Lemma prio_empty : forall x, prio empty x = None.
  Proof. intro x; apply PTrie.get_empty. Qed.
  Lemma size_empty : size empty = 0%N.
  Proof. reflexivity. Qed.
  Lemma pending_empty : pending empty = 0.
  Proof. reflexivity. Qed.

  (** A trie node contributes its optional root and both subtrie cardinalities. *)
  Lemma live_length_node : forall A (l r : PTrieCode.t A) o,
    length (PTrieCode.elements (PTrieCode.node l o r)) =
      length (PTrieCode.elements l) +
      (match o with Some _ => 1 | None => 0 end) + length (PTrieCode.elements r).
  Proof.
    intros A l r o. rewrite PTrie.elements_node, !length_app, !length_map.
    destruct o; cbn [length]; lia.
  Qed.

  (** Replacing one optional binding changes only that binding's cardinality charge. *)
  Lemma live_length_replace : forall A p o (m : PTrieCode.t A),
    length (PTrieCode.elements (PTrieCode.replace p o m)) +
      (match PTrieCode.get p m with Some _ => 1 | None => 0 end) =
    length (PTrieCode.elements m) + (match o with Some _ => 1 | None => 0 end).
  Proof.
    intros A p. induction p; intros o m.
    all: assert (Hcount : length (PTrieCode.elements m) =
      length (PTrieCode.elements (PTrieCode.left m)) +
      (match PTrieCode.value m with Some _ => 1 | None => 0 end) +
      length (PTrieCode.elements (PTrieCode.right m))).
    all: try (rewrite <- (PTrieT.F1_node A m) at 1; apply live_length_node).
    all: cbn [PTrieCode.replace]; rewrite live_length_node, Hcount, PTrie.get_equation.
    - specialize (IHp o (PTrieCode.right m)). lia.
    - specialize (IHp o (PTrieCode.left m)). lia.
    - lia.
  Qed.

  (** Insertion adds one live binding precisely when its code was absent. *)
  Lemma live_length_set : forall A p (a : A) (m : PTrieCode.t A),
    length (PTrieCode.elements (PTrieCode.set p a m)) =
      match PTrieCode.get p m with
      | Some _ => length (PTrieCode.elements m)
      | None => S (length (PTrieCode.elements m))
      end.
  Proof.
    intros A p a m. pose proof (live_length_replace A p (Some a) m) as Hcount.
    unfold PTrieCode.set. destruct (PTrieCode.get p m);
      cbn beta iota zeta in Hcount |- *; lia.
  Qed.

  (** Removing a present binding decreases the live cardinality by exactly one. *)
  Lemma live_length_remove : forall A p (a : A) (m : PTrieCode.t A),
    PTrieCode.get p m = Some a ->
    length (PTrieCode.elements m) =
      S (length (PTrieCode.elements (PTrieCode.remove p m))).
  Proof.
    intros A p a m Hget. pose proof (live_length_replace A p None m) as Hcount.
    rewrite Hget in Hcount. unfold PTrieCode.remove.
    cbn beta iota zeta in Hcount. lia.
  Qed.

  (** Enqueue preserves coverage and installs the supplied exact live cardinality. *)
  Lemma wf_inserted : forall p k q n,
    wf q -> n = N.of_nat (length (PTrieCode.elements (PTrieCode.set k p (live q)))) ->
    wf (enqueue p k q n).
  Proof.
    intros p k [h m count total] n [Hforest [Hcover [Hcount Htotal]]] Hn.
    unfold wf, enqueue. cbn [Base.Heap.pending live live_count pending_count] in *.
    split; [apply heap_valid_insert; [apply HeapValid_zero | exact Hforest] |].
    split.
    - intros a v Hget. unfold prio in Hget. cbn [live] in Hget.
      apply heap_entries_insert. destruct (Pos.eq_dec a k) as [Heq | Hne].
      + subst a. rewrite PTrie.get_set_same in Hget. inversion Hget; subst v.
        left. rewrite heap_tree_entries_eq. left; reflexivity.
      + right. apply Hcover. rewrite PTrie.get_set_other in Hget by congruence.
        exact Hget.
    - split; [exact Hn |]. rewrite heap_count_insert, heap_tree_entries_eq.
      cbn [flat_map length]. rewrite Nat2N.inj_succ, Htotal. reflexivity.
  Qed.

  Lemma wf_push : forall p x q, wf q -> wf (push p x q).
  Proof.
    intros p x q Hwf. unfold push.
    destruct (PTrieCode.get x (live q)) as [old |] eqn:Hget.
    - destruct (N.ltb p old); [|exact Hwf].
      apply wf_inserted; [exact Hwf |]. rewrite live_length_set, Hget.
      exact (proj1 (proj2 (proj2 Hwf))).
    - apply wf_inserted; [exact Hwf |]. rewrite live_length_set, Hget, Nat2N.inj_succ.
      rewrite (proj1 (proj2 (proj2 Hwf))). reflexivity.
  Qed.

  (** A first-step result is the public result because the constructed fuel is positive. *)
  Lemma pop_step_stop : forall q result,
    heap_pop_step (live q) (live_count q) (heap_pending q, pending_count q) = inr result ->
    pop q = result.
  Proof.
    intros [h m n total] result Hstop.
    cbn [heap_pending live live_count pending_count] in Hstop.
    unfold pop, loopN.
    lazymatch goal with
    | |- context [Argent.Loop.loop _ _ _ ?Hacc] => generalize Hacc
    end.
    intro Hacc. destruct Hacc.
    cbn [Argent.Loop.loop loopN_step live live_count Base.Heap.pending pending_count].
    rewrite Hstop. reflexivity.
  Qed.

  (** Removing one forest entry preserves every live binding distinct from that entry. *)
  Lemma wf_drop : forall h m n total e rest m1 n1,
    wf (Queue h m n total) -> heap_remove_min h = Some (e, rest) ->
    (forall a v, PTrieCode.get a m1 = Some v ->
      PTrieCode.get a m = Some v /\ (v, a) <> e) ->
    n1 = N.of_nat (length (PTrieCode.elements m1)) ->
    wf (Queue rest m1 n1 (N.pred total)).
  Proof.
    intros h m n total e rest m1 n1 [Hforest [Hcover [Hn Htotal]]]
      Hremove Hlookup Hn1.
    pose proof (heap_remove_min_correct h Hforest) as Hheap. rewrite Hremove in Hheap.
    destruct Hheap as [Hrest [Hin [Hcount Hmin]]].
    split; [exact Hrest |]; split.
    - intros a v Hget. destruct (Hlookup a v Hget) as [Hold Hne].
      specialize (Hcover a v Hold). apply Hin in Hcover.
      destruct Hcover as [Heq | Hinrest]; [contradiction | exact Hinrest].
    - split; [exact Hn1 |].
      cbn [Base.Heap.pending pending_count] in Htotal |- *.
      rewrite Htotal, Hcount, Nat2N.inj_succ. apply N.pred_succ.
  Qed.

  (** A stale forest entry can be discarded while retaining the live map. *)
  Lemma wf_skip : forall h p k rest m n total,
    wf (Queue h m n total) -> heap_remove_min h = Some ((p, k), rest) ->
    PTrieCode.get k m <> Some p -> wf (Queue rest m n (N.pred total)).
  Proof.
    intros h p k rest m n total Hwf Hremove Hstale.
    apply (wf_drop h m n total (p, k) rest m n); try assumption.
    - intros a v Hget. split; [exact Hget |].
      intro Heq. inversion Heq; subst. apply Hstale; exact Hget.
    - exact (proj1 (proj2 (proj2 Hwf))).
  Qed.

  (** Taking a live minimum removes exactly one live binding and one forest entry. *)
  Lemma wf_take : forall h p k rest m n total,
    wf (Queue h m n total) -> heap_remove_min h = Some ((p, k), rest) ->
    PTrieCode.get k m = Some p ->
    wf (Queue rest (PTrieCode.remove k m) (N.pred n) (N.pred total)) /\
    n = N.succ (N.pred n).
  Proof.
    intros h p k rest m n total Hwf Hremove Hget.
    pose proof (live_length_remove N k p m Hget) as Hsize.
    pose proof (proj1 (proj2 (proj2 Hwf))) as Hn.
    cbn [live live_count] in Hn. rewrite Hsize, Nat2N.inj_succ in Hn.
    split; [|lia]. apply (wf_drop h m n total (p, k) rest).
    - exact Hwf.
    - exact Hremove.
    - intros a v Hlookup. destruct (Pos.eq_dec a k) as [Heq | Hne].
      + subst a. rewrite PTrie.get_remove_same in Hlookup. discriminate.
      + rewrite PTrie.get_remove_other in Hlookup by congruence.
        split; [exact Hlookup |]. intro Heq. inversion Heq; contradiction.
    - lia.
  Qed.

  (** An empty pending forest cannot cover any live binding. *)
  Lemma empty_entries_live : forall h m n total,
    wf (Queue h m n total) -> heap_entries h = [] ->
    forall k, PTrieCode.get k m = None.
  Proof.
    intros h m n total Hwf Hempty k.
    destruct (PTrieCode.get k m) as [p |] eqn:Hget; [|reflexivity].
    pose proof (proj1 (proj2 Hwf) k p Hget) as Hin.
    cbn [Base.Heap.pending] in Hin. rewrite Hempty in Hin. contradiction.
  Qed.

  (** A successful run returns a minimum live entry and only discards forest entries. *)
  Definition pop_result (h : heap_forest) (m : PTrieCode.t N) (n total : N)
      (result : option (N * positive * t)) : Prop :=
    match result with
    | None => forall k, PTrieCode.get k m = None
    | Some (p, k, rest) =>
        PTrieCode.get k m = Some p /\
        (forall a v, PTrieCode.get a m = Some v -> (p <= v)%N) /\
        live rest = PTrieCode.remove k m /\ n = N.succ (size rest) /\ wf rest /\
        (pending_count rest < total)%N /\
        incl (heap_entries (heap_pending rest)) (heap_entries h)
    end.

  (** A result remains valid when its source forest and pending budget are enlarged. *)
  Lemma pop_result_weaken : forall h1 h2 m n total1 total2 result,
    incl (heap_entries h1) (heap_entries h2) -> (total1 <= total2)%N ->
    pop_result h1 m n total1 result -> pop_result h2 m n total2 result.
  Proof.
    intros h1 h2 m n total1 total2 result Hincl Htotal Hresult.
    destruct result as [[[p k] rest] |]; [|exact Hresult].
    destruct Hresult as [Hget [Hmin [Hlive [Hsize [Hwf [Hpending Hentries]]]]]].
    split; [exact Hget |]; split; [exact Hmin |]; split; [exact Hlive |].
    split; [exact Hsize |]; split; [exact Hwf |]; split; [lia |].
    intros a Ha. apply Hincl, Hentries; exact Ha.
  Qed.

  (** The accessibility loop preserves live data while each stale step removes one entry. *)
  Lemma pop_loop_correct : forall m n fs (H : Acc loopN_lt fs),
    wf (Queue (fst (snd fs)) m n (snd (snd fs))) ->
    (snd (snd fs) <= fst fs)%N ->
    pop_result (fst (snd fs)) m n (snd (snd fs))
      (match Argent.Loop.loop loopN_lt (loopN_step (heap_pop_step m n)) fs H with
       | inl _ => None | inr result => result
       end).
  Proof.
    intros m n fs H. induction H as [[fuel [h total]] Hacc IH] using Acc_ind_dep.
    cbn [fst snd]. intros Hwf Hfuel. destruct fuel as [|fuel].
    - cbn [Argent.Loop.loop loopN_step].
      assert (Hempty : heap_entries h = []).
      { apply length_zero_iff_nil.
        pose proof (proj2 (proj2 (proj2 Hwf))) as Hcount.
        cbn [Base.Heap.pending pending_count] in Hcount. lia. }
      exact (empty_entries_live h m n total Hwf Hempty).
    - cbn [Argent.Loop.loop loopN_step Acc_inv]. unfold heap_pop_step at 1.
      pose proof (heap_remove_min_correct h (proj1 Hwf)) as Hheap.
      destruct (heap_remove_min h) as [[[p k] rest] |] eqn:Hremove.
      + destruct Hheap as [Hrest [Hentries [Hcount Hmin]]].
        pose proof (proj2 (proj2 (proj2 Hwf))) as Htotal.
        cbn [Base.Heap.pending pending_count] in Htotal.
        rewrite Hcount, Nat2N.inj_succ in Htotal.
        destruct (PTrieCode.get k m) as [current |] eqn:Hget.
        * destruct (N.eqb p current) eqn:Heq.
          -- apply N.eqb_eq in Heq. subst current.
             destruct (wf_take h p k rest m n total Hwf Hremove Hget) as [Hnew Hn].
             cbn [pop_result live heap_pending size live_count pending_count].
             split; [exact Hget |]; split.
             ++ intros a v Hvalue. apply (heap_precedes_prio (p, k) (v, a)).
                apply Hmin. apply (proj1 (proj2 Hwf)); exact Hvalue.
             ++ split; [reflexivity |]; split; [exact Hn |].
                split; [exact Hnew |]; split; [lia |].
                intros a Ha. apply Hentries. right; exact Ha.
          -- eapply pop_result_weaken with (h1 := rest) (total1 := N.pred total).
             ++ intros a Ha. apply Hentries. right; exact Ha.
             ++ lia.
             ++ apply IH.
                ** apply (wf_skip h p k rest m n total Hwf Hremove).
                   rewrite Hget. intro Hequal. injection Hequal as Hequal.
                   subst current. rewrite N.eqb_refl in Heq. discriminate.
                ** cbn [fst snd]. lia.
        * eapply pop_result_weaken with (h1 := rest) (total1 := N.pred total).
          -- intros a Ha. apply Hentries. right; exact Ha.
          -- lia.
          -- apply IH.
             ++ apply (wf_skip h p k rest m n total Hwf Hremove).
                rewrite Hget. discriminate.
             ++ cbn [fst snd]. lia.
      + exact (empty_entries_live h m n total Hwf Hheap).
  Qed.

  (** Forest capacity supplies enough binary fuel for every pending entry. *)
  Lemma pop_correct : forall q, wf q ->
    pop_result (heap_pending q) (live q) (size q) (pending_count q) (pop q).
  Proof.
    intros [h m n total] Hwf. unfold pop, loopN.
    cbn [heap_pending Base.Heap.pending live live_count pending_count size].
    apply pop_loop_correct; [exact Hwf |].
    change (total <= N.pos (heap_fuel h))%N.
    pose proof (heap_fuel_capacity h (proj1 Hwf)) as Hcapacity.
    pose proof (proj2 (proj2 (proj2 Hwf))) as Hcount.
    cbn [Base.Heap.pending pending_count] in Hcount. lia.
  Qed.

  Lemma wf_pop : forall q p x q1, wf q -> pop q = Some (p, x, q1) -> wf q1.
  Proof.
    intros q p x q1 Hwf Hpop. pose proof (pop_correct q Hwf) as Hcorrect.
    rewrite Hpop in Hcorrect.
    destruct Hcorrect as [Hget [Hmin [Hlive [Hsize [Hnew Hrest]]]]]. exact Hnew.
  Qed.
  Lemma prio_push : forall p x q,
    prio (push p x q) x = Some (match prio q x with Some old => N.min p old | None => p end).
  Proof.
    intros p x q. unfold prio, push.
    destruct (PTrieCode.get x (live q)) as [old|] eqn:Hget.
    - destruct (N.ltb p old) eqn:Hlt.
      + cbn [enqueue live]. rewrite PTrie.get_set_same.
        apply N.ltb_lt in Hlt. rewrite N.min_l by lia. reflexivity.
      + apply N.ltb_ge in Hlt. rewrite N.min_r by lia. exact Hget.
    - cbn [enqueue live]. rewrite PTrie.get_set_same. reflexivity.
  Qed.
  Lemma prio_push_other : forall p x y q, x <> y -> prio (push p x q) y = prio q y.
  Proof.
    intros p x y q Hneq. unfold prio, push.
    destruct (PTrieCode.get x (live q)); [destruct (N.ltb p n)|];
      cbn [enqueue live]; try reflexivity.
    all: rewrite PTrie.get_set_other by congruence; reflexivity.
  Qed.
  Lemma pop_min : forall q p x q1, wf q -> pop q = Some (p, x, q1) ->
    prio q x = Some p /\ (forall y r, prio q y = Some r -> (p <= r)%N) /\
    prio q1 x = None /\ (forall y, y <> x -> prio q1 y = prio q y).
  Proof.
    intros q p x q1 Hwf Hpop. pose proof (pop_correct q Hwf) as Hcorrect.
    rewrite Hpop in Hcorrect. destruct Hcorrect as [Hget [Hmin [Hlive Hrest]]].
    split; [exact Hget |]; split; [exact Hmin |]; split.
    - unfold prio. rewrite Hlive. apply PTrie.get_remove_same.
    - intros y Hne. unfold prio. rewrite Hlive, PTrie.get_remove_other by congruence.
      reflexivity.
  Qed.
  Lemma pop_none : forall q, wf q -> (pop q = None <-> forall x, prio q x = None).
  Proof.
    intros q Hwf. pose proof (pop_correct q Hwf) as Hcorrect.
    destruct (pop q) as [[[p k] rest] |].
    - split; [discriminate |]. intro Hempty.
      destruct Hcorrect as [Hget Hrest]. specialize (Hempty k). unfold prio in Hempty.
      congruence.
    - split; [intro H; exact Hcorrect | intro H; reflexivity].
  Qed.
  Lemma size_push : forall p x q, wf q ->
    size (push p x q) = match prio q x with Some _ => size q | None => N.succ (size q) end.
  Proof.
    intros p x q Hwf; unfold push, prio, size; destruct (PTrieCode.get x (live q));
      [destruct (N.ltb p n)|]; reflexivity.
  Qed.
  Lemma size_pop : forall q p x q1, wf q -> pop q = Some (p, x, q1) ->
    size q = N.succ (size q1).
  Proof.
    intros q p x q1 Hwf Hpop. pose proof (pop_correct q Hwf) as Hcorrect.
    rewrite Hpop in Hcorrect.
    destruct Hcorrect as [Hget [Hmin [Hlive [Hsize Hrest]]]]. exact Hsize.
  Qed.
  Lemma pending_push : forall p x q, wf q -> pending (push p x q) <= S (pending q).
  Proof.
    intros p x q Hwf. unfold pending, push.
    destruct (PTrieCode.get x (live q)); [destruct (N.ltb p n)|];
      cbn [enqueue pending_count]; rewrite ?N2Nat.inj_succ; lia.
  Qed.
  Lemma pending_pop : forall q p x q1, wf q -> pop q = Some (p, x, q1) ->
    pending q1 < pending q.
  Proof.
    intros q p x q1 Hwf Hpop. pose proof (pop_correct q Hwf) as Hcorrect.
    rewrite Hpop in Hcorrect.
    destruct Hcorrect as [Hget [Hmin [Hlive [Hsize [Hnew [Hpending Hentries]]]]]].
    unfold pending. lia.
  Qed.
  Lemma size_pending : forall q, wf q -> N.to_nat (size q) <= pending q.
  Proof.
    intros q [Hforest [Hcover [Hlive Hpending]]].
    assert (Hincl : incl (List.map fst (PTrieCode.elements (live q)))
      (List.map snd (heap_entries (heap_pending q)))).
    { intros k Hin. apply in_map_iff in Hin as [[x p] [Heq Hin]].
      cbn [fst] in Heq. subst x. apply PTrie.elements_spec in Hin.
      apply in_map_iff. exists (p, k). split; [reflexivity|apply Hcover; exact Hin]. }
    pose proof (@NoDup_incl_length positive
      (List.map fst (PTrieCode.elements (live q)))
      (List.map snd (heap_entries (heap_pending q)))
      (PTrie.elements_nodup N (live q)) Hincl) as Hlength.
    rewrite !length_map in Hlength.
    unfold size, pending. rewrite Hlive, Hpending, !Nat2N.id. exact Hlength.
  Qed.
  Definition fits (w : nat) (q : t) : Prop :=
    forall p x, In (p, x) (heap_entries (heap_pending q)) ->
      N.size_nat p + Pos.size_nat x <= w.
  (** Any forest removal retains the width bound of its source queue. *)
  Lemma fits_drop : forall w h m n total e rest m1 n1 total1,
    wf (Queue h m n total) -> fits w (Queue h m n total) ->
    heap_remove_min h = Some (e, rest) -> fits w (Queue rest m1 n1 total1).
  Proof.
    intros w h m n total e rest m1 n1 total1 Hwf Hfits Hremove p k Hin.
    pose proof (heap_remove_min_correct h (proj1 Hwf)) as Hheap.
    rewrite Hremove in Hheap. destruct Hheap as [Hrest [Hentries Hother]].
    apply Hfits. apply Hentries. right; exact Hin.
  Qed.
  Lemma fits_empty : forall w, fits w empty.
  Proof.
    intros w p x Hin. contradiction.
  Qed.
  Lemma fits_push : forall w p x q, wf q -> fits w q ->
    Pos.size_nat x + N.size_nat p <= w -> fits w (push p x q).
  Proof.
    intros w p x q Hwf Hfits Hwidth. unfold push.
    destruct (PTrieCode.get x (live q)); [destruct (N.ltb p n) |]; try exact Hfits.
    all: intros r k Hin; change (In (r, k)
      (heap_entries (heap_insert (HeapTree (p, x) []) (heap_pending q)))) in Hin.
    all: apply heap_entries_insert in Hin; destruct Hin as [Hin | Hin].
    all: try (apply Hfits; exact Hin).
    all: rewrite heap_tree_entries_eq in Hin; cbn [flat_map In] in Hin;
      destruct Hin as [Heq | Hfalse]; [inversion Heq; subst; lia | contradiction].
  Qed.
  Lemma fits_pop : forall w q p x q1, wf q -> fits w q ->
    pop q = Some (p, x, q1) -> fits w q1.
  Proof.
    intros w q p x q1 Hwf Hfits Hpop. pose proof (pop_correct q Hwf) as Hcorrect.
    rewrite Hpop in Hcorrect.
    destruct Hcorrect as [Hget [Hmin [Hlive [Hsize [Hnew [Hpending Hentries]]]]]].
    intros r k Hin. apply Hfits, Hentries; exact Hin.
  Qed.

End Heap.

Module HeapT <: PQ_ALL.
  Include Heap.

  TimeFun size.
  TimeFun enqueue.
  TimeFun push.

  Definition unit_pq (P w : nat) : nat := (Nat.log2 P + 1) * (w + 1).
  Definition c_pq : N := 32768.
  Definition k_insert : N := 128.
  Definition k_remove : N := 512.
  Definition k_step : N := 8192.
  Definition k_credit : N := 8192.
  Definition k_driver : N := 16384.
  Definition stale (q : t) : nat := pending q - N.to_nat (size q).
  Definition credit (P w : nat) : N := (k_credit * N.of_nat (unit_pq P w))%N.
  Definition stale_phi (P w : nat) (q : t) : N :=
    (N.of_nat (stale q) * credit P w)%N.
  Definition phi (P w : nat) (q : t) : N := stale_phi P w q.

  Lemma phi_empty : forall P w, (phi P w empty = 0)%N.
  Proof.
    intros P w. reflexivity.
  Qed.
  Lemma T_size_le : forall q, (T_size q <= c_pq)%N.
  Proof.
    intro q. unfold c_pq. time_step.
  Qed.

  Definition heap := heap_forest.
  Definition forest (q : t) : heap := heap_pending q.
  Definition entries := heap_entries.
  Definition ranks (h : heap) : nat := length h.
  Definition insert (p : N) (x : positive) (h : heap) : heap :=
    heap_insert (HeapTree (p, x) []) h.
  Definition remove_min := heap_remove_min.
  Definition pop_step (q : t) : t + option (N * positive * t) :=
    match HeapCode.heap_pop_step (live q) (live_count q) (heap_pending q, pending_count q) with
    | inl (h, n) => inl (Queue h (live q) (live_count q) n)
    | inr result => inr result
    end.

  TimeFun insert.
  TimeFun remove_min.
  TimeFun pop_step.

  Definition bounded (w : nat) (q : t) : Prop := fits w q.
  Definition output_phi (P w : nat) (r : option (N * positive * t)) : N :=
    match r with Some (_, _, q1) => phi P w q1 | None => 0%N end.

  Lemma F1_pending : forall q, wf q -> length (entries (forest q)) = pending q.
  Proof.
    intros [h m n total] [_ [_ [_ Htotal]]].
    change (length (heap_entries h) = N.to_nat total).
    change (total = N.of_nat (length (heap_entries h))) in Htotal.
    rewrite Htotal, Nat2N.id. reflexivity.
  Qed.
  Lemma F2_ranks : forall P q, wf q -> pending q <= P ->
    ranks (forest q) <= Nat.log2 P + 1.
  Proof.
    intros P q Hwf Hcap.
    pose proof (heap_forest_width (forest q) (proj1 Hwf)) as Hwidth.
    change (length (forest q) <= Nat.log2 (length (entries (forest q))) + 1) in Hwidth.
    rewrite (F1_pending q Hwf) in Hwidth.
    pose proof (Nat.log2_le_mono _ _ Hcap).
    change (length (forest q) <= Nat.log2 P + 1). lia.
  Qed.
  Lemma F3_stale_push : forall p x q, wf q -> stale (push p x q) <= S (stale q).
  Proof.
    intros p x q Hwf. pose proof (pending_push p x q Hwf) as Hpending.
    assert (Hsize : N.to_nat (size q) <= N.to_nat (size (push p x q))).
    { rewrite size_push by exact Hwf. destruct (prio q x); lia. }
    unfold stale. lia.
  Qed.
  Lemma F4_skip : forall q q1, wf q -> pop_step q = inl q1 ->
    wf q1 /\ size q1 = size q /\ pending q = S (pending q1).
  Proof.
    intros [h m n total] q1 Hwf Hstep.
    unfold pop_step, HeapCode.heap_pop_step in Hstep.
    cbn [heap_pending live live_count pending_count] in Hstep.
    pose proof (heap_remove_min_correct h (proj1 Hwf)) as Hheap.
    destruct (heap_remove_min h) as [[[p k] rest] |] eqn:Hremove; [| discriminate].
    destruct Hheap as [Hrest [Hentries [Hcount Hmin]]].
    pose proof (proj2 (proj2 (proj2 Hwf))) as Htotal.
    cbn [Base.Heap.pending pending_count] in Htotal.
    rewrite Hcount, Nat2N.inj_succ in Htotal.
    assert (Hskip : PTrieCode.get k m <> Some p ->
      wf (Queue rest m n (N.pred total)) /\
      size (Queue rest m n (N.pred total)) = size (Queue h m n total) /\
      pending (Queue h m n total) = S (pending (Queue rest m n (N.pred total)))).
    { intro Hstale. split.
      - exact (wf_skip h p k rest m n total Hwf Hremove Hstale).
      - split; [reflexivity |]. unfold pending. cbn [pending_count].
        rewrite Htotal, N.pred_succ, N2Nat.inj_succ. reflexivity. }
    destruct (PTrieCode.get k m) as [current |] eqn:Hget.
    - destruct (N.eqb p current) eqn:Heq; [discriminate |].
      inversion Hstep; subst q1. apply Hskip.
      intro Hsame. inversion Hsame; subst current.
      rewrite N.eqb_refl in Heq. discriminate.
    - inversion Hstep; subst q1. apply Hskip. discriminate.
  Qed.
  Lemma F5_skip_bounded : forall w q q1, wf q -> bounded w q ->
    pop_step q = inl q1 -> bounded w q1.
  Proof.
    intros w [h m n total] q1 Hwf Hfits Hstep.
    unfold bounded in Hfits |- *.
    unfold pop_step, HeapCode.heap_pop_step in Hstep.
    cbn [heap_pending live live_count pending_count] in Hstep.
    destruct (heap_remove_min h) as [[[p k] rest] |] eqn:Hremove; [| discriminate].
    destruct (PTrieCode.get k m) as [current |];
      [destruct (N.eqb p current) |]; try discriminate;
      inversion Hstep; subst q1;
      exact (fits_drop w h m n total (p, k) rest m n (N.pred total) Hwf Hfits Hremove).
  Qed.
  Lemma F6_phi_bounded : forall P w q, wf q -> bounded w q ->
    phi P w q = stale_phi P w q.
  Proof.
    reflexivity.
  Qed.
  Lemma F7_stop : forall q r, wf q -> pop_step q = inr r -> pop q = r.
  Proof.
    intros q r Hwf Hstep. unfold pop_step in Hstep.
    destruct (HeapCode.heap_pop_step (live q) (live_count q)
      (heap_pending q, pending_count q)) as [[h total] | result] eqn:Hraw;
      [discriminate |].
    inversion Hstep; subst result. apply pop_step_stop. exact Hraw.
  Qed.
  Lemma F8_push_bounded : forall w p x q, wf q -> bounded w q ->
    N.size_nat p + Pos.size_nat x <= w -> bounded w (push p x q).
  Proof.
    intros w p x q Hwf Hbounded Hwidth. apply fits_push; try assumption. lia.
  Qed.

  (** Clock estimates only inspect root widths; payload subtrees are not traversed. *)
  Local Definition heap_root_bounded (w : nat) (tr : heap_tree) : Prop :=
    N.size_nat (fst (heap_root tr)) + Pos.size_nat (snd (heap_root tr)) <= w.

  Local Definition heap_roots_bounded (w : nat) (h : heap_forest) : Prop :=
    Forall (fun slot => match slot with
      | Some tr => heap_root_bounded w tr | None => True
      end) h.

  Local Lemma heap_before_clock w (a b : heap_entry) :
    N.size_nat (fst a) + Pos.size_nat (snd a) <= w ->
    (T_heap_before a b <= 16 * N.of_nat (w + 1))%N.
  Proof.
    destruct a as [p x], b as [q y]. intro Hwidth. cbn [fst snd] in Hwidth.
    apply time_of_nat_le in Hwidth.
    time_unfold @T_heap_before; time_unfold N.T_ltb; time_unfold Pos.T_leb.
    time_simpl; time_cbn; time_pose; time_cbn_all.
    destruct (N.ltb p q); destruct (N.eqb p q); time_cbn.
    all: rewrite !Nat2N.inj_add in *; lia.
  Qed.

  Local Lemma heap_link_root_bounded w a b :
    heap_root_bounded w a -> heap_root_bounded w b ->
    heap_root_bounded w (heap_link a b).
  Proof.
    destruct a as [e cs], b as [e' ds].
    unfold heap_root_bounded, heap_link. cbn [heap_root].
    destruct (heap_before e e'); intros Ha Hb; assumption.
  Qed.

  Local Lemma heap_link_clock w a b :
    heap_root_bounded w a -> (T_heap_link a b <= 24 * N.of_nat (w + 1))%N.
  Proof.
    intro Hwidth.
    pose proof (heap_before_clock w (heap_root a) (heap_root b) Hwidth) as Hbefore.
    destruct a as [e cs], b as [e' ds]. cbn [heap_root] in Hbefore.
    time_unfold @T_heap_link. time_simpl; time_cbn.
    rewrite Nat2N.inj_add. lia.
  Qed.

  Local Lemma heap_insert_clock w h : forall tr,
    heap_root_bounded w tr -> heap_roots_bounded w h ->
    (T_heap_insert tr h <= 32 * N.of_nat (w + 1) * N.of_nat (length h + 1))%N.
  Proof.
    remember (32 * N.of_nat (w + 1))%N as budget eqn:Hbudget.
    assert (Hunit : (1 <= N.of_nat (w + 1))%N) by (rewrite Nat2N.inj_add; lia).
    assert (Hpositive : (1 <= budget)%N) by (rewrite Hbudget; lia).
    assert (Hlink : forall a b, heap_root_bounded w a ->
      (1 + T_heap_link a b <= budget)%N).
    { intros a b Hwidth. pose proof (heap_link_clock w a b Hwidth).
      rewrite Hbudget. lia. }
    clear Hbudget Hunit.
    induction h as [|[u|] hs IH]; intros tr Hwidth Hforest.
    - time_unfold @T_heap_insert. cbn [length]. lia.
    - inversion Hforest as [|slot rest Hroot Hrest]; subst.
      pose proof (Hlink tr u Hwidth) as Htick.
      specialize (IH (heap_link tr u) (heap_link_root_bounded w tr u Hwidth Hroot) Hrest).
      time_unfold @T_heap_insert. cbn [length].
      rewrite !Nat2N.inj_add, !Nat2N.inj_succ in *.
      repeat rewrite N.mul_add_distr_l in *. lia.
    - time_unfold @T_heap_insert. cbn [length].
      rewrite !Nat2N.inj_add, !Nat2N.inj_succ. repeat rewrite N.mul_add_distr_l. lia.
  Qed.

  Local Lemma heap_select_clock w h :
    heap_roots_bounded w h ->
    (T_heap_select h <= 32 * N.of_nat (w + 1) * N.of_nat (length h + 1))%N.
  Proof.
    remember (32 * N.of_nat (w + 1))%N as budget eqn:Hbudget.
    assert (Hunit : (1 <= N.of_nat (w + 1))%N) by (rewrite Nat2N.inj_add; lia).
    assert (Hpositive : (2 <= budget)%N) by (rewrite Hbudget; lia).
    assert (Hcompare : forall a b, heap_root_bounded w a ->
      (T_heap_before (heap_root a) (heap_root b) + 4 <= budget)%N).
    { intros a b Hwidth.
      pose proof (heap_before_clock w (heap_root a) (heap_root b) Hwidth).
      rewrite Hbudget. lia. }
    clear Hbudget Hunit.
    induction h as [|[u|] hs IH]; intro Hforest.
    - time_unfold @T_heap_select. cbn [length]. lia.
    - inversion Hforest as [|slot rest Hroot Hrest]; subst.
      specialize (IH Hrest). time_unfold @T_heap_select.
      destruct (heap_select hs) as [[tr rest]|] eqn:E.
      + pose proof (Hcompare u tr Hroot) as Htick.
        destruct (heap_before (heap_root u) (heap_root tr)); time_simpl; time_cbn.
        all: rewrite !Nat2N.inj_add, !Nat2N.inj_succ in *;
          repeat rewrite N.mul_add_distr_l in *; lia.
      + time_simpl; time_cbn. rewrite !Nat2N.inj_add, !Nat2N.inj_succ in *.
        repeat rewrite N.mul_add_distr_l in *. lia.
    - inversion Hforest as [|slot rest Hroot Hrest]; subst.
      specialize (IH Hrest). time_unfold @T_heap_select.
      destruct (heap_select hs) as [[tr rest]|] eqn:E; time_simpl; time_cbn.
      all: rewrite !Nat2N.inj_add, !Nat2N.inj_succ in *;
        repeat rewrite N.mul_add_distr_l in *; lia.
  Qed.

  Local Lemma heap_meld_clock w a : forall b carry,
    heap_roots_bounded w a -> heap_roots_bounded w b ->
    (match carry with Some tr => heap_root_bounded w tr | None => True end) ->
    (T_heap_meld a b carry <=
      64 * N.of_nat (w + 1) * N.of_nat (length a + length b + 1))%N.
  Proof.
    remember (64 * N.of_nat (w + 1))%N as budget eqn:Hbudget.
    assert (Hunit : (1 <= N.of_nat (w + 1))%N) by (rewrite Nat2N.inj_add; lia).
    assert (Hpositive : (2 <= budget)%N) by (rewrite Hbudget; lia).
    assert (Hlink : forall tr u, heap_root_bounded w tr ->
      (T_heap_link tr u + 2 <= budget)%N).
    { intros tr u Hroot. pose proof (heap_link_clock w tr u Hroot).
      rewrite Hbudget. lia. }
    assert (Hinsert : forall tr h,
      heap_root_bounded w tr -> heap_roots_bounded w h ->
      (1 + T_heap_insert tr h <= budget * N.of_nat (length h + 1))%N).
    { intros tr h Hroot Hforest. pose proof (heap_insert_clock w h tr Hroot Hforest).
      assert (Hlength : (1 <= N.of_nat (length h + 1))%N) by
        (rewrite Nat2N.inj_add; lia).
      rewrite Hbudget. nia. }
    clear Hbudget Hunit.
    induction a as [|x xs IH]; intros b carry Ha Hb Hcarry.
    - destruct carry as [tr|]; time_unfold @T_heap_meld; cbn [length].
      + apply Hinsert; assumption.
      + rewrite Nat2N.inj_add. repeat rewrite N.mul_add_distr_l. lia.
    - inversion Ha as [|slot tail Hx Hxs]; subst.
      destruct b as [|y ys].
      + destruct carry as [tr|]; time_unfold @T_heap_meld.
        * pose proof (Hinsert tr (x :: xs) Hcarry Ha) as Hcarry_insert.
          cbn [length]. rewrite Nat.add_0_r. exact Hcarry_insert.
        * cbn [length]. rewrite Nat.add_0_r, Nat2N.inj_add, Nat2N.inj_succ.
          repeat rewrite N.mul_add_distr_l. lia.
      + inversion Hb as [|slot tail Hy Hys]; subst.
        destruct x as [tr|], y as [u|], carry as [c|]; time_unfold @T_heap_meld.
        all: match goal with
          | |- context [T_heap_meld ?tail_a ?tail_b ?next] =>
            let Hnext := fresh "Hnext" in
            assert (Hnext : match next with
              | Some tree => heap_root_bounded w tree | None => True end) by
              (first [exact I | apply heap_link_root_bounded; assumption]);
            pose proof (IH tail_b next Hxs Hys Hnext) as Hmerge
          end.
        all: try match goal with
          | |- context [T_heap_link ?tr ?u] =>
            pose proof (Hlink tr u ltac:(assumption)) as Htick
          end.
        all: time_simpl; cbn [length] in *;
          rewrite ?Nat2N.inj_add, ?Nat2N.inj_succ in *; time_cbn_all;
          repeat rewrite N.mul_add_distr_l in *; lia.
  Qed.

  Local Lemma heap_roots_from_entries w h :
    (forall e, In e (heap_entries h) ->
      N.size_nat (fst e) + Pos.size_nat (snd e) <= w) ->
    heap_roots_bounded w h.
  Proof.
    induction h as [|[tr|] hs IH]; intro Hwidth; constructor.
    - unfold heap_root_bounded. apply Hwidth.
      rewrite heap_entries_cons. apply in_or_app. left. apply heap_root_in.
    - apply IH. intros e Hin. apply Hwidth.
      rewrite heap_entries_cons. apply in_or_app. right. exact Hin.
    - exact I.
    - apply IH. exact Hwidth.
  Qed.

  Local Lemma heap_remove_min_clock w h :
    heap_forest_valid 0 h ->
    (forall e, In e (heap_entries h) ->
      N.size_nat (fst e) + Pos.size_nat (snd e) <= w) ->
    (T_heap_remove_min h <=
      192 * N.of_nat (w + 1) * N.of_nat (length h + 1))%N.
  Proof.
    intros Hvalid Hwidth.
    pose proof (heap_select_clock w h (heap_roots_from_entries w h Hwidth)) as Hselect_clock.
    pose proof (heap_select_entries h) as Hentries.
    time_unfold @T_heap_remove_min.
    destruct (heap_select h) as [[[e cs] rest]|] eqn:Hselect.
    - destruct Hentries as [Hin Hcount].
      pose proof (heap_select_length h (HeapTree e cs) rest Hselect) as Hrest_length.
      pose proof (heap_select_rank_bounds 0 h e cs rest Hvalid Hselect) as Hrank.
      assert (Hrest : heap_roots_bounded w rest).
      { apply heap_roots_from_entries. intros a Ha. apply Hwidth.
        apply (proj2 (Hin a)). right. exact Ha. }
      assert (Hchildren : heap_roots_bounded w (rev_append (map (@Some heap_tree) cs) [])).
      { apply heap_roots_from_entries. intros a Ha. apply Hwidth.
        apply (proj2 (Hin a)). left. apply (proj2 (heap_entries_children e cs a)).
        right. exact Ha. }
      pose proof (heap_meld_clock w (rev_append (map (@Some heap_tree) cs) [])
        rest None Hchildren Hrest I) as Hmeld.
      pose proof (ListDef.T_map_le (@Some heap_tree) (fun _ => 1%N) 1%N cs
        (fun _ => N.le_refl 1)) as Hmap.
      pose proof (List.T_rev_append_le (map (@Some heap_tree) cs) []) as Hreverse.
      assert (Hchildren_length :
        length (rev_append (map (@Some heap_tree) cs) []) = length cs).
      { rewrite heap_children_eq, length_map, length_rev. reflexivity. }
      rewrite Hchildren_length in Hmeld.
      rewrite length_map in Hreverse.
      time_simpl; time_cbn.
      apply time_of_nat_le in Hrest_length.
      destruct Hrank as [_ Hrank]. cbn [Nat.add] in Hrank.
      assert (Hchild_length : (N.of_nat (length cs) + 1 <= N.of_nat (length h))%N) by lia.
      assert (Hwidth_positive : (1 <= N.of_nat (w + 1))%N) by
        (rewrite Nat2N.inj_add; lia).
      repeat rewrite Nat2N.inj_add in Hselect_clock, Hmeld |- *.
      nia.
    - assert (Hwidth_positive : (1 <= N.of_nat (w + 1))%N) by
        (rewrite Nat2N.inj_add; lia).
      rewrite !Nat2N.inj_add in Hselect_clock |- *. nia.
  Qed.

  Lemma T1_insert : forall P w p x q,
    (wf q -> bounded w q -> (pending q < P)%nat ->
    (N.size_nat p + Pos.size_nat x <= w)%nat ->
    T_insert p x (forest q) <= k_insert * N.of_nat (unit_pq P w))%N.
  Proof.
    intros P w p x q Hwf Hbounded Hpending Hentry.
    assert (Hforest : heap_roots_bounded w (forest q)).
    { apply heap_roots_from_entries. intros [a k] Hin. apply Hbounded. exact Hin. }
    assert (Hroot : heap_root_bounded w (HeapTree (p, x) [])).
    { exact Hentry. }
    pose proof (heap_insert_clock w (forest q) (HeapTree (p, x) []) Hroot Hforest) as Hclock.
    pose proof (F2_ranks P q Hwf ltac:(lia)) as Hrank.
    unfold ranks in Hrank. apply time_of_nat_le in Hrank.
    time_unfold @T_insert.
    unfold k_insert, unit_pq. rewrite Nat2N.inj_mul, !Nat2N.inj_add in *.
    nia.
  Qed.
  Lemma T2_remove_min : forall P w q,
    (wf q -> bounded w q -> (pending q <= P)%nat ->
    T_remove_min (forest q) <= k_remove * N.of_nat (unit_pq P w))%N.
  Proof.
    intros P w q Hwf Hbounded Hpending.
    assert (Hvalid : heap_forest_valid 0 (forest q)).
    { exact (proj1 Hwf). }
    assert (Hwidth : forall e, In e (heap_entries (forest q)) ->
      N.size_nat (fst e) + Pos.size_nat (snd e) <= w).
    { intros [p x] Hin. apply Hbounded. exact Hin. }
    pose proof (heap_remove_min_clock w (forest q) Hvalid Hwidth) as Hclock.
    pose proof (F2_ranks P q Hwf Hpending) as Hrank.
    unfold ranks in Hrank. apply time_of_nat_le in Hrank.
    time_unfold @T_remove_min.
    unfold k_remove, unit_pq. rewrite Nat2N.inj_mul, !Nat2N.inj_add in *.
    nia.
  Qed.
  Local Lemma pop_step_clock P w q :
    wf q -> bounded w q -> pending q <= P ->
    (T_pop_step q + c_loopN <= k_step * N.of_nat (unit_pq P w))%N.
  Proof.
    intros Hwf Hbounded Hpending.
    assert (Hunit_bounds :
      (1 <= N.of_nat (unit_pq P w) /\
       N.of_nat (Nat.log2 P + 1) <= N.of_nat (unit_pq P w) /\
       N.of_nat (w + 1) <= N.of_nat (unit_pq P w))%N).
    { unfold unit_pq. rewrite Nat2N.inj_mul, !Nat2N.inj_add. nia. }
    destruct Hunit_bounds as [Hunit_positive [Hunit_log Hunit_width]].
    pose proof (T2_remove_min P w q Hwf Hbounded Hpending) as Hremove.
    pose proof (heap_counter_width (pending_count q) P Hpending) as Htotal_width.
    assert (Hlive_capacity : N.to_nat (live_count q) <= P).
    { pose proof (size_pending q Hwf). change (N.to_nat (size q) <= P). lia. }
    pose proof (heap_counter_width (live_count q) P Hlive_capacity) as Hlive_width.
    pose proof (N.T_pred_le (pending_count q)) as Htotal_pred.
    pose proof (N.T_pred_le (live_count q)) as Hlive_pred.
    apply time_of_nat_le in Htotal_width. apply time_of_nat_le in Hlive_width.
    assert (Htotal_unit : (N.of_nat (N.size_nat (pending_count q)) <=
      N.of_nat (unit_pq P w))%N) by lia.
    assert (Hlive_unit : (N.of_nat (N.size_nat (live_count q)) <=
      N.of_nat (unit_pq P w))%N) by lia.
    pose proof (heap_remove_min_correct (forest q) (proj1 Hwf)) as Hentries.
    unfold forest in Hremove, Hentries. unfold T_remove_min in Hremove.
    time_unfold @T_pop_step. time_unfold @HeapCode.T_heap_pop_step.
    destruct (heap_remove_min (heap_pending q)) as [[[p x] rest]|] eqn:Hmin.
    - destruct Hentries as [Hrest [Hin [Hcount Hmin_order]]].
      assert (Hentry : N.size_nat p + Pos.size_nat x <= w).
      { apply Hbounded. apply (proj2 (Hin (p, x))). left. reflexivity. }
      pose proof (PTrieT.T_get_le N x (live q)) as Hget.
      pose proof (PTrieT.T_remove_le N x (live q)) as Hdelete.
      change (PTrieCode.T_get x (live q) <=
        PTrieT.c_trie * N.of_nat (Pos.size_nat x + 1))%N in Hget.
      change (PTrieCode.T_remove x (live q) <=
        PTrieT.c_trie * N.of_nat (Pos.size_nat x + 1))%N in Hdelete.
      assert (Hentry_width : (N.of_nat (Pos.size_nat x + 1) <=
        N.of_nat (w + 1))%N) by (apply time_of_nat_le; lia).
      assert (Hpriority_width : (N.of_nat (N.size_nat p + 1) <=
        N.of_nat (w + 1))%N) by (apply time_of_nat_le; lia).
      destruct (PTrieCode.get x (live q)) as [current|] eqn:Hlookup.
      + pose proof (N.T_eqb_le p current) as Hequal.
        destruct (N.eqb p current) eqn:Heq; time_simpl; time_cbn.
        all: rewrite Hmin, Hlookup, Heq; time_cbn.
        all: unfold k_step, k_remove, PTrieT.c_trie, c_loopN in *;
          repeat rewrite Nat2N.inj_add in *; lia.
      + time_simpl; time_cbn.
        rewrite Hmin, Hlookup. time_cbn.
        unfold k_step, k_remove, PTrieT.c_trie, c_loopN in *.
        repeat rewrite Nat2N.inj_add in *. lia.
    - time_simpl; time_cbn.
      rewrite Hmin. time_cbn.
      unfold k_step, k_remove, c_loopN in *. lia.
  Qed.

  Lemma T3_skip_credit : forall P w q q1,
    (wf q -> bounded w q -> (pending q <= P)%nat -> pop_step q = inl q1 ->
    T_pop_step q + c_loopN + phi P w q1 <= phi P w q)%N.
  Proof.
    intros P w q q1 Hwf Hbounded Hpending Hskip.
    pose proof (pop_step_clock P w q Hwf Hbounded Hpending) as Hclock.
    destruct (F4_skip q q1 Hwf Hskip) as [Hwf1 [Hsize Hcount]].
    pose proof (size_pending q1 Hwf1) as Hsize_count.
    assert (Hstale : stale q = S (stale q1)).
    { unfold stale. rewrite Hcount, <- Hsize. lia. }
    unfold phi, stale_phi. rewrite Hstale, Nat2N.inj_succ, N.mul_succ_l.
    unfold credit, k_credit, k_step in *. lia.
  Qed.
  Lemma T4_stop_credit : forall P w q r,
    (wf q -> bounded w q -> (pending q <= P)%nat -> pop_step q = inr r ->
    T_pop_step q + c_loopN + output_phi P w r <= k_step * N.of_nat (unit_pq P w) + phi P w q)%N.
  Proof.
    intros P w q r Hwf Hbounded Hpending Hstop.
    pose proof (pop_step_clock P w q Hwf Hbounded Hpending) as Hclock.
    pose proof (F7_stop q r Hwf Hstop) as Hpop.
    destruct r as [[[p x] q1]|]; cbn [output_phi].
    - pose proof (size_pop q p x q1 Hwf Hpop) as Hsize.
      pose proof (pending_pop q p x q1 Hwf Hpop) as Hcount.
      assert (Hstale : stale q1 <= stale q).
      { unfold stale. rewrite Hsize, N2Nat.inj_succ. lia. }
      apply time_of_nat_le in Hstale.
      pose proof (N.mul_le_mono_r _ _ (credit P w) Hstale) as Hcredit.
      unfold phi, stale_phi. lia.
    - lia.
  Qed.
  Local Lemma heap_pop_loop_credit P w h (m : PTrieCode.t N) n total fuel :
    (wf (Queue h m n total) -> bounded w (Queue h m n total) ->
    (pending (Queue h m n total) <= P)%nat ->
    T_loopN (HeapCode.heap_pop_step m n) (fun s => HeapCode.T_heap_pop_step m n s)
      fuel (h, total) +
      match loopN (HeapCode.heap_pop_step m n) fuel (h, total) with
      | inl _ => 0 | inr r => output_phi P w r
      end <= k_step * N.of_nat (unit_pq P w) + phi P w (Queue h m n total) +
        c_loopN * N.of_nat (N.size_nat fuel + 1))%N.
  Proof.
    intros Hwf Hbounded Hcap.
    assert (Hraw : forall h0 total0,
      (HeapCode.T_heap_pop_step m n (h0, total0) <=
        T_pop_step (Queue h0 m n total0))%N).
    { intros h0 total0. time_unfold @T_pop_step. time_cbn.
      destruct (HeapCode.heap_pop_step m n (h0, total0)); time_cbn; lia. }
    set (makeq := fun s : heap_forest * N => Queue (fst s) m n (snd s)).
    set (Inv := fun s => wf (makeq s) /\ bounded w (makeq s) /\ pending (makeq s) <= P).
    set (Phi := fun s => (k_step * N.of_nat (unit_pq P w) + phi P w (makeq s))%N).
    assert (Hgo : forall s s1, Inv s -> HeapCode.heap_pop_step m n s = inl s1 ->
      Inv s1 /\ (HeapCode.T_heap_pop_step m n s + c_loopN + Phi s1 <= Phi s)%N).
    { intros [h0 total0] [h1 total1] [Hwf0 [Hbound0 Hcap0]] Hnext.
      unfold makeq in Hwf0, Hbound0, Hcap0.
      cbn [fst snd] in Hwf0, Hbound0, Hcap0.
      assert (Hstep : pop_step (Queue h0 m n total0) = inl (Queue h1 m n total1)).
      { unfold pop_step. cbn [live live_count heap_pending pending_count].
        rewrite Hnext. reflexivity. }
      destruct (F4_skip _ _ Hwf0 Hstep) as [Hwf1 [Hsize Hpending]].
      pose proof (F5_skip_bounded _ _ _ Hwf0 Hbound0 Hstep) as Hbound1.
      pose proof (T3_skip_credit P w _ _ Hwf0 Hbound0 Hcap0 Hstep) as Hcredit.
      pose proof (Hraw h0 total0) as Hclock.
      split.
      - unfold Inv, makeq. cbn [fst snd]. split; [exact Hwf1|].
        split; [exact Hbound1|]. lia.
      - unfold Phi, makeq. cbn [fst snd]. lia. }
    assert (Hstop : forall s r, Inv s -> HeapCode.heap_pop_step m n s = inr r ->
      (HeapCode.T_heap_pop_step m n s + c_loopN + output_phi P w r <= Phi s)%N).
    { intros [h0 total0] r [Hwf0 [Hbound0 Hcap0]] Hnext.
      unfold makeq in Hwf0, Hbound0, Hcap0.
      cbn [fst snd] in Hwf0, Hbound0, Hcap0.
      assert (Hstep : pop_step (Queue h0 m n total0) = inr r).
      { unfold pop_step. cbn [live live_count heap_pending pending_count].
        rewrite Hnext. reflexivity. }
      pose proof (T4_stop_credit P w _ _ Hwf0 Hbound0 Hcap0 Hstep) as Hcredit.
      pose proof (Hraw h0 total0) as Hclock.
      unfold Phi, makeq. cbn [fst snd]. lia. }
    assert (Hinitial : Inv (h, total)).
    { unfold Inv, makeq. cbn [fst snd]. auto. }
    pose proof (T_loopN_amort (heap_forest * N) (option (N * positive * t))
      (HeapCode.heap_pop_step m n) (fun s => HeapCode.T_heap_pop_step m n s)
      Inv Phi (output_phi P w) fuel (h, total)
      Hgo Hstop Hinitial) as Hloop.
    unfold Phi, makeq in Hloop. cbn [fst snd] in Hloop. exact Hloop.
  Qed.

  (** Constructing binary fuel traverses each forest position once. *)
  Local Lemma heap_fuel_clock h : (T_heap_fuel h <= N.of_nat (length h + 1))%N.
  Proof.
    induction h as [|slot hs IH]; time_unfold @T_heap_fuel; cbn [length].
    - lia.
    - rewrite ?Nat2N.inj_succ, ?Nat2N.inj_add in *. lia.
  Qed.

  Lemma T5_pop_bounded : forall P w q,
    (wf q -> bounded w q -> (pending q <= P)%nat ->
    T_pop q + output_phi P w (pop q) <=
      k_driver * N.of_nat (unit_pq P w) + phi P w q)%N.
  Proof.
    intros P w [h m n total] Hwf Hbounded Hcap.
    pose proof (heap_pop_loop_credit P w h m n total (N.pos (heap_fuel h))
      Hwf Hbounded Hcap) as Hloop.
    cbn [N.size_nat] in Hloop.
    rewrite heap_fuel_size in Hloop.
    pose proof (heap_fuel_clock h) as Hfuel.
    pose proof (F2_ranks P (Queue h m n total) Hwf Hcap) as Hranks.
    change (length h <= Nat.log2 P + 1) in Hranks.
    assert (Hrankbudget : length h <= unit_pq P w) by (unfold unit_pq; nia).
    assert (Hunit : (1 <= N.of_nat (unit_pq P w))%N).
    { assert (1 <= unit_pq P w) by (unfold unit_pq; nia). lia. }
    time_unfold @T_pop. cbn [pending live live_count pending_count].
    unfold pop. cbn [pending live live_count pending_count].
    time_simpl.
    change (1 + (1 + 1 + (1 + T_heap_fuel h + (1 + 1)) +
      T_loopN (HeapCode.heap_pop_step m n) (fun s => HeapCode.T_heap_pop_step m n s)
        (N.pos (heap_fuel h)) (h, total)) +
      output_phi P w
        (match loopN (HeapCode.heap_pop_step m n) (N.pos (heap_fuel h)) (h, total) with
        | inl _ => None | inr result => result end)
      <= k_driver * N.of_nat (unit_pq P w) + phi P w (Queue h m n total))%N.
    destruct (loopN (HeapCode.heap_pop_step m n) (N.pos (heap_fuel h)) (h, total))
      as [s|r]; cbn [output_phi] in *.
    all: unfold k_driver, k_step, c_loopN in Hloop |- *;
      rewrite ?Nat2N.inj_add, ?Nat2N.inj_succ in Hloop, Hfuel;
      lia.
  Qed.
  Local Lemma heap_enqueue_clock p x (q : t) count :
    (T_enqueue p x q count <= T_insert p x (forest q) +
      PTrieT.c_trie * N.of_nat (Pos.size_nat x + 1) +
      N.of_nat (N.size_nat (pending_count q)) + 8)%N.
  Proof.
    destruct q as [h m n total].
    pose proof (PTrieT.T_set_le N x p m) as Hset.
    pose proof (N.T_succ_le total) as Hsucc.
    time_unfold @T_enqueue. time_unfold @T_insert.
    cbn [forest heap_pending Base.Heap.pending live pending_count] in *.
    time_simpl; time_cbn_all. lia.
  Qed.

  Local Lemma heap_push_clock P w p x q :
    (wf q -> bounded w q -> (pending q < P)%nat ->
    (N.size_nat p + Pos.size_nat x <= w)%nat ->
    T_push p x q <= (k_insert + k_step) * N.of_nat (unit_pq P w))%N.
  Proof.
    intros Hwf Hfits Hcap Hwidth. destruct q as [h m n total].
    change (N.to_nat total < P) in Hcap.
    pose proof (size_pending (Queue h m n total) Hwf) as Hlivecap.
    change (N.to_nat n <= N.to_nat total) in Hlivecap.
    pose proof (heap_counter_width n P ltac:(lia)) as Hnw.
    pose proof (heap_counter_width total P ltac:(lia)) as Htw.
    assert (Hkey : Pos.size_nat x + 1 <= unit_pq P w) by (unfold unit_pq; nia).
    assert (Hprio : N.size_nat p <= unit_pq P w) by (unfold unit_pq; nia).
    assert (Hlive : N.size_nat n <= unit_pq P w) by (unfold unit_pq; nia).
    assert (Htotal : N.size_nat total <= unit_pq P w) by (unfold unit_pq; nia).
    assert (Hunit : 1 <= unit_pq P w) by (unfold unit_pq; nia).
    apply time_of_nat_le in Hkey, Hprio, Hlive, Htotal, Hunit.
    pose proof (T1_insert P w p x (Queue h m n total) Hwf Hfits Hcap Hwidth) as Hinsert.
    assert (Henqueue : forall count,
      (T_enqueue p x (Queue h m n total) count <=
        (k_insert + 2048) * N.of_nat (unit_pq P w))%N).
    { intro count. pose proof (heap_enqueue_clock p x (Queue h m n total) count) as Hclock.
      cbn [pending_count] in Hclock. unfold PTrieT.c_trie in Hclock.
      unfold k_insert in Hinsert |- *. lia. }
    pose proof (PTrieT.T_get_le N x m) as Hget.
    pose proof (N.T_succ_le n) as Hsucc.
    unfold PTrieT.c_trie in Hget.
    time_unfold @T_push. cbn [live live_count].
    destruct (PTrieCode.get x m) as [old |] eqn:Hlookup.
    - pose proof (Henqueue n) as Henqueue_now.
      pose proof (N.T_compare_le p old) as Hcompare.
      time_unfold N.T_ltb. destruct (N.ltb p old);
        time_simpl; time_cbn_all; unfold k_insert, k_step in *; lia.
    - pose proof (Henqueue (N.succ n)) as Henqueue_now.
      time_simpl; time_cbn_all; unfold k_insert, k_step in *; lia.
  Qed.

  (** Pushing fits the logarithmic comparison budget at bounded key and priority widths. *)
  Lemma push_bigO : bigO (X := nat * nat * N * positive * t)
    (fun '(P, w, p, x, q) => wf q /\ fits w q /\ (pending q < P)%nat /\
      (Pos.size_nat x + N.size_nat p <= w)%nat)
    (fun '(P, w, _, _, _) => N.of_nat (unit_pq P w))
    (fun '(_, _, p, x, q) => T_push p x q).
  Proof.
    exists (k_insert + k_step)%N.
    intros [[[[P w] p] x] q] [Hwf [Hfits [Hpending Hwidth]]].
    cbn [fst snd].
    pose proof (heap_push_clock P w p x q Hwf Hfits Hpending ltac:(lia)) as Hpush.
    nia.
  Qed.

  Lemma T6_push_bounded : forall P w p x q,
    (wf q -> bounded w q -> (pending q < P)%nat ->
    (N.size_nat p + Pos.size_nat x <= w)%nat ->
    T_push p x q + phi P w (push p x q) <=
      (k_insert + k_step + k_credit) * N.of_nat (unit_pq P w) + phi P w q)%N.
  Proof.
    intros P w p x q Hwf Hfits Hcap Hwidth.
    pose proof (heap_push_clock P w p x q Hwf Hfits Hcap Hwidth) as Hclock.
    pose proof (F3_stale_push p x q Hwf) as Hstale.
    apply time_of_nat_le in Hstale. rewrite Nat2N.inj_succ in Hstale.
    assert (Hphi : (phi P w (push p x q) <= phi P w q + credit P w)%N).
    { unfold phi, stale_phi. eapply N.le_trans.
      - apply N.mul_le_mono_r. exact Hstale.
      - rewrite N.mul_succ_l. lia. }
    unfold credit in Hphi. unfold k_insert, k_step, k_credit in *. lia.
  Qed.

  Lemma T_push_amort : forall P w p x q,
    (wf q -> fits w q -> (pending q < P)%nat ->
    (Pos.size_nat x + N.size_nat p <= w)%nat ->
    T_push p x q + phi P w (push p x q) <=
      c_pq * N.of_nat (unit_pq P w) + phi P w q)%N.
  Proof.
    intros P w p x q Hwf Hfits Hcap Hwidth.
    assert (Hwidth' : N.size_nat p + Pos.size_nat x <= w) by lia.
    pose proof (T6_push_bounded P w p x q Hwf Hfits Hcap Hwidth') as Hpush.
    unfold c_pq, k_insert, k_step, k_credit in *. lia.
  Qed.
  Local Lemma pop_amort_output P w (work potential : N)
      (result : option (N * positive * t)) :
    (work + output_phi P w result <=
      k_driver * N.of_nat (unit_pq P w) + potential ->
    work + match result with Some (_, _, q1) => phi P w q1 | None => 0 end <=
      c_pq * N.of_nat (unit_pq P w) + potential)%N.
  Proof.
    intro Hbound. unfold output_phi in Hbound.
    eapply N.le_trans; [exact Hbound|].
    apply N.add_le_mono_r. apply N.mul_le_mono_r.
    unfold c_pq, k_driver. lia.
  Qed.

  Lemma T_pop_amort : forall P w q,
    (wf q -> fits w q -> (pending q <= P)%nat ->
    T_pop q + match pop q with Some (_, _, q1) => phi P w q1 | None => 0 end
      <= c_pq * N.of_nat (unit_pq P w) + phi P w q)%N.
  Proof.
    intros P w q Hwf Hfits Hpending.
    exact (pop_amort_output P w (T_pop q) (phi P w q) (pop q)
      (T5_pop_bounded P w q Hwf Hfits Hpending)).
  Qed.

  (** Popping pays one comparison budget and the credit of discarded stale entries. *)
  Lemma pop_bigO : bigO (X := nat * nat * t)
    (fun '(P, w, q) => wf q /\ fits w q /\ (pending q <= P)%nat)
    (fun '(P, w, q) =>
      N.of_nat (unit_pq P w * (pending q - N.to_nat (size q) + 1)))
    (fun '(_, _, q) => T_pop q).
  Proof.
    exists (c_pq + k_credit)%N.
    intros [[P w] q] [Hwf [Hfits Hpending]]. cbn [fst snd].
    pose proof (T_pop_amort P w q Hwf Hfits Hpending) as Hpop.
    rewrite (F6_phi_bounded P w q Hwf Hfits) in Hpop.
    unfold stale_phi, stale, credit in Hpop.
    rewrite Nat2N.inj_mul, Nat2N.inj_add.
    nia.
  Qed.
End HeapT.
