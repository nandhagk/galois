(** * Unprioritized pending rows

    A list stores pending rows and a finite set prevents duplicate insertion.
    For example, inserting the same row twice leaves one pending occurrence.
    Builds on: BaseSet and CostList. *)

From Stdlib Require Import List Bool Arith NArith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseEq BaseSet.
Import List.ListNotations Cost.Notations.

Module TotalQueue.

(** The membership cache has a separate invariant relating it to the pending list. *)
Record t (C : Type) := Make {
  pending : list C;
  queued : FinSet.t C
}.

Arguments Make {C}.
Arguments pending {C}.
Arguments queued {C}.

Definition empty {C} : t C := Make [] FinSet.empty.

(** A valid queue has no duplicate row and its set recognizes precisely the pending rows. *)
Definition wf {C} (EC : encoding C) (q : t C) : Prop :=
  FinSet.wf EC (queued q) /\ NoDup (pending q) /\
    forall c, FinSet.mem EC c (queued q) = true <-> In c (pending q).

Definition push_c {C} (EC : encoding C) c (q : t C) :=
  let* present := FinSet.mem_c EC c (queued q) in
  if present then Cost.ret q
  else
    let* keys := FinSet.add_c EC c (queued q) in
    Cost.ret (Make (c :: pending q) keys).

Definition push {C} (EC : encoding C) c q := Cost.value (@push_c C EC c q).

Definition push_many_c {C} (EC : encoding C) cs q :=
  fold_left_c (fun q c => push_c EC c q) cs q.
Definition push_many {C} (EC : encoding C) cs q := Cost.value (@push_many_c C EC cs q).

(** A pop removes the same row from both representations. *)
Definition pop_c {C} (EC : encoding C) (q : t C) : Cost.t (option (C * t C)) :=
  match pending q with
  | [] => Cost.ret None
  | c :: rest =>
    let* keys := FinSet.remove_c EC c (queued q) in
    Cost.ret (Some (c, Make rest keys))
  end.

Definition pop {C} (EC : encoding C) q := Cost.value (@pop_c C EC q).

(** Insertion exposes the cached membership decision. *)
Theorem push_equation {C} EC c (q : t C) :
  push EC c q =
    if FinSet.mem EC c (queued q) then q
    else Make (c :: pending q) (FinSet.add EC c (queued q)).
Proof.
  unfold push, push_c; autorewrite with galois_cost.
  fold (FinSet.mem EC c (queued q)).
  destruct (FinSet.mem EC c (queued q)); autorewrite with galois_cost; reflexivity.
Qed.

(** Empty queues have a valid empty membership cache. *)
Theorem empty_wf {C} (EC : encoding C) : wf EC (@empty C).
Proof.
  split; [apply FinSet.wf_empty|]; split; [constructor|].
  intro c; cbn [empty pending queued]; rewrite FinSet.mem_empty.
  split; [discriminate|contradiction].
Qed.

(** Inserting a row keeps the list and cached set synchronized. *)
Theorem push_wf {C} EC (HE : encoding_laws EC) c (q : t C) :
  wf EC q -> wf EC (push EC c q).
Proof.
  intros [Hwf [Hnodup Hmem]]; rewrite push_equation.
  destruct (FinSet.mem EC c (queued q)) eqn:Hpresent.
  - split; [exact Hwf|]; split; assumption.
  - split; [apply FinSet.wf_add, Hwf|]; cbn [pending queued]; split.
    + constructor; [intro Hin; apply Hmem in Hin; congruence|exact Hnodup].
    + intro d; rewrite FinSet.mem_add by exact Hwf.
      rewrite orb_true_iff, Hmem, (eqb_true_iff EC HE); cbn; intuition congruence.
Qed.

(** Queue insertion adds precisely the supplied row to membership. *)
Theorem push_member {C} EC (HE : encoding_laws EC) c (q : t C) d :
  wf EC q -> (In d (pending (push EC c q)) <-> d = c \/ In d (pending q)).
Proof.
  intros [Hwf [Hnodup Hmem]]; rewrite push_equation.
  destruct (FinSet.mem EC c (queued q)) eqn:Hpresent; cbn [pending In].
  - apply Hmem in Hpresent; intuition congruence.
  - intuition congruence.
Qed.

(** Each attempted insertion increases the list length by at most one. *)
Theorem push_length {C} EC c (q : t C) :
  (length (pending (push EC c q)) <= S (length (pending q)))%nat.
Proof.
  rewrite push_equation; destruct (FinSet.mem EC c (queued q)); cbn [pending length]; lia.
Qed.

(** Multiple insertions are the ordinary left fold of single-row insertions. *)
Theorem push_many_equation {C} EC cs (q : t C) :
  push_many EC cs q = fold_left (fun q c => push EC c q) cs q.
Proof.
  unfold push_many, push_many_c; rewrite value_fold_left_c; reflexivity.
Qed.

(** Multiple insertions keep queue well-formedness. *)
Theorem push_many_wf {C} EC (HE : encoding_laws EC) cs (q : t C) :
  wf EC q -> wf EC (push_many EC cs q).
Proof.
  rewrite push_many_equation; revert q.
  induction cs as [|c cs IH]; intros q Hwf; cbn [fold_left]; [exact Hwf|].
  apply IH, push_wf; assumption.
Qed.

(** A batch retains old rows and adds exactly its input members. *)
Theorem push_many_member {C} EC (HE : encoding_laws EC) cs (q : t C) d :
  wf EC q ->
  (In d (pending (push_many EC cs q)) <-> In d cs \/ In d (pending q)).
Proof.
  rewrite push_many_equation; revert q; induction cs as [|c cs IH]; intros q Hwf.
  - cbn [fold_left In]; tauto.
  - cbn [fold_left]; rewrite IH by (apply push_wf; assumption).
    rewrite push_member by assumption; cbn; intuition congruence.
Qed.

(** A batch's list growth is bounded by its input occurrence count. *)
Theorem push_many_length {C} EC cs (q : t C) :
  (length (pending (push_many EC cs q)) <= length cs + length (pending q))%nat.
Proof.
  rewrite push_many_equation; revert q; induction cs as [|c cs IH]; intro q.
  - reflexivity.
  - cbn [fold_left length]; specialize (IH (push EC c q)).
    pose proof (push_length EC c q); lia.
Qed.

(** Pop exposes the list head and the charged cached-set removal. *)
Theorem pop_equation {C} EC (q : t C) :
  pop EC q =
    match pending q with
    | [] => None
    | c :: rest => Some (c, Make rest (FinSet.remove EC c (queued q)))
    end.
Proof.
  unfold pop, pop_c; destruct (pending q); autorewrite with galois_cost; reflexivity.
Qed.

(** A successful pop keeps well-formedness and removes one pending occurrence. *)
Theorem pop_spec {C} EC (HE : encoding_laws EC) (q r : t C) c :
  wf EC q -> pop EC q = Some (c, r) ->
  wf EC r /\ pending q = c :: pending r.
Proof.
  intros [Hwf [Hnodup Hmem]] Hpop; rewrite pop_equation in Hpop.
  destruct (pending q) as [|d rest] eqn:Hlist; [discriminate|].
  injection Hpop as <- <-; cbn [pending queued]; split; [|reflexivity].
  split; [apply FinSet.wf_remove, Hwf|].
  inversion Hnodup as [|? ? Hfresh Hrest]; subst.
  split; [exact Hrest|]; intro x; cbn [queued pending].
  rewrite FinSet.mem_remove by exact Hwf.
  destruct (eqb EC x d) eqn:Hsame.
  - apply (eqb_true_iff EC HE) in Hsame; subst x; intuition discriminate.
  - apply (eqb_false_iff EC HE) in Hsame; cbn [negb andb].
    rewrite Hmem; cbn; intuition congruence.
Qed.

(** Single insertion retains membership and, on a miss, the set-write charge. *)
Theorem push_cost {C} EC c (q : t C) :
  Cost.ticks (push_c EC c q) =
    (Cost.ticks (FinSet.mem_c EC c (queued q)) +
      if FinSet.mem EC c (queued q) then 0
      else Cost.ticks (FinSet.add_c EC c (queued q)))%N.
Proof.
  unfold push_c; rewrite Cost.ticks_bind.
  fold (FinSet.mem EC c (queued q)).
  destruct (FinSet.mem EC c (queued q)); autorewrite with galois_cost; lia.
Qed.

(** Pop charges the removed row's full encoded-key operation. *)
Theorem pop_cost {C} EC (q : t C) :
  Cost.ticks (pop_c EC q) =
    match pending q with
    | [] => 0%N
    | c :: _ => Cost.ticks (FinSet.remove_c EC c (queued q))
    end.
Proof.
  unfold pop_c; destruct (pending q); autorewrite with galois_cost; lia.
Qed.

Arguments push_c {C} EC c q : simpl never.
Arguments push {C} EC c q : simpl never.
Arguments push_many_c {C} EC cs q : simpl never.
Arguments push_many {C} EC cs q : simpl never.
Arguments pop_c {C} EC q : simpl never.
Arguments pop {C} EC q : simpl never.

End TotalQueue.
Import TotalQueue.
