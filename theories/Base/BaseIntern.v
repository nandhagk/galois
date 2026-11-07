(** * Dense bidirectional interning

    A forward map and an inverse map assign consecutive positive IDs to keys.
    For example, interning [a; b; a] allocates only IDs one and two.
    Builds on: BaseMap, BaseEncoding and BaseEq. *)

From Stdlib Require Import List Bool NArith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap.
Import List.ListNotations Cost.Notations.

Module Intern.

(** An interner stores two computational maps and the next unused positive ID. *)
Record t (K : Type) := Table {
  table : Map.t K positive;
  inverse : Map.t positive K;
  next : positive
}.
Arguments Table {K} table inverse next.
Arguments table {K} _.
Arguments inverse {K} _.
Arguments next {K} _.

(** Empty construction initializes both maps and starts allocating at one. *)
Definition empty_c {K} : Cost.t (t K) := Cost.ret (Table Map.empty Map.empty 1%positive).

(** An empty interner has no allocated IDs. *)
Definition empty {K} : t K := Cost.value empty_c.

(** Forward lookup retains the encoding callback and map costs. *)
Definition find_c {K} (E : encoding K) k (s : t K) := Map.get_c E k (table s).

(** Forward lookup returns an existing key's dense positive ID. *)
Definition find {K} (E : encoding K) k (s : t K) := Cost.value (find_c E k s).

(** Reverse lookup uses the landed positive scalar encoding. *)
Definition key_of_c {K} i (s : t K) := Map.get_c positive_encoding i (inverse s).

(** Reverse lookup returns the key stored at an allocated ID. *)
Definition key_of {K} i (s : t K) := Cost.value (key_of_c i s).

(** The reference size counts forward bindings through the costed map interface. *)
Definition size_c {K} (s : t K) := Map.size_c (table s).

(** Size counts allocated keys. *)
Definition size {K} (s : t K) := Cost.value (size_c s).

(** Tables are well formed, inverse, bounded by the frontier and dense below it. *)
Definition wf {K} (E : encoding K) (s : t K) : Prop :=
  Map.wf E (table s) /\
  Map.wf positive_encoding (inverse s) /\
  (forall k i, find E k s = Some i -> (i < next s)%positive) /\
  (forall k i, find E k s = Some i <-> key_of i s = Some k) /\
  (forall i, (i < next s)%positive -> exists k, find E k s = Some i).

(** Interning charges forward lookup and both map insertions on a miss. *)
Definition intern_c {K} (E : encoding K) k (s : t K) :=
  let* old := find_c E k s in
  match old with
  | Some i => Cost.ret (i, s)
  | None =>
    let* forward := Map.set_c E k (next s) (table s) in
    let* backward := Map.set_c positive_encoding (next s) k (inverse s) in
    Cost.ret (next s, Table forward backward (Pos.succ (next s)))
  end.

(** Interning returns the existing or newly allocated ID and the resulting table. *)
Definition intern {K} (E : encoding K) k (s : t K) := Cost.value (intern_c E k s).

(** Interning reuses an old ID or allocates exactly the current frontier. *)
Theorem intern_equation {K} (E : encoding K) k (s : t K) :
  intern E k s =
  match find E k s with
  | Some i => (i, s)
  | None => (next s, Table (Map.set E k (next s) (table s))
      (Map.set positive_encoding (next s) k (inverse s)) (Pos.succ (next s)))
  end.
Proof.
  unfold intern, intern_c. autorewrite with galois_cost.
  fold (find E k s). destruct (find E k s); reflexivity.
Qed.

(** Empty interning starts with no IDs. *)
Theorem wf_empty {K} (E : encoding K) : wf E (@empty K).
Proof.
  split; [apply Map.wf_empty|]. split; [apply Map.wf_empty|].
  split; [intros k i H; discriminate H|].
  split; [intros k i; split; discriminate|].
  intros i Hi. change (i < 1)%positive in Hi. lia.
Qed.

(** A found key returns its old ID and the unchanged table. *)
Theorem intern_found {K} (E : encoding K) k i (s : t K) :
  find E k s = Some i -> intern E k s = (i, s).
Proof.
  intro H. rewrite intern_equation, H. reflexivity.
Qed.

(** A new key receives the old frontier and advances it by one. *)
Theorem intern_new {K} (E : encoding K) k (s : t K) :
  find E k s = None ->
  fst (intern E k s) = next s /\ next (snd (intern E k s)) = Pos.succ (next s).
Proof.
  intro H. rewrite intern_equation, H. split; reflexivity.
Qed.

(** The returned ID is readable at the interned key. *)
Theorem find_intern {K} (E : encoding K) k (s : t K) :
  wf E s -> find E k (snd (intern E k s)) = Some (fst (intern E k s)).
Proof.
  intros [Hm _]. rewrite intern_equation. destruct (find E k s) eqn:H.
  - exact H.
  - change (Map.get E k (Map.set E k (next s) (table s)) = Some (next s)).
    now apply Map.get_set_same.
Qed.

(** Interning retains every previously allocated key's ID. *)
Theorem find_intern_old {K} (E : encoding K) (HE : encoding_laws E) a k i (s : t K) :
  wf E s -> find E a s = Some i -> find E a (snd (intern E k s)) = Some i.
Proof.
  intros [Hm Hrest] Ha. rewrite intern_equation. destruct (find E k s) eqn:Hk.
  - exact Ha.
  - change (Map.get E a (Map.set E k (next s) (table s)) = Some i).
    rewrite (Map.get_set_other E HE) by
      (try assumption; intro Heq; subst a; congruence).
    exact Ha.
Qed.

(** Forward lookup has the advertised inverse in every well-formed table. *)
Theorem key_of_find {K} (E : encoding K) k i (s : t K) :
  wf E s -> find E k s = Some i -> key_of i s = Some k.
Proof.
  intros [_ [_ [_ [Hlink _]]]]. apply Hlink.
Qed.

Local Lemma fresh_inverse {K} (E : encoding K) (s : t K) :
  wf E s -> key_of (next s) s = None.
Proof.
  intros [_ [_ [Hbound [Hlink _]]]]. destruct (key_of (next s) s) as [k|] eqn:Hget.
  - apply Hlink in Hget. specialize (Hbound _ _ Hget). lia.
  - reflexivity.
Qed.

Local Lemma fresh_bound {K} (E : encoding K) k (s : t K) :
  wf E s ->
  forall a i,
  Map.get E a (Map.set E k (next s) (table s)) = Some i ->
  (i < Pos.succ (next s))%positive.
Proof.
  intros [Hm [_ [Hbound _]]] a i Hget.
  rewrite Map.get_set in Hget by exact Hm.
  destruct (eqb E a k); [injection Hget as <-; lia|].
  specialize (Hbound _ _ Hget). lia.
Qed.

Local Lemma fresh_link {K} (E : encoding K) (HE : encoding_laws E) k (s : t K) :
  wf E s -> find E k s = None ->
  forall a i,
  Map.get E a (Map.set E k (next s) (table s)) = Some i <->
  Map.get positive_encoding i (Map.set positive_encoding (next s) k (inverse s)) = Some a.
Proof.
  intros [Hm [Hinv [Hbound [Hlink Hdense]]]] Hmissing a i.
  pose proof positive_encoding_laws as HP.
  destruct (eqb_dec E HE a k) as [Heq|Hne];
    destruct (Pos.eq_dec i (next s)) as [Hi|Hi].
  - subst a i. rewrite !Map.get_set_same by assumption. split; reflexivity.
  - subst a. rewrite Map.get_set_same by exact Hm.
    rewrite Map.get_set_other by assumption.
    split.
    + intro H. injection H as H. congruence.
    + intro H. apply Hlink in H. change (find E k s = Some i) in H.
      congruence.
  - subst i. rewrite Map.get_set_other by assumption.
    rewrite Map.get_set_same by exact Hinv. split.
    + intro H. specialize (Hbound _ _ H). lia.
    + intro H. injection H as H. congruence.
  - rewrite !Map.get_set_other by assumption. apply Hlink.
Qed.

(** Interning maintains the forward/inverse bijection and dense frontier invariant. *)
Theorem intern_wf {K} (E : encoding K) (HE : encoding_laws E) k (s : t K) :
  wf E s -> wf E (snd (intern E k s)).
Proof.
  intro Hwf. pose proof Hwf as [Hm [Hinv [Hbound [Hlink Hdense]]]].
  rewrite intern_equation. destruct (find E k s) as [i|] eqn:Hmissing; [exact Hwf|].
  cbn [snd]. split; [now apply Map.wf_set|].
  split; [now apply Map.wf_set|]. split.
  - apply fresh_bound. exact Hwf.
  - split; [apply fresh_link; assumption|]. intros i Hi.
    cbn [next] in Hi. destruct (Pos.eq_dec i (next s)) as [Heq|Hne].
    + subst i. exists k. apply Map.get_set_same. exact Hm.
    + assert (Hlt : (i < next s)%positive) by lia.
      destruct (Hdense i Hlt) as [a Ha]. exists a.
      change (Map.get E a (Map.set E k (next s) (table s)) = Some i).
      rewrite (Map.get_set_other E HE) by
        (try assumption; intro Heq; subst a; congruence).
      exact Ha.
Qed.

(** The inverse lookup recovers the key at the returned ID. *)
Theorem key_of_intern {K} (E : encoding K) (HE : encoding_laws E) k (s : t K) :
  wf E s -> key_of (fst (intern E k s)) (snd (intern E k s)) = Some k.
Proof.
  intro Hwf. eapply key_of_find.
  - now apply intern_wf.
  - now apply find_intern.
Qed.

(** Every positive ID below the frontier belongs to an interned key. *)
Theorem ids_dense {K} (E : encoding K) i (s : t K) :
  wf E s -> ((i < next s)%positive <-> exists k, find E k s = Some i).
Proof.
  intros [_ [_ [Hbound [_ Hdense]]]]. split; [apply Hdense|].
  intros [k H]. exact (Hbound k i H).
Qed.

(** List interning charges every input cell and threads allocation in input order. *)
Fixpoint intern_list_c {K} (E : encoding K) (xs : list K) (s : t K) : Cost.t (t K) :=
  match xs with
  | [] => Cost.ret s
  | k :: rest =>
    Cost.step ;;
    let* result := intern_c E k s in intern_list_c E rest (snd result)
  end.

(** List construction starts interning with the empty table. *)
Definition of_list_c {K} (E : encoding K) xs := intern_list_c E xs (@empty K).

(** List construction allocates IDs by first occurrence. *)
Definition of_list {K} (E : encoding K) xs := Cost.value (of_list_c E xs).

Local Lemma list_step {K} (E : encoding K) k rest (s : t K) :
  Cost.value (intern_list_c E (k :: rest) s) =
    Cost.value (intern_list_c E rest (snd (intern E k s))).
Proof.
  reflexivity.
Qed.

Local Lemma wf_list {K} (E : encoding K) (HE : encoding_laws E) xs (s : t K) :
  wf E s -> wf E (Cost.value (intern_list_c E xs s)).
Proof.
  revert s. induction xs as [|k rest IH]; intros s Hwf; [exact Hwf|].
  rewrite list_step. apply IH. now apply intern_wf.
Qed.

(** Interning a list builds a well-formed dense table. *)
Theorem wf_of_list {K} (E : encoding K) (HE : encoding_laws E) xs :
  wf E (of_list E xs).
Proof.
  apply wf_list; [exact HE|apply wf_empty].
Qed.

(** The keys after interning are exactly the old keys and the supplied key. *)
Theorem intern_members {K} (E : encoding K) (HE : encoding_laws E) a k (s : t K) :
  wf E s ->
  ((exists i, find E a (snd (intern E k s)) = Some i) <->
    a = k \/ exists i, find E a s = Some i).
Proof.
  intros [Hm Hrest]. rewrite intern_equation.
  destruct (find E k s) as [j|] eqn:Hk; cbn [snd].
  - split.
    + intro H. now right.
    + intros [->|H]; [now exists j|exact H].
  - change ((exists i, Map.get E a (Map.set E k (next s) (table s)) = Some i) <->
      a = k \/ exists i, find E a s = Some i).
    rewrite Map.get_set by exact Hm.
    destruct (eqb_spec E HE a k) as [Heq|Hne].
    + split; [intro H; now left|intros _; exists (next s); reflexivity].
    + split.
      * intro H. now right.
      * intros [H|H]; [contradiction|exact H].
Qed.

Local Lemma list_members {K} (E : encoding K) (HE : encoding_laws E) xs a (s : t K) :
  wf E s ->
  ((exists i, find E a (Cost.value (intern_list_c E xs s)) = Some i) <->
    In a xs \/ exists i, find E a s = Some i).
Proof.
  revert s. induction xs as [|k rest IH]; intros s Hwf.
  - cbn [intern_list_c]. rewrite Cost.value_ret. cbn [In]. tauto.
  - rewrite list_step, IH by now apply intern_wf.
    rewrite (intern_members E HE) by exact Hwf. cbn [In]. intuition congruence.
Qed.

(** The constructed table contains exactly the keys occurring in its input. *)
Theorem intern_list_spec {K} (E : encoding K) (HE : encoding_laws E) xs k :
  In k xs <-> exists i, find E k (of_list E xs) = Some i.
Proof.
  unfold of_list, of_list_c. rewrite (list_members E HE) by apply wf_empty.
  assert (Hempty : ~ exists i, find E k (@empty K) = Some i).
  { intros [i H]. discriminate H. }
  tauto.
Qed.

Arguments empty_c {K} : simpl never.
Arguments empty {K} : simpl never.
Arguments find_c {K} E k s : simpl never.
Arguments find {K} E k s : simpl never.
Arguments key_of_c {K} i s : simpl never.
Arguments key_of {K} i s : simpl never.
Arguments size_c {K} s : simpl never.
Arguments size {K} s : simpl never.
Arguments intern_c {K} E k s : simpl never.
Arguments intern {K} E k s : simpl never.
Arguments of_list_c {K} E xs : simpl never.
Arguments of_list {K} E xs : simpl never.
Arguments intern_list_c {K} E xs s : simpl never.
Arguments table : simpl never.
Arguments inverse : simpl never.
Arguments next : simpl never.

End Intern.
