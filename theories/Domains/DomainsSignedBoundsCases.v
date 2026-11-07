(** * Charged hemisphere alternatives

    Transfers evaluate every sign-half combination and join the resulting exact component hulls.
    For example, a three-operand selection has at most eight combinations at a valid Bits arity.
    Builds on: DomainsKnownBits, DomainsSignedBoundsForward and DomainsSignedOrder. *)

From Stdlib Require Import ZArith List Bool Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Lattice Require Import LatticeCore.
From Galois.Bits Require Import BitsWord BitsOp.
From Galois.Domains Require Import DomainsNumeric DomainsTnum DomainsKnownBitsForward
  DomainsKnownBits DomainsSignedBounds DomainsSignedOrder DomainsSignedBoundsRange
  DomainsSignedBoundsForward.
Import List.ListNotations Cost.Notations.

Local Open Scope Z_scope.

Definition sb_plain_gamma (w : width) (h : sb_half) (z : Z) : Prop :=
  match h with
  | SBEmpty => False
  | SBRange t lo hi => is_word w z /\ tnum_gamma w t z /\ lo <= z <= hi
  end.

Lemma sb_half_plain : forall w s h z,
  sb_half_gamma w s h z -> sb_plain_gamma w h z.
Proof.
  intros w s [|t lo hi] z Hz;
    unfold sb_half_gamma, sb_bit_gamma, sb_interval_gamma, sb_plain_gamma, sb_range_gamma in *;
    cbn [fst snd] in *; tauto.
Qed.

Definition sb_half_bits (w : width) (h : sb_half) : tnum :=
  match h with
  | SBEmpty => bot (tnum_lattice w)
  | SBRange t _ _ => t
  end.

Definition sb_half_bounds (h : sb_half) : sb_range :=
  match h with
  | SBEmpty => (1, 0)
  | SBRange _ lo hi => (lo, hi)
  end.

Definition sb_is_empty (h : sb_half) : bool :=
  match h with
  | SBEmpty => true
  | SBRange _ _ _ => false
  end.

Fixpoint sb_choices_c (xs : list (width * signed_bounds))
    : Cost.t (list (list (width * sb_half))) :=
  match xs with
  | [] => Cost.ret [[]]
  | (w, a) :: rest =>
    Cost.step ;;
    let* tails := sb_choices_c rest in
    let* a' := signed_bounds_reduce_c w a in
    let* zeros := map_c (fun hs => Cost.step ;; Cost.ret ((w, sb_zero a') :: hs)) tails in
    let* ones := map_c (fun hs => Cost.step ;; Cost.ret ((w, sb_one a') :: hs)) tails in
    app_c zeros ones
  end.

Definition sb_choices (xs : list (width * signed_bounds)) : list (list (width * sb_half)) :=
  Cost.value (sb_choices_c xs).

(** Alternative construction retains every input reduction, map, append and recursive visit. *)
Theorem sb_choices_equation : forall xs,
  sb_choices xs =
  match xs with
  | [] => [[]]
  | (w, a) :: rest =>
    let tails := sb_choices rest in
    let a' := signed_bounds_reduce w a in
    map (cons (w, sb_zero a')) tails ++ map (cons (w, sb_one a')) tails
  end.
Proof.
  intros [|[w a] rest]; unfold sb_choices; cbn [sb_choices_c];
    autorewrite with galois_cost; [reflexivity|].
  reflexivity.
Qed.

(** Some constructed alternative contains every concrete operand tuple. *)
Theorem sb_choices_sound : forall xs cs,
  Forall2 (payload_sound signed_bounds_gamma) xs cs ->
  exists hs, In hs (sb_choices xs) /\ Forall2 (payload_sound sb_plain_gamma) hs cs.
Proof.
  intros xs cs Hpayload.
  induction Hpayload as [|[w a] [v z] rest values Hhead Htail IH].
  - exists []. rewrite sb_choices_equation. split; [now left|constructor].
  - destruct IH as [hs [Hin Hhs]]. destruct Hhead as [Hwidth [Hw Ha]].
    cbn [fst snd] in Hwidth, Hw, Ha. subst v.
    apply (proj2 (signed_bounds_reduce_gamma w a z)) in Ha.
    destruct Ha as [Ha|Ha].
    + exists ((w, sb_zero (signed_bounds_reduce w a)) :: hs). split.
      * rewrite sb_choices_equation. apply in_or_app. left. apply in_map. exact Hin.
      * constructor; [split; [reflexivity|split; [exact Hw|now apply sb_half_plain in Ha]]|
          exact Hhs].
    + exists ((w, sb_one (signed_bounds_reduce w a)) :: hs). split.
      * rewrite sb_choices_equation. apply in_or_app. right. apply in_map. exact Hin.
      * constructor; [split; [reflexivity|split; [exact Hw|now apply sb_half_plain in Ha]]|
          exact Hhs].
Qed.

(** Alternatives preserve the original widths and operand order. *)
Theorem sb_choices_widths : forall xs hs,
  In hs (sb_choices xs) -> map fst hs = map fst xs.
Proof.
  intro xs. induction xs as [|[w a] rest IH]; intros hs Hin;
    rewrite sb_choices_equation in Hin.
  - destruct Hin as [<-|Hnone]; [reflexivity|contradiction].
  - apply in_app_iff in Hin as [Hin|Hin];
      apply in_map_iff in Hin as [tail [<- Hin]]; cbn [map fst]; f_equal; now apply IH.
Qed.

Lemma sb_components_payloads : forall hs cs,
  Forall2 (payload_sound sb_plain_gamma) hs cs ->
  Forall2 (payload_sound tnum_gamma)
    (map (fun wh => (fst wh, sb_half_bits (fst wh) (snd wh))) hs) cs /\
  Forall2 (payload_sound sb_range_pgamma)
    (map (fun wh => (fst wh, sb_half_bounds (snd wh))) hs) cs.
Proof.
  intros hs cs Hpayload.
  induction Hpayload as [|[w h] [v z] rest values Hhead Htail IH].
  - split; constructor.
  - destruct Hhead as [Hwidth [Hw Hh]]. cbn [fst snd] in Hwidth, Hw, Hh. subst v.
    destruct h as [|t lo hi]; [contradiction|]. destruct Hh as [_ [Ht Hb]].
    destruct IH as [IHt IHr]. split.
    + constructor; [split; [reflexivity|split; assumption]|exact IHt].
    + constructor; [split; [reflexivity|split; assumption]|exact IHr].
Qed.

Lemma sb_plain_payload_nonempty : forall hs cs,
  Forall2 (payload_sound sb_plain_gamma) hs cs ->
  existsb (fun wh => sb_is_empty (snd wh)) hs = false.
Proof.
  intros hs cs Hpayload.
  induction Hpayload as [|[w h] y rest values Hhead Htail IH]; [reflexivity|].
  destruct Hhead as [_ [_ Hh]]. destruct h; [contradiction|]. cbn. exact IH.
Qed.

Definition sb_case_forward_c (opts : known_bits_options) (o : op)
    (hs : list (width * sb_half)) (rw : width) : Cost.t signed_bounds :=
  let* empty := existsb_c (fun wh => Cost.step ;; Cost.ret (sb_is_empty (snd wh))) hs in
  if empty then Cost.ret (SignedBounds SBEmpty SBEmpty) else
  let* bits := map_c (fun wh => Cost.step ;;
    Cost.ret (fst wh, sb_half_bits (fst wh) (snd wh))) hs in
  let* ranges := map_c (fun wh => Cost.step ;;
    Cost.ret (fst wh, sb_half_bounds (snd wh))) hs in
  let* t := Cost.step ;; pforward_c (known_bits_word_domain opts) o bits rw in
  let* rs := sb_range_forward_c o ranges rw in
  sb_from_ranges_c rw t rs.

Definition sb_case_forward (opts : known_bits_options) (o : op)
    (hs : list (width * sb_half)) (rw : width) : signed_bounds :=
  Cost.value (sb_case_forward_c opts o hs rw).

(** Pure case evaluation exposes empty handling and the two complete component transfers. *)
Theorem sb_case_forward_equation : forall opts o hs rw,
  sb_case_forward opts o hs rw =
  if existsb (fun wh => sb_is_empty (snd wh)) hs then SignedBounds SBEmpty SBEmpty else
  sb_from_ranges rw
    (pforward (known_bits_word_domain opts) o
      (map (fun wh => (fst wh, sb_half_bits (fst wh) (snd wh))) hs) rw)
    (sb_range_forward o (map (fun wh => (fst wh, sb_half_bounds (snd wh))) hs) rw).
Proof.
  intros opts o hs rw. unfold sb_case_forward, sb_case_forward_c.
  rewrite Cost.value_bind, value_existsb_c.
  change (existsb (fun wh => Cost.value (Cost.step ;; Cost.ret (sb_is_empty (snd wh)))) hs)
    with (existsb (fun wh => sb_is_empty (snd wh)) hs).
  destruct (existsb (fun wh => sb_is_empty (snd wh)) hs);
    autorewrite with galois_cost; reflexivity.
Qed.

(** One hemisphere case preserves its concrete word result through both component transfers. *)
Theorem sb_case_forward_sound : forall opts o hs cs rw z,
  Forall2 (payload_sound sb_plain_gamma) hs cs -> eval_op o cs = Some (rw, z) ->
  signed_bounds_gamma rw (sb_case_forward opts o hs rw) z.
Proof.
  intros opts o hs cs rw z Hpayload Heval.
  destruct (sb_components_payloads hs cs Hpayload) as [Hbits Hranges].
  pose proof (sb_plain_payload_nonempty hs cs Hpayload) as Hempty.
  rewrite sb_case_forward_equation, Hempty.
  apply sb_from_ranges_sound.
  - exact (pforward_sound (known_bits_word_laws opts) o _ cs rw z Hbits Heval).
  - exact (sb_range_forward_sound o _ cs rw z Hranges Heval).
Qed.

Definition sb_join_all_c (w : width) (xs : list signed_bounds) : Cost.t signed_bounds :=
  fold_right_c (fun a b => Cost.step ;; signed_bounds_join_c w a b)
    (SignedBounds SBEmpty SBEmpty) xs.

Definition sb_join_all (w : width) (xs : list signed_bounds) : signed_bounds :=
  Cost.value (sb_join_all_c w xs).

(** Aggregation retains the legacy right-fold order and charges every full join callback. *)
Theorem sb_join_all_equation : forall w xs,
  sb_join_all w xs = fold_right (signed_bounds_join w) (SignedBounds SBEmpty SBEmpty) xs.
Proof.
  intros w xs. unfold sb_join_all, sb_join_all_c. rewrite value_fold_right_c. reflexivity.
Qed.

Lemma sb_join_all_sound : forall w xs a z,
  In a xs -> signed_bounds_gamma w a z -> signed_bounds_gamma w (sb_join_all w xs) z.
Proof.
  intros w xs. induction xs as [|a rest IH]; intros q z Hin Hz; [contradiction|].
  rewrite sb_join_all_equation. cbn [fold_right]. apply signed_bounds_join_sound.
  destruct Hin as [<-|Hin]; [now left|].
  right. rewrite <- sb_join_all_equation. now apply (IH q z).
Qed.

Definition signed_bounds_forward_c (opts : known_bits_options) (o : op)
    (xs : list (width * signed_bounds)) (rw : width) : Cost.t signed_bounds :=
  let* alternatives := sb_choices_c xs in
  let* results := map_c (fun hs => Cost.step ;; sb_case_forward_c opts o hs rw) alternatives in
  sb_join_all_c rw results.

Definition signed_bounds_forward (opts : known_bits_options) (o : op)
    (xs : list (width * signed_bounds)) (rw : width) : signed_bounds :=
  Cost.value (signed_bounds_forward_c opts o xs rw).

(** Multiplier selection changes no other hemisphere callback or traversal charge. *)
Theorem signed_bounds_forward_nonmultiplication : forall opts opts' o, o <> bvmul ->
  signed_bounds_forward_c opts o = signed_bounds_forward_c opts' o.
Proof.
  intros opts opts' o Hother. unfold signed_bounds_forward_c, sb_case_forward_c.
  now rewrite (known_bits_nonmultiplication_agrees opts opts' o Hother).
Qed.

(** The shared harness supplies arity dispatch, so this interface has no operand cap. *)
Theorem signed_bounds_forward_sound : forall opts o xs cs rw z,
  Forall2 (payload_sound signed_bounds_gamma) xs cs -> eval_op o cs = Some (rw, z) ->
  signed_bounds_gamma rw (signed_bounds_forward opts o xs rw) z.
Proof.
  intros opts o xs cs rw z Hpayload Heval.
  destruct (sb_choices_sound xs cs Hpayload) as [hs [Hin Hhs]].
  unfold signed_bounds_forward, signed_bounds_forward_c. autorewrite with galois_cost.
  apply (sb_join_all_sound rw _ (sb_case_forward opts o hs rw) z).
  - apply in_map_iff. exists hs. split; [reflexivity|exact Hin].
  - exact (sb_case_forward_sound opts o hs cs rw z Hhs Heval).
Qed.
