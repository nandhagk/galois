(** * Charged signed-bound backward alternatives

    Each backward case intersects component results with its original operand half.
    For example, an infeasible result half contributes empty facts to every operand column.
    Builds on: DomainsSignedBoundsCases, Back and the shared word interfaces. *)

From Stdlib Require Import ZArith List Bool Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Lattice Require Import LatticeCore.
From Galois.Bits Require Import BitsWord BitsOp.
From Galois.Domains Require Import DomainsNumeric DomainsTnum DomainsTnumMul
  DomainsKnownBitsForward DomainsKnownBits DomainsSignedBounds DomainsSignedOrder
  DomainsSignedBoundsRange DomainsSignedBoundsBack DomainsSignedBoundsCases.
Import List.ListNotations Cost.Notations.

Local Open Scope Z_scope.

Definition sb_lift_half_c (w : width) (h : sb_half) : Cost.t signed_bounds :=
  match h with
  | SBEmpty => Cost.ret (SignedBounds SBEmpty SBEmpty)
  | SBRange t lo hi => sb_lift_c w t lo hi
  end.

Definition sb_lift_half (w : width) (h : sb_half) : signed_bounds :=
  Cost.value (sb_lift_half_c w h).

Lemma sb_lift_half_gamma : forall w h z,
  signed_bounds_gamma w (sb_lift_half w h) z <-> sb_plain_gamma w h z.
Proof.
  intros w [|t lo hi] z; [unfold signed_bounds_gamma, sb_half_gamma; cbn; tauto|].
  apply sb_lift_gamma.
Qed.

Fixpoint sb_candidates_c (hs : list (width * sb_half)) (ts : list tnum)
    (ranges : list (list sb_range)) : Cost.t (list signed_bounds) :=
  match hs, ts, ranges with
  | [], _, _ => Cost.ret []
  | (w, h) :: rest, t :: tail, rs :: more =>
    Cost.step ;;
    let* original := sb_lift_half_c w h in
    let* candidate := sb_from_ranges_c w t rs in
    let* refined := signed_bounds_meet_c w original candidate in
    Cost.map (cons refined) (sb_candidates_c rest tail more)
  | (w, h) :: rest, _, _ =>
    Cost.step ;;
    let* original := sb_lift_half_c w h in
    Cost.map (cons original) (sb_candidates_c rest [] [])
  end.

Definition sb_candidates (hs : list (width * sb_half)) (ts : list tnum)
    (ranges : list (list sb_range)) : list signed_bounds :=
  Cost.value (sb_candidates_c hs ts ranges).

(** Candidate construction retains every original lift, range reduction and meet. *)
Theorem sb_candidates_equation : forall hs ts ranges,
  sb_candidates hs ts ranges =
  match hs, ts, ranges with
  | [], _, _ => []
  | (w, h) :: rest, t :: tail, rs :: more =>
    signed_bounds_meet w (sb_lift_half w h) (sb_from_ranges w t rs) ::
      sb_candidates rest tail more
  | (w, h) :: rest, _, _ => sb_lift_half w h :: sb_candidates rest [] []
  end.
Proof.
  intros [|[w h] rest] [|t tail] [|rs more]; unfold sb_candidates;
    cbn [sb_candidates_c]; autorewrite with galois_cost; reflexivity.
Qed.

Lemma sb_candidates_sound : forall hs cs ts ranges,
  Forall2 (payload_sound sb_plain_gamma) hs cs ->
  Forall2 (fun p c => tnum_gamma (fst p) (snd p) (snd c))
    (combine (map fst hs) ts) cs ->
  Forall2 (fun p c => sb_ranges_gamma (fst p) (snd p) (snd c))
    (combine (map fst hs) ranges) cs ->
  Forall2 (fun p c => signed_bounds_gamma (fst p) (snd p) (snd c))
    (combine (map fst hs) (sb_candidates hs ts ranges)) cs.
Proof.
  intros hs cs ts ranges Hpayload. revert ts ranges.
  induction Hpayload as [|[w h] [v z] rest values Hhead Htail IH];
    intros [|t ts] [|rs more] Hbits Hranges; cbn [map combine fst snd] in *;
    try solve [inversion Hbits]; try solve [inversion Hranges]; try solve [constructor].
  destruct Hhead as [Hwidth [Hw Hh]]. cbn [fst snd] in Hwidth, Hw, Hh. subst v.
  inversion Hbits as [|p c tail cs Ht Hts]; subst.
  inversion Hranges as [|p c tail cs Hrs Hmore]; subst.
  rewrite sb_candidates_equation. cbn [combine map fst snd]. constructor.
  - apply signed_bounds_meet_gamma. split.
    + now apply sb_lift_half_gamma.
    + now apply sb_from_ranges_sound.
  - now apply IH.
Qed.

Lemma sb_ranges_back_columns : forall hs cs ranges,
  Forall2 (payload_sound sb_plain_gamma) hs cs ->
  Forall2 (fun wp_c rs => sb_ranges_gamma (fst (fst wp_c)) rs (snd (snd wp_c)))
    (combine (map (fun wh => (fst wh, sb_half_bounds (snd wh))) hs) cs) ranges ->
  Forall2 (fun p c => sb_ranges_gamma (fst p) (snd p) (snd c))
    (combine (map fst hs) ranges) cs.
Proof.
  intros hs cs ranges Hpayload. revert ranges.
  induction Hpayload as [|[w h] [v z] hs cs Hhead Htail IH]; intros ranges Hranges.
  - inversion Hranges; subst. constructor.
  - inversion Hranges as [|p rs rest more Hr Hmore]; subst.
    cbn [map combine fst snd] in *. constructor; [exact Hr|now apply IH].
Qed.

Definition sb_case_assume_c (o : op) (hs : list (width * sb_half)) (rw : width) (q : sb_half)
    : Cost.t (list signed_bounds) :=
  let* empty := existsb_c (fun wh => Cost.step ;; Cost.ret (sb_is_empty (snd wh))) hs in
  if sb_is_empty q || empty then
    map_c (fun _ => Cost.step ;; Cost.ret (SignedBounds SBEmpty SBEmpty)) hs
  else
    let* bits := map_c (fun wh => Cost.step ;;
      Cost.ret (fst wh, sb_half_bits (fst wh) (snd wh))) hs in
    let* ranges := map_c (fun wh => Cost.step ;;
      Cost.ret (fst wh, sb_half_bounds (snd wh))) hs in
    let* ts := Cost.step ;; passume_c known_bits_classic_domain o bits rw (sb_half_bits rw q) in
    let* rs := sb_ranges_backward_c o ranges rw (sb_half_bounds q) in
    sb_candidates_c hs ts rs.

Definition sb_case_assume (o : op) (hs : list (width * sb_half)) (rw : width) (q : sb_half)
    : list signed_bounds := Cost.value (sb_case_assume_c o hs rw q).

(** Pure backward cases expose the legacy bit dictionary and direct local range constraints. *)
Theorem sb_case_assume_equation : forall o hs rw q,
  sb_case_assume o hs rw q =
  if sb_is_empty q || existsb (fun wh => sb_is_empty (snd wh)) hs then
    map (fun _ => SignedBounds SBEmpty SBEmpty) hs
  else sb_candidates hs
    (passume known_bits_classic_domain o
      (map (fun wh => (fst wh, sb_half_bits (fst wh) (snd wh))) hs) rw (sb_half_bits rw q))
    (sb_ranges_backward o (map (fun wh => (fst wh, sb_half_bounds (snd wh))) hs)
      rw (sb_half_bounds q)).
Proof.
  intros o hs rw q. unfold sb_case_assume, sb_case_assume_c.
  rewrite Cost.value_bind, value_existsb_c.
  change (existsb (fun wh => Cost.value (Cost.step ;; Cost.ret (sb_is_empty (snd wh)))) hs)
    with (existsb (fun wh => sb_is_empty (snd wh)) hs).
  destruct (existsb (fun wh => sb_is_empty (snd wh)) hs), (sb_is_empty q);
    cbn [orb]; autorewrite with galois_cost; reflexivity.
Qed.

(** A feasible backward half case preserves every original concrete operand. *)
Theorem sb_case_assume_sound : forall o hs cs rw z q,
  Forall2 (payload_sound sb_plain_gamma) hs cs -> eval_op o cs = Some (rw, z) ->
  sb_plain_gamma rw q z ->
  Forall2 (fun p c => signed_bounds_gamma (fst p) (snd p) (snd c))
    (combine (map fst hs) (sb_case_assume o hs rw q)) cs.
Proof.
  intros o hs cs rw z q Hpayload Heval Hq.
  destruct (sb_components_payloads hs cs Hpayload) as [Hbits Hranges].
  pose proof (sb_plain_payload_nonempty hs cs Hpayload) as Hempty.
  assert (Hqempty : sb_is_empty q = false) by (destruct q; [contradiction|reflexivity]).
  assert (Hqbits : tnum_gamma rw (sb_half_bits rw q) z)
    by (destruct q; [contradiction|exact (proj1 (proj2 Hq))]).
  assert (Hqrange : sb_range_gamma (sb_half_bounds q) z)
    by (destruct q; [contradiction|exact (proj2 (proj2 Hq))]).
  pose proof (passume_sound (known_bits_word_laws (KnownBitsOptions MulLow)) o _ cs rw z
    (sb_half_bits rw q) Hbits Heval Hqbits) as Hbackbits.
  rewrite map_map in Hbackbits. cbn [fst] in Hbackbits.
  pose proof (sb_ranges_backward_sound o _ cs rw (sb_half_bounds q) z
    Hranges Hqrange Heval) as Hbackranges.
  pose proof (sb_ranges_back_columns hs cs _ Hpayload Hbackranges) as Hcolumns.
  rewrite sb_case_assume_equation, Hempty, Hqempty. cbn [orb].
  now apply sb_candidates_sound.
Qed.

Fixpoint sb_columns_c (ws : list width) (alternatives : list (list signed_bounds))
    : Cost.t (list signed_bounds) :=
  match ws with
  | [] => Cost.ret []
  | w :: rest =>
    Cost.step ;;
    let* heads := map_c (fun qs => Cost.step ;;
      Cost.ret (hd (SignedBounds SBEmpty SBEmpty) qs)) alternatives in
    let* q := sb_join_all_c w heads in
    let* tails := map_c (fun qs => Cost.step ;; Cost.ret (tl qs)) alternatives in
    Cost.map (cons q) (sb_columns_c rest tails)
  end.

Definition sb_columns (ws : list width) (alternatives : list (list signed_bounds))
    : list signed_bounds := Cost.value (sb_columns_c ws alternatives).

(** Column aggregation charges every alternative visit, tail extraction and full join. *)
Theorem sb_columns_equation : forall ws alternatives,
  sb_columns ws alternatives =
  match ws with
  | [] => []
  | w :: rest =>
    sb_join_all w (map (hd (SignedBounds SBEmpty SBEmpty)) alternatives) ::
      sb_columns rest (map (@tl signed_bounds) alternatives)
  end.
Proof.
  intros [|w rest] alternatives; unfold sb_columns; cbn [sb_columns_c];
    autorewrite with galois_cost; [reflexivity|].
  reflexivity.
Qed.

Lemma sb_columns_sound : forall ws alternatives qs (cs : list word),
  In qs alternatives ->
  Forall2 (fun p c => signed_bounds_gamma (fst p) (snd p) (snd c)) (combine ws qs) cs ->
  length ws = length cs ->
  Forall2 (fun p c => signed_bounds_gamma (fst p) (snd p) (snd c))
    (combine ws (sb_columns ws alternatives)) cs.
Proof.
  intro ws. induction ws as [|w rest IH]; intros alternatives [|q qs] [|[v z] values]
    Hin Hsound Hlength; cbn [combine length] in Hsound, Hlength;
    try discriminate; try solve [inversion Hsound]; try solve [constructor].
  inversion Hsound as [|p c tail cs Hq Hqs]; subst.
  rewrite sb_columns_equation. cbn [combine]. constructor.
  - apply (sb_join_all_sound w _ q z); [|exact Hq].
    apply in_map_iff. exists (q :: qs). now split.
  - apply (IH _ qs); [|exact Hqs|lia].
    apply in_map_iff. exists (q :: qs). now split.
Qed.

Fixpoint sb_refine_original_c (xs : list (width * signed_bounds)) (qs : list signed_bounds)
    : Cost.t (list signed_bounds) :=
  match xs, qs with
  | [], _ => Cost.ret []
  | (w, a) :: rest, q :: tail =>
    Cost.step ;;
    let* refined := signed_bounds_meet_c w a q in
    Cost.map (cons refined) (sb_refine_original_c rest tail)
  | (w, a) :: rest, [] =>
    Cost.step ;;
    let* original := signed_bounds_reduce_c w a in
    Cost.map (cons original) (sb_refine_original_c rest [])
  end.

Definition sb_refine_original (xs : list (width * signed_bounds)) (qs : list signed_bounds)
    : list signed_bounds := Cost.value (sb_refine_original_c xs qs).

(** Final refinement retains every meet and the normalization fallback on a short result list. *)
Theorem sb_refine_original_equation : forall xs qs,
  sb_refine_original xs qs =
  match xs, qs with
  | [], _ => []
  | (w, a) :: rest, q :: tail => signed_bounds_meet w a q :: sb_refine_original rest tail
  | (w, a) :: rest, [] => signed_bounds_reduce w a :: sb_refine_original rest []
  end.
Proof.
  intros [|[w a] rest] [|q tail]; unfold sb_refine_original;
    cbn [sb_refine_original_c]; autorewrite with galois_cost; reflexivity.
Qed.

Lemma sb_refine_original_refines : forall xs qs,
  Forall2 (fun wp q => signed_bounds_leb (fst wp) q (snd wp) = true)
    xs (sb_refine_original xs qs).
Proof.
  intro xs. induction xs as [|[w a] rest IH]; intros [|q qs];
    rewrite sb_refine_original_equation; constructor; try apply IH.
  - apply signed_bounds_leb_spec. intros z Hz. now rewrite signed_bounds_reduce_gamma in Hz.
  - apply signed_bounds_leb_spec. intros z Hz. apply signed_bounds_meet_gamma in Hz. tauto.
Qed.

Lemma sb_refine_original_length : forall xs qs, length (sb_refine_original xs qs) = length xs.
Proof.
  intro xs. induction xs as [|[w a] rest IH]; intros [|q qs];
    rewrite sb_refine_original_equation; cbn [length]; try reflexivity; f_equal; apply IH.
Qed.

Lemma sb_refine_original_sound : forall xs cs qs,
  Forall2 (payload_sound signed_bounds_gamma) xs cs ->
  Forall2 (fun p c => signed_bounds_gamma (fst p) (snd p) (snd c))
    (combine (map fst xs) qs) cs ->
  Forall2 (fun p c => signed_bounds_gamma (fst p) (snd p) (snd c))
    (combine (map fst xs) (sb_refine_original xs qs)) cs.
Proof.
  intros xs cs qs Hpayload. revert qs.
  induction Hpayload as [|[w a] [v z] rest values Hhead Htail IH];
    intros [|q qs] Hqs; cbn [map combine] in Hqs;
    try solve [inversion Hqs]; try solve [constructor].
  inversion Hqs as [|p c tail cs Hq Hrest]; subst.
  rewrite sb_refine_original_equation. cbn [map combine]. constructor.
  - apply signed_bounds_meet_gamma. split; [exact (proj2 (proj2 Hhead))|exact Hq].
  - now apply IH.
Qed.

Definition sb_valid_shape_c (o : op) (xs : list (width * signed_bounds)) (rw : width)
    : Cost.t bool :=
  let* ws := map_c (fun wp => Cost.step ;; Cost.ret (fst wp)) xs in
  Cost.ret
    (match result_width o ws with
    | Some w => Pos.eqb w rw
    | None => false
    end).

Definition sb_valid_shape (o : op) (xs : list (width * signed_bounds)) (rw : width) : bool :=
  Cost.value (sb_valid_shape_c o xs rw).

Lemma sb_valid_shape_equation : forall o xs rw,
  sb_valid_shape o xs rw =
  match result_width o (map fst xs) with
  | Some w => Pos.eqb w rw
  | None => false
  end.
Proof.
  intros o xs rw. unfold sb_valid_shape, sb_valid_shape_c.
  autorewrite with galois_cost. reflexivity.
Qed.

Lemma sb_payload_widths : forall (xs : list (width * signed_bounds)) cs,
  Forall2 (payload_sound signed_bounds_gamma) xs cs -> map fst xs = map fst cs.
Proof.
  intros xs cs Hpayload.
  induction Hpayload as [|x c xs cs Hx Htail IH]; cbn [map]; [reflexivity|].
  f_equal; [exact (proj1 Hx)|exact IH].
Qed.

Lemma sb_valid_shape_sound : forall o xs cs rw z,
  Forall2 (payload_sound signed_bounds_gamma) xs cs ->
  eval_op o cs = Some (rw, z) -> sb_valid_shape o xs rw = true.
Proof.
  intros o xs cs rw z Hpayload Heval. rewrite sb_valid_shape_equation.
  rewrite (sb_payload_widths xs cs Hpayload).
  pose proof (eval_op_width o cs (rw, z) Heval) as Hwidth.
  cbn [fst] in Hwidth. rewrite Hwidth. apply Pos.eqb_refl.
Qed.

Definition sb_assume_alternatives_c (o : op) (rw : width) (q : signed_bounds)
    (choices : list (list (width * sb_half))) : Cost.t (list (list signed_bounds)) :=
  fold_right_c
    (fun hs rest =>
      Cost.step ;;
      let* zero := sb_case_assume_c o hs rw (sb_zero q) in
      let* one := sb_case_assume_c o hs rw (sb_one q) in
      app_c [zero; one] rest)
    [] choices.

Definition sb_assume_alternatives (o : op) (rw : width) (q : signed_bounds)
    (choices : list (list (width * sb_half))) : list (list signed_bounds) :=
  Cost.value (sb_assume_alternatives_c o rw q choices).

Lemma sb_assume_alternatives_equation : forall o rw q choices,
  sb_assume_alternatives o rw q choices =
  flat_map (fun hs => [sb_case_assume o hs rw (sb_zero q);
    sb_case_assume o hs rw (sb_one q)]) choices.
Proof.
  intros o rw q choices. unfold sb_assume_alternatives, sb_assume_alternatives_c.
  rewrite value_fold_right_c.
  induction choices as [|hs rest IH]; cbn [fold_right flat_map].
  - reflexivity.
  - rewrite !Cost.value_bind, value_app_c, IH. reflexivity.
Qed.

Definition signed_bounds_assume_c (o : op) (xs : list (width * signed_bounds))
    (rw : width) (q : signed_bounds) : Cost.t (list signed_bounds) :=
  let* valid := sb_valid_shape_c o xs rw in
  if valid then
    let* q' := signed_bounds_reduce_c rw q in
    let* choices := sb_choices_c xs in
    let* alternatives := sb_assume_alternatives_c o rw q' choices in
    let* ws := map_c (fun wp => Cost.step ;; Cost.ret (fst wp)) xs in
    let* columns := sb_columns_c ws alternatives in
    sb_refine_original_c xs columns
  else map_c (fun wp => Cost.step ;; signed_bounds_reduce_c (fst wp) (snd wp)) xs.

Definition signed_bounds_assume (o : op) (xs : list (width * signed_bounds))
    (rw : width) (q : signed_bounds) : list signed_bounds :=
  Cost.value (signed_bounds_assume_c o xs rw q).

(** Backward transfer refines arbitrary raw inputs, including malformed widths and arities. *)
Theorem signed_bounds_assume_refines : forall o xs rw q,
  Forall2 (fun wp q' => signed_bounds_leb (fst wp) q' (snd wp) = true)
    xs (signed_bounds_assume o xs rw q).
Proof.
  intros o xs rw q. unfold signed_bounds_assume, signed_bounds_assume_c.
  autorewrite with galois_cost. destruct (Cost.value (sb_valid_shape_c o xs rw)).
  - autorewrite with galois_cost. apply sb_refine_original_refines.
  - rewrite value_map_c. induction xs as [|[w a] rest IH]; cbn [map]; constructor;
      [|exact IH].
    apply signed_bounds_leb_spec. intros z Hz.
    change (signed_bounds_gamma w (signed_bounds_reduce w a) z) in Hz.
    now rewrite signed_bounds_reduce_gamma in Hz.
Qed.

(** Backward transfer keeps the operand count without a concrete-witness premise. *)
Theorem signed_bounds_assume_length : forall o xs rw q,
  length (signed_bounds_assume o xs rw q) = length xs.
Proof.
  intros o xs rw q. unfold signed_bounds_assume, signed_bounds_assume_c.
  autorewrite with galois_cost. destruct (Cost.value (sb_valid_shape_c o xs rw)).
  - autorewrite with galois_cost. apply sb_refine_original_length.
  - rewrite value_map_c, length_map. reflexivity.
Qed.

(** Full backward transfer preserves every operand of a result satisfying the query. *)
Theorem signed_bounds_assume_sound : forall o xs cs rw z q,
  Forall2 (payload_sound signed_bounds_gamma) xs cs -> eval_op o cs = Some (rw, z) ->
  signed_bounds_gamma rw q z ->
  Forall2 (fun p c => signed_bounds_gamma (fst p) (snd p) (snd c))
    (combine (map fst xs) (signed_bounds_assume o xs rw q)) cs.
Proof.
  intros o xs cs rw z q Hpayload Heval Hq.
  pose proof (sb_valid_shape_sound o xs cs rw z Hpayload Heval) as Hshape.
  unfold signed_bounds_assume, signed_bounds_assume_c. autorewrite with galois_cost.
  change (Cost.value (sb_valid_shape_c o xs rw)) with (sb_valid_shape o xs rw).
  rewrite Hshape. autorewrite with galois_cost.
  destruct (sb_choices_sound xs cs Hpayload) as [hs [Hin Hhs]].
  pose proof (sb_choices_widths xs hs Hin) as Hwidths.
  apply sb_refine_original_sound; [exact Hpayload|].
  apply (proj2 (signed_bounds_reduce_gamma rw q z)) in Hq.
  destruct Hq as [Hq|Hq].
  - apply (sb_columns_sound _ _ (sb_case_assume o hs rw (sb_zero (signed_bounds_reduce rw q)))).
    + change (In (sb_case_assume o hs rw (sb_zero (signed_bounds_reduce rw q)))
        (sb_assume_alternatives o rw (signed_bounds_reduce rw q) (sb_choices xs))).
      rewrite sb_assume_alternatives_equation. apply in_flat_map.
      exists hs. split; [exact Hin|now left].
    + rewrite <- Hwidths. apply (sb_case_assume_sound o hs cs rw z); try assumption.
      now apply sb_half_plain in Hq.
    + rewrite length_map. now apply Forall2_length in Hpayload.
  - apply (sb_columns_sound _ _ (sb_case_assume o hs rw (sb_one (signed_bounds_reduce rw q)))).
    + change (In (sb_case_assume o hs rw (sb_one (signed_bounds_reduce rw q)))
        (sb_assume_alternatives o rw (signed_bounds_reduce rw q) (sb_choices xs))).
      rewrite sb_assume_alternatives_equation. apply in_flat_map.
      exists hs. split; [exact Hin|right; now left].
    + rewrite <- Hwidths. apply (sb_case_assume_sound o hs cs rw z); try assumption.
      now apply sb_half_plain in Hq.
    + rewrite length_map. now apply Forall2_length in Hpayload.
Qed.
