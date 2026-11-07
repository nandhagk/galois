(** * Pole-aware circular backward refinements

    Result and operand cuts cover every satisfying backward case before meeting each operand.
    For example, assuming an unsigned comparison can remove an impossible sign-pole piece.
    Builds on: DomainsWrappedTransfer and interval backward entries. *)

From Stdlib Require Import ZArith List Bool Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Lattice Require Import LatticeCore.
From Galois.Bits Require Import BitsWord BitsFun BitsArith BitsOp BitsTactics.
From Galois.Domains Require Import DomainsBound DomainsThreshold DomainsInterval
  DomainsIntervalBack DomainsIntervalRefine DomainsNumeric DomainsWrapped DomainsWrappedParts
  DomainsWrappedArith DomainsWrappedTransfer.
Import List.ListNotations Cost.Notations.

Local Open Scope Z_scope.

Definition wrapped_pair_join wa wb (a b : wrapped * wrapped) : wrapped * wrapped :=
  (wrapped_join wa (fst a) (fst b), wrapped_join wb (snd a) (snd b)).

(** Each refined payload is interpreted at the corresponding operand width. *)
Definition wrapped_pair_gamma wa wb (a : wrapped * wrapped) (x y : Z) : Prop :=
  wrapped_gamma wa (fst a) x /\ wrapped_gamma wb (snd a) y.

Definition wrapped_pair_union_c wa wb (a b : Cost.t (wrapped * wrapped)) :=
  let* a := a in
  let* b := b in
  let* joined_left := Cost.step ;; join_c (wrapped_lattice wa) (fst a) (fst b) in
  Cost.map (pair joined_left) (Cost.step ;; join_c (wrapped_lattice wb) (snd a) (snd b)).

(** Pair union retains both computations and joins the payloads at their own widths. *)
Theorem wrapped_pair_union_value wa wb a b :
  Cost.value (wrapped_pair_union_c wa wb a b) =
  wrapped_pair_join wa wb (Cost.value a) (Cost.value b).
Proof.
  reflexivity.
Qed.

(** Pair union retains both input costs and charges both width-specific joins and their calls. *)
Theorem wrapped_pair_union_cost wa wb a b :
  Cost.ticks (wrapped_pair_union_c wa wb a b) = (Cost.ticks a + Cost.ticks b + 4)%N.
Proof.
  unfold wrapped_pair_union_c, wrapped_lattice. autorewrite with galois_cost.
  rewrite !ticks_join_of_pure. lia.
Qed.

(** Pair join retains every represented operand pair in either case. *)
Theorem wrapped_pair_join_sound wa wb a b x y :
  wrapped_pair_gamma wa wb a x y \/ wrapped_pair_gamma wa wb b x y ->
  wrapped_pair_gamma wa wb (wrapped_pair_join wa wb a b) x y.
Proof.
  intros [[Hax Hay]|[Hbx Hby]]; split; apply wrapped_join_sound;
    first [now left|now right].
Qed.

Definition wrapped_assume_consistent_c o wa wb a b q : Cost.t bool :=
  match result_width o [wa; wb] with
  | Some rw =>
    Cost.step ;;
    let* result := interval_forward_c ThresholdEmpty o [(wa, a); (wb, b)] rw in
    Cost.step ;;
    Cost.ret (match interval_meet result q with IBot => false | _ => true end)
  | None => Cost.step ;; Cost.ret false
  end.

Definition wrapped_assume_consistent o wa wb a b q :=
  Cost.value (wrapped_assume_consistent_c o wa wb a b q).

(** Consistency accepts every represented operand pair satisfying the result fact. *)
Theorem wrapped_assume_consistent_sound o wa wb a b q x y rw z :
  interval_pgamma wa a x -> interval_pgamma wb b y -> interval_pgamma rw q z ->
  eval_op o [(wa, x); (wb, y)] = Some (rw, z) ->
  wrapped_assume_consistent o wa wb a b q = true.
Proof.
  intros Ha Hb Hq Heval.
  assert (Hpayload : Forall2 (payload_sound interval_pgamma)
      [(wa, a); (wb, b)] [(wa, x); (wb, y)]).
  { constructor.
    - split; [reflexivity|]. split; [exact (proj1 Ha)|exact Ha].
    - constructor; [|constructor].
      split; [reflexivity|]. split; [exact (proj1 Hb)|exact Hb]. }
  pose proof (interval_forward_sound ThresholdEmpty o _ _ rw z Hpayload Heval) as Hforward.
  pose proof (interval_meet_sound rw _ _ z Hforward Hq) as Hmeet.
  pose proof (eval_op_width _ _ _ Heval) as Hwidth.
  change (result_width o [wa; wb] = Some rw) in Hwidth.
  unfold wrapped_assume_consistent, wrapped_assume_consistent_c. rewrite Hwidth.
  autorewrite with galois_cost.
  change (match interval_meet (interval_forward ThresholdEmpty o [(wa, a); (wb, b)] rw) q with
    | IBot => false | _ => true end = true).
  destruct (interval_meet (interval_forward ThresholdEmpty o [(wa, a); (wb, b)] rw) q).
  - exact (False_rect _ (proj2 Hmeet)).
  - reflexivity.
Qed.

Definition wrapped_assume_piece_raw_c o wa wb a b q : Cost.t (wrapped * wrapped) :=
  match a, b, q with
  | IBot, _, _ | _, IBot, _ | _, _, IBot => Cost.step ;; Cost.ret (WBot, WBot)
  | _, _, _ =>
    let* consistent := Cost.step ;; wrapped_assume_consistent_c o wa wb a b q in
    if consistent then
      Cost.step ;;
      let refined := interval_assume_pair o wa a b q in
      Cost.step ;; Cost.ret
        (wrapped_of_interval wa (fst refined), wrapped_of_interval wb (snd refined))
    else Cost.ret (WBot, WBot)
  end.

Local Lemma wrapped_assume_piece_raw_sound o wa wb a b q x y rw z :
  interval_pgamma wa a x -> interval_pgamma wb b y -> interval_pgamma rw q z ->
  eval_op o [(wa, x); (wb, y)] = Some (rw, z) ->
  wrapped_pair_gamma wa wb (Cost.value (wrapped_assume_piece_raw_c o wa wb a b q)) x y.
Proof.
  intros Ha Hb Hq Heval.
  destruct (interval_assume_pair_sound o wa wb a b q x y rw z Ha Hb Hq Heval)
    as [Hleft Hright].
  assert (Ha_nonempty : a <> IBot) by (intro Hempty; subst a; exact (proj2 Ha)).
  assert (Hb_nonempty : b <> IBot) by (intro Hempty; subst b; exact (proj2 Hb)).
  assert (Hq_nonempty : q <> IBot) by (intro Hempty; subst q; exact (proj2 Hq)).
  pose proof (wrapped_assume_consistent_sound o wa wb a b q x y rw z Ha Hb Hq Heval) as Hcheck.
  destruct a as [|la ha]; [contradiction|].
  destruct b as [|lb hb]; [contradiction|].
  destruct q as [|lq hq]; [contradiction|].
  unfold wrapped_assume_piece_raw_c. autorewrite with galois_cost.
  change (Cost.value (wrapped_assume_consistent_c o wa wb (Itv la ha) (Itv lb hb)
    (Itv lq hq))) with
    (wrapped_assume_consistent o wa wb (Itv la ha) (Itv lb hb) (Itv lq hq)).
  rewrite Hcheck. autorewrite with galois_cost.
  split; now apply wrapped_interval_value_sound.
Qed.

Definition wrapped_assume_piece_c o wa wb a b q : Cost.t (wrapped * wrapped) :=
  Cost.step ;;
  let pa := wrapped_pole_cut wa a in
  Cost.step ;;
  let pb := wrapped_pole_cut wb b in
  wrapped_pair_union_c wa wb
    (wrapped_pair_union_c wa wb
      (wrapped_assume_piece_raw_c o wa wb (fst pa) (fst pb) q)
      (wrapped_assume_piece_raw_c o wa wb (fst pa) (snd pb) q))
    (wrapped_pair_union_c wa wb
      (wrapped_assume_piece_raw_c o wa wb (snd pa) (fst pb) q)
      (wrapped_assume_piece_raw_c o wa wb (snd pa) (snd pb) q)).

Local Lemma wrapped_assume_piece_sound o wa wb a b q x y rw z :
  interval_pgamma wa a x -> interval_pgamma wb b y -> interval_pgamma rw q z ->
  eval_op o [(wa, x); (wb, y)] = Some (rw, z) ->
  wrapped_pair_gamma wa wb (Cost.value (wrapped_assume_piece_c o wa wb a b q)) x y.
Proof.
  intros Ha Hb Hq Heval.
  apply wrapped_pole_cut_sound in Ha. apply wrapped_pole_cut_sound in Hb.
  unfold wrapped_assume_piece_c. autorewrite with galois_cost.
  rewrite !wrapped_pair_union_value. apply wrapped_pair_join_sound.
  destruct Ha as [Ha|Ha]; destruct Hb as [Hb|Hb].
  - left. apply wrapped_pair_join_sound. left.
    eapply wrapped_assume_piece_raw_sound; eassumption.
  - left. apply wrapped_pair_join_sound. right.
    eapply wrapped_assume_piece_raw_sound; eassumption.
  - right. apply wrapped_pair_join_sound. left.
    eapply wrapped_assume_piece_raw_sound; eassumption.
  - right. apply wrapped_pair_join_sound. right.
    eapply wrapped_assume_piece_raw_sound; eassumption.
Qed.

Definition wrapped_assume_result_c o wa wb a b rw q : Cost.t (wrapped * wrapped) :=
  Cost.step ;;
  let results := wrapped_parts rw q in
  wrapped_pair_union_c wa wb
    (wrapped_assume_piece_c o wa wb a b (fst results))
    (wrapped_assume_piece_c o wa wb a b (snd results)).

Local Lemma wrapped_assume_result_sound o wa wb a b rw q x y z :
  interval_pgamma wa a x -> interval_pgamma wb b y -> wrapped_gamma rw q z ->
  eval_op o [(wa, x); (wb, y)] = Some (rw, z) ->
  wrapped_pair_gamma wa wb (Cost.value (wrapped_assume_result_c o wa wb a b rw q)) x y.
Proof.
  intros Ha Hb Hq Heval. apply wrapped_parts_spec in Hq.
  unfold wrapped_assume_result_c. autorewrite with galois_cost.
  rewrite wrapped_pair_union_value. apply wrapped_pair_join_sound.
  destruct Hq as [Hq|Hq].
  - left. eapply wrapped_assume_piece_sound; eassumption.
  - right. eapply wrapped_assume_piece_sound; eassumption.
Qed.

Definition wrapped_assume_binary_base_c o wa wb a b rw q : Cost.t (wrapped * wrapped) :=
  Cost.step ;;
  let pa := wrapped_parts wa a in
  Cost.step ;;
  let pb := wrapped_parts wb b in
  let* candidates := wrapped_pair_union_c wa wb
    (wrapped_pair_union_c wa wb
      (wrapped_assume_result_c o wa wb (fst pa) (fst pb) rw q)
      (wrapped_assume_result_c o wa wb (fst pa) (snd pb) rw q))
    (wrapped_pair_union_c wa wb
      (wrapped_assume_result_c o wa wb (snd pa) (fst pb) rw q)
      (wrapped_assume_result_c o wa wb (snd pa) (snd pb) rw q)) in
  Cost.step ;; Cost.ret (wrapped_meet wa a (fst candidates), wrapped_meet wb b (snd candidates)).

(** Joined backward cases retain the concrete pair before meeting both original operands. *)
Theorem wrapped_assume_binary_base_sound o wa wb a b rw q x y z :
  wrapped_gamma wa a x -> wrapped_gamma wb b y -> wrapped_gamma rw q z ->
  eval_op o [(wa, x); (wb, y)] = Some (rw, z) ->
  wrapped_pair_gamma wa wb (Cost.value (wrapped_assume_binary_base_c o wa wb a b rw q)) x y.
Proof.
  intros Ha Hb Hq Heval.
  pose proof (proj1 (wrapped_parts_spec wa a x) Ha) as Hpa.
  pose proof (proj1 (wrapped_parts_spec wb b y) Hb) as Hpb.
  unfold wrapped_assume_binary_base_c. autorewrite with galois_cost.
  rewrite !wrapped_pair_union_value.
  match goal with |- wrapped_pair_gamma _ _
    (wrapped_meet _ _ (fst ?candidates), _) _ _ =>
    assert (Hcandidates : wrapped_pair_gamma wa wb candidates x y)
  end.
  { apply wrapped_pair_join_sound. destruct Hpa as [Hpa|Hpa]; destruct Hpb as [Hpb|Hpb].
    - left. apply wrapped_pair_join_sound. left.
      eapply wrapped_assume_result_sound; eassumption.
    - left. apply wrapped_pair_join_sound. right.
      eapply wrapped_assume_result_sound; eassumption.
    - right. apply wrapped_pair_join_sound. left.
      eapply wrapped_assume_result_sound; eassumption.
    - right. apply wrapped_pair_join_sound. right.
      eapply wrapped_assume_result_sound; eassumption. }
  destruct Hcandidates as [Hleft Hright]. split; now apply wrapped_meet_sound.
Qed.

(** The final meets make every base backward result reductive without semantic premises. *)
Theorem wrapped_assume_binary_base_lower o wa wb a b rw q :
  wrapped_leb wa (fst (Cost.value (wrapped_assume_binary_base_c o wa wb a b rw q))) a = true /\
  wrapped_leb wb (snd (Cost.value (wrapped_assume_binary_base_c o wa wb a b rw q))) b = true.
Proof.
  unfold wrapped_assume_binary_base_c. autorewrite with galois_cost.
  split; apply wrapped_meet_lower_left.
Qed.

Definition wrapped_rewrap (target source : width) (q : wrapped) : wrapped :=
  wrapped_project target source q.

(** Result rewrapping retains each represented value after projection to the operand width. *)
Theorem wrapped_rewrap_sound target source q z :
  wrapped_gamma source q z ->
  wrapped_gamma target (wrapped_rewrap target source q) (wrap target z).
Proof.
  apply wrapped_project_sound.
Qed.

Definition wrapped_assume_trunc (w : width) (a : wrapped) (rw : width) (q : wrapped) : wrapped :=
  let pa := wrapped_parts w a in
  let pq := wrapped_parts rw q in
  wrapped_meet w a (wrapped_join_four w
    (wrapped_of_interval w (interval_assume_rewrap rw (fst pa) (fst pq)))
    (wrapped_of_interval w (interval_assume_rewrap rw (fst pa) (snd pq)))
    (wrapped_of_interval w (interval_assume_rewrap rw (snd pa) (fst pq)))
    (wrapped_of_interval w (interval_assume_rewrap rw (snd pa) (snd pq)))).

(** Truncation refinement retains every operand whose truncated value satisfies the result arc. *)
Theorem wrapped_assume_trunc_sound w a rw q x :
  wrapped_gamma w a x -> wrapped_gamma rw q (wrap rw x) ->
  wrapped_gamma w (wrapped_assume_trunc w a rw q) x.
Proof.
  intros Ha Hq. unfold wrapped_assume_trunc. apply wrapped_meet_sound; [exact Ha|].
  apply wrapped_parts_spec in Ha. apply wrapped_parts_spec in Hq.
  apply wrapped_join_four_sound.
  destruct Ha as [Ha|Ha]; destruct Hq as [Hq|Hq].
  - left. apply wrapped_interval_value_sound. now apply (interval_assume_rewrap_sound rw).
  - right; left. apply wrapped_interval_value_sound.
    now apply (interval_assume_rewrap_sound rw).
  - right; right; left. apply wrapped_interval_value_sound.
    now apply (interval_assume_rewrap_sound rw).
  - right; right; right. apply wrapped_interval_value_sound.
    now apply (interval_assume_rewrap_sound rw).
Qed.

Local Lemma wrapped_add_cancel w x y : wrap w (wrap w (x + y) - y) = wrap w x.
Proof.
  rewrite (wrap_sub w (wrap w (x + y)) y), wrap_wrap, <- wrap_sub.
  replace (x + y - y) with x by ring. reflexivity.
Qed.

Local Lemma wrapped_sub_cancel_left w x y : wrap w (wrap w (x - y) + y) = wrap w x.
Proof.
  rewrite (wrap_add w (wrap w (x - y)) y), wrap_wrap, <- wrap_add.
  replace (x - y + y) with x by ring. reflexivity.
Qed.

Local Lemma wrapped_sub_cancel_right w x y : wrap w (x - wrap w (x - y)) = wrap w y.
Proof.
  rewrite (wrap_sub w x (wrap w (x - y))), wrap_wrap, <- wrap_sub.
  replace (x - (x - y)) with y by ring. reflexivity.
Qed.

Definition wrapped_assume_binary_c o wa wb a b rw q : Cost.t (wrapped * wrapped) :=
  match o with
  | bvadd => Cost.step ;; Cost.ret
      (wrapped_meet wa a (wrapped_sub wa q b), wrapped_meet wb b (wrapped_sub wb q a))
  | bvsub => Cost.step ;; Cost.ret
      (wrapped_meet wa a (wrapped_add wa q b), wrapped_meet wb b (wrapped_sub wb a q))
  | _ => wrapped_assume_binary_base_c o wa wb a b rw q
  end.

Local Lemma wrapped_assume_add_sound w a b q x y :
  wrapped_gamma w a x -> wrapped_gamma w b y -> wrapped_gamma w q (wadd w x y) ->
  wrapped_pair_gamma w w (Cost.value (wrapped_assume_binary_c bvadd w w a b w q)) x y.
Proof.
  intros Ha Hb Hq. split; apply wrapped_meet_sound; try assumption.
  - pose proof (wrapped_sub_sound w q b (wadd w x y) y Hq Hb) as Hleft.
    rewrite wadd_value, wrapped_add_cancel, (wrap_id w x (wrapped_gamma_word _ _ _ Ha))
      in Hleft. exact Hleft.
  - pose proof (wrapped_sub_sound w q a (wadd w x y) x Hq Ha) as Hright.
    rewrite wadd_value in Hright. replace (x + y) with (y + x) in Hright by ring.
    rewrite wrapped_add_cancel, (wrap_id w y (wrapped_gamma_word _ _ _ Hb)) in Hright.
    exact Hright.
Qed.

Local Lemma wrapped_assume_sub_sound w a b q x y :
  wrapped_gamma w a x -> wrapped_gamma w b y -> wrapped_gamma w q (wsub w x y) ->
  wrapped_pair_gamma w w (Cost.value (wrapped_assume_binary_c bvsub w w a b w q)) x y.
Proof.
  intros Ha Hb Hq. split; apply wrapped_meet_sound; try assumption.
  - pose proof (wrapped_add_sound w q b (wsub w x y) y Hq Hb) as Hleft.
    rewrite wsub_value, wrapped_sub_cancel_left, (wrap_id w x (wrapped_gamma_word _ _ _ Ha))
      in Hleft. exact Hleft.
  - pose proof (wrapped_sub_sound w a q x (wsub w x y) Ha Hq) as Hright.
    rewrite wsub_value, wrapped_sub_cancel_right, (wrap_id w y (wrapped_gamma_word _ _ _ Hb))
      in Hright. exact Hright.
Qed.

(** Add and subtract assumptions invert the modular operation before meeting the operands. *)
Theorem wrapped_assume_binary_sound o wa wb a b rw q x y z :
  wrapped_gamma wa a x -> wrapped_gamma wb b y -> wrapped_gamma rw q z ->
  eval_op o [(wa, x); (wb, y)] = Some (rw, z) ->
  wrapped_pair_gamma wa wb (Cost.value (wrapped_assume_binary_c o wa wb a b rw q)) x y.
Proof.
  intros Ha Hb Hq Heval.
  op_cases o by (eapply wrapped_assume_binary_base_sound; eassumption).
  - pose proof (eval_op_fun2_width bvadd wadd wa wb x y (rw, z) eq_refl Heval) as ->.
    rewrite (eval_op_fun2 bvadd wb x y wadd eq_refl) in Heval.
    inversion Heval; subst rw z. now apply wrapped_assume_add_sound.
  - pose proof (eval_op_fun2_width bvsub wsub wa wb x y (rw, z) eq_refl Heval) as ->.
    rewrite (eval_op_fun2 bvsub wb x y wsub eq_refl) in Heval.
    inversion Heval; subst rw z. now apply wrapped_assume_sub_sound.
Qed.

(** Binary circular assumptions always refine each original operand. *)
Theorem wrapped_assume_binary_lower o wa wb a b rw q :
  wrapped_leb wa (fst (Cost.value (wrapped_assume_binary_c o wa wb a b rw q))) a = true /\
  wrapped_leb wb (snd (Cost.value (wrapped_assume_binary_c o wa wb a b rw q))) b = true.
Proof.
  op_cases o by apply wrapped_assume_binary_base_lower; split; apply wrapped_meet_lower_left.
Qed.

Definition wrapped_assume_unary (o : op) (w : width) (a : wrapped) (rw : width) (q : wrapped) :
    wrapped :=
  match o with
  | bvzext _ | bvsext _ => wrapped_meet w a (wrapped_rewrap w rw q)
  | bvtrunc _ => wrapped_assume_trunc w a rw q
  | _ => wrapped_norm w a
  end.

(** Resize assumptions retain operands satisfying the result at its independent result width. *)
Theorem wrapped_assume_unary_sound o w a rw q x z :
  wrapped_gamma w a x -> wrapped_gamma rw q z -> eval_op o [(w, x)] = Some (rw, z) ->
  wrapped_gamma w (wrapped_assume_unary o w a rw q) x.
Proof.
  intros Ha Hq Heval. pose proof (wrapped_gamma_word w a x Ha) as Hword.
  op_cases o by exact (proj2 (wrapped_norm_gamma w a x) Ha).
  - rewrite eval_op_zext in Heval. inversion Heval; subst rw z.
    apply wrapped_meet_sound; [exact Ha|].
    pose proof (wrapped_rewrap_sound w (w + extra)%positive q _ Hq) as Hproject.
    rewrite wrap_narrow, wrap_wrap, (wrap_id w x Hword) in Hproject.
    + exact Hproject.
    + apply width_add_le.
  - rewrite eval_op_sext in Heval. inversion Heval; subst rw z.
    apply wrapped_meet_sound; [exact Ha|].
    pose proof (wrapped_rewrap_sound w (w + extra)%positive q _ Hq) as Hproject.
    rewrite wrap_narrow, wrap_signed, (wrap_id w x Hword) in Hproject.
    + exact Hproject.
    + apply width_add_le.
  - rewrite eval_op_trunc in Heval. destruct (Pos.leb target w); [|discriminate].
    rewrite (wrap_id w x Hword) in Heval. inversion Heval; subst rw z.
    now apply wrapped_assume_trunc_sound.
Qed.

(** Unary circular assumptions are structurally below the original operand. *)
Theorem wrapped_assume_unary_lower o w a rw q :
  wrapped_leb w (wrapped_assume_unary o w a rw q) a = true.
Proof.
  op_cases o by exact (proj2 (wrapped_norm_leb w a)); try apply wrapped_meet_lower_left.
Qed.
