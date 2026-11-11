(** * Actual jump-update effects and row frontiers

    Covered ground rows remain covered unless one of their actual dependencies is queued.
    For example, a joined output that also changes a return dependency is rescheduled.
    Builds on: FrameworkTabulate, FrameworkTabQueue and the public jump-row specification. *)

From Stdlib Require Import List Bool PArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet.
From Galois.Lattice Require Import LatticeCore.
From Galois.Program Require Import ProgramIcfg.
From Galois.Framework Require Import FrameworkMicro FrameworkIfds FrameworkIde FrameworkTabulate
  FrameworkTabQueue FrameworkTabJumpProgress.
Import List.ListNotations.

Module TabJumpEffects.

(** A ground row reads only its actual path or matched-return dependencies. *)
Definition reads {N E P D F} (row : Jump.row N E P D F) : list (Tab.key N D) :=
  match row with
  | Jump.Seed _ | Jump.Call _ => []
  | Jump.Path root a => [(root, Jump.source a)]
  | Jump.Return root a b => [(root, Jump.source a); (Jump.target a, Jump.source b)]
  end.

(** A pending row has at least one actual queued dependency key. *)
Definition pending {N E P D A F} (I : Ide.t N E P D A F)
    (s : Tab.state N E P D F) (row : Jump.row N E P D F) :=
  exists key, In key (reads row) /\ In key (Tab.work s).

(** A row frontier is covered already or has an actual scheduled dependency. *)
Definition frontier {N E P D A F} (I : Ide.t N E P D A F)
    (s : Tab.state N E P D F) (row : Jump.row N E P D F) :=
  Jump.holds I (Jump.lookup I (Tab.jumps s)) row \/ pending I s row.

(** Updating a canonical encoded jump key changes exactly the corresponding lawful query. *)
Theorem lookup_set {N E P D A F} (I : Ide.t N E P D A F) m key f query :
  Map.wf positive_encoding m ->
  Jump.lookup I (Map.set positive_encoding (encode (Jump.enc I) key) f m) query =
    if eqb (Jump.enc I) query key then f else Jump.lookup I m query.
Proof.
  intro Hwf; rewrite !Jump.lookup_equation, !Map.find_or_equation.
  rewrite Map.get_set by exact Hwf.
  assert (Htest : eqb positive_encoding (encode (Jump.enc I) query) (encode (Jump.enc I) key) =
    eqb (Jump.enc I) query key).
  { rewrite !eqb_equation; reflexivity. }
  rewrite Htest; destruct (eqb (Jump.enc I) query key); reflexivity.
Qed.

Local Lemma schedule_effect {N E P D A F} (I : Ide.t N E P D A F) key s :
  TabQueue.coherent (Jump.enc I) (Tab.work s) (Tab.pending s) ->
  let after := Tab.schedule I key s in
  Tab.jumps after = Tab.jumps s /\
    incl (Tab.work s) (Tab.work after) /\ In key (Tab.work after).
Proof.
  intro Hqueue; rewrite Tab.schedule_equation.
  destruct (FinSet.mem (Jump.enc I) key (Tab.pending s)) eqn:Hqueued.
  - split; [reflexivity|]; split; [intros q Hq; exact Hq|].
    exact (TabQueue.queued_in_work (Jump.enc I) key (Tab.work s) (Tab.pending s) Hqueue Hqueued).
  - split; [reflexivity|]; split; [intros q Hq; right; exact Hq|left; reflexivity].
Qed.

(** Scheduling keeps every previous key and ensures its own key is pending in the actual worklist. *)
Theorem schedule_work {N E P D A F} (I : Ide.t N E P D A F) key s :
  TabQueue.coherent (Jump.enc I) (Tab.work s) (Tab.pending s) ->
  incl (Tab.work s) (Tab.work (Tab.schedule I key s)) /\
    In key (Tab.work (Tab.schedule I key s)).
Proof.
  intro Hqueue; exact (proj2 (schedule_effect I key s Hqueue)).
Qed.

(** Actual joined updates ascend, retain queued work and schedule any changed queried dependency. *)
Theorem update_effects {N E P D A F} (I : Ide.t N E P D A F) key f s :
  encoding_laws (Jump.enc I) -> lattice_laws (Micro.lat (Ide.micro I)) ->
  TabJumpProgress.shape I s ->
  let after := Tab.update I key f s in
  (forall q, leb (Micro.lat (Ide.micro I)) (Jump.lookup I (Tab.jumps s) q)
    (Jump.lookup I (Tab.jumps after) q) = true) /\
  incl (Tab.work s) (Tab.work after) /\
  (forall q, Jump.lookup I (Tab.jumps after) q = Jump.lookup I (Tab.jumps s) q \/
    In q (Tab.work after)) /\
  leb (Micro.lat (Ide.micro I)) f (Jump.lookup I (Tab.jumps after) key) = true.
Proof.
  intros HK HL [Hwf Hqueue]; rewrite Tab.update_equation.
  destruct (leb (Micro.lat (Ide.micro I)) f (Jump.lookup I (Tab.jumps s) key)) eqn:Hcovered.
  - split; [intro q; apply leb_refl; exact HL|].
    split; [intros q Hq; exact Hq|]; split; [intro q; left; reflexivity|exact Hcovered].
  - set (updated := Map.set positive_encoding (encode (Jump.enc I) key)
      (join (Micro.lat (Ide.micro I)) (Jump.lookup I (Tab.jumps s) key) f) (Tab.jumps s)).
    remember (Tab.schedule I key
      (Tab.State updated (Tab.callers s) (Tab.ends s) (Tab.work s) (Tab.pending s)))
      as after eqn:Hafter.
    pose proof (schedule_effect I key
      (Tab.State updated (Tab.callers s) (Tab.ends s) (Tab.work s) (Tab.pending s)) Hqueue)
      as Heffect.
    rewrite <- Hafter in Heffect; destruct Heffect as [Hjumps [Hwork Hkey]].
    cbn [Tab.jumps Tab.work] in Hjumps, Hwork, Hkey.
    split.
    + intro q; rewrite Hjumps; unfold updated; rewrite lookup_set by exact Hwf.
      destruct (eqb (Jump.enc I) q key) eqn:Heq.
      * apply (eqb_true_iff (Jump.enc I) HK) in Heq; subst q; apply join_upper_l; exact HL.
      * apply leb_refl; exact HL.
    + split; [exact Hwork|]; split.
      * intro q; rewrite Hjumps; unfold updated; rewrite lookup_set by exact Hwf.
        destruct (eqb (Jump.enc I) q key) eqn:Heq; [|left; reflexivity].
        apply (eqb_true_iff (Jump.enc I) HK) in Heq; subst q; right; exact Hkey.
      * rewrite Hjumps; unfold updated; rewrite lookup_set by exact Hwf.
        rewrite eqb_refl; apply join_upper_r; exact HL.
Qed.

Local Lemma same_or_pending {K} (same : K -> Prop) keys work :
  (forall key, same key \/ In key work) ->
  (forall key, In key keys -> same key) \/ (exists key, In key keys /\ In key work).
Proof.
  intro Hcases; induction keys as [|key keys IH].
  - left; intros q Hq; inversion Hq.
  - destruct (Hcases key) as [Hsame|Hpending].
    + destruct IH as [Hall|[q [Hq Hwork]]].
      * left; intros q [Heq|Hq]; [subst q; exact Hsame|apply Hall; exact Hq].
      * right; exists q; split; [right; exact Hq|exact Hwork].
    + right; exists key; split; [left; reflexivity|exact Hpending].
Qed.

Local Lemma row_transport {N E P D A F} (I : Ide.t N E P D A F) before after row :
  lattice_laws (Micro.lat (Ide.micro I)) ->
  (forall key, leb (Micro.lat (Ide.micro I)) (before key) (after key) = true) ->
  (forall key, In key (reads row) -> after key = before key) ->
  Jump.holds I before row -> Jump.holds I after row.
Proof.
  intros HL Hgrow Hsame Hrow; destruct row as [root|a|root a|root a b];
    unfold Jump.holds in *.
  - eapply leb_trans; [exact HL|exact Hrow|apply Hgrow].
  - eapply leb_trans; [exact HL|exact Hrow|apply Hgrow].
  - rewrite (Hsame (root, Jump.source a) (or_introl eq_refl)).
    eapply leb_trans; [exact HL|exact Hrow|apply Hgrow].
  - rewrite (Hsame (root, Jump.source a) (or_introl eq_refl)).
    rewrite (Hsame (Jump.target a, Jump.source b) (or_intror (or_introl eq_refl))).
    eapply leb_trans; [exact HL|exact Hrow|apply Hgrow].
Qed.

Section Effects.
Context {N E P D A F} (I : Ide.t N E P D A F).
Context (HK : encoding_laws (Jump.enc I)).
Context (HL : lattice_laws (Micro.lat (Ide.micro I))).

(** Any joined update preserves a row frontier without requiring callback monotonicity. *)
Theorem update_frontier key f s row :
  TabJumpProgress.shape I s -> frontier I s row -> frontier I (Tab.update I key f s) row.
Proof.
  intros Hshape [Hrow|[reader [Hread Hwork]]].
  - destruct (update_effects I key f s HK HL Hshape) as
      [Hgrow [Hwork [Hchanges Hcandidate]]].
    destruct (same_or_pending _ (reads row) (Tab.work (Tab.update I key f s)) Hchanges)
      as [Hsame|Hpending].
    + left; apply (row_transport I _ _ row HL Hgrow Hsame Hrow).
    + right; exact Hpending.
  - destruct (update_effects I key f s HK HL Hshape) as [Hgrow [Hworkgrow Hrest]].
    right; exists reader; split; [exact Hread|apply Hworkgrow; exact Hwork].
Qed.

(** A path-edge proposal establishes the frontier for its own actual row. *)
Theorem path_covers root a s :
  TabJumpProgress.shape I s ->
  frontier I
    (Tab.update I (root, Jump.target a)
      (Micro.compose (Ide.micro I) (Jump.weight a)
        (Jump.lookup I (Tab.jumps s) (root, Jump.source a))) s)
    (Jump.Path root a).
Proof.
  intro Hshape.
  set (f := Micro.compose (Ide.micro I) (Jump.weight a)
    (Jump.lookup I (Tab.jumps s) (root, Jump.source a))).
  destruct (update_effects I (root, Jump.target a) f s HK HL Hshape) as
    [Hgrow [Hwork [Hchanges Hcandidate]]].
  destruct (same_or_pending _ (reads (Jump.Path root a))
    (Tab.work (Tab.update I (root, Jump.target a) f s)) Hchanges) as [Hsame|Hpending].
  - left; unfold Jump.holds; cbn beta zeta.
    rewrite (Hsame (root, Jump.source a) (or_introl eq_refl)).
    exact Hcandidate.
  - right; exact Hpending.
Qed.

(** Actual matched-return replay establishes the frontier of that same binary row. *)
Theorem return_covers root a b s :
  TabJumpProgress.shape I s ->
  Cost.value (Jump.matches_c (Icfg.site_enc (Ifds.icfg (Ide.ifds I))) a b) = true ->
  frontier I (Tab.return_ I root a b s) (Jump.Return root a b).
Proof.
  intros Hshape Hmatch; rewrite Tab.return_equation, Hmatch.
  set (f := Micro.compose (Ide.micro I) (Jump.weight b)
    (Micro.compose (Ide.micro I)
      (Jump.lookup I (Tab.jumps s) (Jump.target a, Jump.source b))
      (Micro.compose (Ide.micro I) (Jump.weight a)
        (Jump.lookup I (Tab.jumps s) (root, Jump.source a))))).
  destruct (update_effects I (root, Jump.target b) f s HK HL Hshape) as
    [Hgrow [Hwork [Hchanges Hcandidate]]].
  destruct (same_or_pending _ (reads (Jump.Return root a b))
    (Tab.work (Tab.update I (root, Jump.target b) f s)) Hchanges) as [Hsame|Hpending].
  - left; unfold Jump.holds; cbn beta zeta.
    pose proof (Hsame (root, Jump.source a) (or_introl eq_refl)) as Hbefore.
    pose proof (Hsame (Jump.target a, Jump.source b) (or_intror (or_introl eq_refl))) as Hinside.
    assert (Hproposal :
      Micro.compose (Ide.micro I) (Jump.weight b)
        (Micro.compose (Ide.micro I)
          (Jump.lookup I (Tab.jumps (Tab.update I (root, Jump.target b) f s))
            (Jump.target a, Jump.source b))
          (Micro.compose (Ide.micro I) (Jump.weight a)
            (Jump.lookup I (Tab.jumps (Tab.update I (root, Jump.target b) f s))
              (root, Jump.source a)))) = f).
    { unfold f in Hbefore, Hinside; unfold f; congruence. }
    exact (eq_trans (f_equal (fun proposal => leb (Micro.lat (Ide.micro I)) proposal
      (Jump.lookup I (Tab.jumps (Tab.update I (root, Jump.target b) f s))
        (Jump.output (Jump.Return root a b)))) Hproposal) Hcandidate).
  - right; exact Hpending.
Qed.

(** Replaying any return preserves the frontier of every other ground row. *)
Theorem return_frontier root a b s row :
  TabJumpProgress.shape I s -> frontier I s row -> frontier I (Tab.return_ I root a b s) row.
Proof.
  intros Hshape Hfrontier; rewrite Tab.return_equation.
  destruct (Cost.value (Jump.matches_c (Icfg.site_enc (Ifds.icfg (Ide.ifds I))) a b));
    [apply update_frontier|]; assumption.
Qed.

(** Scheduling a coherent queue retains its map well-formedness and queue shape. *)
Theorem schedule_shape key s :
  TabJumpProgress.shape I s -> TabJumpProgress.shape I (Tab.schedule I key s).
Proof.
  intros [Hwf Hqueue]; rewrite Tab.schedule_equation.
  destruct (FinSet.mem (Jump.enc I) key (Tab.pending s)) eqn:Hqueued; split;
    try exact Hwf; try exact Hqueue.
  apply TabQueue.insert_coherent; assumption.
Qed.

(** Any actual joined proposal preserves jump-map and queue shape. *)
Theorem update_shape key f s :
  TabJumpProgress.shape I s -> TabJumpProgress.shape I (Tab.update I key f s).
Proof.
  intros [Hwf Hqueue]; rewrite Tab.update_equation.
  destruct (leb (Micro.lat (Ide.micro I)) f (Jump.lookup I (Tab.jumps s) key)).
  - split; assumption.
  - apply schedule_shape; split; [apply Map.wf_set; exact Hwf|exact Hqueue].
Qed.

(** Every return replay retains canonical map and queue shape. *)
Theorem return_shape root a b s :
  TabJumpProgress.shape I s -> TabJumpProgress.shape I (Tab.return_ I root a b s).
Proof.
  intro Hshape; rewrite Tab.return_equation.
  destruct (Cost.value (Jump.matches_c (Icfg.site_enc (Ifds.icfg (Ide.ifds I))) a b));
    [apply update_shape|]; exact Hshape.
Qed.

Local Lemma fold_valid {X S} (Inv : S -> Prop) (f : S -> X -> S) xs s :
  (forall s x, Inv s -> In x xs -> Inv (f s x)) -> Inv s -> Inv (fold_left f xs s).
Proof.
  revert s; induction xs as [|x xs IH]; intros s Hstep Hs; cbn [fold_left].
  - exact Hs.
  - apply IH.
    + intros t y Ht Hy; apply Hstep; [exact Ht|right; exact Hy].
    + apply Hstep; [exact Hs|left; reflexivity].
Qed.

(** Complete actual call processing preserves map and queue shape. *)
Theorem call_shape root a s :
  TabJumpProgress.shape I s -> TabJumpProgress.shape I (Cost.value (Tab.call_c I root a s)).
Proof.
  intro Hshape; rewrite Tab.call_equation; apply fold_valid.
  - intros t kv Ht Hin; apply return_shape; exact Ht.
  - exact Hshape.
Qed.

(** Complete actual end processing preserves map and queue shape. *)
Theorem end_shape root a s :
  TabJumpProgress.shape I s -> TabJumpProgress.shape I (Cost.value (Tab.end_c I root a s)).
Proof.
  intro Hshape; rewrite Tab.end_equation; apply fold_valid.
  - intros t kv Ht Hin; apply return_shape; exact Ht.
  - exact Hshape.
Qed.

(** Registering a caller and replaying ends preserves every existing row frontier. *)
Theorem call_frontier root a s row :
  TabJumpProgress.shape I s -> frontier I s row ->
  frontier I (Cost.value (Tab.call_c I root a s)) row.
Proof.
  intros Hshape Hfrontier; rewrite Tab.call_equation.
  refine (proj2 (fold_valid (fun t => TabJumpProgress.shape I t /\ frontier I t row)
    (fun t kv => Tab.return_ I root a (snd kv) t) _ _ _ _)).
  - intros t kv [Ht HP] Hin; split.
    + apply return_shape; exact Ht.
    + apply return_frontier; assumption.
  - split; assumption.
Qed.

(** Registering an end and replaying callers preserves every existing row frontier. *)
Theorem end_frontier root a s row :
  TabJumpProgress.shape I s -> frontier I s row ->
  frontier I (Cost.value (Tab.end_c I root a s)) row.
Proof.
  intros Hshape Hfrontier; rewrite Tab.end_equation.
  refine (proj2 (fold_valid (fun t => TabJumpProgress.shape I t /\ frontier I t row)
    (fun t kv => Tab.return_ I (fst (snd kv)) (snd (snd kv)) a t) _ _ _ _)).
  - intros t kv [Ht HP] Hin; split.
    + apply return_shape; exact Ht.
    + apply return_frontier; assumption.
  - split; assumption.
Qed.

(** Every actual arc case preserves every already-established row frontier. *)
Theorem arc_frontier root a s row :
  TabJumpProgress.shape I s -> frontier I s row ->
  frontier I (Cost.value (Tab.arc_c I root a s)) row.
Proof.
  intros Hshape Hfrontier; rewrite Tab.arc_equation; destruct (Jump.kind a).
  - apply update_frontier; assumption.
  - apply call_frontier; assumption.
  - apply end_frontier; assumption.
Qed.

(** Every actual arc case preserves canonical map and queue shape. *)
Theorem arc_shape root a s :
  TabJumpProgress.shape I s -> TabJumpProgress.shape I (Cost.value (Tab.arc_c I root a s)).
Proof.
  intro Hshape; rewrite Tab.arc_equation; destruct (Jump.kind a).
  - apply update_shape; exact Hshape.
  - apply call_shape; exact Hshape.
  - apply end_shape; exact Hshape.
Qed.

(** Actual return replay never removes a pending key. *)
Theorem return_work root a b s :
  TabJumpProgress.shape I s -> incl (Tab.work s) (Tab.work (Tab.return_ I root a b s)).
Proof.
  intro Hshape; rewrite Tab.return_equation.
  destruct (Cost.value (Jump.matches_c (Icfg.site_enc (Ifds.icfg (Ide.ifds I))) a b)).
  - exact (proj1 (proj2 (update_effects I _ _ s HK HL Hshape))).
  - intros key Hkey; exact Hkey.
Qed.

(** Actual call processing never removes a pending key. *)
Theorem call_work root a s :
  TabJumpProgress.shape I s -> incl (Tab.work s) (Tab.work (Cost.value (Tab.call_c I root a s))).
Proof.
  intro Hshape; rewrite Tab.call_equation.
  refine (proj2 (fold_valid
    (fun t => TabJumpProgress.shape I t /\ incl (Tab.work s) (Tab.work t))
    (fun t kv => Tab.return_ I root a (snd kv) t) _ _ _ _)).
  - intros t kv [Ht Hincluded] Hin; split.
    + apply return_shape; exact Ht.
    + intros key Hkey; apply return_work; [exact Ht|apply Hincluded; exact Hkey].
  - split; [exact Hshape|intros key Hkey; exact Hkey].
Qed.

(** Actual end processing never removes a pending key. *)
Theorem end_work root a s :
  TabJumpProgress.shape I s -> incl (Tab.work s) (Tab.work (Cost.value (Tab.end_c I root a s))).
Proof.
  intro Hshape; rewrite Tab.end_equation.
  refine (proj2 (fold_valid
    (fun t => TabJumpProgress.shape I t /\ incl (Tab.work s) (Tab.work t))
    (fun t kv => Tab.return_ I (fst (snd kv)) (snd (snd kv)) a t) _ _ _ _)).
  - intros t kv [Ht Hincluded] Hin; split.
    + apply return_shape; exact Ht.
    + intros key Hkey; apply return_work; [exact Ht|apply Hincluded; exact Hkey].
  - split; [exact Hshape|intros key Hkey; exact Hkey].
Qed.

(** All arc processing retains pending work until the next actual outer pop. *)
Theorem arc_work root a s :
  TabJumpProgress.shape I s -> incl (Tab.work s) (Tab.work (Cost.value (Tab.arc_c I root a s))).
Proof.
  intro Hshape; rewrite Tab.arc_equation; destruct (Jump.kind a).
  - exact (proj1 (proj2 (update_effects I _ _ s HK HL Hshape))).
  - apply call_work; exact Hshape.
  - apply end_work; exact Hshape.
Qed.

End Effects.

(** A local scan retains any established invariant and post-property under its actual callbacks. *)
Theorem fold_closed {X S} (good P : S -> Prop) (f : S -> X -> S) xs s :
  (forall t x, good t -> In x xs -> good (f t x)) ->
  (forall t x, good t -> P t -> In x xs -> P (f t x)) ->
  good s -> P s -> good (fold_left f xs s) /\ P (fold_left f xs s).
Proof.
  revert s; induction xs as [|x xs IH]; intros s Hgood Hpreserve Hs HP; cbn [fold_left].
  - split; assumption.
  - apply IH.
    + intros t y Ht Hy; apply Hgood; [exact Ht|right; exact Hy].
    + intros t y Ht Hproperty Hy; apply Hpreserve; try assumption; right; exact Hy.
    + apply Hgood; [exact Hs|left; reflexivity].
    + apply Hpreserve; try assumption; left; reflexivity.
Qed.

(** A scan establishes a persistent property when one actual scanned occurrence establishes it. *)
Theorem fold_hit {X S} (good P : S -> Prop) (f : S -> X -> S) xs hit s :
  (forall t x, good t -> In x xs -> good (f t x)) ->
  (forall t x, good t -> P t -> In x xs -> P (f t x)) ->
  (forall t, good t -> P (f t hit)) ->
  In hit xs -> good s -> P (fold_left f xs s).
Proof.
  revert s; induction xs as [|x xs IH]; intros s Hgood Hpreserve Hhit Hin Hs;
    [inversion Hin|].
  cbn [fold_left]; destruct Hin as [Heq|Hin].
  - subst x; refine (proj2 (fold_closed good P f xs (f s hit) _ _ _ _)).
    + intros t y Ht Hy; apply Hgood; [exact Ht|right; exact Hy].
    + intros t y Ht HP Hy; apply Hpreserve; try assumption; right; exact Hy.
    + apply Hgood; [exact Hs|left; reflexivity].
    + apply Hhit; exact Hs.
  - apply IH; try assumption.
    + intros t y Ht Hy; apply Hgood; [exact Ht|right; exact Hy].
    + intros t y Ht HP Hy; apply Hpreserve; try assumption; right; exact Hy.
    + apply Hgood; [exact Hs|left; reflexivity].
Qed.

End TabJumpEffects.
