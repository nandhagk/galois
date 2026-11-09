(** * Structural progress of the actual jump worklist

    Jump keys, encoded bindings and nested records stay within the actual prepared support.
    For example, replaying an end uses the stored caller's own prepared root for its output key.
    Builds on: FrameworkTabRecords and FrameworkTabQueue. *)

From Stdlib Require Import List Bool PArith NArith Arith Lia.
From Galois.Cost Require Import CostMonad CostLoop.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet BaseIndex.
From Galois.Lattice Require Import LatticeCore LatticeHeight.
From Galois.Program Require Import ProgramIcfg.
From Galois.Framework Require Import FrameworkMicro FrameworkIfds FrameworkIde FrameworkTabulate
  FrameworkTabPaths FrameworkTabRecords FrameworkTabQueue FrameworkTabCost.
Import List.ListNotations Cost.Notations.

Module TabJumpProgress.

(** The jump map and the actual pending work have their canonical map and queue invariants. *)
Definition shape {N E P D A F} (I : Ide.t N E P D A F) (s : Tab.state N E P D F) :=
  Map.wf positive_encoding (Tab.jumps s) /\
  TabQueue.coherent (Jump.enc I) (Tab.work s) (Tab.pending s).

(** Stored codes and scheduled keys stay in the full prepared inventory, including bottom visits. *)
Definition supported {N E P D A F} (I : Ide.t N E P D A F)
    (p : Tab.prepared N E P D F) (s : Tab.state N E P D F) :=
  (forall key, In key (Tab.work s) -> In key (Tab.inventory p)) /\
  (forall code f, Map.get positive_encoding code (Tab.jumps s) = Some f ->
    In code (map (encode (Jump.enc I)) (Tab.inventory p))).

(** Structural progress retains bucket ownership together with finite jump support. *)
Definition invariant {N E P D A F} (I : Ide.t N E P D A F) start s :=
  TabRecords.valid I start s /\ shape I s /\ supported I (Tab.prepare I start) s.

(** Rank capacity is measured over every supplied prepared jump-key occurrence. *)
Definition remaining {N E P D A F} (I : Ide.t N E P D A F)
    (H : height (Micro.lat (Ide.micro I))) (p : Tab.prepared N E P D F) m :=
  fold_right (fun key total =>
    (bound H - rank H (Jump.lookup I m key) + total)%nat) O (Tab.inventory p).

(** The semantic potential retains remaining jump rank capacity and actual queued work. *)
Definition potential {N E P D A F} (I : Ide.t N E P D A F)
    (H : height (Micro.lat (Ide.micro I))) (p : Tab.prepared N E P D F)
    (s : Tab.state N E P D F) :=
  (remaining I H p (Tab.jumps s) + length (Tab.work s))%nat.

Local Lemma sum_monotone {X} (old new : X -> nat) xs :
  (forall x, In x xs -> new x <= old x)%nat ->
  (fold_right (fun x n => new x + n) O xs <=
    fold_right (fun x n => old x + n) O xs)%nat.
Proof.
  induction xs as [|x xs IH]; intro Hbound; cbn [fold_right]; [lia|].
  assert (Htail : forall y, In y xs -> (new y <= old y)%nat).
  { intros y Hy; apply Hbound; right; exact Hy. }
  specialize (IH Htail); specialize (Hbound x (or_introl eq_refl)); lia.
Qed.

Local Lemma sum_decreases {X} (old new : X -> nat) xs changed :
  In changed xs -> (forall x, In x xs -> new x <= old x)%nat ->
  (new changed < old changed)%nat ->
  (fold_right (fun x n => new x + n) O xs <
    fold_right (fun x n => old x + n) O xs)%nat.
Proof.
  induction xs as [|x xs IH]; intros Hin Hbound Hchanged; [inversion Hin|].
  cbn [fold_right]; assert (Htail : forall y, In y xs -> (new y <= old y)%nat).
  { intros y Hy; apply Hbound; right; exact Hy. }
  destruct Hin as [Heq|Hin].
  - subst x; pose proof (sum_monotone old new xs Htail); lia.
  - specialize (IH Hin Htail Hchanged); specialize (Hbound x (or_introl eq_refl)); lia.
Qed.

Local Lemma lookup_set {N E P D A F} (I : Ide.t N E P D A F) m key f query :
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

Local Lemma remaining_bound {N E P D A F} (I : Ide.t N E P D A F)
    (H : height (Micro.lat (Ide.micro I))) p m :
  (remaining I H p m <= bound H * length (Tab.inventory p))%nat.
Proof.
  unfold remaining; induction (Tab.inventory p) as [|key keys IH]; cbn [fold_right length];
    nia.
Qed.

Local Lemma schedule_potential {N E P D A F} (I : Ide.t N E P D A F)
    (H : height (Micro.lat (Ide.micro I))) p key s :
  (potential I H p (Tab.schedule I key s) <= S (potential I H p s))%nat.
Proof.
  rewrite Tab.schedule_equation.
  destruct (FinSet.mem (Jump.enc I) key (Tab.pending s));
    unfold potential; cbn [Tab.jumps Tab.work length]; lia.
Qed.

(** Actual joined jump updates spend rank capacity before adding pending work. *)
Theorem update_potential {N E P D A F} (I : Ide.t N E P D A F)
    (H : height (Micro.lat (Ide.micro I))) p key f s :
  encoding_laws (Jump.enc I) -> lattice_laws (Micro.lat (Ide.micro I)) ->
  Map.wf positive_encoding (Tab.jumps s) -> In key (Tab.inventory p) ->
  (potential I H p (Tab.update I key f s) <= potential I H p s)%nat.
Proof.
  intros HK HL Hwf Hkey; rewrite Tab.update_equation.
  destruct (leb (Micro.lat (Ide.micro I)) f (Jump.lookup I (Tab.jumps s) key)) eqn:Hcovered;
    [lia|].
  set (joined := join (Micro.lat (Ide.micro I)) (Jump.lookup I (Tab.jumps s) key) f).
  set (updated := Map.set positive_encoding (encode (Jump.enc I) key) joined (Tab.jumps s)).
  assert (Hrank : (rank H (Jump.lookup I (Tab.jumps s) key) < rank H joined)%nat).
  { apply TabCost.update_rank_progress; try exact HL; try exact Logic.I; exact Hcovered. }
  pose proof (rank_bounded H joined Logic.I) as Hrank_bound.
  assert (Hcredit : (bound H - rank H joined <
    bound H - rank H (Jump.lookup I (Tab.jumps s) key))%nat) by lia.
  assert (Hchanged : (remaining I H p updated < remaining I H p (Tab.jumps s))%nat).
  { unfold remaining; apply sum_decreases with (changed := key); [exact Hkey| |].
    - intros query Hquery; unfold updated; rewrite lookup_set by exact Hwf.
      destruct (eqb (Jump.enc I) query key) eqn:Heq; [|lia].
      apply (eqb_true_iff (Jump.enc I) HK) in Heq; subst query; lia.
    - unfold updated; rewrite lookup_set by exact Hwf; rewrite eqb_refl; exact Hcredit. }
  pose proof (schedule_potential I H p key
    (Tab.State updated (Tab.callers s) (Tab.ends s) (Tab.work s) (Tab.pending s))) as Hschedule.
  unfold potential in *; cbn [Tab.jumps Tab.work] in *; lia.
Qed.

Local Lemma fold_valid {X S} (P : S -> Prop) (f : S -> X -> S) xs s :
  (forall s x, P s -> In x xs -> P (f s x)) -> P s -> P (fold_left f xs s).
Proof.
  revert s; induction xs as [|x xs IH]; intros s Hstep Hs; cbn [fold_left].
  - exact Hs.
  - apply IH.
    + intros t y Ht Hy; apply Hstep; [exact Ht|right; exact Hy].
    + apply Hstep; [exact Hs|left; reflexivity].
Qed.

Local Lemma fold_nonincreasing {X S} (P : S -> Prop) (phi : S -> nat)
    (f : S -> X -> S) xs s :
  (forall s x, P s -> In x xs -> P (f s x) /\ phi (f s x) <= phi s)%nat ->
  P s -> P (fold_left f xs s) /\ (phi (fold_left f xs s) <= phi s)%nat.
Proof.
  revert s; induction xs as [|x xs IH]; intros s Hstep Hs; cbn [fold_left].
  - split; [exact Hs|lia].
  - destruct (Hstep s x Hs (or_introl eq_refl)) as [Hnext Hdecrease].
    assert (Htail : forall t y, P t -> In y xs ->
      P (f t y) /\ (phi (f t y) <= phi t)%nat).
    { intros t y Ht Hy; apply Hstep; [exact Ht|right; exact Hy]. }
    destruct (IH (f s x) Htail Hnext) as [Hfinal Hbound]; split; [exact Hfinal|lia].
Qed.

(** Every prepared root retains its own identity key even on an empty graph. *)
Theorem inventory_seed {N E P D A F} (I : Ide.t N E P D A F) start root :
  In root (TabPaths.roots I start) -> In (root, root) (Tab.inventory (Tab.prepare I start)).
Proof.
  rewrite Tab.prepare_equation; cbn [Tab.inventory].
  intro Hroot; apply in_flat_map; exists root; split; [exact Hroot|apply in_map_iff].
  exists root; split; [reflexivity|left; reflexivity].
Qed.

(** Every actual arc target is supported at each prepared outer root. *)
Theorem inventory_target {N E P D A F} (I : Ide.t N E P D A F) start root a :
  In root (TabPaths.roots I start) -> In a (Jump.arcs I) ->
  In (root, Jump.target a) (Tab.inventory (Tab.prepare I start)).
Proof.
  rewrite Tab.prepare_equation; cbn [Tab.inventory].
  intros Hroot Ha; apply in_flat_map; exists root; split; [exact Hroot|apply in_map_iff].
  exists (Jump.target a); split; [reflexivity|right; apply in_flat_map].
  exists a; split; [exact Ha|right; left; reflexivity].
Qed.

Section Run.
Context {N E P D A F} (I : Ide.t N E P D A F) (start : N).
Context (HV : encoding_laws (IdeValue.key_enc I)).
Context (HK : encoding_laws (Jump.enc I)).

Local Lemma schedule_invariant key s :
  invariant I start s -> In key (Tab.inventory (Tab.prepare I start)) ->
  invariant I start (Tab.schedule I key s).
Proof.
  intros [Hrecords [[Hwf Hqueue] [Hwork Hstored]]] Hkey; split.
  - apply TabRecords.schedule_valid; exact Hrecords.
  - rewrite Tab.schedule_equation.
    destruct (FinSet.mem (Jump.enc I) key (Tab.pending s)) eqn:Hqueued.
    + split; [split; assumption|split; assumption].
    + split.
      * split; [exact Hwf|apply TabQueue.insert_coherent; assumption].
      * split; [|exact Hstored].
        intros other [Heq|Hin]; [subst other; exact Hkey|apply Hwork; exact Hin].
Qed.

Local Lemma update_invariant key f s :
  invariant I start s -> In key (Tab.inventory (Tab.prepare I start)) ->
  invariant I start (Tab.update I key f s).
Proof.
  intros [Hrecords [[Hwf Hqueue] [Hwork Hstored]]] Hkey; rewrite Tab.update_equation.
  destruct (leb (Micro.lat (Ide.micro I)) f (Jump.lookup I (Tab.jumps s) key)).
  - split; [exact Hrecords|]; split; [split; assumption|split; assumption].
  - apply schedule_invariant; [|exact Hkey]; split.
    + apply TabRecords.rebuild_valid; exact Hrecords.
    + split.
      * split; [apply Map.wf_set; exact Hwf|exact Hqueue].
      * split; [exact Hwork|].
        intros code value Hget; cbn [Tab.jumps] in Hget.
        rewrite Map.get_set in Hget by exact Hwf.
        destruct (eqb positive_encoding code (encode (Jump.enc I) key)) eqn:Hcode.
        -- apply (eqb_true_iff positive_encoding positive_encoding_laws) in Hcode; subst code.
           apply in_map; exact Hkey.
        -- apply Hstored with (f := value); exact Hget.
Qed.

Local Lemma return_invariant root a b s :
  invariant I start s -> In root (TabPaths.roots I start) -> In b (Jump.arcs I) ->
  invariant I start (Tab.return_ I root a b s).
Proof.
  intros Hinv Hroot Hb; rewrite Tab.return_equation.
  destruct (Cost.value (Jump.matches_c (Icfg.site_enc (Ifds.icfg (Ide.ifds I))) a b));
    [|exact Hinv].
  apply update_invariant; [exact Hinv|apply inventory_target; assumption].
Qed.

Local Lemma call_invariant root a s :
  invariant I start s -> In root (TabPaths.roots I start) -> In a (Jump.arcs I) ->
  (exists p, Jump.kind a = Icfg.Call p) ->
  invariant I start (Cost.value (Tab.call_c I root a s)).
Proof.
  intros [Hrecords [Hshape Hsupport]] Hroot Ha Hkind.
  rewrite Tab.call_equation; apply fold_valid.
  - intros t [code b] Ht Hin; cbn [snd].
    assert (Hget : Map.get positive_encoding code (TabRecords.ends I s (Jump.target a)) = Some b).
    { apply (proj1 (Map.elements_spec positive_encoding positive_encoding_laws
        code b _ (TabRecords.end_buckets_wf Hrecords (Jump.target a)))); exact Hin. }
    pose proof (TabRecords.end_payload Hrecords _ _ _ Hget) as Howned.
    apply return_invariant; [exact Ht|exact Hroot|exact (proj1 (proj2 Howned))].
  - split.
    + apply TabRecords.register_call_valid; assumption.
    + split; assumption.
Qed.

Local Lemma end_invariant root a s :
  invariant I start s -> In root (TabPaths.roots I start) -> In a (Jump.arcs I) ->
  (exists p, Jump.kind a = Icfg.Return p) ->
  invariant I start (Cost.value (Tab.end_c I root a s)).
Proof.
  intros [Hrecords [Hshape Hsupport]] Hroot Ha Hkind.
  rewrite Tab.end_equation; apply fold_valid.
  - intros t [code [outer call]] Ht Hin; cbn [fst snd].
    assert (Hget : Map.get positive_encoding code (TabRecords.callers I s root) = Some (outer, call)).
    { apply (proj1 (Map.elements_spec positive_encoding positive_encoding_laws
        code (outer, call) _ (TabRecords.caller_buckets_wf Hrecords root))); exact Hin. }
    pose proof (TabRecords.caller_payload Hrecords _ _ _ _ Hget) as Howned.
    apply return_invariant; [exact Ht|exact (proj1 Howned)|exact Ha].
  - split.
    + apply TabRecords.register_end_valid; assumption.
    + split; assumption.
Qed.

Local Lemma arc_invariant root a s :
  invariant I start s -> In root (TabPaths.roots I start) -> In a (Jump.arcs I) ->
  invariant I start (Cost.value (Tab.arc_c I root a s)).
Proof.
  intros Hinv Hroot Ha; rewrite Tab.arc_equation.
  destruct (Jump.kind a) as [|p|p] eqn:Hkind.
  - apply update_invariant; [exact Hinv|apply inventory_target; assumption].
  - apply call_invariant; try assumption; exists p; exact Hkind.
  - apply end_invariant; try assumption; exists p; exact Hkind.
Qed.

(** Actual initialization establishes coherent finite keys and owned empty record maps internally. *)
Theorem initial_invariant : invariant I start (Tab.initial I (Tab.prepare I start)).
Proof.
  rewrite Tab.initial_equation; apply fold_valid.
  - intros s root Hs Hroot.
    apply update_invariant; [exact Hs|apply inventory_seed].
    rewrite Tab.prepare_equation in Hroot; exact Hroot.
  - apply fold_valid.
    + intros s key Hs Hkey; apply schedule_invariant; assumption.
    + split; [apply TabRecords.empty_valid|]; split.
      * split; [apply Map.wf_empty|apply TabQueue.empty_coherent].
      * split; [intros key Hin; inversion Hin|].
        intros code f Hget; cbn [Tab.jumps] in Hget.
        rewrite Map.get_empty in Hget; discriminate.
Qed.

(** Each actual jump callback retains coherent work, finite encoded keys and owned buckets. *)
Theorem step_invariant s :
  invariant I start s ->
  match Tab.step I (Tab.prepare I start) s with
  | inl next | inr next => invariant I start next
  end.
Proof.
  intros [Hrecords [[Hwf Hqueue] [Hwork Hstored]]]; rewrite Tab.tabulate_equation.
  destruct (Tab.work s) as [|[root v] rest] eqn:Hlist.
  - split; [exact Hrecords|]; split.
    + split; [exact Hwf|rewrite Hlist; exact Hqueue].
    + split; [|exact Hstored]; intros key Hkey; rewrite Hlist in Hkey; exact (Hwork key Hkey).
  - apply fold_valid.
    + intros t a Ht Ha; apply arc_invariant; [exact Ht| |].
      * apply (TabRecords.inventory_root I start (root, v)), Hwork; left; reflexivity.
      * apply TabRecords.outgoing_member with (start := start) (v := v); exact Ha.
    + split; [apply TabRecords.rebuild_valid; exact Hrecords|]; split.
      * split; [exact Hwf|apply TabQueue.pop_coherent; assumption].
      * split; [|exact Hstored]; intros key Hkey; apply Hwork; right; exact Hkey.
Qed.

(** Every actual raw jump state retains the structural invariants, including on exhaustion. *)
Theorem raw_invariant fuel :
  match Tab.raw I start fuel with
  | inl s | inr s => invariant I start s
  end.
Proof.
  rewrite Tab.raw_equation.
  pose proof (iterate_value (Tab.step_c I (Tab.prepare I start)) fuel
    (Tab.initial I (Tab.prepare I start))) as Hrun.
  assert (Hpreserved : forall n s result, runs (Tab.step_c I (Tab.prepare I start)) n s result ->
    invariant I start s ->
    match result with inl next | inr next => invariant I start next end).
  { intros n s result Hr; induction Hr as [s|n s r Hstop|n s next result Hnext Hr IH];
      intro Hinv.
    - exact Hinv.
    - pose proof (step_invariant s Hinv) as Hstep.
      rewrite Tab.step_c_value in Hstop; rewrite Hstop in Hstep; exact Hstep.
    - apply IH; pose proof (step_invariant s Hinv) as Hstep.
      rewrite Tab.step_c_value in Hnext; rewrite Hnext in Hstep; exact Hstep. }
  exact (Hpreserved _ _ _ Hrun initial_invariant).
Qed.

Section Height.
Context (H : height (Micro.lat (Ide.micro I))).
Context (HL : lattice_laws (Micro.lat (Ide.micro I))).

Local Lemma return_progress root a b s :
  invariant I start s -> In root (TabPaths.roots I start) -> In b (Jump.arcs I) ->
  invariant I start (Tab.return_ I root a b s) /\
    (potential I H (Tab.prepare I start) (Tab.return_ I root a b s) <=
      potential I H (Tab.prepare I start) s)%nat.
Proof.
  intros Hinv Hroot Hb; split; [apply return_invariant; assumption|].
  rewrite Tab.return_equation.
  destruct (Cost.value (Jump.matches_c (Icfg.site_enc (Ifds.icfg (Ide.ifds I))) a b)); [|lia].
  apply update_potential; [exact HK|exact HL|exact (proj1 (proj1 (proj2 Hinv)))|].
  apply inventory_target; assumption.
Qed.

Local Lemma call_progress root a s :
  invariant I start s -> In root (TabPaths.roots I start) -> In a (Jump.arcs I) ->
  (exists p, Jump.kind a = Icfg.Call p) ->
  invariant I start (Cost.value (Tab.call_c I root a s)) /\
    (potential I H (Tab.prepare I start) (Cost.value (Tab.call_c I root a s)) <=
      potential I H (Tab.prepare I start) s)%nat.
Proof.
  intros [Hrecords [Hshape Hsupport]] Hroot Ha Hkind.
  rewrite !Tab.call_equation.
  assert (Hphi : potential I H (Tab.prepare I start) s =
    potential I H (Tab.prepare I start) (TabRecords.registered_call I root a s)) by reflexivity.
  rewrite Hphi; apply fold_nonincreasing.
  - intros t [code b] Ht Hin; cbn [snd].
    pose proof (TabRecords.end_element I start s (Jump.target a) code b Hrecords Hin) as Howned.
    apply return_progress; [exact Ht|exact Hroot|exact (proj1 (proj2 Howned))].
  - split.
    + apply TabRecords.register_call_valid; assumption.
    + split; assumption.
Qed.

Local Lemma end_progress root a s :
  invariant I start s -> In root (TabPaths.roots I start) -> In a (Jump.arcs I) ->
  (exists p, Jump.kind a = Icfg.Return p) ->
  invariant I start (Cost.value (Tab.end_c I root a s)) /\
    (potential I H (Tab.prepare I start) (Cost.value (Tab.end_c I root a s)) <=
      potential I H (Tab.prepare I start) s)%nat.
Proof.
  intros [Hrecords [Hshape Hsupport]] Hroot Ha Hkind.
  rewrite !Tab.end_equation.
  assert (Hphi : potential I H (Tab.prepare I start) s =
    potential I H (Tab.prepare I start) (TabRecords.registered_end I root a s)) by reflexivity.
  rewrite Hphi; apply fold_nonincreasing.
  - intros t [code [outer call]] Ht Hin; cbn [fst snd].
    pose proof (TabRecords.caller_element I start s root code outer call Hrecords Hin) as Howned.
    apply return_progress; [exact Ht|exact (proj1 Howned)|exact Ha].
  - split.
    + apply TabRecords.register_end_valid; assumption.
    + split; assumption.
Qed.

Local Lemma arc_progress root a s :
  invariant I start s -> In root (TabPaths.roots I start) -> In a (Jump.arcs I) ->
  invariant I start (Cost.value (Tab.arc_c I root a s)) /\
    (potential I H (Tab.prepare I start) (Cost.value (Tab.arc_c I root a s)) <=
      potential I H (Tab.prepare I start) s)%nat.
Proof.
  intros Hinv Hroot Ha; rewrite !Tab.arc_equation.
  destruct (Jump.kind a) as [|p|p] eqn:Hkind.
  - split; [apply update_invariant; [exact Hinv|apply inventory_target; assumption]|].
    apply update_potential; [exact HK|exact HL|exact (proj1 (proj1 (proj2 Hinv)))|].
    apply inventory_target; assumption.
  - apply call_progress; try assumption; exists p; exact Hkind.
  - apply end_progress; try assumption; exists p; exact Hkind.
Qed.

Local Lemma outgoing_progress root source s :
  invariant I start s -> In root (TabPaths.roots I start) ->
  let final := fold_left (fun t a => Cost.value (Tab.arc_c I root a t))
    (Index.find (IdeValue.key_enc I) source (Tab.outgoing (Tab.prepare I start))) s in
  invariant I start final /\
    (potential I H (Tab.prepare I start) final <= potential I H (Tab.prepare I start) s)%nat.
Proof.
  intros Hinv Hroot; apply fold_nonincreasing; [|exact Hinv].
  intros t a Ht Ha; apply arc_progress; [exact Ht|exact Hroot|].
  apply TabRecords.outgoing_member with (start := start) (v := source); exact Ha.
Qed.

Local Lemma step_potential s :
  invariant I start s ->
  match Tab.step I (Tab.prepare I start) s with
  | inl next => (potential I H (Tab.prepare I start) next <
      potential I H (Tab.prepare I start) s)%nat
  | inr _ => True
  end.
Proof.
  intros [Hrecords [[Hwf Hqueue] [Hwork Hstored]]]; rewrite Tab.tabulate_equation.
  destruct (Tab.work s) as [|[root v] rest] eqn:Hlist; [exact Logic.I|].
  set (popped := Tab.State (Tab.jumps s) (Tab.callers s) (Tab.ends s) rest
    (FinSet.remove (Jump.enc I) (root, v) (Tab.pending s))).
  assert (Hpopped : invariant I start popped).
  { split; [apply TabRecords.rebuild_valid; exact Hrecords|]; split.
    - split; [exact Hwf|apply TabQueue.pop_coherent; assumption].
    - split; [|exact Hstored]; intros key Hkey; apply Hwork; right; exact Hkey. }
  assert (Hroot : In root (TabPaths.roots I start)).
  { apply (TabRecords.inventory_root I start (root, v)), Hwork; left; reflexivity. }
  pose proof (proj2 (outgoing_progress root v popped Hpopped Hroot)) as Hprogress.
  unfold popped in *; unfold potential in *; cbn [Tab.jumps Tab.work] in Hprogress.
  rewrite Hlist; cbn [length]; lia.
Qed.

Local Lemma initial_potential :
  (potential I H (Tab.prepare I start) (Tab.initial I (Tab.prepare I start)) <=
    (1 + bound H) * length (Tab.inventory (Tab.prepare I start)))%nat.
Proof.
  pose proof initial_invariant as Hinv.
  destruct Hinv as [Hrecords [[Hwf [Hset [Hnodup Hpending]]] [Hwork Hstored]]].
  pose proof (remaining_bound I H (Tab.prepare I start)
    (Tab.jumps (Tab.initial I (Tab.prepare I start)))) as Hremaining.
  assert (Hlength : (length (Tab.work (Tab.initial I (Tab.prepare I start))) <=
    length (Tab.inventory (Tab.prepare I start)))%nat).
  { apply NoDup_incl_length; [exact Hnodup|exact Hwork]. }
  unfold potential; nia.
Qed.

Local Lemma runs_bound n s result :
  runs (Tab.step_c I (Tab.prepare I start)) n s result -> invariant I start s ->
  match result with
  | inl _ => (n <= potential I H (Tab.prepare I start) s)%nat
  | inr _ => True
  end.
Proof.
  intro Hrun; induction Hrun as [s|n s r Hstop|n s next result Hnext Hrun IH]; intro Hinv.
  - lia.
  - exact Logic.I.
  - pose proof (step_invariant s Hinv) as Hvalid.
    pose proof (step_potential s Hinv) as Hdecrease.
    rewrite Tab.step_c_value in Hnext; rewrite Hnext in Hvalid, Hdecrease.
    specialize (IH Hvalid); destruct result; [lia|exact Logic.I].
Qed.

(** Actual symbolic jump tabulation stops within its full prepared-inventory rank budget. *)
Theorem raw_stops fuel :
  ((1 + bound H) * length (Tab.inventory (Tab.prepare I start)) < Pos.to_nat fuel)%nat ->
  exists stopped, Tab.raw I start fuel = inr stopped /\ Tab.work stopped = [].
Proof.
  intro Hfuel; rewrite Tab.raw_equation.
  destruct (Cost.value (iterate (Tab.step_c I (Tab.prepare I start)) fuel
    (Tab.initial I (Tab.prepare I start)))) as [exhausted|stopped] eqn:Hresult.
  - pose proof (iterate_value (Tab.step_c I (Tab.prepare I start)) fuel
      (Tab.initial I (Tab.prepare I start))) as Hrun; rewrite Hresult in Hrun.
    pose proof (runs_bound _ _ _ Hrun initial_invariant) as Hbound.
    assert (Hcount : (Pos.to_nat fuel <=
      potential I H (Tab.prepare I start) (Tab.initial I (Tab.prepare I start)))%nat)
      by exact Hbound.
    pose proof initial_potential as Hinitial; lia.
  - exists stopped; split; [reflexivity|].
    destruct (iterate_inr_stops (Tab.step_c I (Tab.prepare I start)) fuel
      (Tab.initial I (Tab.prepare I start)) stopped Hresult) as
      [used [last [Hused [Hprefix Hstop]]]].
    rewrite Tab.step_c_value, Tab.tabulate_equation in Hstop.
    destruct (Tab.work last) as [|key rest] eqn:Hwork; [|destruct key; discriminate].
    injection Hstop as Hsame; subst stopped; exact Hwork.
Qed.

End Height.

End Run.

(** Global finite symbolic height supplies data for a charged constructed-budget jump run. *)
Definition complete_raw_c {N E P D A F} (I : Ide.t N E P D A F) start
    (H : height (Micro.lat (Ide.micro I))) :=
  let* p := Tab.prepare_c I start in
  let* fuel := TabCost.rank_fuel_c p (bound H) in
  let* s := Tab.initial_c I p in
  iterate (Tab.step_c I p) fuel s.

Definition complete_raw {N E P D A F} (I : Ide.t N E P D A F) start
    (H : height (Micro.lat (Ide.micro I))) :=
  Cost.value (complete_raw_c I start H).

(** Constructed-height execution agrees with the same raw jump engine at its actual numeric budget. *)
Theorem complete_raw_equation {N E P D A F} (I : Ide.t N E P D A F) start
    (H : height (Micro.lat (Ide.micro I))) :
  complete_raw I start H =
    Tab.raw I start (TabCost.rank_fuel (Tab.prepare I start) (bound H)).
Proof.
  rewrite Tab.raw_equation; unfold complete_raw, complete_raw_c.
  autorewrite with galois_cost; reflexivity.
Qed.

(** The actual finite-height jump run reaches stopping without caller-supplied fuel or result premises. *)
Theorem complete_raw_stops {N E P D A F} (I : Ide.t N E P D A F) start
    (H : height (Micro.lat (Ide.micro I))) :
  encoding_laws (IdeValue.key_enc I) -> encoding_laws (Jump.enc I) ->
  lattice_laws (Micro.lat (Ide.micro I)) ->
  exists stopped, complete_raw I start H = inr stopped /\ Tab.work stopped = [].
Proof.
  intros HV HK HL; rewrite complete_raw_equation.
  apply (raw_stops I start HV HK H HL).
  rewrite TabCost.rank_fuel_numeric; lia.
Qed.

(** Constructive jump execution charges all preparation, numeric construction, initialization and work. *)
Theorem complete_raw_cost_equation {N E P D A F} (I : Ide.t N E P D A F) start
    (H : height (Micro.lat (Ide.micro I))) :
  Cost.ticks (complete_raw_c I start H) =
    let p := Tab.prepare I start in
    let fuel := TabCost.rank_fuel p (bound H) in
    (Cost.ticks (Tab.prepare_c I start) + Cost.ticks (TabCost.rank_fuel_c p (bound H)) +
      Cost.ticks (Tab.initial_c I p) +
      Cost.ticks (iterate (Tab.step_c I p) fuel (Tab.initial I p)))%N.
Proof.
  unfold complete_raw_c; autorewrite with galois_cost; cbn zeta.
  fold (Tab.prepare I start).
  fold (TabCost.rank_fuel (Tab.prepare I start) (bound H)).
  fold (Tab.initial I (Tab.prepare I start)); lia.
Qed.

(** The finite-height jump wrapper checks its actual candidate and retains rejection explicitly. *)
Definition complete_c {N E P D A F} (I : Ide.t N E P D A F) start
    (H : height (Micro.lat (Ide.micro I))) :=
  let* result := complete_raw_c I start H in
  match result with
  | inl s => Cost.ret (Tab.Exhausted s)
  | inr s => Tab.certify_c I start s
  end.

Definition complete {N E P D A F} (I : Ide.t N E P D A F) start
    (H : height (Micro.lat (Ide.micro I))) :=
  Cost.value (complete_c I start H).

(** The finite-height wrapper returns the actual raw execution's checked outcome. *)
Theorem complete_equation {N E P D A F} (I : Ide.t N E P D A F) start
    (H : height (Micro.lat (Ide.micro I))) :
  complete I start H =
    match complete_raw I start H with
    | inl s => Tab.Exhausted s
    | inr s => Cost.value (Tab.certify_c I start s)
    end.
Proof.
  unfold complete, complete_c; autorewrite with galois_cost.
  fold (complete_raw I start H); destruct (complete_raw I start H); reflexivity.
Qed.

(** Numeric completion retains exactly the raw engine's constructed-budget certificate and failures. *)
Theorem complete_agrees {N E P D A F} (I : Ide.t N E P D A F) start
    (H : height (Micro.lat (Ide.micro I))) :
  complete I start H = Tab.tabulate I start (TabCost.rank_fuel (Tab.prepare I start) (bound H)).
Proof.
  rewrite complete_equation, complete_raw_equation, Tab.outcome_equation; reflexivity.
Qed.

(** Finite-height jump completion retains the complete reached ground-checker cost. *)
Theorem complete_cost_equation {N E P D A F} (I : Ide.t N E P D A F) start
    (H : height (Micro.lat (Ide.micro I))) :
  Cost.ticks (complete_c I start H) =
    (Cost.ticks (complete_raw_c I start H) +
      match complete_raw I start H with
      | inl _ => 0
      | inr s => Cost.ticks (check_jumps_c I start (Tab.jumps s))
      end)%N.
Proof.
  unfold complete_c; rewrite Cost.ticks_bind; fold (complete_raw I start H).
  destruct (complete_raw I start H); rewrite ?Cost.ticks_ret, ?Tab.certify_cost_equation;
    reflexivity.
Qed.

(** Numeric exhaustion is impossible for the actual finite-height jump wrapper on lawful inputs. *)
Theorem complete_not_exhausted {N E P D A F} (I : Ide.t N E P D A F) start
    (H : height (Micro.lat (Ide.micro I))) :
  encoding_laws (IdeValue.key_enc I) -> encoding_laws (Jump.enc I) ->
  lattice_laws (Micro.lat (Ide.micro I)) ->
  forall s, complete I start H <> Tab.Exhausted s.
Proof.
  intros HV HK HL s.
  destruct (complete_raw_stops I start H HV HK HL) as [stopped [Hrun Hempty]].
  rewrite complete_equation, Hrun; apply Tab.certify_not_exhausted.
Qed.

End TabJumpProgress.
