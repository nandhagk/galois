(** * Structured source machines

    A one-level syntax view lowers a continuation machine to a skeleton.
    For example, a source loop lowers to a block containing a repeating loop.
    Builds on: ProgramSkeletonMachine and ProgramSimulation. *)

From Stdlib Require Import List Bool Arith Lia.
From Galois.Program Require Import ProgramSemantics ProgramSimulation
  ProgramSkeleton ProgramSkeletonMachine.
Import List.ListNotations.

(** A source view exposes atoms, binary control and paired loop labels. *)
Inductive Shape (L A G : Type) :=
  | ShAtom (a : A)
  | ShSeq (left right : L)
  | ShIf (guard : G) (left right : L)
  | ShLoop (body : L)
  | ShBreak (depth : nat)
  | ShContinue (depth : nat).
Arguments ShAtom {L A G}.
Arguments ShSeq {L A G}.
Arguments ShIf {L A G}.
Arguments ShLoop {L A G}.
Arguments ShBreak {L A G}.
Arguments ShContinue {L A G}.

Module Shape.

(** Paired labels distinguish source break and continue destinations. *)
Definition lower_one {L A G} (lower : L -> Skeleton.stmt A G) (s : Shape L A G) :=
  match s with
  | ShAtom a => Skeleton.Atom a
  | ShSeq a b => Skeleton.Seq (lower a) (lower b)
  | ShIf g a b => Skeleton.If g (lower a) (lower b)
  | ShLoop a => Skeleton.Block (Skeleton.Loop (lower a))
  | ShBreak n => Skeleton.Jump (2 * n + 1)
  | ShContinue n => Skeleton.Jump (2 * n)
  end.

End Shape.

Module Lowering.

(** Source syntax readers and their lowering carry no semantic laws. *)
Record t (L A G : Type) := Make {
  shape : L -> Shape L A G;
  lower : L -> Skeleton.stmt A G
}.
Arguments Make {L A G}.
Arguments shape {L A G}.
Arguments lower {L A G}.

End Lowering.

(** A lowering commutes with each one-level source view. *)
Record lowering_laws {L A G} (lw : Lowering.t L A G) : Prop := {
  lower_shape : forall s,
    Lowering.lower lw s = Shape.lower_one (Lowering.lower lw) (Lowering.shape lw s)
}.
Arguments lower_shape {L A G lw}.

(** A source statement is label-correct at its current loop depth. *)
Inductive source_labels {L A G} (lw : Lowering.t L A G) : nat -> L -> Prop :=
  | labels_atom : forall d s a, Lowering.shape lw s = ShAtom a -> source_labels lw d s
  | labels_seq : forall d s a b, Lowering.shape lw s = ShSeq a b ->
      source_labels lw d a -> source_labels lw d b -> source_labels lw d s
  | labels_if : forall d s g a b, Lowering.shape lw s = ShIf g a b ->
      source_labels lw d a -> source_labels lw d b -> source_labels lw d s
  | labels_loop : forall d s a, Lowering.shape lw s = ShLoop a ->
      source_labels lw (S d) a -> source_labels lw d s
  | labels_break : forall d s n, Lowering.shape lw s = ShBreak n ->
      n < d -> source_labels lw d s
  | labels_continue : forall d s n, Lowering.shape lw s = ShContinue n ->
      n < d -> source_labels lw d s.

(** Source label correctness decomposes into the obligations of its one-level shape. *)
Theorem lowering_labels_shape {L A G} (lw : Lowering.t L A G) d s :
  source_labels lw d s <->
  match Lowering.shape lw s with
  | ShAtom _ => True
  | ShSeq a b | ShIf _ a b => source_labels lw d a /\ source_labels lw d b
  | ShLoop a => source_labels lw (S d) a
  | ShBreak n | ShContinue n => n < d
  end.
Proof.
  split.
  - intro Hlabels; destruct Hlabels; rewrite H; tauto.
  - destruct (Lowering.shape lw s) as [a|a b|g a b|body|n|n] eqn:Hshape;
      intro Hlabels.
    + eapply labels_atom; exact Hshape.
    + destruct Hlabels as [Ha Hb]; eapply labels_seq; eassumption.
    + destruct Hlabels as [Ha Hb]; eapply labels_if; eassumption.
    + eapply labels_loop; eassumption.
    + eapply labels_break; eassumption.
    + eapply labels_continue; eassumption.
Qed.

(** Source label correctness establishes the skeleton's boolean label check. *)
Theorem lowering_labels_ok {L A G} (lw : Lowering.t L A G) :
  lowering_laws lw -> forall d s, source_labels lw d s ->
    labels_ok (2 * d) (Lowering.lower lw s) = true.
Proof.
  intros Hlw d s Hlabels; induction Hlabels;
    rewrite (lower_shape Hlw), H; cbn [Shape.lower_one labels_ok].
  - reflexivity.
  - rewrite IHHlabels1, IHHlabels2; reflexivity.
  - rewrite IHHlabels1, IHHlabels2; reflexivity.
  - replace (S (S (2 * d))) with (2 * S d) by lia; exact IHHlabels.
  - apply Nat.ltb_lt; lia.
  - apply Nat.ltb_lt; lia.
Qed.

(** Source continuations retain sequencing, joins and the two loop labels. *)
Inductive source_frame (L : Type) :=
  | KSeq (s : L)
  | KJoin
  | KLoop (body : L)
  | KExit.
Arguments KSeq {L}.
Arguments KJoin {L}.
Arguments KLoop {L}.
Arguments KExit {L}.

(** Source configurations distinguish source entry, inner loop entry and return. *)
Inductive config (L St : Type) :=
  | Run (s : L) (k : list (source_frame L)) (st : St)
  | Enter (body : L) (k : list (source_frame L)) (st : St)
  | Fin (k : list (source_frame L)) (st : St).
Arguments Run {L St}.
Arguments Enter {L St}.
Arguments Fin {L St}.

Inductive source_target (L : Type) :=
  | JRun (s : L) (k : list (source_frame L))
  | JFin (k : list (source_frame L)).
Arguments JRun {L}.
Arguments JFin {L}.

(** Relative source jumps count loop and exit labels and skip administrative frames. *)
Fixpoint jump_cont {L} (n : nat) (k : list (source_frame L)) :=
  match k with
  | [] => None
  | KSeq _ :: k | KJoin :: k => jump_cont n k
  | KLoop s :: k =>
    match n with
    | 0 => Some (JRun s (KLoop s :: k))
    | S n => jump_cont n k
    end
  | KExit :: k =>
    match n with
    | 0 => Some (JFin k)
    | S n => jump_cont n k
    end
  end.

(** Source control is independent of skeleton positions and preserves the store on jumps. *)
Inductive source_step {L A G St O} (lw : Lowering.t L A G)
    (C : skeleton_client A G St O) : config L St -> list O -> config L St -> Prop :=
  | source_atom : forall s a k st l st', Lowering.shape lw s = ShAtom a ->
      atom_step C a st l st' -> source_step lw C (Run s k st) l (Fin k st')
  | source_seq : forall s a b k st, Lowering.shape lw s = ShSeq a b ->
      source_step lw C (Run s k st) [] (Run a (KSeq b :: k) st)
  | source_if : forall s g a b k st choice, Lowering.shape lw s = ShIf g a b ->
      guard_bool C g st = Some choice ->
      source_step lw C (Run s k st) [] (Run (if choice then a else b) (KJoin :: k) st)
  | source_loop : forall s body k st, Lowering.shape lw s = ShLoop body ->
      source_step lw C (Run s k st) [] (Enter body (KExit :: k) st)
  | source_enter : forall body k st,
      source_step lw C (Enter body k st) [] (Run body (KLoop body :: k) st)
  | source_break : forall s n k k' st, Lowering.shape lw s = ShBreak n ->
      jump_cont (2 * n + 1) k = Some (JFin k') ->
      source_step lw C (Run s k st) [] (Fin k' st)
  | source_continue : forall s n k body k' st, Lowering.shape lw s = ShContinue n ->
      jump_cont (2 * n) k = Some (JRun body k') ->
      source_step lw C (Run s k st) [] (Run body k' st)
  | source_ret_seq : forall s k st,
      source_step lw C (Fin (KSeq s :: k) st) [] (Run s (KJoin :: k) st)
  | source_ret_join : forall k st, source_step lw C (Fin (KJoin :: k) st) [] (Fin k st)
  | source_ret_exit : forall k st, source_step lw C (Fin (KExit :: k) st) [] (Fin k st)
  | source_ret_loop : forall s k st,
      source_step lw C (Fin (KLoop s :: k) st) [] (Run s (KLoop s :: k) st).

(** The source starts at the whole program and shares the client's initial stores. *)
Definition source_machine {L A G St O} (lw : Lowering.t L A G)
    (C : skeleton_client A G St O) (prog : L) : semantics (config L St) O :=
  Semantics (fun c => exists st, c = Run prog [] st /\ init_store C st) (source_step lw C).

(** Source endings retain client atom failures and partial-guard traps. *)
Definition source_endings {L A G St O} (lw : Lowering.t L A G)
    (C : skeleton_client A G St O) : endings (config L St) :=
  Endings
    (fun c => match c with Fin [] _ => True | _ => False end)
    (fun c =>
      match c with
      | Run s _ st =>
        match Lowering.shape lw s with
        | ShAtom a => atom_trap C a st
        | ShIf g _ _ => guard_bool C g st = None
        | _ => False
        end
      | _ => False
      end)
    (fun c =>
      match c with
      | Run s _ st =>
        match Lowering.shape lw s with
        | ShAtom a => atom_stop C a st
        | _ => False
        end
      | _ => False
      end).

(** A source occurrence matches both continuations at its lowered position. *)
Inductive source_context {L A G} (lw : Lowering.t L A G) (prog : L) :
    L -> position -> list (source_frame L) -> list frame -> Prop :=
  | sc_root : source_context lw prog prog [] [] []
  | sc_seq_first : forall s a b p k fs, source_context lw prog s p k fs ->
      Lowering.shape lw s = ShSeq a b ->
      source_context lw prog a (p ++ [DFirst]) (KSeq b :: k) (FSeq p :: fs)
  | sc_seq_second : forall s a b p k fs, source_context lw prog s p k fs ->
      Lowering.shape lw s = ShSeq a b ->
      source_context lw prog b (p ++ [DSecond]) (KJoin :: k) (FJoin p :: fs)
  | sc_if_first : forall s g a b p k fs, source_context lw prog s p k fs ->
      Lowering.shape lw s = ShIf g a b ->
      source_context lw prog a (p ++ [DFirst]) (KJoin :: k) (FJoin p :: fs)
  | sc_if_second : forall s g a b p k fs, source_context lw prog s p k fs ->
      Lowering.shape lw s = ShIf g a b ->
      source_context lw prog b (p ++ [DSecond]) (KJoin :: k) (FJoin p :: fs)
  | sc_loop_body : forall s body p k fs, source_context lw prog s p k fs ->
      Lowering.shape lw s = ShLoop body ->
      source_context lw prog body ((p ++ [DBody]) ++ [DBody])
        (KLoop body :: KExit :: k) (FLoop (p ++ [DBody]) :: FBlock p :: fs).

(** Source context lookup finds exactly the lowered source subtree. *)
Theorem source_context_sub {L A G} (lw : Lowering.t L A G) prog s p k fs :
  lowering_laws lw -> source_context lw prog s p k fs ->
    sub (Lowering.lower lw prog) p = Some (Lowering.lower lw s).
Proof.
  intros Hlw Hctx; induction Hctx; [reflexivity| | | | |].
  all: rewrite !sub_app, IHHctx, (lower_shape Hlw), H;
    cbn [Shape.lower_one sub child]; reflexivity.
Qed.

(** Even depths resume the same loop body in both machines, including invalid depths. *)
Theorem continue_match {L A G St} (lw : Lowering.t L A G) prog s p k fs :
  source_context lw prog s p k fs -> forall n (st : St),
  (jump_cont (2 * n) k = None /\ resume (2 * n) fs st = None) \/
  exists body k' q fs', jump_cont (2 * n) k = Some (JRun body k') /\
    resume (2 * n) fs st = Some (Go q fs' st) /\
    source_context lw prog body q k' fs'.
Proof.
  intro Hctx; induction Hctx; intros n st; try exact (IHHctx n st).
  - left; split; reflexivity.
  - destruct n as [|n].
    + right; eexists; eexists; eexists; eexists; split; [reflexivity|].
      split; [reflexivity|eapply sc_loop_body; eassumption].
    + replace (2 * S n) with (S (S (2 * n))) by lia; exact (IHHctx n st).
Qed.

(** Odd depths leave the same loop in both machines, including invalid depths. *)
Theorem break_match {L A G St} (lw : Lowering.t L A G) prog s p k fs :
  source_context lw prog s p k fs -> forall n (st : St),
  (jump_cont (2 * n + 1) k = None /\ resume (2 * n + 1) fs st = None) \/
  exists owner body k' q fs', Lowering.shape lw owner = ShLoop body /\
    jump_cont (2 * n + 1) k = Some (JFin k') /\
    resume (2 * n + 1) fs st = Some (Ret q fs' st) /\
    source_context lw prog owner q k' fs'.
Proof.
  intro Hctx; induction Hctx; intros n st; try exact (IHHctx n st).
  - left; split; reflexivity.
  - destruct n as [|n].
    + right; eexists; eexists; eexists; eexists; eexists; split; [eassumption|].
      split; [reflexivity|]; split; [reflexivity|exact Hctx].
    + replace (2 * S n + 1) with (S (S (2 * n + 1))) by lia; exact (IHHctx n st).
Qed.

(** Matching states share their store and the exact source occurrence and continuation. *)
Inductive match_state {L A G St} (lw : Lowering.t L A G) (prog : L) :
    config L St -> mstate St -> Prop :=
  | match_run : forall s p k fs st, source_context lw prog s p k fs ->
      match_state lw prog (Run s k st) (Go p fs st)
  | match_enter : forall owner body p k fs st, source_context lw prog owner p k fs ->
      Lowering.shape lw owner = ShLoop body ->
      match_state lw prog (Enter body (KExit :: k) st)
        (Go (p ++ [DBody]) (FBlock p :: fs) st)
  | match_fin : forall s p k fs st, source_context lw prog s p k fs ->
      match_state lw prog (Fin k st) (Ret p fs st).

(** Initial source states match initial skeleton states. *)
Theorem match_state_initial {L A G St O} (lw : Lowering.t L A G)
    (C : skeleton_client A G St O) prog c :
  initial (source_machine lw C prog) c ->
  exists m, initial (skeleton_machine C (Lowering.lower lw prog)) m /\ match_state lw prog c m.
Proof.
  intros [st [-> Hinit]]; exists (Go [] [] st); split.
  - exists st; split; [reflexivity|exact Hinit].
  - apply match_run, sc_root.
Qed.

(** The source's store-preserving jumps require the legacy identity jump effect. *)
Definition source_jump_laws {A G St O} (C : skeleton_client A G St O) : Prop :=
  forall p n st st', jump_effect C p n st st' <-> st' = st.

Section Matching.

Context {L A G St O : Type} (lw : Lowering.t L A G) (C : skeleton_client A G St O)
  (prog : L) (Hlw : lowering_laws lw) (Hjump : source_jump_laws C).

Local Lemma run_forth s p k fs st l c' :
  source_context lw prog s p k fs -> source_step lw C (Run s k st) l c' ->
  exists m', skel_step (Lowering.lower lw prog) C (Go p fs st) l m' /\
    match_state lw prog c' m'.
Proof.
  intros Hctx Hstep; pose proof (source_context_sub lw prog s p k fs Hlw Hctx) as Hsub.
  inversion Hstep as
    [s0 a k0 st0 l0 st' Hshape Hatom
    |s0 a b k0 st0 Hshape
    |s0 g a b k0 st0 choice Hshape Hguard
    |s0 body k0 st0 Hshape
    |body k0 st0
    |s0 n k0 kt st0 Hshape Hcont
    |s0 n k0 body kt st0 Hshape Hcont
    |a k0 st0|k0 st0|k0 st0|a k0 st0]; subst.
  - eexists; split.
    + eapply step_atom; [rewrite Hsub, (lower_shape Hlw), Hshape; reflexivity|eassumption].
    + eapply match_fin; exact Hctx.
  - eexists; split.
    + eapply step_seq; rewrite Hsub, (lower_shape Hlw), Hshape; reflexivity.
    + apply match_run; eapply sc_seq_first; eassumption.
  - eexists; split.
    + eapply step_if; [rewrite Hsub, (lower_shape Hlw), Hshape; reflexivity|eassumption].
    + destruct choice; apply match_run; [eapply sc_if_first|eapply sc_if_second]; eassumption.
  - eexists; split.
    + eapply step_block; rewrite Hsub, (lower_shape Hlw), Hshape; reflexivity.
    + eapply match_enter; eassumption.
  - match goal with Hj : jump_cont _ _ = Some _ |- _ => rename Hj into Hsource end.
    destruct (break_match lw prog s p k fs Hctx n st) as
      [[Hnone _]|[owner [body [k' [q [fs' [Howner [Hcont [Hresume Htarget]]]]]]]]];
      [congruence|].
    rewrite Hcont in Hsource; inversion Hsource; subst.
    eexists; split.
    + eapply step_jump; [rewrite Hsub, (lower_shape Hlw), Hshape; reflexivity| |exact Hresume].
      apply Hjump; reflexivity.
    + eapply match_fin; exact Htarget.
  - match goal with Hj : jump_cont _ _ = Some _ |- _ => rename Hj into Hsource end.
    destruct (continue_match lw prog s p k fs Hctx n st) as
      [[Hnone _]|[body' [kt' [q [fs' [Hcont [Hresume Htarget]]]]]]]; [congruence|].
    rewrite Hcont in Hsource; inversion Hsource; subst.
    eexists; split.
    + eapply step_jump; [rewrite Hsub, (lower_shape Hlw), Hshape; reflexivity| |exact Hresume].
      apply Hjump; reflexivity.
    + apply match_run; exact Htarget.
Qed.

Local Lemma match_forth c m l c' :
  match_state lw prog c m -> source_step lw C c l c' ->
  exists m', skel_step (Lowering.lower lw prog) C m l m' /\ match_state lw prog c' m'.
Proof.
  intros Hmatch Hstep; destruct Hmatch as
    [s p k fs st Hctx|owner body p k fs st Hctx Hshape|s p k fs st Hctx].
  - eapply run_forth; eassumption.
  - inversion Hstep; subst; eexists; split.
    + eapply step_loop.
      rewrite sub_app, (source_context_sub lw prog owner p k fs Hlw Hctx),
        (lower_shape Hlw), Hshape; reflexivity.
    + apply match_run; eapply sc_loop_body; eassumption.
  - inversion Hstep; subst; inversion Hctx; subst.
    + eexists; split; [apply step_ret_seq|apply match_run; eapply sc_seq_second; eassumption].
    + eexists; split; [apply step_ret_join|eapply match_fin; eassumption].
    + eexists; split; [apply step_ret_join|eapply match_fin; eassumption].
    + eexists; split; [apply step_ret_join|eapply match_fin; eassumption].
    + eexists; split; [apply step_ret_loop|apply match_run; exact Hctx].
Qed.

Local Lemma run_back s p k fs st l m' :
  source_context lw prog s p k fs ->
  skel_step (Lowering.lower lw prog) C (Go p fs st) l m' ->
  exists c', source_step lw C (Run s k st) l c' /\ match_state lw prog c' m'.
Proof.
  intros Hctx Hstep; pose proof (source_context_sub lw prog s p k fs Hlw Hctx) as Hsub.
  rewrite (lower_shape Hlw s) in Hsub.
  destruct (Lowering.shape lw s) as [a|a b|g a b|body|n|n] eqn:Hshape;
    cbn [Shape.lower_one] in Hsub; inversion Hstep; subst; try congruence.
  - assert (a0 = a) by congruence; subst a0.
    eexists; split; [eapply source_atom; eassumption|eapply match_fin; exact Hctx].
  - eexists; split; [eapply source_seq; exact Hshape|].
    apply match_run; eapply sc_seq_first; eassumption.
  - assert (g0 = g) by congruence; subst g0.
    eexists; split; [eapply source_if; eassumption|].
    destruct b0; apply match_run; [eapply sc_if_first|eapply sc_if_second]; eassumption.
  - eexists; split; [eapply source_loop; exact Hshape|eapply match_enter; eassumption].
  - assert (n0 = 2 * n + 1) by congruence; subst n0.
    match goal with Hj : jump_effect _ _ _ _ _ |- _ =>
      apply Hjump in Hj; subst st'
    end.
    match goal with Hj : resume _ _ _ = Some _ |- _ => rename Hj into Hmachine end.
    destruct (break_match lw prog s p k fs Hctx n st) as
      [[_ Hnone]|[owner [body [kt [q [fs' [Howner [Hcont [Hresume Htarget]]]]]]]]];
      [congruence|].
    rewrite Hresume in Hmachine; injection Hmachine as <-.
    eexists; split; [eapply source_break; eassumption|eapply match_fin; exact Htarget].
  - assert (n0 = 2 * n) by congruence; subst n0.
    match goal with Hj : jump_effect _ _ _ _ _ |- _ =>
      apply Hjump in Hj; subst st'
    end.
    match goal with Hj : resume _ _ _ = Some _ |- _ => rename Hj into Hmachine end.
    destruct (continue_match lw prog s p k fs Hctx n st) as
      [[_ Hnone]|[body [kt [q [fs' [Hcont [Hresume Htarget]]]]]]]; [congruence|].
    rewrite Hresume in Hmachine; injection Hmachine as <-.
    eexists; split; [eapply source_continue; eassumption|apply match_run; exact Htarget].
Qed.

Local Lemma match_back c m l m' :
  match_state lw prog c m -> skel_step (Lowering.lower lw prog) C m l m' ->
  exists c', source_step lw C c l c' /\ match_state lw prog c' m'.
Proof.
  intros Hmatch Hstep; destruct Hmatch as
    [s p k fs st Hctx|owner body p k fs st Hctx Hshape|s p k fs st Hctx].
  - eapply run_back; eassumption.
  - pose proof (source_context_sub lw prog owner p k fs Hlw Hctx) as Hsub.
    assert (Hloop : sub (Lowering.lower lw prog) (p ++ [DBody]) =
      Some (Skeleton.Loop (Lowering.lower lw body))).
    { rewrite sub_app, Hsub, (lower_shape Hlw), Hshape; reflexivity. }
    inversion Hstep; subst; try congruence.
    eexists; split; [apply source_enter|apply match_run; eapply sc_loop_body; eassumption].
  - inversion Hctx; subst; inversion Hstep; subst.
    + eexists; split; [apply source_ret_seq|apply match_run; eapply sc_seq_second; eassumption].
    + eexists; split; [apply source_ret_join|eapply match_fin; eassumption].
    + eexists; split; [apply source_ret_join|eapply match_fin; eassumption].
    + eexists; split; [apply source_ret_join|eapply match_fin; eassumption].
    + eexists; split; [apply source_ret_loop|apply match_run; exact Hctx].
Qed.

Local Lemma context_root s p k fs :
  source_context lw prog s p k fs -> (k = [] <-> p = [] /\ fs = []).
Proof.
  intro Hctx; destruct Hctx; cbn; split; intro Hempty; try discriminate.
  all: try (split; reflexivity); try reflexivity.
  all: destruct Hempty as [_ Hempty]; discriminate.
Qed.

Local Lemma match_final c m :
  match_state lw prog c m ->
  (final (source_endings lw C) c <->
    final (skeleton_endings (Lowering.lower lw prog) C) m).
Proof.
  intro Hmatch; destruct Hmatch as
    [s p k fs st Hctx|owner body p k fs st Hctx Hshape|s p k fs st Hctx]; cbn.
  - tauto.
  - tauto.
  - pose proof (context_root s p k fs Hctx) as Hroot.
    split.
    + destruct k; [|contradiction].
      intros _; destruct (proj1 Hroot eq_refl) as [-> ->]; exact I.
    + destruct p as [|d p], fs as [|f fs]; try contradiction.
      intros _; pose proof (proj2 Hroot (conj eq_refl eq_refl)) as ->; exact I.
Qed.

Local Lemma match_failures c m :
  match_state lw prog c m ->
  (trapped (source_endings lw C) c <->
    trapped (skeleton_endings (Lowering.lower lw prog) C) m) /\
  (stopped (source_endings lw C) c <->
    stopped (skeleton_endings (Lowering.lower lw prog) C) m).
Proof.
  intro Hmatch; destruct Hmatch as
    [s p k fs st Hctx|owner body p k fs st Hctx Hshape|s p k fs st Hctx]; cbn.
  - rewrite (source_context_sub lw prog s p k fs Hlw Hctx), (lower_shape Hlw).
    destruct (Lowering.shape lw s); cbn; tauto.
  - rewrite sub_app, (source_context_sub lw prog owner p k fs Hlw Hctx),
      (lower_shape Hlw), Hshape; cbn; tauto.
  - tauto.
Qed.

Local Lemma match_running c m :
  match_state lw prog c m ->
  (running (source_machine lw C prog) c <->
    running (skeleton_machine C (Lowering.lower lw prog)) m).
Proof.
  intro Hmatch; split; intros [l [next Hstep]].
  - destruct (match_forth c m l next Hmatch Hstep) as [next' [Hnext _]].
    exists l, next'; exact Hnext.
  - destruct (match_back c m l next Hmatch Hstep) as [next' [Hnext _]].
    exists l, next'; exact Hnext.
Qed.

(** Structured lowering preserves all steps and ending tags on arbitrary matched states. *)
Theorem source_skeleton_bisimulation :
  bisimulation (source_machine lw C prog) (source_endings lw C)
    (skeleton_machine C (Lowering.lower lw prog))
    (skeleton_endings (Lowering.lower lw prog) C) (match_state lw prog).
Proof.
  constructor.
  - intros c m tag Hmatch.
    pose proof (match_final c m Hmatch) as Hfinal.
    destruct (match_failures c m Hmatch) as [Htrap Hstop].
    pose proof (match_running c m Hmatch) as Hrun.
    destruct tag; cbn [ends_as]; try assumption.
    unfold stuck; tauto.
  - exact match_forth.
  - exact match_back.
Qed.

(** Skeleton behaviour equality transports through the specified source endpoints. *)
Theorem source_behaviour_transport c0 c1 m0 m1 :
  match_state lw prog c0 m0 -> match_state lw prog c1 m1 ->
  same_behaviour (skeleton_machine C (Lowering.lower lw prog))
    (skeleton_endings (Lowering.lower lw prog) C) m0
    (skeleton_machine C (Lowering.lower lw prog))
    (skeleton_endings (Lowering.lower lw prog) C) m1 ->
  same_behaviour (source_machine lw C prog) (source_endings lw C) c0
    (source_machine lw C prog) (source_endings lw C) c1.
Proof.
  eapply behaviour_transport; exact source_skeleton_bisimulation.
Qed.

End Matching.
