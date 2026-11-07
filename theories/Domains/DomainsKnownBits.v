(** * Known bits on the shared word harness

    The dictionary uses charged forward and backward entries with explicit multiplier options.
    For example, selecting MulLow retains the classic trailing-zero product rule.
    Builds on: DomainsTransfer, DomainsKnownBitsForward and DomainsKnownBitsBack. *)

From Stdlib Require Import ZArith List Bool Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Lattice Require Import LatticeCore LatticeHeight.
From Galois.Bits Require Import BitsWord BitsFun BitsOp.
From Galois.Domains Require Import DomainsNumeric DomainsTransfer DomainsTnum DomainsTnumRank
  DomainsTnumMul DomainsKnownBitsForward DomainsKnownBitsBack.
Import List.ListNotations Cost.Notations.

Local Open Scope Z_scope.

(** The arity scan charges arbitrary input lists before bounded primitive evaluation. *)
Definition known_bits_eval_c (o : op) (xs : list word) : Cost.t (option word) :=
  let* n := length_c xs in
  if Nat.eqb n (arity o) then Cost.step ;; Cost.ret (eval_op o xs) else Cost.ret None.

(** Guarding evaluation by generated arity preserves every result and every rejection. *)
Theorem known_bits_eval_equation : forall o xs,
  Cost.value (known_bits_eval_c o xs) = eval_op o xs.
Proof.
  intros o xs. unfold known_bits_eval_c. autorewrite with galois_cost.
  destruct (Nat.eqb (length xs) (arity o)) eqn:Harity;
    autorewrite with galois_cost; [reflexivity|].
  destruct (eval_op o xs) as [c|] eqn:Heval; [|reflexivity].
  apply Nat.eqb_neq in Harity. exfalso. apply Harity. now apply (eval_op_arity o xs c).
Qed.

(** Successful generated arity checks bound primitive evaluation to at most three operands. *)
Theorem known_bits_eval_primitive_bound : forall o (xs : list word),
  Nat.eqb (length xs) (arity o) = true -> (length xs <= 3)%nat.
Proof.
  intros o xs Hlength. apply Nat.eqb_eq in Hlength. rewrite Hlength.
  destruct o; repeat constructor.
Qed.

Definition tnum_assume_entry_c (o : op) (rw : width) (q : tnum)
    (xs : list (width * tnum)) : Cost.t (list tnum) :=
  let* qs := tnum_backward_raw_c o xs rw q in
  tnum_refine_c xs qs.

(** Lookup uses the single Bits arity table and retains the chosen entry's full callee cost. *)
Definition known_bits_table (opts : known_bits_options)
    : Transfer.table (width * tnum) tnum op width :=
  {| Transfer.fwd := fun o n => Cost.ret
       (if Nat.eqb n (arity o)
        then Some (fun rw xs => tnum_forward_raw_c opts o xs rw) else None);
     Transfer.bwd := fun o n => Cost.ret
       (if Nat.eqb n (arity o) then Some (tnum_assume_entry_c o) else None) |}.

(** Singleton recognition is deliberately disabled to preserve the legacy count/division precision.
    Empty tests, arity dispatch and backward traversal still use the shared harness. *)
Definition known_bits_shape : Transfer.shape (width * tnum) tnum op width word :=
  {| Transfer.eval_c := known_bits_eval_c;
     Transfer.point_c := fun _ => Cost.ret None;
     Transfer.is_empty_c := fun wp => Cost.step ;;
       Cost.ret (tnum_empty (fst wp) (snd wp));
     Transfer.inj_c := fun rw c => Cost.step ;; Cost.ret (tnum_const rw (snd c));
     Transfer.bot_out := fun w => bot (tnum_lattice w);
     Transfer.top_out := fun _ => tnum_top;
     Transfer.keep_c := fun wp => Cost.step ;;
       Cost.ret (tnum_normalise (fst wp) (snd wp)) |}.

Lemma known_bits_shape_laws :
  transfer_sem known_bits_shape (payload_sound tnum_gamma) (word_output tnum_gamma)
    word_context.
Proof.
  constructor.
  - intros. discriminate.
  - intros [w a] [v z] Hempty [Hwidth [Hz Ha]].
    cbn [fst snd] in Hwidth, Hz, Ha, Hempty. subst v.
    change (tnum_empty w a = true) in Hempty.
    pose proof (tnum_empty_sound w a z Ha). congruence.
  - intros rw [w z] [Hwidth Hword]. cbn [fst snd] in Hwidth, Hword. subst rw.
    change (tnum_gamma w (tnum_const w z) z).
    rewrite <- (wrap_id w z Hword) at 2. apply tnum_const_sound.
  - intros rw [w z] Hg. apply tnum_gamma_bits in Hg. destruct Hg as [Hz Ho].
    pose proof (tnum_all_bits rw 0 ltac:(lia)) as Hbit.
    specialize (Hz 0 ltac:(lia) Hbit). specialize (Ho 0 ltac:(lia) Hbit). congruence.
  - intros. apply tnum_top_sound.
  - intros rw [w a] [v z] [Hwidth [Hz Ha]]. cbn [fst snd] in Hwidth, Ha. subst v.
    apply tnum_normalise_sound. exact Ha.
Qed.

Lemma tnum_refine_word_sound : forall xs cs qs,
  Forall2 (payload_sound tnum_gamma) xs cs ->
  Forall2 (fun wp_y q => tnum_gamma (fst (fst wp_y)) q (snd (snd wp_y)))
    (combine xs cs) qs ->
  Forall2 (word_output tnum_gamma 1%positive) (tnum_refine xs qs) cs.
Proof.
  intros xs cs qs Hpayload. revert qs.
  induction Hpayload as [|[w a] [v z] xs cs Hhead Htail IH]; intros qs Hqs.
  - inversion Hqs; subst. rewrite tnum_refine_equation. constructor.
  - inversion Hqs as [|p q ps qs' Hq Hrest]; subst.
    destruct Hhead as [Hwidth [Hz Ha]]. cbn [fst snd] in Hwidth, Ha, Hq. subst v.
    rewrite tnum_refine_equation. constructor.
    + apply tnum_meet_sound; assumption.
    + now apply IH.
Qed.

(** Every actual forward/backward entry satisfies the landed per-operand-width table laws. *)
Theorem known_bits_table_laws : forall opts,
  table_laws (known_bits_table opts) known_bits_shape (payload_sound tnum_gamma)
    (word_output tnum_gamma) word_context.
Proof.
  intro opts. constructor.
  - intros o n f rw xs cs [w z] Hentry Hlength Hpayload Heval [Hwidth Hword].
    change ((if Nat.eqb n (arity o)
      then Some (fun r ps => tnum_forward_raw_c opts o ps r) else None) = Some f) in Hentry.
    destruct (Nat.eqb n (arity o)); [|discriminate]. injection Hentry as <-.
    cbn [fst snd] in Hwidth. subst rw.
    change (Cost.value (known_bits_eval_c o cs) = Some (w, z)) in Heval.
    rewrite known_bits_eval_equation in Heval.
    exact (tnum_forward_raw_sound opts o xs cs w z Hpayload Heval).
  - intros o n f rw q xs cs [w z] Hentry Hlength Hpayload Heval [Hwidth Hword] Hq.
    change ((if Nat.eqb n (arity o) then Some (tnum_assume_entry_c o) else None) =
      Some f) in Hentry.
    destruct (Nat.eqb n (arity o)); [|discriminate]. injection Hentry as <-.
    cbn [fst snd] in Hwidth. subst rw.
    change (Cost.value (known_bits_eval_c o cs) = Some (w, z)) in Heval.
    rewrite known_bits_eval_equation in Heval.
    change (tnum_gamma w q z) in Hq.
    unfold tnum_assume_entry_c. autorewrite with galois_cost.
    apply (tnum_refine_word_sound xs cs (tnum_backward_raw o xs w q) Hpayload).
    exact (tnum_backward_raw_sound o xs cs w z q Hpayload Heval Hq).
  - intros o n f rw q xs Hentry Hlength.
    change ((if Nat.eqb n (arity o) then Some (tnum_assume_entry_c o) else None) =
      Some f) in Hentry.
    destruct (Nat.eqb n (arity o)); [|discriminate]. injection Hentry as <-.
    unfold tnum_assume_entry_c. autorewrite with galois_cost. apply tnum_refine_length.
Qed.

Lemma known_bits_table_refines : forall opts,
  table_refines (known_bits_table opts) known_bits_shape
    (fun wp q => leb (tnum_lattice (fst wp)) q (snd wp) = true).
Proof.
  intro opts. constructor.
  - intros [w a].
    change (leb (tnum_lattice w) (tnum_normalise w a) a = true).
    apply tnum_leb_bits. split; intros i Hi Hbit;
      cbn [tnum_normalise zeros ones]; rewrite tnum_wrap_bit by exact Hi; exact Hbit.
  - intros o n f rw q xs Hentry Hlength.
    change ((if Nat.eqb n (arity o) then Some (tnum_assume_entry_c o) else None) =
      Some f) in Hentry.
    destruct (Nat.eqb n (arity o)); [|discriminate]. injection Hentry as <-.
    unfold tnum_assume_entry_c. autorewrite with galois_cost. apply tnum_refine_refines.
Qed.

(** The shared word harness supplies empty handling, arity dispatch and reductive backward calls. *)
Definition known_bits_word_builder (opts : known_bits_options) : word_domain tnum :=
  word_of_table (known_bits_table opts) known_bits_shape tnum_lattice (fun _ => tnum_top)
    (fun w z => Cost.step ;; Cost.ret (tnum_const w z))
    (fun w a b => Cost.step ;; Cost.ret (tnum_meet w a b)).

(** Every selected known-bit word dictionary satisfies total soundness and structural refinement. *)
Theorem known_bits_word_builder_laws : forall opts,
  word_laws (known_bits_word_builder opts) tnum_gamma.
Proof.
  intro opts. apply word_of_table_laws.
  - intros. apply known_bits_eval_equation.
  - exact known_bits_shape_laws.
  - apply known_bits_table_laws.
  - apply tnum_laws.
  - apply tnum_gamma_monotone.
  - apply tnum_gamma_bot_empty.
  - intros. apply tnum_top_sound.
  - apply tnum_const_sound.
  - apply known_bits_table_refines.
  - apply tnum_meet_sound.
  - apply tnum_meet_lower_left.
Qed.

(** Nullary malformed calls retain legacy top and every nonempty call uses the shared builder. *)
Definition known_bits_word_domain (opts : known_bits_options) : word_domain tnum :=
  let base := known_bits_word_builder opts in
  {| plat := plat base;
     ptop := ptop base;
     pconst_c := pconst_c base;
     pforward_c := fun o xs rw =>
       match xs with
       | [] => Cost.step ;; Cost.ret tnum_top
       | _ :: _ => pforward_c base o xs rw
       end;
     passume_c := passume_c base;
     pmeet_c := pmeet_c base |}.

(** The compatibility branch cannot hide a concrete result because Bits has no nullary operator. *)
Theorem known_bits_word_laws : forall opts,
  word_laws (known_bits_word_domain opts) tnum_gamma.
Proof.
  intro opts. pose proof (known_bits_word_builder_laws opts) as Hbase. constructor.
  - exact (plat_laws Hbase).
  - exact (pgamma_monotone Hbase).
  - exact (pgamma_bot_empty Hbase).
  - exact (ptop_sound Hbase).
  - exact (pconst_sound Hbase).
  - intros o xs cs rw z Hpayload Heval. destruct xs as [|x xs].
    + inversion Hpayload; subst cs.
      pose proof (eval_op_arity o [] (rw, z) Heval) as Harity. destruct o; discriminate Harity.
    + exact (pforward_sound Hbase o (x :: xs) cs rw z Hpayload Heval).
  - exact (passume_sound Hbase).
  - exact (passume_refines Hbase).
  - exact (pmeet_sound Hbase).
  - exact (pmeet_lower_left Hbase).
Qed.

(** The approved malformed nullary boundary preserves the legacy unrestricted fact. *)
Theorem known_bits_nullary : forall opts o rw,
  pforward (known_bits_word_domain opts) o [] rw = tnum_top.
Proof.
  reflexivity.
Qed.

(** Nonempty calls delegate unchanged, including their complete callee charges. *)
Theorem known_bits_nonempty_delegation : forall opts o x xs rw,
  pforward_c (known_bits_word_domain opts) o (x :: xs) rw =
    pforward_c (known_bits_word_builder opts) o (x :: xs) rw.
Proof.
  reflexivity.
Qed.

(** Multiplier selection leaves every other forward callback and its charge unchanged. *)
Theorem known_bits_nonmultiplication_agrees : forall opts opts' o, o <> bvmul ->
  pforward_c (known_bits_word_domain opts) o =
    pforward_c (known_bits_word_domain opts') o.
Proof.
  intros opts opts' o Hother.
  assert (Hentry : Transfer.fwd (known_bits_table opts) o =
    Transfer.fwd (known_bits_table opts') o).
  { destruct o; try reflexivity. contradiction. }
  unfold known_bits_word_domain, known_bits_word_builder, word_of_table.
  cbn [pforward_c]. unfold Transfer.forward_c, Transfer.dispatch_c. now rewrite Hentry.
Qed.

Definition known_bits_domain : word_domain tnum :=
  known_bits_word_domain known_bits_default_options.

Definition known_bits_classic_domain : word_domain tnum :=
  known_bits_word_domain (KnownBitsOptions MulLow).

Definition known_bits_precise_domain : word_domain tnum := known_bits_domain.
