(** * Signed-bound word dictionaries and observations

    Selected dictionaries share the word harness and queries return exact per-sign component hulls.
    For example, the negative query of the singleton four at width four returns no values.
    Builds on: DomainsSignedBounds. *)

From Stdlib Require Import ZArith List Bool.
From Galois.Cost Require Import CostMonad.
From Galois.Lattice Require Import LatticeCore LatticeHeight.
From Galois.Bits Require Import BitsWord BitsOp.
From Galois.Domains Require Import DomainsNumeric DomainsTagged DomainsTransfer DomainsTnum
  DomainsTnumMul DomainsKnownBitsForward DomainsKnownBits DomainsSignedBounds DomainsSignedOrder
  DomainsSignedWiden DomainsSignedBoundsRange DomainsSignedBoundsCases DomainsSignedBoundsRefine.
Import List.ListNotations Cost.Notations.

Local Open Scope Z_scope.

(** Queries retain the complete cost of reducing their selected hemisphere. *)
Definition signed_bounds_query_c (w : width) (a : signed_bounds) (s : bool)
    : Cost.t (option (tnum * Z * Z)) :=
  let* h := sb_reduce_half_c w s (if s then sb_one a else sb_zero a) in
  Cost.ret
    (match h with
    | SBEmpty => None
    | SBRange t lo hi => Some (t, lo, hi)
    end).

Definition signed_bounds_query (w : width) (a : signed_bounds) (s : bool)
    : option (tnum * Z * Z) :=
  Cost.value (signed_bounds_query_c w a s).

(** The pure observation reads the exact reduced hemisphere. *)
Theorem signed_bounds_query_equation : forall w a s,
  signed_bounds_query w a s =
  match sb_reduce_half w s (if s then sb_one a else sb_zero a) with
  | SBEmpty => None
  | SBRange t lo hi => Some (t, lo, hi)
  end.
Proof.
  intros w a s. unfold signed_bounds_query, signed_bounds_query_c.
  autorewrite with galois_cost. reflexivity.
Qed.

(** Every feasible original word satisfies the queried mask and inclusive endpoints. *)
Theorem signed_bounds_query_sound : forall w a s t lo hi z,
  signed_bounds_query w a s = Some (t, lo, hi) ->
  sb_half_gamma w s (if s then sb_one a else sb_zero a) z ->
  tnum_gamma w t z /\ lo <= z <= hi.
Proof.
  intros w a s t lo hi z Hquery Hz. rewrite signed_bounds_query_equation in Hquery.
  pose proof (proj2 (sb_reduce_half_gamma w s _ z) Hz) as Hreduced.
  destruct (sb_reduce_half w s (if s then sb_one a else sb_zero a)) as [|t' lo' hi'];
    [discriminate|]. injection Hquery as <- <- <-.
  apply sb_half_gamma_range in Hreduced. tauto.
Qed.

(** Query failure is equivalent to emptiness of the original selected hemisphere. *)
Theorem signed_bounds_query_empty : forall w a s,
  signed_bounds_query w a s = None <->
  forall z, ~ sb_half_gamma w s (if s then sb_one a else sb_zero a) z.
Proof.
  intros w a s. rewrite signed_bounds_query_equation.
  pose proof (sb_reduce_half_summary w s (if s then sb_one a else sb_zero a)) as Hsummary.
  destruct (sb_reduce_half w s (if s then sb_one a else sb_zero a)) as [|t lo hi].
  - split; [intro Hquery; exact Hsummary|intro Hempty; reflexivity].
  - split; [discriminate|]. intro Hempty.
    destruct Hsummary as [_ [Hlo _]]. exfalso. exact (Hempty lo Hlo).
Qed.

(** Both reported endpoints are feasible original words in the selected hemisphere. *)
Theorem signed_bounds_query_bounds_exact : forall w a s t lo hi,
  signed_bounds_query w a s = Some (t, lo, hi) ->
  sb_half_gamma w s (if s then sb_one a else sb_zero a) lo /\
  sb_half_gamma w s (if s then sb_one a else sb_zero a) hi.
Proof.
  intros w a s t lo hi Hquery. rewrite signed_bounds_query_equation in Hquery.
  pose proof (sb_reduce_half_summary w s (if s then sb_one a else sb_zero a)) as Hsummary.
  destruct (sb_reduce_half w s (if s then sb_one a else sb_zero a)) as [|t' lo' hi'];
    [discriminate|]. injection Hquery as <- <- <-.
  destruct Hsummary as [_ [Hlo [Hhi _]]]. now split.
Qed.

(** Executable policy data selects staged multiplication and doubling by default. *)
Record signed_bounds_options : Type := SignedBoundsOptions {
  sb_bits_options : known_bits_options;
  sb_widening_choice : sb_widening
}.

Definition signed_bounds_default_options : signed_bounds_options :=
  SignedBoundsOptions known_bits_default_options WidenDouble.

Definition signed_bounds_classic_options : signed_bounds_options :=
  SignedBoundsOptions (KnownBitsOptions MulLow) WidenJoin.

Definition signed_bounds_empty_c (w : width) (a : signed_bounds) : Cost.t bool :=
  let* reduced := signed_bounds_reduce_c w a in
  Cost.ret (sb_is_empty (sb_zero reduced) && sb_is_empty (sb_one reduced)).

Definition signed_bounds_empty (w : width) (a : signed_bounds) : bool :=
  Cost.value (signed_bounds_empty_c w a).

Lemma signed_bounds_empty_sound : forall w a z,
  signed_bounds_gamma w a z -> signed_bounds_empty w a = false.
Proof.
  intros w a z Ha.
  apply (proj2 (signed_bounds_reduce_gamma w a z)) in Ha.
  unfold signed_bounds_empty, signed_bounds_empty_c. autorewrite with galois_cost.
  change (sb_is_empty (sb_zero (signed_bounds_reduce w a)) &&
    sb_is_empty (sb_one (signed_bounds_reduce w a)) = false).
  destruct (signed_bounds_reduce w a) as [[|tz lz uz] [|to lo uo]];
    try reflexivity; destruct Ha as [[Hempty _]|[Hempty _]]; contradiction.
Qed.

(** Shape callbacks keep all normalization costs and use a constant-size canonical top. *)
Definition signed_bounds_shape
    : Transfer.shape (width * signed_bounds) signed_bounds op width word :=
  {| Transfer.eval_c := known_bits_eval_c;
     Transfer.point_c := fun _ => Cost.ret None;
     Transfer.is_empty_c := fun wp => signed_bounds_empty_c (fst wp) (snd wp);
     Transfer.inj_c := fun rw c => signed_bounds_const_c rw (snd c);
     Transfer.bot_out := fun _ => SignedBounds SBEmpty SBEmpty;
     Transfer.top_out := signed_bounds_top;
     Transfer.keep_c := fun wp => signed_bounds_reduce_c (fst wp) (snd wp) |}.

(** Table lookup reuses the generated Bits arity and retains complete entry callback costs. *)
Definition signed_bounds_table (opts : signed_bounds_options)
    : Transfer.table (width * signed_bounds) signed_bounds op width :=
  {| Transfer.fwd := fun o n => Cost.ret
       (if Nat.eqb n (arity o)
        then Some (fun rw xs => signed_bounds_forward_c (sb_bits_options opts) o xs rw)
        else None);
     Transfer.bwd := fun o n => Cost.ret
       (if Nat.eqb n (arity o)
        then Some (fun rw q xs => signed_bounds_assume_c o xs rw q) else None) |}.

Lemma signed_bounds_shape_laws :
  transfer_sem signed_bounds_shape (payload_sound signed_bounds_gamma)
    (word_output signed_bounds_gamma) word_context.
Proof.
  constructor.
  - intros. discriminate.
  - intros [w a] [v z] Hempty [Hwidth [Hz Ha]].
    cbn [fst snd] in Hwidth, Ha. subst v.
    change (signed_bounds_empty w a = true) in Hempty.
    pose proof (signed_bounds_empty_sound w a z Ha). congruence.
  - intros rw [w z] [Hwidth Hword]. cbn [fst snd] in Hwidth, Hword. subst rw.
    change (signed_bounds_gamma w (signed_bounds_const w z) z).
    rewrite <- (wrap_id w z Hword) at 2. apply signed_bounds_const_sound.
  - intros rw [w z] [[Hempty _]|[Hempty _]]; contradiction.
  - intros rw [w z] [Hwidth Hword]. cbn [fst snd] in Hwidth, Hword. subst rw.
    now apply signed_bounds_top_sound.
  - intros rw [w a] [v z] [Hwidth [Hz Ha]]. cbn [fst snd] in Hwidth, Ha. subst v.
    apply signed_bounds_reduce_gamma. exact Ha.
Qed.

Lemma signed_bounds_word_results : forall rw xs cs qs,
  Forall2 (payload_sound signed_bounds_gamma) xs cs ->
  Forall2 (fun p c => signed_bounds_gamma (fst p) (snd p) (snd c))
    (combine (map fst xs) qs) cs ->
  length qs = length xs -> Forall2 (word_output signed_bounds_gamma rw) qs cs.
Proof.
  intros rw xs cs qs Hpayload. revert qs.
  induction Hpayload as [|[w a] [v z] xs cs Hhead Htail IH];
    intros [|q qs] Hqs Hlength; try discriminate; try solve [inversion Hqs].
  - constructor.
  - inversion Hqs as [|p c rest values Hq Hrest]; subst.
    destruct Hhead as [Hwidth [Hz Ha]]. cbn [fst snd] in Hwidth. subst v.
    constructor; [exact Hq|]. apply IH; [exact Hrest|now injection Hlength].
Qed.

(** Every signed-bound entry obeys forward, backward and unconditional backward-length contracts. *)
Theorem signed_bounds_table_laws : forall opts,
  table_laws (signed_bounds_table opts) signed_bounds_shape (payload_sound signed_bounds_gamma)
    (word_output signed_bounds_gamma) word_context.
Proof.
  intro opts. constructor.
  - intros o n f rw xs cs [w z] Hentry Hlength Hpayload Heval [Hwidth Hword].
    change ((if Nat.eqb n (arity o)
      then Some (fun r ps => signed_bounds_forward_c (sb_bits_options opts) o ps r)
      else None) = Some f) in Hentry.
    destruct (Nat.eqb n (arity o)); [|discriminate]. injection Hentry as <-.
    cbn [fst snd] in Hwidth. subst rw.
    change (Cost.value (known_bits_eval_c o cs) = Some (w, z)) in Heval.
    rewrite known_bits_eval_equation in Heval.
    exact (signed_bounds_forward_sound (sb_bits_options opts) o xs cs w z Hpayload Heval).
  - intros o n f rw q xs cs [w z] Hentry Hlength Hpayload Heval [Hwidth Hword] Hq.
    change ((if Nat.eqb n (arity o)
      then Some (fun r a ps => signed_bounds_assume_c o ps r a) else None) = Some f) in Hentry.
    destruct (Nat.eqb n (arity o)); [|discriminate]. injection Hentry as <-.
    cbn [fst snd] in Hwidth. subst rw.
    change (Cost.value (known_bits_eval_c o cs) = Some (w, z)) in Heval.
    rewrite known_bits_eval_equation in Heval. change (signed_bounds_gamma w q z) in Hq.
    apply (signed_bounds_word_results w xs cs (signed_bounds_assume o xs w q) Hpayload).
    + exact (signed_bounds_assume_sound o xs cs w z q Hpayload Heval Hq).
    + apply signed_bounds_assume_length.
  - intros o n f rw q xs Hentry Hlength.
    change ((if Nat.eqb n (arity o)
      then Some (fun r a ps => signed_bounds_assume_c o ps r a) else None) = Some f) in Hentry.
    destruct (Nat.eqb n (arity o)); [|discriminate]. injection Hentry as <-.
    apply signed_bounds_assume_length.
Qed.

Lemma signed_bounds_table_refines : forall opts,
  table_refines (signed_bounds_table opts) signed_bounds_shape
    (fun wp q => signed_bounds_leb (fst wp) q (snd wp) = true).
Proof.
  intro opts. constructor.
  - intros [w a]. apply signed_bounds_leb_spec. intros z Hz.
    change (signed_bounds_gamma w (signed_bounds_reduce w a) z) in Hz.
    now rewrite signed_bounds_reduce_gamma in Hz.
  - intros o n f rw q xs Hentry Hlength.
    change ((if Nat.eqb n (arity o)
      then Some (fun r a ps => signed_bounds_assume_c o ps r a) else None) = Some f) in Hentry.
    destruct (Nat.eqb n (arity o)); [|discriminate]. injection Hentry as <-.
    apply signed_bounds_assume_refines.
Qed.

(** The selected signed-bound word dictionary runs through the actual shared transfer harness. *)
Definition signed_bounds_word_builder (opts : signed_bounds_options) : word_domain signed_bounds :=
  word_of_table (signed_bounds_table opts) signed_bounds_shape
    (signed_bounds_lattice (sb_widening_choice opts)) signed_bounds_top
    signed_bounds_const_c signed_bounds_meet_c.

(** Every selected signed-bound dictionary satisfies word soundness and backward refinement. *)
Theorem signed_bounds_word_builder_laws : forall opts,
  word_laws (signed_bounds_word_builder opts) signed_bounds_gamma.
Proof.
  intro opts. apply word_of_table_laws.
  - intros. apply known_bits_eval_equation.
  - exact signed_bounds_shape_laws.
  - apply signed_bounds_table_laws.
  - apply signed_bounds_laws.
  - intros w a b z Hle Hz.
    change (signed_bounds_leb w a b = true) in Hle.
    exact (proj1 (signed_bounds_leb_spec w a b) Hle z Hz).
  - intros w z [[Hempty _]|[Hempty _]]; contradiction.
  - apply signed_bounds_top_sound.
  - apply signed_bounds_const_sound.
  - apply signed_bounds_table_refines.
  - intros w a b z Ha Hb. apply signed_bounds_meet_gamma. now split.
  - intros w a b. apply signed_bounds_leb_spec. intros z Hz.
    apply signed_bounds_meet_gamma in Hz. tauto.
Qed.

(** The nullary legacy-top boundary is the only exception to unchanged shared-builder delegation. *)
Definition signed_bounds_word_domain (opts : signed_bounds_options) : word_domain signed_bounds :=
  let base := signed_bounds_word_builder opts in
  {| plat := plat base;
     ptop := ptop base;
     pconst_c := pconst_c base;
     pforward_c := fun o xs rw =>
       match xs with
       | [] => signed_bounds_top_c rw
       | _ :: _ => pforward_c base o xs rw
       end;
     passume_c := passume_c base;
     pmeet_c := pmeet_c base |}.

(** Nullary compatibility changes no successful evaluation and all other laws reuse the builder. *)
Theorem signed_bounds_word_laws : forall opts,
  word_laws (signed_bounds_word_domain opts) signed_bounds_gamma.
Proof.
  intro opts. pose proof (signed_bounds_word_builder_laws opts) as Hbase. constructor.
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

(** Both word families preserve legacy top at the malformed nullary boundary. *)
Theorem signed_bounds_nullary : forall opts o rw,
  pforward (signed_bounds_word_domain opts) o [] rw = signed_bounds_top rw.
Proof.
  reflexivity.
Qed.

(** Every nonempty signed-bound call retains the actual shared builder and all its charges. *)
Theorem signed_bounds_nonempty_delegation : forall opts o x xs rw,
  pforward_c (signed_bounds_word_domain opts) o (x :: xs) rw =
    pforward_c (signed_bounds_word_builder opts) o (x :: xs) rw.
Proof.
  reflexivity.
Qed.

(** Every non-multiplication forward call agrees across options, including malformed shapes. *)
Theorem signed_bounds_nonmultiplication_agrees : forall opts opts' o, o <> bvmul ->
  pforward_c (signed_bounds_word_domain opts) o =
    pforward_c (signed_bounds_word_domain opts') o.
Proof.
  intros opts opts' o Hother.
  assert (Hentry : Transfer.fwd (signed_bounds_table opts) o =
    Transfer.fwd (signed_bounds_table opts') o).
  { unfold signed_bounds_table. cbn [Transfer.fwd].
    now rewrite (signed_bounds_forward_nonmultiplication
      (sb_bits_options opts) (sb_bits_options opts') o Hother). }
  unfold signed_bounds_word_domain, signed_bounds_word_builder, word_of_table.
  cbn [pforward_c]. unfold Transfer.forward_c, Transfer.dispatch_c. now rewrite Hentry.
Qed.

(** Multiplier and widening selection leave the entire backward callback unchanged. *)
Theorem signed_bounds_backward_agrees : forall opts opts',
  passume_c (signed_bounds_word_domain opts) =
    passume_c (signed_bounds_word_domain opts').
Proof.
  intros opts opts'.
  unfold signed_bounds_word_domain, signed_bounds_word_builder, word_of_table.
  cbn [passume_c]. unfold Transfer.backward_c.
  cbn [signed_bounds_table Transfer.bwd]. reflexivity.
Qed.

(** Pure backward observations are shared for all multiplier and widening choices. *)
Theorem signed_bounds_backward_values_agree : forall opts opts',
  passume (signed_bounds_word_domain opts) = passume (signed_bounds_word_domain opts').
Proof.
  intros opts opts'. unfold passume. now rewrite (signed_bounds_backward_agrees opts opts').
Qed.

Definition signed_bounds_domain : word_domain signed_bounds :=
  signed_bounds_word_domain signed_bounds_default_options.

Definition signed_bounds_classic_domain : word_domain signed_bounds :=
  signed_bounds_word_domain signed_bounds_classic_options.

(** Width tags reuse the shared malformed-width, bottom and unrestricted-top behavior. *)
Definition signed_bounds_numeric : numeric_domain (tagged signed_bounds) :=
  tagged_domain signed_bounds_domain.

(** Tagged clients inherit the complete selected word dictionary's laws. *)
Theorem signed_bounds_numeric_laws :
  numeric_laws signed_bounds_numeric (tagged_gamma signed_bounds_gamma).
Proof.
  apply tagged_numeric_laws. apply signed_bounds_word_laws.
Qed.
