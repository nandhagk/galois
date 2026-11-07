(** * Stratum derivations and the perfect model

    Each stratum closes facts and rule instances over completed lower strata.
    For example, a negative literal tests the completed lower model.
    Builds on: DatalogSyntax and DatalogStratify. *)

From Stdlib Require Import List PeanoNat Lia.
From Galois.Datalog Require Import DatalogSyntax DatalogStratify.

(** Derivations use inductive same-level positives and fixed lower-level negation. *)
Inductive derives {P} (prog : program P) (facts : list (ground_atom P))
    (st : stratification P) (k : nat) (lower : ground_atom P -> Prop)
    : ground_atom P -> Prop :=
  | derive_fact : forall f, In f facts -> level st (fst f) = k ->
      derives prog facts st k lower f
  | derive_rule : forall r sigma, In r (rules prog) -> level st (pred (head r)) = k ->
      (forall a, In (LPos a) (body r) -> level st (pred a) < k -> lower (ground sigma a)) ->
      (forall a, In (LPos a) (body r) -> level st (pred a) = k ->
        derives prog facts st k lower (ground sigma a)) ->
      (forall a, In (LNeg a) (body r) -> ~ lower (ground sigma a)) ->
      derives prog facts st k lower (ground sigma (head r)).

Arguments derive_fact {P prog facts st k lower}.
Arguments derive_rule {P prog facts st k lower}.

(** The model below a bound combines the preceding completed strata. *)
Fixpoint model_below {P} (prog : program P) (facts : list (ground_atom P))
    (st : stratification P) (n : nat) : ground_atom P -> Prop :=
  match n with
  | 0 => fun _ => False
  | S k => fun f => model_below prog facts st k f \/
      derives prog facts st k (model_below prog facts st k) f
  end.

(** The perfect model completes every level in the supplied stratification. *)
Definition perfect_model {P} (prog : program P) (facts : list (ground_atom P))
    (st : stratification P) := model_below prog facts st (count st).

(** Failed stratification selects the empty model without claiming a model of the rules. *)
Definition least_model {P} (prog : program P) (facts : list (ground_atom P)) :=
  match stratify prog with
  | Some st => perfect_model prog facts st
  | None => fun _ => False
  end.

(** Holding a ground atom is membership in the declarative model. *)
Definition holds {P} (M : ground_atom P -> Prop) (p : P) (ts : tuple) := M (p, ts).

Section Levels.
Context {P : Type} (prog : program P) (facts : list (ground_atom P))
  (st : stratification P).

(** Every stratum derivation has its stratum's predicate level. *)
Theorem derives_level k lower f :
  derives prog facts st k lower f -> level st (fst f) = k.
Proof.
  intro Hderive; destruct Hderive; assumption.
Qed.

(** Completed model members occur below the completion bound. *)
Theorem model_below_level n f :
  model_below prog facts st n f -> level st (fst f) < n.
Proof.
  induction n as [|n IH]; cbn [model_below]; [contradiction |].
  intros [Hbelow | Hderive].
  - specialize (IH Hbelow); lia.
  - pose proof (derives_level n _ _ Hderive); lia.
Qed.

(** Completing further strata retains all earlier model members. *)
Theorem model_below_mono n m f :
  n <= m -> model_below prog facts st n f -> model_below prog facts st m f.
Proof.
  intro Hle; induction Hle as [|m Hle IH]; intro Hbelow.
  - exact Hbelow.
  - left; apply IH, Hbelow.
Qed.

(** A completed atom is derived at its own predicate level. *)
Theorem model_below_stage n f : level st (fst f) < n ->
  (model_below prog facts st n f <->
    derives prog facts st (level st (fst f))
      (model_below prog facts st (level st (fst f))) f).
Proof.
  induction n as [|n IH]; intro Hlevel; [lia |].
  cbn [model_below]; split.
  - intros [Hbelow | Hderive].
    + apply IH; [eapply model_below_level; exact Hbelow | exact Hbelow].
    + pose proof (derives_level n _ _ Hderive) as Heq; rewrite Heq; exact Hderive.
  - intro Hderive; destruct (Nat.eq_dec (level st (fst f)) n) as [Heq | Hne].
    + right; rewrite Heq in Hderive; exact Hderive.
    + left; apply IH; [lia | exact Hderive].
Qed.

(** Two completed bounds agree at every predicate below both bounds. *)
Theorem model_below_agrees n m f : level st (fst f) < n -> level st (fst f) < m ->
  (model_below prog facts st n f <-> model_below prog facts st m f).
Proof.
  intros Hn Hm; rewrite (model_below_stage n f Hn), (model_below_stage m f Hm).
  reflexivity.
Qed.

(** The successfully stratified least model contains facts and every satisfied rule instance. *)
Theorem least_model_closed : stratify prog = Some st ->
  (forall f, In f facts -> least_model prog facts f) /\
  forall r sigma, In r (rules prog) ->
    (forall a, In (LPos a) (body r) -> least_model prog facts (ground sigma a)) ->
    (forall a, In (LNeg a) (body r) -> ~ least_model prog facts (ground sigma a)) ->
    least_model prog facts (ground sigma (head r)).
Proof.
  intro Hstratify; pose proof (stratify_sound prog st Hstratify) as [Hcount Hstrat].
  unfold least_model; rewrite Hstratify; unfold perfect_model; split.
  - intros f Hfact; apply (model_below_stage (count st) f (Hcount (fst f))).
    apply derive_fact; [exact Hfact | reflexivity].
  - intros r sigma Hr Hpos Hneg.
    apply (model_below_stage (count st) (ground sigma (head r)) (Hcount _)).
    apply derive_rule with (r := r) (sigma := sigma); [exact Hr | reflexivity | | |].
    + intros a Ha Hlt; apply (model_below_agrees (count st) _ (ground sigma a));
        [apply Hcount | exact Hlt | apply Hpos; exact Ha].
    + intros a Ha Heq; pose proof (Hpos a Ha) as Hmember.
      apply (model_below_stage (count st) (ground sigma a) (Hcount _)) in Hmember.
      cbn [ground fst] in Hmember; rewrite Heq in Hmember; exact Hmember.
    + intros a Ha Hbelow; apply (Hneg a Ha).
      eapply model_below_mono; [|exact Hbelow]; apply Nat.lt_le_incl, Hcount.
Qed.

End Levels.
