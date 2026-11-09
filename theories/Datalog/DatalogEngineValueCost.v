(** * Value-only duties for wrapper cost composition

    The wrapper derives level and lower-database callback prices from predicate-key budgets.
    For example, callers supply row and probe data without assuming the price of a lower lookup.
    Builds on: DatalogSemiNaiveRunCost and public predicate lookup prices. *)

From Stdlib Require Import List NArith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Datalog Require Import DatalogSyntax DatalogStratify DatalogRelation DatalogFire
  DatalogSolve DatalogJoin DatalogSemiNaive DatalogSemiNaiveIndex DatalogSemiNaiveBudget
  DatalogSemiNaiveCost DatalogSemiNaiveSyntax DatalogSemiNaiveReady
  DatalogSemiNaiveCandidateCost DatalogSemiNaiveInitialCost DatalogSemiNaiveRunCost
  DatalogEngineSetupCost.
Import List.ListNotations SemiNaive SemiNaiveIndex SemiNaiveBudget SemiNaiveCost
  SemiNaiveSyntax SemiNaiveReady SemiNaiveCandidateCost SemiNaiveInitialCost SemiNaiveRunCost
  EngineSetupCost.
Local Open Scope N_scope.

Module EngineValueCost.

(** These data duties remove all level and lower-environment price premises from initialization. *)
Definition initial_values {P} (prog : program P) facts st lower k b : Prop :=
  (forall r, In r (fst (classify st k (rules prog))) ->
    preparation_data [] (positive_atoms (body r)) lower b /\
    firing_data r lower (seed_plan prog lower r) b) /\
  (forall f, In f (seed_atoms prog facts st lower k) ->
    key_budget (ground_encoding prog) (ground_encode b) (ground_width b) f /\
    key_budget (penc prog) (predicate_encode b) (predicate_width b) (fst f) /\
    key_budget tuple_encoding (tuple_encode b) (tuple_width b) (snd f)) /\
  forall spec, In spec (snd (classify st k (rules prog))) ->
    preparation_data [] (positive_atoms (body (tag_rule (fst spec) (snd spec))))
      (tagged_c prog st k lower (indexed prog facts st lower k)
        (indexed prog facts st lower k)) b.

(** Round values retain probes, emitted ground keys and fresh-index data without helper prices. *)
Definition round_values {P} (prog : program P) st lower k b s : Prop :=
  (forall j, In j (jobs s) ->
    firing_data (tagged_rule j)
      (tagged_c prog st k lower (accumulated_index s) (frontier_index s)) (plan j) b /\
    forall row, member row (Join.fire (tagged_rule j)
      (tagged_c prog st k lower (accumulated_index s) (frontier_index s)) (plan j)) = true ->
      key_budget (ground_encoding prog) (ground_encode b) (ground_width b)
        (pred (head (source_rule j)), row)) /\
  (FinSet.is_empty (fresh prog st lower k s) = false ->
    (forall f, FinSet.mem (ground_encoding prog) f (fresh prog st lower k s) = true ->
      key_budget (penc prog) (predicate_encode b) (predicate_width b) (fst f) /\
      key_budget tuple_encoding (tuple_encode b) (tuple_width b) (snd f)) /\
    forall j, In j (jobs s) ->
      maintenance_data prog
        (add_atoms prog (FinSet.elements (fresh prog st lower k s)) Map.empty)
        (plan j) (args_bound b) (rows_bound b)
        (predicate_encode b) (predicate_width b) (tuple_encode b) (tuple_width b)).

Lemma preparation_support {P} (prog : program P) facts st k spec atom :
  In spec (snd (classify st k (rules prog))) ->
  In atom (positive_atoms (body (tag_rule (fst spec) (snd spec)))) ->
  In (fst (pred atom)) (predicate_inventory prog facts).
Proof.
  destruct spec as [r pivot]; cbn [fst snd]; intros Hspec Hatom.
  apply classify_jobs in Hspec as [Hr _].
  apply positive_atoms_spec in Hatom.
  rewrite tag_rule_equation in Hatom; cbn [body] in Hatom.
  apply tagged_positive in Hatom as [i [source [Hocc ->]]].
  apply (literal_support prog facts r (LPos source) Hr).
  apply (proj1 (occurrences_spec 0 (body r) source)); exists i; exact Hocc.
Qed.

Lemma negative_support {P} (prog : program P) facts st lower k s j atom :
  ready prog st lower k s -> In j (jobs s) -> In (LNeg atom) (body (tagged_rule j)) ->
  In (fst (pred atom)) (predicate_inventory prog facts).
Proof.
  intros Hready Hj Hatom.
  destruct (job_member prog st lower k s j Hready Hj) as [Hr _].
  destruct (job_layout _ _ _ _ _ Hready j Hj) as [Htag _].
  rewrite Htag, tag_rule_equation in Hatom; cbn [body] in Hatom.
  apply tagged_negative in Hatom as [source [Hsource ->]].
  apply (literal_support prog facts (source_rule j) (LNeg source) Hr Hsource).
Qed.

Lemma initial_lift {P} (prog : program P) facts st lower k b :
  (forall p, In p (predicate_inventory prog facts) ->
    Cost.ticks (level_c st p) <= level_bound b /\
    Cost.ticks (lower p) <= lower_bound b) ->
  predicate_keys prog facts (predicate_encode b) (predicate_width b) ->
  initial_values prog facts st lower k b -> initial_data prog facts st lower k b.
Proof.
  intros Hcallbacks Hkeys [Hseeds [Hseedkeys Hprepare]].
  assert (Hinput : forall p, In p (predicate_inventory prog facts) -> input prog st lower b p).
  { intros p Hp; destruct (Hcallbacks p Hp); split; [assumption | split; [assumption |
      apply Hkeys, Hp]]. }
  split.
  - intros r Hr; split.
    + apply (proj1 (Hcallbacks _ (head_support prog facts r Hr))).
    + intros atom Ha; apply (proj1 (Hcallbacks _ (literal_support prog facts r (LPos atom) Hr Ha))).
  - split.
    + intros f Hf; apply (proj1 (Hcallbacks _ (fact_support prog facts f Hf))).
    + split.
      * intros r Hr; destruct (Hseeds r Hr) as [Hp Hf]; split; [exact Hp | split; [exact Hf |]].
        apply classify_seeds in Hr as [Hr _]; intros atom [Ha | Ha]; apply Hinput.
        -- apply (literal_support prog facts r (LPos atom) Hr), positive_atoms_spec, Ha.
        -- apply (literal_support prog facts r (LNeg atom) Hr Ha).
      * split; [exact Hseedkeys |].
        intros spec Hspec; split; [apply Hprepare, Hspec |].
        intros atom Ha; apply Hinput, (preparation_support prog facts st k spec atom Hspec Ha).
Qed.

Lemma round_lift {P} (prog : program P) facts st lower k b s :
  ready prog st lower k s ->
  (forall p, In p (predicate_inventory prog facts) ->
    Cost.ticks (level_c st p) <= level_bound b /\
    Cost.ticks (lower p) <= lower_bound b) ->
  predicate_keys prog facts (predicate_encode b) (predicate_width b) ->
  round_values prog st lower k b s -> round_data prog st lower k b s.
Proof.
  intros Hready Hcallbacks Hkeys [Hjobs Hadvance]; split; [|exact Hadvance].
  intros j Hj; destruct (Hjobs j Hj) as [Hfire Hground].
  split; [exact Hfire | split; [|exact Hground]].
  intros atom Ha.
  pose proof (negative_support prog facts st lower k s j atom Hready Hj Ha) as Hp.
  destruct (Hcallbacks (fst (pred atom)) Hp) as [Hl Hlower].
  split; [exact Hl | split; [exact Hlower | apply Hkeys, Hp]].
Qed.

(** Stratifier and lower-database callback duties follow from primitive predicate-key prices. *)
Theorem wrapper_callbacks {P} (prog : program P) facts st db b :
  stratify prog = Some st ->
  predicate_keys prog facts (predicate_encode b) (predicate_width b) ->
  1 + predicate_encode b + predicate_width b <= level_bound b ->
  1 + predicate_encode b + predicate_width b <= lower_bound b ->
  forall p, In p (predicate_inventory prog facts) ->
    Cost.ticks (level_c st p) <= level_bound b /\
    Cost.ticks (rel_of_c prog db p) <= lower_bound b.
Proof.
  intros Hst Hkeys Hlevel Hlower p Hp; split.
  - eapply N.le_trans; [apply (stratified_callback_cost prog st _ _ p Hst (Hkeys p Hp)) |].
    exact Hlevel.
  - eapply N.le_trans; [apply (rel_of_cost prog db p _ _ (Hkeys p Hp)) | exact Hlower].
Qed.

End EngineValueCost.
Import EngineValueCost.
