(** * Preparation callback adequacy

    Preparation receipts account for predicate calls at their actual source boundaries.
    For example, repeated atoms retain separate encoding frames.
    Builds on: RulesAuditPrepareCallbacks, RulesAuditIndexAdequacy,
    RulesAuditNestedProbeAdequacy and RulesAuditJoinSyntaxAdequacy. *)

From Stdlib Require Import List PArith PeanoNat Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet
  CollectionsAuditTrie CollectionsAuditElements CollectionsAuditEncoding CollectionsAuditFinSet
  CollectionsAuditTrieAdequacy CollectionsAuditEncodingAdequacy
  CollectionsAuditFinSetAdequacy CollectionsAuditUnionAdequacy.
From Galois.Rules Require Import RulesSyntax RulesCompile RulesJoin RulesAuditMaterializePrelude
  RulesAuditJoinSyntax RulesAuditNestedPrepare RulesAuditMultiwayPrepare RulesAuditPrepareCallbacks
  RulesAuditIndex RulesAuditIndexAdequacy RulesAuditNestedProbeAdequacy
  RulesAuditJoinSyntaxAdequacy.
Import List.ListNotations.

(** * Runs without predicate callbacks *)

Definition prepare_silent_frame (frame : mat_frame) : Prop :=
  match frame with
  | MatEncode _ _ _ _ => False
  | _ => True
  end.

Definition prepare_silent {A} (run : mat_run A) : Prop :=
  Forall prepare_silent_frame (snd run).

Lemma prepare_silent_return A (value : A) : prepare_silent (mat_return value).
Proof.
  constructor; [exact I | constructor].
Qed.

Lemma prepare_silent_mark A site (run : mat_run A) :
  prepare_silent run -> prepare_silent (mat_mark site run).
Proof.
  destruct run as [value events]; intro H; constructor; assumption || exact I.
Qed.

Lemma prepare_silent_bind A B (run : mat_run A) (next : A -> mat_run B) :
  prepare_silent run -> (forall value, prepare_silent (next value)) ->
  prepare_silent (mat_bind run next).
Proof.
  destruct run as [value events]; intros Hrun Hnext.
  specialize (Hnext value); destruct (next value) as [result later] eqn:Hresult.
  unfold prepare_silent in *; cbn in *; rewrite Hresult; cbn; apply Forall_app; split; assumption.
Qed.

Lemma prepare_silent_lift A E site size work (run : A * list E) :
  prepare_silent (mat_lift site size work run).
Proof.
  destruct run; constructor; [exact I | constructor].
Qed.

Lemma prepare_silent_append A (xs ys : list A) : prepare_silent (mat_append xs ys).
Proof.
  induction xs as [|x xs IH]; cbn [mat_append].
  - apply prepare_silent_mark, prepare_silent_return.
  - apply prepare_silent_mark, prepare_silent_bind; [exact IH |].
    intro; apply prepare_silent_return.
Qed.

Lemma prepare_silent_flatmap A B (f : A -> mat_run (list B)) xs :
  (forall x, prepare_silent (f x)) -> prepare_silent (mat_flatmap f xs).
Proof.
  intro Hf; induction xs as [|x xs IH]; cbn [mat_flatmap].
  - apply prepare_silent_mark, prepare_silent_return.
  - apply prepare_silent_mark, prepare_silent_bind; [apply Hf |].
    intro first; apply prepare_silent_bind; [exact IH |].
    intro later; apply prepare_silent_append.
Qed.

Lemma prepare_silent_filter A (f : A -> mat_run bool) xs :
  (forall x, prepare_silent (f x)) -> prepare_silent (mat_filter f xs).
Proof.
  intro Hf; induction xs as [|x xs IH]; cbn [mat_filter].
  - apply prepare_silent_mark, prepare_silent_return.
  - apply prepare_silent_mark, prepare_silent_bind; [apply Hf |].
    intro keep; apply prepare_silent_bind; [exact IH |].
    intro tail; apply prepare_silent_return.
Qed.

Lemma prepare_silent_foldr A B (f : A -> B -> mat_run B) xs :
  (forall x value, prepare_silent (f x value)) ->
  forall initial, prepare_silent (mat_foldr f xs initial).
Proof.
  intro Hf; induction xs as [|x xs IH]; intro initial; cbn [mat_foldr].
  - apply prepare_silent_mark, prepare_silent_return.
  - apply prepare_silent_mark, prepare_silent_bind; [apply IH |].
    intro value; apply Hf.
Qed.

Lemma prepare_silent_atom_vars P (a : atom P) : prepare_silent (mat_atom_vars a).
Proof.
  unfold mat_atom_vars; apply prepare_silent_flatmap; intro t.
  unfold mat_term_vars; apply prepare_silent_mark; destruct t; apply prepare_silent_return.
Qed.

Lemma prepare_silent_bound_add P bound (a : atom P) : prepare_silent (mat_bound_add bound a).
Proof.
  unfold mat_bound_add; apply prepare_silent_bind; [apply prepare_silent_atom_vars |].
  intro variables; apply prepare_silent_bind; [apply prepare_silent_lift |].
  intro vars; apply prepare_silent_lift.
Qed.

Lemma prepare_silent_atoms_with P v (atoms : list (atom P)) :
  prepare_silent (mat_atoms_with v atoms).
Proof.
  unfold mat_atoms_with; apply prepare_silent_filter; intro a.
  unfold mat_has_variable; apply prepare_silent_bind; [apply prepare_silent_atom_vars |].
  intro variables; apply prepare_silent_bind; [apply prepare_silent_lift |].
  intro vars; apply prepare_silent_lift.
Qed.

Lemma prepare_silent_tuple_key bound terms row :
  prepare_silent (mat_tuple_key bound terms row).
Proof.
  revert row; induction terms as [|t terms IH]; intros [|c row]; cbn [mat_tuple_key].
  - apply prepare_silent_mark, prepare_silent_return.
  - apply prepare_silent_mark, prepare_silent_return.
  - apply prepare_silent_mark, prepare_silent_return.
  - apply prepare_silent_mark, prepare_silent_bind; [apply IH |].
    intros [key |].
    + apply prepare_silent_bind.
      * unfold mat_bound_term; apply prepare_silent_mark; destruct t;
          first [apply prepare_silent_lift | apply prepare_silent_return].
      * intro kept; apply prepare_silent_return.
    + apply prepare_silent_return.
Qed.

Lemma prepare_silent_get_encoded Q A (enc : Q -> mat_run positive) key (input : Map.t Q A) :
  prepare_silent (enc key) -> prepare_silent (mat_get_encoded enc key input).
Proof.
  intro H; unfold mat_get_encoded; apply prepare_silent_bind; [exact H |].
  intro code; destruct (audit_map_code_get code input); constructor; [exact I | constructor].
Qed.

Lemma prepare_silent_set_encoded Q A (enc : Q -> mat_run positive) key value (input : Map.t Q A) :
  prepare_silent (enc key) -> prepare_silent (mat_set_encoded enc key value input).
Proof.
  intro H; unfold mat_set_encoded; apply prepare_silent_bind; [exact H |].
  intro code; destruct (audit_trie_set code (key, value) input).
  constructor; [exact I | constructor].
Qed.

Lemma prepare_silent_index_add bound terms row before :
  prepare_silent (mat_index_add_full bound terms row before).
Proof.
  unfold mat_index_add_full; apply prepare_silent_bind; [apply prepare_silent_tuple_key |].
  intros [key |]; [|apply prepare_silent_return].
  apply prepare_silent_bind.
  - apply prepare_silent_get_encoded; apply prepare_silent_lift.
  - intro raw; apply prepare_silent_bind; [apply prepare_silent_return |].
    intro value; apply prepare_silent_set_encoded, prepare_silent_lift.
Qed.

Lemma prepare_silent_build_index bound terms rows :
  prepare_silent (mat_build_index_full bound terms rows).
Proof.
  unfold mat_build_index_full; apply prepare_silent_foldr; intros; apply prepare_silent_index_add.
Qed.

Lemma prepare_silent_variable_add bound terms v row before :
  prepare_silent (mat_variable_add_full bound terms v row before).
Proof.
  unfold mat_variable_add_full; apply prepare_silent_bind; [apply prepare_silent_tuple_key |].
  intros [key |]; [|apply prepare_silent_return].
  apply prepare_silent_bind; [apply prepare_silent_lift |].
  intros [binding |]; [|apply prepare_silent_return].
  apply prepare_silent_bind; [apply prepare_silent_lift |].
  intro value; apply prepare_silent_bind.
  - apply prepare_silent_get_encoded, prepare_silent_lift.
  - intro raw; apply prepare_silent_bind; [apply prepare_silent_lift |].
    intro next; apply prepare_silent_set_encoded, prepare_silent_lift.
Qed.

Lemma prepare_silent_build_variable bound terms v rows :
  prepare_silent (mat_build_variable_full bound terms v rows).
Proof.
  unfold mat_build_variable_full; apply prepare_silent_foldr; intros.
  apply prepare_silent_variable_add.
Qed.

(** * Receipt composition *)

Definition prepare_receipts {P B A} (E : encoding P)
    (source : P -> positive -> list B -> Prop) (weight : B -> nat) (run : mat_run A)
    (budget : nat) : Prop :=
  exists bodies, rules_predicate_trace_source E source (snd run) bodies /\
    rules_predicate_bodies_work weight bodies <= budget.

Lemma prepare_bodies_work_app B (weight : B -> nat) first second :
  rules_predicate_bodies_work weight (first ++ second) =
    rules_predicate_bodies_work weight first + rules_predicate_bodies_work weight second.
Proof.
  unfold rules_predicate_bodies_work.
  induction first as [|group rest IH]; cbn.
  - reflexivity.
  - rewrite IH; lia.
Qed.

Lemma prepare_receipts_silent P B A (E : encoding P)
    (source : P -> positive -> list B -> Prop) (weight : B -> nat) (run : mat_run A) :
  prepare_silent run -> prepare_receipts E source weight run 0.
Proof.
  unfold prepare_silent, prepare_receipts, rules_predicate_trace_source.
  destruct run as [value events]; cbn; intro Hsilent.
  induction Hsilent as [|frame events Hframe Htail IH].
  - exists []; split; constructor || reflexivity.
  - destruct IH as [bodies [Htrace Hwork]].
    exists ([] :: bodies); split.
    + constructor; [|exact Htrace].
      destruct frame; cbn in *; try contradiction; reflexivity.
    + cbn [rules_predicate_bodies_work] in *; exact Hwork.
Qed.

Lemma prepare_receipts_bind P B A C (E : encoding P)
    (source : P -> positive -> list B -> Prop) (weight : B -> nat)
    (run : mat_run A) (next : A -> mat_run C) first_budget second_budget :
  prepare_receipts E source weight run first_budget ->
  (forall value, prepare_receipts E source weight (next value) second_budget) ->
  prepare_receipts E source weight (mat_bind run next) (first_budget + second_budget).
Proof.
  destruct run as [value events]; intros [first [Hfirst Hbudget]] Hnext.
  specialize (Hnext value); destruct (next value) as [result later] eqn:Hresult.
  destruct Hnext as [second [Hsecond Hsecond_budget]].
  unfold prepare_receipts, rules_predicate_trace_source in *; cbn in *; rewrite Hresult; cbn.
  exists (first ++ second); split.
  - apply Forall2_app; assumption.
  - rewrite prepare_bodies_work_app; lia.
Qed.

Lemma prepare_receipts_mark P B A (E : encoding P)
    (source : P -> positive -> list B -> Prop) (weight : B -> nat) site (run : mat_run A) budget :
  prepare_receipts E source weight run budget ->
  prepare_receipts E source weight (mat_mark site run) budget.
Proof.
  destruct run as [value events]; intros [bodies [Htrace Hbudget]].
  exists ([] :: bodies); split.
  - constructor; [reflexivity | exact Htrace].
  - exact Hbudget.
Qed.

Lemma prepare_receipts_get P B A (E : encoding P)
    (source : P -> positive -> list B -> Prop) (weight : B -> nat) price key (input : Map.t P A) :
  rules_predicate_source_laws E source weight price ->
  prepare_receipts E source weight (mat_get E key input) (price key).
Proof.
  intros [Htotal Hbound].
  destruct (Htotal key) as [body Hbody].
  unfold prepare_receipts, mat_get, mat_bind, mat_encode.
  destruct (audit_map_code_get (encode E key) input) as [out events].
  cbn; exists [[body]; []]; split.
  - constructor.
    + exists key, (encode E key), body; repeat split; assumption || reflexivity.
    + constructor; [reflexivity | constructor].
  - unfold rules_predicate_bodies_work; cbn.
    specialize (Hbound key (encode E key) body Hbody); lia.
Qed.

Lemma prepare_receipts_weaken P B A (E : encoding P)
    (source : P -> positive -> list B -> Prop) (weight : B -> nat) (run : mat_run A) n m :
  prepare_receipts E source weight run n -> n <= m -> prepare_receipts E source weight run m.
Proof.
  intros [bodies [Htrace Hwork]] Hle; exists bodies; split; [exact Htrace | lia].
Qed.

Lemma prepare_receipts_bind_silent P B A C (E : encoding P)
    (source : P -> positive -> list B -> Prop) (weight : B -> nat)
    (run : mat_run A) (next : A -> mat_run C) budget :
  prepare_silent run -> (forall value, prepare_receipts E source weight (next value) budget) ->
  prepare_receipts E source weight (mat_bind run next) budget.
Proof.
  intros Hsilent Hnext.
  replace budget with (0 + budget) by lia.
  apply prepare_receipts_bind; [apply prepare_receipts_silent; exact Hsilent | exact Hnext].
Qed.

(** The nested traversal captures a body for every actual predicate occurrence. *)
Lemma prepare_nested_receipts P B (E : encoding P)
    (source : P -> positive -> list B -> Prop) (weight : B -> nat) price relations atoms :
  rules_predicate_source_laws E source weight price ->
  forall bound, prepare_receipts E source weight (rules_prepare_nested_full E relations atoms bound)
    (rules_predicate_input_budget price atoms).
Proof.
  intro Hlaws; induction atoms as [|a atoms IH]; intro bound.
  - cbn [rules_prepare_nested_full rules_predicate_input_budget].
    apply prepare_receipts_silent, prepare_silent_mark, prepare_silent_return.
  - cbn [rules_prepare_nested_full rules_predicate_input_budget].
    apply prepare_receipts_mark.
    apply prepare_receipts_bind; [apply prepare_receipts_get; exact Hlaws |].
    intro raw; apply prepare_receipts_bind_silent; [apply prepare_silent_build_index |].
    intro index; apply prepare_receipts_bind_silent; [apply prepare_silent_bound_add |].
    intro next_bound.
    eapply prepare_receipts_weaken.
    + apply prepare_receipts_bind with
        (first_budget := rules_predicate_input_budget price atoms) (second_budget := 0).
      * apply IH.
      * intro tail; apply prepare_receipts_silent, prepare_silent_return.
    + change (rules_predicate_input_budget price atoms + 0 <=
        rules_predicate_input_budget price atoms); lia.
Qed.

(** Each selected atom contributes exactly one possible predicate-body allowance. *)
Lemma prepare_variable_map_receipts P B (E : encoding P)
    (source : P -> positive -> list B -> Prop) (weight : B -> nat) price relations bound v atoms :
  rules_predicate_source_laws E source weight price ->
  prepare_receipts E source weight (rules_variable_map_full E relations bound v atoms)
    (rules_predicate_input_budget price atoms).
Proof.
  intro Hlaws; induction atoms as [|a atoms IH].
  - cbn [rules_variable_map_full rules_predicate_input_budget].
    apply prepare_receipts_silent, prepare_silent_mark, prepare_silent_return.
  - cbn [rules_variable_map_full rules_predicate_input_budget].
    apply prepare_receipts_mark.
    apply prepare_receipts_bind; [apply prepare_receipts_get; exact Hlaws |].
    intro raw; apply prepare_receipts_bind_silent; [apply prepare_silent_build_variable |].
    intro index.
    eapply prepare_receipts_weaken.
    + apply prepare_receipts_bind with
        (first_budget := rules_predicate_input_budget price atoms) (second_budget := 0).
      * exact IH.
      * intro tail; apply prepare_receipts_silent, prepare_silent_return.
    + change (rules_predicate_input_budget price atoms + 0 <=
        rules_predicate_input_budget price atoms); lia.
Qed.

Lemma prepare_receipts_bind_silent_at P B A C (E : encoding P)
    (source : P -> positive -> list B -> Prop) (weight : B -> nat)
    (run : mat_run A) (next : A -> mat_run C) budget :
  prepare_silent run -> prepare_receipts E source weight (next (fst run)) budget ->
  prepare_receipts E source weight (mat_bind run next) budget.
Proof.
  destruct run as [value events]; intros Hsilent Hnext; cbn in Hnext.
  unfold mat_bind; destruct (next value) as [result later] eqn:Hresult.
  destruct (prepare_receipts_silent P B A E source weight (value, events) Hsilent)
    as [first [Hfirst Hwork]].
  destruct Hnext as [second [Hsecond Hsecond_work]].
  unfold prepare_receipts, rules_predicate_trace_source in *; cbn in *.
  exists (first ++ second); split.
  - apply Forall2_app; assumption.
  - rewrite prepare_bodies_work_app; lia.
Qed.

Lemma prepare_filter_budget P (price : P -> nat) (keep : atom P -> bool) atoms :
  rules_predicate_input_budget price (filter keep atoms) <=
    rules_predicate_input_budget price atoms.
Proof.
  unfold rules_predicate_input_budget; induction atoms as [|a atoms IH]; cbn.
  - lia.
  - destruct (keep a); cbn; lia.
Qed.

Lemma prepare_variable_receipts P B (E : encoding P)
    (source : P -> positive -> list B -> Prop) (weight : B -> nat) price relations bound v atoms :
  rules_predicate_source_laws E source weight price ->
  prepare_receipts E source weight (rules_prepare_variable_full E relations bound v atoms)
    (rules_predicate_input_budget price atoms).
Proof.
  intro Hlaws; unfold rules_prepare_variable_full.
  apply prepare_receipts_bind_silent_at; [apply prepare_silent_atoms_with |].
  eapply prepare_receipts_weaken.
  - apply prepare_variable_map_receipts; exact Hlaws.
  - unfold mat_atoms_with; rewrite mat_filter_value.
    apply prepare_filter_budget.
Qed.

(** Multiway preparation charges each variable at most once per input atom. *)
Lemma prepare_multiway_receipts P B (E : encoding P)
    (source : P -> positive -> list B -> Prop) (weight : B -> nat) price relations vars atoms :
  rules_predicate_source_laws E source weight price ->
  forall bound, prepare_receipts E source weight
    (rules_prepare_multiway_full E relations vars bound atoms)
    (length vars * rules_predicate_input_budget price atoms).
Proof.
  intro Hlaws; induction vars as [|v vars IH]; intro bound.
  - cbn [rules_prepare_multiway_full]; apply prepare_receipts_silent.
    apply prepare_silent_mark, prepare_silent_return.
  - cbn [rules_prepare_multiway_full length].
    apply prepare_receipts_mark.
    apply prepare_receipts_bind.
    + apply prepare_variable_receipts; exact Hlaws.
    + intro domains; apply prepare_receipts_bind_silent; [apply prepare_silent_lift |].
      intro next_bound.
      eapply prepare_receipts_weaken.
      * apply prepare_receipts_bind with
          (first_budget := length vars * rules_predicate_input_budget price atoms)
          (second_budget := 0).
        -- apply IH.
        -- intro tail; apply prepare_receipts_silent, prepare_silent_return.
      * change (length vars * rules_predicate_input_budget price atoms + 0 <=
        length vars * rules_predicate_input_budget price atoms); lia.
Qed.

(** * Preparation result equations *)

Lemma prepare_get_value P A (E : encoding P) p (relations : Map.t P A) :
  fst (mat_get E p relations) = Map.get E p relations.
Proof.
  unfold mat_get, mat_bind, mat_encode.
  pose proof (audit_map_code_get_erases P A (encode E p) relations) as Hget.
  destruct (audit_map_code_get (encode E p) relations); exact Hget.
Qed.

Lemma prepare_nat_add_value v bound :
  fst (mat_nat_add v bound) = FinSet.add nat_encoding v bound.
Proof.
  unfold mat_nat_add, mat_lift.
  pose proof (audit_finset_add_erases _ _ audit_nat_encode nat_encoding v bound
    (audit_nat_encode_erases v)) as Hadd.
  destruct (audit_finset_add audit_nat_encode v bound); exact Hadd.
Qed.

(** Nested preparation uses the corresponding row-index result at each atom. *)
Lemma prepare_nested_value_given P (E : encoding P) relations atoms :
  (forall bound terms rows,
    fst (mat_build_index_full bound terms rows) = build_index bound terms rows) ->
  forall bound, fst (rules_prepare_nested_full E relations atoms bound) =
    prepare_nested atoms bound (join_relation_rows E relations).
Proof.
  intro Hindex; induction atoms as [|a atoms IH]; intro bound.
  - reflexivity.
  - cbn [rules_prepare_nested_full prepare_nested mat_mark mat_bind].
    pose proof (prepare_get_value P (list tuple) E (pred a) relations) as Hget.
    destruct (mat_get E (pred a) relations) as [raw events] eqn:Hraw; cbn in Hget.
    unfold join_relation_rows; rewrite <- Hget.
    pose proof (Hindex bound (args a) (match raw with Some rows => rows | None => [] end))
      as Hbuild.
    destruct (mat_build_index_full bound (args a)
      (match raw with Some rows => rows | None => [] end)) as [index index_events] eqn:Hindexrun.
    cbn in Hbuild.
    pose proof (proj1 (proj2 mat_join_syntax_erasure) P bound a) as Hbound.
    destruct (mat_bound_add bound a) as [next_bound bound_events] eqn:Hboundrun; cbn in Hbound.
    specialize (IH next_bound).
    destruct (rules_prepare_nested_full E relations atoms next_bound) as [tail tail_events]
      eqn:Htail; cbn in IH.
    cbn [mat_bind mat_return mat_mark]; try rewrite Hraw; try rewrite Hindexrun;
      try rewrite Hboundrun; try rewrite Htail.
    cbn [mat_bind mat_return mat_mark]; rewrite Hbuild, IH, Hbound; reflexivity.
Qed.

Lemma prepare_variable_map_value_given P (E : encoding P) relations bound v atoms :
  (forall bound terms v rows,
    fst (mat_build_variable_full bound terms v rows) = build_variable_index bound terms v rows) ->
  fst (rules_variable_map_full E relations bound v atoms) =
    map (fun a => VariableSearch (args a)
      (build_variable_index bound (args a) v (join_relation_rows E relations (pred a)))) atoms.
Proof.
  intro Hindex; induction atoms as [|a atoms IH].
  - reflexivity.
  - cbn [rules_variable_map_full map mat_mark mat_bind].
    pose proof (prepare_get_value P (list tuple) E (pred a) relations) as Hget.
    destruct (mat_get E (pred a) relations) as [raw events] eqn:Hraw; cbn in Hget.
    unfold join_relation_rows in *; rewrite <- Hget.
    pose proof (Hindex bound (args a) v (match raw with Some rows => rows | None => [] end))
      as Hbuild.
    destruct (mat_build_variable_full bound (args a) v
      (match raw with Some rows => rows | None => [] end)) as [index index_events] eqn:Hindexrun.
    cbn in Hbuild.
    destruct (rules_variable_map_full E relations bound v atoms) as [tail tail_events] eqn:Htail.
    cbn in IH.
    cbn [mat_bind mat_return mat_mark]; try rewrite Hraw; try rewrite Hindexrun; try rewrite Htail.
    cbn [mat_bind mat_return mat_mark]; rewrite Hbuild, IH; reflexivity.
Qed.

Lemma prepare_variable_value_given P (E : encoding P) relations bound v atoms :
  (forall bound terms v rows,
    fst (mat_build_variable_full bound terms v rows) = build_variable_index bound terms v rows) ->
  fst (rules_prepare_variable_full E relations bound v atoms) =
    prepare_variable bound v atoms (join_relation_rows E relations).
Proof.
  intro Hindex; unfold rules_prepare_variable_full, prepare_variable.
  pose proof (proj2 (proj2 (proj2 (proj2 mat_join_syntax_erasure))) P v atoms) as Hselect.
  destruct (mat_atoms_with v atoms) as [selected events] eqn:Hselected; cbn in Hselect.
  pose proof (prepare_variable_map_value_given P E relations bound v selected Hindex) as Hmap.
  destruct (rules_variable_map_full E relations bound v selected) as [result map_events]
    eqn:Hmaprun; cbn in Hmap.
  cbn [mat_bind]; try rewrite Hselected; try rewrite Hmaprun; cbn.
  rewrite Hmap, Hselect; reflexivity.
Qed.

(** Multiway preparation uses the corresponding variable-index result at each selected atom. *)
Lemma prepare_multiway_value_given P (E : encoding P) relations vars atoms :
  (forall bound terms v rows,
    fst (mat_build_variable_full bound terms v rows) = build_variable_index bound terms v rows) ->
  forall bound, fst (rules_prepare_multiway_full E relations vars bound atoms) =
    prepare_multiway vars bound atoms (join_relation_rows E relations).
Proof.
  intro Hindex; induction vars as [|v vars IH]; intro bound.
  - reflexivity.
  - cbn [rules_prepare_multiway_full prepare_multiway mat_mark mat_bind].
    pose proof (prepare_variable_value_given P E relations bound v atoms Hindex) as Hvariable.
    destruct (rules_prepare_variable_full E relations bound v atoms) as [domains events]
      eqn:Hvariable_run; cbn in Hvariable.
    pose proof (prepare_nat_add_value v bound) as Hadd.
    destruct (mat_nat_add v bound) as [next_bound add_events] eqn:Hadd_run; cbn in Hadd.
    specialize (IH next_bound).
    destruct (rules_prepare_multiway_full E relations vars next_bound atoms) as [tail tail_events]
      eqn:Htail; cbn in IH.
    cbn [mat_bind mat_return mat_mark]; try rewrite Hvariable_run; try rewrite Hadd_run;
      try rewrite Htail.
    cbn [mat_bind mat_return mat_mark]; rewrite Hvariable, IH, Hadd; reflexivity.
Qed.

(** Receipt composition leaves the internal work estimate at the preparation boundary. *)
Lemma prepare_nested_source_given :
  mat_index_full_erases_statement -> rules_prepare_nested_full_input_bound_statement ->
  rules_nested_prepare_source_statement.
Proof.
  intros Hindex Hwork P B E relations atoms bound source weight price Hlaws.
  pose proof (prepare_nested_receipts P B E source weight price relations atoms Hlaws bound)
    as Hreceipt.
  pose proof (prepare_nested_value_given P E relations atoms (proj1 (proj2 Hindex)) bound)
    as Hvalue.
  specialize (Hwork P E relations atoms bound).
  destruct (rules_prepare_nested_full E relations atoms bound) as [out events] eqn:Hrun.
  destruct Hreceipt as [bodies [Htrace Hbody]].
  cbn [fst snd] in Htrace, Hbody, Hvalue, Hwork.
  exists bodies; split; [exact Htrace |].
  split; [exact Hvalue | lia].
Qed.

(** The multiway source conclusion composes erasure, callback receipts and internal work. *)
Lemma prepare_multiway_source_given :
  mat_index_full_erases_statement ->
  (forall P (E : encoding P) relations vars bound atoms,
    mat_work (snd (rules_prepare_multiway_full E relations vars bound atoms)) <=
      rules_multiway_prepare_input_budget E relations vars bound atoms) ->
  rules_multiway_prepare_source_statement.
Proof.
  intros Hindex Hwork P B E relations vars bound atoms source weight price Hlaws.
  pose proof (prepare_multiway_receipts P B E source weight price relations vars atoms Hlaws bound)
    as Hreceipt.
  pose proof (prepare_multiway_value_given P E relations vars atoms
    (proj2 (proj2 (proj2 Hindex))) bound) as Hvalue.
  specialize (Hwork P E relations vars bound atoms).
  destruct (rules_prepare_multiway_full E relations vars bound atoms) as [out events] eqn:Hrun.
  destruct Hreceipt as [bodies [Htrace Hbody]].
  cbn [fst snd] in Htrace, Hbody, Hvalue, Hwork.
  exists bodies; split; [exact Htrace |].
  split; [exact Hvalue | lia].
Qed.

(** * Source work composition *)

Lemma prepare_work_app first second :
  mat_work (first ++ second) = mat_work first + mat_work second.
Proof.
  unfold mat_work; induction first as [|frame rest IH]; cbn.
  - reflexivity.
  - rewrite IH; lia.
Qed.

Lemma prepare_work_bind A B (run : mat_run A) (next : A -> mat_run B) :
  mat_work (snd (mat_bind run next)) = mat_work (snd run) + mat_work (snd (next (fst run))).
Proof.
  destruct run as [value events]; destruct (next value) as [result later] eqn:Hnext.
  cbn [mat_bind fst snd]; rewrite Hnext; cbn; apply prepare_work_app.
Qed.

Lemma prepare_work_mark A site (run : mat_run A) :
  mat_work (snd (mat_mark site run)) = 100 + mat_work (snd run).
Proof.
  destruct run; reflexivity.
Qed.

Lemma prepare_work_return A (value : A) : mat_work (snd (mat_return value)) = 100.
Proof.
  reflexivity.
Qed.

(** A rebuilt trie node adds at most one node beyond its two children. *)
Lemma prepare_trie_node_size A (left right : Trie.t A) value :
  audit_trie_nodes (Trie.node left value right) <=
    1 + audit_trie_nodes left + audit_trie_nodes right.
Proof.
  destruct left, value, right; cbn [Trie.node audit_trie_nodes audit_elements_nodes]; lia.
Qed.

(** The two children together never exceed the input trie's node count. *)
Lemma prepare_trie_children_size A (input : Trie.t A) :
  audit_trie_nodes (Trie.left input) + audit_trie_nodes (Trie.right input) <=
    audit_trie_nodes input.
Proof.
  destruct input as [|node]; [reflexivity | destruct node];
    cbn [Trie.left Trie.right audit_trie_nodes audit_elements_nodes]; lia.
Qed.

(** Insertion adds at most one trie node for each bit of the encoded key. *)
Lemma prepare_trie_set_size A code value (input : Trie.t A) :
  audit_trie_nodes (Trie.set code value input) <= audit_trie_nodes input + Pos.size_nat code.
Proof.
  revert input; induction code as [code IH | code IH |]; intro input;
    cbn [Trie.set Pos.size_nat].
  - pose proof (prepare_trie_node_size A (Trie.left input) (Trie.set code value (Trie.right input))
      (Trie.value input)) as Hnode.
    pose proof (prepare_trie_children_size A input) as Hchildren.
    specialize (IH (Trie.right input)); lia.
  - pose proof (prepare_trie_node_size A (Trie.set code value (Trie.left input)) (Trie.right input)
      (Trie.value input)) as Hnode.
    pose proof (prepare_trie_children_size A input) as Hchildren.
    specialize (IH (Trie.left input)); lia.
  - pose proof (prepare_trie_node_size A (Trie.left input) (Trie.right input) (Some value))
      as Hnode.
    pose proof (prepare_trie_children_size A input) as Hchildren; lia.
Qed.

Lemma prepare_trie_union_ne_size A (combine : A -> A -> A) (node : Trie.ne A) :
  forall other,
    audit_trie_nodes (Trie.merge_ne (Trie.union_opt combine) (fun tr => tr) (fun tr => tr)
      node other) <= audit_elements_nodes node + audit_trie_nodes other.
Proof.
  induction node as [r IHr | value | value r IHr | l IHl | l IHl r IHr | l IHl value |
    l IHl value r IHr]; intros [|other].
  all: cbn [Trie.merge_ne audit_trie_nodes]; try lia.
  all: try specialize (IHl (Trie.left (Trie.Nodes other))).
  all: try specialize (IHr (Trie.right (Trie.Nodes other))).
  all: pose proof (prepare_trie_children_size A (Trie.Nodes other)) as Hchildren.
  all: match goal with
  | |- context [Trie.node ?left ?value ?right] =>
      pose proof (prepare_trie_node_size A left right value) as Hnode
  end.
  all: cbn [audit_trie_nodes] in Hchildren; cbn [audit_elements_nodes] in *; lia.
Qed.

(** Set union does not create nodes beyond those present in its two inputs. *)
Lemma prepare_set_union_size K (E : encoding K) (left right : FinSet.t K) :
  audit_trie_nodes (FinSet.union E left right) <= audit_trie_nodes left + audit_trie_nodes right.
Proof.
  destruct left as [|node]; cbn [FinSet.union Map.union_with Trie.union_with Trie.merge
    audit_trie_nodes]; [lia |].
  apply prepare_trie_union_ne_size.
Qed.

Lemma prepare_positive_width_value code : Pos.size_nat code <= Pos.to_nat code.
Proof.
  induction code as [code IH | code IH |]; cbn [Pos.size_nat].
  - rewrite Pos2Nat.inj_xI; lia.
  - rewrite Pos2Nat.inj_xO; lia.
  - reflexivity.
Qed.

Lemma prepare_nat_width_value n : Pos.size_nat (encode nat_encoding n) <= S n.
Proof.
  change (Pos.size_nat (Pos.of_succ_nat n) <= S n).
  pose proof (prepare_positive_width_value (Pos.of_succ_nat n)) as Hwidth.
  rewrite SuccNat2Pos.id_succ in Hwidth; exact Hwidth.
Qed.

(** Constructing a finite set charges each encoded position at most once per input occurrence. *)
Lemma prepare_set_fold_size (xs : list nat) input :
  audit_trie_nodes (fold_left (fun set key => FinSet.add nat_encoding key set) xs input) <=
    audit_trie_nodes input + fold_right (fun key n => S key + n) 0 xs.
Proof.
  revert input; induction xs as [|x xs IH]; intro input; cbn [fold_left fold_right].
  - lia.
  - specialize (IH (FinSet.add nat_encoding x input)).
    pose proof (prepare_trie_set_size (nat * unit)%type (encode nat_encoding x) (x, tt) input)
      as Hset.
    pose proof (prepare_nat_width_value x) as Hwidth.
    change (audit_trie_nodes (FinSet.add nat_encoding x input) <=
      audit_trie_nodes input + Pos.size_nat (encode nat_encoding x)) in Hset.
    lia.
Qed.

Lemma prepare_set_of_list_size xs :
  audit_trie_nodes (FinSet.of_list nat_encoding xs) <=
    fold_right (fun key n => S key + n) 0 xs.
Proof.
  unfold FinSet.of_list; pose proof (prepare_set_fold_size xs FinSet.empty) as H.
  change (audit_trie_nodes (fold_left (fun set key => FinSet.add nat_encoding key set) xs
    FinSet.empty) <= 0 + fold_right (fun key n => S key + n) 0 xs) in H.
  exact H.
Qed.

Lemma prepare_atom_vars_size P (a : atom P) :
  fold_right (fun key n => S key + n) 0 (atom_vars a) <= mat_index_terms_input (args a).
Proof.
  unfold atom_vars, mat_index_terms_input.
  induction (args a) as [|t terms IH]; cbn [flat_map fold_right].
  - lia.
  - destruct t; cbn in *; lia.
Qed.

(** Extending the bound set costs no more nodes than the atom's input allowance. *)
Lemma prepare_bound_add_size P bound (a : atom P) :
  audit_trie_nodes (fst (mat_bound_add bound a)) <=
    audit_trie_nodes bound + mat_index_terms_input (args a).
Proof.
  pose proof (proj1 (proj2 mat_join_syntax_erasure) P bound a) as Hvalue.
  rewrite Hvalue; unfold bound_add.
  pose proof (prepare_set_union_size nat nat_encoding bound
    (FinSet.of_list nat_encoding (atom_vars a))) as Hunion.
  pose proof (prepare_set_of_list_size (atom_vars a)) as Hset.
  pose proof (prepare_atom_vars_size P a) as Hatoms; lia.
Qed.

(** Adding an atom's variables leaves enough of the original measure for the tail. *)
Lemma prepare_nested_tail_size P (E : encoding P) relations a atoms bound :
  rules_nested_prepare_input_size E relations atoms (fst (mat_bound_add bound a)) <=
    rules_nested_prepare_input_size E relations (a :: atoms) bound.
Proof.
  pose proof (prepare_bound_add_size P bound a) as Hbound.
  unfold rules_nested_prepare_input_size; cbn [fold_right].
  lia.
Qed.

Lemma prepare_work_append A (xs ys : list A) :
  mat_work (snd (mat_append xs ys)) = 200 * S (length xs).
Proof.
  induction xs as [|x xs IH]; cbn [mat_append].
  - rewrite prepare_work_mark, prepare_work_return; reflexivity.
  - rewrite prepare_work_mark, prepare_work_bind, IH, prepare_work_return; cbn [length]; lia.
Qed.

Lemma prepare_atom_vars_work_terms terms :
  mat_work (snd (mat_flatmap mat_term_vars terms)) <= 700 * S (length terms).
Proof.
  induction terms as [|t terms IH]; cbn [mat_flatmap].
  - rewrite prepare_work_mark, prepare_work_return; cbn [length]; lia.
  - rewrite prepare_work_mark, !prepare_work_bind, prepare_work_append.
    unfold mat_term_vars; destruct t as [v | c]; cbn [mat_mark mat_return fst snd length].
    + change (100 + (200 + (mat_work (snd (mat_flatmap mat_term_vars terms)) + 400)) <=
        700 * S (S (length terms))); lia.
    + change (100 + (200 + (mat_work (snd (mat_flatmap mat_term_vars terms)) + 200)) <=
        700 * S (S (length terms))); lia.
Qed.

Lemma prepare_nat_encoder_work v :
  audit_nat_events_work (snd (audit_nat_encode v)) <= 4 * (S v) * (S v).
Proof.
  pose proof (audit_nat_encode_count v) as Hcount.
  pose proof (prepare_nat_width_value v) as Hwidth.
  unfold audit_nat_events_work; nia.
Qed.

Lemma prepare_nat_set_budget xs :
  audit_finset_of_list_budget audit_nat_encode audit_nat_events_work xs <=
    24 * (1 + fold_right (fun key n => S key + n) 0 xs) *
      (1 + fold_right (fun key n => S key + n) 0 xs).
Proof.
  induction xs as [|x xs IH].
  - cbn [audit_finset_of_list_budget]; lia.
  - cbn [audit_finset_of_list_budget fold_right].
    pose proof (prepare_nat_encoder_work x) as Hwork.
    pose proof (prepare_nat_width_value x) as Hwidth.
    pose proof (audit_nat_encode_erases x) as Hvalue.
    rewrite Hvalue; nia.
Qed.

Lemma prepare_work_lift A E site size work (run : A * list E) :
  mat_work (snd (mat_lift site size work run)) = work (snd run).
Proof.
  exact (mat_lift_work site size work run).
Qed.

Lemma prepare_terms_length terms : length terms <= mat_index_terms_input terms.
Proof.
  unfold mat_index_terms_input; induction terms as [|t terms IH]; cbn [fold_right length].
  - lia.
  - destruct t; lia.
Qed.

(** Variable collection and set union are bounded by their original atom and bound inputs. *)
Lemma prepare_bound_add_work P bound (a : atom P) :
  mat_work (snd (mat_bound_add bound a)) <=
    1000 * (1 + mat_index_terms_input (args a) + audit_trie_nodes bound) *
      (1 + mat_index_terms_input (args a) + audit_trie_nodes bound).
Proof.
  unfold mat_bound_add; rewrite !prepare_work_bind.
  unfold mat_atom_vars, mat_of_list, mat_union; rewrite !prepare_work_lift.
  pose proof (prepare_atom_vars_work_terms (args a)) as Hvars.
  pose proof (prepare_terms_length (args a)) as Hlength.
  pose proof (mat_atom_vars_value P a) as Hvalue.
  unfold mat_atom_vars in Hvalue; rewrite Hvalue, mat_lift_erases.
  pose proof (audit_finset_of_list_source_bound _ _ audit_nat_encode audit_nat_events_work
    (atom_vars a)) as Hsetwork.
  pose proof (prepare_nat_set_budget (atom_vars a)) as Hbudget.
  pose proof (prepare_atom_vars_size P a) as Hsize.
  pose proof (audit_finset_union_source_bound nat bound
    (fst (audit_finset_of_list audit_nat_encode (atom_vars a)))) as Hunion.
  set (measure := 1 + mat_index_terms_input (args a) + audit_trie_nodes bound) in *.
  assert (Hmeasure : 1 <= measure) by (unfold measure; lia).
  assert (Hvars_bound : S (length (args a)) <= measure) by (unfold measure; lia).
  assert (Hsum_bound : 1 + fold_right (fun key n => S key + n) 0 (atom_vars a) <= measure)
    by (unfold measure; lia).
  assert (Hnode_bound : audit_trie_nodes bound <= measure) by (unfold measure; lia).
  assert (Hsq : measure <= measure * measure) by nia.
  assert (Hsum_sq :
    (1 + fold_right (fun key n => S key + n) 0 (atom_vars a)) *
      (1 + fold_right (fun key n => S key + n) 0 (atom_vars a)) <= measure * measure).
  { nia. }
  set (square := measure * measure) in *.
  replace (1000 * measure * measure) with (1000 * square) by (unfold square; nia).
  assert (Hbudget' : audit_finset_of_list_budget audit_nat_encode audit_nat_events_work
    (atom_vars a) <= 24 * square) by nia.
  clear Hbudget Hsum_sq.
  assert (Hv : mat_work (snd (mat_flatmap mat_term_vars (args a))) <= 700 * square) by lia.
  assert (Hu : CollectionsAuditUnion.audit_finset_union_source_work
    (snd (CollectionsAuditUnion.audit_finset_union bound
      (fst (audit_finset_of_list audit_nat_encode (atom_vars a))))) <= 16 * square) by lia.
  assert (Hs : audit_finset_source_work audit_nat_events_work
    (snd (audit_finset_of_list audit_nat_encode (atom_vars a))) <= 24 * square) by lia.
  eapply Nat.le_trans with (m := 700 * square + (24 * square + 16 * square)).
  2: { change (700 * square + (24 * square + 16 * square) <= 1000 * square); lia. }
  apply Nat.add_le_mono; [exact Hv | apply Nat.add_le_mono; assumption].
Qed.

(** * Relation lookup and input measures *)

Lemma prepare_get_work P A (E : encoding P) key (input : Map.t P A) :
  mat_work (snd (mat_get E key input)) <= 1 + 5 * Pos.size_nat (encode E key).
Proof.
  unfold mat_get; rewrite prepare_work_bind.
  pose proof (rules_probe_map_get_trace_bound (K := P) (V := A) (encode E key) input) as Hget.
  unfold mat_encode; cbn [fst].
  destruct (audit_map_code_get (encode E key) input) as [value events] eqn:Hrun.
  cbn in Hget.
  unfold mat_work; cbn [snd fold_right mat_frame_work]; lia.
Qed.

Lemma prepare_entry_weight_in P (entry : P * list tuple) entries :
  In entry entries -> mat_index_rows_input (snd entry) <=
    fold_right (fun e n => mat_index_rows_input (snd e) + n) 0 entries.
Proof.
  induction entries as [|head tail IH]; cbn; intros Hin.
  - contradiction.
  - destruct Hin as [Heq | Hin]; [subst; lia | specialize (IH Hin); lia].
Qed.

(** A lookup's rows occur among enumerated values even in an arbitrary raw trie. *)
Lemma prepare_lookup_rows_size P (E : encoding P) key relations :
  mat_index_rows_input (join_relation_rows E relations key) <=
    1 + fold_right (fun entry n => mat_index_rows_input (snd entry) + n) 0
      (Map.elements relations).
Proof.
  unfold join_relation_rows, Map.get, Map.code_get.
  destruct (Trie.get (encode E key) relations) as [[stored rows] |] eqn:Hget; cbn.
  - assert (Hin : In (stored, rows) (Map.elements relations)).
    { unfold Map.elements; apply in_map_iff.
      exists (encode E key, (stored, rows)); split; [reflexivity |].
      eapply Trie.elements_complete; exact Hget. }
    pose proof (prepare_entry_weight_in P (stored, rows) (Map.elements relations) Hin) as Hweight.
    cbn in Hweight; lia.
  - change (1 <= 1 + fold_right (fun entry n => mat_index_rows_input (snd entry) + n) 0
      (Map.elements relations)); lia.
Qed.

Lemma prepare_atoms_measure_length P (E : encoding P) atoms :
  length atoms <= fold_right (fun a n => 1 + Pos.size_nat (encode E (pred a)) +
    mat_index_terms_input (args a) + n) 0 atoms.
Proof.
  induction atoms as [|a atoms IH]; cbn [fold_right length]; lia.
Qed.

Lemma prepare_nested_size_components P (E : encoding P) relations a atoms bound :
  let size := rules_nested_prepare_input_size E relations (a :: atoms) bound in
  1 <= size /\
  S (mat_index_terms_input (args a)) <= size /\
  1 + mat_index_terms_input (args a) + audit_trie_nodes bound <= size /\
  Pos.size_nat (encode E (pred a)) <= size /\
  mat_index_rows_input (join_relation_rows E relations (pred a)) <= size /\
  S (length (a :: atoms)) <= size.
Proof.
  pose proof (prepare_lookup_rows_size P E (pred a) relations) as Hrows.
  pose proof (prepare_atoms_measure_length P E atoms) as Hlength.
  unfold rules_nested_prepare_input_size; cbn [fold_right length]; lia.
Qed.

Lemma prepare_nested_size_positive P (E : encoding P) relations atoms bound :
  1 <= rules_nested_prepare_input_size E relations atoms bound.
Proof.
  unfold rules_nested_prepare_input_size; lia.
Qed.

Lemma prepare_index_work_uniform bound terms rows size :
  1 <= size -> S (mat_index_terms_input terms) <= size -> mat_index_rows_input rows <= size ->
  mat_work (snd (mat_build_index_full bound terms rows)) <=
    2000 * (size * size * size * size).
Proof.
  intros Hpositive Hterms Hrows.
  pose proof (mat_build_index_work_bound bound terms rows) as Hwork.
  pose proof (mat_index_rows_length_bound rows) as Hlength.
  cbn zeta in Hwork.
  set (t := S (mat_index_terms_input terms)) in *.
  set (r := mat_index_rows_input rows) in *.
  assert (Hsquare : t * t <= size * size) by nia.
  assert (Hcube : t * t * t <= size * size * size) by nia.
  assert (Hmain : length rows * (300 * t * t * t + 237) <=
    size * (300 * size * size * size + 237)) by nia.
  assert (Hfour : size <= size * size * size * size) by nia.
  set (four := size * size * size * size) in *.
  assert (Hfactor : size * (300 * size * size * size + 237) =
    300 * four + 237 * size) by (unfold four; nia).
  rewrite Hfactor in Hmain.
  clear Hcube Hsquare Hfactor Hlength Hterms.
  clearbody four t r; lia.
Qed.

(** Nested work remains bounded while the bound set grows within the input measure. *)
Lemma prepare_nested_work_uniform P (E : encoding P) relations atoms size :
  forall bound, rules_nested_prepare_input_size E relations atoms bound <= size ->
  mat_work (snd (rules_prepare_nested_full E relations atoms bound)) <=
    5000 * S (length atoms) * (size * size * size * size).
Proof.
  induction atoms as [|a atoms IH]; intros bound Hmeasure.
  - change (mat_work (snd (mat_mark 201 (mat_return ([] : list nested_search)))) <=
      5000 * S (length ([] : list (atom P))) * (size * size * size * size)).
    rewrite prepare_work_mark, prepare_work_return.
    pose proof (prepare_nested_size_positive P E relations [] bound) as Hpositive.
    assert (Hs2 : 1 <= size * size) by nia.
    assert (Hs3 : 1 <= size * size * size) by nia.
    assert (Hfour : 1 <= size * size * size * size) by nia.
    cbn [length]; nia.
  - pose proof (prepare_nested_size_components P E relations a atoms bound) as Hcomponents.
    cbn zeta in Hcomponents.
    destruct Hcomponents as [Hpositive [Hterms [Hbound [Hcode [Hrows Hlength]]]]].
    assert (Hsize : 1 <= size) by lia.
    assert (Hterm_size : S (mat_index_terms_input (args a)) <= size) by lia.
    assert (Hbound_size : 1 + mat_index_terms_input (args a) + audit_trie_nodes bound <= size)
      by lia.
    assert (Hrow_size : mat_index_rows_input (join_relation_rows E relations (pred a)) <= size)
      by lia.
    pose proof (prepare_index_work_uniform bound (args a)
      (join_relation_rows E relations (pred a)) size Hsize Hterm_size Hrow_size) as Hindex.
    pose proof (prepare_get_work P (list tuple) E (pred a) relations) as Hget.
    pose proof (prepare_bound_add_work P bound a) as Hadd.
    pose proof (prepare_nested_tail_size P E relations a atoms bound) as Htail_size.
    specialize (IH (fst (mat_bound_add bound a)) ltac:(lia)).
    assert (Hs2 : 1 <= size * size) by nia.
    assert (Hs3 : size <= size * size * size) by nia.
    assert (Hsquare : size * size <= size * size * size * size) by nia.
    assert (Hfour : size <= size * size * size * size) by nia.
    assert (Hadd' : mat_work (snd (mat_bound_add bound a)) <=
      1000 * (size * size * size * size)) by nia.
    assert (Hget' : mat_work (snd (mat_get E (pred a) relations)) <=
      6 * (size * size * size * size)) by nia.
    change (mat_work (snd (mat_mark 201
      (mat_bind (mat_get E (pred a) relations) (fun raw =>
        mat_bind (mat_build_index_full bound (args a)
          (match raw with Some rows => rows | None => [] end)) (fun index =>
        mat_bind (mat_bound_add bound a) (fun next_bound =>
        mat_bind (rules_prepare_nested_full E relations atoms next_bound) (fun tail =>
          mat_return (NestedSearch bound (args a) index :: tail)))))))) <=
      5000 * S (length (a :: atoms)) * (size * size * size * size)).
    rewrite prepare_work_mark, !prepare_work_bind, prepare_get_value, prepare_work_return.
    fold (join_relation_rows E relations (pred a)).
    set (four := size * size * size * size) in *.
    cbn [length].
    nia.
Qed.

Lemma prepare_nested_length_size P (E : encoding P) relations atoms bound :
  S (length atoms) <= rules_nested_prepare_input_size E relations atoms bound.
Proof.
  destruct atoms as [|a atoms].
  - pose proof (prepare_nested_size_positive P E relations [] bound); cbn [length]; assumption.
  - exact (proj2 (proj2 (proj2 (proj2 (proj2
      (prepare_nested_size_components P E relations a atoms bound)))))).
Qed.

Lemma prepare_nested_work_input_bound : rules_prepare_nested_full_input_bound_statement.
Proof.
  intros P E relations atoms bound.
  set (size := rules_nested_prepare_input_size E relations atoms bound).
  pose proof (prepare_nested_work_uniform P E relations atoms size bound (Nat.le_refl size))
    as Hwork.
  pose proof (prepare_nested_length_size P E relations atoms bound) as Hlength.
  pose proof (prepare_nested_size_positive P E relations atoms bound) as Hpositive.
  change (S (length atoms) <= size) in Hlength.
  change (1 <= size) in Hpositive.
  assert (Hpow : Nat.pow size 5 <= Nat.pow size 16).
  { apply Nat.pow_le_mono_r; lia. }
  assert (Hfive : size * (size * size * size * size) = Nat.pow size 5).
  { cbn [Nat.pow]; nia. }
  unfold rules_nested_prepare_input_budget; fold size.
  eapply Nat.le_trans; [exact Hwork |].
  eapply Nat.le_trans with (m := 5000 * size * (size * size * size * size)).
  - apply Nat.mul_le_mono_r, Nat.mul_le_mono_l; exact Hlength.
  - rewrite <- Nat.mul_assoc, Hfive.
    eapply Nat.le_trans.
    + apply Nat.mul_le_mono_l; exact Hpow.
    + apply Nat.mul_le_mono_r; nia.
Qed.

(** Nested source adequacy combines actual callback receipts with the internal work bound. *)
Theorem rules_nested_prepare_source : rules_nested_prepare_source_statement.
Proof.
  apply prepare_nested_source_given.
  - exact mat_index_full_erases.
  - exact prepare_nested_work_input_bound.
Qed.

(** * Multiway preparation work *)

Lemma prepare_variable_index_work_uniform bound terms v rows size :
  1 <= size -> S (mat_index_terms_input terms) <= size -> S v <= size ->
  mat_index_rows_input rows <= size ->
  mat_work (snd (mat_build_variable_full bound terms v rows)) <=
    2000 * (size * size * size * size).
Proof.
  intros Hpositive Hterms Hv Hrows.
  pose proof (mat_build_variable_work_bound bound terms v rows) as Hwork.
  pose proof (mat_index_rows_length_bound rows) as Hlength.
  cbn zeta in Hwork.
  set (t := S (mat_index_terms_input terms)) in *.
  set (r := mat_index_rows_input rows) in *.
  assert (Hsquare : t * t <= size * size) by nia.
  assert (Hcube : t * t * t <= size * size * size) by nia.
  assert (Hmain : length rows * (1300 * t * t * t + 13 * S v + 200) <=
    size * (1300 * size * size * size + 13 * size + 200)) by nia.
  assert (Hother : r * (2 * t + 98) <= size * (2 * size + 98)).
  { eapply Nat.le_trans with (m := size * (2 * t + 98)).
    - apply Nat.mul_le_mono_r; exact Hrows.
    - apply Nat.mul_le_mono_l; lia. }
  assert (Hs2 : size <= size * size) by nia.
  assert (Hs3 : size * size <= size * size * size) by nia.
  assert (Hfour : size * size * size <= size * size * size * size) by nia.
  set (four := size * size * size * size) in *.
  assert (Hfactor : size * (1300 * size * size * size + 13 * size + 200) =
    1300 * four + 13 * (size * size) + 200 * size) by (unfold four; nia).
  rewrite Hfactor in Hmain.
  assert (Hsquare_four : size * size <= four) by lia.
  assert (Hsize_four : size <= four) by lia.
  replace (size * (2 * size + 98)) with (2 * (size * size) + 98 * size) in Hother by nia.
  set (square := size * size) in *.
  clear Hcube Hsquare Hfactor Hlength Hterms Hv.
  clearbody four square t r; lia.
Qed.

Lemma prepare_nat_add_size v bound :
  audit_trie_nodes (fst (mat_nat_add v bound)) <= audit_trie_nodes bound + S v.
Proof.
  rewrite prepare_nat_add_value.
  pose proof (prepare_trie_set_size (nat * unit)%type (encode nat_encoding v) (v, tt) bound)
    as Hset.
  change (audit_trie_nodes (FinSet.add nat_encoding v bound) <=
    audit_trie_nodes bound + Pos.size_nat (encode nat_encoding v)) in Hset.
  pose proof (prepare_nat_width_value v); lia.
Qed.

(** The variable allowance pays for adding that variable to the next bound set. *)
Lemma prepare_multiway_tail_size P (E : encoding P) relations v vars bound atoms :
  rules_multiway_prepare_input_size E relations vars (fst (mat_nat_add v bound)) atoms <=
    rules_multiway_prepare_input_size E relations (v :: vars) bound atoms.
Proof.
  pose proof (prepare_nat_add_size v bound) as Hadd.
  unfold rules_multiway_prepare_input_size, rules_nested_prepare_input_size; cbn [fold_right]; lia.
Qed.

Lemma prepare_atom_weight_in P (E : encoding P) a atoms :
  In a atoms ->
  1 + Pos.size_nat (encode E (pred a)) + mat_index_terms_input (args a) <=
    fold_right (fun item n => 1 + Pos.size_nat (encode E (pred item)) +
      mat_index_terms_input (args item) + n) 0 atoms.
Proof.
  induction atoms as [|head tail IH]; intro Hin.
  - contradiction.
  - cbn [In] in Hin.
    change (1 + Pos.size_nat (encode E (pred a)) + mat_index_terms_input (args a) <=
      1 + Pos.size_nat (encode E (pred head)) + mat_index_terms_input (args head) +
        fold_right (fun item n => 1 + Pos.size_nat (encode E (pred item)) +
          mat_index_terms_input (args item) + n) 0 tail).
    destruct Hin as [Heq | Hin]; [subst; lia | specialize (IH Hin); lia].
Qed.

Lemma prepare_atoms_dimensions P (E : encoding P) relations atoms bound size :
  rules_nested_prepare_input_size E relations atoms bound <= size ->
  Forall (fun a => S (mat_index_terms_input (args a)) <= size /\
    Pos.size_nat (encode E (pred a)) <= size /\
    mat_index_rows_input (join_relation_rows E relations (pred a)) <= size) atoms.
Proof.
  intro Hsize; apply Forall_forall; intros a Hin.
  pose proof (prepare_atom_weight_in P E a atoms Hin) as Hatom.
  pose proof (prepare_lookup_rows_size P E (pred a) relations) as Hrows.
  unfold rules_nested_prepare_input_size in Hsize; repeat split; lia.
Qed.

Lemma prepare_multiway_size_components P (E : encoding P) relations v vars bound atoms :
  let size := rules_multiway_prepare_input_size E relations (v :: vars) bound atoms in
  1 <= size /\ S v <= size /\
  rules_nested_prepare_input_size E relations atoms bound <= size /\
  S (length (v :: vars)) <= size.
Proof.
  pose proof (prepare_nested_size_positive P E relations atoms bound) as Hnested.
  assert (Hlength : length vars <= fold_right (fun x n => 1 + x + n) 0 vars).
  { induction vars as [|x vars IH].
    - reflexivity.
    - change (S (length vars) <= 1 + x + fold_right (fun x n => 1 + x + n) 0 vars); lia. }
  unfold rules_multiway_prepare_input_size; cbn [fold_right length]; lia.
Qed.

Lemma prepare_has_variable_work P v (a : atom P) size :
  1 <= size -> S (mat_index_terms_input (args a)) <= size -> S v <= size ->
  mat_work (snd (mat_has_variable v a)) <= 1000 * (size * size).
Proof.
  intros Hsize Hterms Hv.
  unfold mat_has_variable; rewrite !prepare_work_bind.
  unfold mat_atom_vars, mat_of_list; rewrite !prepare_work_lift.
  pose proof (mat_atom_vars_value P a) as Hvalue; unfold mat_atom_vars in Hvalue.
  rewrite Hvalue, mat_lift_erases.
  pose proof (prepare_atom_vars_work_terms (args a)) as Hvars.
  pose proof (prepare_terms_length (args a)) as Hlength.
  pose proof (audit_finset_of_list_source_bound _ _ audit_nat_encode audit_nat_events_work
    (atom_vars a)) as Hsetwork.
  pose proof (prepare_nat_set_budget (atom_vars a)) as Hbudget.
  pose proof (prepare_atom_vars_size P a) as Hsum.
  pose proof (mat_bound_term_work_bound (fst (audit_finset_of_list audit_nat_encode (atom_vars a)))
    (TVar v)) as Hmem.
  unfold mat_bound_term in Hmem; rewrite prepare_work_mark, prepare_work_lift in Hmem.
  cbn [mat_term_index_size] in Hmem.
  assert (Hsumsize : 1 + fold_right (fun key n => S key + n) 0 (atom_vars a) <= size) by lia.
  assert (Hsum_sq : (1 + fold_right (fun key n => S key + n) 0 (atom_vars a)) *
    (1 + fold_right (fun key n => S key + n) 0 (atom_vars a)) <= size * size) by nia.
  assert (Hv_sq : S v * S v <= size * size) by nia.
  assert (Hlinear : size <= size * size) by nia.
  set (square := size * size) in *.
  assert (Hbudget' : audit_finset_of_list_budget audit_nat_encode audit_nat_events_work
    (atom_vars a) <= 24 * square) by nia.
  assert (Hvars' : mat_work (snd (mat_flatmap mat_term_vars (args a))) <= 700 * square) by lia.
  assert (Hmem' : audit_finset_source_work audit_nat_events_work
    (snd (audit_finset_mem audit_nat_encode v
      (fst (audit_finset_of_list audit_nat_encode (atom_vars a))))) <= 110 * square) by nia.
  assert (Hset' : audit_finset_source_work audit_nat_events_work
    (snd (audit_finset_of_list audit_nat_encode (atom_vars a))) <= 24 * square) by lia.
  eapply Nat.le_trans with (m := 700 * square + (24 * square + 110 * square)).
  - apply Nat.add_le_mono; [exact Hvars' | apply Nat.add_le_mono; assumption].
  - lia.
Qed.

Lemma prepare_filter_work_uniform P v (atoms : list (atom P)) size :
  1 <= size -> S v <= size ->
  Forall (fun a => S (mat_index_terms_input (args a)) <= size) atoms ->
  mat_work (snd (mat_atoms_with v atoms)) <= 1500 * S (length atoms) * (size * size).
Proof.
  intros Hsize Hv Hatoms; unfold mat_atoms_with.
  induction Hatoms as [|a atoms Hterms Hatoms IH].
  - change (mat_work (snd (mat_mark 4 (mat_return ([] : list (atom P))))) <=
      1500 * S (length ([] : list (atom P))) * (size * size)).
    rewrite prepare_work_mark, prepare_work_return; cbn [length].
    assert (Hsquare : 1 <= size * size) by nia; nia.
  - change (mat_work (snd (mat_mark 4
      (mat_bind (mat_has_variable v a) (fun keep =>
        mat_bind (mat_filter (mat_has_variable v) atoms) (fun tail =>
          mat_return (if keep then a :: tail else tail)))))) <=
      1500 * S (length (a :: atoms)) * (size * size)).
    rewrite prepare_work_mark, !prepare_work_bind, prepare_work_return.
    pose proof (prepare_has_variable_work P v a size Hsize Hterms Hv) as Hhead.
    assert (Hsquare : 1 <= size * size) by nia.
    set (square := size * size) in *; cbn [length]; nia.
Qed.

Lemma prepare_variable_map_work_uniform P (E : encoding P) relations bound v atoms size :
  1 <= size -> S v <= size ->
  Forall (fun a => S (mat_index_terms_input (args a)) <= size /\
    Pos.size_nat (encode E (pred a)) <= size /\
    mat_index_rows_input (join_relation_rows E relations (pred a)) <= size) atoms ->
  mat_work (snd (rules_variable_map_full E relations bound v atoms)) <=
    3000 * S (length atoms) * (size * size * size * size).
Proof.
  intros Hsize Hv Hatoms; induction Hatoms as [|a atoms [Hterms [Hcode Hrows]] Hatoms IH].
  - change (mat_work (snd (mat_mark 221 (mat_return ([] : list variable_search)))) <=
      3000 * S (length ([] : list (atom P))) * (size * size * size * size)).
    rewrite prepare_work_mark, prepare_work_return; cbn [length].
    assert (Hs2 : 1 <= size * size) by nia.
    assert (Hs3 : 1 <= size * size * size) by nia.
    assert (Hfour : 1 <= size * size * size * size) by nia; nia.
  - pose proof (prepare_variable_index_work_uniform bound (args a) v
      (join_relation_rows E relations (pred a)) size Hsize Hterms Hv Hrows) as Hindex.
    pose proof (prepare_get_work P (list tuple) E (pred a) relations) as Hget.
    assert (Hs2 : 1 <= size * size) by nia.
    assert (Hs3 : size <= size * size * size) by nia.
    assert (Hfour : size <= size * size * size * size) by nia.
    assert (Hget' : mat_work (snd (mat_get E (pred a) relations)) <=
      6 * (size * size * size * size)) by nia.
    change (mat_work (snd (mat_mark 221
      (mat_bind (mat_get E (pred a) relations) (fun raw =>
        mat_bind (mat_build_variable_full bound (args a) v
          (match raw with Some rows => rows | None => [] end)) (fun index =>
        mat_bind (rules_variable_map_full E relations bound v atoms) (fun tail =>
          mat_return (VariableSearch (args a) index :: tail))))))) <=
      3000 * S (length (a :: atoms)) * (size * size * size * size)).
    rewrite prepare_work_mark, !prepare_work_bind, prepare_get_value, prepare_work_return.
    fold (join_relation_rows E relations (pred a)).
    set (four := size * size * size * size) in *; cbn [length]; nia.
Qed.

Lemma prepare_filter_length A (keep : A -> bool) xs : length (filter keep xs) <= length xs.
Proof.
  induction xs as [|x xs IH]; cbn [filter length]; [lia |].
  destruct (keep x); cbn [length]; lia.
Qed.

Lemma prepare_variable_work_uniform P (E : encoding P) relations bound v atoms size :
  1 <= size -> S v <= size ->
  Forall (fun a => S (mat_index_terms_input (args a)) <= size /\
    Pos.size_nat (encode E (pred a)) <= size /\
    mat_index_rows_input (join_relation_rows E relations (pred a)) <= size) atoms ->
  mat_work (snd (rules_prepare_variable_full E relations bound v atoms)) <=
    5000 * S (length atoms) * (size * size * size * size).
Proof.
  intros Hsize Hv Hatoms.
  assert (Hterms : Forall (fun a => S (mat_index_terms_input (args a)) <= size) atoms).
  { eapply Forall_impl; [|exact Hatoms]; intros a [H _]; exact H. }
  pose proof (prepare_filter_work_uniform P v atoms size Hsize Hv Hterms) as Hfilter.
  pose proof (proj2 (proj2 (proj2 (proj2 mat_join_syntax_erasure))) P v atoms) as Hselected.
  set (selected := fst (mat_atoms_with v atoms)).
  assert (Hselection : selected = atoms_with_variable v atoms) by exact Hselected.
  assert (Hselected_atoms : Forall (fun a => S (mat_index_terms_input (args a)) <= size /\
    Pos.size_nat (encode E (pred a)) <= size /\
    mat_index_rows_input (join_relation_rows E relations (pred a)) <= size) selected).
  { rewrite Hselection; unfold atoms_with_variable.
    apply Forall_forall; intros a Hin; apply filter_In in Hin; destruct Hin as [Hin _].
    apply Forall_forall with (x := a) in Hatoms; assumption. }
  assert (Hselected_length : length selected <= length atoms).
  { rewrite Hselection; unfold atoms_with_variable; apply prepare_filter_length. }
  pose proof (prepare_variable_map_work_uniform P E relations bound v selected size
    Hsize Hv Hselected_atoms) as Hmap.
  unfold rules_prepare_variable_full; rewrite prepare_work_bind; fold selected.
  assert (Hs2 : 1 <= size * size) by nia.
  assert (Hsquare : size * size <= size * size * size * size) by nia.
  assert (Hfilter' : mat_work (snd (mat_atoms_with v atoms)) <=
    1500 * S (length atoms) * (size * size * size * size)).
  { eapply Nat.le_trans; [exact Hfilter |].
    apply Nat.mul_le_mono_l; exact Hsquare. }
  assert (Hmap' : mat_work (snd (rules_variable_map_full E relations bound v selected)) <=
    3000 * S (length atoms) * (size * size * size * size)).
  { eapply Nat.le_trans; [exact Hmap |].
    apply Nat.mul_le_mono_r, Nat.mul_le_mono_l; lia. }
  set (four := size * size * size * size) in *.
  set (count := S (length atoms)) in *.
  eapply Nat.le_trans with (m := 1500 * count * four + 3000 * count * four).
  - apply Nat.add_le_mono; assumption.
  - nia.
Qed.

Lemma prepare_nat_add_work v bound size :
  1 <= size -> S v <= size ->
  mat_work (snd (mat_nat_add v bound)) <= 1000 * (size * size).
Proof.
  intros Hsize Hv; unfold mat_nat_add; rewrite prepare_work_lift.
  pose proof (prepare_nat_encoder_work v) as Hencoder.
  pose proof (audit_nat_encode_erases v) as Hcode.
  pose proof (prepare_nat_width_value v) as Hwidth.
  unfold audit_finset_add.
  destruct (audit_nat_encode v) as [code events] eqn:Hrun; cbn in Hencoder, Hcode.
  change (code = encode nat_encoding v) in Hcode.
  rewrite <- Hcode in Hwidth.
  pose proof (rules_probe_update_trace_bound code (Some (v, tt)) bound) as Hupdate.
  unfold audit_trie_set.
  destruct (audit_trie_update code (Some (v, tt)) bound) as [out trace] eqn:Hupdate_run.
  cbn in Hupdate.
  unfold audit_finset_source_work; cbn [snd fold_right].
  assert (Hv_sq : S v * S v <= size * size) by nia.
  assert (Hlinear : size <= size * size) by nia.
  set (square := size * size) in *.
  change (audit_nat_events_work events <= 4 * S v * S v) in Hencoder.
  assert (Henc' : audit_nat_events_work events <= 4 * square) by nia.
  assert (Hupdate' : audit_trie_update_trace_source_work trace <= 16 * square) by nia.
  lia.
Qed.

Lemma prepare_multiway_size_positive P (E : encoding P) relations vars bound atoms :
  1 <= rules_multiway_prepare_input_size E relations vars bound atoms.
Proof.
  pose proof (prepare_nested_size_positive P E relations atoms bound) as Hnested.
  unfold rules_multiway_prepare_input_size; lia.
Qed.

(** Each iteration pays for selection and all selected variable indexes at the same input size. *)
Lemma prepare_multiway_work_uniform P (E : encoding P) relations vars atoms size :
  forall bound, rules_multiway_prepare_input_size E relations vars bound atoms <= size ->
  mat_work (snd (rules_prepare_multiway_full E relations vars bound atoms)) <=
    (7 * 1000) * S (length vars) * S (length atoms) * (size * size * size * size).
Proof.
  induction vars as [|v vars IH]; intros bound Hmeasure.
  - change (mat_work (snd (mat_mark 222 (mat_return ([] : list multiway_search)))) <=
      (7 * 1000) * S (length ([] : list nat)) * S (length atoms) * (size * size * size * size)).
    rewrite prepare_work_mark, prepare_work_return; cbn [length].
    pose proof (prepare_multiway_size_positive P E relations [] bound atoms) as Hpositive.
    assert (Hs2 : 1 <= size * size) by nia.
    assert (Hs3 : 1 <= size * size * size) by nia.
    assert (Hfour : 1 <= size * size * size * size) by nia; nia.
  - pose proof (prepare_multiway_size_components P E relations v vars bound atoms) as Hcomponents.
    cbn zeta in Hcomponents.
    destruct Hcomponents as [Hpositive [Hv [Hnested Hlength]]].
    assert (Hsize : 1 <= size) by lia.
    assert (Hv_size : S v <= size) by lia.
    pose proof (prepare_atoms_dimensions P E relations atoms bound size ltac:(lia)) as Hatoms.
    pose proof (prepare_variable_work_uniform P E relations bound v atoms size Hsize Hv_size Hatoms)
      as Hvariable.
    pose proof (prepare_nat_add_work v bound size Hsize Hv_size) as Hadd.
    pose proof (prepare_multiway_tail_size P E relations v vars bound atoms) as Htail_size.
    specialize (IH (fst (mat_nat_add v bound)) ltac:(lia)).
    assert (Hs2 : 1 <= size * size) by nia.
    assert (Hsquare : size * size <= size * size * size * size) by nia.
    assert (Hfour : 1 <= size * size * size * size) by nia.
    assert (Hadd' : mat_work (snd (mat_nat_add v bound)) <=
      1000 * (size * size * size * size)) by nia.
    change (mat_work (snd (mat_mark 222
      (mat_bind (rules_prepare_variable_full E relations bound v atoms) (fun domains =>
        mat_bind (mat_nat_add v bound) (fun next_bound =>
        mat_bind (rules_prepare_multiway_full E relations vars next_bound atoms) (fun tail =>
          mat_return (MultiwaySearch v bound domains :: tail))))))) <=
      (7 * 1000) * S (length (v :: vars)) * S (length atoms) * (size * size * size * size)).
    rewrite prepare_work_mark, !prepare_work_bind, prepare_work_return.
    set (four := size * size * size * size) in *.
    set (count := S (length atoms)) in *.
    cbn [length].
    assert (Hcount : 1 <= count) by (unfold count; lia).
    assert (Hreserve : 1000 * four + 200 <= 2000 * count * four) by nia.
    nia.
Qed.

Lemma prepare_multiway_lengths P (E : encoding P) relations vars bound atoms :
  S (length vars) <= rules_multiway_prepare_input_size E relations vars bound atoms /\
  S (length atoms) <= rules_multiway_prepare_input_size E relations vars bound atoms.
Proof.
  pose proof (prepare_nested_length_size P E relations atoms bound) as Hatoms.
  pose proof (prepare_nested_size_positive P E relations atoms bound) as Hpositive.
  assert (Hvars : length vars <= fold_right (fun x n => 1 + x + n) 0 vars).
  { induction vars as [|x vars IH].
    - reflexivity.
    - change (S (length vars) <= 1 + x + fold_right (fun x n => 1 + x + n) 0 vars); lia. }
  unfold rules_multiway_prepare_input_size; split; lia.
Qed.

Lemma prepare_multiway_work_input_bound P (E : encoding P) relations vars bound atoms :
  mat_work (snd (rules_prepare_multiway_full E relations vars bound atoms)) <=
    rules_multiway_prepare_input_budget E relations vars bound atoms.
Proof.
  set (size := rules_multiway_prepare_input_size E relations vars bound atoms).
  pose proof (prepare_multiway_work_uniform P E relations vars atoms size bound (Nat.le_refl size))
    as Hwork.
  pose proof (prepare_multiway_lengths P E relations vars bound atoms) as [Hvars Hatoms].
  pose proof (prepare_multiway_size_positive P E relations vars bound atoms) as Hpositive.
  change (S (length vars) <= size) in Hvars.
  change (S (length atoms) <= size) in Hatoms.
  change (1 <= size) in Hpositive.
  assert (Hcounts : S (length vars) * S (length atoms) <= size * size) by nia.
  assert (Hpow : Nat.pow size 6 <= Nat.pow size (18 + 2 * length vars)).
  { apply Nat.pow_le_mono_r; lia. }
  assert (Hsix : size * size * (size * size * size * size) = Nat.pow size 6).
  { cbn [Nat.pow]; nia. }
  unfold rules_multiway_prepare_input_budget; fold size.
  eapply Nat.le_trans; [exact Hwork |].
  replace ((7 * 1000) * S (length vars) * S (length atoms) * (size * size * size * size))
    with ((7 * 1000) * (S (length vars) * S (length atoms)) *
      (size * size * size * size)) by nia.
  eapply Nat.le_trans with (m := (7 * 1000) * (size * size) * (size * size * size * size)).
  - apply Nat.mul_le_mono_r, Nat.mul_le_mono_l; exact Hcounts.
  - rewrite <- Nat.mul_assoc, Hsix.
    eapply Nat.le_trans.
    + apply Nat.mul_le_mono_l; exact Hpow.
    + apply Nat.mul_le_mono_r; nia.
Qed.

(** Multiway source adequacy combines actual callback receipts with the internal work bound. *)
Theorem rules_multiway_prepare_source : rules_multiway_prepare_source_statement.
Proof.
  apply prepare_multiway_source_given.
  - exact mat_index_full_erases.
  - exact prepare_multiway_work_input_bound.
Qed.
