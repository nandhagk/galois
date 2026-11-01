(** * Finite-universe adequacy

    Counted preparation and membership preserve the source universe predicate.
    For example, a tuple with a missing constant fails the same membership check.
    Builds on: RulesAuditUniverse and collection adequacy. *)

From Stdlib Require Import List Bool PeanoNat PArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet
  CollectionsAuditCost CollectionsAuditTrie CollectionsAuditTrieAdequacy
  CollectionsAuditFinSet CollectionsAuditFinSetAdequacy CollectionsAuditEncoding
  CollectionsAuditEncodingAdequacy.
From Galois.Rules Require Import RulesSyntax RulesStratify RulesCompile RulesAuditRelations
  RulesAuditRelationsAdequacy RulesAuditUniverse.
Import List.ListNotations.

(** * Predicate and constant extraction *)

(** Literal predicates retain their source order. *)
Lemma ru_literal_predicates_erases P (items : list (literal P)) :
    fst (ru_literal_predicates items) = map (fun l => pred (lit_atom l)) items.
Proof.
  induction items as [|item rest IH]; cbn [ru_literal_predicates map]; try reflexivity.
  destruct (ru_literal_predicates rest) as [tail events]. cbn in *. now rewrite IH.
Qed.

(** Rule predicates retain their source order. *)
Lemma ru_rule_predicates_erases P (items : list (rule P)) :
    fst (ru_rule_predicates items) = flat_map rule_predicates items.
Proof.
  induction items as [|item rest IH]; cbn [ru_rule_predicates flat_map]; try reflexivity.
  pose proof (ru_literal_predicates_erases P (body item)) as Hbody.
  destruct (ru_literal_predicates (body item)) as [ps events]. cbn in Hbody.
  destruct (ru_rule_predicates rest) as [tail te]. cbn in IH.
  unfold rule_predicates. cbn. now rewrite Hbody, IH.
Qed.

(** Fact predicates retain their source order. *)
Lemma ru_fact_predicates_erases P (facts : list (ground_atom P)) :
    fst (ru_fact_predicates facts) = map fst facts.
Proof.
  induction facts as [|[p row] rest IH]; cbn [ru_fact_predicates map]; try reflexivity.
  destruct (ru_fact_predicates rest) as [tail events]. cbn in *. now rewrite IH.
Qed.

(** Term extraction omits variables and retains constants in order. *)
Lemma ru_term_constants_erases P terms :
    fst (@ru_term_constants P terms) =
      flat_map (fun t =>
        match t with
        | TVar _ => []
        | TConst c => [c]
        end) terms.
Proof.
  induction terms as [|t rest IH]; cbn [ru_term_constants flat_map]; try reflexivity.
  destruct (ru_term_constants rest) as [tail events]. cbn in *.
  destruct t; cbn; now rewrite IH.
Qed.

(** Literal constant extraction agrees with the source atom traversal. *)
Lemma ru_literal_constants_erases P (items : list (literal P)) :
    fst (ru_literal_constants items) = flat_map (fun l => atom_constants (lit_atom l)) items.
Proof.
  induction items as [|item rest IH]; cbn [ru_literal_constants flat_map]; try reflexivity.
  pose proof (ru_term_constants_erases P (args (lit_atom item))) as Hhead.
  destruct (ru_term_constants (args (lit_atom item))) as [cs events]. cbn in Hhead.
  destruct (ru_literal_constants rest) as [tail te]. cbn in IH.
  unfold atom_constants. now rewrite Hhead, IH.
Qed.

(** Rule constant extraction agrees with the source rule traversal. *)
Lemma ru_rule_constants_erases P (items : list (rule P)) :
    fst (ru_rule_constants items) =
      flat_map (fun r => atom_constants (head r) ++
        flat_map (fun l => atom_constants (lit_atom l)) (body r)) items.
Proof.
  induction items as [|item rest IH]; cbn [ru_rule_constants flat_map]; try reflexivity.
  pose proof (ru_term_constants_erases P (args (head item))) as Hhead.
  destruct (ru_term_constants (args (head item))) as [cs events]. cbn in Hhead.
  pose proof (ru_literal_constants_erases P (body item)) as Hbody.
  destruct (ru_literal_constants (body item)) as [bs be]. cbn in Hbody.
  destruct (ru_rule_constants rest) as [tail te]. cbn in IH.
  unfold atom_constants. now rewrite Hhead, Hbody, IH.
Qed.

(** Fact constants retain the original tuple concatenation. *)
Lemma ru_fact_constants_erases P (facts : list (ground_atom P)) :
    fst (ru_fact_constants facts) = flat_map snd facts.
Proof.
  induction facts as [|[p row] rest IH]; cbn [ru_fact_constants flat_map]; try reflexivity.
  destruct (ru_fact_constants rest) as [tail events]. cbn in *. now rewrite IH.
Qed.

(** * Preparation and membership *)

(** Preparation stores the source predicate test, arity, and constant set. *)
Lemma rules_universe_prepare_erases P (prog : program P) facts p :
    fst (rules_universe_prepare_counted prog facts p) =
      (FinSet.mem (penc prog) p (preds prog facts), arity prog p, constants prog facts).
Proof.
  unfold rules_universe_prepare_counted, preds, constants.
  pose proof (ru_rule_predicates_erases P (rules prog)) as Hrp.
  destruct (ru_rule_predicates (rules prog)) as [rp rpe]. cbn in Hrp.
  pose proof (ru_fact_predicates_erases P facts) as Hfp.
  destruct (ru_fact_predicates facts) as [fp fpe]. cbn in Hfp.
  pose proof (audit_finset_of_list_erases _ _ (rules_encoder (penc prog)) (penc prog) (rp ++ fp)
    (fun _ _ => eq_refl)) as Hpset.
  destruct (audit_finset_of_list (rules_encoder (penc prog)) (rp ++ fp)) as [pset pse].
  cbn in Hpset.
  pose proof (audit_finset_mem_erases _ _ (rules_encoder (penc prog)) (penc prog) p pset eq_refl)
    as Hmem.
  destruct (audit_finset_mem (rules_encoder (penc prog)) p pset) as [present me]. cbn in Hmem.
  pose proof (ru_rule_constants_erases P (rules prog)) as Hrc.
  destruct (ru_rule_constants (rules prog)) as [rc rce]. cbn in Hrc.
  pose proof (ru_fact_constants_erases P facts) as Hfc.
  destruct (ru_fact_constants facts) as [fc fce]. cbn in Hfc.
  pose proof (audit_finset_of_list_erases _ _ audit_positive_encode positive_encoding (rc ++ fc)
    (fun x _ => audit_positive_encode_erases x)) as Hcset.
  destruct (audit_finset_of_list audit_positive_encode (rc ++ fc)) as [cset cse]. cbn in Hcset.
  cbn. rewrite Hmem, Hpset, Hrp, Hfp, Hcset, Hrc, Hfc. reflexivity.
Qed.

(** The counted constant check agrees with the source's universal membership test. *)
Lemma ru_constants_check_erases P set row :
    fst (@ru_constants_check P set row) = forallb (fun c => FinSet.mem positive_encoding c set) row.
Proof.
  induction row as [|c rest IH]; cbn [ru_constants_check forallb]; try reflexivity.
  pose proof (audit_finset_mem_erases _ _ audit_positive_encode positive_encoding c set
    (audit_positive_encode_erases c)) as Hmem.
  destruct (audit_finset_mem audit_positive_encode c set) as [present events]. cbn in Hmem.
  destruct (ru_constants_check set rest) as [tail te]. cbn in IH.
  now rewrite Hmem, IH.
Qed.

(** The counted unary comparison agrees with the standard equality test. *)
Lemma ru_nat_eqb_erases P lhs rhs : fst (@ru_nat_eqb P lhs rhs) = Nat.eqb lhs rhs.
Proof.
  revert rhs. induction lhs as [|lhs IH]; intros [|rhs]; cbn [ru_nat_eqb Nat.eqb];
    try reflexivity.
  specialize (IH rhs). destruct (ru_nat_eqb lhs rhs) as [answer events]. exact IH.
Qed.

(** Erasing preparation and checking gives the original universe predicate. *)
Theorem rules_universe_erasure : rules_universe_erasure_statement.
Proof.
  intros P prog facts p row.
  pose proof (rules_universe_prepare_erases P prog facts p) as Hprep.
  destruct (rules_universe_prepare_counted prog facts p) as [[[present n] set] events].
  cbn in Hprep. inversion Hprep; subst.
  unfold rules_universe_check_counted, in_universe.
  pose proof (ru_nat_eqb_erases P (length row) (arity prog p)) as Heq.
  destruct (ru_nat_eqb (length row) (arity prog p)) as [arity_ok ae]. cbn in Heq.
  pose proof (ru_constants_check_erases P (constants prog facts) row) as Hconstants.
  destruct (ru_constants_check (constants prog facts) row) as [constant_ok ce]. cbn in Hconstants.
  cbn. now rewrite Heq, Hconstants.
Qed.

(** * Per-event source costs *)

(** An event bounds its concrete source work by its selected allowance. *)
Definition rules_universe_event_bounded P (E : encoding P) (event : rules_universe_event P) :
    Prop :=
  rules_universe_event_work event <= rules_universe_event_budget E event.

(** Pointwise event bounds add across a complete universe trace. *)
Lemma rules_universe_trace_bounded P (E : encoding P) events :
    Forall (rules_universe_event_bounded P E) events ->
    rules_universe_work events <= rules_universe_budget E events.
Proof.
  unfold rules_universe_work, rules_universe_budget, rules_universe_event_bounded.
  intro Hgood. induction Hgood as [|event rest Hhead Htail IH]; cbn [fold_right]; lia.
Qed.

(** Predicate-set preparation includes every source encoder and trie update. *)
Lemma rules_universe_predicate_set_bounded P (E : encoding P) keys set events :
    audit_finset_of_list (rules_encoder E) keys = (set, events) ->
    rules_universe_event_bounded P E (RuPredicatesSet keys set events).
Proof.
  intro Hrun.
  pose proof (rules_relation_distinct_work P E keys set events Hrun) as Hbound.
  exact Hbound.
Qed.

(** Constant-set preparation uses the finite-set construction's own input budget. *)
Lemma rules_universe_constant_set_bounded P (E : encoding P) keys set events :
    audit_finset_of_list audit_positive_encode keys = (set, events) ->
    rules_universe_event_bounded P E (RuConstantsSet keys set events).
Proof.
  intro Hrun.
  pose proof (audit_finset_of_list_source_bound _ _ audit_positive_encode
    audit_basic_encoding_work keys) as Hbound.
  rewrite Hrun in Hbound. exact Hbound.
Qed.

(** The concrete trie lookup trace costs at most five units per key bit. *)
Polymorphic Lemma rules_universe_get_trace_bound A code (input : Trie.t A) :
    audit_trie_get_trace_source_work (snd (audit_trie_get code input)) <= 5 * Pos.size_nat code.
Proof.
  revert input. induction code as [rest IH | rest IH |]; intro input.
  - cbn [audit_trie_get]. specialize (IH (Trie.right input)).
    destruct (audit_trie_get rest (Trie.right input)) as [result events].
    cbn [snd audit_trie_get_trace_source_work] in *.
    pose proof (audit_accessor_bound A input). cbn [Pos.size_nat]. lia.
  - cbn [audit_trie_get]. specialize (IH (Trie.left input)).
    destruct (audit_trie_get rest (Trie.left input)) as [result events].
    cbn [snd audit_trie_get_trace_source_work] in *.
    pose proof (audit_accessor_bound A input). cbn [Pos.size_nat]. lia.
  - cbn [audit_trie_get snd audit_trie_get_trace_source_work].
    pose proof (audit_accessor_bound A input). cbn [Pos.size_nat]. lia.
Qed.

(** Predicate membership prices its encoder entry and actual lookup trace. *)
Polymorphic Lemma rules_universe_predicate_mem_bounded P (E : encoding P) p set result events :
    audit_finset_mem (rules_encoder E) p set = (result, events) ->
    rules_universe_event_bounded P E (RuPredicateMem p set result events).
Proof.
  intro Hrun. unfold audit_finset_mem, rules_encoder, audit_map_code_get in Hrun.
  pose proof (rules_universe_get_trace_bound (P * unit)%type (encode E p) set) as Htrace.
  destruct (audit_trie_get (encode E p) set) as [found body]. cbn in Htrace.
  destruct found as [[stored []] |]; inversion Hrun; subst;
    unfold rules_universe_event_bounded, rules_universe_event_work,
      rules_universe_event_budget; cbn [audit_finset_source_work length]; lia.
Qed.

(** Constant membership prices its actual positive encoder and lookup trace. *)
Polymorphic Lemma rules_universe_constant_mem_bounded P (E : encoding P) c set result events :
    audit_finset_mem audit_positive_encode c set = (result, events) ->
    rules_universe_event_bounded P E (RuConstantMem c set result events).
Proof.
  intro Hrun. unfold audit_finset_mem, audit_positive_encode, audit_map_code_get in Hrun.
  pose proof (rules_universe_get_trace_bound (positive * unit)%type c set) as Htrace.
  destruct (audit_trie_get c set) as [found body]. cbn in Htrace.
  destruct found as [[stored []] |]; inversion Hrun; subst;
    unfold rules_universe_event_bounded, rules_universe_event_work,
      rules_universe_event_budget; cbn [audit_finset_source_work audit_basic_encoding_work length];
    lia.
Qed.

(** * Preparation traversal frames *)

(* Discharge simple frame bounds and concatenate already bounded subtraces. *)
Local Ltac rules_universe_simple :=
  repeat first [assumption | apply Forall_app; split |
    solve [unfold rules_universe_event_bounded; cbn [rules_universe_event_work
      rules_universe_event_budget]; lia] | constructor].

(** Literal predicate traversal emits only bounded frames. *)
Lemma ru_literal_predicates_bounded P (E : encoding P) items :
    Forall (rules_universe_event_bounded P E) (snd (ru_literal_predicates items)).
Proof.
  induction items as [|item rest IH]; cbn [ru_literal_predicates];
    try (destruct (ru_literal_predicates rest) as [tail events]; cbn in IH);
    rules_universe_simple.
Qed.

(** Rule predicate traversal emits only bounded frames. *)
Lemma ru_rule_predicates_bounded P (E : encoding P) items :
    Forall (rules_universe_event_bounded P E) (snd (ru_rule_predicates items)).
Proof.
  induction items as [|item rest IH]; cbn [ru_rule_predicates].
  - rules_universe_simple.
  - pose proof (ru_literal_predicates_bounded P E (body item)) as Hbody.
    destruct (ru_literal_predicates (body item)) as [ps events]. cbn in Hbody.
    destruct (ru_rule_predicates rest) as [tail te]. cbn in IH.
    rules_universe_simple.
Qed.

(** Fact predicate traversal emits only bounded frames. *)
Lemma ru_fact_predicates_bounded P (E : encoding P) facts :
    Forall (rules_universe_event_bounded P E) (snd (ru_fact_predicates facts)).
Proof.
  induction facts as [|[p row] rest IH]; cbn [ru_fact_predicates];
    try (destruct (ru_fact_predicates rest) as [tail events]; cbn in IH);
    rules_universe_simple.
Qed.

(** Term constant traversal emits only bounded frames. *)
Lemma ru_term_constants_bounded P (E : encoding P) terms :
    Forall (rules_universe_event_bounded P E) (snd (ru_term_constants terms)).
Proof.
  induction terms as [|term rest IH]; cbn [ru_term_constants];
    try (destruct (ru_term_constants rest) as [tail events]; cbn in IH);
    rules_universe_simple.
Qed.

(** Literal constant traversal emits only bounded frames. *)
Lemma ru_literal_constants_bounded P (E : encoding P) items :
    Forall (rules_universe_event_bounded P E) (snd (ru_literal_constants items)).
Proof.
  induction items as [|item rest IH]; cbn [ru_literal_constants].
  - rules_universe_simple.
  - pose proof (ru_term_constants_bounded P E (args (lit_atom item))) as Hhead.
    destruct (ru_term_constants (args (lit_atom item))) as [cs events]. cbn in Hhead.
    destruct (ru_literal_constants rest) as [tail te]. cbn in IH.
    rules_universe_simple.
Qed.

(** Rule constant traversal emits only bounded frames. *)
Lemma ru_rule_constants_bounded P (E : encoding P) items :
    Forall (rules_universe_event_bounded P E) (snd (ru_rule_constants items)).
Proof.
  induction items as [|item rest IH]; cbn [ru_rule_constants].
  - rules_universe_simple.
  - pose proof (ru_term_constants_bounded P E (args (head item))) as Hhead.
    destruct (ru_term_constants (args (head item))) as [cs events]. cbn in Hhead.
    pose proof (ru_literal_constants_bounded P E (body item)) as Hbody.
    destruct (ru_literal_constants (body item)) as [bs be]. cbn in Hbody.
    destruct (ru_rule_constants rest) as [tail te]. cbn in IH.
    rules_universe_simple.
Qed.

(** Fact constant traversal emits only bounded frames. *)
Lemma ru_fact_constants_bounded P (E : encoding P) facts :
    Forall (rules_universe_event_bounded P E) (snd (ru_fact_constants facts)).
Proof.
  induction facts as [|[p row] rest IH]; cbn [ru_fact_constants];
    try (destruct (ru_fact_constants rest) as [tail events]; cbn in IH);
    rules_universe_simple.
Qed.

(** Every preparation event bounds its actual concrete subrun. *)
Lemma rules_universe_prepare_bounded P (prog : program P) facts p :
    Forall (rules_universe_event_bounded P (penc prog))
      (snd (rules_universe_prepare_counted prog facts p)).
Proof.
  pose proof (ru_rule_predicates_bounded P (penc prog) (rules prog)) as Hrp.
  pose proof (ru_fact_predicates_bounded P (penc prog) facts) as Hfp.
  pose proof (ru_rule_constants_bounded P (penc prog) (rules prog)) as Hrc.
  pose proof (ru_fact_constants_bounded P (penc prog) facts) as Hfc.
  unfold rules_universe_prepare_counted.
  destruct (ru_rule_predicates (rules prog)) as [rp rpe]. cbn in Hrp.
  destruct (ru_fact_predicates facts) as [fp fpe]. cbn in Hfp.
  destruct (audit_finset_of_list (rules_encoder (penc prog)) (rp ++ fp)) as [pset pse]
    eqn:Hpset.
  pose proof (rules_universe_predicate_set_bounded P (penc prog) (rp ++ fp) pset pse Hpset)
    as Hpset_cost.
  destruct (audit_finset_mem (rules_encoder (penc prog)) p pset) as [present me] eqn:Hmem.
  pose proof (rules_universe_predicate_mem_bounded P (penc prog) p pset present me Hmem)
    as Hmem_cost.
  destruct (ru_rule_constants (rules prog)) as [rc rce]. cbn in Hrc.
  destruct (ru_fact_constants facts) as [fc fce]. cbn in Hfc.
  destruct (audit_finset_of_list audit_positive_encode (rc ++ fc)) as [cset cse] eqn:Hcset.
  pose proof (rules_universe_constant_set_bounded P (penc prog) (rc ++ fc) cset cse Hcset)
    as Hcset_cost.
  rules_universe_simple.
Qed.

(** Every unary equality frame has the same work and budget. *)
Lemma ru_nat_eqb_bounded P (E : encoding P) lhs rhs :
    Forall (rules_universe_event_bounded P E) (snd (ru_nat_eqb lhs rhs)).
Proof.
  revert rhs. induction lhs as [|lhs IH]; intros [|rhs]; cbn [ru_nat_eqb];
    try (specialize (IH rhs); destruct (ru_nat_eqb lhs rhs) as [answer events]; cbn in IH);
    rules_universe_simple.
Qed.

(** Every constant check prices the actual membership call even after a false result. *)
Lemma ru_constants_check_bounded P (E : encoding P) set row :
    Forall (rules_universe_event_bounded P E) (snd (@ru_constants_check P set row)).
Proof.
  induction row as [|c rest IH]; cbn [ru_constants_check].
  - rules_universe_simple.
  - destruct (audit_finset_mem audit_positive_encode c set) as [present me] eqn:Hmem.
    pose proof (rules_universe_constant_mem_bounded P E c set present me Hmem) as Hmem_cost.
    destruct (ru_constants_check set rest) as [tail events]. cbn in IH.
    rules_universe_simple.
Qed.

(** Every tuple check event bounds its actual concrete subrun. *)
Lemma rules_universe_check_bounded P (E : encoding P) state row :
    Forall (rules_universe_event_bounded P E) (snd (@rules_universe_check_counted P state row)).
Proof.
  destruct state as [[present n] set].
  unfold rules_universe_check_counted.
  pose proof (ru_nat_eqb_bounded P E (length row) n) as Heq.
  destruct (ru_nat_eqb (length row) n) as [arity_ok ae]. cbn in Heq.
  pose proof (ru_constants_check_bounded P E set row) as Hconstants.
  destruct (ru_constants_check set row) as [constant_ok ce]. cbn in Hconstants.
  rules_universe_simple.
Qed.

(** Universe preparation and checking preserve membership and fit their selected budgets. *)
Theorem rules_universe_selected_cost : rules_universe_selected_cost_statement.
Proof.
  intros P prog facts p row.
  pose proof (rules_universe_erasure P prog facts p row) as Herase.
  pose proof (rules_universe_prepare_bounded P prog facts p) as Hprep.
  destruct (rules_universe_prepare_counted prog facts p) as [state pe]. cbn in Herase, Hprep.
  pose proof (rules_universe_check_bounded P (penc prog) state row) as Hcheck.
  destruct (rules_universe_check_counted state row) as [result ce]. cbn in Herase, Hcheck.
  split; [exact Herase |]. apply rules_universe_trace_bounded.
  apply Forall_app. auto.
Qed.
