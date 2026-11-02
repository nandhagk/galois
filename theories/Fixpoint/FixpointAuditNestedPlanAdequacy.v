(** * Nested plan phase adequacy

    The counted plan traversals preserve the original plan operations.
    For example, parsing retains the order of a component body and its siblings.
    Builds on: FixpointAuditNestedPlan and collection adequacy. *)

From Stdlib Require Import List PArith PeanoNat Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditCost CollectionsAuditTrie CollectionsAuditTrieAdequacy CollectionsAuditFinSet
  CollectionsAuditFinSetAdequacy.
From Galois.Graph Require Import GraphWto.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointNested
  FixpointAuditWorklist FixpointAuditWorklistBudgetAdequacy FixpointAuditNarrowDiscovery
    FixpointAuditNestedPlan.
Import List.ListNotations.

(** * Semantic agreement *)

Lemma fx_nested_parse_erases X C bound tokens :
  fst (@fx_nested_parse X C bound tokens) = nested_parse bound tokens.
Proof.
  revert tokens; induction bound as [|bound IH]; intro tokens.
  - reflexivity.
  - destruct tokens as [|token rest]; [reflexivity|].
    destruct token as [x|h|]; cbn [fx_nested_parse nested_parse]; try reflexivity.
    + pose proof (IH rest) as Hfirst.
      destruct (@fx_nested_parse X C bound rest) as [[code after] events] eqn:Hrun.
      cbn in Hfirst; rewrite <- Hfirst; reflexivity.
    + pose proof (IH rest) as Hfirst.
      destruct (@fx_nested_parse X C bound rest) as [[body after_body] events] eqn:Hrun.
      cbn in Hfirst; rewrite <- Hfirst.
      pose proof (IH after_body) as Hsecond.
      destruct (@fx_nested_parse X C bound after_body) as [[tail after] later] eqn:Hnext.
      cbn in Hsecond; rewrite <- Hsecond; reflexivity.
Qed.

Lemma fx_nested_rows_erases X C stack code :
  fst (@fx_nested_rows X C stack code) = nested_rows stack code.
Proof.
  revert stack; induction code as [|x rest IH|h body IHbody rest IHrest]; intro stack.
  - reflexivity.
  - cbn [fx_nested_rows nested_rows].
    specialize (IH stack); destruct (@fx_nested_rows X C stack rest) as [rows events].
    cbn in IH; now rewrite IH.
  - cbn [fx_nested_rows nested_rows].
    specialize (IHbody (h :: stack)); specialize (IHrest stack).
    destruct (@fx_nested_rows X C (h :: stack) body) as [rows events].
    destruct (@fx_nested_rows X C stack rest) as [tail later].
    cbn in IHbody, IHrest; now rewrite IHbody, IHrest.
Qed.

Lemma fx_nested_heads_erases X C code :
  fst (@fx_nested_heads X C code) = nested_heads code.
Proof.
  induction code as [|x rest IH|h body IHbody rest IHrest].
  - reflexivity.
  - cbn [fx_nested_heads nested_heads].
    destruct (@fx_nested_heads X C rest) as [heads events]; cbn in IH; exact IH.
  - cbn [fx_nested_heads nested_heads].
    destruct (@fx_nested_heads X C body) as [heads events].
    destruct (@fx_nested_heads X C rest) as [tail later].
    cbn in IHbody, IHrest; now rewrite IHbody, IHrest.
Qed.

Lemma fx_nested_member_fold_erases X C (EX : encoding X) rows :
  fst (@fx_nested_member_fold X C EX rows) =
    fold_right (fun row ix => Map.set EX (fst row) (snd row) ix) Map.empty rows.
Proof.
  induction rows as [|[x stack] rest IH].
  - reflexivity.
  - cbn [fx_nested_member_fold fold_right].
    destruct (@fx_nested_member_fold X C EX rest) as [before events] eqn:Hrest.
    cbn in IH.
    pose proof (audit_trie_set_erases (X * list X)%type (encode EX x) (x, stack) before) as Hset.
    destruct (audit_trie_set (encode EX x) (x, stack) before) as [after body].
    cbn in Hset; change (after = Map.set EX x stack before) in Hset.
    now rewrite Hset, IH.
Qed.

Lemma fx_nested_target_fold_erases X C A (EX : encoding X) (S : System.t X C A) cs :
  fst (fx_nested_target_fold EX S cs) =
    fold_right (fun c ix => index_push EX c (System.target S c) ix) Map.empty cs.
Proof.
  induction cs as [|c rest IH].
  - reflexivity.
  - cbn [fx_nested_target_fold fold_right].
    destruct (fx_nested_target_fold EX S rest) as [before events] eqn:Hrest; cbn in IH.
    pose proof (audit_map_code_get_erases X (list C) (encode EX (System.target S c)) before)
      as Hget.
    destruct (audit_map_code_get (encode EX (System.target S c)) before) as [raw read_events].
    cbn in Hget.
    pose proof (audit_trie_set_erases (X * list C)%type (encode EX (System.target S c))
      (System.target S c, c ::
        match raw with
        | Some values => values
        | None => []
        end) before)
      as Hset.
    destruct (audit_trie_set (encode EX (System.target S c))
      (System.target S c, c ::
        match raw with
        | Some values => values
        | None => []
        end) before)
      as [after write_events].
    cbn in Hset; rewrite <- IH; unfold index_push, index_get, Map.get, Map.set.
    rewrite <- Hget, <- Hset; reflexivity.
Qed.

Lemma fx_nested_members_erases X C (EX : encoding X) code :
  fst (@fx_nested_members X C EX code) = nested_members EX code.
Proof.
  unfold fx_nested_members, nested_members.
  pose proof (fx_nested_rows_erases X C [] code) as Hrows.
  destruct (@fx_nested_rows X C [] code) as [rows events]; cbn in Hrows.
  pose proof (fx_nested_member_fold_erases X C EX rows) as Hfold.
  destruct (@fx_nested_member_fold X C EX rows) as [members tail]; cbn in Hfold.
  now rewrite Hfold, Hrows.
Qed.

Lemma fx_nested_tree_erases X C tokens :
  fst (@fx_nested_tree X C tokens) = nested_tree tokens.
Proof.
  unfold fx_nested_tree, nested_tree.
  pose proof (fx_nested_parse_erases X C (S (length tokens)) (tokens ++ [WClose])) as Hparse.
  destruct (@fx_nested_parse X C (S (length tokens)) (tokens ++ [WClose]))
    as [[code rest] events]; change ((code, rest) = nested_parse (S (length tokens))
    (tokens ++ [WClose])) in Hparse.
  now rewrite <- Hparse.
Qed.

Lemma fx_nested_plan_erases X C A (EX : encoding X) (S : System.t X C A) tokens :
  fst (fx_nested_plan_from_tokens EX S tokens) =
    let code := nested_tree tokens in NestedPlan.Make code (nested_members EX code)
      (nested_targets EX S) (FinSet.of_list EX (nested_heads code)).
Proof.
  unfold fx_nested_plan_from_tokens.
  pose proof (fx_nested_tree_erases X C tokens) as Htree.
  destruct (@fx_nested_tree X C tokens) as [code parse_events]; cbn in Htree.
  pose proof (fx_nested_members_erases X C EX code) as Hmembers.
  destruct (@fx_nested_members X C EX code) as [members member_events]; cbn in Hmembers.
  pose proof (fx_nested_target_fold_erases X C A EX S (System.constraints S)) as Htargets.
  unfold fx_nested_targets.
  destruct (fx_nested_target_fold EX S (System.constraints S)) as [targets target_events].
  cbn in Htargets; change (targets = nested_targets EX S) in Htargets.
  pose proof (fx_nested_heads_erases X C code) as Hheads.
  destruct (@fx_nested_heads X C code) as [heads head_events]; cbn in Hheads.
  pose proof (audit_finset_of_list_erases X (fx_encoder_entry X) (fx_index_encoder EX) EX heads)
    as Hset.
  assert (Hencode : forall x, In x heads -> fst (fx_index_encoder EX x) = encode EX x).
  { intros x Hin; reflexivity. }
  specialize (Hset Hencode).
  destruct (audit_finset_of_list (fx_index_encoder EX) heads) as [head_set set_events].
  cbn in Hset; rewrite Hset, Hheads, Hmembers, Htargets, Htree; reflexivity.
Qed.

(** The counted parser and plan-building traversals agree with their native operations. *)
Theorem fx_nested_plan_semantic : fx_nested_plan_semantic_statement.
Proof.
  unfold fx_nested_plan_semantic_statement.
  repeat split; intros.
  - apply fx_nested_parse_erases.
  - apply fx_nested_tree_erases.
  - apply fx_nested_rows_erases.
  - apply fx_nested_heads_erases.
  - apply fx_nested_members_erases.
  - unfold fx_nested_targets, nested_targets; apply fx_nested_target_fold_erases.
  - apply fx_nested_plan_erases.
Qed.

(** * Selected source costs *)

Definition fx_plan_event_bounded {X C} (EX : encoding X) (event : fx_nested_plan_event X C) : Prop
  :=
  fx_nested_plan_event_work event <= fx_nested_plan_event_budget EX event.

Lemma fx_plan_work_bound X C (EX : encoding X) (events : list (fx_nested_plan_event X C)) :
  Forall (fx_plan_event_bounded EX) events ->
  fx_nested_plan_work events <= fx_nested_plan_budget EX events.
Proof.
  intro Hall; induction Hall as [|event rest Hhead Htail IH].
  - reflexivity.
  - cbn [fx_nested_plan_work fx_nested_plan_budget].
    unfold fx_plan_event_bounded in Hhead; apply Nat.add_le_mono; assumption.
Qed.

Lemma fx_plan_set_budget X (EX : encoding X) heads :
  audit_finset_of_list_budget (fx_index_encoder EX) (@length (fx_encoder_entry X)) heads <=
    1 + 12 * length heads +
      17 * fold_right (fun x n => Pos.size_nat (encode EX x) + n) 0 heads.
Proof.
  induction heads as [|x rest IH].
  - reflexivity.
  - cbn [audit_finset_of_list_budget fx_index_encoder length fold_right fst snd] in *; lia.
Qed.

Lemma fx_plan_heads_set_bounded X C (EX : encoding X) heads :
  let '(out, events) := audit_finset_of_list (fx_index_encoder EX) heads in
  fx_plan_event_bounded EX (@FnpHeadsSet X C heads out events).
Proof.
  pose proof (audit_finset_of_list_source_bound X (fx_encoder_entry X) (fx_index_encoder EX)
    (@length (fx_encoder_entry X)) heads) as Hwork.
  pose proof (fx_plan_set_budget X EX heads) as Hbudget.
  destruct (audit_finset_of_list (fx_index_encoder EX) heads) as [out events].
  cbn [snd] in Hwork.
  unfold fx_plan_event_bounded; cbn [fx_nested_plan_event_work fx_nested_plan_event_budget]; lia.
Qed.

Lemma fx_plan_get_bounded X C (EX : encoding X) x (input : Map.t X (list C)) :
  let '(raw, body) := audit_map_code_get (encode EX x) input in
  fx_plan_event_bounded EX (@FnpTargetRead X C x (encode EX x) input raw body).
Proof.
  pose proof (fx_map_get_body_bound X (list C) (encode EX x) input) as Hbody.
  destruct (audit_map_code_get (encode EX x) input) as [raw body]; cbn [snd] in Hbody.
  change (1 + S (Pos.size_nat (encode EX x)) + audit_trie_get_trace_source_work body <=
    2 + 6 * Pos.size_nat (encode EX x)); lia.
Qed.

(** Close a structural event whose work and budget agree. *)
Local Ltac fx_plan_trivial :=
  unfold fx_plan_event_bounded; cbn [fx_nested_plan_event_work fx_nested_plan_event_budget]; lia.

Lemma fx_plan_parse_bounded X C (EX : encoding X) bound tokens :
  Forall (fx_plan_event_bounded EX) (snd (@fx_nested_parse X C bound tokens)).
Proof.
  revert tokens; induction bound as [|bound IH]; intro tokens.
  - cbn [fx_nested_parse snd]; constructor; [fx_plan_trivial|constructor].
  - destruct tokens as [|token rest].
    + cbn [fx_nested_parse snd]; repeat constructor; fx_plan_trivial.
    + destruct token as [x|h|].
      * pose proof (IH rest) as Htail.
        cbn [fx_nested_parse].
        destruct (@fx_nested_parse X C bound rest) as [[code after] events]; cbn [snd] in Htail.
        cbn [snd]; cbn [app].
        constructor; [fx_plan_trivial|].
        constructor; [fx_plan_trivial|].
        apply Forall_app; split; [exact Htail|repeat constructor; fx_plan_trivial].
      * pose proof (IH rest) as Hbody.
        cbn [fx_nested_parse].
        destruct (@fx_nested_parse X C bound rest) as [[body after_body] body_events].
        cbn [snd] in Hbody; pose proof (IH after_body) as Htail.
        destruct (@fx_nested_parse X C bound after_body) as [[tail after] tail_events].
        cbn [snd] in Htail |- *; cbn [app].
        constructor; [fx_plan_trivial|].
        constructor; [fx_plan_trivial|].
        repeat rewrite Forall_app; repeat split; try assumption; repeat constructor;
          fx_plan_trivial.
      * cbn [fx_nested_parse snd]; repeat constructor; fx_plan_trivial.
Qed.

Lemma fx_plan_rows_bounded X C (EX : encoding X) stack code :
  Forall (fx_plan_event_bounded EX) (snd (@fx_nested_rows X C stack code)).
Proof.
  revert stack; induction code as [|x rest IH|h body IHbody rest IHrest]; intro stack.
  - cbn [fx_nested_rows snd]; repeat constructor; fx_plan_trivial.
  - pose proof (IH stack) as Htail.
    cbn [fx_nested_rows]; destruct (@fx_nested_rows X C stack rest) as [rows events].
    cbn [snd] in Htail |- *; constructor; [fx_plan_trivial|].
    apply Forall_app; split; [exact Htail|repeat constructor; fx_plan_trivial].
  - pose proof (IHbody (h :: stack)) as Hbody; pose proof (IHrest stack) as Htail.
    cbn [fx_nested_rows]; destruct (@fx_nested_rows X C (h :: stack) body) as [rows events].
    destruct (@fx_nested_rows X C stack rest) as [tail later].
    cbn [snd] in Hbody, Htail |- *; constructor; [fx_plan_trivial|].
    repeat rewrite Forall_app; repeat split; try assumption; repeat constructor; fx_plan_trivial.
Qed.

Lemma fx_plan_heads_bounded X C (EX : encoding X) code :
  Forall (fx_plan_event_bounded EX) (snd (@fx_nested_heads X C code)).
Proof.
  induction code as [|x rest IH|h body IHbody rest IHrest].
  - cbn [fx_nested_heads snd]; repeat constructor; fx_plan_trivial.
  - cbn [fx_nested_heads]; destruct (@fx_nested_heads X C rest) as [heads events].
    cbn [snd] in IH |- *; constructor; [fx_plan_trivial|exact IH].
  - cbn [fx_nested_heads]; destruct (@fx_nested_heads X C body) as [heads events].
    destruct (@fx_nested_heads X C rest) as [tail later].
    cbn [snd] in IHbody, IHrest |- *; constructor; [fx_plan_trivial|].
    repeat rewrite Forall_app; repeat split; try assumption; repeat constructor; fx_plan_trivial.
Qed.

Lemma fx_plan_member_set_bounded X C (EX : encoding X) x stack before :
  let '(after, body) := audit_trie_set (encode EX x) (x, stack) before in
  fx_plan_event_bounded EX (@FnpMembersSet X C x stack (encode EX x) before after body).
Proof.
  pose proof (fx_map_set_body_bound X (list X) (encode EX x) x stack before) as Hbody.
  destruct (audit_trie_set (encode EX x) (x, stack) before) as [after body]; cbn [snd] in Hbody.
  change (1 + S (Pos.size_nat (encode EX x)) + audit_trie_update_trace_source_work body <=
    2 + 17 * Pos.size_nat (encode EX x)); lia.
Qed.

Lemma fx_plan_target_set_bounded X C (EX : encoding X) x (value : list C) before :
  let '(after, body) := audit_trie_set (encode EX x) (x, value) before in
  fx_plan_event_bounded EX (@FnpTargetWrite X C x (encode EX x) value before after body).
Proof.
  pose proof (fx_map_set_body_bound X (list C) (encode EX x) x value before) as Hbody.
  destruct (audit_trie_set (encode EX x) (x, value) before) as [after body]; cbn [snd] in Hbody.
  change (1 + S (Pos.size_nat (encode EX x)) + audit_trie_update_trace_source_work body <=
    2 + 17 * Pos.size_nat (encode EX x)); lia.
Qed.

Lemma fx_plan_member_fold_bounded X C (EX : encoding X) rows :
  Forall (fx_plan_event_bounded EX) (snd (@fx_nested_member_fold X C EX rows)).
Proof.
  induction rows as [|[x stack] rest IH].
  - cbn [fx_nested_member_fold snd]; constructor; [fx_plan_trivial|constructor].
  - cbn [fx_nested_member_fold].
    destruct (@fx_nested_member_fold X C EX rest) as [before events]; cbn [snd] in IH.
    pose proof (fx_plan_member_set_bounded X C EX x stack before) as Hset.
    destruct (audit_trie_set (encode EX x) (x, stack) before) as [after body].
    cbn [snd]; constructor; [fx_plan_trivial|].
    apply Forall_app; split; [exact IH|constructor; [exact Hset|constructor]].
Qed.

Lemma fx_plan_target_fold_bounded X C A (EX : encoding X) (S : System.t X C A) cs :
  Forall (fx_plan_event_bounded EX) (snd (fx_nested_target_fold EX S cs)).
Proof.
  induction cs as [|c rest IH].
  - cbn [fx_nested_target_fold snd]; constructor; [fx_plan_trivial|constructor].
  - cbn [fx_nested_target_fold].
    destruct (fx_nested_target_fold EX S rest) as [before events]; cbn [snd] in IH.
    pose proof (fx_plan_get_bounded X C EX (System.target S c) before) as Hget.
    destruct (audit_map_code_get (encode EX (System.target S c)) before) as [raw read_body].
    pose proof (fx_plan_target_set_bounded X C EX (System.target S c)
      (c ::
        match raw with
        | Some values => values
        | None => []
        end) before) as Hset.
    destruct (audit_trie_set (encode EX (System.target S c))
      (System.target S c, c ::
        match raw with
        | Some values => values
        | None => []
        end) before)
      as [after write_body].
    cbn [snd]; constructor; [fx_plan_trivial|].
    apply Forall_app; split; [exact IH|].
    constructor; [fx_plan_trivial|].
    constructor; [exact Hget|].
    constructor; [fx_plan_trivial|].
    constructor; [exact Hset|constructor].
Qed.

Lemma fx_plan_tree_bounded X C (EX : encoding X) tokens :
  Forall (fx_plan_event_bounded EX) (snd (@fx_nested_tree X C tokens)).
Proof.
  pose proof (fx_plan_parse_bounded X C EX (S (length tokens)) (tokens ++ [WClose])) as Hparse.
  unfold fx_nested_tree.
  destruct (@fx_nested_parse X C (S (length tokens)) (tokens ++ [WClose]))
    as [[code rest] events]; cbn [snd] in Hparse |- *.
  constructor; [fx_plan_trivial|].
  constructor; [fx_plan_trivial|exact Hparse].
Qed.

Lemma fx_plan_members_bounded X C (EX : encoding X) code :
  Forall (fx_plan_event_bounded EX) (snd (@fx_nested_members X C EX code)).
Proof.
  pose proof (fx_plan_rows_bounded X C EX [] code) as Hrows.
  unfold fx_nested_members.
  destruct (@fx_nested_rows X C [] code) as [rows row_events]; cbn [snd] in Hrows.
  pose proof (fx_plan_member_fold_bounded X C EX rows) as Hfold.
  destruct (@fx_nested_member_fold X C EX rows) as [members events]; cbn [snd] in Hfold |- *.
  now apply Forall_app.
Qed.

(** Every selected plan event is charged against its own operands and retained body. *)
Theorem fx_nested_plan_selected_cost : fx_nested_plan_selected_cost_statement.
Proof.
  intros X C A EX S tokens.
  pose proof (fx_nested_plan_erases X C A EX S tokens) as Herase.
  pose proof (fx_plan_tree_bounded X C EX tokens) as Htree.
  unfold fx_nested_plan_from_tokens in *.
  destruct (@fx_nested_tree X C tokens) as [code parse_events]; cbn [snd] in Htree.
  pose proof (fx_plan_members_bounded X C EX code) as Hmembers.
  destruct (@fx_nested_members X C EX code) as [members member_events]; cbn [snd] in Hmembers.
  pose proof (fx_plan_target_fold_bounded X C A EX S (System.constraints S)) as Htargets.
  unfold fx_nested_targets in *.
  destruct (fx_nested_target_fold EX S (System.constraints S)) as [targets target_events].
  cbn [snd] in Htargets.
  pose proof (fx_plan_heads_bounded X C EX code) as Hheads.
  destruct (@fx_nested_heads X C code) as [heads head_events]; cbn [snd] in Hheads.
  pose proof (fx_plan_heads_set_bounded X C EX heads) as Hset.
  destruct (audit_finset_of_list (fx_index_encoder EX) heads) as [head_set set_events].
  cbn [fst snd] in Herase |- *; split; [exact Herase|].
  apply fx_plan_work_bound; repeat rewrite Forall_app; repeat split; try assumption.
  constructor; [exact Hset|constructor].
Qed.

(** * Bounds from the original token stream *)

Fixpoint fx_nested_code_size {X} (code : nested_code X) : nat :=
  match code with
  | NestedEnd => 0
  | NestedVisit _ rest => 1 + fx_nested_code_size rest
  | NestedComponent _ body rest => 1 + fx_nested_code_size body + fx_nested_code_size rest
  end.

Lemma fx_plan_work_app X C (left right : list (fx_nested_plan_event X C)) :
  fx_nested_plan_work (left ++ right) = fx_nested_plan_work left + fx_nested_plan_work right.
Proof.
  unfold fx_nested_plan_work; induction left as [|event rest IH]; cbn [app fold_right]; lia.
Qed.

Lemma fx_plan_parse_measure X C bound tokens :
  let '(result, events) := @fx_nested_parse X C bound tokens in
  fx_nested_code_size (fst result) + length (snd result) <= length tokens /\
  fx_nested_plan_work events + 5 * length (snd result) <= 2 + 5 * length tokens.
Proof.
  revert tokens; induction bound as [|bound IH]; intro tokens.
  - cbn [fx_nested_parse fst snd fx_nested_code_size]; split; [lia|].
    change (1 + 5 * length tokens <= 2 + 5 * length tokens); lia.
  - destruct tokens as [|token rest].
    + cbn [fx_nested_parse fst snd fx_nested_code_size]; split; [lia|].
      change (2 + 0 <= 2 + 5 * 0); lia.
    + destruct token as [x|h|].
      * pose proof (IH rest) as Htail.
        cbn [fx_nested_parse].
        destruct (@fx_nested_parse X C bound rest) as [[code after] events].
        cbn [fst snd] in Htail |- *; destruct Htail as [Hsize Hwork].
        split; [cbn [fx_nested_code_size length]; lia|].
        change (fx_nested_plan_work (FnpParse (Datatypes.S bound) (WVertex x :: rest) ::
          FnpCase 0 :: events ++ [FnpCase 1]) + 5 * length after <=
          2 + 5 * length (WVertex x :: rest)).
        change (1 + (1 + fx_nested_plan_work (events ++ [FnpCase 1])) + 5 * length after <=
          2 + 5 * (1 + length rest)).
        rewrite fx_plan_work_app; change (1 + (1 + (fx_nested_plan_work events + 1)) +
          5 * length after <= 2 + 5 * (1 + length rest)); lia.
      * pose proof (IH rest) as Hbody.
        cbn [fx_nested_parse].
        destruct (@fx_nested_parse X C bound rest) as [[body after_body] body_events].
        cbn [fst snd] in Hbody; destruct Hbody as [Hbody_size Hbody_work].
        pose proof (IH after_body) as Htail.
        destruct (@fx_nested_parse X C bound after_body) as [[tail after] tail_events].
        cbn [fst snd] in Htail |- *; destruct Htail as [Htail_size Htail_work].
        split; [cbn [fx_nested_code_size length]; lia|].
        change (1 + (1 + fx_nested_plan_work (body_events ++ tail_events ++ [FnpCase 2])) +
          5 * length after <= 2 + 5 * (1 + length rest)).
        repeat rewrite fx_plan_work_app.
        change (1 + (1 + (fx_nested_plan_work body_events +
          (fx_nested_plan_work tail_events + 1))) + 5 * length after <=
          2 + 5 * (1 + length rest)); lia.
      * cbn [fx_nested_parse fst snd fx_nested_code_size length]; split; [lia|].
        change (2 + 5 * length rest <= 2 + 5 * (1 + length rest)); lia.
Qed.

Lemma fx_plan_rows_measure X C stack code :
  let '(rows, events) := @fx_nested_rows X C stack code in
  length rows = fx_nested_code_size code /\
  fx_nested_plan_work events <= 4 * (1 + fx_nested_code_size code) * (1 + fx_nested_code_size code).
Proof.
  revert stack; induction code as [|x rest IH|h body IHbody rest IHrest]; intro stack.
  - cbn [fx_nested_rows fx_nested_code_size fst snd length]; split; [reflexivity|].
    change (1 <= 4 * (1 + 0) * (1 + 0)); lia.
  - pose proof (IH stack) as Htail.
    cbn [fx_nested_rows]; destruct (@fx_nested_rows X C stack rest) as [rows events].
    cbn [fst snd] in Htail; destruct Htail as [Hlength Hwork].
    split; [cbn [length fx_nested_code_size]; lia|].
    change (1 + fx_nested_plan_work (events ++ [FnpCase 3]) <=
      4 * (1 + (1 + fx_nested_code_size rest)) * (1 + (1 + fx_nested_code_size rest))).
    rewrite fx_plan_work_app; change (1 + (fx_nested_plan_work events + 1) <= 4 * (1 + (1 +
      fx_nested_code_size rest)) * (1 + (1 + fx_nested_code_size rest))); nia.
  - pose proof (IHbody (h :: stack)) as Hbody; pose proof (IHrest stack) as Htail.
    cbn [fx_nested_rows]; destruct (@fx_nested_rows X C (h :: stack) body) as [rows events].
    destruct (@fx_nested_rows X C stack rest) as [tail later].
    cbn [fst snd] in Hbody, Htail; destruct Hbody as [Hbody_length Hbody_work].
    destruct Htail as [Htail_length Htail_work].
    split; [cbn [length fx_nested_code_size]; rewrite length_app; lia|].
    change (1 + fx_nested_plan_work (events ++ later ++ [FnpAppend (length rows); FnpCase 4]) <=
      4 * (1 + (1 + fx_nested_code_size body + fx_nested_code_size rest)) *
        (1 + (1 + fx_nested_code_size body + fx_nested_code_size rest))).
    repeat rewrite fx_plan_work_app.
    change (1 + (fx_nested_plan_work events + (fx_nested_plan_work later +
      (1 + length rows + 1))) <=
      4 * (1 + (1 + fx_nested_code_size body + fx_nested_code_size rest)) *
        (1 + (1 + fx_nested_code_size body + fx_nested_code_size rest))); rewrite Hbody_length; nia.
Qed.

Lemma fx_plan_heads_measure X C code :
  let '(heads, events) := @fx_nested_heads X C code in
  length heads <= fx_nested_code_size code /\
  fx_nested_plan_work events <= 4 * (1 + fx_nested_code_size code) * (1 + fx_nested_code_size code).
Proof.
  induction code as [|x rest IH|h body IHbody rest IHrest].
  - cbn [fx_nested_heads fx_nested_code_size fst snd length]; split; [lia|].
    change (1 <= 4 * (1 + 0) * (1 + 0)); lia.
  - cbn [fx_nested_heads]; destruct (@fx_nested_heads X C rest) as [heads events].
    cbn [fst snd] in IH; destruct IH as [Hlength Hwork].
    split; [cbn [fx_nested_code_size]; lia|].
    change (1 + fx_nested_plan_work events <=
      4 * (1 + (1 + fx_nested_code_size rest)) * (1 + (1 + fx_nested_code_size rest))); nia.
  - cbn [fx_nested_heads]; destruct (@fx_nested_heads X C body) as [heads events].
    destruct (@fx_nested_heads X C rest) as [tail later].
    cbn [fst snd] in IHbody, IHrest; destruct IHbody as [Hbody_length Hbody_work].
    destruct IHrest as [Htail_length Htail_work].
    split; [cbn [length fx_nested_code_size]; rewrite length_app; lia|].
    change (1 + fx_nested_plan_work (events ++ later ++ [FnpAppend (length heads); FnpCase 5]) <=
      4 * (1 + (1 + fx_nested_code_size body + fx_nested_code_size rest)) *
        (1 + (1 + fx_nested_code_size body + fx_nested_code_size rest))).
    repeat rewrite fx_plan_work_app.
    change (1 + (fx_nested_plan_work events + (fx_nested_plan_work later +
      (1 + length heads + 1))) <=
      4 * (1 + (1 + fx_nested_code_size body + fx_nested_code_size rest)) *
        (1 + (1 + fx_nested_code_size body + fx_nested_code_size rest))); nia.
Qed.

Lemma fx_plan_member_fold_input X C (EX : encoding X) rows :
  fx_nested_plan_work (snd (@fx_nested_member_fold X C EX rows)) <=
    1 + 3 * length rows + 17 * fx_index_input_bits EX (map fst rows).
Proof.
  induction rows as [|[x stack] rest IH].
  - reflexivity.
  - pose proof (fx_plan_member_set_bounded X C EX x stack
      (fst (@fx_nested_member_fold X C EX rest))) as Hset.
    cbn [fx_nested_member_fold].
    destruct (@fx_nested_member_fold X C EX rest) as [before events]; cbn [fst snd] in IH, Hset.
    destruct (audit_trie_set (encode EX x) (x, stack) before) as [after body].
    unfold fx_plan_event_bounded in Hset; cbn [fx_nested_plan_event_budget] in Hset.
    cbn [snd].
    change (1 + fx_nested_plan_work (events ++ [FnpMembersSet x stack (encode EX x) before after
      body]) <=
      1 + 3 * length ((x, stack) :: rest) +
      17 * fx_index_input_bits EX (map fst ((x, stack) :: rest))).
    rewrite fx_plan_work_app.
    change (1 + (fx_nested_plan_work events +
      (fx_nested_plan_event_work (@FnpMembersSet X C x stack (encode EX x) before after body) +
        0)) <=
      1 + 3 * (1 + length rest) + 17 *
        (Pos.size_nat (encode EX x) + fx_index_input_bits EX (map fst rest))); lia.
Qed.

Lemma fx_plan_target_fold_input X C A (EX : encoding X) (S : System.t X C A) cs :
  fx_nested_plan_work (snd (fx_nested_target_fold EX S cs)) <=
    1 + 7 * length cs + 23 * fx_index_input_bits EX (map (System.target S) cs).
Proof.
  induction cs as [|c rest IH].
  - reflexivity.
  - cbn [fx_nested_target_fold].
    destruct (fx_nested_target_fold EX S rest) as [before events]; cbn [snd] in IH.
    pose proof (fx_plan_get_bounded X C EX (System.target S c) before) as Hget.
    destruct (audit_map_code_get (encode EX (System.target S c)) before) as [raw read_body].
    pose proof (fx_plan_target_set_bounded X C EX (System.target S c)
      (c ::
        match raw with
        | Some values => values
        | None => []
        end) before) as Hset.
    destruct (audit_trie_set (encode EX (System.target S c))
      (System.target S c, c ::
        match raw with
        | Some values => values
        | None => []
        end) before)
      as [after write_body].
    unfold fx_plan_event_bounded in Hget, Hset; cbn [fx_nested_plan_event_budget] in Hget, Hset.
    cbn [snd].
    change (1 + fx_nested_plan_work (events ++
      [FnpTarget c (System.target S c);
        FnpTargetRead (System.target S c) (encode EX (System.target S c)) before raw read_body;
        FnpCase 8;
        FnpTargetWrite (System.target S c) (encode EX (System.target S c))
          (c ::
            match raw with
            | Some values => values
            | None => []
            end) before after write_body]) <=
      1 + 7 * length (c :: rest) + 23 * fx_index_input_bits EX (map (System.target S) (c :: rest))).
    rewrite fx_plan_work_app.
    change (1 + (fx_nested_plan_work events +
      (1 + (fx_nested_plan_event_work
        (FnpTargetRead (System.target S c) (encode EX (System.target S c)) before raw read_body) +
        (1 + (fx_nested_plan_event_work
        (FnpTargetWrite (System.target S c) (encode EX (System.target S c))
          (c ::
            match raw with
            | Some values => values
            | None => []
            end) before after write_body) +
            0))))) <=
      1 + 7 * (1 + length rest) + 23 *
        (Pos.size_nat (encode EX (System.target S c)) +
          fx_index_input_bits EX (map (System.target S) rest))); lia.
Qed.

Lemma fx_plan_tree_measure X C tokens :
  let '(code, events) := @fx_nested_tree X C tokens in
  fx_nested_code_size code <= 1 + length tokens /\
  fx_nested_plan_work events <= 9 + 7 * length tokens.
Proof.
  pose proof (fx_plan_parse_measure X C (Datatypes.S (length tokens)) (tokens ++ [WClose])) as
    Hparse.
  unfold fx_nested_tree.
  destruct (@fx_nested_parse X C (Datatypes.S (length tokens)) (tokens ++ [WClose]))
    as [[code rest] events].
  cbn [fst snd] in Hparse |- *; destruct Hparse as [Hsize Hwork].
  rewrite length_app in Hsize, Hwork; cbn [length] in Hsize, Hwork.
  split; [lia|].
  change (1 + length tokens + (1 + length tokens + fx_nested_plan_work events) <=
    9 + 7 * length tokens); lia.
Qed.

(** The token and constraint inputs bound the complete counted plan construction. *)
Theorem fx_nested_plan_input_bound : fx_nested_plan_input_bound_statement.
Proof.
  intros X C A EX S tokens.
  pose proof (fx_nested_plan_erases X C A EX S tokens) as Herase.
  pose proof (fx_plan_tree_measure X C tokens) as Htree.
  pose proof (fx_nested_tree_erases X C tokens) as Htree_erase.
  unfold fx_nested_plan_from_tokens in *.
  destruct (@fx_nested_tree X C tokens) as [code parse_events].
  cbn [fst snd] in Htree, Htree_erase; destruct Htree as [Hsize Hparse].
  pose proof (fx_plan_rows_measure X C [] code) as Hrows.
  pose proof (fx_nested_rows_erases X C [] code) as Hrows_erase.
  unfold fx_nested_members in *.
  destruct (@fx_nested_rows X C [] code) as [rows row_events].
  cbn [fst snd] in Hrows, Hrows_erase; destruct Hrows as [Hrows_length Hrows_work].
  pose proof (fx_plan_member_fold_input X C EX rows) as Hmembers.
  destruct (@fx_nested_member_fold X C EX rows) as [members member_events]; cbn [snd] in Hmembers.
  pose proof (fx_plan_target_fold_input X C A EX S (System.constraints S)) as Htargets.
  unfold fx_nested_targets in *.
  destruct (fx_nested_target_fold EX S (System.constraints S)) as [targets target_events].
  cbn [snd] in Htargets.
  pose proof (fx_plan_heads_measure X C code) as Hheads.
  pose proof (fx_nested_heads_erases X C code) as Hheads_erase.
  destruct (@fx_nested_heads X C code) as [heads head_events].
  cbn [fst snd] in Hheads, Hheads_erase; destruct Hheads as [Hheads_length Hheads_work].
  pose proof (fx_plan_heads_set_bounded X C EX heads) as Hset.
  destruct (audit_finset_of_list (fx_index_encoder EX) heads) as [head_set set_events].
  unfold fx_plan_event_bounded in Hset; cbn [fx_nested_plan_event_budget] in Hset.
  cbn [fst snd] in Herase |- *; split; [exact Herase|].
  unfold fx_nested_plan_input_budget; rewrite <- Htree_erase, <- Hrows_erase, <- Hheads_erase.
  repeat rewrite fx_plan_work_app.
  change (fx_nested_plan_work parse_events +
    ((fx_nested_plan_work row_events + fx_nested_plan_work member_events) +
      (fx_nested_plan_work target_events +
      (fx_nested_plan_work head_events +
        (fx_nested_plan_event_work (@FnpHeadsSet X C heads head_set set_events) + 0)))) <=
    200 * (1 + length tokens + length (System.constraints S)) *
      (1 + length tokens + length (System.constraints S)) *
      (1 + length tokens + length (System.constraints S)) +
    40 * (fx_index_input_bits EX (map fst rows) + fx_index_input_bits EX heads +
      fx_index_input_bits EX (map (System.target S) (System.constraints S)))).
  unfold fx_index_input_bits in Hset.
  fold (fx_index_input_bits EX heads) in Hset.
  nia.
Qed.
