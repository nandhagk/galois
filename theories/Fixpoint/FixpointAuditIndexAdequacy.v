(** * Adequacy of indexed preparation

    The counted preparation follows the same right fold and bounds its concrete collection work.
    For example, repeated side targets are inserted once after the finite-set traversal.
    Builds on: FixpointAuditIndex and the collection adequacy theorems. *)

From Stdlib Require Import List PArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsAuditTrie CollectionsAuditFinSet CollectionsAuditElements
  CollectionsAuditTrieAdequacy CollectionsAuditFinSetAdequacy CollectionsAuditElementsAdequacy.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointAuditIndex.
Import List.ListNotations.

(** * Same-run collection bounds *)

Lemma fxi_work_app X C B (budget : fx_index_external_budget X C B) left right :
  fx_index_adapter_work budget (left ++ right) =
    fx_index_adapter_work budget left + fx_index_adapter_work budget right.
Proof.
  induction left as [|event rest IH].
  - reflexivity.
  - change (fxi_event_work budget event + fx_index_adapter_work budget (rest ++ right) =
      (fxi_event_work budget event + fx_index_adapter_work budget rest) +
        fx_index_adapter_work budget right).
    rewrite IH; lia.
Qed.

Lemma fxi_work_cons X C B (budget : fx_index_external_budget X C B) event events :
  fx_index_adapter_work budget (event :: events) =
    fxi_event_work budget event + fx_index_adapter_work budget events.
Proof.
  reflexivity.
Qed.

(** Each finite-set input allowance covers its encoder receipts and trie insertions. *)
Lemma fxi_set_budget_bound X C B (EX : encoding X) (cb : fx_index_external_model X C B)
    (budget : fx_index_external_budget X C B) input :
  (forall x, fst (fxi_encode cb x) = encode EX x) ->
  (forall x, fxi_body_work budget (snd (fxi_encode cb x)) <= fxi_encode_bound budget x) ->
  audit_finset_of_list_budget (fxi_encode cb) (fxi_body_work budget) input <=
    fxi_set_input_budget EX budget input.
Proof.
  intros Hencode Hbound; induction input as [|x rest IH].
  - reflexivity.
  - cbn [audit_finset_of_list_budget fxi_set_input_budget].
    rewrite Hencode; specialize (Hbound x); lia.
Qed.

(** Distinct traversal returns the original keys and stays within its input allowance. *)
Lemma fxi_distinct_adequate X C B (EX : encoding X) (cb : fx_index_external_model X C B)
    (budget : fx_index_external_budget X C B) input :
  (forall x, fst (fxi_encode cb x) = encode EX x) ->
  (forall x, fxi_body_work budget (snd (fxi_encode cb x)) <= fxi_encode_bound budget x) ->
  fst (fxi_distinct_counted cb input) = distinct_unknowns EX input /\
  fx_index_adapter_work budget (snd (fxi_distinct_counted cb input)) <=
    fxi_distinct_input_budget EX budget input.
Proof.
  intros Hencode Hbound.
  pose proof (audit_finset_of_list_erases X B (fxi_encode cb) EX input
    (fun x _ => Hencode x)) as Hset.
  pose proof (audit_finset_of_list_source_bound X B (fxi_encode cb)
    (fxi_body_work budget) input) as Hwork.
  pose proof (fxi_set_budget_bound X C B EX cb budget input Hencode Hbound) as Hbudget.
  unfold fxi_distinct_counted.
  destruct (audit_finset_of_list (fxi_encode cb) input) as [set build] eqn:Hbuild.
  cbn in Hset, Hwork; subst set.
  pose proof (audit_finset_elements_erases X (FinSet.of_list EX input)) as Helements.
  pose proof (audit_finset_elements_work_bound X (FinSet.of_list EX input)) as Helwork.
  destruct (audit_finset_elements (FinSet.of_list EX input)) as [output events].
  cbn in Helements, Helwork; subst output.
  unfold distinct_unknowns, fxi_distinct_input_budget.
  split; [reflexivity |].
  unfold fx_index_adapter_work; cbn [snd fold_right fxi_event_work]; lia.
Qed.

(** A map read retains the encoded key and its concrete trace within the key-width bound. *)
Lemma fxi_read_adequate X C B (EX : encoding X) (cb : fx_index_external_model X C B)
    (budget : fx_index_external_budget X C B) x (m : Map.t X (list C)) :
  fst (fxi_encode cb x) = encode EX x ->
  fxi_body_work budget (snd (fxi_encode cb x)) <= fxi_encode_bound budget x ->
  let '(code, body) := fxi_encode cb x in
  let '(raw, events) := audit_map_code_get code m in
  code = encode EX x /\ raw = Map.get EX x m /\
  fxi_body_work budget body <= fxi_encode_bound budget x /\
  audit_trie_get_trace_source_work events <= 5 * Pos.size_nat (encode EX x).
Proof.
  intros Hcode Hbody.
  destruct (fxi_encode cb x) as [code body]; cbn in Hcode, Hbody; subst code.
  pose proof (audit_map_code_get_erases X (list C) (encode EX x) m) as Hget.
  pose proof (audit_trie_get_trace_adequate (X * list C)%type (encode EX x) m) as Htrace.
  pose proof (audit_trie_get_source_work_bound (X * list C)%type (encode EX x) m) as Hwork.
  unfold audit_map_code_get in Hget |- *.
  destruct (audit_trie_get (encode EX x) m) as [raw events]; cbn in *.
  unfold Map.get; repeat split; try assumption; lia.
Qed.

(** A trie write retains the actual value and trace within the encoded key-width bound. *)
Lemma fxi_write_adequate X C B (EX : encoding X) (cb : fx_index_external_model X C B)
    (budget : fx_index_external_budget X C B) x value (m : Map.t X (list C)) :
  fst (fxi_encode cb x) = encode EX x ->
  fxi_body_work budget (snd (fxi_encode cb x)) <= fxi_encode_bound budget x ->
  let '(code, body) := fxi_encode cb x in
  let '(after, events) := audit_trie_set code (x, value) m in
  code = encode EX x /\ after = Map.set EX x value m /\
  fxi_body_work budget body <= fxi_encode_bound budget x /\
  audit_trie_update_trace_source_work events <= 16 * Pos.size_nat (encode EX x).
Proof.
  intros Hcode Hbody.
  destruct (fxi_encode cb x) as [code body]; cbn in Hcode, Hbody; subst code.
  pose proof (audit_trie_set_erases (X * list C)%type (encode EX x) (x, value) m) as Hset.
  pose proof (audit_trie_update_trace_adequate (X * list C)%type (encode EX x)
    (Some (x, value)) m) as Htrace.
  pose proof (audit_trie_update_source_work_bound (X * list C)%type (encode EX x)
    (Some (x, value)) m) as Hwork.
  unfold audit_trie_set in Hset |- *.
  destruct (audit_trie_update (encode EX x) (Some (x, value)) m) as [after events].
  cbn in *; unfold Map.set; repeat split; try assumption; lia.
Qed.

(** Each right-folded push preserves its tail map and charges its actual read and write. *)
Lemma fxi_push_adequate X C B (EX : encoding X) (cb : fx_index_external_model X C B)
    (budget : fx_index_external_budget X C B) c keys :
  (forall x, fst (fxi_encode cb x) = encode EX x) ->
  (forall x, fxi_body_work budget (snd (fxi_encode cb x)) <= fxi_encode_bound budget x) ->
  forall m, fst (fxi_push_many cb c keys m) = index_push_many EX c keys m /\
    fx_index_adapter_work budget (snd (fxi_push_many cb c keys m)) <=
      fxi_push_input_budget EX budget keys.
Proof.
  intros Hencode Hbound; induction keys as [|x rest IH]; intro m.
  - unfold fx_index_adapter_work; cbn [fxi_push_many index_push_many snd fold_right
      fxi_event_work fxi_push_input_budget]; split; [reflexivity | lia].
  - cbn [fxi_push_many index_push_many fxi_push_input_budget].
    specialize (IH m).
    destruct (fxi_push_many cb c rest m) as [before tail] eqn:Htail.
    cbn in IH; destruct IH as [Herase Htailwork].
    pose proof (fxi_read_adequate X C B EX cb budget x before (Hencode x) (Hbound x)) as Hread.
    destruct (fxi_encode cb x) as [code body] eqn:Henc.
    destruct (audit_map_code_get code before) as [raw get_events] eqn:Hget.
    cbn in Hread; destruct Hread as [Hcode [Hraw [Hbody Hgetwork]]]; subst code.
    set (value := c ::
      match raw with
      | Some values =>
        values
      | None =>
        []
      end).
    pose proof (fxi_write_adequate X C B EX cb budget x value before (Hencode x) (Hbound x))
      as Hwrite.
    rewrite Henc in Hwrite; cbn in Hwrite.
    destruct (audit_trie_set (encode EX x) (x, value) before) as [after set_events] eqn:Hset.
    cbn in Hwrite; destruct Hwrite as [_ [Hafter [_ Hsetwork]]].
    split.
    + cbn [fst]; rewrite Hafter; unfold index_push, index_get; rewrite <- Herase, <- Hraw.
      reflexivity.
    + cbn [snd]; rewrite fxi_work_cons, fxi_work_app.
      unfold fx_index_adapter_work in Htailwork |- *.
      cbn [fold_right fxi_event_work]; lia.
Qed.

(** * Constraint fold *)

(** A distinct-key phase pushes into its input map and bounds both captured traces. *)
Lemma fxi_phase_adequate X C B (EX : encoding X) (cb : fx_index_external_model X C B)
    (budget : fx_index_external_budget X C B) c input (m : Map.t X (list C)) :
  (forall x, fst (fxi_encode cb x) = encode EX x) ->
  (forall x, fxi_body_work budget (snd (fxi_encode cb x)) <= fxi_encode_bound budget x) ->
  let '(keys, distinct_events) := fxi_distinct_counted cb input in
  let '(result, push_events) := fxi_push_many cb c keys m in
  result = index_push_many EX c (distinct_unknowns EX input) m /\
  fx_index_adapter_work budget (distinct_events ++ push_events) <=
    fxi_distinct_input_budget EX budget input +
    fxi_push_input_budget EX budget (distinct_unknowns EX input).
Proof.
  intros Hencode Hbound.
  pose proof (fxi_distinct_adequate X C B EX cb budget input Hencode Hbound) as Hdistinct.
  destruct (fxi_distinct_counted cb input) as [keys distinct_events] eqn:Hdistinct_call.
  cbn in Hdistinct; destruct Hdistinct as [Hkeys Hdistinctwork]; subst keys.
  pose proof (fxi_push_adequate X C B EX cb budget c (distinct_unknowns EX input)
    Hencode Hbound m) as Hpush.
  destruct (fxi_push_many cb c (distinct_unknowns EX input) m) as [result push_events]
    eqn:Hpush_call.
  cbn in Hpush; destruct Hpush as [Hresult Hpushwork].
  change (fx_index_adapter_work budget distinct_events <=
    fxi_distinct_input_budget EX budget input) in Hdistinctwork.
  change (fx_index_adapter_work budget push_events <=
    fxi_push_input_budget EX budget (distinct_unknowns EX input)) in Hpushwork.
  split; [exact Hresult |].
  rewrite fxi_work_app; lia.
Qed.

(** The fold frame adds its three callback bodies to the two captured phase traces and tail. *)
Lemma fxi_fold_frame_work X C B (budget : fx_index_external_budget X C B)
    c target sides deps target_body sides_body deps_body tail output_events contrib_events
    read_events reader_events output_bound read_bound tail_bound :
  fxi_body_work budget target_body <= fxi_target_bound budget c ->
  fxi_body_work budget sides_body <= fxi_sides_bound budget c ->
  fxi_body_work budget deps_body <= fxi_deps_bound budget c ->
  fx_index_adapter_work budget tail <= tail_bound ->
  fx_index_adapter_work budget (output_events ++ contrib_events) <= output_bound ->
  fx_index_adapter_work budget (read_events ++ reader_events) <= read_bound ->
  fx_index_adapter_work budget
    (FxiCase 2 :: tail ++ [FxiTarget c target target_body; FxiSides c sides sides_body] ++
      output_events ++ contrib_events ++ FxiDeps c deps deps_body :: read_events ++ reader_events)
    <= 12 + fxi_target_bound budget c + fxi_sides_bound budget c + fxi_deps_bound budget c +
      output_bound + read_bound + tail_bound.
Proof.
  intros Htarget Hsides Hdeps Htail Houtputs Hreads.
  repeat (rewrite fxi_work_cons || rewrite fxi_work_app).
  rewrite fxi_work_app in Houtputs, Hreads.
  cbn [fxi_event_work].
  assert (fx_index_adapter_work budget [] = 0) as Hnil by reflexivity.
  rewrite Hnil; lia.
Qed.

(** The counted right fold returns the original index and its input-derived work bound. *)
Lemma fxi_fold_adequate X C A B (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (cb : fx_index_external_model X C B)
    (budget : fx_index_external_budget X C B) cs :
  fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb budget ->
  fst (fxi_fold cb cs) = index_constraints EX S SS cs /\
  fx_index_adapter_work budget (snd (fxi_fold cb cs)) <=
    fxi_constraints_input_budget EX S SS budget cs.
Proof.
  intros [Hencode [Htarget [Hsides Hdeps]]] [_ [Hencbound [Htbound [Hsbound Hdbound]]]].
  induction cs as [|c rest IH].
  - cbn [fxi_fold index_constraints fold_right fxi_constraints_input_budget].
    split; [reflexivity |].
    unfold fx_index_adapter_work; cbn [snd fold_right fxi_event_work]; lia.
  - cbn [fxi_fold index_constraints fold_right fxi_constraints_input_budget].
    destruct (fxi_fold cb rest) as [ix tail] eqn:Htail.
    cbn in IH; destruct IH as [Hix Htailwork].
    pose proof (Htarget c) as Ht; pose proof (Htbound c) as Htb.
    destruct (fxi_target cb c) as [target target_body] eqn:Htarget_call.
    cbn in Ht, Htb; subst target.
    pose proof (Hsides c) as Hs; pose proof (Hsbound c) as Hsb.
    destruct (fxi_sides cb c) as [sides sides_body] eqn:Hsides_call.
    cbn in Hs, Hsb; subst sides.
    pose proof (fxi_phase_adequate X C B EX cb budget c
      (System.target S c :: side_targets SS c) (contributors ix) Hencode Hencbound) as Houtputs.
    destruct (fxi_distinct_counted cb (System.target S c :: side_targets SS c))
      as [outputs output_events] eqn:Houtput_call.
    destruct (fxi_push_many cb c outputs (contributors ix)) as [contrib contrib_events]
      eqn:Hcontrib_call.
    cbn in Houtputs; destruct Houtputs as [Hcontrib Houtputwork].
    pose proof (Hdeps c) as Hd; pose proof (Hdbound c) as Hdb.
    destruct (fxi_deps cb c) as [reads read_body] eqn:Hdeps_call.
    cbn in Hd, Hdb; subst reads.
    pose proof (fxi_phase_adequate X C B EX cb budget c (deps SS c) (readers ix)
      Hencode Hencbound) as Hreads.
    destruct (fxi_distinct_counted cb (deps SS c)) as [reads read_events] eqn:Hreads_call.
    destruct (fxi_push_many cb c reads (readers ix)) as [reader reader_events]
      eqn:Hreader_call.
    cbn in Hreads; destruct Hreads as [Hreader Hreadwork].
    change (fx_index_adapter_work budget tail <=
      fxi_constraints_input_budget EX S SS budget rest) in Htailwork.
    change (fx_index_adapter_work budget (output_events ++ contrib_events) <=
      fxi_distinct_input_budget EX budget (System.target S c :: side_targets SS c) +
      fxi_push_input_budget EX budget
        (distinct_unknowns EX (System.target S c :: side_targets SS c))) in Houtputwork.
    change (fx_index_adapter_work budget (read_events ++ reader_events) <=
      fxi_distinct_input_budget EX budget (deps SS c) +
      fxi_push_input_budget EX budget (distinct_unknowns EX (deps SS c))) in Hreadwork.
    split.
    + cbn [fst]; rewrite Hcontrib, Hreader, Hix; reflexivity.
    + cbn [snd].
      pose proof (fxi_fold_frame_work X C B budget c (System.target S c)
        (side_targets SS c) (deps SS c) target_body sides_body read_body tail output_events
        contrib_events read_events reader_events
        (fxi_distinct_input_budget EX budget (System.target S c :: side_targets SS c) +
          fxi_push_input_budget EX budget
            (distinct_unknowns EX (System.target S c :: side_targets SS c)))
        (fxi_distinct_input_budget EX budget (deps SS c) +
          fxi_push_input_budget EX budget (distinct_unknowns EX (deps SS c)))
        (fxi_constraints_input_budget EX S SS budget rest)
        Htb Hsb Hdb Htailwork Houtputwork Hreadwork) as Hframe.
      lia.
Qed.

(** Erasing the counted run recovers the original index for callbacks with matching results. *)
Theorem fx_index_nested_erasure : fx_index_nested_erasure_statement.
Proof.
  intros X C A B EX S SS cb Herase.
  set (budget := FxIndexExternalBudget X C B (fun _ => 1)
    (fun x => fxi_body_work (FxIndexExternalBudget X C B (fun _ => 1)
      (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)) (snd (fxi_encode cb x)))
    (fun c => fxi_body_work (FxIndexExternalBudget X C B (fun _ => 1)
      (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)) (snd (fxi_target cb c)))
    (fun c => fxi_body_work (FxIndexExternalBudget X C B (fun _ => 1)
      (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)) (snd (fxi_sides cb c)))
    (fun c => fxi_body_work (FxIndexExternalBudget X C B (fun _ => 1)
      (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)) (snd (fxi_deps cb c)))).
  assert (Hbounded : fx_index_external_bounded cb budget).
  { unfold fx_index_external_bounded, budget, fxi_body_work; cbn.
    repeat split; intros; lia. }
  pose proof (fxi_fold_adequate X C A B EX S SS cb budget (System.constraints S)
    Herase Hbounded) as [Hresult _].
  exact Hresult.
Qed.

(** The same counted run returns the index within the input-derived source-work budget. *)
Theorem fx_index_nested_input_bound : fx_index_nested_input_bound_statement.
Proof.
  intros X C A B EX S SS cb budget Herase Hbounded.
  pose proof (fxi_fold_adequate X C A B EX S SS cb budget (System.constraints S)
    Herase Hbounded) as Hresult.
  unfold fx_index_nested_counted, fx_index_nested_input_budget.
  destruct (fxi_fold cb (System.constraints S)); exact Hresult.
Qed.

(** Adequate external receipts retain the established erasure and source-work bound. *)
Theorem fx_index_external_source_holds : fx_index_external_source_statement.
Proof.
  intros X C A B EX S SS cb budget source Herase Hbounded.
  pose proof (fx_index_nested_input_bound X C A B EX S SS cb budget Herase Hbounded) as Hresult.
  destruct (fx_index_nested_counted S cb) as [result events]; cbn in *.
  intro Htrace; exact Hresult.
Qed.
