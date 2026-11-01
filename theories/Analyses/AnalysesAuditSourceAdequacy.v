(** * Adequacy of shared exact source combinators

    These proofs connect the typed counters to their plain operations and bound the fixed
    collection and derived-encoding source bodies. For example, a repeated map input retains
    both callback invocations, while erasure preserves the resulting list.
    Builds on: AnalysesAuditSource and the concrete collection adequacy theorems. *)

From Stdlib Require Import Bool List NArith PArith ZArith Lia.
From Galois.Analyses Require Import AnalysesAuditSource AnalysesSsaPreGraph.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditElements
  CollectionsAuditEncoding CollectionsAuditEncodingAdequacy CollectionsAuditTrie
  CollectionsAuditTrieAdequacy CollectionsEncoding CollectionsMap CollectionsTrie.
Import List.ListNotations.

(** Every nonempty external source body has at least one positive frame. *)
Theorem audit_external_body_positive : audit_external_body_positive_statement.
Proof.
  intros I O plain adapter input output trace [_ Hnonempty].
  destruct trace as [|frame rest]; [contradiction|].
  change (64 <= audit_external_frame_work frame + audit_external_trace_work rest).
  unfold audit_external_frame_work. lia.
Qed.

(** Each instrumented callback returns the result of its plain invocation. *)
Theorem audit_external_instrumentation_erases : audit_external_instrumentation_erases_statement.
Proof.
  intros I O plain adapter Hlaws input.
  exact (proj1 (Hlaws input)).
Qed.

(** The retained callback receipt supplies a body for that invocation's actual result. *)
Theorem audit_external_same_call_exists : audit_external_same_call_exists_statement.
Proof.
  intros I O plain adapter Hlaws input output Houtput.
  destruct (Hlaws input) as [Herases [Hbody Hbudget]].
  exists (external_events (external_counted adapter input)).
  unfold audit_external_same_call.
  rewrite <- Herases in Houtput. subst output.
  split; [exact Herases|]. split; assumption.
Qed.

(** Counted append preserves concatenation, including repeated elements. *)
Theorem exact_append_erases : exact_append_erases_statement.
Proof.
  intros Call A site xs ys.
  induction xs as [|x rest IH]; cbn [exact_append exact_case exact_bind exact_return exact_value].
  - reflexivity.
  - now rewrite IH.
Qed.

(** Counted mapping preserves the callback values in input order. *)
Theorem exact_map_erases : exact_map_erases_statement.
Proof.
  intros Call A B site f xs.
  induction xs as [|x rest IH]; cbn [exact_map exact_case exact_bind exact_return exact_value].
  - reflexivity.
  - now rewrite IH.
Qed.

(** Counted left folding passes the actual returned state to its next invocation. *)
Theorem exact_fold_left_erases : exact_fold_left_erases_statement.
Proof.
  intros Call A B site f xs.
  induction xs as [|x rest IH]; intro state;
    cbn [exact_fold_left exact_case exact_bind exact_return exact_value].
  - reflexivity.
  - apply IH.
Qed.

(** Counted right folding passes the actual tail result to its callback. *)
Theorem exact_fold_right_erases : exact_fold_right_erases_statement.
Proof.
  intros Call A B site f state xs.
  induction xs as [|x rest IH];
    cbn [exact_fold_right exact_case exact_bind exact_return exact_value].
  - reflexivity.
  - now rewrite IH.
Qed.

(** Counted lookup preserves the position-level behavior even for malformed maps. *)
Theorem exact_get_erases : exact_get_erases_statement.
Proof.
  intros Call K V inject E body key table; reflexivity.
Qed.

(** Counted insertion preserves the plain persistent update. *)
Theorem exact_set_erases : exact_set_erases_statement.
Proof.
  intros Call K V inject E body key value table; reflexivity.
Qed.

(** * Concrete encoder work *)

Lemma source_encoding_work_app first second :
  audit_encoding_frames_work (first ++ second) =
    audit_encoding_frames_work first + audit_encoding_frames_work second.
Proof.
  induction first as [|frame rest IH]; simpl; [reflexivity|]. rewrite IH. lia.
Qed.

Lemma source_emit_work code tail :
  audit_encoding_frames_work (snd (audit_emit_code code tail)) = 4 * Pos.size_nat code.
Proof.
  revert tail. induction code as [code IH|code IH|]; intro tail;
    cbn [audit_emit_code Pos.size_nat]; try reflexivity;
    specialize (IH tail); destruct (audit_emit_code code tail) as [bits frames];
    cbn [snd audit_encoding_frames_work audit_encoding_frame_charge] in *; lia.
Qed.

Lemma source_stream_work bits :
  audit_encoding_frames_work (snd (audit_stream_positive bits)) = 3 * S (length bits).
Proof.
  induction bits as [|[] rest IH]; cbn [audit_stream_positive]; try reflexivity;
    destruct (audit_stream_positive rest) as [code frames];
    cbn [snd audit_encoding_frames_work audit_encoding_frame_charge length] in *; lia.
Qed.

Lemma source_stream_size bits : Pos.size_nat (stream_positive bits) = S (length bits).
Proof.
  induction bits as [|[] rest IH]; cbn [stream_positive Pos.size_nat length]; lia.
Qed.

Lemma source_emit_length code tail : length (emit_code code tail) =
  2 * Pos.size_nat code + length tail.
Proof.
  revert tail. induction code as [code IH|code IH|]; intro tail;
    cbn [emit_code Pos.size_nat length]; rewrite ?IH; lia.
Qed.

Lemma source_pair_frames A B EA EB first_work second_work frames :
  @audit_pair_events_work A B EA EB first_work second_work (map AuditPairFrame frames) =
    audit_encoding_frames_work frames.
Proof.
  induction frames as [|frame rest IH]; cbn [audit_pair_events_work audit_encoding_frames_work map];
    now rewrite ?IH.
Qed.

(** The pair's work and width refer to the two component receipts from this exact run. *)
Lemma source_pair_work A B EA EB (first : A -> positive * list EA)
    (second : B -> positive * list EB) first_work second_work a b :
  let run := audit_pair_encode first second (a,b) in
  audit_pair_events_work first_work second_work (snd run) =
    first_work (snd (first a)) + second_work (snd (second b)) +
    5 + 10 * (Pos.size_nat (fst (first a)) + Pos.size_nat (fst (second b))) /\
  Pos.size_nat (fst run) =
    1 + 2 * (Pos.size_nat (fst (first a)) + Pos.size_nat (fst (second b))).
Proof.
  unfold audit_pair_encode.
  destruct (first a) as [ac ae]. destruct (second b) as [bc be].
  pose proof (source_emit_work bc []) as Hbw.
  pose proof (audit_emit_code_erases bc []) as Hbe.
  destruct (audit_emit_code bc []) as [bt bf]. cbn [snd fst] in Hbw, Hbe.
  pose proof (source_emit_work ac bt) as Haw.
  pose proof (audit_emit_code_erases ac bt) as Hae.
  destruct (audit_emit_code ac bt) as [bits af]. cbn [snd fst] in Haw, Hae.
  pose proof (source_stream_work bits) as Hsw.
  pose proof (audit_stream_positive_erases bits) as Hse.
  destruct (audit_stream_positive bits) as [result sf]. cbn [snd fst] in Hsw, Hse.
  cbn [fst snd audit_pair_events_work app].
  rewrite source_pair_frames, !source_encoding_work_app.
  rewrite Hae, Hbe, !source_emit_length in Hsw.
  rewrite Hse, source_stream_size, Hae, Hbe, !source_emit_length.
  cbn [length] in *. split; lia.
Qed.

Lemma source_pair_bound A B EA EB (first : A -> positive * list EA)
    (second : B -> positive * list EB) first_work second_work a b :
  let run := audit_pair_encode first second (a,b) in
  audit_pair_events_work first_work second_work (snd run) <=
    first_work (snd (first a)) + second_work (snd (second b)) + 8 * Pos.size_nat (fst run).
Proof.
  destruct (source_pair_work A B EA EB first second first_work second_work a b)
    as [Hwork Hsize]. cbv zeta. rewrite Hwork, Hsize. lia.
Qed.

(** Pair encoding preserves its code and pays for both actual component bodies. *)
Theorem audit_pre_pair_encoding_adequacy : audit_pre_pair_encoding_adequacy_statement.
Proof.
  intros A B EA EB ab bb [a b].
  pose proof (audit_pair_encode_erases A B _ _ (pre_external_encode EA)
    (pre_external_encode EB) EA EB a b eq_refl eq_refl) as Herases.
  pose proof (source_pair_bound A B _ _ (pre_external_encode EA)
    (pre_external_encode EB) (pre_external_encode_work ab) (pre_external_encode_work bb) a b)
    as Hbound.
  split; [exact Herases|].
  unfold pre_pair_encode_body. rewrite <- Herases.
  cbv zeta in Hbound.
  cbn [pre_external_encode pre_external_encode_work fold_right fst snd] in *. lia.
Qed.

(** A nested pair pays for its inner pair before constructing the final code. *)
Lemma source_triple_adequacy :
  forall A B C (EA : encoding A) (EB : encoding B) (EC : encoding C)
    (ab : A -> nat) (bb : B -> nat) (cb : C -> nat) key,
  let run := pre_triple_source_encoding EA EB EC key in
  fst run = encode (pair_encoding (pair_encoding EA EB) EC) key /\
  pre_triple_source_work ab bb cb (snd run) <=
    128 + ab (fst (fst key)) + bb (snd (fst key)) + cb (snd key) +
    16 * Pos.size_nat (fst run).
Proof.
  intros A B C EA EB EC ab bb cb [[a b] c].
  set (first := audit_pair_encode (pre_external_encode EA) (pre_external_encode EB)).
  pose proof (audit_pair_encode_erases A B _ _ (pre_external_encode EA)
    (pre_external_encode EB) EA EB a b eq_refl eq_refl) as Hfirst.
  pose proof (audit_pair_encode_erases (A * B)%type C _ _ first (pre_external_encode EC)
    (pair_encoding EA EB) EC (a,b) c Hfirst eq_refl) as Herases.
  pose proof (source_pair_bound A B _ _ (pre_external_encode EA)
    (pre_external_encode EB) (pre_external_encode_work ab) (pre_external_encode_work bb) a b)
    as Hinner.
  pose proof (source_pair_work (A * B)%type C _ _ first (pre_external_encode EC)
    (audit_pair_events_work (pre_external_encode_work ab) (pre_external_encode_work bb))
    (pre_external_encode_work cb) (a,b) c) as [Houter Hsize].
  split; [exact Herases|].
  unfold pre_triple_source_work, pre_triple_source_encoding.
  fold first in Hinner |- *. cbv zeta in Hinner.
  cbn [pre_external_encode pre_external_encode_work fold_right fst snd] in *.
  nia.
Qed.

(** A version encodes only its selected constructor's components and sum tags. *)
Lemma source_frg_adequacy :
  forall B E U (EB : encoding B) (EE : encoding E) (EU : encoding U)
    (bb : B -> nat) (eb : E -> nat) (ub : U -> nat) d,
  let run := pre_frg_source_encoding EB EE EU d in
  fst run = encode (frg_version_encoding EB EE EU) d /\
  pre_frg_source_work bb eb ub (snd run) <=
    128 + 64 * Pos.size_nat (fst run) +
    match d with
    | FrUnavailable u | FrInitial u => ub u
    | FrFresh e u => eb e + ub u
    | FrPhi b u => bb b + ub u
    end.
Proof.
  intros B E U EB EE EU bb eb ub version.
  destruct version as [u|u|e u|b u].
  - cbn [pre_frg_source_encoding pre_frg_source_work audit_sum_encode
      pre_external_encode audit_sum_events_work pre_external_encode_work fold_right
      frg_version_encoding encode sum_encoding fst snd].
    split; [reflexivity|lia].
  - cbn [pre_frg_source_encoding pre_frg_source_work audit_sum_encode
      pre_external_encode audit_sum_events_work pre_external_encode_work fold_right
      frg_version_encoding encode sum_encoding fst snd].
    split; [reflexivity|lia].
  - pose proof (audit_pair_encode_erases E U _ _ (pre_external_encode EE)
      (pre_external_encode EU) EE EU e u eq_refl eq_refl) as Herases.
    pose proof (source_pair_bound E U _ _ (pre_external_encode EE)
      (pre_external_encode EU) (pre_external_encode_work eb) (pre_external_encode_work ub) e u)
      as Hbound.
    unfold pre_frg_source_encoding, pre_frg_source_work.
    destruct (audit_pair_encode (pre_external_encode EE) (pre_external_encode EU) (e,u))
      as [code events] eqn:Hrun.
    cbn [audit_sum_encode audit_sum_events_work pre_external_encode_work fold_right
      pre_external_encode fst snd Pos.size_nat] in *.
    rewrite Hrun. cbn [fst snd audit_sum_events_work Pos.size_nat].
    split.
    + cbn [frg_version_encoding AnalysesSsaPreGraph.frg_version_key encode sum_encoding].
      now rewrite Herases.
    + lia.
  - pose proof (audit_pair_encode_erases B U _ _ (pre_external_encode EB)
      (pre_external_encode EU) EB EU b u eq_refl eq_refl) as Herases.
    pose proof (source_pair_bound B U _ _ (pre_external_encode EB)
      (pre_external_encode EU) (pre_external_encode_work bb) (pre_external_encode_work ub) b u)
      as Hbound.
    unfold pre_frg_source_encoding, pre_frg_source_work.
    destruct (audit_pair_encode (pre_external_encode EB) (pre_external_encode EU) (b,u))
      as [code events] eqn:Hrun.
    cbn [audit_sum_encode audit_sum_events_work pre_external_encode_work fold_right
      pre_external_encode fst snd Pos.size_nat] in *.
    rewrite Hrun. cbn [fst snd audit_sum_events_work Pos.size_nat].
    split.
    + cbn [frg_version_encoding AnalysesSsaPreGraph.frg_version_key encode sum_encoding].
      now rewrite Herases.
    + lia.
Qed.

(** Nested pairs and version tags preserve their selected codes and component body charges. *)
Theorem audit_pre_derived_encoding_adequacy : audit_pre_derived_encoding_adequacy_statement.
Proof.
  split; [exact source_triple_adequacy|exact source_frg_adequacy].
Qed.

(** * Concrete enumeration work *)

Lemma source_elements_work_app A (first second : list (audit_elements_event A)) :
  audit_elements_work (first ++ second) =
    audit_elements_work first + audit_elements_work second.
Proof.
  induction first as [|event rest IH]; simpl; [reflexivity|]. rewrite IH. lia.
Qed.

Lemma source_path_step path depth :
  (forall p, Pos.size_nat (path p) <= depth + Pos.size_nat p) ->
  forall (bit : bool) p,
    Pos.size_nat (path (if bit then xI p else xO p)) <= S depth + Pos.size_nat p.
Proof.
  intros Hpath bit p. specialize (Hpath (if bit then xI p else xO p)).
  destruct bit; cbn [Pos.size_nat] in Hpath; lia.
Qed.

Lemma source_elements_fold_length A (node : Trie.ne A) :
  forall path acc, length (fst (audit_elements_fold_ne path node acc)) <=
    length acc + exact_ne_nodes node.
Proof.
  induction node as [r IH|v|v r IH|l IH|l IHl r IHr|l IH v|l IHl v r IHr];
    intros path acc; cbn [audit_elements_fold_ne exact_ne_nodes].
  - specialize (IH (fun p => path (xI p)) acc).
    destruct (audit_elements_fold_ne (fun p => path (xI p)) r acc); cbn in *; lia.
  - cbn. lia.
  - specialize (IH (fun p => path (xI p)) ((path xH,v)::acc)).
    destruct (audit_elements_fold_ne (fun p => path (xI p)) r ((path xH,v)::acc));
      cbn in *; lia.
  - specialize (IH (fun p => path (xO p)) acc).
    destruct (audit_elements_fold_ne (fun p => path (xO p)) l acc); cbn in *; lia.
  - specialize (IHl (fun p => path (xO p)) acc).
    destruct (audit_elements_fold_ne (fun p => path (xO p)) l acc) as [middle le].
    specialize (IHr (fun p => path (xI p)) middle).
    destruct (audit_elements_fold_ne (fun p => path (xI p)) r middle); cbn in *; lia.
  - specialize (IH (fun p => path (xO p)) acc).
    destruct (audit_elements_fold_ne (fun p => path (xO p)) l acc); cbn in *; lia.
  - specialize (IHl (fun p => path (xO p)) acc).
    destruct (audit_elements_fold_ne (fun p => path (xO p)) l acc) as [middle le].
    specialize (IHr (fun p => path (xI p)) ((path xH,v)::middle)).
    destruct (audit_elements_fold_ne (fun p => path (xI p)) r ((path xH,v)::middle));
      cbn in *; lia.
Qed.

(** Prefix depth bounds emitted positions; node count also bounds every deeper suffix. *)
Lemma source_elements_fold_work A (node : Trie.ne A) :
  forall path depth acc,
    (forall p, Pos.size_nat (path p) <= depth + Pos.size_nat p) ->
    audit_elements_work (snd (audit_elements_fold_ne path node acc)) <=
      (14 + depth + exact_ne_nodes node) * exact_ne_nodes node.
Proof.
  induction node as [r IH|v|v r IH|l IH|l IHl r IHr|l IH v|l IHl v r IHr];
    intros path depth acc Hpath;
    pose proof (Hpath xH) as Hhere; cbn [Pos.size_nat] in Hhere;
    cbn [audit_elements_fold_ne exact_ne_nodes].
  - specialize (IH _ (S depth) acc (source_path_step path depth Hpath true)).
    destruct (audit_elements_fold_ne (fun p => path (xI p)) r acc).
    cbn [snd audit_elements_work audit_elements_frame_work app] in *; nia.
  - cbn [snd audit_elements_work audit_elements_frame_work app]. nia.
  - specialize (IH _ (S depth) ((path xH,v)::acc)
      (source_path_step path depth Hpath true)).
    destruct (audit_elements_fold_ne (fun p => path (xI p)) r ((path xH,v)::acc)).
    cbn [snd audit_elements_work audit_elements_frame_work app] in *; nia.
  - specialize (IH _ (S depth) acc (source_path_step path depth Hpath false)).
    destruct (audit_elements_fold_ne (fun p => path (xO p)) l acc).
    cbn [snd audit_elements_work audit_elements_frame_work app] in *; nia.
  - specialize (IHl _ (S depth) acc (source_path_step path depth Hpath false)).
    destruct (audit_elements_fold_ne (fun p => path (xO p)) l acc) as [middle le].
    specialize (IHr _ (S depth) middle (source_path_step path depth Hpath true)).
    destruct (audit_elements_fold_ne (fun p => path (xI p)) r middle).
    cbn [snd audit_elements_work audit_elements_frame_work app] in *.
    rewrite source_elements_work_app. nia.
  - specialize (IH _ (S depth) acc (source_path_step path depth Hpath false)).
    destruct (audit_elements_fold_ne (fun p => path (xO p)) l acc).
    cbn [snd audit_elements_work audit_elements_frame_work app] in *.
    rewrite source_elements_work_app.
    cbn [audit_elements_work audit_elements_frame_work app]. nia.
  - specialize (IHl _ (S depth) acc (source_path_step path depth Hpath false)).
    destruct (audit_elements_fold_ne (fun p => path (xO p)) l acc) as [middle le].
    specialize (IHr _ (S depth) ((path xH,v)::middle)
      (source_path_step path depth Hpath true)).
    destruct (audit_elements_fold_ne (fun p => path (xI p)) r ((path xH,v)::middle)).
    cbn [snd audit_elements_work audit_elements_frame_work app] in *.
    rewrite source_elements_work_app.
    cbn [audit_elements_work audit_elements_frame_work app]. nia.
Qed.

Lemma source_elements_reverse A (input acc : list (positive * A)) :
  length (fst (audit_elements_reverse input acc)) = length input + length acc /\
  audit_elements_work (snd (audit_elements_reverse input acc)) = 2 * S (length input).
Proof.
  revert acc. induction input as [|x rest IH]; intro acc; simpl.
  - split; reflexivity.
  - specialize (IH (x::acc)).
    destruct (audit_elements_reverse rest (x::acc)); cbn in *; lia.
Qed.

Lemma source_elements_values A (input : list (positive * A)) :
  audit_elements_work (snd (audit_elements_values input)) = 2 * S (length input).
Proof.
  induction input as [|[position value] rest IH]; simpl; [reflexivity|].
  destruct (audit_elements_values rest); cbn in *; lia.
Qed.

(** Enumeration pays for position construction, reversal and projection on arbitrary raw tries. *)
Lemma source_map_elements_bound K V (table : Map.t K V) :
  audit_elements_work (snd (audit_map_elements table)) <=
    32 * (S (exact_trie_nodes table)) ^ 2.
Proof.
  unfold audit_map_elements, audit_trie_elements.
  destruct table as [|node].
  - cbn. lia.
  - pose proof (source_elements_fold_length (K * V)%type node (fun p => p) []) as Hlength.
    pose proof (source_elements_fold_work (K * V)%type node (fun p => p) 0 []
      (fun p => Nat.le_refl _)) as Hwork.
    destruct (audit_elements_fold_ne (fun p => p) node []) as [reversed fe].
    pose proof (source_elements_reverse (K * V)%type reversed []) as [Hreverse Hrwork].
    destruct (audit_elements_reverse reversed []) as [positions re].
    pose proof (source_elements_values (K * V)%type positions) as Hvwork.
    destruct (audit_elements_values positions) as [values ve].
    cbn [snd fst length exact_trie_nodes Nat.pow] in *.
    rewrite !source_elements_work_app. nia.
Qed.

(** Each fixed map charge bounds its actual literal collection implementation. *)
Theorem audit_pre_map_implementation_adequacy : audit_pre_map_implementation_adequacy_statement.
Proof.
  intros K V body call.
  destruct call as [key code|key code before answer|key code value before after|
    key code before after|before answer];
    unfold pre_map_literal_work, pre_map_fixed_charge.
  - unfold audit_encoding_weight. lia.
  - pose proof (audit_trie_get_source_work_bound (K * V)%type code before).
    unfold audit_get_weight, audit_key_bits_weight. lia.
  - pose proof (audit_trie_update_source_work_bound (K * V)%type code
      (Some (key,value)) before).
    unfold audit_set_weight, audit_key_bits_weight. lia.
  - pose proof (audit_trie_update_source_work_bound (K * V)%type code None before).
    unfold audit_remove_weight, audit_key_bits_weight. lia.
  - pose proof (source_map_elements_bound K V before). lia.
Qed.

(** The external call retains the very receipt used for its value, event and body payload. *)
Lemma source_external_same_run Call I O plain (adapter : audit_external_adapter I O plain)
    (input : I) (call : O -> Call) :
  audit_external_adapter_laws adapter ->
  let receipt := external_counted adapter input in
  let run := exact_external_call adapter input call in
  exact_value run = external_value receipt /\
  exact_events run = [AuditCall (call (exact_value run))] /\
  exact_bodies run = [(call (exact_value run),external_events receipt)] /\
  audit_external_same_call adapter input (exact_value run) (external_events receipt).
Proof.
  intro Hlaws. cbv zeta.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  exact (Hlaws input).
Qed.
