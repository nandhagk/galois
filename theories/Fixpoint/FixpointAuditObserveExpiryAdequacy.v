(** * Adequacy of observation lifetimes

    The counted lifetime search retains the selected last reader and its source work.
    For example, a later component that reads a value prevents an earlier expiry.
    Builds on: FixpointAuditObserveExpiry and collection adequacy. *)

From Stdlib Require Import List Bool PArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsTrie
  CollectionsAuditTrie
  CollectionsAuditMap CollectionsAuditFinSet CollectionsAuditMapAdequacy
  CollectionsAuditFinSetAdequacy CollectionsAuditTrieAdequacy.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointObserve
  FixpointAuditWorklist FixpointAuditWorklistCallbacks FixpointAuditNestedCallbacks
  FixpointAuditNestedCallbacksAdequacy FixpointAuditObserveExecute FixpointAuditObserveExpiry.
Import List.ListNotations.

(** * Lifetime erasure *)

Lemma fx_observe_reader_uses_erases X C A (EX : encoding X) (S : System.t X C A)
    members cs :
  fst (fx_observe_reader_uses EX S members cs) =
    existsb (fun c => FinSet.mem EX (System.target S c) members) cs.
Proof.
  induction cs as [|c rest IH].
  - reflexivity.
  - cbn [fx_observe_reader_uses existsb].
    pose proof (audit_finset_mem_erases X (fx_encoder_entry X) (fx_index_encoder EX) EX
      (System.target S c) members eq_refl) as Hmem.
    destruct (audit_finset_mem (fx_index_encoder EX) (System.target S c) members) as [out events].
    destruct (fx_observe_reader_uses EX S members rest) as [later tail].
    cbn in Hmem, IH |- *; now rewrite Hmem, IH.
Qed.

Lemma fx_observe_component_uses_erases X C A (EX : encoding X) (S : System.t X C A)
    ix members x :
  fst (fx_observe_component_uses EX S ix members x) =
    observation_component_uses EX S ix members x.
Proof.
  pose proof (audit_finset_mem_erases X (fx_encoder_entry X) (fx_index_encoder EX) EX x members
    eq_refl) as Hmem.
  pose proof (audit_map_get_erases X (list C) (fx_encoder_entry X) (fx_index_encoder EX) EX x
    (readers ix) eq_refl) as Hread.
  unfold fx_observe_component_uses, observation_component_uses, readers_of.
  destruct (audit_finset_mem (fx_index_encoder EX) x members) as [present mem].
  destruct (audit_map_get (fx_index_encoder EX) x (readers ix)) as [found read].
  cbn in Hmem, Hread; subst present found.
  pose proof (fx_observe_reader_uses_erases X C A EX S members
    (match Map.get EX x (readers ix) with
    | Some cs => cs
    | None => []
    end)) as Huses.
  destruct (fx_observe_reader_uses EX S members
    (match Map.get EX x (readers ix) with
    | Some cs => cs
    | None => []
    end)) as [used calls].
  cbn in Huses |- *; now rewrite Huses.
Qed.

Lemma fx_observe_last_reader_erases X C A (EX : encoding X) (S : System.t X C A)
    ix order x :
  fst (fx_observe_last_reader EX S ix order x) = observation_last_reader EX S ix order x.
Proof.
  induction order as [|component rest IH].
  - reflexivity.
  - destruct component as [|h body].
    + cbn [fx_observe_last_reader observation_last_reader].
      destruct (fx_observe_last_reader EX S ix rest x) as [last events]; exact IH.
    + cbn [fx_observe_last_reader observation_last_reader].
      destruct (fx_observe_last_reader EX S ix rest x) as [[last|] events];
        cbn [fst snd] in IH |- *.
      * now rewrite <- IH.
      * rewrite <- IH.
        pose proof (audit_finset_of_list_erases X (fx_encoder_entry X) (fx_index_encoder EX) EX
          (h :: body) (fun _ _ => eq_refl)) as Hset.
        destruct (audit_finset_of_list (fx_index_encoder EX) (h :: body)) as [members set].
        cbn in Hset; subst members.
        pose proof (fx_observe_component_uses_erases X C A EX S ix
          (FinSet.of_list EX (h :: body)) x)
          as Huses.
        destruct (fx_observe_component_uses EX S ix
          (fold_left (fun s k => FinSet.add EX k s) body (FinSet.add EX h FinSet.empty)) x)
          as [used calls] eqn:Hcall.
        change (fst (fx_observe_component_uses EX S ix
          (fold_left (fun s k => FinSet.add EX k s) body (FinSet.add EX h FinSet.empty)) x) =
          observation_component_uses EX S ix (FinSet.of_list EX (h :: body)) x)
          in Huses.
        rewrite Hcall in Huses; cbn [fst snd] in Huses |- *; now rewrite Huses.
Qed.

(** Expiration folding erases to the original persistent map traversal. *)
Theorem fx_observe_expiry_fold_correct : fx_observe_expiry_fold_statement.
Proof.
  intros X C A EX S ix order xs; induction xs as [|x rest IH].
  - reflexivity.
  - cbn [fx_observe_expiry_fold fold_right].
    pose proof (fx_observe_last_reader_erases X C A EX S ix order x) as Hlast.
    destruct (fx_observe_expiry_fold EX S ix order rest) as [before tail].
    destruct (fx_observe_last_reader EX S ix order x) as [[h|] calls]; cbn [fst snd] in IH, Hlast.
    + rewrite <- Hlast.
      pose proof (audit_map_get_erases X (list X) (fx_encoder_entry X) (fx_index_encoder EX) EX h
        before eq_refl) as Hread.
      destruct (audit_map_get (fx_index_encoder EX) h before) as [old read]; cbn [fst snd] in Hread.
      pose proof (audit_map_set_erases X (list X) (fx_encoder_entry X) (fx_index_encoder EX) EX h
        (x ::
          match old with
          | Some ys => ys
          | None => []
          end) before eq_refl) as Hwrite.
      destruct (audit_map_set (fx_index_encoder EX) h
        (x ::
          match old with
          | Some ys => ys
          | None => []
          end) before) as [after write].
      cbn [fst snd] in Hwrite |- *; rewrite Hwrite, Hread, IH; reflexivity.
    + rewrite <- Hlast; exact IH.
Qed.

(** * Lifetime frame bounds *)

Lemma fx_expiry_work_app X C (first last : list (fx_observe_expiry_event X C)) :
  fx_observe_expiry_work (first ++ last) =
    fx_observe_expiry_work first + fx_observe_expiry_work last.
Proof.
  induction first as [|event rest IH].
  - reflexivity.
  - change (fx_observe_expiry_event_work event + fx_observe_expiry_work (rest ++ last) =
      (fx_observe_expiry_event_work event + fx_observe_expiry_work rest) +
        fx_observe_expiry_work last).
    rewrite IH; lia.
Qed.

Lemma fx_expiry_mem_bound X (EX : encoding X) x members :
  audit_finset_source_work (@length (fx_encoder_entry X))
    (snd (audit_finset_mem (fx_index_encoder EX) x members)) <=
    7 + 5 * Pos.size_nat (encode EX x).
Proof.
  unfold audit_finset_mem, fx_index_encoder, audit_map_code_get.
  pose proof (audit_trie_get_trace_adequate (X * unit)%type (encode EX x) members) as Htrace.
  pose proof (audit_trie_get_source_work_bound (X * unit)%type (encode EX x) members) as Hbound.
  destruct (audit_trie_get (encode EX x) members) as [found trace].
  cbn [snd] in Htrace, Hbound; destruct found; cbn [snd option_map audit_finset_source_work];
    rewrite Htrace; cbn [length]; lia.
Qed.

Lemma fx_expiry_set_budget X (EX : encoding X) xs :
  audit_finset_of_list_budget (fx_index_encoder EX) (@length (fx_encoder_entry X)) xs =
    fx_observe_expiry_set_budget EX xs.
Proof.
  induction xs as [|x rest IH].
  - reflexivity.
  - cbn [audit_finset_of_list_budget fx_observe_expiry_set_budget fx_index_encoder].
    now rewrite IH.
Qed.

Lemma fx_observe_reader_uses_bound X C A (EX : encoding X) (S : System.t X C A)
    members cs :
  fx_observe_expiry_work (snd (fx_observe_reader_uses EX S members cs)) <=
    fx_observe_reader_uses_budget EX S cs.
Proof.
  induction cs as [|c rest IH].
  - reflexivity.
  - cbn [fx_observe_reader_uses fx_observe_reader_uses_budget].
    pose proof (fx_expiry_mem_bound X EX (System.target S c) members) as Hmem.
    destruct (audit_finset_mem (fx_index_encoder EX) (System.target S c) members) as [out events].
    destruct (fx_observe_reader_uses EX S members rest) as [later tail].
    cbn [snd] in Hmem, IH |- *.
    change (1 + (1 + (audit_finset_source_work (@length (fx_encoder_entry X)) events +
      fx_observe_expiry_work tail)) <=
      9 + 5 * Pos.size_nat (encode EX (System.target S c)) +
        fx_observe_reader_uses_budget EX S rest).
    lia.
Qed.

Lemma fx_observe_component_uses_bound X C A (EX : encoding X) (S : System.t X C A)
    ix members x :
  fx_observe_expiry_work (snd (fx_observe_component_uses EX S ix members x)) <=
    fx_observe_component_uses_budget EX S ix x.
Proof.
  pose proof (fx_expiry_mem_bound X EX x members) as Hmem.
  pose proof (audit_map_get_source_work_bound X (list C) (fx_encoder_entry X)
    (fx_index_encoder EX) (@length (fx_encoder_entry X)) x (readers ix)) as Hread.
  pose proof (audit_map_get_erases X (list C) (fx_encoder_entry X) (fx_index_encoder EX) EX x
    (readers ix) eq_refl) as Herase.
  unfold fx_observe_component_uses.
  destruct (audit_finset_mem (fx_index_encoder EX) x members) as [present mem].
  destruct (audit_map_get (fx_index_encoder EX) x (readers ix)) as [found read].
  cbn [fst snd] in Hmem, Hread, Herase.
  pose proof (fx_observe_reader_uses_bound X C A EX S members
    (match found with
    | Some cs => cs
    | None => []
    end)) as Huses.
  destruct (fx_observe_reader_uses EX S members
    (match found with
    | Some cs => cs
    | None => []
    end)) as [used calls].
  cbn [snd] in Huses.
  unfold fx_observe_component_uses_budget, readers_of, index_get.
  rewrite <- Herase.
  cbn [fx_index_encoder length fst snd] in Hread.
  change (1 + (audit_finset_source_work (@length (fx_encoder_entry X)) mem +
    (audit_map_source_work (@length (fx_encoder_entry X)) read + fx_observe_expiry_work calls)) <=
      16 + 10 * Pos.size_nat (encode EX x) +
        fx_observe_reader_uses_budget EX S
          (match found with
          | Some cs => cs
          | None => []
          end)).
  lia.
Qed.

Lemma fx_observe_last_reader_bound X C A (EX : encoding X) (S : System.t X C A)
    ix order x :
  fx_observe_expiry_work (snd (fx_observe_last_reader EX S ix order x)) <=
    fx_observe_last_reader_budget EX S ix order x.
Proof.
  induction order as [|component rest IH].
  - reflexivity.
  - destruct component as [|h body].
    + cbn [fx_observe_last_reader fx_observe_last_reader_budget].
      destruct (fx_observe_last_reader EX S ix rest x) as [last events]; cbn [snd] in IH |- *.
      change (1 + fx_observe_expiry_work events <=
        1 + fx_observe_last_reader_budget EX S ix rest x); lia.
    + cbn [fx_observe_last_reader fx_observe_last_reader_budget].
      pose proof (fx_observe_last_reader_erases X C A EX S ix rest x) as Herase.
      destruct (fx_observe_last_reader EX S ix rest x) as [[last|] events];
        cbn [fst snd] in IH, Herase |- *.
      * rewrite <- Herase; cbn [fst snd].
        change (1 + fx_observe_expiry_work events <=
          1 + fx_observe_last_reader_budget EX S ix rest x + 0); lia.
      * rewrite <- Herase; cbn [fst snd].
        pose proof (audit_finset_of_list_source_bound X (fx_encoder_entry X) (fx_index_encoder EX)
          (@length (fx_encoder_entry X)) (h :: body)) as Hset.
        rewrite fx_expiry_set_budget in Hset.
        destruct (audit_finset_of_list (fx_index_encoder EX) (h :: body)) as [members set].
        cbn [snd] in Hset.
        pose proof (fx_observe_component_uses_bound X C A EX S ix members x) as Huses.
        destruct (fx_observe_component_uses EX S ix members x) as [used calls].
        cbn [snd] in Huses |- *.
        change (1 + fx_observe_expiry_work (events ++ FxExpirySet set :: calls) <=
          1 + fx_observe_last_reader_budget EX S ix rest x +
            (fx_observe_expiry_set_budget EX (h :: body) +
              fx_observe_component_uses_budget EX S ix x)).
        rewrite fx_expiry_work_app.
        change (1 + (fx_observe_expiry_work events +
          (audit_finset_source_work (@length (fx_encoder_entry X)) set +
            fx_observe_expiry_work calls)) <=
          1 + fx_observe_last_reader_budget EX S ix rest x +
            (fx_observe_expiry_set_budget EX (h :: body) +
              fx_observe_component_uses_budget EX S ix x)).
        lia.
Qed.

(** Expiration folding charges each selected search and persistent map operation. *)
Theorem fx_observe_expiry_fold_bound : fx_observe_expiry_fold_bound_statement.
Proof.
  intros X C A EX S ix order xs; induction xs as [|x rest IH].
  - change (1 <= 1); lia.
  - cbn [fx_observe_expiry_fold fx_observe_expiry_fold_budget].
    pose proof (fx_observe_last_reader_erases X C A EX S ix order x) as Herase.
    pose proof (fx_observe_last_reader_bound X C A EX S ix order x) as Hlast.
    destruct (fx_observe_expiry_fold EX S ix order rest) as [before tail].
    destruct (fx_observe_last_reader EX S ix order x) as [[h|] calls];
      cbn [fst snd] in IH, Herase, Hlast |- *.
    + rewrite <- Herase.
      pose proof (audit_map_get_source_work_bound X (list X) (fx_encoder_entry X)
        (fx_index_encoder EX) (@length (fx_encoder_entry X)) h before) as Hread.
      destruct (audit_map_get (fx_index_encoder EX) h before) as [old read].
      cbn [snd fx_index_encoder length fst] in Hread.
      pose proof (audit_map_set_source_work_bound X (list X) (fx_encoder_entry X)
        (fx_index_encoder EX) (@length (fx_encoder_entry X)) h
        (x ::
          match old with
          | Some ys => ys
          | None => []
          end) before) as Hwrite.
      destruct (audit_map_set (fx_index_encoder EX) h
        (x ::
          match old with
          | Some ys => ys
          | None => []
          end) before) as [after write].
      cbn [snd fx_index_encoder length fst] in Hwrite |- *.
      change (1 + fx_observe_expiry_work (tail ++ calls ++ [FxExpiryMap read; FxExpiryMap write]) <=
        1 + fx_observe_expiry_fold_budget EX S ix order rest +
          fx_observe_last_reader_budget EX S ix order x +
          (10 + 21 * Pos.size_nat (encode EX h))).
      repeat rewrite fx_expiry_work_app.
      cbn [fx_observe_expiry_work fx_observe_expiry_event_work fold_right]; lia.
    + rewrite <- Herase.
      change (1 + fx_observe_expiry_work (tail ++ calls) <=
        1 + fx_observe_expiry_fold_budget EX S ix order rest +
          fx_observe_last_reader_budget EX S ix order x + 0).
      rewrite fx_expiry_work_app; lia.
Qed.

(** * Lifetime callback receipts *)

Definition fx_expiry_receipts {X C A B} (source : fx_declared_callback_source X C A B)
    (budget : fx_declared_callback_budget X C A B) (events : list (fx_observe_expiry_event X C)) :
    Prop :=
  exists groups, Forall2 (fx_observe_expiry_event_source source) events groups /\
    fx_declared_body_work (fx_body_weight budget) groups <=
      fold_right (fun event n => fx_observe_expiry_external_budget budget event + n) 0 events.

Lemma fx_expiry_receipts_app X C A B (source : fx_declared_callback_source X C A B)
    (budget : fx_declared_callback_budget X C A B) first last :
  fx_expiry_receipts source budget first -> fx_expiry_receipts source budget last ->
  fx_expiry_receipts source budget (first ++ last).
Proof.
  intros [left [Hleft Hleft_bound]] [right [Hright Hright_bound]].
  exists (left ++ right); split.
  - now apply Forall2_app.
  - rewrite fx_declared_body_work_app, fold_right_app.
    assert (Hfold : forall events n,
      fold_right (fun event total => fx_observe_expiry_external_budget budget event + total) n
        events =
      fold_right (fun event total => fx_observe_expiry_external_budget budget event + total) 0
        events + n).
    { induction events as [|event rest IH]; intro n; cbn; [lia | rewrite IH; lia]. }
    rewrite Hfold; lia.
Qed.

Lemma fx_expiry_receipts_one X C A B (source : fx_declared_callback_source X C A B)
    (budget : fx_declared_callback_budget X C A B) event group :
  fx_observe_expiry_event_source source event group ->
  fx_nested_group_work (fx_body_weight budget) group <=
    fx_observe_expiry_external_budget budget event ->
  fx_expiry_receipts source budget [event].
Proof.
  intros Hsource Hbound; exists [group]; split.
  - constructor; [exact Hsource | constructor].
  - change (fx_nested_group_work (fx_body_weight budget) group + 0 <=
      fx_observe_expiry_external_budget budget event + 0); lia.
Qed.

Section ExpiryReceipts.

Context {X C A B : Type} (EX : encoding X) (S : System.t X C A).

Context (source : fx_declared_callback_source X C A B).

Context (budget : fx_declared_callback_budget X C A B).

Context (Hlaws : fx_observe_expiry_source_laws EX S source budget).

Lemma fx_expiry_case_receipt : fx_expiry_receipts source budget [FxExpiryCase].
Proof.
  apply fx_expiry_receipts_one with (group := []); reflexivity.
Qed.

Lemma fx_expiry_target_receipt c :
  fx_expiry_receipts source budget [FxExpiryTarget c (System.target S c)].
Proof.
  destruct Hlaws as [_ [Htarget [_ Hbound]]].
  destruct (Htarget c) as [body Hbody].
  apply fx_expiry_receipts_one with (group := [body]).
  - cbn [fx_observe_expiry_event_source]; exists body; auto.
  - pose proof (Hbound c (System.target S c) body Hbody) as Hwork.
    change (fx_one_body_work (fx_body_weight budget) body + 0 <= fx_budget_target budget c); lia.
Qed.

Lemma fx_expiry_mem_receipt x members :
  fx_expiry_receipts source budget
    [FxExpirySet (snd (audit_finset_mem (fx_index_encoder EX) x members))].
Proof.
  destruct Hlaws as [Hencode [_ [Hbound _]]].
  destruct (Hencode x) as [body Hbody].
  pose proof (Hbound x (encode EX x) body Hbody) as Hwork.
  unfold audit_finset_mem, fx_index_encoder, audit_map_code_get.
  destruct (audit_trie_get (encode EX x) members) as [found trace].
  apply fx_expiry_receipts_one with (group := [body]).
  - cbn [fx_observe_expiry_event_source fx_nested_entries fx_nested_entry_source flat_map];
      constructor; [exact Hbody | constructor].
  - change (fx_one_body_work (fx_body_weight budget) body + 0 <=
      fx_budget_encode_x budget x + 0); lia.
Qed.

Lemma fx_expiry_set_receipt xs :
  fx_expiry_receipts source budget
    [FxExpirySet (snd (audit_finset_of_list (fx_index_encoder EX) xs))].
Proof.
  destruct Hlaws as [Hencode [_ [Hbound _]]].
  destruct (audit_finset_of_list (fx_index_encoder EX) xs) as [set events] eqn:Hset.
  pose proof (fx_plan_set_receipts EX source Hencode xs set events Hset) as Hreceipts.
  destruct Hreceipts as [bodies Hbodies].
  apply fx_expiry_receipts_one with (group := bodies).
  - exact Hbodies.
  - apply fx_nested_entries_body_bound with (source := source); assumption.
Qed.

Lemma fx_expiry_reader_map_receipt x (input : Map.t X (list C)) :
  fx_expiry_receipts source budget
    [FxExpiryReaders (snd (audit_map_get (fx_index_encoder EX) x input))].
Proof.
  destruct Hlaws as [Hencode [_ [Hbound _]]].
  destruct (Hencode x) as [body Hbody].
  pose proof (Hbound x (encode EX x) body Hbody) as Hwork.
  unfold audit_map_get, fx_index_encoder.
  destruct (audit_map_code_get (encode EX x) input) as [out trace].
  apply fx_expiry_receipts_one with (group := [body]).
  - cbn [fx_observe_expiry_event_source fx_observe_map_entries fx_nested_entry_source flat_map];
      constructor; [exact Hbody | constructor].
  - change (fx_one_body_work (fx_body_weight budget) body + 0 <=
      fx_budget_encode_x budget x + 0); lia.
Qed.

Lemma fx_expiry_map_get_receipt x (input : Map.t X (list X)) :
  fx_expiry_receipts source budget
    [FxExpiryMap (snd (audit_map_get (fx_index_encoder EX) x input))].
Proof.
  destruct Hlaws as [Hencode [_ [Hbound _]]].
  destruct (Hencode x) as [body Hbody].
  pose proof (Hbound x (encode EX x) body Hbody) as Hwork.
  unfold audit_map_get, fx_index_encoder.
  destruct (audit_map_code_get (encode EX x) input) as [out trace].
  apply fx_expiry_receipts_one with (group := [body]).
  - cbn [fx_observe_expiry_event_source fx_observe_map_entries fx_nested_entry_source flat_map];
      constructor; [exact Hbody | constructor].
  - change (fx_one_body_work (fx_body_weight budget) body + 0 <=
      fx_budget_encode_x budget x + 0); lia.
Qed.

Lemma fx_expiry_map_set_receipt x value (input : Map.t X (list X)) :
  fx_expiry_receipts source budget
    [FxExpiryMap (snd (audit_map_set (fx_index_encoder EX) x value input))].
Proof.
  destruct Hlaws as [Hencode [_ [Hbound _]]].
  destruct (Hencode x) as [body Hbody].
  pose proof (Hbound x (encode EX x) body Hbody) as Hwork.
  unfold audit_map_set, fx_index_encoder.
  destruct (audit_trie_set (encode EX x) (x, value) input) as [out trace].
  apply fx_expiry_receipts_one with (group := [body]).
  - cbn [fx_observe_expiry_event_source fx_observe_map_entries fx_nested_entry_source flat_map];
      constructor; [exact Hbody | constructor].
  - change (fx_one_body_work (fx_body_weight budget) body + 0 <=
      fx_budget_encode_x budget x + 0); lia.
Qed.

Lemma fx_expiry_reader_receipts members cs :
  fx_expiry_receipts source budget (snd (fx_observe_reader_uses EX S members cs)).
Proof.
  induction cs as [|c rest IH].
  - exact fx_expiry_case_receipt.
  - cbn [fx_observe_reader_uses].
    pose proof (fx_expiry_mem_receipt (System.target S c) members) as Hmem.
    destruct (audit_finset_mem (fx_index_encoder EX) (System.target S c) members) as [present mem].
    destruct (fx_observe_reader_uses EX S members rest) as [later tail].
    cbn [snd] in Hmem, IH |- *.
    change (fx_expiry_receipts source budget
      ([FxExpiryCase] ++ [FxExpiryTarget c (System.target S c)] ++ [FxExpirySet mem] ++ tail)).
    apply fx_expiry_receipts_app; [exact fx_expiry_case_receipt |].
    apply fx_expiry_receipts_app; [apply fx_expiry_target_receipt |].
    apply fx_expiry_receipts_app; assumption.
Qed.

Lemma fx_expiry_component_receipts ix members x :
  fx_expiry_receipts source budget (snd (fx_observe_component_uses EX S ix members x)).
Proof.
  pose proof (fx_expiry_mem_receipt x members) as Hmem.
  pose proof (fx_expiry_reader_map_receipt x (readers ix)) as Hread.
  unfold fx_observe_component_uses.
  destruct (audit_finset_mem (fx_index_encoder EX) x members) as [present mem].
  destruct (audit_map_get (fx_index_encoder EX) x (readers ix)) as [found read].
  pose proof (fx_expiry_reader_receipts members
    (match found with
    | Some cs => cs
    | None => []
    end)) as Huses.
  destruct (fx_observe_reader_uses EX S members
    (match found with
    | Some cs => cs
    | None => []
    end)) as [used calls].
  cbn [snd] in Hmem, Hread, Huses |- *.
  change (fx_expiry_receipts source budget
    ([FxExpiryCase] ++ [FxExpirySet mem] ++ [FxExpiryReaders read] ++ calls)).
  apply fx_expiry_receipts_app; [exact fx_expiry_case_receipt |].
  apply fx_expiry_receipts_app; [exact Hmem |].
  apply fx_expiry_receipts_app; assumption.
Qed.

Lemma fx_expiry_last_reader_receipts ix order x :
  fx_expiry_receipts source budget (snd (fx_observe_last_reader EX S ix order x)).
Proof.
  induction order as [|component rest IH].
  - exact fx_expiry_case_receipt.
  - destruct component as [|h body].
    + cbn [fx_observe_last_reader].
      destruct (fx_observe_last_reader EX S ix rest x) as [last events].
      cbn [snd] in IH |- *.
      change (fx_expiry_receipts source budget ([FxExpiryCase] ++ events)).
      apply fx_expiry_receipts_app; [exact fx_expiry_case_receipt | exact IH].
    + cbn [fx_observe_last_reader].
      destruct (fx_observe_last_reader EX S ix rest x) as [[last|] events]; cbn [snd] in IH |- *.
      * change (fx_expiry_receipts source budget ([FxExpiryCase] ++ events)).
        apply fx_expiry_receipts_app; [exact fx_expiry_case_receipt | exact IH].
      * pose proof (fx_expiry_set_receipt (h :: body)) as Hset.
        destruct (audit_finset_of_list (fx_index_encoder EX) (h :: body)) as [members set].
        pose proof (fx_expiry_component_receipts ix members x) as Huses.
        destruct (fx_observe_component_uses EX S ix members x) as [used calls].
        cbn [snd] in Hset, Huses |- *.
        change (fx_expiry_receipts source budget
          ([FxExpiryCase] ++ events ++ [FxExpirySet set] ++ calls)).
        apply fx_expiry_receipts_app; [exact fx_expiry_case_receipt |].
        apply fx_expiry_receipts_app; [exact IH |].
        apply fx_expiry_receipts_app; assumption.
Qed.

Lemma fx_expiry_fold_receipts ix order xs :
  fx_expiry_receipts source budget (snd (fx_observe_expiry_fold EX S ix order xs)).
Proof.
  induction xs as [|x rest IH].
  - exact fx_expiry_case_receipt.
  - cbn [fx_observe_expiry_fold].
    pose proof (fx_expiry_last_reader_receipts ix order x) as Hlast.
    destruct (fx_observe_expiry_fold EX S ix order rest) as [before tail].
    destruct (fx_observe_last_reader EX S ix order x) as [[h|] calls];
      cbn [snd] in IH, Hlast |- *.
    + pose proof (fx_expiry_map_get_receipt h before) as Hread.
      destruct (audit_map_get (fx_index_encoder EX) h before) as [old read].
      pose proof (fx_expiry_map_set_receipt h
        (x ::
          match old with
          | Some ys => ys
          | None => []
          end) before) as Hwrite.
      destruct (audit_map_set (fx_index_encoder EX) h
        (x ::
          match old with
          | Some ys => ys
          | None => []
          end) before) as [after write].
      cbn [snd] in Hread, Hwrite |- *.
      change (fx_expiry_receipts source budget
        ([FxExpiryCase] ++ tail ++ calls ++ [FxExpiryMap read] ++ [FxExpiryMap write])).
      apply fx_expiry_receipts_app; [exact fx_expiry_case_receipt |].
      apply fx_expiry_receipts_app; [exact IH |].
      apply fx_expiry_receipts_app; [exact Hlast |].
      apply fx_expiry_receipts_app; assumption.
    + change (fx_expiry_receipts source budget ([FxExpiryCase] ++ tail ++ calls)).
      apply fx_expiry_receipts_app; [exact fx_expiry_case_receipt |].
      apply fx_expiry_receipts_app; assumption.
Qed.

End ExpiryReceipts.

(** One expiry execution supplies its exact result, source bodies and separate frame bound. *)
Theorem fx_observe_expiry_fold_source : fx_observe_expiry_fold_source_statement.
Proof.
  intros X C A B EX S ix source budget order xs Hlaws.
  pose proof (fx_observe_expiry_fold_correct X C A EX S ix order xs) as Herase.
  pose proof (fx_observe_expiry_fold_bound X C A EX S ix order xs) as Hframe.
  pose proof (fx_expiry_fold_receipts EX S source budget Hlaws ix order xs) as Hreceipts.
  destruct (fx_observe_expiry_fold EX S ix order xs) as [out events].
  cbn [fst snd] in Herase, Hframe, Hreceipts |- *.
  destruct Hreceipts as [groups [Hsource Hwork]].
  exists groups; repeat split; try assumption; lia.
Qed.
