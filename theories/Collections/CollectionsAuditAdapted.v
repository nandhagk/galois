(** * Adapted complete source bounds

    These compositions require actual source/body laws only for genuine foreign callbacks.
    For example, saved predecessor reads remain concrete library calls with no foreign price law.
    Builds on: complete input recurrences and the shared actual-call adapter. *)

From Stdlib Require Import List PArith NArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsUnionFind
  CollectionsAuditCallback
  CollectionsAuditEncoderBudget
  CollectionsAuditUnionFindWhole
  CollectionsAuditUnionFind
  CollectionsAuditUnionFindAdapters
  CollectionsAuditEncoding.
Import List.ListNotations.

(** Genuine foreign source laws bind the actual retained inputs, results and bodies. *)
Definition audit_uf_whole_input_bound_adapted_statement : Prop :=
  forall K CE (enc : K -> positive * list CE) work budget enc_source,
    audit_external_callback_adapter enc work enc_source budget ->
    (forall fuel key forest,
      audit_uf_source_work work (snd (audit_uf_find_fuel enc fuel key forest)) <=
        audit_uf_find_input_budget enc budget fuel key forest) /\
    (forall x y forest,
      audit_uf_source_work work (snd (audit_uf_union enc x y forest)) <=
        audit_uf_union_input_budget enc budget x y forest) /\
    (forall x y forest,
      audit_uf_source_work work (snd (audit_uf_equivb enc x y forest)) <=
        audit_uf_equivb_input_budget enc budget x y forest) /\
    (forall actions forest,
      audit_uf_source_work work (snd (audit_uf_history enc actions forest)) <=
        audit_uf_history_input_budget enc budget actions forest).

(** Genuine foreign source laws bind the actual retained inputs, results and bodies. *)
Definition audit_uf_pair_whole_input_bound_adapted_statement : Prop :=
  forall A B EA EB (first : A -> positive * list EA) (second : B -> positive * list EB)
      first_work second_work first_budget second_budget inputs first_source second_source,
    audit_external_callback_adapter first first_work first_source first_budget ->
    audit_external_callback_adapter second second_work second_source second_budget ->
    let enc := audit_uf_pair_encode first second in
    let budget := audit_pair_input_budget first second first_budget second_budget in
    let actions := map (fun xy => AuditUFUnion (fst xy) (snd xy)) inputs in
    audit_uf_source_work (audit_uf_pair_encoder_work first_work second_work)
      (snd (audit_uf_pair_of_unions first second inputs)) <=
      audit_uf_history_input_budget enc budget actions UnionFind.make.

(** Genuine foreign source laws bind the actual retained inputs, results and bodies. *)
Definition audit_uf_list_whole_input_bound_adapted_statement : Prop :=
  forall A CE (element : A -> positive * list CE) work budget inputs element_source,
    audit_external_callback_adapter element work element_source budget ->
    let enc := audit_uf_list_encode element in
    let key_budget := audit_list_input_budget element budget in
    let actions := map (fun xy => AuditUFUnion (fst xy) (snd xy)) inputs in
    audit_uf_source_work (audit_uf_list_encoder_work work)
      (snd (audit_uf_list_of_unions element inputs)) <=
      audit_uf_history_input_budget enc key_budget actions UnionFind.make.

(** Genuine foreign source laws bind the actual retained inputs, results and bodies. *)
Definition audit_uf_branches_whole_input_bound_adapted_statement : Prop :=
  forall K CE (enc : K -> positive * list CE) work budget left right forest enc_source,
    audit_external_callback_adapter enc work enc_source budget ->
    let branches := audit_uf_branches enc left right forest in
    audit_uf_source_work work (snd (fst branches)) +
      audit_uf_source_work work (snd (snd branches)) <=
    audit_uf_history_input_budget enc budget left forest +
      audit_uf_history_input_budget enc budget right forest.

(** Genuine foreign source laws bind the actual retained inputs, results and bodies. *)
Definition audit_pair_input_bound_adapted_statement : Prop :=
  forall A B EA EB (first : A -> positive * list EA) (second : B -> positive * list EB)
      first_work second_work first_budget second_budget key first_source second_source,
    audit_external_callback_adapter first first_work first_source first_budget ->
    audit_external_callback_adapter second second_work second_source second_budget ->
    audit_pair_events_work first_work second_work (snd (audit_pair_encode first second key)) <=
      audit_pair_input_budget first second first_budget second_budget key.

(** Genuine foreign source laws bind the actual retained inputs, results and bodies. *)
Definition audit_list_input_bound_adapted_statement : Prop :=
  forall A CE (element : A -> positive * list CE) element_work element_budget keys element_source,
    audit_external_callback_adapter element element_work element_source element_budget ->
    audit_list_events_work element_work (snd (audit_list_encode element keys)) <=
      audit_list_input_budget element element_budget keys.
