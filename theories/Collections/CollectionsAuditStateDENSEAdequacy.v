(** * Dense slot semantic adequacy

    Valid dense slots preserve the represented map through preparation and updates.
    For example, removing a present key leaves every other key's lookup unchanged.
    Builds on: CollectionsAuditState and the dense universe invariants. *)

From Stdlib Require Import List Bool NArith PArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsDenseSet CollectionsAuditState.
Import List.ListNotations.

(** * Checked observations and proofs *)

(** A valid prepared key reads the same entry as the original key. *)
Theorem prepared_key_refinement : prepared_key_refinement_statement.
Proof.
  intros K V E p m Hvalid; unfold key_valid in Hvalid.
  unfold prepared_lookup, Map.get; rewrite Hvalid; reflexivity.
Qed.

(** Valid prepared updates and removals agree with the ordinary map operations. *)
Theorem prepared_key_update : prepared_key_update_statement.
Proof.
  intros K V E p v m Hp; unfold key_valid in Hp.
  unfold prepared_update, prepared_remove, Map.set, Map.remove; rewrite Hp; split; reflexivity.
Qed.

(** Batch preparation and reading agree with key-by-key lookup for arbitrary slot maps. *)
Theorem slot_batch_refinement : slot_batch_refinement_statement.
Proof.
  intros K V E u m keys; unfold prepare_slots, read_slots; rewrite map_map.
  apply map_ext; intro k; unfold slot_lookup, prepare_slot.
  destruct (Map.get E k (dense_index u)); reflexivity.
Qed.

(** Two valid slot maps with equal key lookups have equal representations. *)
Theorem slot_canonical : slot_canonical_statement.
Proof.
  intros K V E u a b [Huniverse [Hwa Hba]] [_ [Hwb Hbb]] Hlookup.
  apply (Map.extensionality N_encoding a b); [exact Hwa|exact Hwb|].
  intro i; destruct (N.lt_ge_cases i (dense_length u)) as [Hin|Hout].
  - destruct (dense_index_position E u i Huniverse Hin) as [k Hslot].
    specialize (Hlookup k); unfold slot_lookup in Hlookup; rewrite Hslot in Hlookup; exact Hlookup.
  - destruct (Map.get N_encoding i a) as [va|] eqn:Ha;
      destruct (Map.get N_encoding i b) as [vb|] eqn:Hb; try reflexivity.
    + specialize (Hba i va Ha); lia.
    + specialize (Hba i va Ha); lia.
    + specialize (Hbb i vb Hb); lia.
Qed.

(** A successful update of a valid slot map preserves validity, writes the key and frames other
    keys. *)
Theorem slot_update : slot_update_statement.
Proof.
  intros K V E u m m' k v [Huniverse [Hmap Hbound]] Hupdate.
  unfold slot_update in Hupdate.
  destruct (Map.get E k (dense_index u)) as [i|] eqn:Hslot; [|discriminate].
  inversion Hupdate; subst m'; clear Hupdate.
  split.
  - split; [exact Huniverse|]; split; [apply Map.wf_set; exact Hmap|].
    intros j value Hget; destruct (N.eq_dec j i) as [->|Hneq].
    + eapply dense_lookup_bound; eassumption.
    + rewrite Map.get_set_other in Hget by exact Hneq; eapply Hbound; exact Hget.
  - split.
    + unfold slot_lookup; rewrite Hslot, Map.get_set_same; reflexivity.
    + intros x Hneq; unfold slot_lookup.
      destruct (Map.get E x (dense_index u)) as [j|] eqn:Hx; [|reflexivity].
      assert (Hji : j <> i).
      { intro Heq; subst j.
        pose proof (dense_lookup_eqb E u k x i i Huniverse Hslot Hx) as Heqb.
        rewrite N.eqb_refl in Heqb; symmetry in Heqb; apply Pos.eqb_eq in Heqb.
        apply (encode_injective E) in Heqb; contradiction. }
      rewrite Map.get_set_other by exact Hji; reflexivity.
Qed.

(** Enumerated keys are exactly the keys whose slot lookups succeed. *)
Lemma slot_elements_keys :
  forall K V (E : encoding K) (u : dense_universe K) (m : slot_map V),
    map fst (CollectionsAuditState.slot_elements E u m) =
      filter (fun k =>
        match slot_lookup E u m k with
        | Some _ => true
        | None => false
        end) (dense_keys u).
Proof.
  intros K V E u m; unfold slot_elements.
  generalize (dense_keys u); intro keys; induction keys as [|k rest IH]; [reflexivity|].
  cbn [flat_map map filter]; destruct (slot_lookup E u m k); cbn; rewrite IH; reflexivity.
Qed.

(** For a valid slot map, enumeration exactly matches lookups and contains no duplicate keys. *)
Theorem slot_elements : slot_elements_statement.
Proof.
  intros K V E u m [Huniverse [Hmap Hbound]]; split.
  - intros k v; unfold slot_elements; rewrite in_flat_map; split.
    + intros [x [Hx Hin]].
      destruct (slot_lookup E u m x) as [value|] eqn:Hlookup; cbn in Hin; [|contradiction].
      destruct Hin as [Heq|Hfalse]; [inversion Heq; subst; exact Hlookup|contradiction].
    + intro Hlookup; exists k; split.
      * apply (proj1 (dense_lookup_member E u k Huniverse)).
        unfold slot_lookup in Hlookup; destruct (Map.get E k (dense_index u)) as [i|] eqn:Hslot;
          [now exists i|discriminate].
      * rewrite Hlookup; cbn; auto.
  - rewrite slot_elements_keys; apply NoDup_filter; exact (proj1 Huniverse).
Qed.

(** Successful removal from a valid slot map preserves validity, clears the key and frames other
    keys. *)
Theorem slot_remove_frame : slot_remove_frame_statement.
Proof.
  intros K V E u m m' k [Huniverse [Hmap Hbound]] Hremove.
  unfold slot_remove, prepare_slot in Hremove.
  destruct (Map.get E k (dense_index u)) as [i|] eqn:Hslot; [|discriminate].
  inversion Hremove; subst m'; clear Hremove.
  split.
  - split; [exact Huniverse|]; split; [apply Map.wf_remove; exact Hmap|].
    intros j value Hget; destruct (N.eq_dec j i) as [->|Hneq].
    + rewrite Map.get_remove_same in Hget; discriminate.
    + rewrite Map.get_remove_other in Hget by exact Hneq; eapply Hbound; exact Hget.
  - split.
    + unfold slot_lookup; rewrite Hslot, Map.get_remove_same; reflexivity.
    + intros x Hneq; unfold slot_lookup.
      destruct (Map.get E x (dense_index u)) as [j|] eqn:Hx; [|reflexivity].
      assert (Hji : j <> i).
      { intro Heq; subst j.
        pose proof (dense_lookup_eqb E u k x i i Huniverse Hslot Hx) as Heqb.
        rewrite N.eqb_refl in Heqb; symmetry in Heqb; apply Pos.eqb_eq in Heqb.
        apply (encode_injective E) in Heqb; contradiction. }
      rewrite Map.get_remove_other by exact Hji; reflexivity.
Qed.

(** A successful slot update of a refining map refines the corresponding abstract map update. *)
Theorem slot_update_refines : slot_update_refines_statement.
Proof.
  intros K V E u m m' abstract k value [Hvalid [Habstract Hlookup]] Hupdate.
  destruct (slot_update K V E u m m' k value Hvalid Hupdate) as [Hvalid' [Hsame Hframe]].
  split; [exact Hvalid'|]; split; [apply Map.wf_set; exact Habstract|].
  intro x; destruct (Pos.eq_dec (encode E x) (encode E k)) as [Heq|Hneq].
  - apply (encode_injective E) in Heq; subst x; rewrite Hsame, Map.get_set_same; reflexivity.
  - assert (Hx : x <> k) by (intro Heq; subst x; contradiction).
    rewrite Hframe by exact Hx; rewrite Map.get_set_other by exact Hx; apply Hlookup.
Qed.

(** A successful slot removal from a refining map refines the corresponding abstract map
    removal. *)
Theorem slot_remove_refines : slot_remove_refines_statement.
Proof.
  intros K V E u m m' abstract k [Hvalid [Habstract Hlookup]] Hremove.
  destruct (slot_remove_frame K V E u m m' k Hvalid Hremove) as [Hvalid' [Hsame Hframe]].
  split; [exact Hvalid'|]; split; [apply Map.wf_remove; exact Habstract|].
  intro x; destruct (Pos.eq_dec (encode E x) (encode E k)) as [Heq|Hneq].
  - apply (encode_injective E) in Heq; subst x; rewrite Hsame, Map.get_remove_same; reflexivity.
  - assert (Hx : x <> k) by (intro Heq; subst x; contradiction).
    rewrite Hframe by exact Hx; rewrite Map.get_remove_other by exact Hx; apply Hlookup.
Qed.

(** For a refining slot map, emitted bindings match abstract lookups and have no duplicate keys. *)
Theorem slot_elements_refines : slot_elements_refines_statement.
Proof.
  intros K V E u m abstract [Hvalid [Habstract Hlookup]].
  destruct (slot_elements K V E u m Hvalid) as [Hmembers Hnodup].
  split; [intros k v; rewrite Hmembers, Hlookup; reflexivity|exact Hnodup].
Qed.

(** Converting a valid slot map to a map produces a refining abstract map. *)
Theorem slot_to_map : slot_to_map_statement.
Proof.
  intros K V E u m Hvalid; split; [exact Hvalid|].
  split; [unfold slot_to_map; apply Map.wf_of_list|].
  intro k; unfold slot_to_map; rewrite Map.get_of_list.
  destruct (find (fun kv => Pos.eqb (encode E (fst kv)) (encode E k))
    (rev (CollectionsAuditState.slot_elements E u m))) as [[found value]|] eqn:Hfind; cbn.
  - apply find_some in Hfind as [Hin Hcode]; cbn in Hcode.
    apply Pos.eqb_eq in Hcode; apply (encode_injective E) in Hcode; subst found.
    apply in_rev in Hin.
    apply (proj1 (proj1 (slot_elements K V E u m Hvalid) k value)) in Hin.
    exact Hin.
  - destruct (slot_lookup E u m k) as [value|] eqn:Hlookup; [|reflexivity].
    exfalso.
    assert (Hin : In (k,value) (rev (CollectionsAuditState.slot_elements E u m))).
    { apply (proj1 (in_rev _ _)).
      apply (proj2 (proj1 (slot_elements K V E u m Hvalid) k value)); exact Hlookup. }
    pose proof (find_none _ _ Hfind (k,value) Hin) as Hfalse.
    cbn in Hfalse; rewrite Pos.eqb_refl in Hfalse; discriminate.
Qed.

(** A conversion step writes a present abstract binding to its prepared slot. *)
Definition slot_fill_step {K V} (E : encoding K) (u : dense_universe K) (abstract : Map.t K V)
    (m : slot_map V) (k : K) : slot_map V :=
  match Map.get E k abstract, prepare_slot E u k with
  | Some value, Some i => Map.set N_encoding i value m
  | _, _ => m
  end.

(** Each conversion step preserves the bounded-slot validity invariant. *)
Lemma slot_fill_step_valid :
  forall K V (E : encoding K) (u : dense_universe K) (abstract : Map.t K V) m k,
    slot_valid E u m -> slot_valid E u (slot_fill_step E u abstract m k).
Proof.
  intros K V E u abstract m k Hvalid; unfold slot_fill_step.
  destruct (Map.get E k abstract) as [value|]; [|exact Hvalid].
  destruct (prepare_slot E u k) as [i|] eqn:Hslot; [|exact Hvalid].
  assert (Hupdate : CollectionsAuditState.slot_update E u m k value =
    Some (Map.set N_encoding i value m)).
  { unfold CollectionsAuditState.slot_update, prepare_slot in *; rewrite Hslot; reflexivity. }
  exact (proj1 (slot_update K V E u m _ k value Hvalid Hupdate)).
Qed.

(** A conversion step at another key preserves this key's lookup. *)
Lemma slot_fill_step_other :
  forall K V (E : encoding K) (u : dense_universe K) (abstract : Map.t K V) m x k,
    slot_valid E u m -> x <> k ->
    slot_lookup E u (slot_fill_step E u abstract m k) x = slot_lookup E u m x.
Proof.
  intros K V E u abstract m x k Hvalid Hneq; unfold slot_fill_step.
  destruct (Map.get E k abstract) as [value|]; [|reflexivity].
  destruct (prepare_slot E u k) as [i|] eqn:Hslot; [|reflexivity].
  assert (Hupdate : CollectionsAuditState.slot_update E u m k value =
    Some (Map.set N_encoding i value m)).
  { unfold CollectionsAuditState.slot_update, prepare_slot in *; rewrite Hslot; reflexivity. }
  destruct (slot_update K V E u m _ k value Hvalid Hupdate) as [_ [_ Hframe]].
  apply Hframe; exact Hneq.
Qed.

(** A step at a known key and abstract binding installs exactly that value. *)
Lemma slot_fill_step_same :
  forall K V (E : encoding K) (u : dense_universe K) (abstract : Map.t K V) m k i value,
    slot_valid E u m -> Map.get E k abstract = Some value -> prepare_slot E u k = Some i ->
    slot_lookup E u (slot_fill_step E u abstract m k) k = Some value.
Proof.
  intros K V E u abstract m k i value Hvalid Hget Hslot; unfold slot_fill_step; rewrite Hget, Hslot.
  assert (Hupdate : CollectionsAuditState.slot_update E u m k value =
    Some (Map.set N_encoding i value m)).
  { unfold CollectionsAuditState.slot_update, prepare_slot in *; rewrite Hslot; reflexivity. }
  exact (proj1 (proj2 (slot_update K V E u m _ k value Hvalid Hupdate))).
Qed.

(** Folding conversion steps preserves slot validity. *)
Lemma slot_fill_valid :
  forall K V (E : encoding K) (u : dense_universe K) (abstract : Map.t K V) keys m,
    slot_valid E u m -> slot_valid E u (fold_left (slot_fill_step E u abstract) keys m).
Proof.
  intros K V E u abstract keys; induction keys as [|k rest IH]; intros m Hvalid; [exact Hvalid|].
  cbn [fold_left]; apply IH, slot_fill_step_valid; exact Hvalid.
Qed.

(** If the abstract map has no binding, conversion never changes that key. *)
Lemma slot_fill_absent :
  forall K V (E : encoding K) (u : dense_universe K) (abstract : Map.t K V) keys m k,
    slot_valid E u m -> Map.get E k abstract = None ->
    slot_lookup E u (fold_left (slot_fill_step E u abstract) keys m) k = slot_lookup E u m k.
Proof.
  intros K V E u abstract keys; induction keys as [|x rest IH];
    intros m k Hvalid Hnone; [reflexivity|].
  cbn [fold_left]; rewrite IH by (try apply slot_fill_step_valid; assumption).
  destruct (Pos.eq_dec (encode E k) (encode E x)) as [Heq|Hneq].
  - apply (encode_injective E) in Heq; subst x; unfold slot_fill_step; rewrite Hnone; reflexivity.
  - apply slot_fill_step_other; [exact Hvalid|intro Heq; subst x; contradiction].
Qed.

(** A correct binding remains correct through any later conversion steps. *)
Lemma slot_fill_preserves :
  forall K V (E : encoding K) (u : dense_universe K) (abstract : Map.t K V) keys m k i value,
    slot_valid E u m -> Map.get E k abstract = Some value -> prepare_slot E u k = Some i ->
    slot_lookup E u m k = Some value ->
    slot_lookup E u (fold_left (slot_fill_step E u abstract) keys m) k = Some value.
Proof.
  intros K V E u abstract keys; induction keys as [|x rest IH];
    intros m k i value Hvalid Hget Hslot Hcurrent;
    [exact Hcurrent|].
  cbn [fold_left]; apply IH with (i := i); try assumption.
  - apply slot_fill_step_valid; exact Hvalid.
  - destruct (Pos.eq_dec (encode E k) (encode E x)) as [Heq|Hneq].
    + apply (encode_injective E) in Heq; subst x; eapply slot_fill_step_same; eassumption.
    + rewrite slot_fill_step_other by (try assumption; intro Heq; subst x; contradiction).
      exact Hcurrent.
Qed.

(** Once a known key occurs in the input list, its abstract binding is installed. *)
Lemma slot_fill_present :
  forall K V (E : encoding K) (u : dense_universe K) (abstract : Map.t K V) keys m k i value,
    slot_valid E u m -> Map.get E k abstract = Some value -> prepare_slot E u k = Some i ->
    In k keys ->
    slot_lookup E u (fold_left (slot_fill_step E u abstract) keys m) k = Some value.
Proof.
  intros K V E u abstract keys; induction keys as [|x rest IH];
    intros m k i value Hvalid Hget Hslot Hin;
    [contradiction|].
  cbn [fold_left]; destruct Hin as [Heq|Hin].
  - subst x; eapply slot_fill_preserves; try eassumption.
    + apply slot_fill_step_valid; exact Hvalid.
    + eapply slot_fill_step_same; eassumption.
  - apply IH with (i := i); try assumption; apply slot_fill_step_valid; exact Hvalid.
Qed.

(** For a well-formed universe, conversion yields valid slots, preserves prepared-key lookups and
    returns none for unprepared keys. *)
Theorem slot_of_map : slot_of_map_statement.
Proof.
  intros K V E u abstract Huniverse.
  assert (Hempty : slot_valid E u (@Map.empty N V)).
  { split; [exact Huniverse|]; split; [apply Map.wf_empty|].
    intros i value Hget; rewrite Map.get_empty in Hget; discriminate. }
  unfold slot_of_map; change (let result :=
    fold_left (slot_fill_step E u abstract) (dense_keys u) Map.empty in
    slot_valid E u result /\ forall k, slot_lookup E u result k =
      match prepare_slot E u k with
      | Some _ => Map.get E k abstract
      | None => None
      end).
  split; [apply slot_fill_valid; exact Hempty|].
  intro k; destruct (prepare_slot E u k) as [i|] eqn:Hslot.
  - destruct (Map.get E k abstract) as [value|] eqn:Hget.
    + eapply slot_fill_present; try eassumption.
      apply (proj1 (dense_lookup_member E u k Huniverse)); exists i; exact Hslot.
    + rewrite (slot_fill_absent K V E u abstract (dense_keys u) Map.empty k Hempty Hget).
      unfold slot_lookup, prepare_slot in *; rewrite Hslot, Map.get_empty; reflexivity.
  - unfold slot_lookup, prepare_slot in *; rewrite Hslot; reflexivity.
Qed.

(** The empty slot map is valid for every well-formed universe. *)
Theorem slot_empty : slot_empty_statement.
Proof.
  intros K V E u Huniverse; split; [exact Huniverse|]; split; [apply Map.wf_empty|].
  intros i value Hget; rewrite Map.get_empty in Hget; discriminate.
Qed.

(** For valid slots, every key in the universe admits a successful update result. *)
Theorem slot_present_update : slot_present_update_statement.
Proof.
  intros K V E u m k value [Huniverse Hmap] Hin.
  apply (proj2 (dense_lookup_member E u k Huniverse)) in Hin as [i Hslot].
  exists (Map.set N_encoding i value m).
  unfold CollectionsAuditState.slot_update; rewrite Hslot; reflexivity.
Qed.

(** For valid slots and a successful preparation, the index is in range and its read agrees with
    lookup. *)
Theorem slot_prepare : slot_prepare_statement.
Proof.
  intros K V E u m k i [Huniverse Hmap] Hslot; split.
  - eapply dense_lookup_bound; eassumption.
  - unfold slot_read, slot_lookup, prepare_slot in *; rewrite Hslot; reflexivity.
Qed.

(** A key with no prepared slot is rejected by lookup and update. *)
Theorem slot_outside : slot_outside_statement.
Proof.
  intros K V E u m k v Hslot; unfold prepare_slot in Hslot.
  unfold slot_lookup, CollectionsAuditState.slot_update; rewrite Hslot; split; reflexivity.
Qed.

(** A key with no prepared slot is rejected by removal. *)
Theorem slot_remove_outside : slot_remove_outside_statement.
Proof.
  intros K V E u m k Hslot; unfold slot_remove; rewrite Hslot; reflexivity.
Qed.

(** A successfully prepared token is valid and retains the original key. *)
Theorem dense_token_prepare : dense_token_prepare_statement.
Proof.
  intros K E u key token Htoken; unfold dense_token_prepare in Htoken.
  destruct (prepare_slot E u key) as [i|] eqn:Hslot; [|discriminate].
  inversion Htoken; subst token; split; [exact Hslot|reflexivity].
Qed.

(** A valid token reads the same value as lookup of its key. *)
Theorem dense_token_read : dense_token_read_statement.
Proof.
  intros K V E u token m Hvalid; unfold dense_token_valid, prepare_slot in Hvalid.
  unfold dense_token_read, slot_read, slot_lookup; rewrite Hvalid; reflexivity.
Qed.

(** Token preparation fails exactly when ordinary slot preparation fails. *)
Theorem dense_token_scope : dense_token_scope_statement.
Proof.
  intros K E u key; unfold CollectionsAuditState.dense_token_prepare.
  destruct (prepare_slot E u key); split; intro H; try discriminate; reflexivity.
Qed.
