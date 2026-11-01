(** * Persistent union-find observer adequacy

    The observer preserves forest results and accounts for every selected source frame.
    For example, path compression writes into the forest returned by the recursive find.
    Builds on: CollectionsAuditUnionFind and concrete map and traversal adequacy. *)

From Stdlib Require Import List PArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsUnionFind CollectionsAuditUnionFind CollectionsAuditMap CollectionsAuditPrimitive
  CollectionsAuditMapTraverse CollectionsAuditUnion CollectionsAuditElements
  CollectionsAuditMapAdequacy CollectionsAuditPrimitiveAdequacy CollectionsAuditMapTraverseAdequacy
  CollectionsAuditUnionAdequacy CollectionsAuditElementsAdequacy.
Import List.ListNotations.

(** * Exact source results *)

(** When encoder codes agree with the original encoding on every key, fuelled find returns
    exactly the original representative and compressed forest. *)
Theorem audit_uf_find_fuel_erases : audit_uf_find_fuel_erases_statement.
Proof.
  intros K CE enc original fuel; induction fuel as [|fuel IH]; intros key forest Henc.
  - reflexivity.
  - cbn [audit_uf_find_fuel UnionFind.find_fuel].
    pose proof (audit_map_get_erases K K CE enc original key
      (UnionFind.parents forest) (Henc key)) as Hread.
    destruct (audit_map_get enc key (UnionFind.parents forest)) as [parent reads].
    cbv beta iota zeta delta [fst] in Hread; rewrite <- Hread.
    destruct parent as [next|]; try reflexivity.
    specialize (IH next forest Henc).
    destruct (audit_uf_find_fuel enc fuel next forest) as [[root compressed] child].
    cbv beta iota zeta delta [fst] in IH; rewrite <- IH.
    pose proof (audit_map_set_erases K K CE enc original key root
      (UnionFind.parents compressed) (Henc key)) as Hwrite.
    destruct (audit_map_set enc key root (UnionFind.parents compressed)) as [parents writes].
    cbv beta iota zeta delta [fst] in Hwrite; cbn [fst UnionFind.redirect]; now rewrite Hwrite.
Qed.

(** When encoder codes agree with the original encoding on every key, find returns exactly
    the original representative and compressed forest at the cached maximum-rank fuel. *)
Theorem audit_uf_find_erases : audit_uf_find_erases_statement.
Proof.
  intros K CE enc original key forest Henc; apply audit_uf_find_fuel_erases; exact Henc.
Qed.

Lemma audit_uf_rank_of_erases K CE enc (original : encoding K) forest key
    (Henc : forall k, fst (enc k) = encode original k) :
  fst (@audit_uf_rank_of K CE enc forest key) = UnionFind.rank_of original forest key.
Proof.
  unfold audit_uf_rank_of, UnionFind.rank_of.
  pose proof (audit_map_get_erases K nat CE enc original key
    (UnionFind.ranks forest) (Henc key)) as Hread.
  destruct (audit_map_get enc key (UnionFind.ranks forest)) as [found calls].
  cbv beta iota zeta delta [fst] in Hread; rewrite <- Hread; destruct found; reflexivity.
Qed.

Lemma audit_uf_touch_erases K CE enc (original : encoding K) key forest
    (Henc : forall k, fst (enc k) = encode original k) :
  fst (@audit_uf_touch K CE enc key forest) = UnionFind.touch original key forest.
Proof.
  unfold audit_uf_touch, UnionFind.touch.
  pose proof (audit_map_get_erases K nat CE enc original key
    (UnionFind.ranks forest) (Henc key)) as Hread.
  destruct (audit_map_get enc key (UnionFind.ranks forest)) as [found reads].
  cbv beta iota zeta delta [fst] in Hread; rewrite <- Hread; destruct found; try reflexivity.
  pose proof (audit_map_set_erases K nat CE enc original key 0
    (UnionFind.ranks forest) (Henc key)) as Hwrite.
  destruct (audit_map_set enc key 0 (UnionFind.ranks forest)) as [ranks writes].
  cbv beta iota zeta delta [fst] in Hwrite; cbn [fst]; now rewrite Hwrite.
Qed.

Lemma audit_uf_link_erases K CE enc (original : encoding K) child root raise forest
    (Henc : forall k, fst (enc k) = encode original k) :
  fst (@audit_uf_link K CE enc child root raise forest) =
    UnionFind.link original child root raise forest.
Proof.
  unfold audit_uf_link, UnionFind.link; destruct raise.
  - pose proof (audit_uf_rank_of_erases K CE enc original forest root Henc) as Hrank.
    destruct (audit_uf_rank_of enc forest root) as [rank reads].
    cbv beta iota zeta delta [fst] in Hrank; rewrite <- Hrank.
    pose proof (audit_map_set_erases K K CE enc original child root
      (UnionFind.parents forest) (Henc child)) as Hp.
    pose proof (audit_map_set_erases K nat CE enc original root (S rank)
      (UnionFind.ranks forest) (Henc root)) as Hr.
    destruct (audit_map_set enc child root (UnionFind.parents forest)) as [parents pe].
    destruct (audit_map_set enc root (S rank) (UnionFind.ranks forest)) as [ranks re].
    cbv beta iota zeta delta [fst] in Hp, Hr; cbn [fst]; now rewrite Hp, Hr.
  - pose proof (audit_map_set_erases K K CE enc original child root
      (UnionFind.parents forest) (Henc child)) as Hp.
    destruct (audit_map_set enc child root (UnionFind.parents forest)) as [parents pe].
    cbv beta iota zeta delta [fst] in Hp; cbn [fst UnionFind.redirect]; now rewrite Hp.
Qed.

(** When encoder codes agree with the original encoding on every key, union returns exactly
    the forest produced by the original union in the selected equality and rank branch. *)
Theorem audit_uf_union_erases : audit_uf_union_erases_statement.
Proof.
  intros K CE enc original x y forest Henc; unfold audit_uf_union, UnionFind.union.
  pose proof (audit_uf_find_erases K CE enc original x forest Henc) as Hfirst.
  destruct (audit_uf_find enc x forest) as [[rx first] xe].
  cbv beta iota zeta delta [fst] in Hfirst; rewrite <- Hfirst.
  pose proof (audit_uf_find_erases K CE enc original y first Henc) as Hsecond.
  destruct (audit_uf_find enc y first) as [[ry second] ye].
  cbv beta iota zeta delta [fst] in Hsecond; rewrite <- Hsecond.
  pose proof (Henc rx) as Hx; pose proof (Henc ry) as Hy.
  destruct (enc rx) as [cx ex]; destruct (enc ry) as [cy ey].
  cbv beta iota zeta delta [fst] in Hx, Hy.
  pose proof (audit_positive_eqb_erases cx cy) as Heq.
  destruct (audit_positive_eqb cx cy) as [equal eq].
  cbv beta iota zeta delta [fst] in Heq; unfold UnionFind.key_eqb; rewrite <- Hx, <- Hy, <- Heq.
  destruct equal.
  - pose proof (audit_uf_touch_erases K CE enc original rx second Henc) as Htouch.
    destruct (audit_uf_touch enc rx second); exact Htouch.
  - pose proof (audit_uf_rank_of_erases K CE enc original second rx Henc) as Hrx.
    pose proof (audit_uf_rank_of_erases K CE enc original second ry Henc) as Hry.
    destruct (audit_uf_rank_of enc second rx) as [rankx re1].
    destruct (audit_uf_rank_of enc second ry) as [ranky re2].
    cbv beta iota zeta delta [fst] in Hrx, Hry; rewrite <- Hrx, <- Hry.
    destruct (Nat.compare rankx ranky);
      match goal with
      | |- context [audit_uf_link enc ?a ?b ?r second] =>
        pose proof (audit_uf_link_erases K CE enc original a b r second Henc) as Hlink;
        destruct (audit_uf_link enc a b r second); exact Hlink
      end.
Qed.

(** When encoder codes agree with the original encoding on every key, equivalence testing
    returns exactly the original boolean and second compressed forest. *)
Theorem audit_uf_equivb_erases : audit_uf_equivb_erases_statement.
Proof.
  intros K CE enc original x y forest Henc; unfold audit_uf_equivb, UnionFind.equivb.
  pose proof (audit_uf_find_erases K CE enc original x forest Henc) as Hfirst.
  destruct (audit_uf_find enc x forest) as [[rx first] xe].
  cbv beta iota zeta delta [fst] in Hfirst; rewrite <- Hfirst.
  pose proof (audit_uf_find_erases K CE enc original y first Henc) as Hsecond.
  destruct (audit_uf_find enc y first) as [[ry second] ye].
  cbv beta iota zeta delta [fst] in Hsecond; rewrite <- Hsecond.
  pose proof (Henc rx) as Hx; pose proof (Henc ry) as Hy.
  destruct (enc rx) as [cx ex]; destruct (enc ry) as [cy ey].
  cbv beta iota zeta delta [fst] in Hx, Hy.
  pose proof (audit_positive_eqb_erases cx cy) as Heq.
  destruct (audit_positive_eqb cx cy) as [equal eq].
  cbv beta iota zeta delta [fst] in Heq; cbn [fst UnionFind.key_eqb]; now rewrite Heq, Hx, Hy.
Qed.

(** For every forest, discarding support events returns exactly the original ordered key list
    obtained from the parent and rank domains. *)
Theorem audit_uf_keys_erases : audit_uf_keys_erases_statement.
Proof.
  intros K CE original forest; unfold audit_uf_keys, UnionFind.keys.
  pose proof (audit_map_transform_erases K K unit unit (fun _ => (tt, [])) (fun _ => tt)
    (UnionFind.parents forest) (fun _ => eq_refl)) as Hp.
  pose proof (audit_map_transform_erases K nat unit unit (fun _ => (tt, [])) (fun _ => tt)
    (UnionFind.ranks forest) (fun _ => eq_refl)) as Hr.
  destruct (audit_map_transform (fun _ : K => (tt, @nil unit))
    (UnionFind.parents forest)) as [parents pe].
  destruct (audit_map_transform (fun _ : nat => (tt, @nil unit))
    (UnionFind.ranks forest)) as [ranks re].
  cbv beta iota zeta delta [fst] in Hp, Hr; rewrite <- Hp, <- Hr.
  pose proof (audit_finset_union_erases K original parents ranks) as Hu.
  destruct (audit_finset_union parents ranks) as [merged ue].
  cbv beta iota zeta delta [fst] in Hu; rewrite <- Hu.
  pose proof (audit_finset_elements_erases K merged) as He.
  destruct (audit_finset_elements merged); exact He.
Qed.

(** * Event counts *)

Lemma audit_uf_find_fuel_max_rank K CE (enc : K -> positive * list CE) fuel : forall key forest,
  UnionFind.max_rank (snd (fst (audit_uf_find_fuel enc fuel key forest))) =
    UnionFind.max_rank forest.
Proof.
  induction fuel as [|fuel IH]; intros key forest; cbn [audit_uf_find_fuel]; try reflexivity.
  destruct (audit_map_get enc key (UnionFind.parents forest)) as [[next|] reads];
    try reflexivity.
  specialize (IH next forest).
  destruct (audit_uf_find_fuel enc fuel next forest) as [[root compressed] child].
  destruct (audit_map_set enc key root (UnionFind.parents compressed)); exact IH.
Qed.

(** For any encoder and forest, fuelled find emits at most one terminal event plus three
    events per unit of input fuel. *)
Theorem audit_uf_find_fuel_count : audit_uf_find_fuel_count_statement.
Proof.
  intros K CE enc fuel; induction fuel as [|fuel IH]; intros key forest; cbn [audit_uf_find_fuel].
  - cbn; lia.
  - destruct (audit_map_get enc key (UnionFind.parents forest)) as [[next|] reads].
    + specialize (IH next forest).
      destruct (audit_uf_find_fuel enc fuel next forest) as [[root compressed] child].
      destruct (audit_map_set enc key root (UnionFind.parents compressed)) as [parents writes].
      cbn in *; rewrite length_app; cbn; lia.
    + cbn; lia.
Qed.

Lemma audit_uf_touch_count K CE (enc : K -> positive * list CE) key forest :
  length (snd (audit_uf_touch enc key forest)) <= 2.
Proof.
  unfold audit_uf_touch; destruct (audit_map_get enc key (UnionFind.ranks forest))
    as [[rank|] reads]; try (cbn; lia).
  destruct (audit_map_set enc key 0 (UnionFind.ranks forest)); cbn; lia.
Qed.

Lemma audit_uf_rank_of_count K CE (enc : K -> positive * list CE) forest key :
  length (snd (audit_uf_rank_of enc forest key)) = 1.
Proof.
  unfold audit_uf_rank_of; destruct (audit_map_get enc key (UnionFind.ranks forest)); reflexivity.
Qed.

Lemma audit_uf_link_count K CE (enc : K -> positive * list CE) child root raise forest :
  length (snd (audit_uf_link enc child root raise forest)) <= 4.
Proof.
  unfold audit_uf_link; destruct raise.
  - pose proof (audit_uf_rank_of_count K CE enc forest root) as Hrank.
    destruct (audit_uf_rank_of enc forest root) as [rank reads].
    destruct (audit_map_set enc child root (UnionFind.parents forest)).
    destruct (audit_map_set enc root (S rank) (UnionFind.ranks forest)).
    cbn [snd] in *; rewrite length_app; cbn; lia.
  - destruct (audit_map_set enc child root (UnionFind.parents forest)); cbn; lia.
Qed.

(** For any encoder and forest, the union event count is at most sixteen plus six times the
    successor of the input forest maximum rank. *)
Theorem audit_uf_union_count : audit_uf_union_count_statement.
Proof.
  intros K CE enc x y forest.
  pose proof (audit_uf_find_fuel_count K CE enc (S (UnionFind.max_rank forest)) x forest) as Hx.
  pose proof (audit_uf_find_fuel_max_rank K CE enc (S (UnionFind.max_rank forest)) x forest)
    as Hmax.
  change (length (snd (audit_uf_find enc x forest)) <= 1 + 3 * S (UnionFind.max_rank forest)) in Hx.
  change (UnionFind.max_rank (snd (fst (audit_uf_find enc x forest))) =
    UnionFind.max_rank forest) in Hmax.
  unfold audit_uf_union.
  destruct (audit_uf_find enc x forest) as [[rx first] xe].
  pose proof (audit_uf_find_fuel_count K CE enc (S (UnionFind.max_rank first)) y first) as Hy.
  change (length (snd (audit_uf_find enc y first)) <= 1 + 3 * S (UnionFind.max_rank first)) in Hy.
  destruct (audit_uf_find enc y first) as [[ry second] ye].
  destruct (enc rx) as [cx ex]; destruct (enc ry) as [cy ey].
  destruct (audit_positive_eqb cx cy) as [equal eq].
  cbv beta iota zeta delta [snd fst] in Hx, Hy, Hmax.
  destruct equal.
  - pose proof (audit_uf_touch_count K CE enc rx second) as Htouch.
    destruct (audit_uf_touch enc rx second); cbn [snd] in *.
    rewrite !length_app; cbn; lia.
  - pose proof (audit_uf_rank_of_count K CE enc second rx) as Hrx.
    pose proof (audit_uf_rank_of_count K CE enc second ry) as Hry.
    destruct (audit_uf_rank_of enc second rx) as [rankx re1].
    destruct (audit_uf_rank_of enc second ry) as [ranky re2].
    destruct (Nat.compare rankx ranky);
      match goal with
      | |- context [audit_uf_link enc ?a ?b ?r second] =>
        pose proof (audit_uf_link_count K CE enc a b r second) as Hlink;
        destruct (audit_uf_link enc a b r second)
      end;
      cbn [snd] in *; rewrite !length_app; cbn; lia.
Qed.

(** For any encoder and forest, the equivalence event count is at most five plus six times
    the successor of the input forest maximum rank. *)
Theorem audit_uf_equivb_count : audit_uf_equivb_count_statement.
Proof.
  intros K CE enc x y forest.
  pose proof (audit_uf_find_fuel_count K CE enc (S (UnionFind.max_rank forest)) x forest) as Hx.
  pose proof (audit_uf_find_fuel_max_rank K CE enc (S (UnionFind.max_rank forest)) x forest)
    as Hmax.
  change (length (snd (audit_uf_find enc x forest)) <= 1 + 3 * S (UnionFind.max_rank forest)) in Hx.
  change (UnionFind.max_rank (snd (fst (audit_uf_find enc x forest))) =
    UnionFind.max_rank forest) in Hmax.
  unfold audit_uf_equivb; destruct (audit_uf_find enc x forest) as [[rx first] xe].
  pose proof (audit_uf_find_fuel_count K CE enc (S (UnionFind.max_rank first)) y first) as Hy.
  change (length (snd (audit_uf_find enc y first)) <= 1 + 3 * S (UnionFind.max_rank first)) in Hy.
  destruct (audit_uf_find enc y first) as [[ry second] ye].
  destruct (enc rx) as [cx ex]; destruct (enc ry) as [cy ey].
  destruct (audit_positive_eqb cx cy); cbv beta iota zeta delta [snd fst] in Hx, Hy, Hmax.
  cbn [snd]; rewrite !length_app; cbn; lia.
Qed.

(** * Work and history bounds *)

Lemma audit_uf_primitive_work_app K CE work (first second : list (audit_uf_event K CE)) :
  audit_uf_primitive_work work (first ++ second) =
    audit_uf_primitive_work work first + audit_uf_primitive_work work second.
Proof.
  induction first as [|event rest IH]; cbn; try lia.
  destruct event; cbn in *; lia.
Qed.

Lemma audit_uf_source_work_app K CE work (first second : list (audit_uf_event K CE)) :
  audit_uf_source_work work (first ++ second) =
    audit_uf_source_work work first + audit_uf_source_work work second.
Proof.
  unfold audit_uf_source_work; rewrite length_app, audit_uf_primitive_work_app; lia.
Qed.

(** Fuelled find source work is at most four times its fuel-derived event-count bound plus
    the actual primitive work retained in that same find trace. *)
Theorem audit_uf_find_fuel_work_bound : audit_uf_find_fuel_work_bound_statement.
Proof.
  intros K CE enc work fuel key forest; unfold audit_uf_source_work.
  pose proof (audit_uf_find_fuel_count K CE enc fuel key forest); lia.
Qed.

(** Union source work is at most four times its maximum-rank event-count bound plus the
    actual primitive work retained in that same union trace. *)
Theorem audit_uf_union_work_bound : audit_uf_union_work_bound_statement.
Proof.
  intros K CE enc work x y forest; unfold audit_uf_source_work.
  pose proof (audit_uf_union_count K CE enc x y forest); lia.
Qed.

(** Equivalence source work is at most four times its maximum-rank event-count bound plus
    the actual primitive work retained in that same equivalence trace. *)
Theorem audit_uf_equivb_work_bound : audit_uf_equivb_work_bound_statement.
Proof.
  intros K CE enc work x y forest; unfold audit_uf_source_work.
  pose proof (audit_uf_equivb_count K CE enc x y forest); lia.
Qed.

(** Support enumeration source work is at most sixteen outer-frame units plus the actual
    primitive work of both map traversals, their union and ordered enumeration. *)
Theorem audit_uf_keys_work_bound : audit_uf_keys_work_bound_statement.
Proof.
  intros K CE work forest; unfold audit_uf_keys.
  destruct (audit_map_transform (fun _ : K => (tt, @nil unit)) (UnionFind.parents forest)).
  destruct (audit_map_transform (fun _ : nat => (tt, @nil unit)) (UnionFind.ranks forest)).
  destruct (audit_finset_union t t0); destruct (audit_finset_elements t1).
  unfold audit_uf_source_work; cbn [snd length]; lia.
Qed.

Lemma audit_transform_zero_child K V (events : list (audit_map_transform_event K V unit unit)) :
  audit_map_transform_child_work (fun _ => 0) events = 0.
Proof.
  induction events as [|event rest IH]; cbn; try reflexivity.
  destruct event; cbn in *; exact IH.
Qed.

(** Support enumeration source work is bounded by the stated input/intermediate trie-node
    counts and emitted position bits, with both fixed unit mappers discharged concretely. *)
Theorem audit_uf_keys_input_bound : audit_uf_keys_input_bound_statement.
Proof.
  intros K CE work forest; unfold audit_uf_keys.
  pose proof (audit_map_transform_source_bound K K unit unit (fun _ => (tt, []))
    (fun _ => 0) (UnionFind.parents forest)) as Hp.
  pose proof (audit_map_transform_source_bound K nat unit unit (fun _ => (tt, []))
    (fun _ => 0) (UnionFind.ranks forest)) as Hr.
  destruct (audit_map_transform (fun _ : K => (tt, @nil unit)) (UnionFind.parents forest))
    as [parents pe].
  destruct (audit_map_transform (fun _ : nat => (tt, @nil unit)) (UnionFind.ranks forest))
    as [ranks re].
  cbv beta iota zeta delta [fst snd].
  pose proof (audit_finset_union_source_bound K parents ranks) as Hu.
  destruct (audit_finset_union parents ranks) as [merged ue].
  pose proof (audit_finset_elements_work_bound K merged) as He.
  destruct (audit_finset_elements merged) as [keys oe].
  cbv beta iota zeta delta [fst snd] in *.
  rewrite audit_transform_zero_child in Hp, Hr.
  unfold audit_uf_source_work; cbn [length audit_uf_primitive_work]; lia.
Qed.

Lemma audit_uf_action_erases K CE enc (original : encoding K) action forest
    (Henc : forall k, fst (enc k) = encode original k) :
  fst (@audit_uf_action_run K CE enc action forest) =
    audit_uf_original_action original forest action.
Proof.
  destruct action as [key|x y]; cbn [audit_uf_action_run audit_uf_original_action].
  - pose proof (audit_uf_find_erases K CE enc original key forest Henc) as Hfind.
    destruct (audit_uf_find enc key forest) as [[root result] events].
    cbv beta iota zeta delta [fst snd] in *; now rewrite <- Hfind.
  - apply audit_uf_union_erases; exact Henc.
Qed.

(** When encoder codes agree with the original encoding on every key, a history returns
    exactly the fold of original actions with each returned forest threaded into the next action. *)
Theorem audit_uf_history_erases : audit_uf_history_erases_statement.
Proof.
  intros K CE enc original actions; induction actions as [|action rest IH]; intros forest Henc.
  - reflexivity.
  - cbn [audit_uf_history fold_left].
    pose proof (audit_uf_action_erases K CE enc original action forest Henc) as Haction.
    destruct (audit_uf_action_run enc action forest) as [next first].
    specialize (IH next Henc); destruct (audit_uf_history enc rest next) as [out tail].
    cbv beta iota zeta delta [fst] in *; now rewrite IH, Haction.
Qed.

(** When encoder codes agree with the original encoding on every key, the union-list adapter
    returns exactly the original union fold from the empty forest in input order. *)
Theorem audit_uf_of_unions_erases : audit_uf_of_unions_erases_statement.
Proof.
  intros K CE enc original inputs Henc; unfold audit_uf_of_unions.
  rewrite (audit_uf_history_erases K CE enc original _ _ Henc).
  unfold UnionFind.of_unions; generalize (@UnionFind.make K).
  induction inputs as [|[x y] rest IH]; intro forest; cbn; auto.
Qed.

Lemma audit_uf_action_count K CE (enc : K -> positive * list CE) action forest :
  length (snd (audit_uf_action_run enc action forest)) <=
    match action with
    | AuditUFFind _ => 1 + 3 * S (UnionFind.max_rank forest)
    | AuditUFUnion _ _ => 16 + 6 * S (UnionFind.max_rank forest)
    end.
Proof.
  destruct action as [key|x y]; cbn [audit_uf_action_run].
  - pose proof (audit_uf_find_fuel_count K CE enc (S (UnionFind.max_rank forest)) key forest)
      as Hfind.
    change (length (snd (audit_uf_find enc key forest)) <=
      1 + 3 * S (UnionFind.max_rank forest)) in Hfind.
    destruct (audit_uf_find enc key forest) as [[root result] events]; exact Hfind.
  - apply audit_uf_union_count.
Qed.

Lemma audit_uf_history_count K CE (enc : K -> positive * list CE) actions : forall forest,
  length (snd (audit_uf_history enc actions forest)) <=
    audit_uf_history_frame_budget enc actions forest.
Proof.
  induction actions as [|action rest IH]; intro forest; cbn [audit_uf_history
    audit_uf_history_frame_budget]; try (cbn; lia).
  pose proof (audit_uf_action_count K CE enc action forest) as Haction.
  destruct (audit_uf_action_run enc action forest) as [next first].
  specialize (IH next); destruct (audit_uf_history enc rest next) as [out tail].
  cbv beta iota zeta delta [fst snd] in *; cbn [length]; rewrite length_app; lia.
Qed.

(** History source work is at most four times the frame budget over its actual intermediate
    forests plus the actual primitive work retained in that same history trace. *)
Theorem audit_uf_history_bound : audit_uf_history_bound_statement.
Proof.
  intros K CE enc work actions forest; unfold audit_uf_source_work.
  pose proof (audit_uf_history_count K CE enc actions forest); lia.
Qed.

(** Union-list source work is at most four times its history frame budget from the empty
    forest plus the actual primitive work retained in that same union-list trace. *)
Theorem audit_uf_of_unions_source_bound : audit_uf_of_unions_source_bound_statement.
Proof.
  intros K CE enc work inputs; apply audit_uf_history_bound.
Qed.

(** Source work summed over independently started branches is at most four times their
    summed history frame budgets plus the actual primitive work of both retained branch traces. *)
Theorem audit_uf_branches_bound : audit_uf_branches_bound_statement.
Proof.
  intros K CE enc work left right forest.
  pose proof (audit_uf_history_bound K CE enc work left forest) as Hl.
  pose proof (audit_uf_history_bound K CE enc work right forest) as Hr.
  cbv beta iota zeta delta [audit_uf_branches fst snd] in *; lia.
Qed.
