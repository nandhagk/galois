(** * Whole union-find source-work adequacy

    Input recurrences cover concrete map accesses, numeric control and persistent histories.
    For example, the second find is bounded on the forest returned by the first find.
    Builds on: CollectionsAuditUnionFindWhole and primitive, map and encoder adequacy. *)

From Stdlib Require Import List PArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsUnionFind
  CollectionsAuditMap CollectionsAuditPrimitive CollectionsAuditUnionFind
  CollectionsAuditUnionFindAdapters CollectionsAuditUnionFindWhole CollectionsAuditEncoderBudget
  CollectionsAuditMapAdequacy CollectionsAuditPrimitiveAdequacy
  CollectionsAuditEncoderBudgetAdequacy
  CollectionsAuditUnionFindAdequacy.
Import List.ListNotations.

(** * Concrete access budgets *)

Lemma audit_uf_read_input_bound K V CE (enc : K -> positive * list CE) work budget key
    (input : Map.t K V) (Hbudget : forall key, work (snd (enc key)) <= budget key) :
  4 + audit_map_source_work work (snd (audit_map_get enc key input)) <=
    audit_uf_read_budget enc budget key.
Proof.
  pose proof (audit_map_get_source_work_bound K V CE enc work key input) as Hread.
  specialize (Hbudget key); unfold audit_uf_read_budget; lia.
Qed.

Lemma audit_uf_write_input_bound K V CE (enc : K -> positive * list CE) work budget key value
    (input : Map.t K V) (Hbudget : forall key, work (snd (enc key)) <= budget key) :
  4 + audit_map_source_work work (snd (audit_map_set enc key value input)) <=
    audit_uf_write_budget enc budget key.
Proof.
  pose proof (audit_map_set_source_work_bound K V CE enc work key value input) as Hwrite.
  specialize (Hbudget key); unfold audit_uf_write_budget; lia.
Qed.

Lemma audit_uf_find_whole_bound K CE (enc : K -> positive * list CE) work budget
    (Hbudget : forall key, work (snd (enc key)) <= budget key) fuel : forall key forest,
  audit_uf_source_work work (snd (audit_uf_find_fuel enc fuel key forest)) <=
    audit_uf_find_input_budget enc budget fuel key forest.
Proof.
  induction fuel as [|fuel IH]; intros key forest.
  - reflexivity.
  - cbn [audit_uf_find_fuel audit_uf_find_input_budget].
    pose proof (audit_uf_read_input_bound K K CE enc work budget key
      (UnionFind.parents forest) Hbudget) as Hread.
    destruct (audit_map_get enc key (UnionFind.parents forest)) as [[next|] reads].
    + specialize (IH next forest).
      destruct (audit_uf_find_fuel enc fuel next forest) as [[root compressed] child].
      pose proof (audit_uf_write_input_bound K K CE enc work budget key root
        (UnionFind.parents compressed) Hbudget) as Hwrite.
      destruct (audit_map_set enc key root (UnionFind.parents compressed)) as [parents writes].
      cbv beta iota zeta delta [fst snd] in *.
      rewrite !audit_uf_source_work_app.
      unfold audit_uf_source_work at 1 3; cbn [length audit_uf_primitive_work].
      lia.
    + cbv beta iota zeta delta [fst snd] in *.
      unfold audit_uf_source_work; cbn [length audit_uf_primitive_work]; lia.
Qed.

Lemma audit_uf_rank_whole_bound K CE (enc : K -> positive * list CE) work budget forest key
    (Hbudget : forall key, work (snd (enc key)) <= budget key) :
  audit_uf_source_work work (snd (audit_uf_rank_of enc forest key)) <=
    audit_uf_read_budget enc budget key.
Proof.
  pose proof (audit_uf_read_input_bound K nat CE enc work budget key
    (UnionFind.ranks forest) Hbudget) as Hread.
  unfold audit_uf_rank_of.
  destruct (audit_map_get enc key (UnionFind.ranks forest)) as [found reads].
  unfold audit_uf_source_work; cbn [snd length audit_uf_primitive_work] in *; lia.
Qed.

Lemma audit_uf_touch_whole_bound K CE (enc : K -> positive * list CE) work budget key forest
    (Hbudget : forall key, work (snd (enc key)) <= budget key) :
  audit_uf_source_work work (snd (audit_uf_touch enc key forest)) <=
    audit_uf_touch_input_budget enc budget key forest.
Proof.
  pose proof (audit_uf_read_input_bound K nat CE enc work budget key
    (UnionFind.ranks forest) Hbudget) as Hread.
  unfold audit_uf_touch, audit_uf_touch_input_budget.
  destruct (audit_map_get enc key (UnionFind.ranks forest)) as [[rank|] reads].
  - unfold audit_uf_source_work; cbn [fst snd length audit_uf_primitive_work] in *; lia.
  - pose proof (audit_uf_write_input_bound K nat CE enc work budget key 0
      (UnionFind.ranks forest) Hbudget) as Hwrite.
    destruct (audit_map_set enc key 0 (UnionFind.ranks forest)) as [ranks writes].
    unfold audit_uf_source_work; cbn [fst snd length audit_uf_primitive_work] in *; lia.
Qed.

Lemma audit_uf_link_whole_bound K CE (enc : K -> positive * list CE) work budget
    child root raise forest (Hbudget : forall key, work (snd (enc key)) <= budget key) :
  audit_uf_source_work work (snd (audit_uf_link enc child root raise forest)) <=
    audit_uf_link_input_budget enc budget child root raise forest.
Proof.
  unfold audit_uf_link, audit_uf_link_input_budget; destruct raise.
  - pose proof (audit_uf_rank_whole_bound K CE enc work budget forest root Hbudget) as Hrank.
    destruct (audit_uf_rank_of enc forest root) as [rank reads].
    pose proof (audit_uf_write_input_bound K K CE enc work budget child root
      (UnionFind.parents forest) Hbudget) as Hp.
    pose proof (audit_uf_write_input_bound K nat CE enc work budget root (S rank)
      (UnionFind.ranks forest) Hbudget) as Hr.
    destruct (audit_map_set enc child root (UnionFind.parents forest)) as [parents pe].
    destruct (audit_map_set enc root (S rank) (UnionFind.ranks forest)) as [ranks re].
    cbv beta iota zeta delta [fst snd] in *.
    rewrite audit_uf_source_work_app.
    unfold audit_uf_source_work at 2; cbn [length audit_uf_primitive_work
      audit_uf_unary_compare_work]; unfold audit_uf_unary_compare_work; lia.
  - pose proof (audit_uf_write_input_bound K K CE enc work budget child root
      (UnionFind.parents forest) Hbudget) as Hp.
    destruct (audit_map_set enc child root (UnionFind.parents forest)) as [parents pe].
    unfold audit_uf_source_work; cbn [snd length audit_uf_primitive_work] in *; lia.
Qed.

(** * Composing actual calls *)

Lemma audit_uf_union_whole_bound K CE (enc : K -> positive * list CE) work budget x y forest
    (Hbudget : forall key, work (snd (enc key)) <= budget key) :
  audit_uf_source_work work (snd (audit_uf_union enc x y forest)) <=
    audit_uf_union_input_budget enc budget x y forest.
Proof.
  unfold audit_uf_union, audit_uf_union_input_budget.
  pose proof (audit_uf_find_whole_bound K CE enc work budget Hbudget
    (S (UnionFind.max_rank forest)) x forest) as Hx.
  change (audit_uf_source_work work (snd (audit_uf_find enc x forest)) <=
    audit_uf_find_input_budget enc budget (S (UnionFind.max_rank forest)) x forest) in Hx.
  destruct (audit_uf_find enc x forest) as [[rx first] xe].
  cbv beta iota zeta delta [fst snd].
  pose proof (audit_uf_find_whole_bound K CE enc work budget Hbudget
    (S (UnionFind.max_rank first)) y first) as Hy.
  change (audit_uf_source_work work (snd (audit_uf_find enc y first)) <=
    audit_uf_find_input_budget enc budget (S (UnionFind.max_rank first)) y first) in Hy.
  destruct (audit_uf_find enc y first) as [[ry second] ye].
  cbv beta iota zeta delta [fst snd].
  pose proof (Hbudget rx) as Hrx; pose proof (Hbudget ry) as Hry.
  destruct (enc rx) as [cx ex]; destruct (enc ry) as [cy ey].
  cbv beta iota zeta delta [fst snd].
  pose proof (audit_positive_eqb_source_bound cx cy) as Heq.
  destruct (audit_positive_eqb cx cy) as [equal eq].
  cbv beta iota zeta delta [fst snd] in *.
  destruct equal.
  - pose proof (audit_uf_touch_whole_bound K CE enc work budget rx second Hbudget) as Htouch.
    destruct (audit_uf_touch enc rx second) as [out events].
    cbv beta iota zeta delta [snd] in *; rewrite !audit_uf_source_work_app.
    unfold audit_uf_source_work at 3; cbn [length audit_uf_primitive_work]; lia.
  - pose proof (audit_uf_rank_whole_bound K CE enc work budget second rx Hbudget) as Hrankx.
    pose proof (audit_uf_rank_whole_bound K CE enc work budget second ry Hbudget) as Hranky.
    destruct (audit_uf_rank_of enc second rx) as [rankx re1].
    destruct (audit_uf_rank_of enc second ry) as [ranky re2].
    cbv beta iota zeta delta [fst snd].
    destruct (Nat.compare rankx ranky);
      match goal with
      | |- context [audit_uf_link enc ?a ?b ?r second] =>
        pose proof (audit_uf_link_whole_bound K CE enc work budget a b r second Hbudget)
          as Hlink;
        destruct (audit_uf_link enc a b r second) as [out events]
      end;
      cbv beta iota zeta delta [snd] in *; rewrite !audit_uf_source_work_app;
      unfold audit_uf_source_work at 3 6;
      cbn [length audit_uf_primitive_work audit_uf_unary_compare_work];
      unfold audit_uf_unary_compare_work; lia.
Qed.

Lemma audit_uf_equivb_whole_bound K CE (enc : K -> positive * list CE) work budget x y forest
    (Hbudget : forall key, work (snd (enc key)) <= budget key) :
  audit_uf_source_work work (snd (audit_uf_equivb enc x y forest)) <=
    audit_uf_equivb_input_budget enc budget x y forest.
Proof.
  unfold audit_uf_equivb, audit_uf_equivb_input_budget.
  pose proof (audit_uf_find_whole_bound K CE enc work budget Hbudget
    (S (UnionFind.max_rank forest)) x forest) as Hx.
  change (audit_uf_source_work work (snd (audit_uf_find enc x forest)) <=
    audit_uf_find_input_budget enc budget (S (UnionFind.max_rank forest)) x forest) in Hx.
  destruct (audit_uf_find enc x forest) as [[rx first] xe].
  cbv beta iota zeta delta [fst snd].
  pose proof (audit_uf_find_whole_bound K CE enc work budget Hbudget
    (S (UnionFind.max_rank first)) y first) as Hy.
  change (audit_uf_source_work work (snd (audit_uf_find enc y first)) <=
    audit_uf_find_input_budget enc budget (S (UnionFind.max_rank first)) y first) in Hy.
  destruct (audit_uf_find enc y first) as [[ry second] ye].
  cbv beta iota zeta delta [fst snd].
  pose proof (Hbudget rx) as Hrx; pose proof (Hbudget ry) as Hry.
  destruct (enc rx) as [cx ex]; destruct (enc ry) as [cy ey].
  cbv beta iota zeta delta [fst snd].
  pose proof (audit_positive_eqb_source_bound cx cy) as Heq.
  destruct (audit_positive_eqb cx cy) as [equal eq].
  cbv beta iota zeta delta [fst snd] in *; rewrite !audit_uf_source_work_app.
  unfold audit_uf_source_work at 3; cbn [length audit_uf_primitive_work]; lia.
Qed.

Lemma audit_uf_history_whole_bound K CE (enc : K -> positive * list CE) work budget actions
    (Hbudget : forall key, work (snd (enc key)) <= budget key) : forall forest,
  audit_uf_source_work work (snd (audit_uf_history enc actions forest)) <=
    audit_uf_history_input_budget enc budget actions forest.
Proof.
  induction actions as [|action rest IH]; intro forest.
  - reflexivity.
  - assert (Haction : audit_uf_source_work work (snd (audit_uf_action_run enc action forest)) <=
        audit_uf_action_input_budget enc budget action forest).
    { destruct action as [key|x y]; cbn [audit_uf_action_run audit_uf_action_input_budget].
      - pose proof (audit_uf_find_whole_bound K CE enc work budget Hbudget
          (S (UnionFind.max_rank forest)) key forest) as Hfind.
        change (audit_uf_source_work work (snd (audit_uf_find enc key forest)) <=
          audit_uf_find_input_budget enc budget (S (UnionFind.max_rank forest)) key forest)
          in Hfind.
        destruct (audit_uf_find enc key forest) as [[root result] events]; exact Hfind.
      - apply audit_uf_union_whole_bound; exact Hbudget. }
    cbn [audit_uf_history audit_uf_history_input_budget].
    destruct (audit_uf_action_run enc action forest) as [next first].
    specialize (IH next); destruct (audit_uf_history enc rest next) as [out tail].
    cbv beta iota zeta delta [fst snd] in *.
    change (audit_uf_source_work work ([AuditUFHistoryCase (S (length rest))] ++ first ++ tail)
      <= 4 + audit_uf_action_input_budget enc budget action forest +
        audit_uf_history_input_budget enc budget rest next).
    rewrite !audit_uf_source_work_app.
    unfold audit_uf_source_work at 1; cbn [length audit_uf_primitive_work]; lia.
Qed.

(** Assuming the actual encoder body work is bounded by its budget at every key, find,
    union, equivalence and history source work are bounded by their respective input recurrences. *)
Theorem audit_uf_whole_input_bound : audit_uf_whole_input_bound_statement.
Proof.
  intros K CE enc work budget Hbudget.
  split; [apply audit_uf_find_whole_bound; exact Hbudget |].
  split; [intros; apply audit_uf_union_whole_bound; exact Hbudget |].
  split; [intros; apply audit_uf_equivb_whole_bound; exact Hbudget |].
  intros; apply audit_uf_history_whole_bound; exact Hbudget.
Qed.

(** Assuming each actual component encoder body is bounded by its per-component budget,
    pair-key union source work is bounded by the history input recurrence with the fixed pair
    budget. *)
Theorem audit_uf_pair_whole_input_bound : audit_uf_pair_whole_input_bound_statement.
Proof.
  intros A B EA EB first second fw sw fb sb inputs Hfirst Hsecond.
  apply audit_uf_history_whole_bound; intro key.
  apply audit_pair_input_bound; assumption.
Qed.

(** Assuming each actual element encoder body is bounded by its per-element budget,
    list-key union source work is bounded by the history input recurrence charging every
    occurrence. *)
Theorem audit_uf_list_whole_input_bound : audit_uf_list_whole_input_bound_statement.
Proof.
  intros A CE element work budget inputs Hbudget.
  apply audit_uf_history_whole_bound; intro key.
  apply audit_list_input_bound; exact Hbudget.
Qed.

(** Assuming actual encoder body work is bounded at every key, summed source work of
    independently started branches is bounded by the sum of their history input recurrences. *)
Theorem audit_uf_branches_whole_input_bound : audit_uf_branches_whole_input_bound_statement.
Proof.
  intros K CE enc work budget left right forest Hbudget.
  pose proof (audit_uf_history_whole_bound K CE enc work budget left Hbudget forest) as Hl.
  pose proof (audit_uf_history_whole_bound K CE enc work budget right Hbudget forest) as Hr.
  cbv beta iota zeta delta [audit_uf_branches fst snd] in *; lia.
Qed.
