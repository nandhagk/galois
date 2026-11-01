(** * Historical union-find trace adequacy

    Selected-event traces retain the original persistent forest results and additive counters.
    For example, two histories from one forest contribute separate key-bit totals.
    Builds on: CollectionsAuditHistorical and CollectionsUnionFind. *)

From Stdlib Require Import List Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsUnionFind
  CollectionsAuditHistorical.
Import List.ListNotations.

(** * Result preservation *)

Lemma trace_find_fuel_result K (E : encoding K) fuel : forall x uf,
  fst (trace_find_fuel E fuel x uf) = UnionFind.find_fuel E fuel x uf.
Proof.
  induction fuel as [|fuel IH]; intros x uf; cbn [trace_find_fuel UnionFind.find_fuel].
  - reflexivity.
  - destruct (Map.get E x (UnionFind.parents uf)) as [next|]; try reflexivity.
    specialize (IH next uf).
    destruct (trace_find_fuel E fuel next uf) as [[root compressed] events].
    cbn in IH; rewrite <- IH; reflexivity.
Qed.

(** Discarding the historical find trace yields exactly the original representative and
    compressed forest for the supplied key and forest. *)
Theorem trace_find_result : trace_find_result_statement.
Proof.
  intros K E x uf; apply trace_find_fuel_result.
Qed.

(** Discarding the historical union trace yields exactly the forest produced by the original
    union in whichever equality and rank branches are selected. *)
Theorem trace_union_result : trace_union_result_statement.
Proof.
  intros K E x y uf.
  unfold trace_union, UnionFind.union.
  pose proof (trace_find_result K E x uf) as Hfirst.
  destruct (trace_find E x uf) as [[rx first] xe]; cbv beta iota zeta delta [fst] in Hfirst.
  rewrite <- Hfirst.
  pose proof (trace_find_result K E y first) as Hsecond.
  destruct (trace_find E y first) as [[ry second] ye]; cbv beta iota zeta delta [fst] in Hsecond.
  rewrite <- Hsecond.
  destruct (UnionFind.key_eqb E rx ry).
  - unfold UnionFind.touch; destruct (Map.get E rx (UnionFind.ranks second)); reflexivity.
  - destruct (Nat.compare (UnionFind.rank_of E second rx)
      (UnionFind.rank_of E second ry)); reflexivity.
Qed.

Lemma trace_action_result K (E : encoding K) action uf :
  fst (trace_action E action uf) = action_step E action uf.
Proof.
  destruct action as [key|x y]; cbn [trace_action action_step].
  - pose proof (trace_find_result K E key uf) as Hfind.
    destruct (trace_find E key uf) as [[root result] events]; cbn in *.
    now rewrite <- Hfind.
  - apply trace_union_result.
Qed.

(** Discarding a historical action trace yields exactly the fold of original actions,
    threading each returned persistent forest into the next action. *)
Theorem trace_actions_result : trace_actions_result_statement.
Proof.
  intros K E actions; induction actions as [|action rest IH]; intro uf; cbn [trace_actions].
  - reflexivity.
  - pose proof (trace_action_result K E action uf) as Haction.
    destruct (trace_action E action uf) as [next first]; cbn in Haction.
    specialize (IH next); destruct (trace_actions E rest next) as [last tail].
    cbn in *; rewrite IH, Haction; reflexivity.
Qed.

(** * Additive selected-event observations *)

Lemma event_key_bits_app K (E : encoding K) first second :
  event_key_bits E (first ++ second) = event_key_bits E first + event_key_bits E second.
Proof.
  induction first as [|event rest IH].
  - reflexivity.
  - destruct event; simpl in *; lia.
Qed.

Lemma event_unary_total_app K (first second : list (union_event K)) :
  event_unary_total (first ++ second) = event_unary_total first + event_unary_total second.
Proof.
  induction first as [|event rest IH]; simpl; lia.
Qed.

(** Key-bit and unary-work totals of concatenated independently started branch traces equal
    the sums of the corresponding totals of their two retained traces. *)
Theorem trace_branch_sum : trace_branch_sum_statement.
Proof.
  intros K E uf left right; unfold trace_branches.
  split; [apply event_key_bits_app | apply event_unary_total_app].
Qed.

Lemma union_trace_bits K (E : encoding K) events :
  union_trie_read_bits E events + union_trie_write_bits E events +
    union_key_compare_bits E events = event_key_bits E events.
Proof.
  induction events as [|event rest IH].
  - reflexivity.
  - destruct event; cbn [union_trie_read_bits union_trie_write_bits union_key_compare_bits
    event_key_bits event_keys] in *; simpl in *; lia.
Qed.

(** The historical work record retains the original action-fold result, partitions key bits
    into read/write/comparison totals, and records exactly the input-action and output-event
    counts. *)
Theorem union_source_work : union_source_work_statement.
Proof.
  intros K E actions uf costs.
  pose proof (trace_actions_result K E actions uf) as Hresult.
  destruct (trace_actions E actions uf) as [result events]; cbn in Hresult.
  cbn [union_trace_work]; split; [exact Hresult |].
  split; [apply union_trace_bits | split; reflexivity].
Qed.
