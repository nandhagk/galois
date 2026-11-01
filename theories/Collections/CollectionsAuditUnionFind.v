(** * Counted persistent union-find

    This observer follows actual parent compression, rank accesses and persistent updates.
    For example, two sibling histories start from the same forest and are charged separately.
    Builds on: CollectionsUnionFind and shared map, encoding and positive-equality models. *)

From Stdlib Require Import List PArith PeanoNat.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsUnionFind
  CollectionsAuditPrimitive CollectionsAuditMap
  CollectionsAuditMapTraverse CollectionsAuditUnion CollectionsAuditElements.
Import List.ListNotations.

(** * Actual forest operation events *)

Inductive audit_uf_event (K CE : Type) : Type :=
  | AuditUFFindCase (fuel : nat) (key : K) (forest : UnionFind.t K)
  | AuditUFParentRead (key : K) (result : option K) (calls : list (audit_map_event K K CE))
  | AuditUFParentWrite (key root : K) (calls : list (audit_map_event K K CE))
  | AuditUFRankRead (key : K) (result : option nat) (calls : list (audit_map_event K nat CE))
  | AuditUFRankWrite (key : K) (rank : nat) (calls : list (audit_map_event K nat CE))
  | AuditUFEncode (key : K) (code : positive) (events : list CE)
  | AuditUFEqual (left right : positive) (result : bool) (events : list audit_positive_eqb_event)
  | AuditUFRankCompare (left right : nat) (result : comparison)
  | AuditUFRankMax (left right result : nat)
  | AuditUFKeysParents (calls : list (audit_map_transform_event K K unit unit))
  | AuditUFKeysRanks (calls : list (audit_map_transform_event K nat unit unit))
  | AuditUFKeysUnion (calls : list (audit_union_event K))
  | AuditUFKeysElements (calls : list (audit_set_elements_event K))
  | AuditUFHistoryCase (remaining : nat).

Arguments AuditUFFindCase {K CE} _ _ _.
Arguments AuditUFParentRead {K CE} _ _ _.
Arguments AuditUFParentWrite {K CE} _ _ _.
Arguments AuditUFRankRead {K CE} _ _ _.
Arguments AuditUFRankWrite {K CE} _ _ _.
Arguments AuditUFEncode {K CE} _ _ _.
Arguments AuditUFEqual {K CE} _ _ _ _.
Arguments AuditUFRankCompare {K CE} _ _ _.
Arguments AuditUFRankMax {K CE} _ _ _.
Arguments AuditUFKeysParents {K CE} _.
Arguments AuditUFKeysRanks {K CE} _.
Arguments AuditUFKeysUnion {K CE} _.
Arguments AuditUFKeysElements {K CE} _.
Arguments AuditUFHistoryCase {K CE} _.

(** The recursive parent lookup uses the original forest; writes use the returned compressed one. *)
Fixpoint audit_uf_find_fuel {K CE} (enc : K -> positive * list CE) (fuel : nat)
    (key : K) (forest : UnionFind.t K) : (K * UnionFind.t K) * list (audit_uf_event K CE) :=
  match fuel with
  | 0 => ((key, forest), [AuditUFFindCase fuel key forest])
  | S rest =>
      let '(parent, reads) := audit_map_get enc key (UnionFind.parents forest) in
      match parent with
      | None => ((key, forest), [AuditUFFindCase fuel key forest; AuditUFParentRead key parent
        reads])
      | Some next =>
          let '((root, compressed), child) := audit_uf_find_fuel enc rest next forest in
          let '(parents, writes) := audit_map_set enc key root (UnionFind.parents compressed) in
          let output := UnionFind.Forest parents (UnionFind.ranks compressed)
            (UnionFind.max_rank compressed) in
          ((root, output), [AuditUFFindCase fuel key forest; AuditUFParentRead key parent reads] ++
            child ++ [AuditUFParentWrite key root writes])
      end
  end.

Definition audit_uf_find {K CE} (enc : K -> positive * list CE) (key : K) (forest : UnionFind.t K)
    : (K * UnionFind.t K) * list (audit_uf_event K CE) :=
  audit_uf_find_fuel enc (S (UnionFind.max_rank forest)) key forest.

(** Rank lookup retains the actual optional binding and its default-zero branch. *)
Definition audit_uf_rank_of {K CE} (enc : K -> positive * list CE) (forest : UnionFind.t K)
  (key : K)
    : nat * list (audit_uf_event K CE) :=
  let '(found, calls) := audit_map_get enc key (UnionFind.ranks forest) in
  (match found with
  | Some n => n
  | None => 0
  end, [AuditUFRankRead key found calls]).

(** Touch executes the rank write only when the original read is absent. *)
Definition audit_uf_touch {K CE} (enc : K -> positive * list CE) (key : K) (forest : UnionFind.t K)
    : UnionFind.t K * list (audit_uf_event K CE) :=
  let '(found, reads) := audit_map_get enc key (UnionFind.ranks forest) in
  match found with
  | Some _ => (forest, [AuditUFRankRead key found reads])
  | None =>
      let '(ranks, writes) := audit_map_set enc key 0 (UnionFind.ranks forest) in
      (UnionFind.Forest (UnionFind.parents forest) ranks (UnionFind.max_rank forest),
        [AuditUFRankRead key found reads; AuditUFRankWrite key 0 writes])
  end.

(** A link preserves every strict operand of the rank-raising record construction. *)
Definition audit_uf_link {K CE} (enc : K -> positive * list CE)
    (child root : K) (raise : bool) (forest : UnionFind.t K)
    : UnionFind.t K * list (audit_uf_event K CE) :=
  if raise then
    let '(old_rank, rank_reads) := audit_uf_rank_of enc forest root in
    let new_rank := S old_rank in
    let '(parents, parent_writes) := audit_map_set enc child root (UnionFind.parents forest) in
    let '(ranks, rank_writes) := audit_map_set enc root new_rank (UnionFind.ranks forest) in
    let maximum := Nat.max (UnionFind.max_rank forest) new_rank in
    (UnionFind.Forest parents ranks maximum, rank_reads ++
      [AuditUFParentWrite child root parent_writes; AuditUFRankWrite root new_rank rank_writes;
       AuditUFRankMax (UnionFind.max_rank forest) new_rank maximum])
  else
    let '(parents, writes) := audit_map_set enc child root (UnionFind.parents forest) in
    (UnionFind.Forest parents (UnionFind.ranks forest) (UnionFind.max_rank forest),
      [AuditUFParentWrite child root writes]).

(** Union threads both finds and records the actual equality, rank and link branches. *)
Definition audit_uf_union {K CE} (enc : K -> positive * list CE) (x y : K)
    (forest : UnionFind.t K) : UnionFind.t K * list (audit_uf_event K CE) :=
  let '((rx, first), xe) := audit_uf_find enc x forest in
  let '((ry, second), ye) := audit_uf_find enc y first in
  let '(cx, xenc) := enc rx in
  let '(cy, yenc) := enc ry in
  let '(equal, eq) := audit_positive_eqb cx cy in
  let prefix := xe ++ ye ++ [AuditUFEncode rx cx xenc; AuditUFEncode ry cy yenc;
                             AuditUFEqual cx cy equal eq] in
  if equal then
    let '(out, events) := audit_uf_touch enc rx second in (out, prefix ++ events)
  else
    let '(rankx, re1) := audit_uf_rank_of enc second rx in
    let '(ranky, re2) := audit_uf_rank_of enc second ry in
    let compared := Nat.compare rankx ranky in
    let '(out, events) := match compared with
      | Lt => audit_uf_link enc rx ry false second
      | Gt => audit_uf_link enc ry rx false second
      | Eq => audit_uf_link enc ry rx true second
      end in
    (out, prefix ++ re1 ++ re2 ++ [AuditUFRankCompare rankx ranky compared] ++ events).

(** Equivalence testing retains both compressed states and the actual encoded-key comparison. *)
Definition audit_uf_equivb {K CE} (enc : K -> positive * list CE) (x y : K)
    (forest : UnionFind.t K) : (bool * UnionFind.t K) * list (audit_uf_event K CE) :=
  let '((rx, first), xe) := audit_uf_find enc x forest in
  let '((ry, second), ye) := audit_uf_find enc y first in
  let '(cx, xenc) := enc rx in
  let '(cy, yenc) := enc ry in
  let '(equal, eq) := audit_positive_eqb cx cy in
  ((equal, second), xe ++ ye ++ [AuditUFEncode rx cx xenc; AuditUFEncode ry cy yenc;
                                 AuditUFEqual cx cy equal eq]).

(** Support enumeration retains both actual map traversals, union and output traversal. *)
Definition audit_uf_keys {K CE} (forest : UnionFind.t K)
    : list K * list (audit_uf_event K CE) :=
  let '(parents, pe) := audit_map_transform (fun _ : K => (tt, @nil unit))
    (UnionFind.parents forest) in
  let '(ranks, re) := audit_map_transform (fun _ : nat => (tt, @nil unit))
    (UnionFind.ranks forest) in
  let '(merged, ue) := audit_finset_union parents ranks in
  let '(output, oe) := audit_finset_elements merged in
  (output, [AuditUFKeysParents pe; AuditUFKeysRanks re; AuditUFKeysUnion ue;
    AuditUFKeysElements oe]).

(** * Exact future result obligations *)

Definition audit_uf_find_fuel_erases_statement : Prop :=
  forall K CE (enc : K -> positive * list CE) (original : encoding K) fuel key forest,
    (forall k, fst (enc k) = encode original k) ->
    fst (audit_uf_find_fuel enc fuel key forest) = UnionFind.find_fuel original fuel key forest.

(** Discarding the uf find events recovers the corresponding original operation under its
  premises. *)
Definition audit_uf_find_erases_statement : Prop :=
  forall K CE (enc : K -> positive * list CE) (original : encoding K) key forest,
    (forall k, fst (enc k) = encode original k) ->
    fst (audit_uf_find enc key forest) = UnionFind.find original key forest.

(** Discarding the uf union events recovers the corresponding original operation under its
  premises. *)
Definition audit_uf_union_erases_statement : Prop :=
  forall K CE (enc : K -> positive * list CE) (original : encoding K) x y forest,
    (forall k, fst (enc k) = encode original k) ->
    fst (audit_uf_union enc x y forest) = UnionFind.union original x y forest.

(** Discarding the uf equivb events recovers the corresponding original operation under its
  premises. *)
Definition audit_uf_equivb_erases_statement : Prop :=
  forall K CE (enc : K -> positive * list CE) (original : encoding K) x y forest,
    (forall k, fst (enc k) = encode original k) ->
    fst (audit_uf_equivb enc x y forest) = UnionFind.equivb original x y forest.

(** Discarding the uf keys events recovers the corresponding original operation under its
  premises. *)
Definition audit_uf_keys_erases_statement : Prop :=
  forall K CE (original : encoding K) (forest : UnionFind.t K),
    fst (@audit_uf_keys K CE forest) = UnionFind.keys original forest.

(** * Fixed source-block work and input-derived bounds *)

(** Unary rank operations charge their actual constructor traversals. *)
Definition audit_uf_unary_compare_work (left right : nat) : nat := 3 * S (Nat.min left right).

Fixpoint audit_uf_primitive_work {K CE} (enc_work : list CE -> nat)
    (events : list (audit_uf_event K CE)) : nat :=
  match events with
  | [] => 0
  | AuditUFParentRead _ _ calls :: rest => audit_map_source_work enc_work calls +
      audit_uf_primitive_work enc_work rest
  | AuditUFParentWrite _ _ calls :: rest => audit_map_source_work enc_work calls +
      audit_uf_primitive_work enc_work rest
  | AuditUFRankRead _ _ calls :: rest => audit_map_source_work enc_work calls +
      audit_uf_primitive_work enc_work rest
  | AuditUFRankWrite _ _ calls :: rest => audit_map_source_work enc_work calls +
      audit_uf_primitive_work enc_work rest
  | AuditUFEncode _ _ calls :: rest => enc_work calls + audit_uf_primitive_work enc_work rest
  | AuditUFEqual _ _ _ calls :: rest => audit_positive_eqb_source_work calls +
      audit_uf_primitive_work enc_work rest
  | AuditUFRankCompare x y _ :: rest => audit_uf_unary_compare_work x y +
      audit_uf_primitive_work enc_work rest
  | AuditUFRankMax x y _ :: rest => audit_uf_unary_compare_work x y +
      audit_uf_primitive_work enc_work rest
  | AuditUFKeysParents calls :: rest => audit_map_transform_source_work (fun _ => 0) calls +
      audit_uf_primitive_work enc_work rest
  | AuditUFKeysRanks calls :: rest => audit_map_transform_source_work (fun _ => 0) calls +
      audit_uf_primitive_work enc_work rest
  | AuditUFKeysUnion calls :: rest => audit_finset_union_source_work calls +
      audit_uf_primitive_work enc_work rest
  | AuditUFKeysElements calls :: rest => audit_set_elements_work calls +
      audit_uf_primitive_work enc_work rest
  | _ :: rest => audit_uf_primitive_work enc_work rest
  end.

Definition audit_uf_source_work {K CE} (enc_work : list CE -> nat)
    (events : list (audit_uf_event K CE)) : nat :=
  4 * length events + audit_uf_primitive_work enc_work events.

(** The bounds count the real fuel or max-rank input, not an arbitrary output cost. *)
Definition audit_uf_find_fuel_count_statement : Prop :=
  forall K CE (enc : K -> positive * list CE) fuel key forest,
    length (snd (audit_uf_find_fuel enc fuel key forest)) <= 1 + 3 * fuel.

(** Union event count is bounded by the forest maximum rank. *)
Definition audit_uf_union_count_statement : Prop :=
  forall K CE (enc : K -> positive * list CE) x y forest,
    length (snd (audit_uf_union enc x y forest)) <= 16 + 6 * S (UnionFind.max_rank forest).

(** Equivalence-test event count is bounded by the forest maximum rank. *)
Definition audit_uf_equivb_count_statement : Prop :=
  forall K CE (enc : K -> positive * list CE) x y forest,
    length (snd (audit_uf_equivb enc x y forest)) <= 5 + 6 * S (UnionFind.max_rank forest).

(** Fuelled find work is bounded by its fuel frames and actual primitive work. *)
Definition audit_uf_find_fuel_work_bound_statement : Prop :=
  forall K CE (enc : K -> positive * list CE) enc_work fuel key forest,
    let events := snd (audit_uf_find_fuel enc fuel key forest) in
    audit_uf_source_work enc_work events <=
      4 * (1 + 3 * fuel) + audit_uf_primitive_work enc_work events.

(** Union work is bounded by maximum-rank frames and actual primitive work. *)
Definition audit_uf_union_work_bound_statement : Prop :=
  forall K CE (enc : K -> positive * list CE) enc_work x y forest,
    let events := snd (audit_uf_union enc x y forest) in
    audit_uf_source_work enc_work events <=
      4 * (16 + 6 * S (UnionFind.max_rank forest)) + audit_uf_primitive_work enc_work events.

(** Equivalence work is bounded by maximum-rank frames and actual primitive work. *)
Definition audit_uf_equivb_work_bound_statement : Prop :=
  forall K CE (enc : K -> positive * list CE) enc_work x y forest,
    let events := snd (audit_uf_equivb enc x y forest) in
    audit_uf_source_work enc_work events <=
      4 * (5 + 6 * S (UnionFind.max_rank forest)) + audit_uf_primitive_work enc_work events.

(** The fixed parent/rank mapper returns [tt] without a client callback body. *)
Definition audit_uf_keys_work_bound_statement : Prop :=
  forall K CE enc_work (forest : UnionFind.t K),
    let events := snd (@audit_uf_keys K CE forest) in
    audit_uf_source_work enc_work events <= 16 + audit_uf_primitive_work enc_work events.

(** The support bound includes both input trees, actual union and all emitted position bits. *)
Definition audit_uf_keys_input_bound_statement : Prop :=
  forall K CE enc_work (forest : UnionFind.t K),
    let parents := fst (audit_map_transform (fun _ : K => (tt, @nil unit))
      (UnionFind.parents forest)) in
    let ranks := fst (audit_map_transform (fun _ : nat => (tt, @nil unit))
      (UnionFind.ranks forest)) in
    let merged := fst (audit_finset_union parents ranks) in
    audit_uf_source_work enc_work (snd (@audit_uf_keys K CE forest)) <=
      23 + 18 * (audit_trie_nodes (UnionFind.parents forest) + audit_trie_nodes
        (UnionFind.ranks forest)) +
      15 * audit_trie_nodes parents + 19 * audit_trie_nodes merged + audit_trie_output_bits merged.

(** * Linear and branching histories *)

Inductive audit_uf_action (K : Type) : Type :=
  | AuditUFFind (key : K)
  | AuditUFUnion (left right : K).

Arguments AuditUFFind {K} _.
Arguments AuditUFUnion {K} _ _.

Definition audit_uf_action_run {K CE} (enc : K -> positive * list CE)
    (action : audit_uf_action K) (forest : UnionFind.t K)
    : UnionFind.t K * list (audit_uf_event K CE) :=
  match action with
  | AuditUFFind key =>
      let '((_, result), events) := audit_uf_find enc key forest in (result, events)
  | AuditUFUnion x y => audit_uf_union enc x y forest
  end.

(** This reference action is the corresponding original library call. *)
Definition audit_uf_original_action {K} (enc : encoding K) (forest : UnionFind.t K)
    (action : audit_uf_action K) : UnionFind.t K :=
  match action with
  | AuditUFFind key => snd (UnionFind.find enc key forest)
  | AuditUFUnion x y => UnionFind.union enc x y forest
  end.

Fixpoint audit_uf_history {K CE} (enc : K -> positive * list CE)
    (actions : list (audit_uf_action K)) (forest : UnionFind.t K)
    : UnionFind.t K * list (audit_uf_event K CE) :=
  match actions with
  | [] => (forest, [AuditUFHistoryCase 0])
  | action :: rest =>
      let '(next, first) := audit_uf_action_run enc action forest in
      let '(out, tail) := audit_uf_history enc rest next in
      (out, AuditUFHistoryCase (S (length rest)) :: first ++ tail)
  end.

(** Discarding the uf history events recovers the corresponding original operation under its
  premises. *)
Definition audit_uf_history_erases_statement : Prop :=
  forall K CE (enc : K -> positive * list CE) (original : encoding K) actions forest,
    (forall k, fst (enc k) = encode original k) ->
    fst (audit_uf_history enc actions forest) =
      fold_left (audit_uf_original_action original) actions forest.

(** This mathematical adapter represents the original [of_unions] fold, not extra runtime work. *)
Definition audit_uf_of_unions {K CE} (enc : K -> positive * list CE) (inputs : list (K * K)) :=
  audit_uf_history enc (map (fun xy => AuditUFUnion (fst xy) (snd xy)) inputs) UnionFind.make.

(** Discarding the uf of unions events recovers the corresponding original operation under its
  premises. *)
Definition audit_uf_of_unions_erases_statement : Prop :=
  forall K CE (enc : K -> positive * list CE) (original : encoding K) inputs,
    (forall k, fst (enc k) = encode original k) ->
    fst (audit_uf_of_unions enc inputs) = UnionFind.of_unions original inputs.

(** The budget tracks max-rank on each actual persistent state before an action. *)
Fixpoint audit_uf_history_frame_budget {K CE} (enc : K -> positive * list CE)
    (actions : list (audit_uf_action K)) (forest : UnionFind.t K) : nat :=
  match actions with
  | [] => 1
  | action :: rest =>
      let next := fst (audit_uf_action_run enc action forest) in
      1 + (match action with
           | AuditUFFind _ => 1 + 3 * S (UnionFind.max_rank forest)
           | AuditUFUnion _ _ => 16 + 6 * S (UnionFind.max_rank forest)
           end) + audit_uf_history_frame_budget enc rest next
  end.

(** History work is bounded by its frame budget and actual primitive work. *)
Definition audit_uf_history_bound_statement : Prop :=
  forall K CE (enc : K -> positive * list CE) enc_work actions forest,
    let events := snd (audit_uf_history enc actions forest) in
    audit_uf_source_work enc_work events <=
      4 * audit_uf_history_frame_budget enc actions forest + audit_uf_primitive_work enc_work
        events.

(** Union-list work is bounded by history frames and actual primitive work. *)
Definition audit_uf_of_unions_source_bound_statement : Prop :=
  forall K CE (enc : K -> positive * list CE) enc_work inputs,
    let actions := map (fun xy => AuditUFUnion (fst xy) (snd xy)) inputs in
    let events := snd (audit_uf_of_unions enc inputs) in
    audit_uf_source_work enc_work events <=
      4 * audit_uf_history_frame_budget enc actions UnionFind.make + audit_uf_primitive_work
        enc_work events.

(** Both branches are evaluated from the same original forest, with distinct retained traces. *)
Definition audit_uf_branches {K CE} (enc : K -> positive * list CE)
    (left right : list (audit_uf_action K)) (forest : UnionFind.t K) :=
  (audit_uf_history enc left forest, audit_uf_history enc right forest).

(** Combined branch work is bounded by both frame budgets and their primitive work. *)
Definition audit_uf_branches_bound_statement : Prop :=
  forall K CE (enc : K -> positive * list CE) enc_work left right forest,
    let branches := audit_uf_branches enc left right forest in
    let le := snd (fst branches) in
    let re := snd (snd branches) in
    audit_uf_source_work enc_work le + audit_uf_source_work enc_work re <=
      4 * (audit_uf_history_frame_budget enc left forest +
           audit_uf_history_frame_budget enc right forest) +
      audit_uf_primitive_work enc_work le + audit_uf_primitive_work enc_work re.
