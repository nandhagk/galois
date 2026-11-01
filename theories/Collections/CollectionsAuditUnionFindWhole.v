(** * Whole persistent union-find input budgets

    These recurrences follow actual intermediate forests and keys without reading event work.
    For example, a second find uses the forest returned by the first find, including compression.
    Builds on: the counted union-find bodies and concrete encoder input budgets. *)

From Stdlib Require Import List PArith PeanoNat.
From Galois.Collections Require Import CollectionsEncoding CollectionsUnionFind
  CollectionsAuditMap
  CollectionsAuditPrimitive
  CollectionsAuditEncoding
  CollectionsAuditUnionFind
  CollectionsAuditUnionFindAdapters
  CollectionsAuditEncoderBudget.
Import List.ListNotations.

Definition audit_uf_read_budget {K CE} (enc : K -> positive * list CE)
    (budget : K -> nat) (key : K) : nat :=
  9 + budget key + 5 * Pos.size_nat (fst (enc key)).

Definition audit_uf_write_budget {K CE} (enc : K -> positive * list CE)
    (budget : K -> nat) (key : K) : nat :=
  6 + budget key + 16 * Pos.size_nat (fst (enc key)).

(** Fuel is the existing source's unary max-rank measure; this model adds no runtime fuel. *)
Fixpoint audit_uf_find_input_budget {K CE} (enc : K -> positive * list CE)
    (budget : K -> nat) (fuel : nat) (key : K) (forest : UnionFind.t K) : nat :=
  match fuel with
  | 0 => 4
  | S rest =>
      4 + audit_uf_read_budget enc budget key +
      match fst (audit_map_get enc key (UnionFind.parents forest)) with
      | None => 0
      | Some next => audit_uf_find_input_budget enc budget rest next forest +
          audit_uf_write_budget enc budget key
      end
  end.

Definition audit_uf_touch_input_budget {K CE} (enc : K -> positive * list CE)
    (budget : K -> nat) (key : K) (forest : UnionFind.t K) : nat :=
  audit_uf_read_budget enc budget key +
  match fst (audit_map_get enc key (UnionFind.ranks forest)) with
  | Some _ => 0
  | None => audit_uf_write_budget enc budget key
  end.

Definition audit_uf_link_input_budget {K CE} (enc : K -> positive * list CE)
    (budget : K -> nat) (child root : K) (raise : bool) (forest : UnionFind.t K) : nat :=
  if raise then
    let old_rank := fst (audit_uf_rank_of enc forest root) in
    audit_uf_read_budget enc budget root + audit_uf_write_budget enc budget child +
    audit_uf_write_budget enc budget root +
    4 + 3 * S (Nat.min (UnionFind.max_rank forest) (S old_rank))
  else audit_uf_write_budget enc budget child.

(** Every rank comparison and maximum uses its actual unary operands. *)
Definition audit_uf_union_input_budget {K CE} (enc : K -> positive * list CE)
    (budget : K -> nat) (x y : K) (forest : UnionFind.t K) : nat :=
  let '(rx, first) := fst (audit_uf_find enc x forest) in
  let '(ry, second) := fst (audit_uf_find enc y first) in
  let cx := fst (enc rx) in
  let cy := fst (enc ry) in
  audit_uf_find_input_budget enc budget (S (UnionFind.max_rank forest)) x forest +
  audit_uf_find_input_budget enc budget (S (UnionFind.max_rank first)) y first +
  12 + budget rx + budget ry + 2 * Nat.min (Pos.size_nat cx) (Pos.size_nat cy) +
  if fst (audit_positive_eqb cx cy) then audit_uf_touch_input_budget enc budget rx second
  else
    let rankx := fst (audit_uf_rank_of enc second rx) in
    let ranky := fst (audit_uf_rank_of enc second ry) in
    audit_uf_read_budget enc budget rx + audit_uf_read_budget enc budget ry +
    4 + 3 * S (Nat.min rankx ranky) +
    match Nat.compare rankx ranky with
    | Lt => audit_uf_link_input_budget enc budget rx ry false second
    | Gt => audit_uf_link_input_budget enc budget ry rx false second
    | Eq => audit_uf_link_input_budget enc budget ry rx true second
    end.

Definition audit_uf_equivb_input_budget {K CE} (enc : K -> positive * list CE)
    (budget : K -> nat) (x y : K) (forest : UnionFind.t K) : nat :=
  let '(rx, first) := fst (audit_uf_find enc x forest) in
  let '(ry, _) := fst (audit_uf_find enc y first) in
  audit_uf_find_input_budget enc budget (S (UnionFind.max_rank forest)) x forest +
  audit_uf_find_input_budget enc budget (S (UnionFind.max_rank first)) y first +
  12 + budget rx + budget ry +
  2 * Nat.min (Pos.size_nat (fst (enc rx))) (Pos.size_nat (fst (enc ry))).

Definition audit_uf_action_input_budget {K CE} (enc : K -> positive * list CE)
    (budget : K -> nat) (action : audit_uf_action K) (forest : UnionFind.t K) : nat :=
  match action with
  | AuditUFFind key =>
      audit_uf_find_input_budget enc budget (S (UnionFind.max_rank forest)) key forest
  | AuditUFUnion x y => audit_uf_union_input_budget enc budget x y forest
  end.

(** The recurrence retains every persistent state before the next original action. *)
Fixpoint audit_uf_history_input_budget {K CE} (enc : K -> positive * list CE)
    (budget : K -> nat) (actions : list (audit_uf_action K)) (forest : UnionFind.t K) : nat :=
  match actions with
  | [] => 4
  | action :: rest =>
      let next := fst (audit_uf_action_run enc action forest) in
      4 + audit_uf_action_input_budget enc budget action forest +
        audit_uf_history_input_budget enc budget rest next
  end.

(** Whole-operation bounds require a per-key encoder law, never a union-find work premise. *)
Definition audit_uf_whole_input_bound_statement : Prop :=
  forall K CE (enc : K -> positive * list CE) work budget,
    (forall key, work (snd (enc key)) <= budget key) ->
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

(** Pair keys instantiate the fixed pair body; only their external children supply budgets. *)
Definition audit_uf_pair_whole_input_bound_statement : Prop :=
  forall A B EA EB (first : A -> positive * list EA) (second : B -> positive * list EB)
      first_work second_work first_budget second_budget inputs,
    (forall a, first_work (snd (first a)) <= first_budget a) ->
    (forall b, second_work (snd (second b)) <= second_budget b) ->
    let enc := audit_uf_pair_encode first second in
    let budget := audit_pair_input_budget first second first_budget second_budget in
    let actions := map (fun xy => AuditUFUnion (fst xy) (snd xy)) inputs in
    audit_uf_source_work (audit_uf_pair_encoder_work first_work second_work)
      (snd (audit_uf_pair_of_unions first second inputs)) <=
      audit_uf_history_input_budget enc budget actions UnionFind.make.

(** List keys charge each occurrence of each external element encoder in every real key call. *)
Definition audit_uf_list_whole_input_bound_statement : Prop :=
  forall A CE (element : A -> positive * list CE) work budget inputs,
    (forall a, work (snd (element a)) <= budget a) ->
    let enc := audit_uf_list_encode element in
    let key_budget := audit_list_input_budget element budget in
    let actions := map (fun xy => AuditUFUnion (fst xy) (snd xy)) inputs in
    audit_uf_source_work (audit_uf_list_encoder_work work)
      (snd (audit_uf_list_of_unions element inputs)) <=
      audit_uf_history_input_budget enc key_budget actions UnionFind.make.

(** Branches start at the same original forest and each pays its full persistent history. *)
Definition audit_uf_branches_whole_input_bound_statement : Prop :=
  forall K CE (enc : K -> positive * list CE) work budget left right forest,
    (forall key, work (snd (enc key)) <= budget key) ->
    let branches := audit_uf_branches enc left right forest in
    audit_uf_source_work work (snd (fst branches)) +
      audit_uf_source_work work (snd (snd branches)) <=
    audit_uf_history_input_budget enc budget left forest +
      audit_uf_history_input_budget enc budget right forest.

Example audit_uf_initial_find_whole_budget :
  audit_uf_find_input_budget audit_positive_encode (fun _ => 1) 1 1%positive UnionFind.make = 19.
Proof.
  reflexivity.
Qed.
