(** * Historical collection event counters

    These counters record selected events rather than full source-runtime accounting.
    For example, a batch read records the number of present slots.
    Builds on: CollectionsUnionFind and CollectionsAuditState. *)

From Stdlib Require Import List NArith PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsUnionFind
  CollectionsAuditState.
Import List.ListNotations.
Record slot_batch_work : Type := SlotBatchWork {
  slot_reads : nat;
  slot_key_bits : nat
}.

Fixpoint read_slots_counted {V} (m : slot_map V) (slots : list (option N)) :
    list (option V) * slot_batch_work :=
  match slots with
  | [] => ([], SlotBatchWork 0 0)
  | None :: rest =>
    let '(out, work) := read_slots_counted m rest in (None :: out, work)
  | Some i :: rest =>
    let '(out, work) := read_slots_counted m rest in
    (slot_read m i :: out, SlotBatchWork (S (slot_reads work))
      (Pos.size_nat (encode N_encoding i) + slot_key_bits work))
  end.

(** Counted slot reads preserve the result and account for present slots and their encoded
  widths. *)
Definition slot_batch_cost_statement : Prop :=
  forall V (m : slot_map V) slots,
    let '(out, work) := read_slots_counted m slots in
    out = read_slots m slots /\ length out = length slots /\
    slot_reads work = length (filter (fun s => match s with
    | Some _ => true
    | None => false
    end)
      slots) /\
    slot_key_bits work = fold_right (fun slot bits => match slot with
      | Some i => Pos.size_nat (encode N_encoding i) + bits
      | None => bits
      end) 0 slots.
Inductive union_action (K : Type) : Type :=
  | FindAction (x : K)
  | UnionAction (x y : K).

Arguments FindAction {K}.
Arguments UnionAction {K}.

Definition action_step {K} (E : encoding K) (a : union_action K) (uf : UnionFind.t K) :
    UnionFind.t K :=
  match a with
  | FindAction x => snd (UnionFind.find E x uf)
  | UnionAction x y => UnionFind.union E x y uf
  end.

Inductive union_event (K : Type) : Type :=
  | UFFuelCheck (remaining : nat)
  | UFParentGet (key : K)
  | UFParentSet (key : K)
  | UFRankGet (key : K)
  | UFRankSet (key : K)
  | UFKeyCompare (left right : K)
  | UFRankCompare (left right : nat)
  | UFRankSuccessor (rank : nat)
  | UFRankMax (left right : nat).
Arguments UFFuelCheck {K}.
Arguments UFParentGet {K}.
Arguments UFParentSet {K}.
Arguments UFRankGet {K}.
Arguments UFRankSet {K}.
Arguments UFKeyCompare {K}.
Arguments UFRankCompare {K}.
Arguments UFRankSuccessor {K}.
Arguments UFRankMax {K}.

Fixpoint trace_find_fuel {K} (E : encoding K) (fuel : nat) (x : K) (uf : UnionFind.t K)
    : (K * UnionFind.t K) * list (union_event K) :=
  match fuel with
  | 0 => ((x, uf), [UFFuelCheck 0])
  | S rest =>
    match Map.get E x (UnionFind.parents uf) with
    | None => ((x, uf), [UFFuelCheck (S rest); UFParentGet x])
    | Some y =>
      let '(result, events) := trace_find_fuel E rest y uf in
      let '(root, compressed) := result in
      ((root, UnionFind.redirect E x root compressed),
        UFFuelCheck (S rest) :: UFParentGet x :: events ++ [UFParentSet x])
    end
  end.

Definition trace_find {K} (E : encoding K) (x : K) (uf : UnionFind.t K) :=
  trace_find_fuel E (S (UnionFind.max_rank uf)) x uf.

Definition trace_union {K} (E : encoding K) (x y : K) (uf : UnionFind.t K)
    : UnionFind.t K * list (union_event K) :=
  let '(first, e1) := trace_find E x uf in
  let '(rx, uf1) := first in
  let '(second, e2) := trace_find E y uf1 in
  let '(ry, uf2) := second in
  let prefix := e1 ++ e2 ++ [UFKeyCompare rx ry] in
  if UnionFind.key_eqb E rx ry then
    match Map.get E rx (UnionFind.ranks uf2) with
    | Some _ => (uf2, prefix ++ [UFRankGet rx])
    | None => (UnionFind.Forest (UnionFind.parents uf2)
        (Map.set E rx 0 (UnionFind.ranks uf2)) (UnionFind.max_rank uf2),
        prefix ++ [UFRankGet rx; UFRankSet rx])
    end
  else
    let rankx := UnionFind.rank_of E uf2 rx in
    let ranky := UnionFind.rank_of E uf2 ry in
    let ranked := prefix ++ [UFRankGet rx; UFRankGet ry; UFRankCompare rankx ranky] in
    match Nat.compare rankx ranky with
    | Lt => (UnionFind.link E rx ry false uf2, ranked ++ [UFParentSet rx])
    | Gt => (UnionFind.link E ry rx false uf2, ranked ++ [UFParentSet ry])
    | Eq => (UnionFind.link E ry rx true uf2,
        ranked ++ [UFRankGet rx; UFRankSuccessor rankx; UFParentSet ry; UFRankSet rx;
          UFRankMax (UnionFind.max_rank uf2) (S rankx)])
    end.

(** Discarding the find trace returns the original union-find result. *)
Definition trace_find_result_statement : Prop :=
  forall K (E : encoding K) x uf, fst (trace_find E x uf) = UnionFind.find E x uf.
(** Discarding the union trace returns the original union-find result. *)
Definition trace_union_result_statement : Prop :=
  forall K (E : encoding K) x y uf, fst (trace_union E x y uf) = UnionFind.union E x y uf.

Definition event_keys {K} (event : union_event K) : list K :=
  match event with
  | UFParentGet k | UFParentSet k | UFRankGet k | UFRankSet k => [k]
  | UFKeyCompare a b => [a; b]
  | _ => []
  end.

Definition event_key_bits {K} (E : encoding K) (events : list (union_event K)) : nat :=
  fold_right (fun event total => fold_right (fun k n => Pos.size_nat (encode E k) + n)
    total (event_keys event)) 0 events.

Record union_callback_costs (K : Type) : Type := UnionCallbackCosts {
  union_encode_work : K -> nat
}.
Arguments union_encode_work {K}.

Definition event_encode_work {K} (costs : union_callback_costs K) (events : list (union_event
  K)) : nat :=
  fold_right (fun event total => fold_right (fun k n => union_encode_work costs k + n)
    total (event_keys event)) 0 events.

Definition event_unary_work {K} (event : union_event K) : nat :=
  match event with
  | UFRankCompare a b | UFRankMax a b => S (Nat.min a b)
  | UFRankSuccessor _ | UFFuelCheck _ => 1
  | _ => 0
  end.

Definition event_unary_total {K} (events : list (union_event K)) : nat :=
  fold_right (fun event total => event_unary_work event + total) 0 events.

Definition trace_action {K} (E : encoding K) (action : union_action K) (uf : UnionFind.t K)
    : UnionFind.t K * list (union_event K) :=
  match action with
  | FindAction x => let '(r, events) := trace_find E x uf in (snd r, events)
  | UnionAction x y => trace_union E x y uf
  end.

Fixpoint trace_actions {K} (E : encoding K) (actions : list (union_action K)) (uf : UnionFind.t K)
    : UnionFind.t K * list (union_event K) :=
  match actions with
  | [] => (uf, [])
  | action :: rest =>
    let '(next, first) := trace_action E action uf in
    let '(last, tail) := trace_actions E rest next in (last, first ++ tail)
  end.

(** Discarding action traces yields the fold of the original union-find actions. *)
Definition trace_actions_result_statement : Prop :=
  forall K (E : encoding K) actions uf,
    fst (trace_actions E actions uf) = fold_left (fun state action => action_step E action
      state) actions uf.

Definition trace_branches {K} (E : encoding K) (uf : UnionFind.t K)
    (left right : list (union_action K)) : list (union_event K) :=
  snd (trace_actions E left uf) ++ snd (trace_actions E right uf).

(** The two branch traces contribute additive key-bit and unary-work totals. *)
Definition trace_branch_sum_statement : Prop :=
  forall K (E : encoding K) (uf : UnionFind.t K) left right,
    event_key_bits E (trace_branches E uf left right) =
      event_key_bits E (snd (trace_actions E left uf)) + event_key_bits E (snd (trace_actions E
        right uf)) /\
    event_unary_total (trace_branches E uf left right) =
      event_unary_total (snd (trace_actions E left uf)) + event_unary_total (snd (trace_actions
        E right uf)).

Record union_callback_cost_laws {K} (observed bound : union_callback_costs K) : Prop := {
  union_encode_bound : forall k, union_encode_work observed k <= union_encode_work bound k
}.

Definition union_map_gets {K} (events : list (union_event K)) : nat :=
  fold_right (fun event n => match event with
  | UFParentGet _ | UFRankGet _ => S n
  | _ => n
  end)
    0 events.
Definition union_map_sets {K} (events : list (union_event K)) : nat :=
  fold_right (fun event n => match event with
  | UFParentSet _ | UFRankSet _ => S n
  | _ => n
  end)
    0 events.
Definition union_comparisons {K} (events : list (union_event K)) : nat :=
  fold_right (fun event n => match event with
  | UFKeyCompare _ _ => S n
  | _ => n
  end) 0 events.
Definition union_fuel_checks {K} (events : list (union_event K)) : nat :=
  fold_right (fun event n => match event with
  | UFFuelCheck _ => S n
  | _ => n
  end) 0 events.
Definition union_trie_read_bits {K} (E : encoding K) (events : list (union_event K)) : nat :=
  fold_right (fun event total => match event with
    | UFParentGet k | UFRankGet k => Pos.size_nat (encode E k) + total
    | _ => total
    end) 0 events.
Definition union_trie_write_bits {K} (E : encoding K) (events : list (union_event K)) : nat :=
  fold_right (fun event total => match event with
    | UFParentSet k | UFRankSet k => Pos.size_nat (encode E k) + total
    | _ => total
    end) 0 events.
Definition union_key_compare_bits {K} (E : encoding K) (events : list (union_event K)) : nat :=
  fold_right (fun event total => match event with
    | UFKeyCompare a b => Pos.size_nat (encode E a) + Pos.size_nat (encode E b) + total
    | _ => total
    end) 0 events.

Record union_source_work : Type := UnionSourceWork {
  union_work_gets : nat;
  union_work_sets : nat;
  union_work_fuel_checks : nat;
  union_work_key_comparisons : nat;
  union_work_read_bits : nat;
  union_work_write_bits : nat;
  union_work_compare_bits : nat;
  union_work_encoder : nat;
  union_work_unary : nat;
  union_work_event_count : nat;
  union_work_actions : nat
}.

Definition union_trace_work {K} (E : encoding K) (costs : union_callback_costs K)
    (actions : list (union_action K)) (events : list (union_event K)) : union_source_work :=
  UnionSourceWork (union_map_gets events) (union_map_sets events) (union_fuel_checks events)
    (union_comparisons events) (union_trie_read_bits E events) (union_trie_write_bits E events)
    (union_key_compare_bits E events) (event_encode_work costs events) (event_unary_total events)
    (length events) (length actions).

(** The historical work record accounts for the action result, event bits and counts. *)
Definition union_source_work_statement : Prop :=
  forall K (E : encoding K) actions uf costs,
    let '(result, events) := trace_actions E actions uf in
    let work := union_trace_work E costs actions events in
    result = fold_left (fun state action => action_step E action state) actions uf /\
    union_work_read_bits work + union_work_write_bits work + union_work_compare_bits work =
      event_key_bits E events /\
    union_work_actions work = length actions /\ union_work_event_count work = length events.

(** The named prepared-key contract combines exact functional and composite-length laws. *)
