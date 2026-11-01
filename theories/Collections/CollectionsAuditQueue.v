(** * Persistent queue observations

    These models record source-shaped operations on the existing persistent priority queue.
    For example, inserting into an occupied heap slot records its link and comparison.
    Builds on: CollectionsEncoding, CollectionsMap, CollectionsHeap and CollectionsTrie. *)

From Stdlib Require Import List Bool PArith Arith ZArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsHeap CollectionsAuditCost CollectionsAuditTrie CollectionsAuditPrimitive
    CollectionsAuditCompare.
Import List.ListNotations.

(** Events retain operands and map versions needed to account for each operation. *)

Inductive queue_event (K : Type) : Type :=
  | QInsertSlot
  | QMeldSlot
  | QSelectSlot
  | QLink
  | QEntryCompare (a b : PQueue.entry K)
  | QPriorityLt (a b : positive)
  | QPriorityEq (a b : positive)
  | QGet (k : K) (m : Map.t K positive)
  | QSet (k : K) (p : positive) (m : Map.t K positive)
  | QRemove (k : K) (m : Map.t K positive)
  | QEncode (k : K)
  | QChildren (t : PQueue.tree K)
  | QExamined
  | QStale
  | QAccepted
  | QFuelStep.

Arguments QInsertSlot {K}.
Arguments QMeldSlot {K}.
Arguments QSelectSlot {K}.
Arguments QLink {K}.
Arguments QEntryCompare {K}.
Arguments QPriorityLt {K}.
Arguments QPriorityEq {K}.
Arguments QGet {K}.
Arguments QSet {K}.
Arguments QRemove {K}.
Arguments QEncode {K}.
Arguments QChildren {K}.
Arguments QExamined {K}.
Arguments QStale {K}.
Arguments QAccepted {K}.
Arguments QFuelStep {K}.

Definition queue_link {K} (a b : PQueue.tree K) : PQueue.tree K * list (queue_event K) :=
  (PQueue.link a b, [QLink; QEntryCompare (PQueue.root a) (PQueue.root b)]).

Fixpoint queue_insert {K} (t : PQueue.tree K) (h : PQueue.heap K)
    : PQueue.heap K * list (queue_event K) :=
  match h with
  | [] => ([Some t], [QInsertSlot])
  | None :: hs => (Some t :: hs, [QInsertSlot])
  | Some u :: hs =>
    let '(v, ev) := queue_link t u in
    let '(rest, er) := queue_insert v hs in
    (None :: rest, QInsertSlot :: ev ++ er)
  end.

Fixpoint queue_meld {K} (a b : PQueue.heap K) (carry : option (PQueue.tree K))
    : PQueue.heap K * list (queue_event K) :=
  match a with
  | [] =>
    match carry with
    | None => (b, [QMeldSlot])
    | Some t =>
      let '(r, es) := queue_insert t b in
      (r, QMeldSlot :: es)
    end
  | x :: xs =>
    match b with
    | [] =>
      match carry with
      | None => (a, [QMeldSlot])
      | Some t =>
        let '(r, es) := queue_insert t a in
        (r, QMeldSlot :: es)
      end
    | y :: ys =>
      let '(slot, carry', links) :=
        match x, y, carry with
        | None, None, c => (c, None, [])
        | Some t, None, None
        | None, Some t, None => (Some t, None, [])
        | Some t, Some u, None
        | Some t, None, Some u
        | None, Some t, Some u =>
          let '(v, es) := queue_link t u in
          (None, Some v, es)
        | Some t, Some u, Some c =>
          let '(v, es) := queue_link t u in
          (Some c, Some v, es)
        end in
      let '(r, es) := queue_meld xs ys carry' in
      (PQueue.digit slot r, QMeldSlot :: links ++ es)
    end
  end.

Fixpoint queue_select {K} (h : PQueue.heap K)
    : option (PQueue.tree K * PQueue.heap K) * list (queue_event K) :=
  match h with
  | [] => (None, [QSelectSlot])
  | x :: xs =>
    let '(v, es) := queue_select xs in
    match v with
    | None =>
      (match x with
       | None => None
       | Some t => Some (t, [])
       end, QSelectSlot :: es)
    | Some (t, rest) =>
      match x with
      | None => (Some (t, PQueue.digit None rest), QSelectSlot :: es)
      | Some u =>
        (if PQueue.precedesb (PQueue.root u) (PQueue.root t)
         then Some (u, PQueue.digit None xs) else Some (t, PQueue.digit (Some u) rest),
         QSelectSlot :: es ++ [QEntryCompare (PQueue.root u) (PQueue.root t)])
      end
    end
  end.

Definition queue_remove_min {K} (h : PQueue.heap K)
    : option (PQueue.entry K * PQueue.heap K) * list (queue_event K) :=
  let '(v, es) := queue_select h in
  match v with
  | None => (None, es)
  | Some (t, rest) =>
    let children := PQueue.children_heap t in
    let '(merged, em) := queue_meld children rest None in
    (Some (PQueue.root t, merged), es ++ [QChildren t] ++ em)
  end.

Definition queue_push {K} (E : encoding K) (p : positive) (k : K) (q : PQueue.t K)
    : PQueue.t K * list (queue_event K) :=
  let go n :=
    let '(h, es) := queue_insert (PQueue.Tree (p, encode E k, k) []) (PQueue.pending q) in
    (PQueue.Queue h (Map.set E k p (PQueue.live q)) n (S (PQueue.pending_count q)),
     [QEncode k] ++ es ++ [QSet k p (PQueue.live q)]) in
  match PQueue.priority E k q with
  | None =>
    let '(r, es) := go (S (PQueue.live_count q)) in
    (r, QGet k (PQueue.live q) :: es)
  | Some old =>
    if Pos.ltb p old then
      let '(r, es) := go (PQueue.live_count q) in
      (r, QGet k (PQueue.live q) :: QPriorityLt p old :: es)
    else (q, [QGet k (PQueue.live q); QPriorityLt p old])
  end.

Fixpoint queue_pop_fuel {K} (E : encoding K) (fuel : nat) (h : PQueue.heap K)
    (m : Map.t K positive) (n : nat)
    : option (positive * K * PQueue.t K) * list (queue_event K) :=
  match fuel with
  | 0 => (None, [QFuelStep])
  | S rest =>
    let '(v, es) := queue_remove_min h in
    match v with
    | None => (None, QFuelStep :: es)
    | Some ((p, c, k), h') =>
      match Map.get E k m with
      | Some current =>
        if Pos.eqb p current then
          (Some (p, k, PQueue.Queue h' (Map.remove E k m) (Nat.pred n) rest),
           QFuelStep :: es ++ [QExamined; QGet k m; QPriorityEq p current; QAccepted;
                               QRemove k m])
        else
          let '(r, er) := queue_pop_fuel E rest h' m n in
          (r, QFuelStep :: es ++ [QExamined; QGet k m; QPriorityEq p current; QStale] ++ er)
      | None =>
        let '(r, er) := queue_pop_fuel E rest h' m n in
        (r, QFuelStep :: es ++ [QExamined; QGet k m; QStale] ++ er)
      end
    end
  end.

Definition queue_pop {K} (E : encoding K) (q : PQueue.t K) :=
  queue_pop_fuel E (PQueue.pending_count q) (PQueue.pending q) (PQueue.live q)
    (PQueue.live_count q).

Inductive queue_push_execution {K} (E : encoding K) (priority : positive) (key : K)
    (state : PQueue.t K) : PQueue.t K -> list (queue_event K) -> Prop :=
  | QueuePushNew heap insert_events :
      PQueue.priority E key state = None ->
      queue_insert (PQueue.Tree (priority, encode E key, key) []) (PQueue.pending state) =
        (heap, insert_events) ->
      queue_push_execution E priority key state
        (PQueue.Queue heap (Map.set E key priority (PQueue.live state))
          (S (PQueue.live_count state)) (S (PQueue.pending_count state)))
        (QGet key (PQueue.live state) :: [QEncode key] ++ insert_events ++
          [QSet key priority (PQueue.live state)])
  | QueuePushLower old heap insert_events :
      PQueue.priority E key state = Some old -> Pos.ltb priority old = true ->
      queue_insert (PQueue.Tree (priority, encode E key, key) []) (PQueue.pending state) =
        (heap, insert_events) ->
      queue_push_execution E priority key state
        (PQueue.Queue heap (Map.set E key priority (PQueue.live state))
          (PQueue.live_count state) (S (PQueue.pending_count state)))
        (QGet key (PQueue.live state) :: QPriorityLt priority old :: [QEncode key] ++
    insert_events ++
          [QSet key priority (PQueue.live state)])
  | QueuePushUnchanged old :
      PQueue.priority E key state = Some old -> Pos.ltb priority old = false ->
      queue_push_execution E priority key state state
        [QGet key (PQueue.live state); QPriorityLt priority old].

Inductive queue_pop_fuel_execution {K} (E : encoding K) :
    nat -> PQueue.heap K -> Map.t K positive -> nat ->
    option (positive * K * PQueue.t K) -> list (queue_event K) -> Prop :=
  | QueuePopZero heap live count :
      queue_pop_fuel_execution E 0 heap live count None [QFuelStep]
  | QueuePopEmpty rest heap live count remove_events :
      queue_remove_min heap = (None, remove_events) ->
      queue_pop_fuel_execution E (S rest) heap live count None (QFuelStep :: remove_events)
  | QueuePopAccepted rest heap live count priority code key next_heap remove_events :
      queue_remove_min heap = (Some ((priority, code, key), next_heap), remove_events) ->
      Map.get E key live = Some priority ->
      queue_pop_fuel_execution E (S rest) heap live count
        (Some (priority, key, PQueue.Queue next_heap (Map.remove E key live) (Nat.pred count) rest))
        (QFuelStep :: remove_events ++ [QExamined; QGet key live; QPriorityEq priority priority;
          QAccepted; QRemove key live])
  | QueuePopStale rest heap live count priority code key next_heap current remove_events result
    later :
      queue_remove_min heap = (Some ((priority, code, key), next_heap), remove_events) ->
      Map.get E key live = Some current -> Pos.eqb priority current = false ->
      queue_pop_fuel_execution E rest next_heap live count result later ->
      queue_pop_fuel_execution E (S rest) heap live count result
        (QFuelStep :: remove_events ++ [QExamined; QGet key live; QPriorityEq priority current;
    QStale] ++ later)
  | QueuePopMissing rest heap live count priority code key next_heap remove_events result later :
      queue_remove_min heap = (Some ((priority, code, key), next_heap), remove_events) ->
      Map.get E key live = None ->
      queue_pop_fuel_execution E rest next_heap live count result later ->
      queue_pop_fuel_execution E (S rest) heap live count result
        (QFuelStep :: remove_events ++ [QExamined; QGet key live; QStale] ++ later).

(** Both outer source relations have an actual counted run and the existing result. *)
Definition queue_outer_execution_statement : Prop :=
  (forall K (E : encoding K) priority key state,
    let '(result, events) := queue_push E priority key state in
    queue_push_execution E priority key state result events /\
    result = PQueue.push E priority key state) /\
  (forall K (E : encoding K) fuel heap live count,
    let '(result, events) := queue_pop_fuel E fuel heap live count in
    queue_pop_fuel_execution E fuel heap live count result events /\
    result = PQueue.pop_fuel E fuel heap live count).

(** Each traced queue operation returns the existing operation's exact result. *)
Definition queue_projection_laws : Prop :=
  (forall K (t : PQueue.tree K) h, fst (queue_insert t h) = PQueue.insert t h) /\
  (forall K (a b : PQueue.heap K) c, fst (queue_meld a b c) = PQueue.meld a b c) /\
  (forall K (h : PQueue.heap K), fst (queue_select h) = PQueue.select h) /\
  (forall K (h : PQueue.heap K), fst (queue_remove_min h) = PQueue.remove_min h) /\
  (forall K (E : encoding K) p k q, fst (queue_push E p k q) = PQueue.push E p k q) /\
  (forall K (E : encoding K) fuel h m n,
    fst (queue_pop_fuel E fuel h m n) = PQueue.pop_fuel E fuel h m n) /\
  (forall K (E : encoding K) q, fst (queue_pop E q) = PQueue.pop E q).

(** * Event cost dimensions *)

(** Each map event includes its encoder; [QEncode] records the heap entry key. *)
Definition queue_event_keys {K} (event : queue_event K) : list K :=
  match event with
  | QGet k _
  | QSet k _ _
  | QRemove k _
  | QEncode k => [k]
  | _ => []
  end.

Definition queue_key_calls {K} (events : list (queue_event K)) : list K :=
  flat_map queue_event_keys events.

Definition queue_key_bits {K} (E : encoding K) (events : list (queue_event K)) : nat :=
  fold_right (fun k n => Pos.size_nat (encode E k) + n) 0 (queue_key_calls events).

Definition queue_entry_compare_args {K} (a b : PQueue.entry K) : list (positive * positive) :=
  let p := fst (fst a) in
  let q := fst (fst b) in
  let x := snd (fst a) in
  let y := snd (fst b) in
  [(p, q); (p, q); (x, y)].

Definition queue_comparisons {K} (event : queue_event K) : list (positive * positive) :=
  match event with
  | QEntryCompare a b => queue_entry_compare_args a b
  | QPriorityLt a b
  | QPriorityEq a b => [(a, b)]
  | _ => []
  end.

Definition queue_compare_calls {K} (events : list (queue_event K)) : list (positive * positive) :=
  flat_map queue_comparisons events.

Definition queue_compare_operand_bits {K} (events : list (queue_event K)) : nat :=
  fold_right (fun '(x, y) n => Pos.size_nat x + Pos.size_nat y + n) 0
    (queue_compare_calls events).

(** Element-cell work excludes the two terminal calls for each child traversal. *)
Definition queue_child_cells {K} (events : list (queue_event K)) : nat :=
  fold_right (fun event n =>
    match event with
    | QChildren (PQueue.Tree _ cs) => 2 * length cs + n
    | _ => n
    end) 0 events.

Definition queue_child_calls {K} (events : list (queue_event K)) : nat :=
  fold_right (fun event n =>
    match event with
    | QChildren (PQueue.Tree _ cs) => 2 + 2 * length cs + n
    | _ => n
    end) 0 events.

Definition queue_stale_count {K} (events : list (queue_event K)) : nat :=
  length (filter (fun event =>
    match event with
    | QStale => true
    | _ => false
    end) events).

Definition queue_examined_count {K} (events : list (queue_event K)) : nat :=
  length (filter (fun event =>
    match event with
    | QExamined => true
    | _ => false
    end) events).

(** This ghost count describes retained path positions, not native allocation. *)
Fixpoint queue_remove_nodes {A} (p : positive) (tr : Trie.t A) : nat :=
  (if Trie.is_empty (Trie.remove p tr) then 0 else 1) +
  match p with
  | xH => 0
  | xO q => queue_remove_nodes q (Trie.left tr)
  | xI q => queue_remove_nodes q (Trie.right tr)
  end.

Definition queue_trie_visits {K} (E : encoding K) (event : queue_event K) : nat :=
  match event with
  | QGet k _
  | QSet k _ _
  | QRemove k _ => Pos.size_nat (encode E k)
  | _ => 0
  end.

Definition queue_trie_nodes {K} (E : encoding K) (event : queue_event K) : nat :=
  match event with
  | QSet k _ _ => Pos.size_nat (encode E k)
  | QRemove k m => queue_remove_nodes (encode E k) m
  | _ => 0
  end.

Definition queue_total_trie_visits {K} (E : encoding K) (events : list (queue_event K)) : nat :=
  fold_right (fun event n => queue_trie_visits E event + n) 0 events.

Definition queue_total_trie_nodes {K} (E : encoding K) (events : list (queue_event K)) : nat :=
  fold_right (fun event n => queue_trie_nodes E event + n) 0 events.

(** Encoder body work is charged independently from encoded bit length. *)

Definition queue_slot_steps {K} (events : list (queue_event K)) : nat :=
  length (filter (fun event =>
    match event with
    | QInsertSlot
    | QMeldSlot
    | QSelectSlot => true
    | _ => false
    end) events).

Definition queue_link_count {K} (events : list (queue_event K)) : nat :=
  length (filter (fun event =>
    match event with
    | QLink => true
    | _ => false
    end) events).

Definition queue_fuel_steps {K} (events : list (queue_event K)) : nat :=
  length (filter (fun event =>
    match event with
    | QFuelStep => true
    | _ => false
    end) events).

Definition queue_comparison_model (xy : positive * positive) : nat :=
  audit_binary_weight (Z.pos (fst xy)) (Z.pos (snd xy)).

Definition queue_event_primitive_model {K} (E : encoding K) (event : queue_event K) : nat :=
  match event with
  | QGet key _ => audit_get_weight (encode E key) +
      audit_encoding_weight (audit_key_bits_weight (encode E key))
  | QSet key _ _ => audit_set_weight (encode E key) +
      audit_encoding_weight (audit_key_bits_weight (encode E key))
  | QRemove key _ => audit_remove_weight (encode E key) +
      audit_encoding_weight (audit_key_bits_weight (encode E key))
  | QEncode key => audit_encoding_weight (audit_key_bits_weight (encode E key))
  | QChildren (PQueue.Tree _ children) => 1 + 2 * length children
  | QEntryCompare a b => fold_right (fun xy n => queue_comparison_model xy + n) 0
      (queue_entry_compare_args a b)
  | QPriorityLt a b
  | QPriorityEq a b => queue_comparison_model (a, b)
  | _ => 0
  end.

Definition queue_model_budget {K} (E : encoding K) (events : list (queue_event K)) : nat :=
  64 * S (length events) * S (length events) + 64 * length events +
    fold_right (fun event n => queue_event_primitive_model E event + n) 0 events.

Definition queue_model_work {K} (E : encoding K) (events : list (queue_event K)) : nat :=
  64 * S (length events) * S (length events) +
    fold_right (fun event n => 64 + queue_event_primitive_model E event + n) 0 events.

(** The queue model work and budget are equal for every trace. *)
Definition queue_model_equation_statement : Prop :=
  forall K (E : encoding K) events, queue_model_work E events = queue_model_budget E events.

(** Counted insertion returns the queue result with bounded events and exact model work. *)
Definition queue_insert_counted_statement : Prop :=
  forall K (E : encoding K) (tree : PQueue.tree K) heap,
    let '(result, events) := queue_insert tree heap in
    result = PQueue.insert tree heap /\
    length events <= S (3 * length heap) /\
    queue_model_work E events = queue_model_budget E events.

(** Counted selection returns the queue result with bounded events and exact model work. *)
Definition queue_select_counted_statement : Prop :=
  forall K (E : encoding K) (heap : PQueue.heap K),
    let '(result, events) := queue_select heap in
    result = PQueue.select heap /\
    length events <= S (2 * length heap) /\
    queue_model_work E events = queue_model_budget E events.

(** Counted melding returns the queue result with bounded events and exact model work. *)
Definition queue_meld_counted_statement : Prop :=
  forall K (E : encoding K) (a b : PQueue.heap K) carry,
    let '(result, events) := queue_meld a b carry in
    result = PQueue.meld a b carry /\
    length events <= 2 + 4 * (length a + length b) /\
    queue_model_work E events = queue_model_budget E events.

(** Counted minimum removal returns the queue result with exact model work. *)
Definition queue_remove_min_counted_statement : Prop :=
  forall K (E : encoding K) (heap : PQueue.heap K),
    let '(result, events) := queue_remove_min heap in
    result = PQueue.remove_min heap /\
    queue_model_work E events = queue_model_budget E events.

(** Counted fuelled pop returns the queue result with bounded fuel steps and exact work. *)
Definition queue_pop_fuel_counted_statement : Prop :=
  forall K (E : encoding K) fuel heap live count,
    let '(result, events) := queue_pop_fuel E fuel heap live count in
    result = PQueue.pop_fuel E fuel heap live count /\
    queue_fuel_steps events <= S fuel /\
    queue_model_work E events = queue_model_budget E events.

(** Counted push returns the queue result with exact model work. *)
Definition queue_push_counted_statement : Prop :=
  forall K (E : encoding K) priority key state,
    let '(result, events) := queue_push E priority key state in
    result = PQueue.push E priority key state /\
    queue_model_work E events = queue_model_budget E events.

(** Counted pop returns the queue result with bounded fuel steps and exact model work. *)
Definition queue_pop_counted_statement : Prop :=
  forall K (E : encoding K) state,
    let '(result, events) := queue_pop E state in
    result = PQueue.pop E state /\
    queue_fuel_steps events <= S (PQueue.pending_count state) /\
    queue_model_work E events = queue_model_budget E events.

Example queue_zero_fuel_is_charged :
  let '(result, events) := queue_pop nat_encoding (@PQueue.empty nat) in
  (result, queue_model_work nat_encoding events) = (None, 320).
Proof.
  reflexivity.
Qed.

Example queue_strict_comparison_all_operands :
  length (queue_entry_compare_args (1%positive, 3%positive, 0%nat)
    (2%positive, 4%positive, 1%nat)) = 3.
Proof.
  reflexivity.
Qed.

Definition audit_queue_input_width {K} (E : encoding K) (heap : PQueue.heap K)
    (live : Map.t K positive) (extra_keys : list K) (extra_numbers : list positive) : nat :=
  let entries := PQueue.entries heap in
  let live_rows := Map.elements live in
  let keys := extra_keys ++ map snd entries ++ map fst live_rows in
  let numbers := extra_numbers ++ flat_map (fun entry => [fst (fst entry); snd (fst entry)])
    entries ++
    map snd live_rows in
  Nat.max (fold_right Nat.max 0 (map (fun k => audit_key_bits_weight (encode E k)) keys))
    (fold_right Nat.max 0 (map audit_key_bits_weight numbers)).

Definition audit_queue_input_scale {K} (fuel : nat) (heap : PQueue.heap K) : nat :=
  1 + fuel + length heap + length (PQueue.entries heap).

Definition audit_queue_input_event_bound {K} (fuel : nat) (heap : PQueue.heap K) : nat :=
  256 * Nat.pow (S (audit_queue_input_scale fuel heap)) 3.

Definition audit_queue_input_budget {K} (E : encoding K) (fuel : nat) (heap : PQueue.heap K)
    (live : Map.t K positive) (extra_keys : list K) (extra_numbers : list positive) : nat :=
  let size := audit_queue_input_scale fuel heap in
  let count := audit_queue_input_event_bound fuel heap in
  let width := audit_queue_input_width E heap live extra_keys extra_numbers in
  1024 * S count * S count + count * (128 + 12 * width + 8 * size).

(** Counted push returns the queue result with input-derived event and work bounds. *)
Definition audit_queue_push_input_statement : Prop :=
  forall K (E : encoding K) priority key state,
    let '(result, events) := queue_push E priority key state in
    result = PQueue.push E priority key state /\
    length events <= audit_queue_input_event_bound 1 (PQueue.pending state) /\
    queue_model_work E events <= audit_queue_input_budget E 1 (PQueue.pending state)
    (PQueue.live state) [key] [priority].

(** Counted fuelled pop returns the queue result with input-derived event and work bounds. *)
Definition audit_queue_pop_fuel_input_statement : Prop :=
  forall K (E : encoding K) fuel heap live count,
    let '(result, events) := queue_pop_fuel E fuel heap live count in
    result = PQueue.pop_fuel E fuel heap live count /\ length events <=
    audit_queue_input_event_bound fuel heap /\
    queue_model_work E events <= audit_queue_input_budget E fuel heap live [] [].

(** Counted pop returns the queue result with input-derived event and work bounds. *)
Definition audit_queue_pop_input_statement : Prop :=
  forall K (E : encoding K) state,
    let '(result, events) := queue_pop E state in
    result = PQueue.pop E state /\
    length events <= audit_queue_input_event_bound (PQueue.pending_count state) (PQueue.pending
    state) /\
    queue_model_work E events <= audit_queue_input_budget E (PQueue.pending_count state)
      (PQueue.pending state) (PQueue.live state) [] [].

Definition audit_queue_encoder_model (K B : Type) : Type := K -> positive * list B.

(** The encoder model returns the supplied key encoding. *)
Definition audit_queue_encoder_erases {K B} (E : encoding K) (encoder :
    audit_queue_encoder_model K B) : Prop :=
  forall k, fst (encoder k) = encode E k.

Definition audit_queue_nested_event (K B : Type) : Type := queue_event K * (option (option
    positive) * list B).

Definition audit_queue_push_nested {K B} (encoder : audit_queue_encoder_model K B)
    (priority : positive) (key : K) (state : PQueue.t K)
    : PQueue.t K * list (audit_queue_nested_event K B) :=
  let '(lookup_code, lookup_body) := encoder key in
  let found := Map.code_get lookup_code (PQueue.live state) in
  let go := fun live_count =>
    let '(tree_code, tree_body) := encoder key in
    let '(heap, events) := queue_insert (PQueue.Tree (priority, tree_code, key) [])
    (PQueue.pending state) in
    let '(set_code, set_body) := encoder key in
    (PQueue.Queue heap (Trie.set set_code (key, priority) (PQueue.live state)) live_count
      (S (PQueue.pending_count state)),
     (QEncode key, (None, tree_body)) :: map (fun e => (e, (None, []))) events ++ [(QSet key
    priority (PQueue.live state), (None, set_body))]) in
  match found with
  | None => let '(result, events) := go (S (PQueue.live_count state)) in
      (result, (QGet key (PQueue.live state), (Some found, lookup_body)) :: events)
  | Some old => let lower := Pos.ltb priority old in
    if lower then let '(result, events) := go (PQueue.live_count state) in
      (result, (QGet key (PQueue.live state), (Some found, lookup_body)) :: (QPriorityLt
    priority old, (None, [])) :: events)
    else (state, [(QGet key (PQueue.live state), (Some found, lookup_body)); (QPriorityLt
    priority old, (None, []))])
  end.

Fixpoint audit_queue_pop_fuel_nested {K B} (encoder : audit_queue_encoder_model K B)
    (fuel : nat) (heap : PQueue.heap K) (live : Map.t K positive) (count : nat)
    : option (positive * K * PQueue.t K) * list (audit_queue_nested_event K B) :=
  match fuel with
  | 0 => (None, [(QFuelStep, (None, []))])
  | S rest => let '(selected, select_events) := queue_remove_min heap in
    match selected with
    | None => (None, (QFuelStep, (None, [])) :: map (fun e => (e, (None, []))) select_events)
    | Some ((priority, code, key), remaining) =>
      let '(lookup_code, lookup_body) := encoder key in let current := Map.code_get lookup_code
    live in
      match current with
      | Some actual => let equal := Pos.eqb priority actual in
        if equal then let '(remove_code, remove_body) := encoder key in
          (Some (priority, key, PQueue.Queue remaining (Trie.remove remove_code live) (Nat.pred
    count) rest),
           (QFuelStep, (None, [])) :: map (fun e => (e, (None, []))) select_events ++
           [(QExamined, (None, [])); (QGet key live, (Some current, lookup_body)); (QPriorityEq
    priority actual, (None, []));
            (QAccepted, (None, [])); (QRemove key live, (None, remove_body))])
        else let '(result, events) := audit_queue_pop_fuel_nested encoder rest remaining live
    count in
          (result, (QFuelStep, (None, [])) :: map (fun e => (e, (None, []))) select_events ++
            [(QExamined, (None, [])); (QGet key live, (Some current, lookup_body)); (QPriorityEq
    priority actual, (None, [])); (QStale, (None, []))] ++ events)
      | None => let '(result, events) := audit_queue_pop_fuel_nested encoder rest remaining live
    count in
          (result, (QFuelStep, (None, [])) :: map (fun e => (e, (None, []))) select_events ++
            [(QExamined, (None, [])); (QGet key live, (Some current, lookup_body)); (QStale,
    (None, []))] ++ events)
      end
    end
  end.

Definition audit_queue_pop_nested {K B} (encoder : audit_queue_encoder_model K B) (state :
    PQueue.t K) :=
  audit_queue_pop_fuel_nested encoder (PQueue.pending_count state) (PQueue.pending state)
    (PQueue.live state) (PQueue.live_count state).

Definition audit_queue_nested_body_work {K B} (weight : B -> nat) (events : list
    (audit_queue_nested_event K B)) : nat :=
  fold_right (fun event total => fold_right (fun item n => weight item + n) 0 (snd (snd event))
    + total) 0 events.

Definition audit_queue_nested_total_work {K B} (E : encoding K) (weight : B -> nat)
    (events : list (audit_queue_nested_event K B)) : nat :=
  queue_model_work E (map fst events) + audit_queue_nested_body_work weight events.

(** Nested push erases to the counted trace and obeys its input-derived bounds. *)
Definition audit_queue_push_nested_statement : Prop :=
  forall K B (E : encoding K) (encoder : audit_queue_encoder_model K B) priority key state,
    audit_queue_encoder_erases E encoder ->
    let '(result, events) := audit_queue_push_nested encoder priority key state in
    result = PQueue.push E priority key state /\ map fst events = snd (queue_push E priority key
    state) /\
    length events <= audit_queue_input_event_bound 1 (PQueue.pending state) /\
    queue_model_work E (map fst events) <= audit_queue_input_budget E 1 (PQueue.pending state)
    (PQueue.live state) [key] [priority].

(** Nested fuelled pop erases to the counted trace and obeys its input-derived bounds. *)
Definition audit_queue_pop_fuel_nested_statement : Prop :=
  forall K B (E : encoding K) (encoder : audit_queue_encoder_model K B) fuel heap live count,
    audit_queue_encoder_erases E encoder ->
    let '(result, events) := audit_queue_pop_fuel_nested encoder fuel heap live count in
    result = PQueue.pop_fuel E fuel heap live count /\ map fst events = snd (queue_pop_fuel E
    fuel heap live count) /\
    length events <= audit_queue_input_event_bound fuel heap /\
    queue_model_work E (map fst events) <= audit_queue_input_budget E fuel heap live [] [].

(** Nested pop erases to the counted trace and obeys its input-derived bounds. *)
Definition audit_queue_pop_nested_statement : Prop :=
  forall K B (E : encoding K) (encoder : audit_queue_encoder_model K B) state,
    audit_queue_encoder_erases E encoder ->
    let '(result, events) := audit_queue_pop_nested encoder state in
    result = PQueue.pop E state /\ map fst events = snd (queue_pop E state) /\
    length events <= audit_queue_input_event_bound (PQueue.pending_count state) (PQueue.pending
    state) /\
    queue_model_work E (map fst events) <= audit_queue_input_budget E (PQueue.pending_count state)
      (PQueue.pending state) (PQueue.live state) [] [].

Definition audit_queue_capture_encoder {K B} (encoder : audit_queue_encoder_model K B)
    : audit_queue_encoder_model K (positive * list B) :=
  fun key => let '(code, body) := encoder key in (code, [(code, body)]).

Definition audit_queue_recorded_push {K B} (encoder : audit_queue_encoder_model K B)
    (priority : positive) (key : K) (state : PQueue.t K) :=
  audit_queue_push_nested (audit_queue_capture_encoder encoder) priority key state.

Definition audit_queue_recorded_pop {K B} (encoder : audit_queue_encoder_model K B) (state :
    PQueue.t K) :=
  audit_queue_pop_nested (audit_queue_capture_encoder encoder) state.

Definition audit_queue_recorded_pop_fuel {K B} (encoder : audit_queue_encoder_model K B)
    (fuel : nat) (heap : PQueue.heap K) (live : Map.t K positive) (count : nat) :=
  audit_queue_pop_fuel_nested (audit_queue_capture_encoder encoder) fuel heap live count.

Definition audit_queue_recorded_body_work {K B} (weight : B -> nat)
    (events : list (audit_queue_nested_event K (positive * list B))) : nat :=
  audit_queue_nested_body_work (fun captured => 1 + fold_right (fun item n => weight item + n) 0
    (snd captured)) events.

(** Recorded queue events retain the encoder codes and observed map reads. *)
Definition audit_queue_recorded_codes {K B} (E : encoding K)
    (events : list (audit_queue_nested_event K (positive * list B))) : Prop :=
  Forall (fun recorded => let '(event, (observed, bodies)) := recorded in
    match event with
    | QGet key m => observed = Some (Map.get E key m) /\ exists body, bodies = [(encode E key,
    body)]
    | QSet key _ _
    | QRemove key _
    | QEncode key =>
        observed = None /\ exists body, bodies = [(encode E key, body)]
    | _ => observed = None /\ bodies = []
    end) events.

(** Recorded push and pop preserve queue results, traces, codes and input-derived bounds. *)
Definition audit_queue_recorded_statement : Prop :=
  (forall K B (E : encoding K) (encoder : audit_queue_encoder_model K B) priority key state,
    audit_queue_encoder_erases E encoder ->
    let '(result, events) := audit_queue_recorded_push encoder priority key state in
    result = PQueue.push E priority key state /\ map fst events = snd (queue_push E priority key
    state) /\
    audit_queue_recorded_codes E events /\
    length events <= audit_queue_input_event_bound 1 (PQueue.pending state) /\
    queue_model_work E (map fst events) <= audit_queue_input_budget E 1 (PQueue.pending state)
    (PQueue.live state) [key] [priority]) /\
  (forall K B (E : encoding K) (encoder : audit_queue_encoder_model K B) state,
    audit_queue_encoder_erases E encoder ->
    let '(result, events) := audit_queue_recorded_pop encoder state in
    result = PQueue.pop E state /\ map fst events = snd (queue_pop E state) /\
    audit_queue_recorded_codes E events /\
    length events <= audit_queue_input_event_bound (PQueue.pending_count state) (PQueue.pending
    state) /\
    queue_model_work E (map fst events) <= audit_queue_input_budget E (PQueue.pending_count state)
      (PQueue.pending state) (PQueue.live state) [] []).

(** The queue family combines its execution, projection, counted and nested contracts. *)
Definition audit_queue_family_statement : Prop :=
  queue_outer_execution_statement /\ queue_projection_laws /\
  queue_insert_counted_statement /\ queue_select_counted_statement /\
    queue_meld_counted_statement /\
  queue_remove_min_counted_statement /\ queue_pop_fuel_counted_statement /\
  audit_queue_push_input_statement /\ audit_queue_pop_fuel_input_statement /\
    audit_queue_pop_input_statement /\
  audit_queue_push_nested_statement /\ audit_queue_pop_fuel_nested_statement /\
    audit_queue_pop_nested_statement /\
  audit_queue_recorded_statement.

Definition audit_queue_ltb_source_work (a b : positive) : nat :=
  audit_positive_order_source_work (snd (audit_positive_ltb a b)).

Definition audit_queue_leb_source_work (a b : positive) : nat :=
  audit_positive_order_source_work (snd (audit_positive_leb a b)).

Definition audit_queue_eq_source_work (a b : positive) : nat :=
  audit_positive_eqb_source_work (snd (audit_positive_eqb a b)).

Definition audit_queue_recorded_source_event {K B}
    (recorded : audit_queue_nested_event K (positive * list B)) : nat :=
  let '(event, (_, bodies)) := recorded in
  64 +
  match event, bodies with
  | QGet _ input, [(code, _)] => 5 + audit_trie_get_source_work code input
  | QSet key priority input, [(code, _)] =>
      2 + audit_trie_update_source_work code (Some (key, priority)) input
  | QRemove _ input, [(code, _)] => 2 + audit_trie_update_source_work code None input
  | QEntryCompare a b, _ =>
      audit_queue_ltb_source_work (fst (fst a)) (fst (fst b)) +
      audit_queue_eq_source_work (fst (fst a)) (fst (fst b)) +
      audit_queue_leb_source_work (snd (fst a)) (snd (fst b))
  | QPriorityLt a b, _ => audit_queue_ltb_source_work a b
  | QPriorityEq a b, _ => audit_queue_eq_source_work a b
  | QChildren (PQueue.Tree _ children), _ => 2 * length children + 2
  | _, _ => 0
  end.

Definition audit_queue_recorded_internal_source_work {K B}
    (events : list (audit_queue_nested_event K (positive * list B))) : nat :=
  fold_right (fun event total => audit_queue_recorded_source_event event + total) 0 events.

Definition audit_queue_recorded_full_source_work {K B} (weight : B -> nat)
    (events : list (audit_queue_nested_event K (positive * list B))) : nat :=
  audit_queue_recorded_internal_source_work events + audit_queue_recorded_body_work weight events.

Definition audit_queue_full_input_budget {K} (E : encoding K) (fuel : nat) (heap : PQueue.heap K)
    (live : Map.t K positive) (extra_keys : list K) (extra_numbers : list positive) : nat :=
  let size := audit_queue_input_scale fuel heap in
  let count := audit_queue_input_event_bound fuel heap in
  let width := audit_queue_input_width E heap live extra_keys extra_numbers in
  count * (256 + 64 * S width + 8 * size).

(** Recorded full push preserves its execution and codes with bounded source work. *)
Definition audit_queue_recorded_full_push_statement : Prop :=
  forall K B (E : encoding K) (encoder : audit_queue_encoder_model K B) (weight : B -> nat)
    priority key state,
    audit_queue_encoder_erases E encoder ->
    let '(result, events) := audit_queue_recorded_push encoder priority key state in
    result = PQueue.push E priority key state /\ map fst events = snd (queue_push E priority key
    state) /\
    queue_push_execution E priority key state result (map fst events) /\
    audit_queue_recorded_codes E events /\
    length events <= audit_queue_input_event_bound 1 (PQueue.pending state) /\
    audit_queue_recorded_full_source_work weight events <=
      audit_queue_full_input_budget E 1 (PQueue.pending state) (PQueue.live state) [key]
    [priority] +
      audit_queue_recorded_body_work weight events.

(** Recorded full pop preserves its execution and codes with bounded source work. *)
Definition audit_queue_recorded_full_pop_statement : Prop :=
  forall K B (E : encoding K) (encoder : audit_queue_encoder_model K B) (weight : B -> nat) state,
    audit_queue_encoder_erases E encoder ->
    let '(result, events) := audit_queue_recorded_pop encoder state in
    result = PQueue.pop E state /\ map fst events = snd (queue_pop E state) /\
    queue_pop_fuel_execution E (PQueue.pending_count state) (PQueue.pending state) (PQueue.live
    state)
      (PQueue.live_count state) result (map fst events) /\ audit_queue_recorded_codes E events /\
    length events <= audit_queue_input_event_bound (PQueue.pending_count state) (PQueue.pending
    state) /\
    audit_queue_recorded_full_source_work weight events <=
      audit_queue_full_input_budget E (PQueue.pending_count state) (PQueue.pending state)
    (PQueue.live state) [] [] +
      audit_queue_recorded_body_work weight events.

(** Recorded full fuelled pop preserves its execution and codes with bounded source work. *)
Definition audit_queue_recorded_full_pop_fuel_statement : Prop :=
  forall K B (E : encoding K) (encoder : audit_queue_encoder_model K B) (weight : B -> nat) fuel
    heap live count,
    audit_queue_encoder_erases E encoder ->
    let '(result, events) := audit_queue_recorded_pop_fuel encoder fuel heap live count in
    result = PQueue.pop_fuel E fuel heap live count /\ map fst events = snd (queue_pop_fuel E
    fuel heap live count) /\
    queue_pop_fuel_execution E fuel heap live count result (map fst events) /\
    audit_queue_recorded_codes E events /\
    length events <= audit_queue_input_event_bound fuel heap /\
    audit_queue_recorded_full_source_work weight events <=
      audit_queue_full_input_budget E fuel heap live [] [] + audit_queue_recorded_body_work
    weight events.

(** The full queue contract combines primitive and recorded source obligations. *)
Definition audit_queue_full_source_contract_statement : Prop :=
  audit_positive_compare_cont_statement /\ audit_positive_order_statement /\
  audit_positive_eqb_erases_statement /\ audit_positive_eqb_source_bound_statement /\
  audit_trie_get_source_work_bound_statement /\ audit_trie_update_source_work_bound_statement /\
  audit_trie_get_trace_adequate_statement /\ audit_trie_update_trace_adequate_statement /\
  audit_map_code_get_run_correct_statement /\ audit_queue_family_statement /\
  audit_queue_recorded_full_push_statement /\ audit_queue_recorded_full_pop_fuel_statement /\
  audit_queue_recorded_full_pop_statement.

(** This adapter is only for genuinely external encoder bodies. *)
Record audit_queue_external_encoder_adapter {K B} (E : encoding K)
    (encoder : audit_queue_encoder_model K B) (weight : B -> nat)
    (source : K -> positive -> list B -> nat -> Prop) (budget : K -> nat) : Prop := {
  audit_queue_external_encoder_value : audit_queue_encoder_erases E encoder;
  audit_queue_external_encoder_source : forall key code body,
    encoder key = (code, body) ->
    source key code body (fold_right (fun item n => weight item + n) 0 body) /\
    fold_right (fun item n => weight item + n) 0 body <= budget key
}.

Definition audit_queue_recorded_encoder_budget_event {K B} (budget : K -> nat)
    (recorded : audit_queue_nested_event K (positive * list B)) : nat :=
  let '(event, (_, bodies)) := recorded in
  match event, bodies with
  | QGet key _, [_]
  | QSet key _ _, [_]
  | QRemove key _, [_]
  | QEncode key, [_] => budget key
  | _, _ => 0
  end.

Definition audit_queue_recorded_encoder_budget {K B} (budget : K -> nat)
    (events : list (audit_queue_nested_event K (positive * list B))) : nat :=
  fold_right (fun event n => audit_queue_recorded_encoder_budget_event budget event + n) 0 events.

(** Push with an external encoder preserves its result and bounds source work. *)
Definition audit_queue_external_encoder_push_statement : Prop :=
  forall K B (E : encoding K) (encoder : audit_queue_encoder_model K B) (weight : B -> nat)
    source budget priority key state,
    audit_queue_external_encoder_adapter E encoder weight source budget ->
    let '(result, events) := audit_queue_push_nested (audit_queue_capture_encoder encoder)
      priority key state in
    result = PQueue.push E priority key state /\
    audit_queue_recorded_full_source_work weight events <=
      audit_queue_full_input_budget E 1 (PQueue.pending state) (PQueue.live state) [key]
        [priority] +
      audit_queue_recorded_encoder_budget budget events.

(** Pop with an external encoder preserves its result and bounds source work. *)
Definition audit_queue_external_encoder_pop_statement : Prop :=
  forall K B (E : encoding K) (encoder : audit_queue_encoder_model K B) (weight : B -> nat)
    source budget state,
    audit_queue_external_encoder_adapter E encoder weight source budget ->
    let '(result, events) := audit_queue_pop_nested (audit_queue_capture_encoder encoder) state in
    result = PQueue.pop E state /\
    audit_queue_recorded_full_source_work weight events <=
      audit_queue_full_input_budget E (PQueue.pending_count state) (PQueue.pending state)
        (PQueue.live state) [] [] +
      audit_queue_recorded_encoder_budget budget events.

(** Fuelled pop with an external encoder preserves its result and bounds source work. *)
Definition audit_queue_external_encoder_pop_fuel_statement : Prop :=
  forall K B (E : encoding K) (encoder : audit_queue_encoder_model K B) (weight : B -> nat)
    source budget fuel heap live count,
    audit_queue_external_encoder_adapter E encoder weight source budget ->
    let '(result, events) := audit_queue_recorded_pop_fuel encoder fuel heap live count in
    result = PQueue.pop_fuel E fuel heap live count /\
    audit_queue_recorded_full_source_work weight events <=
      audit_queue_full_input_budget E fuel heap live [] [] + audit_queue_recorded_encoder_budget
        budget events.
