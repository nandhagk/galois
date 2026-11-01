(** * G4 collections semantics

    This declaration-only pilot isolates G4 semantic contracts.
    For example, it keeps the historical observation in its original statement.
    Builds on: Galois.Collections. *)

From Stdlib Require Import List NArith PArith Permutation Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsDenseSet CollectionsUnionFind.
Import List.ListNotations.

Record prepared_key (K : Type) : Type := PreparedKey {
  key_value : K;
  key_code : positive
}.

Arguments PreparedKey {K}.
Arguments key_value {K}.
Arguments key_code {K}.

Definition key_valid {K} (E : encoding K) (p : prepared_key K) : Prop :=
  key_code p = encode E (key_value p).

Definition prepare_key {K} (E : encoding K) (k : K) : prepared_key K :=
  PreparedKey k (encode E k).

(** Preparing a key stores its original value together with its encoding. *)
Definition prepare_key_valid_statement : Prop :=
  forall K (E : encoding K) k, key_valid E (prepare_key E k).

Definition prepared_lookup {K V} (p : prepared_key K) (m : Map.t K V) : option V :=
  Map.code_get (key_code p) m.

Definition prepared_update {K V} (p : prepared_key K) (v : V) (m : Map.t K V) : Map.t K V :=
  Trie.set (key_code p) (key_value p, v) m.

Definition prepared_remove {K V} (p : prepared_key K) (m : Map.t K V) : Map.t K V :=
  Trie.remove (key_code p) m.

(** A valid prepared key gives the same lookup as the original key. *)
Definition prepared_key_refinement_statement : Prop :=
  forall K V (E : encoding K) (p : prepared_key K) (m : Map.t K V),
    key_valid E p -> prepared_lookup p m = Map.get E (key_value p) m.

(** Equal codes of valid prepared keys identify equal original keys. *)
Definition prepared_key_injection_statement : Prop :=
  forall K (E : encoding K) (p q : prepared_key K),
    key_valid E p -> key_valid E q -> key_code p = key_code q -> key_value p = key_value q.

(** Updates and removals through a valid prepared key agree with the original map operations. *)
Definition prepared_key_update_statement : Prop :=
  forall K V (E : encoding K) (p : prepared_key K) (v : V) (m : Map.t K V),
    key_valid E p -> prepared_update p v m = Map.set E (key_value p) v m /\
    prepared_remove p m = Map.remove E (key_value p) m.

(** Equal prepared pair codes identify equal pairs. *)
Definition prepared_pair_statement : Prop :=
  forall A B (EA : encoding A) (EB : encoding B) (x y : A * B),
    key_code (prepare_key (pair_encoding EA EB) x) =
      key_code (prepare_key (pair_encoding EA EB) y) -> x = y.

Definition prepared_key_bits {K} (p : prepared_key K) : nat := Pos.size_nat (key_code p).

(** Equal prepared list codes identify equal lists. *)
Definition prepared_list_injection_statement : Prop :=
  forall A (EA : encoding A) (xs ys : list A),
    key_code (prepare_key (list_encoding EA) xs) = key_code (prepare_key (list_encoding EA) ys)
      -> xs = ys.

(** A prepared pair code has one delimiter bit plus twice the component code widths. *)
Definition prepared_pair_bits_statement : Prop :=
  forall A B (EA : encoding A) (EB : encoding B) (a : A) (b : B),
    Pos.size_nat (key_code (prepare_key (pair_encoding EA EB) (a,b))) =
      S (2 * Pos.size_nat (encode EA a) + 2 * Pos.size_nat (encode EB b)).

(** A prepared list code has one delimiter bit plus twice the sum of element code widths. *)
Definition prepared_list_bits_statement : Prop :=
  forall A (EA : encoding A) (xs : list A),
    Pos.size_nat (key_code (prepare_key (list_encoding EA) xs)) =
      S (2 * fold_right (fun a bits => Pos.size_nat (encode EA a) + bits) 0 xs).

(** Declarations from the DenseProbe candidate. *)
Definition slot_map (V : Type) := Map.t N V.

Definition slot_valid {K V} (E : encoding K) (u : dense_universe K) (m : slot_map V) : Prop :=
  dense_universe_wf E u /\ Map.wf N_encoding m /\
  forall i v, Map.get N_encoding i m = Some v -> (i < dense_length u)%N.

Definition prepare_slot {K} (E : encoding K) (u : dense_universe K) (k : K) : option N :=
  Map.get E k (dense_index u).

Definition slot_read {V} (m : slot_map V) (i : N) : option V := Map.get N_encoding i m.

Definition slot_lookup {K V} (E : encoding K) (u : dense_universe K)
    (m : slot_map V) (k : K) : option V :=
  match Map.get E k (dense_index u) with
  | Some i => Map.get N_encoding i m
  | None => None
  end.

Definition slot_update {K V} (E : encoding K) (u : dense_universe K)
    (m : slot_map V) (k : K) (v : V) : option (slot_map V) :=
  match Map.get E k (dense_index u) with
  | Some i => Some (Map.set N_encoding i v m)
  | None => None
  end.

Definition slot_elements {K V} (E : encoding K) (u : dense_universe K)
    (m : slot_map V) : list (K * V) :=
  flat_map (fun k => match slot_lookup E u m k with
    | Some v => [(k, v)]
    | None => []
    end) (dense_keys u).

Definition slot_to_map {K V} (E : encoding K) (u : dense_universe K)
    (m : slot_map V) : Map.t K V := Map.of_list E (slot_elements E u m).

Definition dense_map_refines {K V} (E : encoding K) (u : dense_universe K)
    (m : slot_map V) (abstract : Map.t K V) : Prop :=
  slot_valid E u m /\ Map.wf E abstract /\
  forall k, slot_lookup E u m k = Map.get E k abstract.

Definition slot_of_map {K V} (E : encoding K) (u : dense_universe K)
    (abstract : Map.t K V) : slot_map V :=
  fold_left (fun result k =>
    match Map.get E k abstract, prepare_slot E u k with
    | Some value, Some i => Map.set N_encoding i value result
    | _, _ => result
    end) (dense_keys u) Map.empty.

(** A successful valid slot update preserves validity, writes the key and leaves other keys
  unchanged. *)
Definition slot_update_statement : Prop :=
  forall K V (E : encoding K) (u : dense_universe K) (m m' : slot_map V) k v,
    slot_valid E u m -> slot_update E u m k v = Some m' ->
    slot_valid E u m' /\ slot_lookup E u m' k = Some v /\
    forall x, x <> k -> slot_lookup E u m' x = slot_lookup E u m x.

(** Elements of a valid slot map describe exactly its lookups without duplicate keys. *)
Definition slot_elements_statement : Prop :=
  forall K V (E : encoding K) (u : dense_universe K) (m : slot_map V),
    slot_valid E u m ->
    (forall k v, In (k, v) (slot_elements E u m) <-> slot_lookup E u m k = Some v) /\
    NoDup (map fst (slot_elements E u m)).

(** Valid slot maps with identical key lookups are equal. *)
Definition slot_canonical_statement : Prop :=
  forall K V (E : encoding K) (u : dense_universe K) (a b : slot_map V),
    slot_valid E u a -> slot_valid E u b ->
    (forall k, slot_lookup E u a k = slot_lookup E u b k) -> a = b.

(** Converting a valid slot map to a map yields a refined abstract map. *)
Definition slot_to_map_statement : Prop :=
  forall K V (E : encoding K) (u : dense_universe K) (m : slot_map V),
    slot_valid E u m -> dense_map_refines E u m (slot_to_map E u m).

(** Converting an abstract map creates valid slots and preserves lookups inside the universe. *)
Definition slot_of_map_statement : Prop :=
  forall K V (E : encoding K) (u : dense_universe K) (abstract : Map.t K V),
    dense_universe_wf E u -> slot_valid E u (slot_of_map E u abstract) /\
    forall k, slot_lookup E u (slot_of_map E u abstract) k =
      match prepare_slot E u k with
      | Some _ => Map.get E k abstract
      | None => None
      end.

(** A prepared slot is in range and its read agrees with lookup by key. *)
Definition slot_prepare_statement : Prop :=
  forall K V (E : encoding K) (u : dense_universe K) (m : slot_map V) k i,
    slot_valid E u m -> prepare_slot E u k = Some i ->
    (i < dense_length u)%N /\ slot_read m i = slot_lookup E u m k.

(** An unprepared key has no slot lookup and cannot be updated. *)
Definition slot_outside_statement : Prop :=
  forall K V (E : encoding K) (u : dense_universe K) (m : slot_map V) k v,
    prepare_slot E u k = None -> slot_lookup E u m k = None /\ slot_update E u m k v = None.

(** The empty slot map is valid for a well-formed universe. *)
Definition slot_empty_statement : Prop :=
  forall K V (E : encoding K) (u : dense_universe K),
    dense_universe_wf E u -> slot_valid E u (@Map.empty N V).

(** Every key in a valid universe admits a successful slot update. *)
Definition slot_present_update_statement : Prop :=
  forall K V (E : encoding K) (u : dense_universe K) (m : slot_map V) k v,
    slot_valid E u m -> In k (dense_keys u) ->
    exists m', slot_update E u m k v = Some m'.

Definition prepare_slots {K} (E : encoding K) (u : dense_universe K) (keys : list K) :
    list (option N) := map (prepare_slot E u) keys.

Definition read_slots {V} (m : slot_map V) (slots : list (option N)) : list (option V) :=
  map (fun slot => match slot with
  | Some i => slot_read m i
  | None => None
  end) slots.

(** Batch reads after preparation agree with the list of key lookups. *)
Definition slot_batch_refinement_statement : Prop :=
  forall K V (E : encoding K) (u : dense_universe K) (m : slot_map V) keys,
    read_slots m (prepare_slots E u keys) = map (slot_lookup E u m) keys.

(** Declarations from the DenseUpdateProbe candidate. *)
Definition slot_remove {K V} (E : encoding K) (u : dense_universe K)
    (m : slot_map V) (k : K) : option (slot_map V) :=
  match prepare_slot E u k with
  | Some i => Some (Map.remove N_encoding i m)
  | None => None
  end.

(** A successful slot update refines the corresponding abstract map update. *)
Definition slot_update_refines_statement : Prop :=
  forall K V (E : encoding K) (u : dense_universe K) (m m' : slot_map V)
    (abstract : Map.t K V) k value,
    dense_map_refines E u m abstract -> slot_update E u m k value = Some m' ->
    dense_map_refines E u m' (Map.set E k value abstract).

(** A successful slot removal refines the corresponding abstract map removal. *)
Definition slot_remove_refines_statement : Prop :=
  forall K V (E : encoding K) (u : dense_universe K) (m m' : slot_map V)
    (abstract : Map.t K V) k,
    dense_map_refines E u m abstract -> slot_remove E u m k = Some m' ->
    dense_map_refines E u m' (Map.remove E k abstract).

(** Successful slot removal preserves validity and other keys while clearing the removed key. *)
Definition slot_remove_frame_statement : Prop :=
  forall K V (E : encoding K) (u : dense_universe K) (m m' : slot_map V) k,
    slot_valid E u m -> slot_remove E u m k = Some m' ->
    slot_valid E u m' /\ slot_lookup E u m' k = None /\
    forall other, other <> k -> slot_lookup E u m' other = slot_lookup E u m other.

(** Removal fails for a key with no prepared slot. *)
Definition slot_remove_outside_statement : Prop :=
  forall K V (E : encoding K) (u : dense_universe K) (m : slot_map V) k,
    prepare_slot E u k = None -> slot_remove E u m k = None.

(** Slot elements enumerate the abstract map lookups without duplicate keys. *)
Definition slot_elements_refines_statement : Prop :=
  forall K V (E : encoding K) (u : dense_universe K) (m : slot_map V) (abstract : Map.t K V),
    dense_map_refines E u m abstract ->
    (forall k value, In (k,value) (slot_elements E u m) <-> Map.get E k abstract = Some value) /\
    NoDup (map fst (slot_elements E u m)).

(** Declarations from the DenseTokenProbe candidate. *)
Record dense_slot_token {K} (E : encoding K) (u : dense_universe K) : Type := DenseSlotToken {
  dense_token_key : K;
  dense_token_index : N
}.
Arguments DenseSlotToken {K E u}.
Arguments dense_token_key {K E u}.
Arguments dense_token_index {K E u}.

Definition dense_token_valid {K} (E : encoding K) (u : dense_universe K)
    (token : dense_slot_token E u) : Prop :=
  prepare_slot E u (dense_token_key token) = Some (dense_token_index token).

Definition dense_token_prepare {K} (E : encoding K) (u : dense_universe K) (key : K) :
    option (dense_slot_token E u) :=
  match prepare_slot E u key with
  | Some index => Some (DenseSlotToken key index)
  | None => None
  end.

Definition dense_token_read {K V} (E : encoding K) (u : dense_universe K)
    (token : dense_slot_token E u) (m : slot_map V) : option V := slot_read m
      (dense_token_index token).

(** A successfully prepared token is valid and retains its original key. *)
Definition dense_token_prepare_statement : Prop :=
  forall K (E : encoding K) (u : dense_universe K) key token,
    dense_token_prepare E u key = Some token ->
    dense_token_valid E u token /\ dense_token_key token = key.

(** Reading a valid token agrees with lookup of its key. *)
Definition dense_token_read_statement : Prop :=
  forall K V (E : encoding K) (u : dense_universe K) (token : dense_slot_token E u) (m :
    slot_map V),
    dense_token_valid E u token -> dense_token_read E u token m = slot_lookup E u m
      (dense_token_key token).

(** Token preparation fails exactly when ordinary slot preparation fails. *)
Definition dense_token_scope_statement : Prop :=
  forall K (E : encoding K) (u : dense_universe K) key,
    dense_token_prepare E u key = None <-> prepare_slot E u key = None.
