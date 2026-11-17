(** * Dense interning fixtures

    These fixtures cover reuse, reverse lookup and empty tables.
    For example, [2; 1; 2] uses exactly two IDs.
    Builds on: Intern, Map and Key.

    Groups:
    - [LookupTests] Finding an identifier from a key, and a key from an identifier.
    - [SizeTests] The number of keys in a table and the size bounds.
    - [FrontierTests] The next identifier to allocate.
    - [GroupTests] Grouping of values by key, in input order.
    - [AgreementTests] The lookups agree with the underlying maps. *)

From Stdlib Require Import List NArith.
From Galois.Base Require Import Key Map Intern Trie.
Import List.ListNotations.

(** * Fixtures *)

(** The nat-keyed trie map used under the intern table. *)
Module NatMap := TrieMapCode NatKeyCode.

(** The nat-keyed intern table over that map. *)
Module NatIntern := InternCode NatKeyCode NatMap.

(** Interns the keys of a list in order, starting from the empty table. *)
Definition intern_list xs :=
  fold_left (fun s k => snd (NatIntern.intern k s)) xs NatIntern.empty.

(** The table after interning 2, 1 and 2 in that order. *)
Definition interned := intern_list [2; 1; 2].

(** * Lookup *)

Module LookupTests.

  (** The first key interned gets identifier 1. *)
  Example first_key_gets_one : NatIntern.find 2 interned = Some 1%positive.
  Proof. vm_compute. reflexivity. Qed.

  (** An identifier reads back the key that it names. *)
  Example name_maps_identifier_to_key : NatIntern.name 2%positive interned = Some 1.
  Proof. vm_compute. reflexivity. Qed.

  (** A key that was never interned has no identifier. *)
  Example absent_key_has_no_identifier : NatIntern.find 3 interned = None.
  Proof. vm_compute. reflexivity. Qed.

  (** The empty table names no identifier. *)
  Example empty_table_names_nothing : NatIntern.name 1%positive NatIntern.empty = None.
  Proof. vm_compute. reflexivity. Qed.

  (** A name read back from an identifier finds that same identifier. *)
  Example name_round_trips_through_find :
    match NatIntern.name 2%positive interned with
    | Some k => NatIntern.find k interned
    | None => None
    end = Some 2%positive.
  Proof. vm_compute. reflexivity. Qed.

  (** An identifier that was never allocated has no name. *)
  Example unallocated_identifier_has_no_name :
    NatIntern.name 3%positive interned = None.
  Proof. vm_compute. reflexivity. Qed.

  (** The first key of a list gets identifier 1. *)
  Example first_listed_key_gets_one :
    NatIntern.find 9 (intern_list [9; 4; 7]) = Some 1%positive.
  Proof. vm_compute. reflexivity. Qed.

  (** The last key of a list gets the last identifier. *)
  Example last_listed_key_gets_last_identifier :
    NatIntern.find 7 (intern_list [9; 4; 7]) = Some 3%positive.
  Proof. vm_compute. reflexivity. Qed.

  (** Any key finds nothing in a table built from an empty list. *)
  Example empty_list_finds_nothing :
    NatIntern.find 9 (intern_list []) = None.
  Proof. vm_compute. reflexivity. Qed.

End LookupTests.

(** * Size *)

Module SizeTests.

  (** Interning a repeated key does not add a second identifier. *)
  Example size_counts_distinct_keys : NatIntern.size interned = 2%N.
  Proof. vm_compute. reflexivity. Qed.

  (** The table holds at least two keys. *)
  Example size_is_at_least_two : N.leb 2 (NatIntern.size interned) = true.
  Proof. vm_compute. reflexivity. Qed.

  (** The table holds fewer than three keys. *)
  Example size_is_below_three : N.leb 3 (NatIntern.size interned) = false.
  Proof. vm_compute. reflexivity. Qed.

  (** The table holds fewer than four keys. *)
  Example size_is_below_four : N.leb 4 (NatIntern.size interned) = false.
  Proof. vm_compute. reflexivity. Qed.

  (** The empty table has size zero. *)
  Example empty_table_has_size_zero :
    N.to_nat (NatIntern.size NatIntern.empty) = 0.
  Proof. vm_compute. reflexivity. Qed.

End SizeTests.

(** * Frontier *)

Module FrontierTests.

  (** The empty table allocates identifier 1 next. *)
  Example empty_frontier_is_one :
    Pos.to_nat (intern_next NatIntern.empty) = 1.
  Proof. vm_compute. reflexivity. Qed.

  (** After two distinct keys the next identifier is 3. *)
  Example next_identifier_after_two_keys_is_three :
    Pos.to_nat (intern_next interned) = 3.
  Proof. vm_compute. reflexivity. Qed.

  (** The size plus one equals the next identifier after two keys. *)
  Example size_successor_is_three :
    S (N.to_nat (NatIntern.size interned)) = 3.
  Proof. vm_compute. reflexivity. Qed.

End FrontierTests.

(** * Group *)

Module GroupTests.

  (** Grouped values keep their input order within each key. *)
  Example group_keeps_input_order :
    find_group NatKeyCode.encode 2
      (group_by NatKeyCode.encode fst [(2, 10); (1, 11); (2, 12); (1, 13)]) =
    [(2, 10); (2, 12)].
  Proof.
    vm_compute. reflexivity.
  Qed.

End GroupTests.

(** * Agreement *)

Module AgreementTests.

  (** Finding a key agrees with its entry in the forward map. *)
  Example find_agrees_with_forward_map :
    NatIntern.find 1 interned = NatMap.get 1 (intern_forward interned).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Naming an identifier agrees with its entry in the inverse map. *)
  Example name_agrees_with_inverse_map :
    NatIntern.name 2%positive interned =
      PTrieCode.get 2%positive (Intern.intern_inverse interned).
  Proof.
    vm_compute. reflexivity.
  Qed.

End AgreementTests.

(* BaseInternTest.intern_ticks retires with Cost.ticks. The size observations use
   N.to_nat where the old size was nat. intern_symbolic_size_client is replaced
   by the public find_range, dense and intern_new laws. intern_symbolic_index_client,
   intern_fresh_last_client and intern_first_allocation_client use the old of_list
   laws. List construction now composes intern through fold_left, as above. *)
