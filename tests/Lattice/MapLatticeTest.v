(** * Map lattice fixtures

    These examples check a sparse map with a bottom default.
    For example, joining two singleton maps keeps both bindings.
    Builds on: MapLattice, Map, Key and Simple.

    Groups:
    - [OrderTests] The order of maps with a bottom default.
    - [JoinTests] Joins of singleton maps, and joins of a map with itself.
    - [WideningTests] Widening and narrowing of maps.
    - [SetterTests] The default of a map at keys that were set or not set.
    - [LiftTests] The lifted environment with a fresh bottom.
    - [BoundTests] The time bounds of inclusion, join and the bottom test. *)

From Stdlib Require Import List NArith.
From Galois.Base Require Import Key Map.
From Galois.Lattice Require Import MapLattice Simple WithBot JoinWidening.
Import List.ListNotations.

(** * Fixtures *)

(** Positive-keyed maps built by the trie map functor. *)
Module PosMap := TrieMapCode PosKeyCode.

(** The lattice of environments, that is maps from positive keys to booleans. *)
Module Env := MapLatticeCode PosKeyCode PosMap BoolLatCode.

(** The widening adapter of the environment lattice. *)
Module EnvWide := JoinWideningCode Env.

(** The environment lattice with a fresh bottom added. *)
Module LiftedEnv := WithBotCode Env.

(** The timed map and environment, for the time bounds. *)
Module TimedPosMap := TrieMapT PosKeyT.
Module TimedEnv := MapLatticeT PosKeyT TimedPosMap BoolLatT.

(** The empty map. *)
Definition e0 : PosMap.t bool := PosMap.empty.

(** The map that binds key 1 to true. *)
Definition e1 := PosMap.set 1%positive true e0.

(** The map that binds key 2 to true. *)
Definition e2 := PosMap.set 2%positive true e0.

(** * Order *)

Module OrderTests.

  (** The empty map is below the map of key 1. *)
  Example empty_map_below_singleton : Env.leb e0 e1 = true.
  Proof. vm_compute. reflexivity. Qed.

  (** The map of key 1 is not below the map of key 2. *)
  Example singleton_not_below_other_singleton : Env.leb e1 e2 = false.
  Proof. vm_compute. reflexivity. Qed.

  (** A map compared with itself, after a repeated set, is below itself. *)
  Example constructed_bottom_default_comparison_reflexive :
    let m := PosMap.set 1%positive true (PosMap.set 1%positive false PosMap.empty) in
    Env.leb m m = true.
  Proof. vm_compute. reflexivity. Qed.

End OrderTests.

(** * Join *)

Module JoinTests.

  (** Joining two singleton maps keeps both bindings, the later one first. *)
  Example join_keeps_both_bindings :
    PosMap.elements (Env.join e1 e2) = [(2%positive, true); (1%positive, true)].
  Proof. vm_compute. reflexivity. Qed.

  (** Joining a singleton map with itself keeps its one binding. *)
  Example singleton_self_join : PosMap.elements (Env.join e1 e1) = [(1%positive, true)].
  Proof.
    vm_compute. reflexivity.
  Qed.

End JoinTests.

(** * Widening *)

Module WideningTests.

  (** Widening two singleton maps keeps both bindings. *)
  Example widen_keeps_both_bindings :
    PosMap.elements (EnvWide.widen tt e1 e2) = [(2%positive, true); (1%positive, true)].
  Proof. vm_compute. reflexivity. Qed.

  (** Narrowing two singleton maps keeps the binding of the first. *)
  Example narrow_keeps_first_binding :
    PosMap.elements (EnvWide.narrow e1 e2) = [(1%positive, true)].
  Proof. vm_compute. reflexivity. Qed.

End WideningTests.

(** * Setters *)

Module SetterTests.

  (** A key set to true has the default true of a set key. *)
  Example set_key_has_true_default :
    Env.default (PosMap.get 1%positive (PosMap.set 1%positive true e0)) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A key that was not set has the bottom default false. *)
  Example unset_key_has_false_default :
    Env.default (PosMap.get 2%positive (PosMap.set 1%positive true e0)) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

End SetterTests.

(** * Lifted *)

Module LiftTests.

  (** A reached empty environment is above the fresh bottom. *)
  Example lifted_environment_reached_empty_is_above_fresh_bottom :
    LiftedEnv.leb (Some e0) None = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

End LiftTests.

(** * Bounds *)

Module BoundTests.

  (** Comparison charges the sum of the public sizes, including missing-key defaults. *)
  Example map_inclusion_bigO_bound :
    (TimedEnv.T_leb e1 e2 <=
      TimedEnv.c_lat * (N.of_nat (TimedEnv.size e1 + TimedEnv.size e2) + 1))%N.
  Proof.
    apply N.leb_le. vm_compute. reflexivity.
  Qed.

  (** Joining disjoint singletons fits the same two-map size measure. *)
  Example map_join_bigO_bound :
    (TimedEnv.T_join e1 e2 <=
      TimedEnv.c_lat * (N.of_nat (TimedEnv.size e1 + TimedEnv.size e2) + 1))%N.
  Proof.
    apply N.leb_le. vm_compute. reflexivity.
  Qed.

  (** The bottom test fits the size of one nonempty map. *)
  Example map_bottom_bigO_bound :
    (TimedEnv.T_is_bot e1 <= TimedEnv.c_lat * (N.of_nat (TimedEnv.size e1) + 1))%N.
  Proof.
    apply N.leb_le. vm_compute. reflexivity.
  Qed.

End BoundTests.
