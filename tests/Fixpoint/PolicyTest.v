(** * Widening policy observations

    Boolean policies exercise covered contributions, unheaded joins and delayed heads.
    For example, a head with zero delay widens on its first strict contribution.
    Builds on: PolicyCode, PolicySig and Trie. *)

From Stdlib Require Import Bool NArith PArith.
From Galois.Base Require Import Trie.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import PolicySig Policy.

Module PolicyBool <: WLATTICE_OPS.
  Definition t := bool.
  Definition leb := implb.
  Definition bot := false.
  Definition is_bot := negb.
  Definition join := orb.
  Definition wparam := unit.
  Definition widen (_ : unit) := orb.
  Definition narrow := andb.
End PolicyBool.

Module P := PolicyCode PolicyBool.

Definition unheaded : policy unit :=
  Policy unit PTrieCode.empty PTrieCode.empty tt 0.

Definition delayed : policy unit :=
  Policy unit PTrieCode.empty
    (PTrieCode.set 1%positive (HeadCfg 1%N 0) PTrieCode.empty) tt 0.

(** A covered contribution leaves the value and counter unchanged. *)
Example covered_keeps_counter : P.update delayed 1%positive 2%N true false = (true, 2%N).
Proof.
  vm_compute; reflexivity.
Qed.

(** An unheaded strict contribution joins without spending a counter. *)
Example unheaded_joins : P.update unheaded 1%positive 0%N false true = (true, 0%N).
Proof.
  vm_compute; reflexivity.
Qed.

(** The first strict contribution at a delayed head spends one counter. *)
Example delayed_head_joins : P.update delayed 1%positive 0%N false true = (true, 1%N).
Proof.
  vm_compute; reflexivity.
Qed.
