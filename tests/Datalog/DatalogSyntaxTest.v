(** * Datalog syntax and relation examples

    Grounding and valid relation operations compute on small tuples.
    For example, grounding a repeated variable repeats its assigned constant.
    Builds on: DatalogSyntax, DatalogRelation and LatticeSet. *)

From Stdlib Require Import List PArith PeanoNat.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseSet.
From Galois.Lattice Require Import LatticeCore LatticeSet.
From Galois.Datalog Require Import DatalogSyntax DatalogStratify DatalogRelation.
Import List.ListNotations.

Example ground_repeated_variable :
  ground (fun _ => 2%positive)
    (Atom true [TVar 0; TConst 1%positive; TVar 0]) =
  (true, [2%positive; 1%positive; 2%positive]).
Proof.
  vm_compute. reflexivity.
Qed.

Definition one_row := set_of_list tuple_encoding [[1%positive; 2%positive]].
Definition another_row := set_of_list tuple_encoding [[2%positive; 1%positive]].

Example relation_union_membership :
  (FinSet.mem tuple_encoding [1%positive; 2%positive]
      (set_raw (join relation_lattice one_row another_row)),
   FinSet.mem tuple_encoding [2%positive; 1%positive]
      (set_raw (join relation_lattice one_row another_row)),
   FinSet.mem tuple_encoding [1%positive; 1%positive]
      (set_raw (join relation_lattice one_row another_row))) = (true, true, false).
Proof.
  vm_compute. reflexivity.
Qed.

Example unsafe_head : ~ safe_rule (Rule (Atom 0 [TVar 0]) []).
Proof.
  intro Hsafe; destruct (Hsafe 0 (or_introl (or_introl eq_refl))) as [a [Hbad _]].
  contradiction.
Qed.

Example unsafe_negation :
  ~ safe_rule (Rule (Atom 0 [TConst 2%positive]) [LNeg (Atom 1 [TVar 0])]).
Proof.
  intro Hsafe.
  assert (Hnegative : exists a, In (LNeg a) [LNeg (Atom 1 [TVar 0])] /\ In 0 (atom_vars a)).
  { exists (Atom 1 [TVar 0]); cbn; auto. }
  destruct (Hsafe 0 (or_intror Hnegative)) as [a [Hbad _]].
  cbn in Hbad; destruct Hbad as [Hbad | Hbad]; [discriminate | contradiction].
Qed.

Example stratify_empty :
  option_map (fun st => (level st 42, count st))
    (stratify (Program nat_encoding (fun _ => Cost.ret 0) [])) = Some (0, 1).
Proof.
  vm_compute; reflexivity.
Qed.

Example universe_nullary_without_constants :
  universe (Program nat_encoding (fun _ => Cost.ret 0) [Rule (Atom 0 []) []]) [] = [[]].
Proof.
  vm_compute; reflexivity.
Qed.
