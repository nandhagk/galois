(** * Symbolic clients of primitive firing costs

    Literal collection exposes its price without unfolding the source firing implementation.
    For example, negative literals count in the supplied inventory even though collection omits them.
    Builds on: DatalogFire and its public positive-atom collection cost. *)

From Stdlib Require Import List NArith PArith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding.
From Galois.Lattice Require Import LatticeSet.
From Galois.Datalog Require Import DatalogSyntax DatalogRelation DatalogFire DatalogCost.
Import List.ListNotations.

Example symbolic_literal_inventory {P} (ls : list (literal P)) :
  Cost.ticks (positive_atoms_c ls) = N.of_nat (length ls).
Proof.
  apply positive_atoms_cost.
Qed.

Example mixed_literal_inventory {P} (a : atom P) :
  Cost.ticks (positive_atoms_c [LNeg a; LPos a; LNeg a]) = 3%N.
Proof.
  rewrite positive_atoms_cost; reflexivity.
Qed.

Example empty_literal_inventory {P} :
  Cost.ticks (@positive_atoms_c P []) = 0%N.
Proof.
  rewrite positive_atoms_cost; reflexivity.
Qed.

Example symbolic_term_price b t c v :
  (N.pos (Pos.size c) <= v)%N ->
  (Cost.ticks (bind_term_c b t c) <= 1 + N.of_nat (length b) + v)%N.
Proof.
  apply bind_term_cost.
Qed.

Example symbolic_instantiation_price b ts :
  (Cost.ticks (instantiate_c b ts) <=
    N.of_nat (length ts) * (1 + N.of_nat (length b)))%N.
Proof.
  apply instantiate_cost.
Qed.

Example nonempty_matching_price :
  (Cost.ticks (bind_terms_c [TVar 0] [2%positive] []) <= (1 + 1) * (2 + 1 + 2))%N.
Proof.
  apply (bind_terms_cost [TVar 0] [2%positive] [] 1 2); [reflexivity |].
  intros c [<- | Hbad]; [vm_compute; discriminate | contradiction].
Qed.

Definition primitive_negative_rule : rule bool :=
  Rule (Atom true [TConst 2%positive]) [LNeg (Atom false [TConst 2%positive])].

Definition primitive_negative_env (_ : bool) :=
  Cost.lift (fun _ => 17%N) (fun _ => set_empty tuple_encoding) tt.

Example nonunit_negative_price :
  (Cost.ticks (negative_ok_c primitive_negative_rule primitive_negative_env []) <=
    1 * (3 + 1 * (1 + 0) + 17 + 200 + 200))%N.
Proof.
  apply (negative_cost primitive_negative_rule primitive_negative_env [] 1 0 17 200 200);
    [reflexivity |].
  intros atom [Heq | Hbad]; [injection Heq as <- | contradiction].
  repeat split; vm_compute; first [reflexivity | discriminate].
Qed.
