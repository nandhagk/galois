(** * Costed preparation agreement

    The public preparation value is the value of its single costed implementation.
    For example, callback charges do not change a prepared graph's record values.
    Builds on: GraphPrepared. *)

From Stdlib Require Import List NArith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseIntern.
From Galois.Graph Require Import GraphModel GraphPrepared.
Import List.ListNotations Cost.Notations.

Module PreparedCost.
Local Open Scope N_scope.

(** Cost erasure returns the existing public preparation on its full arbitrary-input domain. *)
Theorem prepare_c_value {V E} enc (g : Graph.t V E) :
  Cost.value (Prepared.prepare_c enc g) = Prepared.prepare enc g.
Proof.
  reflexivity.
Qed.

(** Present mapping retains the traversal tick, callback overhead and complete callee charge. *)
Theorem present_cost {A B} (f : A -> Cost.t (option B)) xs :
  Cost.ticks (Prepared.present_c f xs) =
    fold_right (fun x n => 2 + Cost.ticks (f x) + n) 0 xs.
Proof.
  induction xs as [|x rest IH]; [reflexivity|].
  cbn [Prepared.present_c fold_right]. autorewrite with galois_cost.
  rewrite IH. lia.
Qed.

(** Erasing reverse costs preserves the existing full-domain reversed prepared view. *)
Theorem reverse_c_value {V E} (p : Prepared.t V E) exits :
  Cost.value (Prepared.reverse_c p exits) = Prepared.reverse p exits.
Proof.
  reflexivity.
Qed.

(** Reversal pays every exit occurrence and its actual inverse lookup, including unknown IDs. *)
Theorem reverse_cost {V E} (p : Prepared.t V E) exits :
  Cost.ticks (Prepared.reverse_c p exits) =
    fold_right (fun i n => 2 + Cost.ticks (Prepared.name_of_c p i) + n) 0 exits.
Proof.
  rewrite Prepared.reverse_c_equation. autorewrite with galois_cost.
  rewrite present_cost. lia.
Qed.

(** A supplied width bound gives a linear bound without restricting duplicates or unknown exits. *)
Theorem reverse_cost_bound {V E} (p : Prepared.t V E) exits w :
  (forall i, In i exits -> key_bits positive_encoding i <= w) ->
    Cost.ticks (Prepared.reverse_c p exits) <= N.of_nat (length exits) * (3 + 2 * w).
Proof.
  intro Hwidth. rewrite reverse_cost.
  induction exits as [|i rest IH]; [cbn; lia|].
  cbn [fold_right length]. rewrite Nat2N.inj_succ.
  assert (Htail : forall j, In j rest -> key_bits positive_encoding j <= w).
  { intros j Hj. apply Hwidth. now right. }
  specialize (IH Htail).
  pose proof (Hwidth i (or_introl eq_refl)) as Hi.
  pose proof (encode_cost_bound positive_encoding_cost_laws i) as Hencode.
  unfold Prepared.name_of_c at 1. rewrite Intern.key_of_cost, Map.get_cost.
  fold (key_bits positive_encoding i). nia.
Qed.

End PreparedCost.
