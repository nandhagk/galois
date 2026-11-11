(** * Tabulator primitive and numeric-fuel costs

    Numeric fuel construction charges the supplied height and the whole prepared key inventory.
    For example, an inventory containing unreachable facts still contributes to preparation.
    Builds on: FrameworkTabulate, LatticeHeight and the public finite-container cost equations. *)

From Stdlib Require Import List NArith Lia.
From Galois.Cost Require Import CostMonad CostList CostBound.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Lattice Require Import LatticeCore LatticeHeight.
From Galois.Framework Require Import FrameworkMicro FrameworkIfds FrameworkIde FrameworkTabulate.
Import List.ListNotations Cost.Notations.

Module TabCost.

(** Unary numeric evidence is converted by a charged traversal. *)
Fixpoint binary_c (n : nat) : Cost.t N :=
  match n with
  | O => Cost.ret 0%N
  | S n => Cost.step ;; Cost.map N.succ (binary_c n)
  end.

Definition binary n := Cost.value (binary_c n).

(** Numeric conversion keeps the supplied natural's exact value. *)
Theorem binary_equation n : binary n = N.of_nat n.
Proof.
  induction n as [|n IH]; [reflexivity|].
  unfold binary in *; cbn [binary_c]; autorewrite with galois_cost.
  rewrite IH, Nat2N.inj_succ; reflexivity.
Qed.

(** Numeric conversion charges every unary constructor in the supplied evidence. *)
Theorem binary_cost n : Cost.ticks (binary_c n) = N.of_nat n.
Proof.
  induction n as [|n IH]; [reflexivity|].
  cbn [binary_c]; autorewrite with galois_cost.
  rewrite IH, Nat2N.inj_succ; lia.
Qed.

Definition count_c {X} (xs : list X) :=
  fold_left_c (fun n _ => Cost.ret (N.succ n)) xs 0%N.

(** Counting the prepared support returns its full occurrence count. *)
Theorem count_value {X} (xs : list X) :
  Cost.value (count_c xs) = N.of_nat (length xs).
Proof.
  unfold count_c; rewrite value_fold_left_c.
  assert (Hacc : forall (ys : list X) n,
    fold_left (fun n _ => N.succ n) ys n = (n + N.of_nat (length ys))%N).
  { intro ys; induction ys as [|y ys IH]; intro n; cbn [fold_left length].
    - lia.
    - rewrite IH, Nat2N.inj_succ; lia. }
  rewrite Hacc; reflexivity.
Qed.

(** Counting charges every prepared support occurrence, including duplicates. *)
Theorem count_cost {X} (xs : list X) :
  Cost.ticks (count_c xs) = N.of_nat (length xs).
Proof.
  assert (Hacc : forall (ys : list X) n,
    Cost.ticks (fold_left_c (fun n _ => Cost.ret (N.succ n)) ys n) =
      N.of_nat (length ys)).
  { intro ys; induction ys as [|y ys IH]; intro n; [reflexivity|].
    rewrite ticks_fold_left_c_cons, Cost.ticks_ret, IH.
    cbn [length]; rewrite Nat2N.inj_succ; lia. }
  apply Hacc.
Qed.

(** Numeric construction pays for the supplied height and every inventory occurrence. *)
Definition inventory_fuel_c {X} (inventory : list X) h :=
  let* height := binary_c h in
  let* keys := count_c inventory in
  Cost.step ;;
  Cost.ret (N.succ_pos ((1 + height) * keys)).

Definition inventory_fuel {X} (inventory : list X) h :=
  Cost.value (inventory_fuel_c inventory h).

(** The constructed numeral contains one final stopping callback after the rank budget. *)
Theorem inventory_fuel_equation {X} (inventory : list X) h :
  inventory_fuel inventory h =
    N.succ_pos ((1 + N.of_nat h) * N.of_nat (length inventory)).
Proof.
  unfold inventory_fuel, inventory_fuel_c; autorewrite with galois_cost.
  rewrite count_value; fold (binary h); rewrite binary_equation; reflexivity.
Qed.

(** Numeric construction retains the height conversion, inventory traversal and final arithmetic step. *)
Theorem inventory_fuel_cost {X} (inventory : list X) h :
  Cost.ticks (inventory_fuel_c inventory h) =
    (N.of_nat h + N.of_nat (length inventory) + 1)%N.
Proof.
  unfold inventory_fuel_c; autorewrite with galois_cost.
  rewrite binary_cost, count_cost; lia.
Qed.

(** The numeric interpretation counts one initial visit and h updates per inventory occurrence. *)
Theorem inventory_fuel_numeric {X} (inventory : list X) h :
  Pos.to_nat (inventory_fuel inventory h) = S ((1 + h) * length inventory).
Proof.
  rewrite inventory_fuel_equation.
  assert (Hpos : forall p, Pos.to_nat p = N.to_nat (N.pos p)) by reflexivity.
  rewrite Hpos, N.succ_pos_spec, N2Nat.inj_succ, N2Nat.inj_mul, N2Nat.inj_add.
  rewrite !Nat2N.id; reflexivity.
Qed.

(** The proposed jump rank budget uses the same charged numeric constructor. *)
Definition rank_fuel_c {N E P D F} (p : Tab.prepared N E P D F) h :=
  inventory_fuel_c (Tab.inventory p) h.

Definition rank_fuel {N E P D F} (p : Tab.prepared N E P D F) h :=
  Cost.value (rank_fuel_c p h).

(** Fuel construction is explicit data and does not eliminate any proposition into a numeral. *)
Theorem rank_fuel_equation {N E P D F} (p : Tab.prepared N E P D F) h :
  rank_fuel p h =
    N.succ_pos ((1 + N.of_nat h) * N.of_nat (length (Tab.inventory p))).
Proof.
  apply inventory_fuel_equation.
Qed.

(** The numeric budget includes one final stopping callback after all allowed visits. *)
Theorem rank_fuel_numeric {N E P D F} (p : Tab.prepared N E P D F) h :
  Pos.to_nat (rank_fuel p h) = S ((1 + h) * length (Tab.inventory p)).
Proof.
  apply inventory_fuel_numeric.
Qed.

(** Fuel construction charges both the supplied numeric evidence and the whole key inventory. *)
Theorem rank_fuel_cost {N E P D F} (p : Tab.prepared N E P D F) h :
  Cost.ticks (rank_fuel_c p h) =
    (N.of_nat h + N.of_nat (length (Tab.inventory p)) + 1)%N.
Proof.
  apply inventory_fuel_cost.
Qed.

(** A rejected contribution makes the actual joined value strictly increase its lawful rank. *)
Theorem update_rank_progress {F} (L : lattice F) inv (H : height_on L inv) a b :
  lattice_laws L -> inv a -> inv b -> leb L b a = false ->
  (rank H a < rank H (join L a b))%nat.
Proof.
  intros HL Ha Hb Hmiss; apply join_rank_grows; try assumption.
  destruct (leb L (join L a b) a) eqn:Hjoin; [|reflexivity].
  pose proof (leb_trans HL _ _ _ (join_upper_r HL a b) Hjoin) as Hcovered.
  rewrite Hmiss in Hcovered; discriminate.
Qed.

(** Scheduling has a numeric bound retaining the full composite-key encoding cost and width. *)
Theorem schedule_cost {N E P D A F} (I : Ide.t N E P D A F) k s Ke w :
  (Cost.ticks (encode_c (Jump.enc I) k) <= Ke)%N ->
  (key_bits (Jump.enc I) k <= w)%N ->
  (Cost.ticks (Tab.schedule_c I k s) <= 2 * (1 + Ke + w))%N.
Proof.
  intros Hencode Hwidth; rewrite Tab.schedule_cost_equation.
  rewrite FinSet.mem_cost; fold (key_bits (Jump.enc I) k).
  destruct (FinSet.mem (Jump.enc I) k (Tab.pending s)).
  - lia.
  - rewrite FinSet.add_cost; fold (key_bits (Jump.enc I) k); lia.
Qed.

(** Update costs retain the actual query, callback, encoding and positive-map insertion budgets. *)
Theorem update_cost {N E P D A F} (I : Ide.t N E P D A F) k f s Kq Kl Kj Ke Kput w :
  (Cost.ticks (Jump.lookup_c I (Tab.jumps s) k) <= Kq)%N ->
  (Cost.ticks (leb_c (Micro.lat (Ide.micro I)) f
    (Jump.lookup I (Tab.jumps s) k)) <= Kl)%N ->
  (Cost.ticks (join_c (Micro.lat (Ide.micro I))
    (Jump.lookup I (Tab.jumps s) k) f) <= Kj)%N ->
  (Cost.ticks (encode_c (Jump.enc I) k) <= Ke)%N ->
  (forall (joined : F) (m : Map.t positive F),
    Cost.ticks (Map.set_c positive_encoding (encode (Jump.enc I) k) joined m) <= Kput)%N ->
  (key_bits (Jump.enc I) k <= w)%N ->
  (Cost.ticks (Tab.update_c I k f s) <= Kq + Kl + Kj + Kput + 3 * Ke + 2 * w + 5)%N.
Proof.
  intros Hq Hl Hj He Hput Hw; rewrite Tab.update_cost_equation; cbn zeta.
  destruct (leb (Micro.lat (Ide.micro I)) f (Jump.lookup I (Tab.jumps s) k)).
  - lia.
  - pose proof (schedule_cost I k
      (Tab.State
        (Map.set positive_encoding (encode (Jump.enc I) k)
          (join (Micro.lat (Ide.micro I)) (Jump.lookup I (Tab.jumps s) k) f) (Tab.jumps s))
        (Tab.callers s) (Tab.ends s) (Tab.work s) (Tab.pending s)) Ke w He Hw) as Hschedule.
    specialize (Hput
      (join (Micro.lat (Ide.micro I)) (Jump.lookup I (Tab.jumps s) k) f) (Tab.jumps s)).
    lia.
Qed.

End TabCost.
