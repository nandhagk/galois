(** * List cost fixtures

    These examples observe values and exact charges, including skipped callbacks.
    For example, finding the first element does not charge the rest.
    Builds on: CostList. *)

From Stdlib Require Import List NArith Lia.
From Galois.Cost Require Import CostMonad CostList.
Import List.ListNotations Cost.Notations.
Open Scope N_scope.

Definition twice_c (x : nat) : Cost.t nat := Cost.tick 2 ;; Cost.ret (2 * x)%nat.
Definition even_c (x : nat) : Cost.t bool := Cost.tick 2 ;; Cost.ret (Nat.even x).
Definition present_c (x : nat) : Cost.t (option nat) :=
  Cost.tick 2 ;; Cost.ret (if Nat.even x then Some x else None).

(** An importing client obtains witnesses for an arbitrary callback through the public contract. *)
Example filter_map_arbitrary_callback {A B} (f : A -> option B) xs y :
  In y (filter_map f xs) <-> exists x, In x xs /\ f x = Some y.
Proof.
  apply filter_map_spec.
Qed.

Example empty_traversals :
  (Cost.value (length_c ([] : list nat)), Cost.ticks (length_c ([] : list nat)),
   Cost.value (app_c [] [1%nat]), Cost.ticks (rev_c ([] : list nat)),
   Cost.value (map_c twice_c []), Cost.ticks (filter_c even_c []),
   Cost.value (forallb_c even_c []), Cost.value (existsb_c even_c []),
   Cost.value (find_c even_c []), Cost.ticks (filter_map_c present_c [])) =
  (0%nat, 0, [1%nat], 0, [], 0, true, false, None, 0).
Proof.
  vm_compute. reflexivity.
Qed.

Example singleton_traversals :
  (Cost.value (length_c [3%nat]), Cost.ticks (length_c [3%nat]),
   Cost.value (app_c [3%nat] [4%nat]), Cost.ticks (app_c [3%nat] []),
   Cost.value (rev_c [3%nat]), Cost.ticks (rev_c [3%nat]),
   Cost.value (map_c twice_c [3%nat]), Cost.ticks (map_c twice_c [3%nat]),
   Cost.value (filter_c even_c [3%nat]), Cost.ticks (filter_c even_c [3%nat]),
   Cost.value (filter_map_c present_c [2%nat]), Cost.ticks (filter_map_c present_c [2%nat])) =
  (1%nat, 1, [3%nat; 4%nat], 1, [3%nat], 1, [6%nat], 3, [], 3, [2%nat], 3).
Proof.
  vm_compute. reflexivity.
Qed.

Example ordered_traversals :
  (Cost.value (rev_c [1%nat; 2%nat; 3%nat]),
   Cost.value (map_c twice_c [1%nat; 2%nat; 3%nat]),
   Cost.value (filter_c even_c [1%nat; 2%nat; 4%nat; 3%nat]),
   Cost.value (filter_map_c present_c [1%nat; 2%nat; 4%nat; 3%nat]),
   Cost.ticks (filter_map_c present_c [1%nat; 2%nat; 4%nat; 3%nat])) =
  ([3%nat; 2%nat; 1%nat], [2%nat; 4%nat; 6%nat],
   [2%nat; 4%nat], [2%nat; 4%nat], 12).
Proof.
  vm_compute. reflexivity.
Qed.

Example short_circuit_boundaries :
  (Cost.ticks (forallb_c even_c []), Cost.ticks (existsb_c even_c []),
   Cost.ticks (find_c even_c []),
   Cost.value (forallb_c even_c [2%nat]), Cost.ticks (forallb_c even_c [2%nat]),
   Cost.value (existsb_c even_c [1%nat]), Cost.ticks (existsb_c even_c [1%nat]),
   Cost.value (find_c even_c [2%nat]), Cost.ticks (find_c even_c [2%nat])) =
  (0, 0, 0, true, 3, false, 3, Some 2%nat, 3).
Proof.
  vm_compute. reflexivity.
Qed.

Example stopped_and_exhausted :
  (Cost.value (forallb_c even_c [1%nat; 2%nat; 4%nat]),
   Cost.ticks (forallb_c even_c [1%nat; 2%nat; 4%nat]),
   Cost.value (existsb_c even_c [1%nat; 2%nat; 4%nat]),
   Cost.ticks (existsb_c even_c [1%nat; 2%nat; 4%nat]),
   Cost.value (find_c even_c [1%nat; 3%nat]),
   Cost.ticks (find_c even_c [1%nat; 3%nat])) = (false, 3, true, 6, None, 6).
Proof.
  vm_compute. reflexivity.
Qed.

Definition add_c (a x : nat) : Cost.t nat := Cost.tick 2 ;; Cost.ret (a + x)%nat.

Example fold_boundaries :
  (Cost.value (fold_left_c add_c [] 7%nat), Cost.ticks (fold_left_c add_c [] 7%nat),
   Cost.value (fold_right_c add_c 7%nat []), Cost.ticks (fold_right_c add_c 7%nat []),
   Cost.value (fold_left_c add_c [2%nat] 7%nat), Cost.ticks (fold_left_c add_c [2%nat] 7%nat),
   Cost.value (fold_right_c add_c 7%nat [2%nat]), Cost.ticks (fold_right_c add_c 7%nat [2%nat]),
   Cost.value (fold_left_c add_c [1%nat; 2%nat; 3%nat] 0%nat),
   Cost.ticks (fold_right_c add_c 0%nat [1%nat; 2%nat; 3%nat])) =
  (7%nat, 0, 7%nat, 0, 9%nat, 3, 9%nat, 3, 6%nat, 9).
Proof.
  vm_compute. reflexivity.
Qed.

Example fold_spends_credit l b :
  Cost.ticks (fold_left_c (fun n (_ : unit) => Cost.tick (N.of_nat n) ;; Cost.ret O) l b)
    <= N.of_nat (length l) + N.of_nat b.
Proof.
  pose proof (ticks_fold_left_c_potential
    (fun n (_ : unit) => Cost.tick (N.of_nat n) ;; Cost.ret O)
    (fun _ => True) N.of_nat 0 l b) as Hcredit.
  assert (Hstep : forall n x, True -> In x l ->
    True /\ Cost.ticks (Cost.tick (N.of_nat n) ;; Cost.ret O) +
      N.of_nat (Cost.value (Cost.tick (N.of_nat n) ;; Cost.ret O)) <= 0 + N.of_nat n).
  { intros n x _ _. split; [constructor | autorewrite with galois_cost; cbn; lia]. }
  specialize (Hcredit Hstep I). nia.
Qed.
