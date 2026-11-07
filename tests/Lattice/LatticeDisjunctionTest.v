(** * Disjunction fixtures

    Capped joins retain weak laws while leastness needs selective component joins.
    For example, two incomparable flat values at cap one join to a nonleast singleton.
    Builds on: LatticeDisjunction, LatticeFlat and LatticeSimple. *)

From Stdlib Require Import List Bool NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Lattice Require Import LatticeCore LatticeHeight LatticeDisjunction LatticeFlat
  LatticeSimple.
Import List.ListNotations Cost.Notations.

Definition flat_bool := flat_lattice Bool.eqb.

Example disjunction_cap_one :
  join (disjunction 1 flat_bool) [FVal false] [FVal true; FBot] = [FTop].
Proof.
  vm_compute; reflexivity.
Qed.

Example disjunction_cap_two :
  join (disjunction 2 flat_bool) [FVal false] [FVal true; FBot] = [FVal false; FVal true].
Proof.
  vm_compute; reflexivity.
Qed.

Example disjunction_nonleast_counterexample :
  (leb (disjunction 1 flat_bool) [FVal false] [FVal false; FVal true],
   leb (disjunction 1 flat_bool) [FVal true] [FVal false; FVal true],
   leb (disjunction 1 flat_bool)
     (join (disjunction 1 flat_bool) [FVal false] [FVal true])
     [FVal false; FVal true]) = (true, true, false).
Proof.
  vm_compute; reflexivity.
Qed.

Example disjunction_negative :
  leb (disjunction 2 flat_bool) [FVal true] [FVal false] = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example disjunction_empty :
  (join (disjunction 0 flat_bool) [] [],
   leb (disjunction 0 flat_bool) [] [],
   widen (disjunction 0 flat_bool) [] []) = ([], true, []).
Proof.
  vm_compute; reflexivity.
Qed.

Example disjunction_cap_zero :
  join (disjunction 0 flat_bool) [FVal false] [] = [FVal false].
Proof.
  vm_compute; reflexivity.
Qed.

Example disjunction_empty_right :
  leb (disjunction 1 flat_bool) [FBot] [] = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example disjunction_empty_costs :
  (Cost.ticks (leb_c (disjunction 0 flat_bool) [] []),
   Cost.ticks (join_c (disjunction 0 flat_bool) [] []),
   Cost.ticks (widen_c (disjunction 0 flat_bool) [] [FVal false])) = (0%N, 1%N, 6%N).
Proof.
  vm_compute; reflexivity.
Qed.

Example disjunction_collapse :
  widen (disjunction 2 flat_bool) [FVal false] [FVal true] = [FTop].
Proof.
  vm_compute; reflexivity.
Qed.

Example disjunction_covered :
  widen (disjunction 2 flat_bool) [FTop; FVal true] [FVal false] = [FTop; FVal true].
Proof.
  vm_compute; reflexivity.
Qed.

Example bool_join_selective :
  forall a b, leb bool_lattice (join bool_lattice a b) a = true \/
    leb bool_lattice (join bool_lattice a b) b = true.
Proof.
  intros [] []; vm_compute; auto.
Qed.

Example selective_disjunction_client k : lub_laws (disjunction k bool_lattice).
Proof.
  apply disjunction_lub; [exact bool_laws | exact bool_join_selective].
Qed.

Example selective_leastness :
  leb (disjunction 1 bool_lattice)
    (join (disjunction 1 bool_lattice) [false] [true]) [false; true] = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example disjunction_leb_ticks :
  Cost.ticks (leb_c (disjunction 1 flat_bool) [FVal false] [FVal true; FVal false]) = 8%N.
Proof.
  vm_compute; reflexivity.
Qed.

Example disjunction_join_ticks :
  Cost.ticks (join_c (disjunction 1 flat_bool) [FVal false] [FVal true]) = 9%N.
Proof.
  vm_compute; reflexivity.
Qed.

(** The component join callback charges seven ticks before disjunction overhead. *)
Definition expensive_bool : lattice bool :=
  {| leb_c := leb_c bool_lattice;
     bot := false;
     join_c := fun a b => Cost.tick 7 ;; Cost.ret (orb a b);
     widen_c := widen_c bool_lattice;
     narrow_c := narrow_c bool_lattice |}.

Example fixed_cap_long_tail :
  (Cost.ticks (join_c (disjunction 1 expensive_bool) [] [false; true]),
   Cost.ticks (join_c (disjunction 1 expensive_bool) [] [false; true; false; true])) =
    (14%N, 34%N).
Proof.
  vm_compute; reflexivity.
Qed.

Example widening_callback_ticks :
  Cost.ticks (widen_c (disjunction 1 expensive_bool) [false] [true]) = 19%N.
Proof.
  vm_compute; reflexivity.
Qed.

Example disjunction_measure_client :
  let W := disjunction_wrank bool_lattice (fun _ => True) bool_closed
    bool_laws bool_wrank 1 in
  (wbound W, wrank W [false; false],
   wrank W (widen (disjunction 1 bool_lattice) [false; false] [true])) = (3, 3, 0).
Proof.
  vm_compute; reflexivity.
Qed.
