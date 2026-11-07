(** * Order-solver importing clients

    Each hint has a symbolic client that keeps the lattice abstract.
    For example, transitivity connects three successive comparisons without computation.
    Builds on: LatticeTactics and LatticeSimple. *)

From Galois.Lattice Require Import LatticeCore LatticeTactics LatticeSimple.

Section Hints.
Context {A : Type} (L : lattice A) (H : lattice_laws L) (a b c d : A).

Example solve_refl : leb L a a = true.
Proof.
  order_solver.
Qed.

Example solve_trans :
  leb L a b = true -> leb L b c = true -> leb L c d = true -> leb L a d = true.
Proof.
  intros Hab Hbc Hcd; order_solver.
Qed.

Example solve_bottom : leb L (bot L) a = true.
Proof.
  order_solver.
Qed.

Example solve_join_left : leb L a (join L a b) = true.
Proof.
  order_solver.
Qed.

Example solve_join_right : leb L b (join L a b) = true.
Proof.
  order_solver.
Qed.

Example solve_widen_left : leb L a (widen L a b) = true.
Proof.
  order_solver.
Qed.

Example solve_widen_right : leb L b (widen L a b) = true.
Proof.
  order_solver.
Qed.

Example solve_narrow_lower : leb L b a = true -> leb L (narrow L a b) a = true.
Proof.
  intro Hba; order_solver.
Qed.

Example solve_narrow_upper : leb L b a = true -> leb L b (narrow L a b) = true.
Proof.
  intro Hba; order_solver.
Qed.

Example solve_meet_left meet (HM : meet_laws L meet) : leb L (meet a b) a = true.
Proof.
  order_solver.
Qed.

Example solve_meet_right meet (HM : meet_laws L meet) : leb L (meet a b) b = true.
Proof.
  order_solver.
Qed.

Example solve_join_monotone (HU : lub_laws L) :
  leb L a b = true -> leb L c d = true -> leb L (join L a c) (join L b d) = true.
Proof.
  intros Hab Hcd; order_solver.
Qed.
End Hints.

Example reject_false_comparison : True.
Proof.
  pose proof bool_laws as H.
  Fail assert (leb bool_lattice true false = true) by order_solver.
  exact I.
Qed.

Example reject_missing_laws {A} (L : lattice A) (a : A) : True.
Proof.
  Fail assert (leb L a a = true) by order_solver.
  exact I.
Qed.
