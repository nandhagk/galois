(** * Boolean and unit lattices

    Booleans model reachability or liveness, while unit supplies a trivial slot.
    For example, joining false and true gives true.
    Builds on: LatticeCore, LatticeHeight, LatticeConcrete and LatticeKit. *)

From Stdlib Require Import Bool Arith Lia.
From Galois.Lattice Require Import LatticeCore LatticeHeight LatticeConcrete LatticeKit.

(** Boolean order is implication and join is disjunction. *)
Definition bool_lattice : lattice bool := simple implb false orb.

(** Unit operations have a unique result. *)
Definition unit_lattice : lattice unit := simple (fun _ _ => true) tt (fun _ _ => tt).

(** Boolean implication and disjunction satisfy the weak laws. *)
Theorem bool_laws : lattice_laws bool_lattice.
Proof.
  apply simple_laws; intros; repeat match goal with
  | b : bool |- _ => destruct b
  end; cbn in *; congruence.
Qed.

(** Disjunction is a least upper bound in implication order. *)
Theorem bool_lub : lub_laws bool_lattice.
Proof.
  constructor; intros [] [] []; cbn; congruence.
Qed.

(** Unit satisfies the weak laws through the finite-domain defaults. *)
Theorem unit_laws : lattice_laws unit_lattice.
Proof.
  apply simple_laws; intros; reflexivity.
Qed.

(** Unit joins are least upper bounds. *)
Theorem unit_lub : lub_laws unit_lattice.
Proof.
  constructor; intros; reflexivity.
Qed.

(** True bounds both booleans. *)
Definition bool_top : top bool_lattice.
Proof.
  refine {| top_value := true |}; intros []; reflexivity.
Defined.

(** Unit's unique value is greatest. *)
Definition unit_top : top unit_lattice.
Proof.
  refine {| top_value := tt |}; intros []; reflexivity.
Defined.

(** The total boolean invariant is closed under all operations. *)
Theorem bool_closed : closed_on bool_lattice (fun _ => True).
Proof.
  constructor; intros; exact I.
Qed.

(** The total unit invariant is closed under all operations. *)
Theorem unit_closed : closed_on unit_lattice (fun _ => True).
Proof.
  constructor; intros; exact I.
Qed.

(** False and true have heights zero and one. *)
Definition bool_height : height bool_lattice.
Proof.
  refine {| rank := fun b : bool => if b then 1 else 0;
            bound := 1 |}.
  - intros [] _; cbn; lia.
  - intros [] [] _ _ Hle; cbn in *; try discriminate; lia.
  - intros [] [] _ _ Hstrict; cbn in *; try discriminate; lia.
Defined.

(** Unit has height zero. *)
Definition unit_height : height unit_lattice.
Proof.
  refine {| rank := fun _ => 0;
            bound := 0 |}.
  - intros; lia.
  - intros; lia.
  - intros [] [] _ _ Hstrict; discriminate.
Defined.

(** Boolean widening credits complement its height. *)
Definition bool_wrank : widening_rank bool_lattice :=
  height_wrank bool_lattice bool_laws bool_lub bool_closed (fun _ _ => eq_refl) bool_height.

(** Unit widening needs no progress credits. *)
Definition unit_wrank : widening_rank unit_lattice :=
  height_wrank unit_lattice unit_laws unit_lub unit_closed (fun _ _ => eq_refl) unit_height.

(** Boolean reachability denotes every concrete value precisely when true. *)
Definition bool_gamma {C} : concretisation bool C :=
  {| gamma := fun b _ => b = true |}.

(** Unit denotes every concrete value. *)
Definition unit_gamma {C} : concretisation unit C :=
  {| gamma := fun _ _ => True |}.

(** Boolean reachability meaning is monotone. *)
Theorem bool_gamma_laws {C} : concretisation_laws bool_lattice (@bool_gamma C).
Proof.
  constructor; intros [] [] c Hle Hc; cbn in *; congruence.
Qed.

(** Boolean bottom is unreachable. *)
Theorem bool_bot_empty {C} : bottom_empty bool_lattice (@bool_gamma C).
Proof.
  constructor; intros c Hfalse; discriminate.
Qed.

(** Boolean top denotes all concrete values. *)
Theorem bool_top_full {C} : top_full bool_top (@bool_gamma C).
Proof.
  constructor; intros; reflexivity.
Qed.

(** Unit's constant meaning is monotone. *)
Theorem unit_gamma_laws {C} : concretisation_laws unit_lattice (@unit_gamma C).
Proof.
  constructor; intros; exact I.
Qed.

(** Unit top denotes every concrete value. *)
Theorem unit_top_full {C} : top_full unit_top (@unit_gamma C).
Proof.
  constructor; intros; exact I.
Qed.

(** A live boolean need requires equality and a dead need imposes no condition. *)
Definition bool_agree {C} : agreement bool C :=
  {| agree := fun b x y => b = true -> x = y |}.

(** Unit needs no information. *)
Definition unit_agree {C} : agreement unit C :=
  {| agree := fun _ _ _ => True |}.

(** Boolean needs give reflexive antitone agreement. *)
Theorem bool_agree_laws {C} : agreement_laws bool_lattice (@bool_agree C).
Proof.
  constructor.
  - intros b c _; reflexivity.
  - intros [] [] x y Hle Hxy Hlive; cbn in *; try discriminate; apply Hxy; reflexivity.
Qed.

(** Dead values place no restriction on a pair. *)
Theorem bool_agree_bot {C} : agreement_bot bool_lattice (@bool_agree C).
Proof.
  constructor; intros x y Hfalse; discriminate.
Qed.

(** Agreement on both boolean needs suffices on their disjunction. *)
Theorem bool_agree_join {C} : agreement_join_law bool_lattice (@bool_agree C).
Proof.
  constructor; intros [] [] x y Hx Hy Hlive; cbn in *; try discriminate;
    first [solve [apply Hx; reflexivity] | solve [apply Hy; reflexivity]].
Qed.

(** Boolean agreement is symmetric and transitive at each need. *)
Theorem bool_agree_equivalence {C} : agreement_equivalence (@bool_agree C).
Proof.
  constructor; cbn.
  - intros a x y Hxy Ha; symmetry; apply Hxy, Ha.
  - intros a x y z Hxy Hyz Ha; transitivity y; [apply Hxy | apply Hyz]; exact Ha.
Qed.

(** Unit agreement is reflexive and antitone. *)
Theorem unit_agree_laws {C} : agreement_laws unit_lattice (@unit_agree C).
Proof.
  constructor; intros; exact I.
Qed.

(** Unit bottom requires no information. *)
Theorem unit_agree_bot {C} : agreement_bot unit_lattice (@unit_agree C).
Proof.
  constructor; intros; exact I.
Qed.

(** Unit agreement holds on every join. *)
Theorem unit_agree_join {C} : agreement_join_law unit_lattice (@unit_agree C).
Proof.
  constructor; intros; exact I.
Qed.

(** Unit agreement is symmetric and transitive. *)
Theorem unit_agree_equivalence {C} : agreement_equivalence (@unit_agree C).
Proof.
  constructor; intros; exact I.
Qed.
