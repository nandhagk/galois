(** * Polyhedral computation fixtures

    These examples exercise raw constraints independently of expression linearization.
    For example, 2*x <= 1 does not rationally entail x <= 0.
    Builds on: Poly, LinCert, Linearize, ZLang and positive keys. *)

From Stdlib Require Import List ZArith.
From Galois.Base Require Import Key.
From Galois.Domains Require Import LangSig ValueSig ZLang.
From Galois.States Require Import EnvSig.
From Galois.Relational Require Import LinForm LinCertSig LinCert Linearize PolySig Poly.
Import List.ListNotations.

Local Open Scope Z_scope.

Module FixtureLinearize := LinearizeCode PosKeyCode ZLangCode.
Module FixtureCertificate := LinCertCode PosKeyCode.
Module FixturePoly := PolyCode PosKeyCode ZLangCode FixtureLinearize FixtureCertificate.

Definition upper_x (b : Z) : lcons positive := LCons _ [(1%positive, 1)] RLe b.
Definition lower_x (b : Z) : lcons positive := LCons _ [(1%positive, -1)] RLe (-b).
Definition equal_x (b : Z) : lcons positive := LCons _ [(1%positive, 1)] REq b.
Definition equal_y (b : Z) : lcons positive := LCons _ [(2%positive, 1)] REq b.

(** The strict rational complement retains a fractional countermodel. *)
Example fractional_countermodel :
  FixturePoly.entail_cert [LCons _ [(1%positive, 2)] RLe 1] (upper_x 0) = None.
Proof.
  vm_compute. reflexivity.
Qed.

(** A tight rational endpoint produces a cut-free certificate. *)
Example rational_endpoint_certificate :
  FixturePoly.entail_cert [LCons _ [(1%positive, 2)] RLe 2]
    (LCons _ [(1%positive, 3)] RLe 3) = Some (Cert [3] 2 false).
Proof.
  vm_compute. reflexivity.
Qed.

(** Opposite inequalities eliminate their common variable with exact multipliers. *)
Example eliminate_opposite_rows :
  FixturePoly.fm_elim 1%positive
    [LCons _ [(1%positive, 1); (2%positive, 1)] RLe 3; lower_x 1] =
    [Tracked _ (LCons _ [(2%positive, 1)] RLe 2) [1; 1]].
Proof.
  vm_compute. reflexivity.
Qed.

(** A negative equality pivot keeps the other inequality's orientation. *)
Example eliminate_negative_equality :
  FixturePoly.fm_elim 1%positive
    [LCons _ [(1%positive, -2); (2%positive, 1)] REq 4; upper_x 3] =
    [Tracked _ (LCons _ [] REq 0) [0; 0];
     Tracked _ (LCons _ [(2%positive, 1)] RLe 10) [1; 2]].
Proof.
  vm_compute. reflexivity.
Qed.

(** Substitution sums all occurrences of the substituted and surviving variables. *)
Example substitute_repeated_keys :
  FixturePoly.subst 1%positive (Lin _ [(2%positive, 2)] 1)
    (LCons _ [(1%positive, 1); (1%positive, 2); (2%positive, -1)] RLe 7) =
    LCons _ [(2%positive, 5)] RLe 4.
Proof.
  vm_compute. reflexivity.
Qed.

(** Rationally inconsistent inequalities are recognized as bottom. *)
Example inconsistent_inequalities :
  FixturePoly.is_bot (Reached [upper_x 0; lower_x 1]) = true.
Proof.
  vm_compute. reflexivity.
Qed.

(** Inconsistent equalities also entail the explicit unreachable state. *)
Example inconsistent_equalities :
  FixturePoly.leb (Reached [equal_x 0; equal_x 1]) Unreached = true.
Proof.
  vm_compute. reflexivity.
Qed.

(** An integer divisibility obstruction is not a rational contradiction. *)
Example rationally_feasible_equality :
  FixturePoly.is_bot (Reached [LCons _ [(1%positive, 2)] REq 1]) = false.
Proof.
  vm_compute. reflexivity.
Qed.

(** Checking both inequality directions recognizes an equality conclusion. *)
Example equality_from_opposite_bounds :
  FixturePoly.leb (Reached [upper_x 2; lower_x 2]) (Reached [equal_x 2]) = true.
Proof.
  vm_compute. reflexivity.
Qed.

(** The weak join retains the shared weaker bound. *)
Example join_shared_bound :
  FixturePoly.join (Reached [upper_x 1]) (Reached [upper_x 2]) = Reached [upper_x 2].
Proof.
  vm_compute. reflexivity.
Qed.

(** Widening drops the old bound that the candidate violates. *)
Example widening_drops_old_bound :
  FixturePoly.widen tt (Reached [upper_x 1]) (Reached [upper_x 2]) = Reached [].
Proof.
  vm_compute. reflexivity.
Qed.

(** The temporary variable handles a self-dependent affine assignment. *)
Example assign_self_dependent :
  FixturePoly.leb
    (Reached (FixturePoly.assign_linear 1%positive
      (Lin _ [(1%positive, 1); (2%positive, 1)] 0) [equal_x 1; equal_y 2]))
    (Reached [equal_x 3; equal_y 2]) = true.
Proof.
  vm_compute. reflexivity.
Qed.

(** A noninvertible assignment retains the new equality and surviving variables. *)
Example assign_noninvertible :
  FixturePoly.leb
    (Reached (FixturePoly.assign_linear 1%positive
      (Lin _ [(2%positive, 1)] 2) [equal_x 10; equal_y 3]))
    (Reached [equal_x 5; equal_y 3]) = true.
Proof.
  vm_compute. reflexivity.
Qed.

(** Projected bounds include the constant part of a queried linear form. *)
Example range_with_constant :
  FixturePoly.range_linear [lower_x 2; upper_x 5] (Lin _ [(1%positive, 1)] 1) =
    (Fin 3, Fin 6).
Proof.
  vm_compute. reflexivity.
Qed.

(** Integer upper bounds round down at fractional rational endpoints. *)
Example range_rounds_upper :
  FixturePoly.range_linear [LCons _ [(1%positive, 2)] RLe 5]
    (Lin _ [(1%positive, 1)] 0) = (NegInf, Fin 2).
Proof.
  vm_compute. reflexivity.
Qed.

(** Integer lower bounds round up at fractional rational endpoints. *)
Example range_rounds_lower :
  FixturePoly.range_linear [LCons _ [(1%positive, -2)] RLe (-5)]
    (Lin _ [(1%positive, 1)] 0) = (Fin 3, PosInf).
Proof.
  vm_compute. reflexivity.
Qed.

(** Range checking merges repeated keys and removes canceled source variables once. *)
Example range_repeated_source_keys :
  FixturePoly.range_linear
    [LCons _ [(1%positive, 3); (1%positive, -1);
      (2%positive, 7); (2%positive, -7)] RLe 5]
    (Lin _ [(1%positive, 1)] 0) = (NegInf, Fin 2).
Proof.
  vm_compute. reflexivity.
Qed.

(** A raw equality with repeated keys retains its exact queried value. *)
Example range_repeated_equality :
  FixturePoly.range_linear [LCons _ [(1%positive, 3); (1%positive, -1)] REq 6]
    (Lin _ [(1%positive, 1)] 1) = (Fin 4, Fin 4).
Proof.
  vm_compute. reflexivity.
Qed.

(** A raw chain keeps its original certificate indices after shared normalization. *)
Definition raw_certificate_chain : list (lcons positive) :=
  [LCons _ [(1%positive, 1); (2%positive, -1); (2%positive, -1)] REq 0;
   LCons _ [(2%positive, 1); (3%positive, -1); (3%positive, -1)] REq 0;
   LCons _ [(3%positive, 1)] RLe 0].

Example raw_chain_certificate_checked :
  (match FixturePoly.entail_cert raw_certificate_chain (upper_x 0) with
   | Some k => FixtureCertificate.check_entails raw_certificate_chain (upper_x 0) k
   | None => false
   end) = true.
Proof.
  vm_compute. reflexivity.
Qed.

(** Canceled source coordinates do not affect the shared normalized entailment engine. *)
Example entail_canceled_source_keys :
  (let P := [LCons _ [(1%positive, 1); (1%positive, -1); (2%positive, 1)] RLe 0] in
   let c := LCons _ [(2%positive, 1)] RLe 0 in
   match FixturePoly.entail_cert P c with
   | Some k => FixtureCertificate.check_entails P c k
   | None => false
   end) = true.
Proof.
  vm_compute. reflexivity.
Qed.

(** Target normalization preserves acceptance against its original repeated occurrences. *)
Example entail_repeated_target_checked :
  (let c := LCons _ [(2%positive, 1); (2%positive, -1); (1%positive, 2)] RLe 4 in
   match FixturePoly.entail_cert [upper_x 2] c with
   | Some k => FixtureCertificate.check_entails [upper_x 2] c k
   | None => false
   end) = true.
Proof.
  vm_compute. reflexivity.
Qed.

(** An empty source can certify a tautology whose raw coefficients cancel. *)
Example empty_source_canceled_target :
  FixturePoly.entail_cert [] (LCons _ [(1%positive, 1); (1%positive, -1)] RLe 0) =
    Some (Cert [] 1 false).
Proof.
  vm_compute. reflexivity.
Qed.

(** A direct equality target retains its exact equality certificate. *)
Example direct_equality_certificate :
  FixturePoly.entail_cert [equal_x 2] (equal_x 2) = Some (Cert [1] 1 false).
Proof.
  vm_compute. reflexivity.
Qed.

(** A one-sided inequality cannot certify an equality conclusion. *)
Example direct_equality_rejects_halfspace :
  FixturePoly.entail_cert [upper_x 0] (equal_x 0) = None.
Proof.
  vm_compute. reflexivity.
Qed.

(** A source contradiction certifies an equality with the canonical positive scale. *)
Example source_contradiction_equality_certificate :
  (let P := [equal_x 0; equal_x 1] in
   match FixturePoly.entail_cert P (equal_y 7) with
   | Some k => FixtureCertificate.check_entails P (equal_y 7) k
   | None => false
   end) = true.
Proof.
  vm_compute. reflexivity.
Qed.

(** Signed preparation merges long alternating updates while retaining the constant. *)
Definition prepared_zero_form : lin positive :=
  Lin _ (repeat (2%positive, 1) 8 ++
    concat (repeat [(2%positive, -1); (2%positive, 1)] 8) ++
    repeat (2%positive, -1) 8) 7.

Example signed_preparation_cancels_alternating_units :
  poly_prepare_form PosKeyCode.encode prepared_zero_form = Lin _ [] 7.
Proof.
  vm_compute. reflexivity.
Qed.

(** This fixture supplies a raw affine form to exercise the public assignment path. *)
Module PreparedFixtureLinearize.
  Definition lin_of (_ : term ZLangCode.op positive) : option (lin positive * wrapr) :=
    Some (prepared_zero_form, NoWrap).
  Definition atoms_of (_ : ZLangCode.guard) (_ : list (term ZLangCode.op positive))
      : list (atom positive) := [].
End PreparedFixtureLinearize.

Module PreparedFixturePoly :=
  PolyCode PosKeyCode ZLangCode PreparedFixtureLinearize FixtureCertificate.

(** The same prepared form reaches both the assignment row and its final checker. *)
Example assignment_uses_the_prepared_zero_form :
  PreparedFixturePoly.assign 1%positive (Leaf 2%positive) (Reached []) =
    Reached [equal_x 7].
Proof.
  vm_compute. reflexivity.
Qed.
