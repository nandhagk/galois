(** * Recurrence observation examples

    Word literals and mathematical coefficients have different sign-normalization rules.
    For example, the eight-bit literal 255 becomes minus one and coefficient two stays two.
    Builds on: AnalysesLoopsChrec. *)

From Stdlib Require Import ZArith NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Analyses.Loops Require Import AnalysesLoopsChrec.
Import Chrec.

Definition scev_test_env (_ : nat) : Z := 0%Z.

Definition scev_test_affine (base step : Z) : Chrec.t nat :=
  CRec (CInv (IConst base)) (CInv (IConst step)).

Example scev_constant_value :
  Chrec.eval scev_test_env (CInv (IConst 7)) 12 = 7%Z.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_signed_word_literal_and_coefficient :
  signed_iexpr 8%positive Signed (IWordConst 255 : iexpr nat) = IConst (-1) /\
  signed_iexpr 1%positive Signed (IConst 2 : iexpr nat) = IConst 2.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example scev_unsigned_literal_boundary :
  signed_iexpr 1%positive Unsigned (IWordConst (-1) : iexpr nat) = IConst 1.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_nested_additive_value :
  Chrec.eval scev_test_env
    (CRec (CInv (IConst 0)) (scev_test_affine 1 1)) 4 = 10%Z.
Proof.
  vm_compute; reflexivity.
Qed.

(* The LOOP-SCEV recovery explicitly changes this one legacy AST expectation.
   Its generic second difference contains two copies of the cross-step product. *)
Example scev_affine_product_normal_form :
  chrec_mul (scev_test_affine 2 3) (scev_test_affine 5 7) =
    CRec (CInv (IMul (IConst 2) (IConst 5)))
      (CRec (CInv (IAdd (IAdd (IMul (IConst 2) (IConst 7))
          (IMul (IConst 5) (IConst 3))) (IMul (IConst 3) (IConst 7))))
        (CInv (IAdd (IMul (IConst 3) (IConst 7)) (IMul (IConst 3) (IConst 7))))).
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_geometric_product :
  Chrec.eval scev_test_env
    (chrec_mul (CGeo (CInv (IConst 2)) (CInv (IConst 3)))
      (CGeo (CInv (IConst 5)) (CInv (IConst 2)))) 3 = 2160%Z.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_fallback_nodes :
  let a := CGeo (CInv (IConst 2)) (CInv (IConst 3)) in
  let b := scev_test_affine 1 2 in
  chrec_add a b = CSum a b /\ chrec_mul a b = CProduct a b /\
    Chrec.eval scev_test_env (CSum a b) 2 = 23%Z /\
    Chrec.eval scev_test_env (CProduct a b) 2 = 90%Z.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** Every environment and iteration observes the old and generic affine products identically. *)
Example scev_affine_product_legacy_evaluation {V} (inv : V -> Z) x s y t k :
  Chrec.eval inv (chrec_mul (CRec (CInv x) (CInv s)) (CRec (CInv y) (CInv t))) k =
    Chrec.eval inv
      (CRec (CInv (IMul x y))
        (CRec (CInv (IAdd (IAdd (IMul x t) (IMul y s)) (IMul s t)))
          (CInv (IMul (IConst 2) (IMul s t))))) k.
Proof.
  rewrite eval_mul.
  induction k as [|k IHk]; [reflexivity|].
  change (((Chrec.eval inv (CRec (CInv x) (CInv s)) k + eval_iexpr inv s) *
    (Chrec.eval inv (CRec (CInv y) (CInv t)) k + eval_iexpr inv t))%Z =
    (Chrec.eval inv
      (CRec (CInv (IMul x y))
        (CRec (CInv (IAdd (IAdd (IMul x t) (IMul y s)) (IMul s t)))
          (CInv (IMul (IConst 2) (IMul s t))))) k +
      Chrec.eval inv
        (CRec (CInv (IAdd (IAdd (IMul x t) (IMul y s)) (IMul s t)))
          (CInv (IMul (IConst 2) (IMul s t)))) k)%Z).
  rewrite <- IHk, !eval_affine; cbn [Chrec.eval eval_iexpr]; ring.
Qed.

Example scev_algebra_actual_ticks :
  Cost.ticks (chrec_mul_c (scev_test_affine 2 3) (scev_test_affine 5 7)) = 1%N /\
    Cost.ticks (chrec_add_c (scev_test_affine 2 3) (scev_test_affine 5 7)) = 5%N.
Proof.
  vm_compute; split; reflexivity.
Qed.
