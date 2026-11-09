(** * Update table examples

    Table dispatch accepts the three supported recurrence updates and rejects malformed payloads.
    For example, direct doubling requires no independent other-expression.
    Builds on: AnalysesLoopsIdioms. *)

From Stdlib Require Import NArith ZArith List.
From Galois.Cost Require Import CostMonad.
From Galois.Analyses.Loops Require Import AnalysesLoopsChrec AnalysesLoopsIdioms.
Import Chrec List.ListNotations.

Example idiom_additive :
  Idiom.apply Idiom.SAdd (CInv (IVar 10)) (Some (CInv (IVar 11))) =
    Some (CRec (CInv (IVar 10)) (CInv (IVar 11))).
Proof.
  vm_compute; reflexivity.
Qed.

Example idiom_doubling_preserves_legacy_shape :
  Idiom.apply Idiom.SDouble (CInv (IVar 10)) None =
    Some (CGeo (CInv (IVar 10)) (CInv (IConst 2))).
Proof.
  vm_compute; reflexivity.
Qed.

Example idiom_doubling_rejects_other :
  Idiom.apply Idiom.SDouble (CInv (IConst 1) : Chrec.t nat)
    (Some (CInv (IConst 2))) = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example idiom_additive_missing_other :
  Idiom.apply Idiom.SAdd (CInv (IConst 1) : Chrec.t nat) None = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example idiom_actual_dispatch_ticks :
  List.map (fun kind =>
    Cost.ticks (Idiom.apply_c kind (CInv (IConst 1) : Chrec.t nat) None))
    [Idiom.SAdd; Idiom.SMul; Idiom.SDouble] = [3; 4; 5]%N.
Proof.
  vm_compute; reflexivity.
Qed.
