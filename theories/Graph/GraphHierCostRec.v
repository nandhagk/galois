(** * Recursive hierarchy cost aggregation

    Sibling expansion charges are summed against actual component members and actual output depth.
    For example, disjoint sibling SCCs share one level's source-work budget.
    Builds on: GraphHier, GraphHierWork and GraphHierStructure. *)

From Stdlib Require Import List PArith NArith Arith Lia Permutation.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Graph Require Import GraphPrepared GraphHierSpec GraphHier GraphHierWork
  GraphHierStructure.
Import List.ListNotations.
Local Open Scope N_scope.

Module HierCostRec.

(** Sibling assembly charges one list step and retains every actual expansion callback tick. *)
Theorem assemble_cost cs expand :
  Cost.ticks (HierRun.assemble_c cs expand) =
  match cs as current return
      (forall c, In c current -> Cost.t (option Hier.tree)) -> N with
  | [] => fun _ => 0
  | c :: rest => fun next =>
    1 + Cost.ticks (next c (or_introl eq_refl)) +
      Cost.ticks (HierRun.assemble_c rest (fun d Hin => next d (or_intror Hin)))
  end expand.
Proof.
  destruct cs; [reflexivity|].
  cbn [HierRun.assemble_c]. autorewrite with galois_cost. lia.
Qed.

(** Successful callbacks accumulate one common-depth budget per source occurrence. *)
Theorem assemble_bound {V E} (p : Prepared.t V E) w K cs expand :
  (forall c Hin, exists t, Cost.value (expand c Hin) = Some t /\
    Permutation c (Hier.members_tree t) /\
    Cost.ticks (expand c Hin) <=
      K * N.of_nat (S (HierWork.depth_tree t)) * HierWork.mass p w c) ->
  Cost.ticks (HierRun.assemble_c cs expand) <=
    N.of_nat (length cs) +
      K * N.of_nat (S (HierWork.depth (Cost.value (HierRun.assemble_c cs expand)))) *
        HierWork.mass p w (concat cs).
Proof.
  revert expand. induction cs as [|c rest IH]; intros expand Hcallbacks.
  - rewrite assemble_cost. cbn [length concat HierWork.mass HierWork.sum fold_right]. nia.
  - destruct (Hcallbacks c (or_introl eq_refl)) as [t [Ht [Hmembers Hcost]]].
    assert (Htail : forall d Hin, exists tree,
      Cost.value (expand d (or_intror Hin)) = Some tree /\
      Permutation d (Hier.members_tree tree) /\
      Cost.ticks (expand d (or_intror Hin)) <=
        K * N.of_nat (S (HierWork.depth_tree tree)) * HierWork.mass p w d).
    { intros d Hin. apply Hcallbacks. }
    pose proof (IH _ Htail) as Hrest.
    rewrite assemble_cost, HierRun.assemble_value_equation, Ht.
    cbn [HierWork.depth concat length].
    unfold HierWork.mass. rewrite HierWork.sum_app.
    fold (HierWork.mass p w c) (HierWork.mass p w (concat rest)).
    pose proof (Nat.le_max_l (HierWork.depth_tree t)
      (HierWork.depth (Cost.value (HierRun.assemble_c rest
        (fun d Hin => expand d (or_intror Hin)))))) as Hleft.
    pose proof (Nat.le_max_r (HierWork.depth_tree t)
      (HierWork.depth (Cost.value (HierRun.assemble_c rest
        (fun d Hin => expand d (or_intror Hin)))))) as Hright.
    rewrite !Nat2N.inj_succ.
    assert (Hleft' : N.of_nat (HierWork.depth_tree t) <=
      N.of_nat (Nat.max (HierWork.depth_tree t)
        (HierWork.depth (Cost.value (HierRun.assemble_c rest
          (fun d Hin => expand d (or_intror Hin))))))) by lia.
    assert (Hright' : N.of_nat (HierWork.depth (Cost.value (HierRun.assemble_c rest
      (fun d Hin => expand d (or_intror Hin))))) <=
      N.of_nat (Nat.max (HierWork.depth_tree t)
        (HierWork.depth (Cost.value (HierRun.assemble_c rest
          (fun d Hin => expand d (or_intror Hin))))))) by lia.
    rewrite Nat2N.inj_succ in Hrest, Hcost.
    assert (Hfirst_scale :
      K * N.succ (N.of_nat (HierWork.depth_tree t)) * HierWork.mass p w c <=
      K * N.succ (N.of_nat (Nat.max (HierWork.depth_tree t)
        (HierWork.depth (Cost.value (HierRun.assemble_c rest
          (fun d Hin => expand d (or_intror Hin))))))) * HierWork.mass p w c).
    { apply N.mul_le_mono_r, N.mul_le_mono_l. lia. }
    assert (Hrest_scale :
      K * N.succ (N.of_nat (HierWork.depth (Cost.value (HierRun.assemble_c rest
        (fun d Hin => expand d (or_intror Hin)))))) * HierWork.mass p w (concat rest) <=
      K * N.succ (N.of_nat (Nat.max (HierWork.depth_tree t)
        (HierWork.depth (Cost.value (HierRun.assemble_c rest
          (fun d Hin => expand d (or_intror Hin))))))) * HierWork.mass p w (concat rest)).
    { apply N.mul_le_mono_r, N.mul_le_mono_l. lia. }
    set (tail := HierRun.assemble_c rest (fun d (Hin : In d rest) => expand d (or_intror Hin)))
      in *.
    set (current := expand c (or_introl eq_refl)) in *.
    set (mfirst := HierWork.mass p w c) in *.
    set (mrest := HierWork.mass p w (concat rest)) in *.
    set (dmax := N.of_nat (Nat.max (HierWork.depth_tree t)
      (HierWork.depth (Cost.value tail)))) in *.
    change (Cost.ticks tail <= N.of_nat (length rest) +
      K * N.succ (N.of_nat (HierWork.depth (Cost.value tail))) * mrest) in Hrest.
    nia.
Qed.

End HierCostRec.
