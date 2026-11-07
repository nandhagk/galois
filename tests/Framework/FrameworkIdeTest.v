(** * Symbolic jump and value fixtures

    A two-function taint problem and integer translations use finite fact support.
    For example, a translation jump maps the integer 41 to 42 without listing integers.
    Builds on: FrameworkIde, FrameworkStack and DomainsPoint. *)

From Stdlib Require Import List Bool ZArith NArith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Lattice Require Import LatticeCore LatticeSimple.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramCfg ProgramIcfg.
From Galois.Domains Require Import DomainsPoint.
From Galois.Fixpoint Require Import FixpointSystem FixpointCheck FixpointAnalysis.
From Galois.Framework Require Import FrameworkMicro FrameworkIfds FrameworkStack FrameworkIde.
From Galois.Tests.Framework Require Import FrameworkDenseTest.
Import List.ListNotations Cost.Notations.
Local Open Scope nat_scope.

Definition two_functions : Cfg.t nat nat :=
  Cfg.Make (Graph.of_pure [0] [0; 1; 2; 3]
    (fun n => match n with 0 => [0] | 1 => [1] | 2 => [2] | _ => [] end)
    (fun e => e)
    (fun e => S e)) nat_encoding nat_encoding.

Definition icfg :=
  Icfg.of_pure two_functions nat_encoding
    (fun e => match e with
      | 0 => Icfg.Call 7
      | 2 => Icfg.Return 7
      | _ => Icfg.Internal
      end).

Definition taint : Ifds.t nat nat nat unit :=
  Ifds.of_pure icfg unit_encoding [tt]
    (fun e d => match e, d with
      | 1, None => [None; Some tt]
      | _, _ => [d]
      end).

Definition ifds_ide := Ifds.as_ide taint.

Definition taint_keys : list (jkey nat unit) :=
  [((0, None), (0, None)); ((0, Some tt), (0, Some tt));
   ((1, None), (1, None)); ((1, Some tt), (1, Some tt));
   ((1, None), (2, None)); ((1, None), (2, Some tt));
   ((1, Some tt), (2, Some tt));
   ((0, None), (3, None)); ((0, None), (3, Some tt));
   ((0, Some tt), (3, Some tt))].

Definition taint_jump :=
  Map.of_list positive_encoding (map (fun k => (encode (Jump.enc ifds_ide) k, true)) taint_keys).

Example taint_jump_accepts : check_jumps ifds_ide 0 taint_jump = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example taint_jump_rejects : check_jumps ifds_ide 0 Map.empty = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example taint_matched_return :
  (Jump.lookup ifds_ide taint_jump ((0, None), (3, Some tt)),
   Jump.lookup ifds_ide taint_jump ((0, None), (2, Some tt))) = (true, false).
Proof.
  vm_compute; reflexivity.
Qed.

Example ifds_value_phase_runs :
  observe (value_analysis ifds_ide (Jump.lookup_c ifds_ide taint_jump) (0, None) tt)
    4 [(0, None); (3, Some tt)] = Some [tt; tt].
Proof.
  vm_compute; reflexivity.
Qed.

Example ifds_value_candidate :
  check_post unit_lattice
    (Analysis.system
      (value_analysis ifds_ide (Jump.lookup_c ifds_ide taint_jump) (0, None) tt))
    (fun _ => tt) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example stack_truncation : Stack.truncate 2 [7; 8; 9] = [7; 8].
Proof.
  vm_compute; reflexivity.
Qed.

Example matched_path :
  Stack.balanced taint 0 None 3 (Some tt).
Proof.
  eapply Stack.next.
  - apply (Stack.call taint 0 7 None None []); vm_compute; auto.
  - eapply Stack.next.
    + apply (Stack.internal taint 1 None (Some tt) [7]); vm_compute; auto.
    + eapply Stack.next.
      * apply (Stack.return_ taint 2 7 (Some tt) (Some tt) []); vm_compute; auto.
      * apply Stack.refl.
Qed.

Example mismatched_return_rejected :
  ~ Stack.step taint (2, Some tt, [8]) 2 (3, Some tt, []).
Proof.
  intro Hstep; inversion Hstep; subst; vm_compute in *; congruence.
Qed.

Example zero_step_balanced : Stack.balanced taint 0 None 0 None.
Proof.
  apply Stack.refl.
Qed.

(** Translations x+b form an affine symbolic family over an infinite flat integer carrier. *)
Definition translation_compose (f g : point) :=
  match f, g with
  | PBot, _ | _, PBot => PBot
  | PVal b, PVal c => PVal (b + c)
  | _, _ => PTop
  end.

Definition translation_apply (f a : point) :=
  match f, a with
  | PBot, _ | _, PBot => PBot
  | PVal b, PVal z => PVal (z + b)
  | _, _ => PTop
  end.

Definition translations : Micro.t point point :=
  Micro.of_pure (PVal 0) translation_compose translation_apply point_lattice.

(** Translation composition applies the right function before the left function. *)
Theorem translations_composition f g a :
  translation_apply (translation_compose f g) a =
    translation_apply f (translation_apply g a).
Proof.
  destruct f, g, a; cbn [translation_compose translation_apply];
    try reflexivity; f_equal; lia.
Qed.

(** Translation by zero is identity on every flat integer fact. *)
Theorem translations_identity a : translation_apply (PVal 0) a = a.
Proof.
  destruct a; cbn [translation_apply]; try reflexivity; f_equal; lia.
Qed.

Definition affine_ifds : Ifds.t nat nat nat unit :=
  Ifds.of_pure icfg unit_encoding [] (fun _ d => [d]).

Definition affine : Ide.t nat nat nat unit point point :=
  Ide.Make affine_ifds point_lattice translations
    (fun e _ _ => Cost.ret (PVal (if Nat.eqb e 1 then 1 else 0))).

Definition affine_keys : list (jkey nat unit * point) :=
  [(((0, None), (0, None)), PVal 0);
   (((1, None), (1, None)), PVal 0);
   (((1, None), (2, None)), PVal 1);
   (((0, None), (3, None)), PVal 1)].

Definition affine_jump :=
  Map.of_list positive_encoding (map (fun kv => (encode (Jump.enc affine) (fst kv), snd kv))
    affine_keys).

Example affine_jump_accepts : check_jumps affine 0 affine_jump = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example affine_jump_rejects_missing_return :
  check_jumps affine 0 (Map.remove positive_encoding
    (encode (Jump.enc affine) ((0, None), (3, None))) affine_jump) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example affine_integer_value :
  observe (value_analysis affine (Jump.lookup_c affine affine_jump) (0, None) (PVal 41))
    8 [(0, None); (1, None); (2, None); (3, None)] =
    Some [PVal 41; PVal 41; PVal 42; PVal 42].
Proof.
  vm_compute; reflexivity.
Qed.

Example affine_hand_candidate :
  check_post point_lattice
    (Analysis.system (value_analysis affine (Jump.lookup_c affine affine_jump)
      (0, None) (PVal 41)))
    (fun v => match fst v with 0 | 1 => PVal 41 | _ => PVal 42 end) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example affine_value_rejects_bottom :
  check_post point_lattice
    (Analysis.system (value_analysis affine (Jump.lookup_c affine affine_jump)
      (0, None) (PVal 41))) (fun _ => PBot) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example affine_different_unlisted_integer :
  Micro.apply translations (PVal 1) (PVal 1000000) = PVal 1000001.
Proof.
  vm_compute; reflexivity.
Qed.

(** Distinct integers embed injectively, so the value carrier is infinite. *)
Theorem infinite_value_carrier (x y : Z) : PVal x = PVal y -> x = y.
Proof.
  congruence.
Qed.

Definition no_flow : Ifds.t nat nat nat unit :=
  Ifds.of_pure (Icfg.of_pure singleton nat_encoding (fun _ => Icfg.Internal))
    unit_encoding [] (fun _ _ => []).

Definition no_flow_ide := Ifds.as_ide no_flow.
Definition no_flow_jump := Map.of_list positive_encoding
  [(encode (Jump.enc no_flow_ide) ((0, None), (0, None)), true)].

Example no_flow_identity : check_jumps no_flow_ide 0 no_flow_jump = true.
Proof.
  vm_compute; reflexivity.
Qed.

Definition integer_bound (xs : list point) :=
  fold_right (fun a n => match a with PVal z => Z.max z n | _ => n end) 0%Z xs.

Local Lemma member_bounded xs z : In (PVal z) xs -> (z <= integer_bound xs)%Z.
Proof.
  induction xs as [|a xs IH]; cbn [In integer_bound fold_right]; [contradiction|].
  intros [Heq|Hin].
  - subst a; apply Z.le_max_l.
  - specialize (IH Hin); destruct a; try exact IH.
    eapply Z.le_trans; [exact IH|apply Z.le_max_r].
Qed.

(** No finite list enumerates the value carrier or the shared symbolic-function carrier. *)
Theorem no_carrier_enumeration (xs : list point) : exists a, ~ In a xs.
Proof.
  exists (PVal (integer_bound xs + 1)); intro Hin.
  pose proof (member_bounded xs _ Hin); lia.
Qed.
