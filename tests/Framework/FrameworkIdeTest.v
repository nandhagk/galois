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

(** An importing client can inspect prepared arc occurrences through the public equation. *)
Example affine_prepared_arc :
  In (Jump.Arc 1 (1, None) (2, None) Icfg.Internal (PVal 1)) (Jump.arcs affine).
Proof.
  rewrite Jump.arcs_equation; vm_compute; auto.
Qed.

(** An importing client observes initial and callee roots without opening preparation. *)
Example affine_prepared_roots :
  Cost.value (Jump.roots_c affine 0 (Jump.arcs affine)) = [(0, None); (1, None)].
Proof.
  rewrite Jump.roots_c_value, Jump.arcs_equation; vm_compute; reflexivity.
Qed.

(** An importing client uses the lookup equation to reason about missing bindings. *)
Example affine_empty_lookup k : Jump.lookup affine Map.empty k = PBot.
Proof.
  rewrite Jump.lookup_equation, Map.find_or_equation, Map.get_empty; reflexivity.
Qed.

(** Ground seed membership uses the supplied fact domain. *)
Example affine_seed_row : In (Jump.Seed (0, None)) (Jump.rows affine 0).
Proof.
  apply Jump.rows_spec; left; exists (0, None); vm_compute; auto.
Qed.

(** Ground call membership uses an actual prepared call occurrence. *)
Example affine_call_row :
  In (Jump.Call (Jump.Arc 0 (0, None) (1, None) (Icfg.Call 7) (PVal 0)))
    (Jump.rows affine 0).
Proof.
  apply Jump.rows_spec; right; left.
  exists (Jump.Arc 0 (0, None) (1, None) (Icfg.Call 7) (PVal 0)), 7.
  vm_compute; auto.
Qed.

(** Ground path membership retains the actual procedure-entry root. *)
Example affine_path_row :
  In (Jump.Path (1, None) (Jump.Arc 1 (1, None) (2, None) Icfg.Internal (PVal 1)))
    (Jump.rows affine 0).
Proof.
  apply Jump.rows_spec; right; right; left.
  exists (1, None), (Jump.Arc 1 (1, None) (2, None) Icfg.Internal (PVal 1)).
  vm_compute; auto.
Qed.

(** Ground return membership checks the encoded site test without an injectivity premise. *)
Example affine_return_row :
  In (Jump.Return (0, None)
    (Jump.Arc 0 (0, None) (1, None) (Icfg.Call 7) (PVal 0))
    (Jump.Arc 2 (2, None) (3, None) (Icfg.Return 7) (PVal 0))) (Jump.rows affine 0).
Proof.
  apply Jump.rows_spec; right; right; right.
  exists (0, None), (Jump.Arc 0 (0, None) (1, None) (Icfg.Call 7) (PVal 0)),
    (Jump.Arc 2 (2, None) (3, None) (Icfg.Return 7) (PVal 0)).
  vm_compute; repeat split; auto.
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

Module PreFreezeMicro.

(** This historical contract contains the fields before function-order application. *)
Record laws {A F} (LA : lattice A) (M : Micro.t A F) : Prop := {
  lat_ok : lattice_laws (Micro.lat M);
  lub_ok : lub_laws (Micro.lat M);
  id_apply : forall a, equivalent LA (Micro.apply M (Micro.id M) a) a;
  compose_apply : forall f g a, equivalent LA
    (Micro.apply M (Micro.compose M f g) a) (Micro.apply M f (Micro.apply M g a));
  apply_mono : forall f a b, leb LA a b = true ->
    leb LA (Micro.apply M f a) (Micro.apply M f b) = true;
  compose_mono : forall f f' g g',
    leb (Micro.lat M) f f' = true -> leb (Micro.lat M) g g' = true ->
    leb (Micro.lat M) (Micro.compose M f g) (Micro.compose M f' g') = true;
  join_upper : forall f g a,
    leb LA (Micro.apply M f a) (Micro.apply M (join (Micro.lat M) f g) a) = true /\
    leb LA (Micro.apply M g a) (Micro.apply M (join (Micro.lat M) f g) a) = true
}.

End PreFreezeMicro.

Definition indiscrete_functions : lattice bool :=
  simple (fun _ _ => true) false (fun _ _ => true).

Definition bad_micro : Micro.t bool bool :=
  Micro.of_pure true andb andb indiscrete_functions.

(** The old obligations permit function comparisons that do not preserve application. *)
Theorem bad_micro_old_obligations : PreFreezeMicro.laws bool_lattice bad_micro.
Proof.
  constructor.
  - apply simple_laws; intros; reflexivity.
  - constructor; intros; reflexivity.
  - intros []; split; reflexivity.
  - intros [] [] []; split; reflexivity.
  - intros [] [] [] Hle; cbn in *; congruence.
  - intros; reflexivity.
  - intros [] [] []; split; reflexivity.
Qed.

(** The new field rejects true-to-false function comparison at the true value. *)
Theorem bad_micro_new_laws_rejected : ~ micro_laws bool_lattice bad_micro.
Proof.
  intro Hlaw; pose proof (apply_order Hlaw true false true eq_refl) as Hbound.
  discriminate Hbound.
Qed.

Definition reachability_micro : Micro.t bool bool :=
  Micro.of_pure true andb andb bool_lattice.

(** Ordinary Boolean function order gives a useful nonunit lawful control. *)
Theorem reachability_micro_laws : micro_laws bool_lattice reachability_micro.
Proof.
  constructor.
  - exact bool_laws.
  - exact bool_lub.
  - intros []; split; reflexivity.
  - intros [] [] []; split; reflexivity.
  - intros [] [] [] Hle; cbn in *; congruence.
  - intros [] [] [] Hle; cbn in *; congruence.
  - intros [] [] [] [] Hf Hg; cbn in *; congruence.
  - intros [] [] []; split; reflexivity.
Qed.

Definition bad_order_ide : Ide.t nat nat nat unit bool bool :=
  Ide.Make no_flow bool_lattice bad_micro (fun _ _ _ => Cost.ret true).

Example bad_order_empty_jump_passes_enumerated_checker :
  check_jumps bad_order_ide 0 Map.empty = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example bad_order_accepted_bound_loses_identity_application :
  (Micro.apply bad_micro (Micro.id bad_micro) true,
   Micro.apply bad_micro (Jump.lookup bad_order_ide Map.empty ((0, None), (0, None))) true) =
    (true, false).
Proof.
  vm_compute; reflexivity.
Qed.

Definition unsupported_cfg : Cfg.t nat nat :=
  Cfg.Make (Graph.of_pure [0] [0; 1; 2]
    (fun n => match n with 0 => [0] | 1 => [1] | _ => [] end)
    (fun e => e) (fun e => S e)) nat_encoding nat_encoding.

Definition unsupported_flow : Ifds.t nat nat nat unit :=
  Ifds.of_pure (Icfg.of_pure unsupported_cfg nat_encoding (fun _ => Icfg.Internal))
    unit_encoding []
    (fun e d => match e, d with
      | 0, None => [Some tt]
      | 1, Some _ => [d]
      | _, _ => []
      end).

(** A generated ordinary fact outside the declared inventory violates flow closure. *)
Theorem unsupported_flow_not_closed : ~ Ifds.flow_closed unsupported_flow.
Proof.
  intro Hclosed.
  assert (Hedge : In 0 (Cfg.edges unsupported_cfg)) by (vm_compute; auto).
  exact (Hclosed 0 None (Some tt) Hedge I (or_introl eq_refl)).
Qed.

Example unsupported_seed_rejected : ~ Ifds.seed_supported unsupported_flow (0, Some tt).
Proof.
  vm_compute; tauto.
Qed.

Example zero_seed_supported : Ifds.seed_supported unsupported_flow (0, None).
Proof.
  vm_compute; exact I.
Qed.

Definition unsupported_ide := Ifds.as_ide unsupported_flow.
Definition unsupported_jump := Map.of_list positive_encoding
  [(encode (Jump.enc unsupported_ide) ((0, None), (0, None)), true);
   (encode (Jump.enc unsupported_ide) ((0, None), (1, Some tt)), true)].

Example unsupported_jump_passes_enumerated_checker :
  check_jumps unsupported_ide 0 unsupported_jump = true.
Proof.
  vm_compute; reflexivity.
Qed.

(** Row reflection alone does not cover a two-edge path through an unlisted input fact. *)
Example omitted_fact_support_is_not_a_path_theorem :
  Stack.balanced unsupported_flow 0 None 2 (Some tt) /\
  Jump.lookup unsupported_ide unsupported_jump ((0, None), (2, Some tt)) = false.
Proof.
  split.
  - eapply Stack.next.
    + apply (Stack.internal unsupported_flow 0 None (Some tt) []); vm_compute; auto.
    + eapply Stack.next.
      * apply (Stack.internal unsupported_flow 1 (Some tt) (Some tt) []); vm_compute; auto.
      * apply Stack.refl.
  - vm_compute; reflexivity.
Qed.

Inductive affine_fn :=
  | FDead
  | FLinear (scale offset : Z)
  | FAny.

Definition affine_le f g :=
  match f, g with
  | FDead, _ | _, FAny => true
  | FLinear a b, FLinear c d => Z.eqb a c && Z.eqb b d
  | _, _ => false
  end.

Definition affine_join f g :=
  match f, g with
  | FDead, _ => g
  | _, FDead => f
  | FLinear a b, FLinear c d =>
    if Z.eqb a c && Z.eqb b d then f else FAny
  | _, _ => FAny
  end.

Definition noncommuting_micro : Micro.t point affine_fn :=
  Micro.of_pure (FLinear 1 0)
    (fun f g => match f, g with
      | FDead, _ | _, FDead => FDead
      | FLinear a b, FLinear c d => FLinear (a * c) (a * d + b)
      | _, _ => FAny
      end)
    (fun f x => match f, x with
      | FDead, _ | _, PBot => PBot
      | FLinear a b, PVal z => PVal (a * z + b)
      | _, _ => PTop
      end) (simple affine_le FDead affine_join).

Definition noncommuting_ide : Ide.t nat nat nat unit point affine_fn :=
  Ide.Make affine_ifds point_lattice noncommuting_micro
    (fun _ _ _ => Cost.ret (FLinear 1 0)).

Definition noncommuting_row :=
  Jump.Return (0, @None unit)
    (Jump.Arc 0 (0, None) (1, None) (Icfg.Call 7) (FLinear 1 1))
    (Jump.Arc 2 (2, None) (3, None) (Icfg.Return 7) (FLinear 1 3)).

Example matched_return_composition_is_not_reversed :
  (Cost.value (Jump.rhs_c noncommuting_ide
    (fun k => Cost.ret (if Nat.eqb (fst (fst k)) 1 then FLinear 2 0 else FLinear 1 0))
    noncommuting_row),
   Micro.apply noncommuting_micro
     (Micro.compose noncommuting_micro (FLinear 1 1)
       (Micro.compose noncommuting_micro (FLinear 2 0) (FLinear 1 3))) (PVal 4)) =
    (FLinear 2 5, PVal 15).
Proof.
  vm_compute; reflexivity.
Qed.
