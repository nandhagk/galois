(** * Importing whole-run numerical bounds

    A varying family pays for every repeated edge occurrence on infinite affine carriers.
    For example, doubling the family retains the extra preparation even when all jumps are equal.
    Builds on: FrameworkTabRunCost and the lawful affine micro algebra. *)

From Stdlib Require Import List NArith.
From Galois.Cost Require Import CostMonad CostBound.
From Galois.Base Require Import BaseEncoding.
From Galois.Lattice Require Import LatticeCore LatticeHeight.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramCfg ProgramIcfg.
From Galois.Framework Require Import FrameworkUtil FrameworkMicro FrameworkIfds FrameworkIde
  FrameworkTabulate FrameworkTabEncodingCost FrameworkTabPrepareCost FrameworkTabRunCost
  FrameworkTabJumpProgress FrameworkTabCheckCost FrameworkTabValues FrameworkTabValueRunCost
  FrameworkTabValueProgress.
From Galois.Tests.Framework Require Import FrameworkTabAffineTest.
Import List.ListNotations.

Module TabRunFamily.

Definition problem n : Ide.t unit unit unit unit LawfulAffine.value LawfulAffine.function :=
  Ide.Make
    (Ifds.of_pure
      (Icfg.of_pure
        (Cfg.Make (Graph.of_pure [tt] [tt] (fun _ => repeat tt n) (fun _ => tt) (fun _ => tt))
          unit_encoding unit_encoding)
        unit_encoding (fun _ => Icfg.Internal))
      unit_encoding [] (fun _ d => [d]))
    LawfulAffine.values LawfulAffine.micro (fun _ _ _ => Cost.ret (Micro.id LawfulAffine.micro)).

Local Lemma unit_budget x : TabEncodingCost.bounded unit_encoding x 1%N 1%N.
Proof.
  destruct x; split; reflexivity.
Qed.

Local Lemma vertex_laws n : encoding_laws (IdeValue.key_enc (problem n)).
Proof.
  apply FrameworkKey.pair_laws; [exact unit_encoding_laws|].
  apply FrameworkKey.option_laws; exact unit_encoding_laws.
Qed.

Local Lemma jump_laws n : encoding_laws (Jump.enc (problem n)).
Proof.
  apply jkey_enc_laws; exact unit_encoding_laws.
Qed.

Local Lemma primitive_duties n : TabRunCost.primitives (problem n) tt 1%N 1%N 1%N.
Proof.
  constructor.
  - intros [[] d] Hv; apply unit_budget.
  - intros [[] [[]|]] Hv; [apply unit_budget|exact Logic.I].
  - intros a Ha; apply unit_budget.
  - intros a p Ha Hkind; apply unit_budget.
  - intros f g; reflexivity.
  - intros f g; reflexivity.
  - intros f g; reflexivity.
Qed.

Local Lemma callback_duties n :
  TabPrepareCost.callbacks (problem n) 1%N 1%N 1%N 1%N 1%N 1%N 1%N.
Proof.
  constructor.
  - intros node Hnode; reflexivity.
  - intros edge Hedge; reflexivity.
  - intros edge Hedge; reflexivity.
  - intros edge Hedge; reflexivity.
  - intros edge d Hedge Hd; reflexivity.
  - intros edge d Hedge Hd; reflexivity.
  - intros edge x y Hedge Hx Hy; apply N.le_0_l.
Qed.

Local Lemma value_duties n :
  TabValueRunCost.primitives (problem n) (tt, None) 1%N 1%N 1%N.
Proof.
  constructor.
  - intros [[] d] Hv; apply unit_budget.
  - intros [[] [[]|]] Hv; [apply unit_budget|exact Logic.I].
  - intros f a; reflexivity.
  - intros a b; reflexivity.
  - intros a b; reflexivity.
Qed.

Local Lemma source_duties n edge :
  In edge (Cfg.edges (Icfg.cfg (Ifds.icfg (Ide.ifds (problem n))))) ->
  TabEncodingCost.bounded
    (Cfg.node_enc (Icfg.cfg (Ifds.icfg (Ide.ifds (problem n)))))
    (Graph.source (Cfg.graph (Icfg.cfg (Ifds.icfg (Ide.ifds (problem n))))) edge) 1%N 1%N.
Proof.
  intro Hedge; apply unit_budget.
Qed.

Local Lemma fact_duties n d :
  In d (Ifds.facts (Ide.ifds (problem n))) ->
  TabEncodingCost.bounded (Ifds.fact_enc (Ide.ifds (problem n))) d 1%N 1%N.
Proof.
  intro Hd; inversion Hd.
Qed.

(** Every fuel and family size import the raw-run bound with primitive duties closed. *)
Example raw_family n fuel :
  (Cost.ticks (Tab.raw_c (problem n) tt fuel) <=
    TabPrepareCost.prepare_charge (problem n) 1 1 1 1 1 1 1 1 1 1 1 +
    TabRunCost.initial_charge (problem n) 1 1 1 +
    (TabRunCost.step_charge (problem n) 1 1 1 + 2) * N.pos fuel)%N.
Proof.
  apply TabRunCost.raw_numeric.
  - exact (primitive_duties n).
  - exact (vertex_laws n).
  - exact (jump_laws n).
  - exact (callback_duties n).
  - exact (source_duties n).
  - exact (fact_duties n).
Qed.

(** Constructed fuel retains the full occurrence inventory on the same infinite symbolic carrier. *)
Example complete_family n :
  (Cost.ticks
    (TabJumpProgress.complete_raw_c (problem n) tt LawfulAffine.function_height) <=
    TabRunCost.complete_charge (problem n) 1 1 1 1 1 1 1 1 1 1
      (N.of_nat (bound LawfulAffine.function_height)))%N.
Proof.
  apply TabRunCost.complete_raw_numeric.
  - exact (primitive_duties n).
  - exact (vertex_laws n).
  - exact (jump_laws n).
  - exact (callback_duties n).
  - exact (source_duties n).
  - exact (fact_duties n).
Qed.

(** The same importing family stops without a fuel, output, final-map or success premise. *)
Example complete_family_stops n :
  exists stopped,
    TabJumpProgress.complete_raw (problem n) tt LawfulAffine.function_height = inr stopped /\
    Tab.work stopped = [].
Proof.
  apply TabJumpProgress.complete_raw_stops.
  - exact (vertex_laws n).
  - exact (jump_laws n).
  - exact (lat_ok _ _ LawfulAffine.micro_laws).
Qed.

(** The asymptotic client discharges the genuine duties uniformly over an unbounded input family. *)
Example complete_family_bigO :
  bigO
    (fun n => TabRunCost.complete_charge (problem n) 1 1 1 1 1 1 1 1 1 1
      (N.of_nat (bound LawfulAffine.function_height)))
    (fun n => Cost.ticks
      (TabJumpProgress.complete_raw_c (problem n) tt LawfulAffine.function_height)).
Proof.
  apply TabRunCost.complete_raw_bigO.
  - exact primitive_duties.
  - exact vertex_laws.
  - exact jump_laws.
  - exact callback_duties.
  - exact source_duties.
  - exact fact_duties.
Qed.

(** Certification imports every reached ground-checker charge on the same varying family. *)
Example certified_family n :
  (Cost.ticks (TabJumpProgress.complete_c (problem n) tt LawfulAffine.function_height) <=
    TabRunCost.complete_charge (problem n) 1 1 1 1 1 1 1 1 1 1
      (N.of_nat (bound LawfulAffine.function_height)) +
    TabCheckCost.checker_charge (problem n) 1 1 1 1 1 1 1 1 1 1)%N.
Proof.
  apply TabCheckCost.complete_cost.
  - exact (primitive_duties n).
  - exact (vertex_laws n).
  - exact (jump_laws n).
  - exact (callback_duties n).
  - exact (source_duties n).
  - exact (fact_duties n).
Qed.

(** The full certified jump asymptotic bound has all primitive duties discharged uniformly. *)
Example certified_family_bigO :
  bigO
    (fun n => (TabRunCost.complete_charge (problem n) 1 1 1 1 1 1 1 1 1 1
      (N.of_nat (bound LawfulAffine.function_height)) +
      TabCheckCost.checker_charge (problem n) 1 1 1 1 1 1 1 1 1 1)%N)
    (fun n => Cost.ticks
      (TabJumpProgress.complete_c (problem n) tt LawfulAffine.function_height)).
Proof.
  apply TabCheckCost.tabulate_bigO.
  - exact primitive_duties.
  - exact vertex_laws.
  - exact jump_laws.
  - exact callback_duties.
  - exact source_duties.
  - exact fact_duties.
Qed.

(** Arbitrary raw jump readers and affine seeds satisfy the actual value-run numerical bound. *)
Example raw_value_family n J a0 fuel :
  (Cost.ticks (TabValues.raw_c (problem n) J (tt, None) a0 fuel) <=
    TabValueRunCost.prepare_charge (problem n) 1 1 1 1 1 1 1 1 1 +
    TabValueRunCost.initial_charge (problem n) 1 1 1 +
    (TabValueRunCost.step_charge (problem n) 1 1 1 + 2) * N.pos fuel)%N.
Proof.
  apply TabValueRunCost.raw_cost.
  - exact (value_duties n).
  - exact (vertex_laws n).
  - exact (callback_duties n).
Qed.

(** The value phase constructs and charges its own value-height fuel on the same family. *)
Example complete_raw_value_family n J a0 :
  (Cost.ticks (TabValueProgress.complete_raw_c
    (problem n) J (tt, None) a0 LawfulAffine.value_height) <=
    TabValueRunCost.complete_charge (problem n) 1 1 1 1 1 1 1 1 1 1
      (N.of_nat (bound LawfulAffine.value_height)))%N.
Proof.
  apply TabValueRunCost.complete_raw_cost.
  - exact (value_duties n).
  - exact (vertex_laws n).
  - exact (callback_duties n).
Qed.

Example supplied_outgoing_occurrences n :
  N.of_nat (length (Graph.out
    (Cfg.graph (Icfg.cfg (Ifds.icfg (Ide.ifds (problem n))))) tt)) = N.of_nat n.
Proof.
  change (N.of_nat (length (repeat tt n)) = N.of_nat n).
  rewrite repeat_length; reflexivity.
Qed.

Example nonempty_complete_bound :
  (Cost.ticks
    (TabJumpProgress.complete_raw_c (problem 2) tt LawfulAffine.function_height) <=
    TabRunCost.complete_charge (problem 2) 1 1 1 1 1 1 1 1 1 1 2)%N.
Proof.
  exact (complete_family 2).
Qed.

Example doubled_complete_bound :
  (Cost.ticks
    (TabJumpProgress.complete_raw_c (problem 4) tt LawfulAffine.function_height) <=
    TabRunCost.complete_charge (problem 4) 1 1 1 1 1 1 1 1 1 1 2)%N.
Proof.
  exact (complete_family 4).
Qed.

Example empty_family_boundary :
  match TabJumpProgress.complete_raw (problem 0) tt LawfulAffine.function_height with
  | inl _ => false
  | inr _ => true
  end = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example nonempty_raw_exhaustion :
  match Tab.raw (problem 1) tt 1%positive with
  | inl _ => true
  | inr _ => false
  end = true.
Proof.
  vm_compute; reflexivity.
Qed.

End TabRunFamily.
