(** * Preparation bounds on actual supplied inventories

    Computed controls retain callback work and duplicate inventory occurrences.
    For example, unused duplicate facts increase preparation even when the graph has no edges.
    Builds on: FrameworkTabPrepareCost and the generated call-chain presentation. *)

From Stdlib Require Import List NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramCfg ProgramIcfg.
From Galois.Framework Require Import FrameworkUtil FrameworkIfds FrameworkIde FrameworkTabulate
  FrameworkTabPrepareCost.
From Galois.Tests.Framework Require Import FrameworkTabCostTest.
Import List.ListNotations.

(** Pure call-chain presentations discharge the primitive preparation domain at every size. *)
Example chain_callbacks n :
  TabPrepareCost.callbacks (Ifds.as_ide (call_chain n)) 1 1 1 1 1 0 1.
Proof.
  constructor; intros.
  all: first [change (1 <= 1)%N; reflexivity | change (0 <= 0)%N; reflexivity].
Qed.

(** Every supplied chain imports the arc bound with its actual primitive callbacks. *)
Example arbitrary_chain_arc_bound n :
  (Cost.ticks (Jump.arcs_c (Ifds.as_ide (call_chain n))) <=
    TabPrepareCost.arcs_charge (Ifds.as_ide (call_chain n)) 1 1 1 1 1 0 1)%N.
Proof.
  apply TabPrepareCost.arcs_cost, chain_callbacks.
Qed.

Definition chain_preparation_bound n :=
  TabPrepareCost.prepare_charge (Ifds.as_ide (call_chain n)) 1 1 1 1 1 0 1 1 1 8 1.

Example short_chain_preparation_fits_bound :
  (Cost.ticks (Tab.prepare_c (Ifds.as_ide (call_chain 2)) 0%nat) <=
    chain_preparation_bound 2)%N.
Proof.
  vm_compute; discriminate.
Qed.

Example doubled_chain_preparation_fits_bound :
  (Cost.ticks (Tab.prepare_c (Ifds.as_ide (call_chain 4)) 0%nat) <=
    chain_preparation_bound 4)%N.
Proof.
  vm_compute; discriminate.
Qed.

(** Full preparation derives the source index charge from the original scalar callbacks. *)
Example importing_short_chain_preparation_bound :
  (Cost.ticks (Tab.prepare_c (Ifds.as_ide (call_chain 2)) 0%nat) <=
    chain_preparation_bound 2)%N.
Proof.
  apply TabPrepareCost.prepare_cost.
  - apply chain_callbacks.
  - apply FrameworkKey.pair_laws; [exact nat_encoding_laws|].
    apply FrameworkKey.option_laws; exact unit_encoding_laws.
  - intros e He; vm_compute in He.
    repeat destruct He as [He|He]; try contradiction; subst e;
      vm_compute; split; discriminate.
  - intros d Hd; inversion Hd.
Qed.

Definition duplicate_facts : Ifds.t nat nat nat unit :=
  Ifds.of_pure
    (Icfg.of_pure
      (Cfg.Make (Graph.of_pure [] [0] (fun _ => []) (fun e => e) (fun e => e))
        nat_encoding nat_encoding)
      nat_encoding (fun _ => Icfg.Internal))
    unit_encoding [tt; tt] (fun _ d => [d]).

Example duplicate_unused_facts_remain_in_inventory :
  length (Tab.inventory (Tab.prepare (Ifds.as_ide duplicate_facts) 9)) = 3%nat.
Proof.
  vm_compute; reflexivity.
Qed.

Example duplicate_unused_facts_still_cost_work :
  (Cost.ticks (Tab.prepare_c (Ifds.as_ide (call_chain 0)) 9%nat) <
    Cost.ticks (Tab.prepare_c (Ifds.as_ide duplicate_facts) 9%nat))%N.
Proof.
  vm_compute; reflexivity.
Qed.

Example unlisted_raw_start_retains_its_actual_root_key :
  Tab.inventory (Tab.prepare (Ifds.as_ide duplicate_facts) 9) =
    [((9, None), (9, None)); ((9, Some tt), (9, Some tt)); ((9, Some tt), (9, Some tt))].
Proof.
  vm_compute; reflexivity.
Qed.
