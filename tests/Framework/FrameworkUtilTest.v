(** * Primitive callback accounting for framework edge enumeration

    Importing clients retain nonunit outgoing prices and duplicate edge occurrences.
    For example, two node callbacks priced at seven yield twenty-one enumeration ticks.
    Builds on: FrameworkUtil, GraphModel and ProgramCfg. *)

From Stdlib Require Import List NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramCfg.
From Galois.Framework Require Import FrameworkUtil.
Import List.ListNotations.

Definition priced_graph price : Graph.t bool bool :=
  Graph.Make [false] [false; true]
    (Cost.lift (fun _ => price) (fun (n : bool) => if n then [] else [false; false; true]))
    (Cost.lift (fun _ => 1%N) (fun _ => false))
    (Cost.lift (fun _ => 1%N) (fun _ => true)).
Definition priced_cfg price := Cfg.Make (priced_graph price) bool_encoding bool_encoding.

(** A symbolic importing client discharges the primitive outgoing-callback duty for every price. *)
Example varying_price_bound price :
  (Cost.ticks (fw_edges_c (priced_cfg price)) <= 2 * (2 + price) + 3)%N.
Proof.
  change (Cost.ticks (fw_edges_c (priced_cfg price)) <=
    N.of_nat (length (Graph.nodes (Cfg.graph (priced_cfg price)))) * (2 + price) +
      N.of_nat (length (Cfg.edges (priced_cfg price))))%N.
  apply fw_edges_cost; intros n Hn; change (price <= price)%N; apply N.le_refl.
Qed.

Example duplicate_edges :
  Cost.value (fw_edges_c (priced_cfg 7%N)) = [false; false; true].
Proof.
  vm_compute; reflexivity.
Qed.

Example nonunit_reader_charge :
  Cost.ticks (fw_edges_c (priced_cfg 7%N)) = 21%N.
Proof.
  vm_compute; reflexivity.
Qed.

Definition empty_cfg :=
  Cfg.Make (Graph.Make [] [] (Cost.lift (fun _ => 99%N) (fun (_ : bool) => [false]))
    (Cost.ret (A := bool)) (Cost.ret (A := bool))) bool_encoding bool_encoding.

Example empty_enumeration :
  Cost.value (fw_edges_c empty_cfg) = [] /\ Cost.ticks (fw_edges_c empty_cfg) = 0%N.
Proof.
  vm_compute; split; reflexivity.
Qed.

(** A second importing client composes the general flattening contract with arbitrary callback data. *)
Example symbolic_flatten {A B} (f : A -> Cost.t (list B)) xs price :
  (forall x, In x xs -> (Cost.ticks (f x) <= price)%N) ->
  (Cost.ticks (fw_flat_map_c f xs) <= N.of_nat (length xs) * (2 + price) +
    N.of_nat (length (flat_map (fun x => Cost.value (f x)) xs)))%N.
Proof.
  apply fw_flat_map_cost_bound.
Qed.
