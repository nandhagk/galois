(** * Erased cost extraction

    The realization removes tick arithmetic from computational roots.
    For example, an extracted bind passes its result directly to its continuation.
    Builds on: CostMonad, CostList, CostLoop and OCaml extraction. *)

From Stdlib.extraction Require Import Extraction ExtrOcamlBasic.
From Galois.Cost Require Import CostMonad CostList CostLoop.

Extraction Language OCaml.
Set Extraction Output Directory ".".

(** Erasing the constructor count also covers primitive projection nodes in client terms. *)
Extraction Implicit Cost.mk [ticks].
Extract Inductive Cost.t => "Galois_cost.t" [ "Galois_cost.make" ]
  "(fun branch value -> branch value)".
Extract Constant Cost.ret => "Galois_cost.ret".
Extract Constant Cost.bind => "Galois_cost.bind".
Extract Constant Cost.value => "Galois_cost.value".
Extract Constant Cost.map => "Galois_cost.map".
Extract Constant Cost.lift => "Galois_cost.lift".
Extract Constant Cost.tick => "Galois_cost.tick".
Extract Constant Cost.step => "Galois_cost.step".
Extract Constant Cost.tick_bits => "Galois_cost.tick_bits".
Extract Constant Cost.refine => "Galois_cost.refine".
Extract Constant Cost.ticks => "(fun _ -> failwith ""GALOIS_COST_TICKS"")".

Extraction "cost_erased.ml"
  length_c app_c rev_c map_c filter_c forallb_c existsb_c
  fold_left_c fold_right_c filter_map_c find_c iterate.
