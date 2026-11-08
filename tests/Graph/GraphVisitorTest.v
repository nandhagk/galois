(** * Visitor state and tick observations

    Event dispatch retains callback charges and product visitors keep independent state.
    For example, a three-event trace increments a counter three times.
    Builds on: GraphVisitor. *)

From Stdlib Require Import List NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Graph Require Import GraphVisitor GraphSearchSpec.
Import List.ListNotations Cost.Notations.

Definition counter : Visitor.t unit nat :=
  Visitor.of_pure (fun _ _ s => S s) (fun _ _ _ _ s => S s) (fun _ _ s => S s).

Definition short_trace :=
  [Search.Enter 1%positive None; Search.Edge tt 1%positive 1%positive Search.Back;
    Search.Exit 1%positive None].

Definition counted :=
  let* s := Visitor.apply_c counter (Search.Enter 1%positive None) 0 in
  let* s := Visitor.apply_c counter (Search.Edge tt 1%positive 1%positive Search.Back) s in
  Visitor.apply_c counter (Search.Exit 1%positive None) s.

Example count_state_ticks : (Cost.value counted, Cost.ticks counted) = (3, 6%N).
Proof.
  vm_compute. reflexivity.
Qed.

Example paired_state_ticks :
  (Cost.value (Visitor.apply_c (Visitor.pair counter counter)
    (Search.Enter 1%positive None) (0, 5)),
   Cost.ticks (Visitor.apply_c (Visitor.pair counter counter)
    (Search.Enter 1%positive None) (0, 5))) = ((1, 6), 5%N).
Proof.
  vm_compute. reflexivity.
Qed.

Example noop_empty_state :
  Visitor.apply (@Visitor.noop unit (list nat)) (Search.Exit 1%positive None) [] = [].
Proof.
  vm_compute. reflexivity.
Qed.

Definition restricted :=
  Scope.Make (FinSet.of_list positive_encoding [1%positive])
    (Some (FinSet.of_list positive_encoding [1%positive; 2%positive])).

Example scope_blocks_and_bounds :
  (Scope.admits restricted 1%positive, Scope.admits restricted 2%positive,
    Scope.admits restricted 3%positive) = (false, true, false).
Proof.
  vm_compute. reflexivity.
Qed.

Definition numbered : Search.result unit :=
  Search.Result [1%positive; 2%positive; 3%positive] [2%positive; 1%positive; 3%positive]
    (Map.of_list positive_encoding [(2%positive, (tt, 1%positive))])
    (Map.of_list positive_encoding
      [(1%positive, 1%positive); (2%positive, 2%positive); (3%positive, 3%positive)])
    (Map.of_list positive_encoding
      [(2%positive, 1%positive); (1%positive, 2%positive); (3%positive, 3%positive)])
    (FinSet.of_list positive_encoding [1%positive; 2%positive; 3%positive]).

Example all_edge_classes :
  (Search.classify numbered 1%positive 2%positive,
   Search.classify numbered 2%positive 1%positive,
   Search.classify numbered 1%positive 3%positive,
   Search.classify numbered 3%positive 2%positive) =
  (Some Search.Tree, Some Search.Back, Some Search.Forward, Some Search.Cross).
Proof.
  vm_compute. reflexivity.
Qed.

Example missing_numbers_rejected : Search.classify numbered 9%positive 1%positive = None.
Proof.
  vm_compute. reflexivity.
Qed.

(** The scope cost equation applies to arbitrary raw blocked and optional-region sets. *)
Example scope_cost_client s v :
  Cost.ticks (Scope.admits_c s v) =
    (1 + Cost.ticks (FinSet.mem_c positive_encoding v (Scope.blocked s)) +
      if FinSet.mem positive_encoding v (Scope.blocked s) then 0 else
      match Scope.within s with
      | None => 0
      | Some region => Cost.ticks (FinSet.mem_c positive_encoding v region)
      end)%N.
Proof.
  apply Scope.admits_cost_equation.
Qed.

Example scope_selected_query_ticks :
  (Cost.ticks (Scope.admits_c restricted 1%positive),
    Cost.ticks (Scope.admits_c restricted 2%positive),
    Cost.ticks (Scope.admits_c restricted 3%positive)) = (4, 9, 9)%N.
Proof.
  vm_compute. reflexivity.
Qed.
