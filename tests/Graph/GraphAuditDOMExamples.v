(** * Dominator audit examples

    These examples exercise forest indexing and captured encoder operands.
    For example, a child is inserted into the row for its actual parent.
    Builds on: GraphAuditDominators and the graph and collection models. *)

From Stdlib Require Import List Bool PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsAuditMap.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDominators GraphAuditDfs
  GraphAuditDominators.
Import List.ListNotations.

(** Encode a vertex while recording the argument passed to the callback. *)
Definition dom_example_encode (v : nat) : positive * list nat :=
  (encode nat_encoding v, [100 + v]).

(** Recognize a child lookup that retained its actual encoder receipt. *)
Definition dom_example_child_read (event : audit_dom_source_event nat nat nat) : bool :=
  match event with
  | DomSourceChild (AuditMapGet key _ _ _ body _) =>
    Nat.eqb key 0 &&
      match body with
      | [item] => Nat.eqb item 100
      | _ => false
      end
  | _ => false
  end.

Example dom_children_empty :
  audit_dom_children_counted (E := nat) nat_encoding [] = (Map.empty, [AuditDomCase 0]).
Proof.
  reflexivity.
Qed.

Example dom_children_shared_parent :
  fst (audit_dom_children_counted (E := nat) nat_encoding [(1, 0); (2, 0)]) =
    Map.set nat_encoding 0 [1; 2] Map.empty /\
  length (snd (audit_dom_children_counted (E := nat) nat_encoding [(1, 0); (2, 0)])) = 7.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example dom_source_child_receipt :
  fst (audit_dom_source_children (E := nat) dom_example_encode [(1, 0)]) =
    Map.set nat_encoding 0 [1] Map.empty /\
  existsb dom_example_child_read
    (snd (audit_dom_source_children (E := nat) dom_example_encode [(1, 0)])) = true.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example dom_roots_parentless_and_child :
  fst (audit_dom_roots_counted (E := nat) nat_encoding
    (Map.set nat_encoding 1 0 Map.empty) [0; 1]) = [0].
Proof.
  reflexivity.
Qed.

(** The edge from zero to one gives a nonempty valid immediate-dominator map. *)
Definition dom_example_graph : Graph.t nat nat :=
  {| Graph.entries := [0];
      Graph.nodes := [0; 1];
      Graph.out := fun v => if Nat.eqb v 0 then [7] else [];
      Graph.source := fun _ => 0;
      Graph.target := fun _ => 1 |}.

Example dom_checker_accepts_and_rejects :
  let p := prepare nat_encoding dom_example_graph in
  check_idom p (Map.set nat_encoding 1 0 Map.empty) = true /\
  check_idom p Map.empty = false.
Proof.
  vm_compute; split; reflexivity.
Qed.

(** The target callback records the edge used by the initial DFS. *)
Definition dom_example_target (edge : nat) : nat * list nat := (1, [200 + edge]).

(** The source search uses these two observable callbacks. *)
Definition dom_example_callbacks : audit_dfs_callback_model nat nat nat :=
  AuditDfsCallbackModel nat nat nat dom_example_target dom_example_encode.

(** Recognize an initial DFS target capture with its original edge and body. *)
Definition dom_example_initial_target (event : audit_dom_source_event nat nat nat) : bool :=
  match event with
  | DomSourceInitialDfs (_, calls) =>
    existsb (fun call =>
      match call with
      | AuditGraphTargetCapture _ _ _ edge value body =>
        Nat.eqb edge 7 && Nat.eqb value 1 &&
          match body with
          | [item] => Nat.eqb item 207
          | _ => false
          end
      | AuditGraphEncodeCapture _ _ _ _ _ _ => false
      end) calls
  | _ => false
  end.

Example dom_source_search_keeps_target_receipt :
  let p := prepare nat_encoding dom_example_graph in
  let parents := Map.set nat_encoding 1 0 Map.empty in
  let receipt := audit_dom_search_source_counted p parents dom_example_callbacks in
  audit_dom_source_result receipt = dom_search p parents /\
  existsb dom_example_initial_target (audit_dom_source_events receipt) = true.
Proof.
  vm_compute; split; reflexivity.
Qed.

(** The counted tree retains its supplied parent and the two distinct dominance answers. *)
Example dom_counted_tree_two_vertices :
  let p := prepare nat_encoding dom_example_graph in
  let parents := Map.set nat_encoding 1 0 Map.empty in
  let tree := fst (audit_dom_tree_counted p parents) in
  Map.get nat_encoding 1 (idom tree) = Some 0 /\
  dominates_b nat_encoding tree 0 1 = true /\
  dominates_b nat_encoding tree 1 0 = false.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.
