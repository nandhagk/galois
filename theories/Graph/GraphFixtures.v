(** * Hand-written graph certificates

    Named graphs carry parent maps and token lists independently of graph producers.
    For example, a diamond's join has its entry as immediate dominator.
    Builds on: GraphPrepared, GraphCheckDom, GraphCheckWto and BaseMap. *)

From Stdlib Require Import List Bool Arith PArith.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Graph Require Import GraphModel GraphPrepared GraphDomSpec GraphHierSpec
  GraphCheckWto GraphCheckDom.
Import List.ListNotations.
Close Scope positive_scope.

Module Fixtures.

Definition Edge := (nat * nat)%type.

Definition graph roots nodes (edges : list Edge) :=
  Graph.of_pure roots nodes (fun v => filter (fun e => Nat.eqb (fst e) v) edges) fst snd.

Definition prepare roots nodes edges := Prepared.prepare nat_encoding (graph roots nodes edges).

Definition parents (bindings : list (positive * positive)) :=
  Map.of_list positive_encoding bindings.

(** Hand-written binding lists always produce well-formed candidate maps. *)
Theorem parents_wf bindings : Map.wf positive_encoding (parents bindings).
Proof.
  apply Map.wf_of_list.
Qed.

Local Lemma prepare_ready roots nodes edges :
  NoDup nodes -> incl roots nodes ->
  (forall a b, In (a, b) edges -> In a nodes /\ In b nodes) ->
  NoDup edges -> Prepared.ready (prepare roots nodes edges).
Proof.
  intros Hnodes Hroots Hendpoints Hedges.
  apply Prepared.prepare_ready; [exact nat_encoding_laws| |].
  - constructor.
    + exact Hnodes.
    + exact Hroots.
    + intros v [a b] Hin. apply filter_In in Hin. destruct Hin as [_ Hsame].
      cbn in Hsame. now apply Nat.eqb_eq in Hsame.
    + intros v [a b] Hv Hin. apply filter_In in Hin.
      destruct Hin as [Hin _]. exact (proj2 (Hendpoints a b Hin)).
  - intro v. apply NoDup_filter. exact Hedges.
Qed.

(** Close finite node, root and endpoint obligations of these explicit fixtures. *)
Local Ltac solve_fixture :=
  apply prepare_ready;
  [ repeat (apply NoDup_cons; [cbn; intuition congruence|]); apply NoDup_nil
  | intros x Hin; vm_compute in Hin |- *; intuition congruence
  | intros a b Hin; vm_compute in Hin |- *; intuition congruence
  | repeat (apply NoDup_cons; [cbn; intuition congruence|]); apply NoDup_nil ].

Module Line.

(** The line is 1 -> 2 -> 3 -> 4. *)
Definition prepared := prepare [1] [1; 2; 3; 4] [(1, 2); (2, 3); (3, 4)].
Definition parents := parents [(2, 1); (3, 2); (4, 3)]%positive.
Definition wto := [Wto.WVertex 1; Wto.WVertex 2; Wto.WVertex 3; Wto.WVertex 4]%positive.

(** The line satisfies the graph, outgoing-uniqueness and preparation invariants. *)
Theorem fixture_ready : Prepared.ready prepared.
Proof.
  solve_fixture.
Qed.

(** The hand-written line order satisfies the unrestricted weak-order contract. *)
Theorem wto_valid : Wto.valid prepared (Prepared.entry_ids prepared) wto.
Proof.
  apply (proj1 (WtoCheck.check_correct prepared _ wto fixture_ready)).
  vm_compute. reflexivity.
Qed.

(** The line's parent representation is certified independently of its semantic checker. *)
Theorem parents_wf : Map.wf positive_encoding parents.
Proof.
  apply Map.wf_of_list.
Qed.

Definition tree := DomCheck.of_parents prepared parents.

(** The supplied line parents and their reference numbering form an exact dominator tree. *)
Theorem tree_exact : Dom.exact prepared tree.
Proof.
  apply DomCheck.check_sound; [exact fixture_ready|exact parents_wf|].
  vm_compute. reflexivity.
Qed.

End Line.

Module Diamond.

(** The entry branches to 2 and 3, which both enter the join 4. *)
Definition prepared := prepare [1] [1; 2; 3; 4] [(1, 2); (1, 3); (2, 4); (3, 4)].
Definition parents := parents [(2, 1); (3, 1); (4, 1)]%positive.
Definition wto := [Wto.WVertex 1; Wto.WVertex 2; Wto.WVertex 3; Wto.WVertex 4]%positive.

(** The diamond satisfies the graph, outgoing-uniqueness and preparation invariants. *)
Theorem fixture_ready : Prepared.ready prepared.
Proof.
  solve_fixture.
Qed.

(** The hand-written diamond order satisfies the unrestricted weak-order contract. *)
Theorem wto_valid : Wto.valid prepared (Prepared.entry_ids prepared) wto.
Proof.
  apply (proj1 (WtoCheck.check_correct prepared _ wto fixture_ready)).
  vm_compute. reflexivity.
Qed.

(** Public map construction certifies the diamond's parent representation. *)
Theorem parents_wf : Map.wf positive_encoding parents.
Proof.
  apply Map.wf_of_list.
Qed.

Definition tree := DomCheck.of_parents prepared parents.

(** Both branches and the join have exactly the supplied immediate dominators. *)
Theorem tree_exact : Dom.exact prepared tree.
Proof.
  apply DomCheck.check_sound; [exact fixture_ready|exact parents_wf|].
  vm_compute. reflexivity.
Qed.

End Diamond.

Module JoinLoop.

(** The diamond's join 4 has the additional self-loop 4 -> 4. *)
Definition prepared :=
  prepare [1] [1; 2; 3; 4] [(1, 2); (1, 3); (2, 4); (3, 4); (4, 4)].
Definition parents := parents [(2, 1); (3, 1); (4, 1)]%positive.
Definition wto :=
  [Wto.WVertex 1; Wto.WVertex 2; Wto.WVertex 3; Wto.WOpen 4; Wto.WClose]%positive.

(** The looped diamond satisfies the graph and preparation invariants. *)
Theorem fixture_ready : Prepared.ready prepared.
Proof.
  solve_fixture.
Qed.

(** The join's opening token accounts for its self-loop. *)
Theorem wto_valid : Wto.valid prepared (Prepared.entry_ids prepared) wto.
Proof.
  apply (proj1 (WtoCheck.check_correct prepared _ wto fixture_ready)).
  vm_compute. reflexivity.
Qed.

(** Public map construction certifies the looped diamond's parent representation. *)
Theorem parents_wf : Map.wf positive_encoding parents.
Proof.
  apply Map.wf_of_list.
Qed.

Definition tree := DomCheck.of_parents prepared parents.

(** The join's self-loop does not change the supplied immediate dominators. *)
Theorem tree_exact : Dom.exact prepared tree.
Proof.
  apply DomCheck.check_sound; [exact fixture_ready|exact parents_wf|].
  vm_compute. reflexivity.
Qed.

End JoinLoop.

Module NestedLoop.

(** The outer cycle is 1 -> 2 -> 3 -> 4 -> 1 and the inner back edge is 3 -> 2. *)
Definition prepared := prepare [1] [1; 2; 3; 4] [(1, 2); (2, 3); (3, 2); (3, 4); (4, 1)].
Definition parents := parents [(2, 1); (3, 2); (4, 3)]%positive.
Definition wto :=
  [Wto.WOpen 1; Wto.WOpen 2; Wto.WVertex 3; Wto.WClose; Wto.WVertex 4; Wto.WClose]%positive.

(** Both nested cycles have valid endpoints and duplicate-free adjacency. *)
Theorem fixture_ready : Prepared.ready prepared.
Proof.
  solve_fixture.
Qed.

(** Both backward edges target the corresponding enclosing loop heads. *)
Theorem wto_valid : Wto.valid prepared (Prepared.entry_ids prepared) wto.
Proof.
  apply (proj1 (WtoCheck.check_correct prepared _ wto fixture_ready)).
  vm_compute. reflexivity.
Qed.

(** Public map construction certifies the nested-loop parent representation. *)
Theorem parents_wf : Map.wf positive_encoding parents.
Proof.
  apply Map.wf_of_list.
Qed.

Definition tree := DomCheck.of_parents prepared parents.

(** The nested-loop dominator tree follows the forward chain from entry 1. *)
Theorem tree_exact : Dom.exact prepared tree.
Proof.
  apply DomCheck.check_sound; [exact fixture_ready|exact parents_wf|].
  vm_compute. reflexivity.
Qed.

End NestedLoop.

Module TwoEntry.

(** Entries 1 and 2 both reach 3, followed by the shared tail 3 -> 4. *)
Definition prepared := prepare [1; 2] [1; 2; 3; 4] [(1, 3); (2, 3); (3, 4)].
Definition parents := parents [(4, 3)]%positive.
Definition wto := [Wto.WVertex 1; Wto.WVertex 2; Wto.WVertex 3; Wto.WVertex 4]%positive.

(** Both entries are valid and the shared-tail indexes satisfy preparation laws. *)
Theorem fixture_ready : Prepared.ready prepared.
Proof.
  solve_fixture.
Qed.

(** The shared-tail order covers paths from both graph entries. *)
Theorem wto_valid : Wto.valid prepared (Prepared.entry_ids prepared) wto.
Proof.
  apply (proj1 (WtoCheck.check_correct prepared _ wto fixture_ready)).
  vm_compute. reflexivity.
Qed.

(** Public map construction certifies the shared-tail parent representation. *)
Theorem parents_wf : Map.wf positive_encoding parents.
Proof.
  apply Map.wf_of_list.
Qed.

Definition tree := DomCheck.of_parents prepared parents.

(** Neither entry dominates the join and node 3 immediately dominates the tail node 4. *)
Theorem tree_exact : Dom.exact prepared tree.
Proof.
  apply DomCheck.check_sound; [exact fixture_ready|exact parents_wf|].
  vm_compute. reflexivity.
Qed.

End TwoEntry.

Module SelfLoop.

(** The sole entry has the self-loop 1 -> 1. *)
Definition prepared := prepare [1] [1] [(1, 1)].
Definition parents := parents [].
Definition wto := [Wto.WOpen 1; Wto.WClose]%positive.

(** The singleton cyclic graph satisfies all preparation invariants. *)
Theorem fixture_ready : Prepared.ready prepared.
Proof.
  solve_fixture.
Qed.

(** The empty-body component is a valid order for the self-loop. *)
Theorem wto_valid : Wto.valid prepared (Prepared.entry_ids prepared) wto.
Proof.
  apply (proj1 (WtoCheck.check_correct prepared _ wto fixture_ready)).
  vm_compute. reflexivity.
Qed.

(** The empty parent map has a public representation certificate. *)
Theorem parents_wf : Map.wf positive_encoding parents.
Proof.
  apply Map.wf_of_list.
Qed.

Definition tree := DomCheck.of_parents prepared parents.

(** A singleton self-loop has no strict immediate dominator. *)
Theorem tree_exact : Dom.exact prepared tree.
Proof.
  apply DomCheck.check_sound; [exact fixture_ready|exact parents_wf|].
  vm_compute. reflexivity.
Qed.

End SelfLoop.

Module Irreducible.

(** Entry 1 reaches both nodes of the cycle 2 -> 3 -> 2, giving two cycle entries. *)
Definition prepared := prepare [1] [1; 2; 3] [(1, 2); (1, 3); (2, 3); (3, 2)].
Definition parents := parents [(2, 1); (3, 1)]%positive.
Definition wto := [Wto.WVertex 1; Wto.WOpen 2; Wto.WVertex 3; Wto.WClose]%positive.

(** The irreducible graph has valid entries and duplicate-free labelled outgoing lists. *)
Theorem fixture_ready : Prepared.ready prepared.
Proof.
  solve_fixture.
Qed.

(** The weak order accepts both entries into the irreducible cycle. *)
Theorem wto_valid : Wto.valid prepared (Prepared.entry_ids prepared) wto.
Proof.
  apply (proj1 (WtoCheck.check_correct prepared _ wto fixture_ready)).
  vm_compute. reflexivity.
Qed.

(** Public map construction certifies the irreducible graph's parent representation. *)
Theorem parents_wf : Map.wf positive_encoding parents.
Proof.
  apply Map.wf_of_list.
Qed.

Definition tree := DomCheck.of_parents prepared parents.

(** Both cycle nodes have entry 1 as their immediate dominator. *)
Theorem tree_exact : Dom.exact prepared tree.
Proof.
  apply DomCheck.check_sound; [exact fixture_ready|exact parents_wf|].
  vm_compute. reflexivity.
Qed.

End Irreducible.

Module Empty.

(** The empty graph has no entries, nodes, edges or parent bindings. *)
Definition prepared := prepare [] [] [].
Definition parents := parents [].
Definition wto : list Wto.token := [].

(** Empty reference preparation satisfies readiness without a nonempty-domain premise. *)
Theorem fixture_ready : Prepared.ready prepared.
Proof.
  solve_fixture.
Qed.

(** The empty token list is valid on the empty rooted graph. *)
Theorem wto_valid : Wto.valid prepared (Prepared.entry_ids prepared) wto.
Proof.
  apply (proj1 (WtoCheck.check_correct prepared _ wto fixture_ready)).
  vm_compute. reflexivity.
Qed.

(** Empty graph parents have a public representation certificate. *)
Theorem parents_wf : Map.wf positive_encoding parents.
Proof.
  apply Map.wf_of_list.
Qed.

Definition tree := DomCheck.of_parents prepared parents.

(** The empty graph has an exact empty dominator forest. *)
Theorem tree_exact : Dom.exact prepared tree.
Proof.
  apply DomCheck.check_sound; [exact fixture_ready|exact parents_wf|].
  vm_compute. reflexivity.
Qed.

End Empty.

Module Singleton.

(** A single entry without an edge has neither a strict dominator nor a cyclic token. *)
Definition prepared := prepare [1] [1] [].
Definition parents := parents [].
Definition wto := [Wto.WVertex 1]%positive.

(** The edgeless singleton satisfies the graph and preparation invariants. *)
Theorem fixture_ready : Prepared.ready prepared.
Proof.
  solve_fixture.
Qed.

(** An acyclic singleton needs a vertex token alone. *)
Theorem wto_valid : Wto.valid prepared (Prepared.entry_ids prepared) wto.
Proof.
  apply (proj1 (WtoCheck.check_correct prepared _ wto fixture_ready)).
  vm_compute. reflexivity.
Qed.

(** The edgeless singleton's empty parent map has a public representation certificate. *)
Theorem parents_wf : Map.wf positive_encoding parents.
Proof.
  apply Map.wf_of_list.
Qed.

Definition tree := DomCheck.of_parents prepared parents.

(** The singleton is its own reflexive ancestor and has no strict dominator. *)
Theorem tree_exact : Dom.exact prepared tree.
Proof.
  apply DomCheck.check_sound; [exact fixture_ready|exact parents_wf|].
  vm_compute. reflexivity.
Qed.

End Singleton.

Module Unreachable.

(** The line is accompanied by listed node 5, which has no path from entry 1. *)
Definition prepared := prepare [1] [1; 2; 3; 4; 5] [(1, 2); (2, 3); (3, 4)].
Definition parents := Line.parents.
Definition wto := Line.wto.

(** Unreachable listed nodes are allowed by readiness. *)
Theorem fixture_ready : Prepared.ready prepared.
Proof.
  solve_fixture.
Qed.

(** Listed unreachable nodes are excluded from rooted weak-order coverage. *)
Theorem wto_valid : Wto.valid prepared (Prepared.entry_ids prepared) wto.
Proof.
  apply (proj1 (WtoCheck.check_correct prepared _ wto fixture_ready)).
  vm_compute. reflexivity.
Qed.

(** The shared line parent map keeps its public representation certificate. *)
Theorem parents_wf : Map.wf positive_encoding parents.
Proof.
  apply Map.wf_of_list.
Qed.

Definition tree := DomCheck.of_parents prepared parents.

(** The dominator forest covers the line and has no binding for unreachable node 5. *)
Theorem tree_exact : Dom.exact prepared tree.
Proof.
  apply DomCheck.check_sound; [exact fixture_ready|exact parents_wf|].
  vm_compute. reflexivity.
Qed.

End Unreachable.

End Fixtures.
