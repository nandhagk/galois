(** * Graph preparation

    Preparation caches predecessor occurrences and graph sizes.
    For example, parallel edges contribute repeated predecessors.
    Builds on: graph data and the public preparation signature. *)

From Stdlib Require Import List NArith PArith.
From Argent Require Import Time Tactics Std BigO.
From Galois.Base Require Import Trie.
From Galois.Graph Require Import Data DigraphSig.

Module DigraphCode <: DIGRAPH_OPS.
  Definition add_pred (u v : positive) (p : ptrie (list positive)) :=
    PTrieCode.set v (u :: match trie_get v p with Some vs => vs | None => nil end) p.

  Definition prepare (g : digraph) : prepared :=
    let predecessors :=
      fold_right (fun u p => fold_right (add_pred u) p (succs g u)) Empty (verts g) in
    Prepared g predecessors (N.of_nat (length (verts g))) (N.of_nat (graph_e g)).
End DigraphCode.

Module Digraph <: DIGRAPH.
  Include DigraphCode.

  Lemma prepare_base : forall g, base (prepare g) = g.
  Proof.
    reflexivity.
  Qed.

  Lemma prepare_correct : forall g, prepared_ok (prepare g).
  Proof. Admitted. (* SIG-QUESTION: prepare_ready assumes a well-formed source graph. *)
End Digraph.

Module DigraphT <: DIGRAPH_T.
  Include Digraph.
  TimeFun add_pred.
  TimeFun prepare.
  Definition c_prepare : N := 1%N. (* STUB *)

  Lemma T_prepare_le : forall g,
    (T_prepare g <= c_prepare * N.of_nat (graph_n g + graph_e g + 1) *
      N.of_nat (graph_width g + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma prepare_bigO : bigO (fun _ => True)
    (fun g => N.of_nat ((graph_n g + graph_e g + 1) * (graph_width g + 1))) T_prepare.
  Proof. Admitted. (* STUB *)
End DigraphT.
