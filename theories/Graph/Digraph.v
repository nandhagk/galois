(** * Graph preparation

    Preparation caches predecessor occurrences and graph sizes.
    For example, parallel edges contribute repeated predecessors.
    Builds on: graph data and the public preparation signature. *)

From Stdlib Require Import List NArith PArith Sorting.Permutation.
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

  (** Inserting one predecessor changes exactly the row selected by its target. *)
  Local Lemma add_pred_lookup u v w p :
    (match trie_get w (add_pred u v p) with Some vs => vs | None => nil end) =
    if Pos.eqb w v then
      u :: match trie_get w p with Some vs => vs | None => nil end
    else match trie_get w p with Some vs => vs | None => nil end.
  Proof.
    unfold add_pred. destruct (Pos.eqb w v) eqn:Heq.
    - apply Pos.eqb_eq in Heq. subst w. rewrite PTrie.get_set_same. reflexivity.
    - apply Pos.eqb_neq in Heq. rewrite PTrie.get_set_other by exact Heq. reflexivity.
  Qed.

  (** A successor row contributes one predecessor for each matching occurrence. *)
  Local Lemma predecessor_row u vs p v :
    (match trie_get v (fold_right (add_pred u) p vs) with
     | Some us => us | None => nil end) =
    map (fun _ => u) (filter (Pos.eqb v) vs) ++
      match trie_get v p with Some us => us | None => nil end.
  Proof.
    induction vs as [|w vs IH].
    - reflexivity.
    - cbn [fold_right filter]. rewrite add_pred_lookup.
      destruct (Pos.eqb v w); cbn [map app]; now rewrite IH.
  Qed.

  (** Folding source rows retains their order and every repeated occurrence. *)
  Local Lemma predecessor_rows g vs p v :
    (match trie_get v
      (fold_right (fun u acc => fold_right (add_pred u) acc (succs g u)) p vs) with
     | Some us => us | None => nil end) =
    flat_map (fun u => map (fun _ => u) (filter (Pos.eqb v) (succs g u))) vs ++
      match trie_get v p with Some us => us | None => nil end.
  Proof.
    induction vs as [|u vs IH].
    - reflexivity.
    - cbn [fold_right flat_map]. rewrite predecessor_row, IH, app_assoc. reflexivity.
  Qed.

  Lemma prepare_base : forall g, base (prepare g) = g.
  Proof.
    reflexivity.
  Qed.

  (** Preparation counts and indexes every source occurrence without a well-formedness premise. *)
  Lemma prepare_correct : forall g, prepared_ok (prepare g).
  Proof.
    intros [vs rows]. unfold prepared_ok, prepare.
    cbn [nv ne base graph_n verts nodes]. split; [reflexivity|].
    split; [reflexivity|]. intro v. unfold preds.
    rewrite predecessor_rows, PTrie.get_empty, app_nil_r. reflexivity.
  Qed.
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
