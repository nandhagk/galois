(** * Graph preparation

    Preparation caches predecessor occurrences and graph sizes.
    For example, parallel edges contribute repeated predecessors.
    Builds on: graph data and the public preparation signature. *)

From Stdlib Require Import List NArith PArith Lia Arith Sorting.Permutation.
From Argent Require Import Time Tactics Std BigO.
From Galois.Base Require Import Key Trie.
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

(** A one bit reserves the carry work needed when a unary size becomes binary. *)
Fixpoint graph_ones (p : positive) : N :=
  match p with
  | xI q => (1 + graph_ones q)%N
  | xO q => graph_ones q
  | xH => 1%N
  end.

(** Incrementing pays its carry chain from the one bits it removes. *)
Lemma graph_succ_time p :
  (Std.Pos.T_succ p + graph_ones (Pos.succ p) <= graph_ones p + 2)%N.
Proof.
  induction p as [p IH|p IH|]; time_unfold Std.Pos.T_succ;
    cbn [Pos.succ graph_ones]; time_cbn_all; nia.
Qed.

(** Unary-to-positive conversion has linear amortised cost. *)
Lemma graph_of_succ_nat_time n :
  (Key.Pos.T_of_succ_nat n + graph_ones (Pos.of_succ_nat n) <=
    3 * N.of_nat n + 2)%N.
Proof.
  induction n as [|n IH].
  - time_unfold Key.Pos.T_of_succ_nat.
    cbn [Pos.of_succ_nat graph_ones]. time_cbn. lia.
  - pose proof (graph_succ_time (Pos.of_succ_nat n)) as Hcarry.
    time_unfold Key.Pos.T_of_succ_nat.
    cbn [Pos.of_succ_nat]. rewrite Nat2N.inj_succ. time_cbn_all. nia.
Qed.

(** Computing a binary count from its unary size takes linear time. *)
Lemma graph_of_nat_time n : (TimeHelpers.N.T_of_nat n <= 3 * N.of_nat n + 3)%N.
Proof.
  destruct n as [|n].
  - time_unfold TimeHelpers.N.T_of_nat. time_cbn. lia.
  - pose proof (graph_of_succ_nat_time n) as Hconversion.
    time_unfold TimeHelpers.N.T_of_nat. rewrite Nat2N.inj_succ. time_cbn_all. nia.
Qed.

(** The structural maximum agrees with the standard natural-number maximum. *)
Local Lemma digraph_max_nat a b : graph_max a b = Nat.max a b.
Proof.
  revert b. induction a as [|a IH]; intros [|b]; cbn [graph_max Nat.max]; auto.
Qed.

(** A vertex occurrence is bounded by the width of its containing list. *)
Local Lemma digraph_vertex_width_member vs v : In v vs -> Pos.size_nat v <= vertex_width vs.
Proof.
  induction vs as [|u vs IH]; [contradiction|].
  intros [Heq|Hin]; cbn [vertex_width fold_right]; rewrite digraph_max_nat.
  - subst u. apply Nat.le_max_l.
  - eapply Nat.le_trans; [apply IH; exact Hin|apply Nat.le_max_r].
Qed.

(** Every listed successor row contributes its width to the graph's row maximum. *)
Local Lemma digraph_row_width_member g vs u : In u vs ->
  vertex_width (succs g u) <=
    fold_right (fun v w => graph_max (vertex_width (succs g v)) w) 0 vs.
Proof.
  induction vs as [|v vs IH]; [contradiction|].
  intros [Heq|Hin]; cbn [fold_right]; rewrite digraph_max_nat.
  - subst v. apply Nat.le_max_l.
  - eapply Nat.le_trans; [apply IH; exact Hin|apply Nat.le_max_r].
Qed.

(** Graph width covers all source and target occurrences, including repetitions. *)
Local Lemma digraph_width_occurrences g :
  Forall (fun u => Pos.size_nat u <= graph_width g /\
    Forall (fun v => Pos.size_nat v <= graph_width g) (succs g u)) (verts g).
Proof.
  destruct g as [vs rows]. cbn [verts]. apply Forall_forall. intros u Hin. split.
  - eapply Nat.le_trans; [apply digraph_vertex_width_member; exact Hin|].
    cbn [graph_width]. rewrite digraph_max_nat. apply Nat.le_max_l.
  - apply Forall_forall. intros v Hv.
    eapply Nat.le_trans; [apply digraph_vertex_width_member; exact Hv|].
    eapply Nat.le_trans; [apply digraph_row_width_member; exact Hin|].
    cbn [graph_width]. rewrite digraph_max_nat. apply Nat.le_max_r.
Qed.

(** Reading one successor row pays only the source key's digits. *)
Local Lemma digraph_succs_time g u w : Pos.size_nat u <= w ->
  (T_succs g u <= 4 * N.of_nat (w + 1))%N.
Proof.
  intro Hwidth. destruct g as [vs rows].
  pose proof (PTrieT.trie_get_clock (list positive) u rows) as Hget.
  time_unfold @T_succs. time_cbn. rewrite Hget. rewrite Nat2N.inj_add. nia.
Qed.

(** Counting edges adds each row length once, so repeated rows are charged explicitly. *)
Local Lemma edge_count_fold_time g vs w :
  Forall (fun u => Pos.size_nat u <= w) vs ->
  (1 + List.T_fold_right (fun u n => (length (succs g u) + n)%nat)
    (fun u n => 1 + ((T_succs g u + Datatypes.T_length (succs g u)) +
      Nat.T_add (length (succs g u)) n))%N 0%nat vs <=
    16 * N.of_nat (length vs +
      fold_right (fun u n => (length (succs g u) + n)%nat) 0%nat vs + 1) *
      N.of_nat (w + 1))%N.
Proof.
  induction vs as [|u vs IH]; intro Hwidth.
  - time_unfold @List.T_fold_right. cbn [length fold_right].
    rewrite Nat2N.inj_add. nia.
  - inversion Hwidth as [|u0 vs0 Hu Hvs]; subst u0 vs0.
    specialize (IH Hvs).
    pose proof (digraph_succs_time g u w Hu) as Hread.
    pose proof (Datatypes.T_length_le (succs g u)) as Hlength.
    pose proof (Nat.T_add_le (length (succs g u))
      (fold_right (fun v n => length (succs g v) + n) 0 vs)) as Hadd.
    time_unfold @List.T_fold_right. cbn beta iota zeta.
    cbn [length fold_right]. rewrite !Nat2N.inj_add, ?time_of_nat_succ in *.
    clear - IH Hread Hlength Hadd. nia.
Qed.

(** The edge cache's unary count obeys the same graph-size and key-width envelope. *)
Lemma digraph_edge_count_time g :
  (T_graph_e g <= 16 * N.of_nat (graph_n g + graph_e g + 1) *
    N.of_nat (graph_width g + 1))%N.
Proof.
  destruct g as [vs rows].
  assert (Hwidth : Forall (fun u => Pos.size_nat u <= graph_width (Digraph vs rows)) vs).
  { eapply Forall_impl; [|exact (digraph_width_occurrences (Digraph vs rows))].
    intros u Hu. exact (proj1 Hu). }
  pose proof (edge_count_fold_time (Digraph vs rows) vs
    (graph_width (Digraph vs rows)) Hwidth) as Hclock.
  time_unfold @T_graph_e. exact Hclock.
Qed.

(** Computing the source count traverses each listed vertex occurrence once. *)
Lemma digraph_vertex_count_time g :
  (T_graph_n g <= 2 * N.of_nat (graph_n g + 1))%N.
Proof.
  destruct g as [vs rows].
  pose proof (Datatypes.T_length_le vs) as Hlength.
  time_unfold @T_graph_n. cbn [graph_n]. rewrite Nat2N.inj_add. lia.
Qed.

Module DigraphT <: DIGRAPH_T.
  Include Digraph.
  TimeFun add_pred.
  TimeFun prepare.
  Definition c_prepare : N := (128 * (PTrieT.c_trie + 1))%N.

  (** One predecessor insertion pays one lookup and one update at the target key. *)
  Local Lemma add_pred_time u v p :
    (T_add_pred u v p <= 8 * (PTrieT.c_trie + 1) * N.of_nat (Pos.size_nat v + 1))%N.
  Proof.
    pose proof (PTrieT.trie_get_clock (list positive) v p) as Hget.
    pose proof (PTrieT.T_set_le (list positive) v
      (u :: match trie_get v p with Some vs => vs | None => nil end) p) as Hset.
    time_unfold @T_add_pred. rewrite Hget. rewrite !Nat2N.inj_add in *. nia.
  Qed.

  (** Each successor occurrence pays one insertion, independently of its accumulator. *)
  Local Lemma predecessor_row_time u vs p w :
    Forall (fun v => Pos.size_nat v <= w) vs ->
    (List.T_fold_right (add_pred u) (fun v acc => T_add_pred u v acc) p vs <=
      16 * (PTrieT.c_trie + 1) * N.of_nat (length vs + 1) * N.of_nat (w + 1))%N.
  Proof.
    induction vs as [|v vs IH]; intro Hwidth.
    - time_unfold @List.T_fold_right. cbn [length]. rewrite Nat2N.inj_add. nia.
    - inversion Hwidth as [|v0 vs0 Hv Hvs]; subst v0 vs0.
      specialize (IH Hvs).
      pose proof (add_pred_time u v (fold_right (add_pred u) p vs)) as Hhead.
      time_unfold @List.T_fold_right. cbn beta iota zeta.
      cbn [length]. rewrite !Nat2N.inj_add, ?time_of_nat_succ in *.
      clear - IH Hhead Hv. nia.
  Qed.

  (** The outer fold charges source occurrences and every occurrence in their rows. *)
  Local Lemma predecessor_rows_time g vs p w :
    Forall (fun u => Pos.size_nat u <= w /\
      Forall (fun v => Pos.size_nat v <= w) (succs g u)) vs ->
    (List.T_fold_right (fun u acc => fold_right (add_pred u) acc (succs g u))
      (fun u acc => 1 + (T_succs g u +
        List.T_fold_right (add_pred u) (fun v row => T_add_pred u v row) acc (succs g u)))%N
      p vs <= 32 * (PTrieT.c_trie + 1) *
        N.of_nat (length vs +
          fold_right (fun u n => (length (succs g u) + n)%nat) 0%nat vs + 1) *
        N.of_nat (w + 1))%N.
  Proof.
    induction vs as [|u vs IH]; intro Hwidth.
    - time_unfold @List.T_fold_right. cbn [length fold_right].
      rewrite Nat2N.inj_add. nia.
    - inversion Hwidth as [|u0 vs0 [Hu Hrow] Hvs]; subst u0 vs0.
      specialize (IH Hvs).
      pose proof (digraph_succs_time g u w Hu) as Hread.
      pose proof (predecessor_row_time u (succs g u)
        (fold_right (fun v acc => fold_right (add_pred v) acc (succs g v)) p vs)
        w Hrow) as Hhead.
      time_unfold @List.T_fold_right. cbn beta iota zeta.
      cbn [length fold_right]. rewrite !Nat2N.inj_add, ?time_of_nat_succ in *.
      clear - IH Hread Hhead. nia.
  Qed.

  Lemma T_prepare_le : forall g,
    (T_prepare g <= c_prepare * N.of_nat (graph_n g + graph_e g + 1) *
      N.of_nat (graph_width g + 1))%N.
  Proof.
    intros [vs rows].
    pose proof (predecessor_rows_time (Digraph vs rows) vs Empty
      (graph_width (Digraph vs rows)) (digraph_width_occurrences (Digraph vs rows))) as Hpred.
    pose proof (digraph_edge_count_time (Digraph vs rows)) as Hedges.
    pose proof (Datatypes.T_length_le vs) as Hlength.
    pose proof (graph_of_nat_time (length vs)) as Hnv.
    pose proof (graph_of_nat_time (graph_e (Digraph vs rows))) as Hne.
    unfold c_prepare. time_unfold @T_prepare. unfold T_verts.
    cbn [verts graph_n] in *. rewrite !Nat2N.inj_add in *.
    change (List.T_fold_right (fun u acc => fold_right (add_pred u) acc
        (succs (Digraph vs rows) u))
      (fun u acc => 1 + (T_succs (Digraph vs rows) u +
        List.T_fold_right (add_pred u) (fun v row => T_add_pred u v row)
          acc (succs (Digraph vs rows) u)))%N Empty vs <=
      32 * (PTrieT.c_trie + 1) * (N.of_nat (length vs) +
        N.of_nat (graph_e (Digraph vs rows)) + 1) *
        (N.of_nat (graph_width (Digraph vs rows)) + 1))%N in Hpred.
    nia.
  Qed.

  Lemma prepare_bigO : bigO (fun _ => True)
    (fun g => N.of_nat ((graph_n g + graph_e g + 1) * (graph_width g + 1))) T_prepare.
  Proof.
    exists c_prepare. intros g _.
    eapply N.le_trans; [apply T_prepare_le|].
    rewrite Nat2N.inj_mul. nia.
  Qed.
End DigraphT.
