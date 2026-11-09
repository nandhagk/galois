(** * Weak orders and partial rank queries

    Weak orders flatten the one hierarchy and index its actual token positions.
    For example, an unknown ID has no rank and no enclosing-header row.
    Builds on: GraphHier, GraphHierExact and the public map interface. *)

From Stdlib Require Import List PArith Arith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet BaseTacticsInv.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor GraphSearchSpec GraphHierSpec
  GraphHier GraphHierExact GraphWeakOrderFacts GraphSearchInvariant GraphHierCycles
  GraphHierCycleHeads GraphLoopStructure.
Import List.ListNotations Cost.Notations.
Local Open Scope nat_scope.

Module WeakOrder.

(** The producer flattens exactly the hierarchy returned by its one recursive SCC computation. *)
Definition compute_c {V E} (p : Prepared.t V E) roots :=
  let* forest := HierRun.compute_c p (Scope.Make FinSet.empty None) roots in
  Wto.of_forest_c forest.

Definition compute {V E} (p : Prepared.t V E) roots := Cost.value (compute_c p roots).

(** Weak-order computation is token projection of the actual hierarchy. *)
Theorem compute_equation {V E} (p : Prepared.t V E) roots :
  compute p roots =
    Wto.of_forest (HierRun.compute p (Scope.Make FinSet.empty None) roots).
Proof.
  unfold compute, compute_c. rewrite Cost.value_bind. reflexivity.
Qed.

(** Ready preparation makes produced weak orders valid for all supplied root occurrences. *)
Theorem compute_valid {V E} (p : Prepared.t V E) roots :
  Prepared.ready p -> Wto.valid p roots (compute p roots).
Proof.
  intro Hready. rewrite compute_equation.
  apply (HierExact.exact_wto_valid_ready p _ roots _ Hready).
  apply HierExact.compute_exact, Hready.
Qed.

(** Positions use one positive counter per listed vertex and retain no default. *)
Fixpoint rank_rows_c start (vs : list positive) : Cost.t (Map.t positive positive) :=
  match vs with
  | [] => Cost.ret Map.empty
  | v :: rest =>
    Cost.step ;;
    let* tail := rank_rows_c (Pos.succ start) rest in
    Map.set_c positive_encoding v start tail
  end.

Definition rank_rows start vs := Cost.value (rank_rows_c start vs).

(** Rank construction exposes the head binding and its actual successor counter. *)
Theorem rank_rows_equation start vs :
  rank_rows start vs =
  match vs with
  | [] => Map.empty
  | v :: rest => Map.set positive_encoding v start (rank_rows (Pos.succ start) rest)
  end.
Proof.
  destruct vs; reflexivity.
Qed.

(** Every rank map has canonical storage, independently of repeated token IDs. *)
Theorem rank_rows_wf start vs : Map.wf positive_encoding (rank_rows start vs).
Proof.
  revert start. induction vs as [|v rest IH]; intro start; rewrite rank_rows_equation.
  - apply Map.wf_empty.
  - apply Map.wf_set, IH.
Qed.

Fixpoint advance start n :=
  match n with
  | O => start
  | S n => advance (Pos.succ start) n
  end.

(** The proof-level counter observation advances by the supplied list position. *)
Theorem advance_count start n : Pos.to_nat (advance start n) = Pos.to_nat start + n.
Proof.
  revert start. induction n as [|n IH]; intro start; cbn [advance].
  - lia.
  - rewrite IH, Pos2Nat.inj_succ. lia.
Qed.

(** Duplicate-free vertex orders have exactly their indexed one-based rank bindings. *)
Theorem rank_rows_spec start vs :
  NoDup vs -> forall v i,
  Map.get positive_encoding v (rank_rows start vs) = Some i <->
    exists n, nth_error vs n = Some v /\ i = advance start n.
Proof.
  revert start. induction vs as [|x rest IH]; intros start Hnodup v i.
  - rewrite rank_rows_equation, Map.get_empty. split; [discriminate|].
    intros [n [Hnth _]]. rewrite nth_error_nil in Hnth. discriminate.
  - inversion Hnodup as [|head tail Hfresh Htail]; subst.
    rewrite rank_rows_equation. destruct (Pos.eq_dec v x) as [->|Hne].
    + rewrite Map.get_set_same by apply rank_rows_wf.
      split.
      * intro Heq. inversion Heq; subst. exists 0. split; reflexivity.
      * intros [[|n] [Hnth Heq]]; [exact (eq_sym (f_equal Some Heq))|].
        cbn [nth_error] in Hnth. apply nth_error_In in Hnth. contradiction.
    + rewrite (Map.get_set_other positive_encoding positive_encoding_laws)
        by (try apply rank_rows_wf; exact Hne).
      rewrite (IH (Pos.succ start) Htail). split.
      * intros [n [Hnth Heq]]. exists (S n). exact (conj Hnth Heq).
      * intros [[|n] [Hnth Heq]].
        -- exfalso. apply Hne. now inversion Hnth.
        -- exists n. exact (conj Hnth Heq).
Qed.

Definition ranks_c w :=
  let* vs := Wto.order_c w in rank_rows_c 1%positive vs.

Definition ranks w := Cost.value (ranks_c w).

(** Rank indexing consumes the existing token-order projection. *)
Theorem ranks_equation w : ranks w = rank_rows 1%positive (Wto.order w).
Proof.
  reflexivity.
Qed.

(** Every present vertex has its actual positive rank and missing vertices have no binding. *)
Theorem ranks_spec w :
  NoDup (Wto.order w) -> forall v i,
  Map.get positive_encoding v (ranks w) = Some i <->
    exists n, nth_error (Wto.order w) n = Some v /\ Pos.to_nat i = S n.
Proof.
  intro Hnodup. intros v i. rewrite ranks_equation, rank_rows_spec by exact Hnodup.
  split; intros [n [Hnth Hi]]; exists n; split; [exact Hnth| |exact Hnth|].
  - subst i. rewrite advance_count. reflexivity.
  - apply Pos2Nat.inj. rewrite advance_count. cbn [Pos.to_nat]. lia.
Qed.

(** Textually forward vertices have strictly increasing actual ranks. *)
Theorem ranks_before w u v :
  NoDup (Wto.order w) -> before (Wto.order w) u v ->
  exists i j, Map.get positive_encoding u (ranks w) = Some i /\
    Map.get positive_encoding v (ranks w) = Some j /\ (i < j)%positive.
Proof.
  intros Hnodup Hbefore.
  destruct (proj1 (SearchInvariant.before_indices _ u v) Hbefore)
    as [n [m [Hlt [Hn Hm]]]].
  exists (Pos.of_succ_nat n), (Pos.of_succ_nat m). split.
  - apply (proj2 (ranks_spec w Hnodup u _)). exists n.
    split; [exact Hn|apply SuccNat2Pos.id_succ].
  - split.
    + apply (proj2 (ranks_spec w Hnodup v _)). exists m.
      split; [exact Hm|apply SuccNat2Pos.id_succ].
    + apply Pos2Nat.inj_lt. rewrite !SuccNat2Pos.id_succ. lia.
Qed.

Definition heads_of_c w v :=
  let* rows := Wto.annotate_c [] w in
  let* index := Map.of_list_c positive_encoding rows in
  Map.get_c positive_encoding v index.

Definition heads_of w v := Cost.value (heads_of_c w v).

(** Header queries retain the optional lookup of the actual annotation index. *)
Theorem heads_of_equation w v :
  heads_of w v = Map.get positive_encoding v
    (Map.of_list positive_encoding (Wto.annotate [] w)).
Proof.
  reflexivity.
Qed.

Local Lemma lookup_rows_sound (rows : list (positive * list positive)) v stack :
  Map.get positive_encoding v (Map.of_list positive_encoding rows) = Some stack ->
    In (v, stack) rows.
Proof.
  rewrite Map.of_list_get. intro Hget.
  pose proof (fold_left_invariant
    (fun old (row : positive * list positive) =>
      if eqb positive_encoding v (fst row) then Some (snd row) else old)
    rows None
    (fun old => old = None \/ exists heads, old = Some heads /\ In (v, heads) rows))
    as Hfold.
  assert (Hinvariant : forall old row, In row rows ->
    (old = None \/ exists heads, old = Some heads /\ In (v, heads) rows) ->
    ((if eqb positive_encoding v (fst row) then Some (snd row) else old) = None \/
      exists heads,
        (if eqb positive_encoding v (fst row) then Some (snd row) else old) = Some heads /\
        In (v, heads) rows)).
  { intros old [key heads] Hin Hold. cbn [fst snd].
    destruct (eqb positive_encoding v key) eqn:Heq; [|exact Hold].
    apply (eqb_true_iff positive_encoding positive_encoding_laws) in Heq. subst key.
    right. exists heads. auto. }
  destruct (Hfold (or_introl eq_refl) Hinvariant) as [Hnone|[heads [Heq Hin]]].
  - congruence.
  - rewrite Hget in Heq. inversion Heq; subst heads. exact Hin.
Qed.

Local Lemma lookup_annotation_complete w v stack :
  NoDup (Wto.order w) -> In (v, stack) (Wto.annotate [] w) ->
    Map.get positive_encoding v
      (Map.of_list positive_encoding (Wto.annotate [] w)) = Some stack.
Proof.
  intros Hunique Hrow. rewrite Map.of_list_get.
  destruct (in_split (v, stack) _ Hrow) as [first [last Hsplit]].
  rewrite Hsplit, fold_left_app. cbn [fold_left fst snd].
  rewrite (eqb_refl positive_encoding v).
  apply (fold_left_invariant _ last (Some stack) (fun old => old = Some stack));
    [reflexivity|].
  intros old [key heads] Hin Hold. cbn [fst snd].
  destruct (eqb positive_encoding v key) eqn:Heq; [|exact Hold].
  apply (eqb_true_iff positive_encoding positive_encoding_laws) in Heq. subst key.
  assert (Hsame : stack = heads).
  { apply (WeakOrderFacts.annotation_functional w [] v stack heads Hunique Hrow).
    rewrite Hsplit. apply in_or_app. right. now right. }
  now subst heads.
Qed.

(** On a unique token order, a header query returns exactly that node's enclosing annotation. *)
Theorem heads_of_spec w v stack :
  NoDup (Wto.order w) ->
  (heads_of w v = Some stack <-> In (v, stack) (Wto.annotate [] w)).
Proof.
  intro Hunique. rewrite heads_of_equation. split.
  - apply lookup_rows_sound.
  - apply lookup_annotation_complete, Hunique.
Qed.

(** Edges that do not return to an enclosing head have increasing actual partial ranks. *)
Theorem ranks_forward {V E} (p : Prepared.t V E) scope roots w u e v :
  Wto.valid_within p scope roots w ->
  Prepared.arc p u e v -> In u (Wto.order w) -> Scope.admits scope v = true ->
  (forall stack, In (u, stack) (Wto.annotate [] w) -> ~ In v stack) ->
  exists i j, Map.get positive_encoding u (ranks w) = Some i /\
    Map.get positive_encoding v (ranks w) = Some j /\ (i < j)%positive.
Proof.
  intros Hvalid Harc Hu Hallowed Hnothead.
  apply ranks_before; [exact (Wto.unique _ _ _ _ Hvalid)|].
  destruct (Wto.edges _ _ _ _ Hvalid u e v Harc Hu Hallowed) as [Hbefore|[stack [Hin Hv]]].
  - exact Hbefore.
  - exfalso. exact (Hnothead stack Hin Hv).
Qed.

(** Every nonempty rooted cycle passes through a head enclosing every actual point of that cycle. *)
Theorem cycles_have_head {V E} (p : Prepared.t V E) roots v es :
  Prepared.ready p ->
  Search.scoped_reachable p (Scope.Make FinSet.empty None) roots v ->
  Search.scoped_path p (Scope.Make FinSet.empty None) v es v -> es <> [] ->
  exists h, In h (HierCycles.points p v es) /\
    forall x, In x (HierCycles.points p v es) ->
      exists stack, In (x, stack) (Wto.annotate [] (compute p roots)) /\ In h stack.
Proof.
  intros Hready Hreach Hcycle Hnonempty.
  pose proof (HierExact.compute_exact p (Scope.Make FinSet.empty None) roots Hready) as Hexact.
  destruct (proj1 (HierCycleHeads.exact_heads p) _ _ _ Hexact v es Hreach Hcycle Hnonempty)
    as [h [Hpoint Hmembers]].
  exists h. split; [exact Hpoint|]. intros x Hx. rewrite compute_equation.
  apply LoopStructure.member_annotation. exact (Hmembers x Hx).
Qed.

End WeakOrder.
