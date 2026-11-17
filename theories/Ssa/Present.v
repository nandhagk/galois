(** * Language control-flow occurrences

    Edges retain the source block and the selected exit arm.
    For example, two arms aimed at the same block remain distinct.

    Main results
    - [edges_complexity] Edge enumeration is linear in its output, O(n) for n edges, in [BlockCfgT]
      and [PointCfgT].
    - [entries_complexity] Entry enumeration is linear in its output, O(n) for n entries, in
      [BlockCfgT] and [PointCfgT].
    - [out_complexity] Outgoing lookup is linear in the node key and the returned edges,
      O(|n| + k) for k edges, in [BlockCfgT] and [PointCfgT].
    - [inc_complexity] Incoming lookup is linear in the node key and the returned edges,
      O(|n| + k) for k edges, in [BlockCfgT] and [PointCfgT].
    - [nodes_complexity] Node enumeration is linear in its output, O(n) for n nodes, in
      [BlockCfgT] and [PointCfgT].
    - [prepare_complexity] The concrete preparation clock has the published asymptotic bound,
      O((s + 1) (w + 1)) for s function size and width w.

    Builds on: Ssa.Lang. *)

From Stdlib Require Import List PArith NArith ZArith Bool Lia Arith Wf_nat.
From Argent Require Import Time Tactics Std Complexity BigO.
From Galois.Base Require Import Code KeySig Key Trie.
From Galois.Graph Require Import DigraphSig.
From Galois.Program Require Import CfgSig VarsSig Vars SsaSig Ssa.
From Galois.Ssa Require Import Lang LiveSig ValidateSig.
Import List.ListNotations.
Import ComplexityNotations.

Inductive exit_arm :=
  | Jump_arm
  | True_arm
  | False_arm.

Record block_edge := BlockEdge {
  edge_source : positive;
  edge_arm : exit_arm;
  edge_target : positive
}.
TimeFun edge_source.
TimeFun edge_arm.
TimeFun edge_target.

Definition point_key := (positive * N)%type.

Module ArmKeyCode <: KEY_OPS.
  Definition t := exit_arm.
  Definition encode a := match a with Jump_arm => 1%positive | True_arm => 2%positive
    | False_arm => 3%positive end.
  Definition eqb a b := match a, b with
    | Jump_arm, Jump_arm | True_arm, True_arm | False_arm, False_arm => true
    | _, _ => false
    end.
End ArmKeyCode.

Module ArmKey <: KEY.
  Include ArmKeyCode.
  Include KEY_SPEC.
  Lemma encode_inj : forall a b, encode a = encode b -> a = b.
  Proof.
    intros [] []; cbn [encode]; congruence.
  Qed.
  Lemma eqb_spec : forall a b, reflect (a = b) (eqb a b).
  Proof.
    intros [] []; cbn [eqb]; constructor; congruence.
  Qed.
End ArmKey.

Module ArmKeyT <: KEY_T.
  Include ArmKey.
  TimeFun encode.
  TimeFun eqb.
  Definition c_key : N := 1.
  Lemma T_encode_le : forall k, (T_encode k <= c_key * N.of_nat (bits k + 1))%N.
  Proof.
    intros []; unfold c_key, bits, encode; time_step.
  Qed.
  Lemma T_eqb_le : forall a b, (T_eqb a b <= c_key * N.of_nat (bits a + 1))%N.
  Proof.
    intros [] []; unfold c_key, bits, encode; time_step.
  Qed.
End ArmKeyT.

Module EdgeArmTargetKey := PairKeyT ArmKeyT PosKeyT.
Module EdgeTupleKey := PairKeyT PosKeyT EdgeArmTargetKey.
Definition block_edge_tuple (e : block_edge) : EdgeTupleKey.t :=
  (edge_source e, (edge_arm e, edge_target e)).
TimeFun block_edge_tuple.

Module BlockEdgeCode <: KEY_OPS.
  Definition t := block_edge.
  Definition encode e := EdgeTupleKey.encode (block_edge_tuple e).
  Definition eqb a b := EdgeTupleKey.eqb (block_edge_tuple a) (block_edge_tuple b).
End BlockEdgeCode.

Module BlockEdgeKey <: KEY.
  Include BlockEdgeCode.
  Include KEY_SPEC.
  Lemma encode_inj : forall a b, encode a = encode b -> a = b.
  Proof.
    intros [s a t] [s' a' t'] Heq.
    apply EdgeTupleKey.encode_inj in Heq.
    unfold block_edge_tuple in Heq; cbn in Heq.
    inversion Heq; reflexivity.
  Qed.
  Lemma eqb_spec : forall a b, reflect (a = b) (eqb a b).
  Proof.
    intros [s a t] [s' a' t']; unfold eqb.
    destruct (EdgeTupleKey.eqb_spec (block_edge_tuple (BlockEdge s a t))
      (block_edge_tuple (BlockEdge s' a' t'))) as [Heq | Hneq].
    - constructor. unfold block_edge_tuple in Heq; cbn in Heq.
      inversion Heq; reflexivity.
    - constructor. intro Heq; apply Hneq; now rewrite Heq.
  Qed.
End BlockEdgeKey.

Module BlockEdge <: KEY_T.
  Include BlockEdgeKey.
  TimeFun encode.
  TimeFun eqb.
  Definition c_key : N := 8 * (EdgeTupleKey.c_key + 1).
  Lemma T_encode_le : forall k, (T_encode k <= c_key * N.of_nat (bits k + 1))%N.
  Proof.
    intro k. pose proof (EdgeTupleKey.T_encode_le (block_edge_tuple k)) as Hcall.
    change (EdgeTupleKey.T_encode (block_edge_tuple k) <=
      EdgeTupleKey.c_key * N.of_nat (bits k + 1))%N in Hcall.
    unfold c_key. time_unfold T_encode. time_unfold T_block_edge_tuple.
    time_unfold T_edge_source. time_unfold T_edge_arm. time_unfold T_edge_target.
    time_simpl; time_cbn.
    change (1 + (4 + EdgeTupleKey.T_encode (block_edge_tuple k)) <=
      8 * (EdgeTupleKey.c_key + 1) * N.of_nat (bits k + 1))%N.
    rewrite Nat2N.inj_add in *; nia.
  Qed.
  Lemma T_eqb_le : forall a b, (T_eqb a b <= c_key * N.of_nat (bits a + 1))%N.
  Proof.
    intros a b.
    pose proof (EdgeTupleKey.T_eqb_le (block_edge_tuple a) (block_edge_tuple b)) as Hcall.
    change (EdgeTupleKey.T_eqb (block_edge_tuple a) (block_edge_tuple b) <=
      EdgeTupleKey.c_key * N.of_nat (bits a + 1))%N in Hcall.
    unfold c_key. time_unfold T_eqb. time_unfold T_block_edge_tuple.
    time_unfold T_edge_source. time_unfold T_edge_arm. time_unfold T_edge_target.
    time_simpl; time_cbn.
    change (1 + (4 + 4 + EdgeTupleKey.T_eqb (block_edge_tuple a) (block_edge_tuple b)) <=
      8 * (EdgeTupleKey.c_key + 1) * N.of_nat (bits a + 1))%N.
    pose proof (Pos.size_nat_pos (encode a)) as Hwidth.
    assert (Hbits : 1 <= bits a) by exact Hwidth. apply time_of_nat_le in Hbits.
    rewrite Nat2N.inj_add in *; nia.
  Qed.
End BlockEdge.

Module PointKey := PairKeyT PosKeyT NKeyT.

Record point_edge := PointEdge {
  point_src : PointKey.t;
  point_dst : PointKey.t;
  point_block_edge : option block_edge
}.

TimeFun point_src.
TimeFun point_dst.
TimeFun point_block_edge.
Module OptionalBlockEdgeKey := OptionKeyT BlockEdge.
Module PointTargetEdgeKey := PairKeyT PointKey OptionalBlockEdgeKey.
Module PointEdgeTupleKey := PairKeyT PointKey PointTargetEdgeKey.

Definition point_edge_tuple (e : point_edge) : PointEdgeTupleKey.t :=
  (point_src e, (point_dst e, point_block_edge e)).
TimeFun point_edge_tuple.

Module PointEdgeCode <: KEY_OPS.
  Definition t := point_edge.
  Definition encode e := PointEdgeTupleKey.encode (point_edge_tuple e).
  Definition eqb a b := PointEdgeTupleKey.eqb (point_edge_tuple a) (point_edge_tuple b).
End PointEdgeCode.

Module PointEdgeKey <: KEY.
  Include PointEdgeCode.
  Include KEY_SPEC.
  Lemma encode_inj : forall a b, encode a = encode b -> a = b.
  Proof.
    intros [s t e] [s' t' e'] Heq.
    apply PointEdgeTupleKey.encode_inj in Heq.
    unfold point_edge_tuple in Heq; cbn in Heq.
    inversion Heq; reflexivity.
  Qed.
  Lemma eqb_spec : forall a b, reflect (a = b) (eqb a b).
  Proof.
    intros [s t e] [s' t' e']; unfold eqb.
    destruct (PointEdgeTupleKey.eqb_spec (point_edge_tuple (PointEdge s t e))
      (point_edge_tuple (PointEdge s' t' e'))) as [Heq | Hneq].
    - constructor. unfold point_edge_tuple in Heq; cbn in Heq.
      inversion Heq; reflexivity.
    - constructor. intro Heq; apply Hneq; now rewrite Heq.
  Qed.
End PointEdgeKey.

Module PointEdge <: KEY_T.
  Include PointEdgeKey.
  TimeFun encode.
  TimeFun eqb.
  Definition c_key : N := 8 * (PointEdgeTupleKey.c_key + 1).
  Lemma T_encode_le : forall k, (T_encode k <= c_key * N.of_nat (bits k + 1))%N.
  Proof.
    intro k. pose proof (PointEdgeTupleKey.T_encode_le (point_edge_tuple k)) as Hcall.
    change (PointEdgeTupleKey.T_encode (point_edge_tuple k) <=
      PointEdgeTupleKey.c_key * N.of_nat (bits k + 1))%N in Hcall.
    unfold c_key. time_unfold T_encode. time_unfold T_point_edge_tuple.
    time_unfold T_point_src. time_unfold T_point_dst. time_unfold T_point_block_edge.
    time_simpl; time_cbn.
    change (1 + (4 + PointEdgeTupleKey.T_encode (point_edge_tuple k)) <=
      8 * (PointEdgeTupleKey.c_key + 1) * N.of_nat (bits k + 1))%N.
    rewrite Nat2N.inj_add in *; nia.
  Qed.
  Lemma T_eqb_le : forall a b, (T_eqb a b <= c_key * N.of_nat (bits a + 1))%N.
  Proof.
    intros a b.
    pose proof (PointEdgeTupleKey.T_eqb_le (point_edge_tuple a) (point_edge_tuple b)) as Hcall.
    change (PointEdgeTupleKey.T_eqb (point_edge_tuple a) (point_edge_tuple b) <=
      PointEdgeTupleKey.c_key * N.of_nat (bits a + 1))%N in Hcall.
    unfold c_key. time_unfold T_eqb. time_unfold T_point_edge_tuple.
    time_unfold T_point_src. time_unfold T_point_dst. time_unfold T_point_block_edge.
    time_simpl; time_cbn.
    change (1 + (4 + 4 + PointEdgeTupleKey.T_eqb (point_edge_tuple a) (point_edge_tuple b)) <=
      8 * (PointEdgeTupleKey.c_key + 1) * N.of_nat (bits a + 1))%N.
    pose proof (Pos.size_nat_pos (encode a)) as Hwidth.
    assert (Hbits : 1 <= bits a) by exact Hwidth. apply time_of_nat_le in Hbits.
    rewrite Nat2N.inj_add in *; nia.
  Qed.
End PointEdge.

Definition point_row := (point_edge * list positive * list positive)%type.

(** Instruction rows start at index `i` and return the index of the exit point. *)
Fixpoint code_rows {K} (b : positive) (i : N) (cs : list (positive * K * list positive))
    : list point_row * N :=
  match cs with
  | [] => ([], i)
  | (x, _, ys) :: rest =>
      let rows := code_rows b (N.succ i) rest in
      ((PointEdge (b, i) (b, N.succ i) None, ys, [x]) :: fst rows, snd rows)
  end.
TimeFun code_rows.

(** Instruction destinations stay in their block and strictly advance their index. *)
Lemma code_rows_dest_bounds {K} b i (cs : list (positive * K * list positive)) n :
  In n (map (fun r => point_dst (fst (fst r))) (fst (code_rows b i cs))) ->
    fst n = b /\ (i < snd n <= i + N.of_nat (length cs))%N.
Proof.
  revert i; induction cs as [|[[x op] xs] rest IH]; intros i Hin.
  - contradiction.
  - cbn [code_rows fst snd map point_dst] in Hin.
    cbn [length]. rewrite Nat2N.inj_succ.
    destruct Hin as [Heq|Hin].
    + subst n; cbn; split; [reflexivity|lia].
    + destruct (IH (N.succ i) Hin) as [Hb Hbound]. split; [exact Hb|lia].
Qed.

(** The instruction destinations within one block are pairwise distinct. *)
Lemma code_rows_dest_nodup {K} b i (cs : list (positive * K * list positive)) :
  NoDup (map (fun r => point_dst (fst (fst r))) (fst (code_rows b i cs))).
Proof.
  revert i; induction cs as [|[[x op] xs] rest IH]; intro i.
  - constructor.
  - cbn [code_rows fst snd map point_dst]. constructor; [|apply IH].
    intro Hin. destruct (code_rows_dest_bounds _ _ _ _ Hin) as [_ Hbound].
    cbn in Hbound; lia.
Qed.

(** A complete instruction chain contains every source and its final endpoint. *)
Lemma code_rows_endpoints {K} b i (cs : list (positive * K * list positive)) :
  In (b, snd (code_rows b i cs))
      ((b, i) :: map (fun r => point_dst (fst (fst r))) (fst (code_rows b i cs))) /\
  forall row, In row (fst (code_rows b i cs)) ->
    In (point_src (fst (fst row)))
      ((b, i) :: map (fun r => point_dst (fst (fst r))) (fst (code_rows b i cs))).
Proof.
  revert i; induction cs as [|[[x op] xs] rest IH]; intro i.
  - cbn [code_rows fst snd map]. split; [now left|intros row Hin; contradiction].
  - cbn [code_rows fst snd map point_dst]. destruct (IH (N.succ i)) as [Hlast Hsource].
    split; [now right|]. intros row [Heq|Hin].
    + subst row; cbn; now left.
    + right; now apply Hsource.
Qed.

(** Instruction rows are internal point edges. *)
Lemma code_rows_internal {K} b i (cs : list (positive * K * list positive)) row :
  In row (fst (code_rows b i cs)) -> point_block_edge (fst (fst row)) = None.
Proof.
  revert i; induction cs as [|[[x op] xs] rest IH]; intros i Hin; [contradiction|].
  cbn [code_rows fst] in Hin. destruct Hin as [Heq|Hin].
  - subst row; reflexivity.
  - now apply (IH (N.succ i)).
Qed.

(** Each exit edge with the arguments that it passes. *)
Definition exit_edge_args {G} (source : positive) (e : exit positive G)
    : list (block_edge * list positive) :=
  match e with
  | Jump target args => [(BlockEdge source Jump_arm target, args)]
  | Branch _ _ yes yes_args no no_args =>
      [(BlockEdge source True_arm yes, yes_args); (BlockEdge source False_arm no, no_args)]
  | Return _ => []
  end.
TimeFun exit_edge_args.

(** The guard and its operands hold on the true arm of a branch. *)
Definition exit_guards {G} (source : positive) (e : exit positive G)
    : list (block_edge * list (G * list positive)) :=
  match e with
  | Jump target _ => [(BlockEdge source Jump_arm target, [])]
  | Branch g xs yes _ no _ =>
      [(BlockEdge source True_arm yes, [(g, xs)]); (BlockEdge source False_arm no, [])]
  | Return _ => []
  end.
TimeFun exit_guards.

Definition guard_uses {G} (e : exit positive G) : list positive :=
  match e with
  | Branch _ xs _ _ _ _ => xs
  | _ => []
  end.
TimeFun guard_uses.

Definition exit_returns {G} (e : exit positive G) : list positive :=
  match e with
  | Return xs => xs
  | _ => []
  end.
TimeFun exit_returns.

Fixpoint pair_args (xs ys : list positive) : list (positive * positive) :=
  match xs, ys with
  | x :: xs', y :: ys' => (x, y) :: pair_args xs' ys'
  | _, _ => []
  end.
TimeFun pair_args.

(** The rows of one kept block, computed once. *)
Record block_summary := BlockSummary {
  summary_block : positive;
  summary_params : list positive;
  summary_points : list point_key;
  summary_internal : list point_row;
  summary_exit : point_key;
  summary_outgoing : list point_row;
  summary_returns : list positive
}.

TimeFun summary_block.
TimeFun summary_params.
TimeFun summary_points.
TimeFun summary_internal.
TimeFun summary_exit.
TimeFun summary_outgoing.
TimeFun summary_returns.

(** A key is listed when the table has a row for it. *)
Definition is_listed {A} (m : ptrie A) (b : positive) : bool :=
  match trie_get b m with
  | Some _ => true
  | None => false
  end.
TimeFun is_listed.

(** Exit edges whose target is a kept block, with their arguments. *)
Definition listed_edge_args {A G} (kept : ptrie A) (source : positive) (e : exit positive G)
    : list (block_edge * list positive) :=
  filter (fun ea => is_listed kept (edge_target (fst ea))) (exit_edge_args source e).
TimeFun listed_edge_args.

(** Guard rows of the exit edges whose target is a kept block. *)
Definition listed_guards {A G} (kept : ptrie A) (source : positive) (e : exit positive G)
    : list (block_edge * list (G * list positive)) :=
  filter (fun eg => is_listed kept (edge_target (fst eg))) (exit_guards source e).
TimeFun listed_guards.

Definition summarize {A K G} (kept : ptrie A) (item : positive * block positive K G)
    : block_summary :=
  let b := fst item in
  let body := snd item in
  let rows := code_rows b 1%N (code _ _ _ body) in
  let last := (b, snd rows) in
  let internal := (PointEdge (b, 0%N) (b, 1%N) None, nil, params _ _ _ body) :: fst rows in
  BlockSummary b (params _ _ _ body)
    ((b, 0%N) :: map (fun r => point_dst (fst (fst r))) internal)
    internal last
    (map (fun ea => (PointEdge last (edge_target (fst ea), 0%N) (Some (fst ea)),
        guard_uses (term _ _ _ body) ++ snd ea, nil))
      (listed_edge_args kept b (term _ _ _ body)))
    (exit_returns (term _ _ _ body)).
TimeFun summarize.

(** Every point of a summary keeps the identifier of its owning block. *)
Lemma summarize_point_owner {A K G} (kept : ptrie A)
    (item : positive * block positive K G) n :
  In n (summary_points (summarize kept item)) -> fst n = fst item.
Proof.
  change (In n ((fst item, 0%N) :: (fst item, 1%N) ::
    map (fun r => point_dst (fst (fst r)))
      (fst (code_rows (fst item) 1%N (code _ _ _ (snd item))))) -> fst n = fst item).
  intros [Heq|[Heq|Hin]]; try (subst n; reflexivity).
  now apply code_rows_dest_bounds in Hin as [Howner _].
Qed.

(** A point index is at most the block's instruction count plus its parameter edge. *)
Lemma summarize_point_index {A K G} (kept : ptrie A)
    (item : positive * block positive K G) n :
  In n (summary_points (summarize kept item)) ->
    (snd n <= N.of_nat (length (code _ _ _ (snd item)) + 1))%N.
Proof.
  change (In n ((fst item, 0%N) :: (fst item, 1%N) ::
    map (fun r => point_dst (fst (fst r)))
      (fst (code_rows (fst item) 1%N (code _ _ _ (snd item))))) ->
    (snd n <= N.of_nat (length (code _ _ _ (snd item)) + 1))%N).
  rewrite Nat2N.inj_add. intros [Heq|[Heq|Hin]]; try (subst n; cbn; lia).
  apply code_rows_dest_bounds in Hin as [_ Hbound].
  change (snd n <= N.of_nat (length (code _ _ _ (snd item))) + 1)%N.
  rewrite N.add_comm. exact (proj2 Hbound).
Qed.

(** The entry and instruction points of a summary never repeat. *)
Lemma summarize_points_nodup {A K G} (kept : ptrie A)
    (item : positive * block positive K G) :
  NoDup (summary_points (summarize kept item)).
Proof.
  change (NoDup ((fst item, 0%N) :: (fst item, 1%N) ::
    map (fun r => point_dst (fst (fst r)))
      (fst (code_rows (fst item) 1%N (code _ _ _ (snd item)))))).
  constructor.
  - intros [Heq|Hin]; [discriminate|].
    apply code_rows_dest_bounds in Hin as [_ Hbound]; cbn in Hbound; lia.
  - constructor; [|apply code_rows_dest_nodup].
    intro Hin. apply code_rows_dest_bounds in Hin as [_ Hbound]; cbn in Hbound; lia.
Qed.

(** The exit point of a summary is one of its listed points. *)
Lemma summarize_exit_listed {A K G} (kept : ptrie A)
    (item : positive * block positive K G) :
  In (summary_exit (summarize kept item)) (summary_points (summarize kept item)).
Proof.
  change (In (fst item, snd (code_rows (fst item) 1%N (code _ _ _ (snd item))))
    ((fst item, 0%N) :: (fst item, 1%N) ::
      map (fun r => point_dst (fst (fst r)))
        (fst (code_rows (fst item) 1%N (code _ _ _ (snd item)))))).
  right. apply code_rows_endpoints.
Qed.

(** Both ends of an internal edge belong to its summary. *)
Lemma summarize_internal_endpoints {A K G} (kept : ptrie A)
    (item : positive * block positive K G) row :
  In row (summary_internal (summarize kept item)) ->
    In (point_src (fst (fst row))) (summary_points (summarize kept item)) /\
    In (point_dst (fst (fst row))) (summary_points (summarize kept item)).
Proof.
  change (In row ((PointEdge (fst item, 0%N) (fst item, 1%N) None,
      [], params _ _ _ (snd item)) ::
    fst (code_rows (fst item) 1%N (code _ _ _ (snd item)))) ->
    In (point_src (fst (fst row))) (summary_points (summarize kept item)) /\
    In (point_dst (fst (fst row))) (summary_points (summarize kept item))).
  intros [Heq|Hin].
  - subst row; split; [now left|now right; left].
  - split.
    + right. now apply (proj2 (code_rows_endpoints (fst item) 1%N
        (code _ _ _ (snd item)))).
    + right; right. apply in_map_iff. exists row; now split.
Qed.

Lemma summarize_internal_no_block {A K G} (kept : ptrie A)
    (item : positive * block positive K G) row :
  In row (summary_internal (summarize kept item)) ->
    point_block_edge (fst (fst row)) = None.
Proof.
  change (In row ((PointEdge (fst item, 0%N) (fst item, 1%N) None,
      [], params _ _ _ (snd item)) ::
    fst (code_rows (fst item) 1%N (code _ _ _ (snd item)))) ->
    point_block_edge (fst (fst row)) = None).
  intros [Heq|Hin]; [subst row; reflexivity|]. now apply code_rows_internal in Hin.
Qed.

(** Summary point lists of distinct blocks are disjoint. *)
Lemma summaries_points_nodup {A K G} (kept : ptrie A)
    (bs : list (positive * block positive K G)) :
  NoDup (map fst bs) ->
    NoDup (flat_map (fun item => summary_points (summarize kept item)) bs).
Proof.
  induction bs as [|item rest IH]; intro Hdistinct.
  - constructor.
  - inversion Hdistinct as [|id ids Hfresh Hrest]; subst.
    cbn [flat_map]. apply NoDup_app.
    + apply summarize_points_nodup.
    + now apply IH.
    + intros n Hitem Hin. apply in_flat_map in Hin.
      destruct Hin as [other [Hother Hpoint]].
      apply summarize_point_owner in Hitem.
      apply summarize_point_owner in Hpoint.
      apply Hfresh. rewrite <- Hitem, Hpoint. now apply in_map.
Qed.

(** Mapping the block summaries commutes with flattening their point lists. *)
Lemma flat_map_after_map {A B C} (f : B -> list C) (g : A -> B) xs :
  flat_map f (map g xs) = flat_map (fun x => f (g x)) xs.
Proof.
  induction xs as [|x rest IH]; cbn [map flat_map]; [reflexivity|now rewrite IH].
Qed.
Fixpoint param_defs {K} (b : positive) (i : nat) (xs : list positive)
    : list (positive * definition positive positive K) :=
  match xs with
  | [] => []
  | x :: rest => (x, Param b i) :: param_defs b (S i) rest
  end.
TimeFun param_defs.

Definition block_value_defs {K G} (item : positive * block positive K G)
    : list (positive * definition positive positive K) :=
  param_defs (fst item) 0 (params _ _ _ (snd item)) ++
    map (fun i => (fst (fst i), Op (snd (fst i)) (snd i))) (code _ _ _ (snd item)).
TimeFun block_value_defs.

Definition block_homes {K G} (item : positive * block positive K G)
    : list (positive * positive) :=
  map (fun x => (x, fst item)) (block_defs (snd item)).
TimeFun block_homes.

(** A table keeps the first row of each key, as `find_block` does. *)
Definition first_table {A B} (key : A -> positive) (rows : list (A * B)) : ptrie B :=
  fold_right (fun r m => PTrieCode.set (key (fst r)) (snd r) m) Empty rows.
TimeFun first_table.

(** The unshared specification lists every row of a key in row order. *)
Definition multi_table_specification {A} (key : A -> positive) (rows : list A)
    : ptrie (list A) :=
  fold_right (fun r m => PTrieCode.set (key r) (r :: index_row m (key r)) m) Empty rows.

(** A multi-table computes each row key once and retains row order. *)
Definition multi_table {A} (key : A -> positive) (rows : list A) : ptrie (list A) :=
  fold_right (fun r m =>
    let k := key r in PTrieCode.set k (r :: index_row m k) m) Empty rows.
TimeFun multi_table.

(** Sharing the row key leaves the table unchanged. *)
Lemma multi_table_agrees {A} (key : A -> positive) rows :
  multi_table key rows = multi_table_specification key rows.
Proof.
  reflexivity.
Qed.

(** A multi-table contains precisely the rows whose key matches its lookup key. *)
Lemma multi_table_spec {A} (key : A -> positive) (rows : list A) x y :
  In y (index_row (multi_table key rows) x) <-> In y rows /\ key y = x.
Proof.
  induction rows as [|a rest IH].
  - unfold multi_table, index_row; cbn [fold_right].
    rewrite PTrie.get_empty. cbn; tauto.
  - change (In y (index_row
      (PTrieCode.set (key a) (a :: index_row (multi_table key rest) (key a))
        (multi_table key rest)) x) <-> In y (a :: rest) /\ key y = x).
    unfold index_row at 1.
    destruct (Pos.eq_dec x (key a)) as [Heq | Hneq].
    + subst x. rewrite PTrie.get_set_same. cbn. rewrite IH; cbn; intuition congruence.
    + rewrite PTrie.get_set_other by exact Hneq.
      change (In y (index_row (multi_table key rest) x) <->
        In y (a :: rest) /\ key y = x).
      rewrite IH; cbn; intuition congruence.
Qed.

(** This recursive view records the first unvisited block in encounter order. *)
Fixpoint selected_blocks {K G} (seen : ptrie unit)
    (bs : list (positive * block positive K G)) : list (positive * block positive K G) :=
  match bs with
  | [] => []
  | item :: rest =>
    match trie_get (fst item) seen with
    | Some _ => selected_blocks seen rest
    | None => item :: selected_blocks (PTrieCode.set (fst item) tt seen) rest
    end
  end.

(** The tail-recursive selection accumulator is the reverse of the recursive view. *)
Lemma first_blocks_fold {K G} (bs : list (positive * block positive K G)) seen acc :
  snd (fold_left (fun state item =>
    match trie_get (fst item) (fst state) with
    | Some _ => state
    | None => (PTrieCode.set (fst item) tt (fst state), item :: snd state)
    end) bs (seen, acc)) = rev (selected_blocks seen bs) ++ acc.
Proof.
  revert seen acc; induction bs as [|item rest IH]; intros seen acc.
  - reflexivity.
  - cbn [fold_left selected_blocks fst snd].
    destruct (trie_get (fst item) seen) as [[]|].
    + apply IH.
    + rewrite IH. cbn [rev]. rewrite <- app_assoc. reflexivity.
Qed.

(** The public first-block selection agrees with its recursive view. *)
Lemma first_blocks_selected {K G} (bs : list (positive * block positive K G)) :
  first_blocks bs = selected_blocks Empty bs.
Proof.
  unfold first_blocks. rewrite first_blocks_fold, app_nil_r, rev_append_rev, app_nil_r.
  apply rev_involutive.
Qed.

(** Selection only removes blocks and excludes identifiers already in the table. *)
Lemma selected_blocks_in {K G} (bs : list (positive * block positive K G)) seen item :
  In item (selected_blocks seen bs) ->
    In item bs /\ trie_get (fst item) seen = None.
Proof.
  revert seen; induction bs as [|a rest IH]; intros seen Hin.
  - contradiction.
  - cbn [selected_blocks] in Hin.
    destruct (trie_get (fst a) seen) as [[]|] eqn:Hseen.
    + destruct (IH seen Hin) as [Hrest Hnone]. split; [now right|exact Hnone].
    + destruct Hin as [Heq | Hin].
      * subst item. split; [now left|exact Hseen].
      * destruct (IH _ Hin) as [Hrest Hnone]. split; [now right|].
        destruct (Pos.eq_dec (fst item) (fst a)) as [Heq | Hneq].
        -- rewrite Heq, PTrie.get_set_same in Hnone; discriminate.
        -- rewrite PTrie.get_set_other in Hnone by exact Hneq; exact Hnone.
Qed.

(** Selection emits each block identifier at most once. *)
Lemma selected_blocks_nodup {K G} (bs : list (positive * block positive K G)) seen :
  NoDup (map fst (selected_blocks seen bs)).
Proof.
  revert seen; induction bs as [|a rest IH]; intro seen.
  - constructor.
  - cbn [selected_blocks]. destruct (trie_get (fst a) seen) as [[]|].
    + apply IH.
    + cbn [map]. constructor; [|apply IH].
      intros Hin. apply in_map_iff in Hin.
      destruct Hin as [item [Heq Hin]].
      apply selected_blocks_in in Hin. destruct Hin as [_ Hnone].
      rewrite Heq, PTrie.get_set_same in Hnone; discriminate.
Qed.

(** Selection cannot increase the number of blocks. *)
Lemma selected_blocks_length {K G} (bs : list (positive * block positive K G)) seen :
  length (selected_blocks seen bs) <= length bs.
Proof.
  revert seen; induction bs as [|a rest IH]; intro seen.
  - reflexivity.
  - cbn [selected_blocks]. destruct (trie_get (fst a) seen) as [[]|]; cbn [length].
    + specialize (IH seen); lia.
    + specialize (IH (PTrieCode.set (fst a) tt seen)); lia.
Qed.

(** Selection preserves first lookup for every identifier not already visited. *)
Lemma selected_blocks_find {K G} (bs : list (positive * block positive K G)) seen b :
  find_block b (selected_blocks seen bs) =
    match trie_get b seen with Some _ => None | None => find_block b bs end.
Proof.
  revert seen; induction bs as [|[a body] rest IH]; intro seen.
  - cbn [selected_blocks find_block]. destruct (trie_get b seen); reflexivity.
  - cbn [selected_blocks fst]. destruct (trie_get a seen) as [[]|] eqn:Hseen.
    + rewrite IH. cbn [find_block].
      destruct (Pos.eqb b a) eqn:Heq; [|reflexivity].
      apply Pos.eqb_eq in Heq. subst b. rewrite Hseen; reflexivity.
    + cbn [find_block]. destruct (Pos.eqb b a) eqn:Heq.
      * apply Pos.eqb_eq in Heq. subst b. rewrite Hseen; reflexivity.
      * rewrite IH, PTrie.get_set_other by now apply Pos.eqb_neq.
        reflexivity.
Qed.

(** Selecting first blocks preserves the source interpreter's lookup exactly. *)
Lemma first_blocks_find {K G} (bs : list (positive * block positive K G)) b :
  find_block b (first_blocks bs) = find_block b bs.
Proof.
  rewrite first_blocks_selected, selected_blocks_find, PTrie.get_empty. reflexivity.
Qed.
(** Successful source lookup returns a block actually present in the source list. *)
Lemma find_block_in {K G} (bs : list (positive * block positive K G)) b body :
  find_block b bs = Some body -> In (b, body) bs.
Proof.
  induction bs as [|[a found] rest IH]; cbn [find_block]; intro Hfind.
  - discriminate.
  - destruct (Pos.eqb b a) eqn:Heq.
    + apply Pos.eqb_eq in Heq. inversion Hfind; subst; now left.
    + right; now apply IH.
Qed.

(** A block identifier is listed exactly when source lookup succeeds. *)
Lemma find_block_exists {K G} (bs : list (positive * block positive K G)) b :
  (exists body, find_block b bs = Some body) <-> In b (map fst bs).
Proof.
  induction bs as [|[a body] rest IH]; cbn [find_block map fst].
  - split; [intros [? H]; discriminate|contradiction].
  - destruct (Pos.eqb b a) eqn:Heq.
    + apply Pos.eqb_eq in Heq; subst b. split; intro H.
      * now left.
      * exists body; reflexivity.
    + apply Pos.eqb_neq in Heq. rewrite IH; cbn; intuition congruence.
Qed.

(** With distinct identifiers, membership identifies the selected block body. *)
Lemma find_block_of_in {K G} (bs : list (positive * block positive K G)) b body :
  NoDup (map fst bs) -> In (b, body) bs -> find_block b bs = Some body.
Proof.
  induction bs as [|[a found] rest IH]; intros Hdistinct Hin; [contradiction|].
  inversion Hdistinct as [|head tail Hfresh Htail]; subst.
  cbn [find_block]. destruct Hin as [Heq|Hin].
  - inversion Heq; subst; now rewrite Pos.eqb_refl.
  - destruct (Pos.eqb b a) eqn:Heq.
    + apply Pos.eqb_eq in Heq; subst b. exfalso; apply Hfresh.
      apply in_map_iff. exists (a, body); auto.
    + apply IH; assumption.
Qed.

(** Indexing a block projection retains exactly the first source block. *)
Lemma block_table_get {K G A} (f : block positive K G -> A)
    (bs : list (positive * block positive K G)) b :
  trie_get b (first_table PosKeyCode.encode (map (fun item => (fst item, f (snd item))) bs)) =
    option_map f (find_block b bs).
Proof.
  induction bs as [|[a body] rest IH].
  - unfold first_table; cbn [map fold_right find_block option_map].
    apply PTrie.get_empty.
  - change (trie_get b (PTrieCode.set a (f body)
      (first_table PosKeyCode.encode (map (fun item => (fst item, f (snd item))) rest))) =
      option_map f (if Pos.eqb b a then Some body else find_block b rest)).
    destruct (Pos.eqb b a) eqn:Heq.
    + apply Pos.eqb_eq in Heq. subst b. apply PTrie.get_set_same.
    + rewrite PTrie.get_set_other by now apply Pos.eqb_neq. exact IH.
Qed.

(** The block index recognizes precisely the identifiers supplied to it. *)
Lemma block_table_listed {K G A} (f : block positive K G -> A)
    (bs : list (positive * block positive K G)) b :
  is_listed (first_table PosKeyCode.encode (map (fun item => (fst item, f (snd item))) bs)) b
    = true <-> In b (map fst bs).
Proof.
  unfold is_listed. rewrite block_table_get, <- find_block_exists.
  destruct (find_block b bs) as [body|]; cbn [option_map].
  - split; [intro H; exists body; reflexivity|intro H; reflexivity].
  - split; [discriminate|intros [body H]; discriminate].
Qed.

(** Listed edges retain their source identifier and a syntactic target. *)
Lemma exit_edge_args_shape {G} b (e : exit positive G) edge args :
  In (edge, args) (exit_edge_args b e) ->
    edge_source edge = b /\ In (edge_target edge) (exit_targets e).
Proof.
  destruct e; cbn [exit_edge_args exit_targets]; intro Hin.
  - destruct Hin as [Heq|[]]. inversion Heq; subst; cbn; auto.
  - destruct Hin as [Heq|[Heq|[]]]; inversion Heq; subst; cbn; auto.
  - contradiction.
Qed.

(** Every syntactic successor has an outgoing edge occurrence. *)
Lemma exit_edge_args_successor {G} b (e : exit positive G) target :
  successor e target -> exists edge args, In (edge, args) (exit_edge_args b e) /\
    edge_source edge = b /\ edge_target edge = target.
Proof.
  destruct e as [next args|guard xs yes yes_args no no_args|values];
    cbn [successor exit_edge_args]; intro Hnext.
  - subst target. exists (BlockEdge b Jump_arm next), args; cbn; auto.
  - destruct Hnext as [Heq|Heq]; subst target.
    + exists (BlockEdge b True_arm yes), yes_args; cbn; auto.
    + exists (BlockEdge b False_arm no), no_args; cbn; auto.
  - contradiction.
Qed.

(** Exit targets and the language successor predicate describe the same identifiers. *)
Lemma exit_targets_successor {G} (e : exit positive G) target :
  In target (exit_targets e) <-> successor e target.
Proof.
  destruct e; cbn [exit_targets successor In]; intuition congruence.
Qed.
Record lang_prepared (K G : Type) := LangPrepared {
  lang_source : func positive K G;
  lang_entries : list positive;
  lang_blocks : list positive;
  lang_edges : list block_edge;
  lang_out : ptrie (list block_edge);
  lang_inc : ptrie (list block_edge);
  lang_points : list point_key;
  lang_point_edges : list point_edge;
  lang_point_out : ptrie (list point_edge);
  lang_point_inc : ptrie (list point_edge);
  lang_vars : var_tables positive;
  lang_ssa : ssa_tables positive block_edge positive K G;
  lang_point_tables : ssa_point_tables positive block_edge point_key point_edge positive
}.

Arguments LangPrepared {K G}.
Arguments lang_source {K G}.
Arguments lang_entries {K G}.
Arguments lang_blocks {K G}.
Arguments lang_edges {K G}.
Arguments lang_out {K G}.
Arguments lang_inc {K G}.
Arguments lang_points {K G}.
Arguments lang_point_edges {K G}.
Arguments lang_point_out {K G}.
Arguments lang_point_inc {K G}.
Arguments lang_vars {K G}.
Arguments lang_ssa {K G}.
Arguments lang_point_tables {K G}.

TimeFun lang_source.
TimeFun lang_entries.
TimeFun lang_blocks.
TimeFun lang_edges.
TimeFun lang_out.
TimeFun lang_inc.
TimeFun lang_points.
TimeFun lang_point_edges.
TimeFun lang_point_out.
TimeFun lang_point_inc.
TimeFun lang_vars.
TimeFun lang_ssa.
TimeFun lang_point_tables.

(** Preparation keeps the first block of each identifier, lists the edges and the entry
    that reach a kept block, and indexes their rows. *)
Definition lang_prepare {K G} (p : func positive K G) : lang_prepared K G :=
  let bs := first_blocks (blocks _ _ _ p) in
  let params_table := first_table PosKeyCode.encode
    (map (fun item => (fst item, params _ _ _ (snd item))) bs) in
  let ss := map (summarize params_table) bs in
  let block_rows := flat_map (fun item =>
    listed_edge_args params_table (fst item) (term _ _ _ (snd item))) bs in
  let edges := map fst block_rows in
  let rows := flat_map (fun s => summary_internal s ++ summary_outgoing s) ss in
  let pedges := map (fun r => fst (fst r)) rows in
  let entries :=
    if is_listed params_table (entry _ _ _ p) then [entry _ _ _ p] else [] in
  LangPrepared p entries (map fst bs) edges
    (multi_table edge_source edges) (multi_table edge_target edges)
    (flat_map summary_points ss) pedges
    (multi_table (fun e => PointKey.encode (point_src e)) pedges)
    (multi_table (fun e => PointKey.encode (point_dst e)) pedges)
    (VarTables
      (first_table PointEdge.encode (map (fun r => (fst (fst r), snd (fst r))) rows))
      (first_table PointEdge.encode (map (fun r => (fst (fst r), snd r)) rows))
      (first_table PointKey.encode
        (map (fun s => (summary_exit s, summary_returns s)) ss)))
    (SsaTables
      (inputs _ _ _ p ++ flat_map (fun item => block_defs (snd item)) bs)
      (flat_map (index_row params_table) entries)
      (flat_map (fun r => map (pair (fst r))
        (pair_args (index_row params_table (edge_target (fst r))) (snd r))) block_rows)
      (first_table PosKeyCode.encode (flat_map block_value_defs bs))
      (first_table PosKeyCode.encode
        (map (fun x => (x, entry _ _ _ p)) (inputs _ _ _ p) ++ flat_map block_homes bs))
      (entry _ _ _ p)
      params_table
      (first_table BlockEdge.encode (map (fun r =>
        (fst r, pair_args (index_row params_table (edge_target (fst r))) (snd r)))
        block_rows))
      (first_table BlockEdge.encode
        (flat_map (fun item =>
          listed_guards params_table (fst item) (term _ _ _ (snd item))) bs)))
    (SsaPointTables
      (first_table PosKeyCode.encode
        (map (fun s => (summary_block s, summary_points s)) ss))
      (first_table PosKeyCode.encode (map (fun s =>
        (summary_block s, map (fun r => fst (fst r)) (summary_internal s))) ss))
      (first_table PosKeyCode.encode (map (fun s => (summary_block s,
        PointEdge (summary_block s, 0%N) (summary_block s, 1%N) None)) ss))
      (PointEdge (entry _ _ _ p, 0%N) (entry _ _ _ p, 1%N) None)
      (first_table PointKey.encode
        (flat_map (fun s => map (fun n => (n, summary_block s)) (summary_points s)) ss))
      (entry _ _ _ p)
      (first_table PointEdge.encode (flat_map (fun r =>
        match point_block_edge (fst (fst r)) with
        | Some be => [(fst (fst r), be)]
        | None => []
        end) rows))
      params_table
      (first_table BlockEdge.encode block_rows)
      (first_table PosKeyCode.encode
        (flat_map (fun r => map (fun x => (x, point_src (fst (fst r)))) (snd r)) rows))).
TimeFun lang_prepare.

(** The structural maximum is the ordinary maximum of its two sizes. *)
Lemma graph_max_nat a b : graph_max a b = Nat.max a b.
Proof.
  revert b; induction a as [|a IH]; intros [|b]; cbn [graph_max Nat.max]; auto.
Qed.
(** An identifier's width is bounded by the maximum over its containing list. *)
Lemma vertex_width_in xs x : In x xs -> Pos.size_nat x <= vertex_width xs.
Proof.
  induction xs as [|a rest IH]; cbn [vertex_width fold_right]; intro Hin.
  - contradiction.
  - rewrite graph_max_nat. fold (vertex_width rest). destruct Hin as [Heq|Hin].
    + subst x. apply Nat.le_max_l.
    + specialize (IH Hin). pose proof (Nat.le_max_r (Pos.size_nat a) (vertex_width rest)).
      lia.
Qed.

(** The public function width covers every syntax identifier. *)
Lemma function_id_width {K G} (p : func positive K G) x :
  In x (function_ids p) -> Pos.size_nat x <= function_width p.
Proof.
  intro Hin. unfold function_width. rewrite graph_max_nat.
  eapply Nat.le_trans; [apply vertex_width_in; exact Hin|apply Nat.le_max_l].
Qed.

(** Every listed block identifier belongs to the source identifier inventory. *)
Lemma block_id_in_function {K G} (p : func positive K G) b body :
  In (b, body) (blocks _ _ _ p) -> In b (function_ids p).
Proof.
  intro Hin. unfold function_ids. right. apply in_or_app; right.
  apply in_flat_map. exists (b, body). split; [exact Hin|]. cbn; now left.
Qed.

(** Every listed block's exit target belongs to the source identifier inventory. *)
Lemma target_in_function {K G} (p : func positive K G) b body t :
  In (b, body) (blocks _ _ _ p) -> In t (exit_targets (term _ _ _ body)) ->
    In t (function_ids p).
Proof.
  intros Hin Htarget. unfold function_ids. right. apply in_or_app; right.
  apply in_flat_map. exists (b, body). split; [exact Hin|]. cbn; now right.
Qed.

(** Every retained entry is the identifier of a retained block. *)
Lemma lang_entries_nodes {K G} (p : func positive K G) b :
  In b (lang_entries (lang_prepare p)) -> In b (lang_blocks (lang_prepare p)).
Proof.
  change (In b (if is_listed (first_table PosKeyCode.encode
      (map (fun item => (fst item, params _ _ _ (snd item)))
        (first_blocks (blocks _ _ _ p)))) (entry _ _ _ p)
    then [entry _ _ _ p] else []) -> In b (map fst (first_blocks (blocks _ _ _ p)))).
  destruct (is_listed _ _) eqn:Hlisted.
  - cbn. intros [Heq|[]]; subst b. now apply block_table_listed in Hlisted.
  - contradiction.
Qed.

(** Every prepared edge comes from a retained source and targets a retained block. *)
Lemma lang_edges_shape {K G} (p : func positive K G) edge :
  In edge (lang_edges (lang_prepare p)) ->
  exists body, In (edge_source edge, body) (first_blocks (blocks _ _ _ p)) /\
    In (edge_target edge) (exit_targets (term _ _ _ body)) /\
    In (edge_target edge) (lang_blocks (lang_prepare p)).
Proof.
  set (bs := first_blocks (blocks _ _ _ p)).
  set (kept := first_table PosKeyCode.encode
    (map (fun item => (fst item, params _ _ _ (snd item))) bs)).
  change (In edge (map fst (flat_map (fun item =>
      listed_edge_args kept (fst item) (term _ _ _ (snd item))) bs)) ->
    exists body, In (edge_source edge, body) bs /\
      In (edge_target edge) (exit_targets (term _ _ _ body)) /\
      In (edge_target edge) (map fst bs)).
  intro Hin. apply in_map_iff in Hin.
  destruct Hin as [[edge' args] [Heq Hin]]. cbn in Heq; subst edge'.
  apply in_flat_map in Hin. destruct Hin as [item [Hitem Hin]].
  unfold listed_edge_args in Hin. apply filter_In in Hin.
  destruct Hin as [Hexit Htarget].
  destruct (exit_edge_args_shape _ _ _ _ Hexit) as [Hsource Hsyntax].
  exists (snd item). split.
  - rewrite Hsource. destruct item; exact Hitem.
  - split; [exact Hsyntax|].
    unfold kept in Htarget. now apply block_table_listed in Htarget.
Qed.

(** Every well-formed source successor remains an indexed block edge. *)
Lemma lang_edges_successor {K G} (p : func positive K G) b body target :
  NoDup (map fst (blocks _ _ _ p)) -> targets_listed p ->
  In (b, body) (blocks _ _ _ p) -> successor (term _ _ _ body) target ->
  exists edge, In edge (lang_edges (lang_prepare p)) /\
    edge_source edge = b /\ edge_target edge = target.
Proof.
  intros Hdistinct Htargets Hin Hnext.
  destruct (exit_edge_args_successor b _ target Hnext) as [edge [args [Hedge [Hsrc Hdst]]]].
  exists edge; split; [|now split].
  change (In edge (map fst (flat_map (fun item =>
    listed_edge_args (first_table PosKeyCode.encode
      (map (fun item => (fst item, params _ _ _ (snd item)))
        (first_blocks (blocks _ _ _ p))))
      (fst item) (term _ _ _ (snd item))) (first_blocks (blocks _ _ _ p))))).
  apply in_map_iff. exists (edge, args); split; [reflexivity|].
  apply in_flat_map. exists (b, body); split.
  - apply find_block_in. rewrite first_blocks_find. now apply find_block_of_in.
  - unfold listed_edge_args. apply filter_In; split; [exact Hedge|].
    cbn [fst]. rewrite Hdst. apply block_table_listed.
    apply find_block_exists. rewrite first_blocks_find. apply find_block_exists.
    apply (Htargets b body target Hin). now apply exit_targets_successor.
Qed.

(** Each retained block contributes at most two block edges. *)
Lemma lang_edges_length {K G} (p : func positive K G) :
  length (lang_edges (lang_prepare p)) <= 2 * length (lang_blocks (lang_prepare p)).
Proof.
  change (length (map fst (flat_map (fun item => listed_edge_args
    (first_table PosKeyCode.encode
      (map (fun item => (fst item, params _ _ _ (snd item)))
        (first_blocks (blocks _ _ _ p))))
    (fst item) (term _ _ _ (snd item))) (first_blocks (blocks _ _ _ p)))) <=
    2 * length (map fst (first_blocks (blocks _ _ _ p)))).
  rewrite !length_map.
  generalize (first_table PosKeyCode.encode
    (map (fun item => (fst item, params _ _ _ (snd item)))
      (first_blocks (blocks _ _ _ p)))) as kept.
  induction (first_blocks (blocks _ _ _ p)) as [|item rest IH]; intro kept.
  - reflexivity.
  - cbn [flat_map length]. rewrite length_app. specialize (IH kept).
    assert (Hedge : length (listed_edge_args kept (fst item) (term _ _ _ (snd item))) <= 2).
    { unfold listed_edge_args.
      eapply Nat.le_trans; [apply filter_length_le|].
      destruct (term _ _ _ (snd item)); cbn [exit_edge_args length]; lia. }
    lia.
Qed.

(** A retained block contributes all of its summary points to the point graph. *)
Lemma lang_summary_points {K G} (p : func positive K G) item n :
  In item (first_blocks (blocks _ _ _ p)) ->
  In n (summary_points (summarize
    (first_table PosKeyCode.encode (map (fun item =>
      (fst item, params _ _ _ (snd item))) (first_blocks (blocks _ _ _ p)))) item)) ->
  In n (lang_points (lang_prepare p)).
Proof.
  intros Hitem Hpoint. change (In n (flat_map summary_points
    (map (summarize (first_table PosKeyCode.encode
      (map (fun item => (fst item, params _ _ _ (snd item)))
        (first_blocks (blocks _ _ _ p))))) (first_blocks (blocks _ _ _ p))))).
  apply in_flat_map. eexists; split; [|exact Hpoint]. now apply in_map.
Qed.

(** Every retained block has its entry point in the point graph. *)
Lemma lang_point_zero {K G} (p : func positive K G) b :
  In b (lang_blocks (lang_prepare p)) -> In (b, 0%N) (lang_points (lang_prepare p)).
Proof.
  change (In b (map fst (first_blocks (blocks _ _ _ p))) ->
    In (b, 0%N) (lang_points (lang_prepare p))).
  intro Hin. apply in_map_iff in Hin. destruct Hin as [item [Heq Hin]].
  subst b. eapply lang_summary_points; [exact Hin|]. now left.
Qed.

(** Every point edge joins two points of the prepared graph. *)
Lemma lang_point_edges_nodes {K G} (p : func positive K G) edge :
  In edge (lang_point_edges (lang_prepare p)) ->
  In (point_src edge) (lang_points (lang_prepare p)) /\
  In (point_dst edge) (lang_points (lang_prepare p)).
Proof.
  set (bs := first_blocks (blocks _ _ _ p)).
  set (kept := first_table PosKeyCode.encode
    (map (fun item => (fst item, params _ _ _ (snd item))) bs)).
  change (In edge (map (fun r => fst (fst r))
    (flat_map (fun s => summary_internal s ++ summary_outgoing s)
      (map (summarize kept) bs))) ->
    In (point_src edge) (lang_points (lang_prepare p)) /\
    In (point_dst edge) (lang_points (lang_prepare p))).
  intro Hin. apply in_map_iff in Hin. destruct Hin as [row [Heq Hin]].
  subst edge. apply in_flat_map in Hin. destruct Hin as [summary [Hsummary Hin]].
  apply in_map_iff in Hsummary. destruct Hsummary as [item [Heq Hitem]].
  subst summary. apply in_app_or in Hin. destruct Hin as [Hinternal|Houtgoing].
  - destruct (summarize_internal_endpoints _ _ _ Hinternal) as [Hsrc Hdst].
    split; eapply lang_summary_points; eauto.
  - change (In row (map (fun ea =>
      (PointEdge (summary_exit (summarize kept item)) (edge_target (fst ea), 0%N)
        (Some (fst ea)), guard_uses (term _ _ _ (snd item)) ++ snd ea, []))
      (listed_edge_args kept (fst item) (term _ _ _ (snd item))))) in Houtgoing.
    apply in_map_iff in Houtgoing. destruct Houtgoing as [[be args] [Heq Hedge]].
    subst row. cbn [fst point_src point_dst]. split.
    + eapply lang_summary_points; [exact Hitem|apply summarize_exit_listed].
    + apply lang_point_zero. apply filter_In in Hedge as [_ Hlisted].
      unfold kept in Hlisted. now apply block_table_listed in Hlisted.
Qed.

(** Any nonnegative row weight is at most the sum of its containing list. *)
Lemma list_weight_member {A} (weight : A -> nat) xs x : In x xs ->
  weight x <= fold_right (fun y n => weight y + n) 0 xs.
Proof.
  induction xs as [|a rest IH]; intro Hin; [contradiction|].
  cbn [fold_right]. destruct Hin as [Heq|Hin]; [subst a; lia|].
  specialize (IH Hin); lia.
Qed.

Lemma block_code_size {K G} (p : func positive K G) id body :
  In (id, body) (blocks _ _ _ p) -> length (code _ _ _ body) <= function_size p.
Proof.
  intro Hin. pose proof (list_weight_member
    (fun item => length (code _ _ _ (snd item))) _ _ Hin) as Hcode.
  cbn [snd] in Hcode. unfold function_size. lia.
Qed.

(** Point identifiers and indices fit their source function's syntax budget. *)
Lemma lang_point_bounds {K G} (p : func positive K G) n :
  In n (lang_points (lang_prepare p)) ->
    Pos.size_nat (fst n) <= function_width p /\
    (snd n <= N.of_nat (function_size p + 1))%N.
Proof.
  set (bs := first_blocks (blocks _ _ _ p)).
  set (kept := first_table PosKeyCode.encode
    (map (fun item => (fst item, params _ _ _ (snd item))) bs)).
  change (In n (flat_map summary_points (map (summarize kept) bs)) ->
    Pos.size_nat (fst n) <= function_width p /\
    (snd n <= N.of_nat (function_size p + 1))%N).
  intro Hin. apply in_flat_map in Hin. destruct Hin as [summary [Hsummary Hpoint]].
  apply in_map_iff in Hsummary. destruct Hsummary as [[b body] [Heq Hbody]]. subst summary.
  assert (Hsource : In (b, body) (blocks _ _ _ p)).
  { unfold bs in Hbody. rewrite first_blocks_selected in Hbody.
    now apply selected_blocks_in in Hbody as [Hbody _]. }
  split.
  - rewrite (summarize_point_owner _ _ _ Hpoint). cbn [fst].
    apply function_id_width. now apply (block_id_in_function p b body).
  - pose proof (summarize_point_index _ _ _ Hpoint) as Hindex.
    pose proof (block_code_size _ _ _ Hsource) as Hlength.
    assert (HlengthN : (N.of_nat (length (code _ _ _ body) + 1) <=
      N.of_nat (function_size p + 1))%N) by (apply time_of_nat_le; lia).
    cbn [snd] in Hindex. lia.
Qed.

(** The size component of function width also bounds one extra point index. *)
Lemma function_index_width {K G} (p : func positive K G) i :
  (i <= N.of_nat (function_size p + 1))%N ->
    Pos.size_nat (N.succ_pos i) <= function_width p + 2.
Proof.
  intro Hindex.
  assert (Hwidth : Pos.size_nat (Pos.of_succ_nat (function_size p)) <= function_width p).
  { unfold function_width. rewrite graph_max_nat. apply Nat.le_max_r. }
  pose proof (Pos.size_nat_upper (Pos.of_succ_nat (function_size p))) as Hvalue.
  pose proof (Nat.pow_le_mono_r 2 _ _ ltac:(discriminate) Hwidth) as Hpower.
  rewrite SuccNat2Pos.id_succ in Hvalue.
  assert (Hindex_nat : N.to_nat i <= function_size p + 1) by lia.
  assert (Hencode : Pos.to_nat (N.succ_pos i) = S (N.to_nat i)).
  { change (N.to_nat (N.pos (N.succ_pos i)) = S (N.to_nat i)).
    rewrite N.succ_pos_spec, N2Nat.inj_succ. reflexivity. }
  apply Pos.size_nat_least. rewrite Hencode, Nat.pow_add_r. cbn [Nat.pow]. nia.
Qed.

(** The point pair code needs only a fixed multiple of source identifier width. *)
Lemma lang_point_key_width {K G} (p : func positive K G) n :
  In n (lang_points (lang_prepare p)) -> PointKey.bits n <= 4 * (function_width p + 1).
Proof.
  intro Hin. destruct (lang_point_bounds _ _ Hin) as [Hblock Hindex].
  pose proof (function_index_width _ _ Hindex) as Hcounter.
  unfold PointKey.bits, PointKey.encode, pair_code.
  cbn [PosKeyT.encode NKeyT.encode]. rewrite glue_bits.
  change (2 * Pos.size_nat (fst n) + Pos.size_nat (N.succ_pos (snd n)) - 1 <=
    4 * (function_width p + 1)). lia.
Qed.

(** A projected block edge uses the block components of its point endpoints. *)
Lemma lang_point_edge_block_sides {K G} (p : func positive K G) edge be :
  In edge (lang_point_edges (lang_prepare p)) -> point_block_edge edge = Some be ->
    edge_source be = fst (point_src edge) /\ edge_target be = fst (point_dst edge).
Proof.
  set (bs := first_blocks (blocks _ _ _ p)).
  set (kept := first_table PosKeyCode.encode
    (map (fun item => (fst item, params _ _ _ (snd item))) bs)).
  change (In edge (map (fun r => fst (fst r))
    (flat_map (fun s => summary_internal s ++ summary_outgoing s)
      (map (summarize kept) bs))) -> point_block_edge edge = Some be ->
    edge_source be = fst (point_src edge) /\ edge_target be = fst (point_dst edge)).
  intros Hin Hprojection. apply in_map_iff in Hin. destruct Hin as [row [Heq Hin]].
  subst edge. apply in_flat_map in Hin. destruct Hin as [summary [Hsummary Hin]].
  apply in_map_iff in Hsummary. destruct Hsummary as [item [Heq Hitem]].
  subst summary. apply in_app_or in Hin. destruct Hin as [Hinternal|Houtgoing].
  - rewrite (summarize_internal_no_block _ _ _ Hinternal) in Hprojection; discriminate.
  - change (In row (map (fun ea =>
      (PointEdge (summary_exit (summarize kept item)) (edge_target (fst ea), 0%N)
        (Some (fst ea)), guard_uses (term _ _ _ (snd item)) ++ snd ea, []))
      (listed_edge_args kept (fst item) (term _ _ _ (snd item))))) in Houtgoing.
    apply in_map_iff in Houtgoing. destruct Houtgoing as [[be' args] [Heq Hedge]].
    subst row. cbn [fst point_block_edge] in Hprojection. inversion Hprojection; subst be'.
    apply filter_In in Hedge as [Hsyntax _].
    destruct (exit_edge_args_shape _ _ _ _ Hsyntax) as [Hsource _].
    change (edge_source be = fst item /\ edge_target be = edge_target be).
    split; [exact Hsource|reflexivity].
Qed.

Lemma block_edge_width_from_ends edge width :
  Pos.size_nat (edge_source edge) <= width -> Pos.size_nat (edge_target edge) <= width ->
    BlockEdge.bits edge <= 4 * (width + 1).
Proof.
  intros Hsource Htarget.
  unfold BlockEdge.bits, BlockEdge.encode, block_edge_tuple,
    EdgeTupleKey.encode, EdgeArmTargetKey.encode, pair_code.
  cbn [fst snd PosKeyT.encode]. rewrite !glue_bits.
  destruct (edge_arm edge); cbn [ArmKeyT.encode Pos.size_nat]; lia.
Qed.

Module Prepared (O : OPS) <: TYPE.
  Definition t := lang_prepared O.K O.G.
End Prepared.

Module PrepareCode (O : OPS) (Q : TYPE with Definition t := lang_prepared O.K O.G)
    <: LANG_PREPARE_OPS O Q.
  Definition prepare (p : func positive O.K O.G) : Q.t := lang_prepare p.
End PrepareCode.

Module BlockCfgCode (O : OPS) (Q : TYPE with Definition t := lang_prepared O.K O.G)
    <: CFG_INDEXED_OPS Q PosKeyCode BlockEdge.
  Definition entries (q : Q.t) := lang_entries q.
  Definition edges (q : Q.t) := lang_edges q.
  Definition src (_ : Q.t) (e : block_edge) := edge_source e.
  Definition dst (_ : Q.t) (e : block_edge) := edge_target e.
  Definition nodes (q : Q.t) := lang_blocks q.
  Definition out (q : Q.t) (b : positive) := index_row (lang_out q) (PosKeyCode.encode b).
  Definition inc (q : Q.t) (b : positive) := index_row (lang_inc q) (PosKeyCode.encode b).
End BlockCfgCode.

Module BlockCfg (O : OPS) (Q : TYPE with Definition t := lang_prepared O.K O.G)
    <: CFG Q PosKey BlockEdge.
  Include BlockCfgCode O Q.
  Definition wf (p : Q.t) := p = lang_prepare (lang_source p).
  Lemma nodes_nodup : forall p, wf p -> NoDup (nodes p).
  Proof.
    intros p Hwf. unfold wf in Hwf. rewrite Hwf.
    unfold nodes; cbn [lang_prepare lang_blocks].
    rewrite first_blocks_selected. apply selected_blocks_nodup.
  Qed.
  Lemma entries_nodes : forall p n, wf p -> In n (entries p) -> In n (nodes p).
  Proof.
    intros p n Hwf. unfold wf in Hwf. rewrite Hwf.
    apply lang_entries_nodes.
  Qed.
  Lemma edges_nodes : forall p e, wf p -> In e (edges p) ->
    In (src p e) (nodes p) /\ In (dst p e) (nodes p).
  Proof.
    intros p e Hwf. unfold wf in Hwf. rewrite Hwf. intro Hin.
    destruct (lang_edges_shape _ _ Hin) as [body [Hsource [_ Htarget]]].
    split; [|exact Htarget].
    unfold nodes; cbn [lang_prepare lang_blocks].
    apply in_map_iff. exists (edge_source e, body); auto.
  Qed.
  Lemma out_spec : forall p n e, wf p ->
    (In e (out p n) <-> In e (edges p) /\ src p e = n).
  Proof.
    intros p n e Hwf. unfold wf in Hwf. rewrite Hwf.
    unfold out, edges, src; cbn [lang_prepare lang_out lang_edges].
    apply multi_table_spec.
  Qed.
  Lemma inc_spec : forall p n e, wf p ->
    (In e (inc p n) <-> In e (edges p) /\ dst p e = n).
  Proof.
    intros p n e Hwf. unfold wf in Hwf. rewrite Hwf.
    unfold inc, edges, dst; cbn [lang_prepare lang_inc lang_edges].
    apply multi_table_spec.
  Qed.
End BlockCfg.

Module BlockCfgT (O : OPS) (Q : TYPE with Definition t := lang_prepared O.K O.G)
    <: CFG_T Q PosKeyT BlockEdge.
  Include BlockCfg O Q.
  TimeFun entries.
  TimeFun edges.
  TimeFun src.
  TimeFun dst.
  TimeFun nodes.
  TimeFun out.
  TimeFun inc.
  Definition c_cfg : N := 4.
  Definition c_cfg_adj : N := 8.
  Lemma T_entries_le : forall p,
    (T_entries p <= c_cfg * N.of_nat (length (entries p) + 1))%N.
  Proof.
    intro p. unfold c_cfg. time_unfold T_entries. time_unfold @T_lang_entries.
    rewrite Nat2N.inj_add. time_cbn; nia.
  Qed.
  Lemma T_edges_le : forall p,
    (T_edges p <= c_cfg * N.of_nat (length (edges p) + 1))%N.
  Proof.
    intro p. unfold c_cfg. time_unfold T_edges. time_unfold @T_lang_edges.
    rewrite Nat2N.inj_add. time_cbn; nia.
  Qed.
  Lemma T_src_le : forall p e, (T_src p e <= c_cfg)%N.
  Proof.
    intros p e. unfold c_cfg. time_unfold T_src. time_unfold T_edge_source.
    time_cbn; lia.
  Qed.
  Lemma T_dst_le : forall p e, (T_dst p e <= c_cfg)%N.
  Proof.
    intros p e. unfold c_cfg. time_unfold T_dst. time_unfold T_edge_target.
    time_cbn; lia.
  Qed.
  Lemma T_nodes_le : forall p,
    (T_nodes p <= c_cfg_adj * N.of_nat (length (nodes p) + 1))%N.
  Proof.
    intro p. unfold c_cfg_adj. time_unfold T_nodes. time_unfold @T_lang_blocks.
    rewrite Nat2N.inj_add. time_cbn; nia.
  Qed.
  Lemma T_out_le : forall p n,
    (T_out p n <= c_cfg_adj * N.of_nat (PosKeyT.bits n + length (out p n) + 1))%N.
  Proof.
    intros p n. unfold c_cfg_adj. time_unfold T_out.
    time_unfold @T_lang_out. time_unfold @T_index_row.
    time_unfold PosKeyT.T_encode.
    rewrite !Nat2N.inj_add. time_cbn.
    unfold PosKeyT.bits, PosKeyT.encode, PosKeyCode.encode; PTrieT.trie_get_le; nia.
  Qed.
  Lemma T_inc_le : forall p n,
    (T_inc p n <= c_cfg_adj * N.of_nat (PosKeyT.bits n + length (inc p n) + 1))%N.
  Proof.
    intros p n. unfold c_cfg_adj. time_unfold T_inc.
    time_unfold @T_lang_inc. time_unfold @T_index_row.
    time_unfold PosKeyT.T_encode.
    rewrite !Nat2N.inj_add. time_cbn.
    unfold PosKeyT.bits, PosKeyT.encode, PosKeyCode.encode; PTrieT.trie_get_le; nia.
  Qed.
  (** Edge enumeration is linear in its output. *)
  Lemma edges_complexity :
    T_edges p ∈ 𝑂(N.of_nat (length (edges p))) for p.
  Proof.
    apply bigO_intro with (c := c_cfg). intros p _.
    pose proof (T_edges_le p) as Htime.
    rewrite Nat2N.inj_add in Htime. nia.
  Qed.
  (** Entry enumeration is linear in its output. *)
  Lemma entries_complexity :
    T_entries p ∈ 𝑂(N.of_nat (length (entries p))) for p.
  Proof.
    apply bigO_intro with (c := c_cfg). intros p _.
    pose proof (T_entries_le p) as Htime.
    rewrite Nat2N.inj_add in Htime. nia.
  Qed.
  (** Outgoing lookup is linear in the node key and returned edges. *)
  Lemma out_complexity :
    T_out p n ∈ 𝑂(N.of_nat (PosKeyT.bits n + length (out p n))) for (p, n).
  Proof.
    apply bigO_intro with (c := c_cfg_adj). intros [p n] _.
    pose proof (T_out_le p n) as Htime.
    rewrite Nat2N.inj_add in Htime. nia.
  Qed.
  (** Incoming lookup is linear in the node key and returned edges. *)
  Lemma inc_complexity :
    T_inc p n ∈ 𝑂(N.of_nat (PosKeyT.bits n + length (inc p n))) for (p, n).
  Proof.
    apply bigO_intro with (c := c_cfg_adj). intros [p n] _.
    pose proof (T_inc_le p n) as Htime.
    rewrite Nat2N.inj_add in Htime. nia.
  Qed.
  (** Node enumeration is linear in its output. *)
  Lemma nodes_complexity :
    T_nodes p ∈ 𝑂(N.of_nat (length (nodes p))) for p.
  Proof.
    apply bigO_intro with (c := c_cfg_adj). intros p _.
    pose proof (T_nodes_le p) as Htime.
    rewrite Nat2N.inj_add in Htime. nia.
  Qed.
End BlockCfgT.

Module PointCfgCode (O : OPS) (Q : TYPE with Definition t := lang_prepared O.K O.G)
    <: CFG_INDEXED_OPS Q PointKey PointEdge.
  Definition entries (q : Q.t) : list point_key :=
    map (fun b => (b, 0%N)) (lang_entries q).
  Definition edges (q : Q.t) := lang_point_edges q.
  Definition src (_ : Q.t) (e : point_edge) := point_src e.
  Definition dst (_ : Q.t) (e : point_edge) := point_dst e.
  Definition nodes (q : Q.t) := lang_points q.
  Definition out (q : Q.t) (n : point_key) := index_row (lang_point_out q) (PointKey.encode n).
  Definition inc (q : Q.t) (n : point_key) := index_row (lang_point_inc q) (PointKey.encode n).
End PointCfgCode.

Module PointCfg (O : OPS) (Q : TYPE with Definition t := lang_prepared O.K O.G)
    <: CFG Q PointKey PointEdge.
  Include PointCfgCode O Q.
  Definition wf (p : Q.t) := p = lang_prepare (lang_source p).
  Lemma nodes_nodup : forall p, wf p -> NoDup (nodes p).
  Proof.
    intros p Hwf. unfold wf in Hwf. rewrite Hwf.
    change (NoDup (flat_map summary_points
      (map (summarize (first_table PosKeyCode.encode
        (map (fun item => (fst item, params _ _ _ (snd item)))
          (first_blocks (blocks _ _ _ (lang_source p))))))
        (first_blocks (blocks _ _ _ (lang_source p)))))).
    rewrite flat_map_after_map. apply summaries_points_nodup.
    rewrite first_blocks_selected. apply selected_blocks_nodup.
  Qed.
  Lemma entries_nodes : forall p n, wf p -> In n (entries p) -> In n (nodes p).
  Proof.
    intros p n Hwf. unfold wf in Hwf. rewrite Hwf.
    unfold entries, nodes. intro Hin. apply in_map_iff in Hin.
    destruct Hin as [b [Heq Hin]]. subst n. apply lang_point_zero.
    now apply lang_entries_nodes.
  Qed.
  Lemma edges_nodes : forall p e, wf p -> In e (edges p) ->
    In (src p e) (nodes p) /\ In (dst p e) (nodes p).
  Proof.
    intros p e Hwf. unfold wf in Hwf. rewrite Hwf.
    apply lang_point_edges_nodes.
  Qed.
  Lemma out_spec : forall p n e, wf p ->
    (In e (out p n) <-> In e (edges p) /\ src p e = n).
  Proof.
    intros p n e Hwf. unfold wf in Hwf. rewrite Hwf.
    unfold out, edges, src; cbn [lang_prepare lang_point_out lang_point_edges].
    rewrite multi_table_spec.
    split; intros [Hin Heq]; split; try exact Hin.
    - now apply PointKey.encode_inj in Heq.
    - now rewrite Heq.
  Qed.
  Lemma inc_spec : forall p n e, wf p ->
    (In e (inc p n) <-> In e (edges p) /\ dst p e = n).
  Proof.
    intros p n e Hwf. unfold wf in Hwf. rewrite Hwf.
    unfold inc, edges, dst; cbn [lang_prepare lang_point_inc lang_point_edges].
    rewrite multi_table_spec.
    split; intros [Hin Heq]; split; try exact Hin.
    - now apply PointKey.encode_inj in Heq.
    - now rewrite Heq.
  Qed.
End PointCfg.

Module PointCfgT (O : OPS) (Q : TYPE with Definition t := lang_prepared O.K O.G)
    <: CFG_T Q PointKey PointEdge.
  Include PointCfg O Q.
  TimeFun entries.
  TimeFun edges.
  TimeFun src.
  TimeFun dst.
  TimeFun nodes.
  TimeFun out.
  TimeFun inc.
  Definition c_cfg : N := 8.
  Definition c_cfg_adj : N := 8 * (PointKey.c_key + 1).
  Lemma T_entries_le : forall p,
    (T_entries p <= c_cfg * N.of_nat (length (entries p) + 1))%N.
  Proof.
    intro p. unfold c_cfg, entries. rewrite length_map.
    pose proof (ListDef.T_map_le (fun b : positive => (b, 0%N)) (fun _ => 1%N)
      1%N (lang_entries p) (fun _ => N.le_refl _)) as Hmap.
    time_unfold T_entries. time_unfold @T_lang_entries.
    time_simpl; time_cbn. rewrite Nat2N.inj_add; nia.
  Qed.
  Lemma T_edges_le : forall p,
    (T_edges p <= c_cfg * N.of_nat (length (edges p) + 1))%N.
  Proof.
    intro p. unfold c_cfg. time_unfold T_edges. time_unfold @T_lang_point_edges.
    rewrite Nat2N.inj_add. time_cbn; nia.
  Qed.
  Lemma T_src_le : forall p e, (T_src p e <= c_cfg)%N.
  Proof.
    intros p e. unfold c_cfg. time_unfold T_src. time_unfold T_point_src.
    time_cbn; lia.
  Qed.
  Lemma T_dst_le : forall p e, (T_dst p e <= c_cfg)%N.
  Proof.
    intros p e. unfold c_cfg. time_unfold T_dst. time_unfold T_point_dst.
    time_cbn; lia.
  Qed.
  Lemma T_nodes_le : forall p,
    (T_nodes p <= c_cfg_adj * N.of_nat (length (nodes p) + 1))%N.
  Proof.
    intro p. unfold c_cfg_adj. time_unfold T_nodes. time_unfold @T_lang_points.
    rewrite Nat2N.inj_add. time_cbn; nia.
  Qed.
  Lemma T_out_le : forall p n,
    (T_out p n <= c_cfg_adj * N.of_nat (PointKey.bits n + length (out p n) + 1))%N.
  Proof.
    intros p n. pose proof (PointKey.T_encode_le n) as Hkey.
    unfold c_cfg_adj. time_unfold T_out.
    time_unfold @T_lang_point_out. time_unfold @T_index_row.
    PTrieT.trie_get_le. change (Pos.size_nat (PointKey.encode n)) with (PointKey.bits n) in *.
    rewrite !Nat2N.inj_add in *; nia.
  Qed.
  Lemma T_inc_le : forall p n,
    (T_inc p n <= c_cfg_adj * N.of_nat (PointKey.bits n + length (inc p n) + 1))%N.
  Proof.
    intros p n. pose proof (PointKey.T_encode_le n) as Hkey.
    unfold c_cfg_adj. time_unfold T_inc.
    time_unfold @T_lang_point_inc. time_unfold @T_index_row.
    PTrieT.trie_get_le. change (Pos.size_nat (PointKey.encode n)) with (PointKey.bits n) in *.
    rewrite !Nat2N.inj_add in *; nia.
  Qed.
  (** Edge enumeration is linear in its output. *)
  Lemma edges_complexity :
    T_edges p ∈ 𝑂(N.of_nat (length (edges p))) for p.
  Proof.
    apply bigO_intro with (c := c_cfg). intros p _.
    pose proof (T_edges_le p) as Htime.
    rewrite Nat2N.inj_add in Htime. nia.
  Qed.
  (** Entry enumeration is linear in its output. *)
  Lemma entries_complexity :
    T_entries p ∈ 𝑂(N.of_nat (length (entries p))) for p.
  Proof.
    apply bigO_intro with (c := c_cfg). intros p _.
    pose proof (T_entries_le p) as Htime.
    rewrite Nat2N.inj_add in Htime. nia.
  Qed.
  (** Outgoing lookup is linear in the node key and returned edges. *)
  Lemma out_complexity :
    T_out p n ∈ 𝑂(N.of_nat (PointKey.bits n + length (out p n))) for (p, n).
  Proof.
    apply bigO_intro with (c := c_cfg_adj). intros [p n] _.
    pose proof (T_out_le p n) as Htime.
    rewrite Nat2N.inj_add in Htime. nia.
  Qed.
  (** Incoming lookup is linear in the node key and returned edges. *)
  Lemma inc_complexity :
    T_inc p n ∈ 𝑂(N.of_nat (PointKey.bits n + length (inc p n))) for (p, n).
  Proof.
    apply bigO_intro with (c := c_cfg_adj). intros [p n] _.
    pose proof (T_inc_le p n) as Htime.
    rewrite Nat2N.inj_add in Htime. nia.
  Qed.
  (** Node enumeration is linear in its output. *)
  Lemma nodes_complexity :
    T_nodes p ∈ 𝑂(N.of_nat (length (nodes p))) for p.
  Proof.
    apply bigO_intro with (c := c_cfg_adj). intros p _.
    pose proof (T_nodes_le p) as Htime.
    rewrite Nat2N.inj_add in Htime. nia.
  Qed.
End PointCfgT.

Module PresentVarsData (O : OPS) (Q : TYPE with Definition t := lang_prepared O.K O.G)
    <: VARS_DATA_T Q PosKeyT.
  Definition tables (q : Q.t) := lang_vars q.
  TimeFun tables.
  Definition c_tables : N := 2.
  Lemma T_tables_le : forall q, (T_tables q <= c_tables)%N.
  Proof.
    intro q. unfold c_tables. time_unfold T_tables. time_unfold @T_lang_vars.
    time_cbn; lia.
  Qed.
End PresentVarsData.

Module PresentSsaData (O : OPS)
    (K : TYPE with Definition t := O.K) (G : TYPE with Definition t := O.G)
    (Q : TYPE with Definition t := lang_prepared O.K O.G)
    <: SSA_DATA_T Q PosKeyT BlockEdge PosKeyT K G.
  Definition tables (q : Q.t) := lang_ssa q.
  TimeFun tables.
  Definition c_tables : N := 2.
  Lemma T_tables_le : forall q, (T_tables q <= c_tables)%N.
  Proof.
    intro q. unfold c_tables. time_unfold T_tables. time_unfold @T_lang_ssa.
    time_cbn; lia.
  Qed.
End PresentSsaData.

Module PresentPointsData (O : OPS) (Q : TYPE with Definition t := lang_prepared O.K O.G)
    <: SSA_POINTS_DATA_T Q PosKeyT BlockEdge PointKey PointEdge PosKeyT.
  Definition tables (q : Q.t) := lang_point_tables q.
  TimeFun tables.
  Definition c_tables : N := 2.
  Lemma T_tables_le : forall q, (T_tables q <= c_tables)%N.
  Proof.
    intro q. unfold c_tables. time_unfold T_tables. time_unfold @T_lang_point_tables.
    time_cbn; lia.
  Qed.
End PresentPointsData.

Definition present_row_count {A} (keys : list positive) (rows : ptrie (list A)) : nat :=
  fold_right (fun k n => length (index_row rows k) + n) 0 keys.

Lemma present_row_count_empty {A} keys : @present_row_count A keys Empty = 0.
Proof.
  induction keys as [|k rest IH]; [reflexivity|].
  unfold present_row_count at 1; cbn [fold_right].
  unfold index_row at 1. rewrite PTrie.get_empty. exact IH.
Qed.

Lemma present_row_count_other {A} keys (rows : ptrie (list A)) id values :
  ~ In id keys ->
  present_row_count keys (PTrieCode.set id values rows) = present_row_count keys rows.
Proof.
  induction keys as [|k rest IH]; intro Hfresh; [reflexivity|].
  unfold present_row_count at 1 2; cbn [fold_right].
  assert (Hk : k <> id) by (intro Heq; subst k; apply Hfresh; now left).
  unfold index_row at 1. rewrite PTrie.get_set_other by exact Hk.
  fold (present_row_count rest (PTrieCode.set id values rows)).
  fold (present_row_count rest rows). rewrite IH; [reflexivity|].
  intro Hin; apply Hfresh; now right.
Qed.

Lemma present_row_count_set {A} keys (rows : ptrie (list A)) id values :
  NoDup keys -> present_row_count keys (PTrieCode.set id values rows) <=
    length values + present_row_count keys rows.
Proof.
  induction keys as [|k rest IH]; intro Hdistinct; [cbn [present_row_count fold_right]; lia|].
  inversion Hdistinct as [|a tail Hfresh Hrest]; subst.
  unfold present_row_count at 1 2; cbn [fold_right].
  fold (present_row_count rest (PTrieCode.set id values rows)).
  fold (present_row_count rest rows).
  destruct (Pos.eq_dec k id) as [Heq|Hneq].
  - subst k. unfold index_row at 1. rewrite PTrie.get_set_same.
    rewrite present_row_count_other by exact Hfresh. lia.
  - unfold index_row at 1. rewrite PTrie.get_set_other by exact Hneq.
    specialize (IH Hrest).
    change (length (index_row rows k) + present_row_count rest (PTrieCode.set id values rows)
      <= length values + (length (index_row rows k) + present_row_count rest rows)). lia.
Qed.

Lemma present_first_table_count {A B} (key : A -> positive) keys
    (rows : list (A * list B)) : NoDup keys ->
  present_row_count keys (first_table key rows) <=
    fold_right (fun row n => length (snd row) + n) 0 rows.
Proof.
  intro Hdistinct. induction rows as [|row rest IH].
  - change (@present_row_count B keys Empty <= 0). rewrite present_row_count_empty; lia.
  - change (present_row_count keys (PTrieCode.set (key (fst row)) (snd row)
      (first_table key rest)) <= length (snd row) +
        fold_right (fun row n => length (snd row) + n) 0 rest).
    eapply Nat.le_trans; [apply present_row_count_set; exact Hdistinct|]. lia.
Qed.

Lemma present_map_injective_nodup {A B} (f : A -> B) xs :
  (forall x y, f x = f y -> x = y) -> NoDup xs -> NoDup (map f xs).
Proof.
  intros Hinj Hdistinct. induction Hdistinct as [|x rest Hfresh Hrest IH].
  - constructor.
  - cbn [map]. constructor; [|exact IH]. intro Hin.
    apply in_map_iff in Hin as [y [Heq Hin]]. apply Hinj in Heq; subst y. contradiction.
Qed.

Lemma present_map_flat_map {A B C} (f : B -> C) (g : A -> list B) xs :
  map f (flat_map g xs) = flat_map (fun x => map f (g x)) xs.
Proof.
  induction xs as [|x rest IH]; cbn [flat_map map]; [reflexivity|].
  now rewrite map_app, IH.
Qed.

Lemma summarize_internal_edges_nodup {A K G} (kept : ptrie A)
    (item : positive * block positive K G) :
  NoDup (map (fun row => fst (fst row)) (summary_internal (summarize kept item))).
Proof.
  apply (NoDup_map_inv point_dst).
  rewrite map_map.
  pose proof (summarize_points_nodup kept item) as Hpoints.
  change (NoDup ((fst item, 0%N) ::
    map (fun row => point_dst (fst (fst row)))
      (summary_internal (summarize kept item)))) in Hpoints.
  now inversion Hpoints.
Qed.

Lemma summarize_outgoing_edges_nodup {A K G} (kept : ptrie A)
    (item : positive * block positive K G) :
  NoDup (map (fun row => fst (fst row)) (summary_outgoing (summarize kept item))).
Proof.
  destruct item as [b [ps cs term]]. destruct term;
    cbn [summarize summary_outgoing fst snd Lang.term listed_edge_args exit_edge_args
      filter edge_target map];
    repeat match goal with |- context [if ?flag then _ else _] => destruct flag end;
    repeat constructor; cbn; intuition discriminate.
Qed.

Lemma summarize_outgoing_block {A K G} (kept : ptrie A)
    (item : positive * block positive K G) row :
  In row (summary_outgoing (summarize kept item)) ->
    exists be, point_block_edge (fst (fst row)) = Some be.
Proof.
  change (In row (map (fun ea =>
    (PointEdge (summary_exit (summarize kept item)) (edge_target (fst ea), 0%N)
      (Some (fst ea)), guard_uses (term _ _ _ (snd item)) ++ snd ea, ([] : list positive)))
    (listed_edge_args kept (fst item) (term _ _ _ (snd item)))) ->
    exists be, point_block_edge (fst (fst row)) = Some be).
  intro Hin. apply in_map_iff in Hin as [ea [Heq Hin]]. subst row. eexists; reflexivity.
Qed.

Lemma summarize_edges_nodup {A K G} (kept : ptrie A)
    (item : positive * block positive K G) :
  NoDup (map (fun row => fst (fst row))
    (summary_internal (summarize kept item) ++ summary_outgoing (summarize kept item))).
Proof.
  rewrite map_app. apply NoDup_app.
  - apply summarize_internal_edges_nodup.
  - apply summarize_outgoing_edges_nodup.
  - intros edge Hi Ho. apply in_map_iff in Hi as [ri [Hei Hi]].
    apply in_map_iff in Ho as [ro [Heo Ho]].
    pose proof (summarize_internal_no_block _ _ _ Hi) as Hnone.
    destruct (summarize_outgoing_block _ _ _ Ho) as [be Hsome].
    rewrite Hei in Hnone. rewrite Heo in Hsome. congruence.
Qed.

Lemma summarize_edge_owner {A K G} (kept : ptrie A)
    (item : positive * block positive K G) row :
  In row (summary_internal (summarize kept item) ++ summary_outgoing (summarize kept item)) ->
    fst (point_src (fst (fst row))) = fst item.
Proof.
  intro Hin. apply in_app_or in Hin as [Hi|Ho].
  - apply summarize_internal_endpoints in Hi as [Hs _].
    now apply summarize_point_owner in Hs.
  - change (In row (map (fun ea =>
      (PointEdge (summary_exit (summarize kept item)) (edge_target (fst ea), 0%N)
        (Some (fst ea)), guard_uses (term _ _ _ (snd item)) ++ snd ea, ([] : list positive)))
      (listed_edge_args kept (fst item) (term _ _ _ (snd item))))) in Ho.
    apply in_map_iff in Ho as [ea [Heq Hin]]. subst row. reflexivity.
Qed.

Lemma summaries_edges_nodup {A K G} (kept : ptrie A)
    (bs : list (positive * block positive K G)) :
  NoDup (map fst bs) ->
  NoDup (flat_map (fun item => map (fun row => fst (fst row))
    (summary_internal (summarize kept item) ++ summary_outgoing (summarize kept item))) bs).
Proof.
  induction bs as [|item rest IH]; intro Hdistinct; [constructor|].
  inversion Hdistinct as [|id ids Hfresh Hrest]; subst.
  cbn [flat_map]. apply NoDup_app.
  - apply summarize_edges_nodup.
  - now apply IH.
  - intros edge Hitem Hin. apply in_flat_map in Hin as [other [Hother Hedge]].
    apply in_map_iff in Hitem as [ri [Hei Hi]].
    apply in_map_iff in Hedge as [ro [Heo Ho]].
    apply summarize_edge_owner in Hi. apply summarize_edge_owner in Ho.
    rewrite Hei in Hi. rewrite Heo in Ho.
    apply Hfresh. rewrite <- Hi, Ho. now apply in_map.
Qed.

Lemma lang_point_edges_nodup {K G} (p : func positive K G) :
  NoDup (lang_point_edges (lang_prepare p)).
Proof.
  change (NoDup (map (fun row => fst (fst row))
    (flat_map (fun summary => summary_internal summary ++ summary_outgoing summary)
      (map (summarize (first_table PosKeyCode.encode
        (map (fun item => (fst item, params _ _ _ (snd item)))
          (first_blocks (blocks _ _ _ p))))) (first_blocks (blocks _ _ _ p)))))).
  rewrite flat_map_after_map, present_map_flat_map.
  apply summaries_edges_nodup. rewrite first_blocks_selected. apply selected_blocks_nodup.
Qed.

Definition present_weight {A} (weight : A -> nat) (xs : list A) : nat :=
  fold_right (fun x n => weight x + n) 0 xs.

Lemma present_weight_map {A B} (weight : B -> nat) (f : A -> B) xs :
  present_weight weight (map f xs) = present_weight (fun x => weight (f x)) xs.
Proof.
  induction xs as [|x rest IH]; [reflexivity|].
  change (weight (f x) + present_weight weight (map f rest) =
    weight (f x) + present_weight (fun x => weight (f x)) rest). now rewrite IH.
Qed.

Lemma present_weight_app {A} (weight : A -> nat) xs ys :
  present_weight weight (xs ++ ys) = present_weight weight xs + present_weight weight ys.
Proof.
  induction xs as [|x rest IH]; [reflexivity|].
  change (weight x + present_weight weight (rest ++ ys) =
    (weight x + present_weight weight rest) + present_weight weight ys). rewrite IH; lia.
Qed.

Lemma present_weight_flat_map {A B} (weight : B -> nat) (f : A -> list B) xs :
  present_weight weight (flat_map f xs) = present_weight (fun x => present_weight weight (f x)) xs.
Proof.
  induction xs as [|x rest IH]; [reflexivity|].
  change (present_weight weight (f x ++ flat_map f rest) =
    present_weight weight (f x) + present_weight (fun x => present_weight weight (f x)) rest).
  now rewrite present_weight_app, IH.
Qed.

Lemma present_weight_plus {A} (f g : A -> nat) xs :
  present_weight (fun x => f x + g x) xs = present_weight f xs + present_weight g xs.
Proof.
  induction xs as [|x rest IH]; [reflexivity|].
  change ((f x + g x) + present_weight (fun x => f x + g x) rest =
    (f x + present_weight f rest) + (g x + present_weight g rest)). rewrite IH; lia.
Qed.

Lemma present_weight_mono {A} (f g : A -> nat) xs :
  (forall x, In x xs -> f x <= g x) -> present_weight f xs <= present_weight g xs.
Proof.
  induction xs as [|x rest IH]; intro Hle; [reflexivity|].
  change (f x + present_weight f rest <= g x + present_weight g rest). assert (Hx := Hle x (or_introl eq_refl)).
  specialize (IH (fun y Hin => Hle y (or_intror Hin))). lia.
Qed.

Lemma present_flat_length {A B} (f : A -> list B) xs :
  length (flat_map f xs) = present_weight (fun x => length (f x)) xs.
Proof.
  induction xs as [|x rest IH]; [reflexivity|].
  change (length (f x ++ flat_map f rest) =
    length (f x) + present_weight (fun x => length (f x)) rest).
  now rewrite length_app, IH.
Qed.

Lemma selected_blocks_weight {K G} (weight : positive * block positive K G -> nat) bs seen :
  present_weight weight (selected_blocks seen bs) <= present_weight weight bs.
Proof.
  revert seen. induction bs as [|item rest IH]; intro seen; [reflexivity|].
  cbn [selected_blocks]. destruct (trie_get (fst item) seen) as [[]|].
  - change (present_weight weight (selected_blocks seen rest) <= weight item + present_weight weight rest).
    specialize (IH seen); lia.
  - change (weight item + present_weight weight (selected_blocks (PTrieCode.set (fst item) tt seen) rest) <=
      weight item + present_weight weight rest).
    specialize (IH (PTrieCode.set (fst item) tt seen)); lia.
Qed.

Lemma code_rows_length {K} b i (cs : list (positive * K * list positive)) :
  length (fst (code_rows b i cs)) = length cs.
Proof.
  revert i; induction cs as [|[[x op] ys] rest IH]; intro i;
    cbn [code_rows fst length]; [reflexivity|now rewrite IH].
Qed.

Definition present_row_vars (row : point_row) := length (snd (fst row)) + length (snd row).

Lemma code_rows_var_count {K} b i (cs : list (positive * K * list positive)) :
  present_weight present_row_vars (fst (code_rows b i cs)) =
    length (flat_map (fun '(x, _, ys) => x :: ys) cs).
Proof.
  revert i; induction cs as [|[[x op] ys] rest IH]; intro i; [reflexivity|].
  change (length ys + 1 + present_weight present_row_vars (fst (code_rows b (N.succ i) rest)) =
    length ((x :: ys) ++ flat_map (fun '(x, _, ys) => x :: ys) rest)).
  rewrite IH, length_app; cbn [length]; lia.
Qed.

Lemma summarize_points_length {A K G} (kept : ptrie A)
    (item : positive * block positive K G) :
  length (summary_points (summarize kept item)) = length (code _ _ _ (snd item)) + 2.
Proof.
  change (S (S (length (map (fun row => point_dst (fst (fst row)))
    (fst (code_rows (fst item) 1%N (code _ _ _ (snd item))))))) =
      length (code _ _ _ (snd item)) + 2).
  rewrite length_map, code_rows_length. lia.
Qed.

Lemma summarize_edges_length {A K G} (kept : ptrie A)
    (item : positive * block positive K G) :
  length (summary_internal (summarize kept item) ++ summary_outgoing (summarize kept item)) <=
    length (code _ _ _ (snd item)) + 3.
Proof.
  rewrite length_app.
  change (S (length (fst (code_rows (fst item) 1%N (code _ _ _ (snd item))))) +
    length (map (fun ea =>
      (PointEdge (summary_exit (summarize kept item)) (edge_target (fst ea), 0%N)
        (Some (fst ea)), guard_uses (term _ _ _ (snd item)) ++ snd ea, ([] : list positive)))
      (listed_edge_args kept (fst item) (term _ _ _ (snd item)))) <=
    length (code _ _ _ (snd item)) + 3).
  rewrite length_map, code_rows_length.
  assert (Hlength : length (listed_edge_args kept (fst item) (term _ _ _ (snd item))) <= 2).
  { unfold listed_edge_args. eapply Nat.le_trans; [apply filter_length_le|].
    destruct (term _ _ _ (snd item)); cbn [exit_edge_args length]; lia. }
  lia.
Qed.

Lemma present_exit_vars_count {A G} (kept : ptrie A) b last (e : exit positive G) :
  present_weight present_row_vars
    (map (fun ea => (PointEdge last (edge_target (fst ea), 0%N) (Some (fst ea)),
      guard_uses e ++ snd ea, ([] : list positive))) (listed_edge_args kept b e)) +
    length (exit_returns e) <= 2 * length (exit_uses e).
Proof.
  destruct e; cbn [listed_edge_args exit_edge_args filter edge_target fst snd
    map present_weight fold_right present_row_vars guard_uses exit_returns exit_uses];
    repeat match goal with |- context [if ?flag then _ else _] => destruct flag end;
    cbn [map present_weight fold_right present_row_vars fst snd length];
    unfold present_row_vars; cbn [fst snd length app]; repeat rewrite length_app; lia.
Qed.

Definition present_body_vars {K G} (body : block positive K G) : list positive :=
  params _ _ _ body ++ flat_map (fun '(x, _, ys) => x :: ys) (code _ _ _ body) ++
    exit_uses (term _ _ _ body).

Lemma summarize_vars_count {A K G} (kept : ptrie A)
    (item : positive * block positive K G) :
  present_weight present_row_vars
    (summary_internal (summarize kept item) ++ summary_outgoing (summarize kept item)) +
    length (summary_returns (summarize kept item)) <= 2 * length (present_body_vars (snd item)).
Proof.
  rewrite present_weight_app.
  pose proof (present_exit_vars_count kept (fst item)
    (summary_exit (summarize kept item)) (term _ _ _ (snd item))) as Hexit.
  change (length (params _ _ _ (snd item)) +
    present_weight present_row_vars (fst (code_rows (fst item) 1%N (code _ _ _ (snd item)))) +
    present_weight present_row_vars (summary_outgoing (summarize kept item)) +
    length (exit_returns (term _ _ _ (snd item))) <= 2 * length (present_body_vars (snd item))).
  rewrite code_rows_var_count. unfold present_body_vars. rewrite !length_app.
  change (present_weight present_row_vars (summary_outgoing (summarize kept item)) +
    length (exit_returns (term _ _ _ (snd item))) <= 2 * length (exit_uses (term _ _ _ (snd item)))) in Hexit.
  lia.
Qed.

Lemma present_weight_scale {A} (f : A -> nat) factor xs :
  present_weight (fun x => factor * f x) xs = factor * present_weight f xs.
Proof.
  induction xs as [|x rest IH]; [cbn [present_weight fold_right]; lia|].
  change (factor * f x + present_weight (fun x => factor * f x) rest =
    factor * (f x + present_weight f rest)). rewrite IH; lia.
Qed.

Lemma present_reader_length {A B} (key : A -> positive) (xs : list A) (rows : ptrie (list B)) :
  length (flat_map (fun x => index_row rows (key x)) xs) =
    present_row_count (map key xs) rows.
Proof.
  induction xs as [|x rest IH]; [reflexivity|].
  cbn [flat_map map present_row_count fold_right]. rewrite length_app, IH. reflexivity.
Qed.

Lemma present_pair_reader_length {A B} (key : A -> positive) (xs : list A)
    (rows rows' : ptrie (list B)) :
  length (flat_map (fun x => index_row rows (key x) ++ index_row rows' (key x)) xs) =
    present_row_count (map key xs) rows + present_row_count (map key xs) rows'.
Proof.
  induction xs as [|x rest IH]; [reflexivity|].
  cbn [flat_map map present_row_count fold_right]. rewrite !length_app, IH. unfold present_row_count; lia.
Qed.

Lemma summaries_vars_count {A K G} (kept : ptrie A)
    (bs : list (positive * block positive K G)) :
  present_weight present_row_vars
    (flat_map (fun s => summary_internal s ++ summary_outgoing s) (map (summarize kept) bs)) +
  present_weight (fun s => length (summary_returns s)) (map (summarize kept) bs) <=
    2 * length (flat_map (fun item => present_body_vars (snd item)) bs).
Proof.
  rewrite present_weight_flat_map, !present_weight_map, <- present_weight_plus,
    present_flat_length, <- present_weight_scale.
  apply present_weight_mono. intros item Hin. apply summarize_vars_count.
Qed.

Lemma lang_occurrences_length {K G} (p : func positive K G) :
  length (flat_map (fun e =>
    index_row (edge_uses (lang_vars (lang_prepare p))) (PointEdge.encode e) ++
    index_row (edge_defs (lang_vars (lang_prepare p))) (PointEdge.encode e))
      (lang_point_edges (lang_prepare p)) ++
    flat_map (fun n => index_row (node_exits (lang_vars (lang_prepare p))) (PointKey.encode n))
      (lang_points (lang_prepare p))) <= 2 * length (function_vars p).
Proof.
  set (bs := first_blocks (blocks _ _ _ p)).
  set (kept := first_table PosKeyCode.encode
    (map (fun item => (fst item, params _ _ _ (snd item))) bs)).
  set (ss := map (summarize kept) bs).
  set (rows := flat_map (fun s => summary_internal s ++ summary_outgoing s) ss).
  set (es := map (fun row => fst (fst row)) rows).
  set (ns := flat_map summary_points ss).
  assert (Hedges : NoDup (map PointEdge.encode es)).
  { apply present_map_injective_nodup; [apply PointEdge.encode_inj|].
    apply (lang_point_edges_nodup p). }
  assert (Hnodes : NoDup (map PointKey.encode ns)).
  { apply present_map_injective_nodup; [apply PointKey.encode_inj|].
    unfold ns, ss. rewrite flat_map_after_map. apply summaries_points_nodup.
    unfold bs; rewrite first_blocks_selected. apply selected_blocks_nodup. }
  pose proof (present_first_table_count PointEdge.encode (map PointEdge.encode es)
    (map (fun row => (fst (fst row), snd (fst row))) rows) Hedges) as Huses.
  pose proof (present_first_table_count PointEdge.encode (map PointEdge.encode es)
    (map (fun row => (fst (fst row), snd row)) rows) Hedges) as Hdefs.
  pose proof (present_first_table_count PointKey.encode (map PointKey.encode ns)
    (map (fun s => (summary_exit s, summary_returns s)) ss) Hnodes) as Hexits.
  change (present_row_count (map PointEdge.encode es)
    (first_table PointEdge.encode (map (fun row => (fst (fst row), snd (fst row))) rows)) <=
    present_weight (fun row => length (snd row))
      (map (fun row => (fst (fst row), snd (fst row))) rows)) in Huses.
  change (present_row_count (map PointEdge.encode es)
    (first_table PointEdge.encode (map (fun row => (fst (fst row), snd row)) rows)) <=
    present_weight (fun row => length (snd row))
      (map (fun row => (fst (fst row), snd row)) rows)) in Hdefs.
  change (present_row_count (map PointKey.encode ns)
    (first_table PointKey.encode (map (fun s => (summary_exit s, summary_returns s)) ss)) <=
    present_weight (fun row => length (snd row))
      (map (fun s => (summary_exit s, summary_returns s)) ss)) in Hexits.
  rewrite present_weight_map in Huses. rewrite present_weight_map in Hdefs.
  rewrite present_weight_map in Hexits. cbn [snd] in Huses, Hdefs, Hexits.
  pose proof (summaries_vars_count kept bs) as Hstored.
  change (present_weight present_row_vars rows +
    present_weight (fun s => length (summary_returns s)) ss <=
    2 * length (flat_map (fun item => present_body_vars (snd item)) bs)) in Hstored.
  unfold present_row_vars in Hstored. rewrite present_weight_plus in Hstored.
  assert (Hsource : length (flat_map (fun item => present_body_vars (snd item)) bs) <=
    length (function_vars p)).
  { unfold bs, function_vars. rewrite length_app, !present_flat_length,
      first_blocks_selected.
    pose proof (selected_blocks_weight (fun item => length (present_body_vars (snd item)))
      (blocks _ _ _ p) Empty) as Hselected.
    change (present_weight (fun item => length (present_body_vars (snd item)))
      (selected_blocks Empty (blocks _ _ _ p)) <= length (inputs _ _ _ p) +
      present_weight (fun item => length (present_body_vars (snd item))) (blocks _ _ _ p)). lia. }
  rewrite length_app, present_pair_reader_length, present_reader_length.
  change (present_row_count (map PointEdge.encode es)
    (first_table PointEdge.encode (map (fun row => (fst (fst row), snd (fst row))) rows)) +
    present_row_count (map PointEdge.encode es)
    (first_table PointEdge.encode (map (fun row => (fst (fst row), snd row)) rows)) +
    present_row_count (map PointKey.encode ns)
    (first_table PointKey.encode (map (fun s => (summary_exit s, summary_returns s)) ss)) <=
    2 * length (function_vars p)).
  eapply Nat.le_trans.
  - apply Nat.add_le_mono; [apply Nat.add_le_mono; [exact Huses|exact Hdefs]|exact Hexits].
  - eapply Nat.le_trans; [exact Hstored|]. lia.
Qed.

Lemma summaries_structure_count {A K G} (kept : ptrie A)
    (bs : list (positive * block positive K G)) :
  length (flat_map summary_points (map (summarize kept) bs)) +
  length (flat_map (fun s => summary_internal s ++ summary_outgoing s) (map (summarize kept) bs)) <=
    5 * (length bs + present_weight (fun item => length (code _ _ _ (snd item))) bs).
Proof.
  induction bs as [|item rest IH]; [reflexivity|].
  cbn [map flat_map length present_weight fold_right]. rewrite !length_app.
  rewrite summarize_points_length.
  pose proof (summarize_edges_length kept item) as Hedges. rewrite length_app in Hedges. unfold present_weight in IH; lia.
Qed.

Lemma lang_structure_length {K G} (p : func positive K G) :
  length (lang_points (lang_prepare p)) + length (lang_point_edges (lang_prepare p)) <=
    5 * function_size p.
Proof.
  set (bs := first_blocks (blocks _ _ _ p)).
  set (kept := first_table PosKeyCode.encode
    (map (fun item => (fst item, params _ _ _ (snd item))) bs)).
  change (length (flat_map summary_points (map (summarize kept) bs)) +
    length (map (fun row => fst (fst row))
      (flat_map (fun s => summary_internal s ++ summary_outgoing s) (map (summarize kept) bs))) <=
    5 * function_size p).
  rewrite length_map. pose proof (summaries_structure_count kept bs) as Hcount.
  assert (Hblocks : length bs <= length (blocks _ _ _ p)).
  { unfold bs; rewrite first_blocks_selected; apply selected_blocks_length. }
  assert (Hcode : present_weight (fun item => length (code _ _ _ (snd item))) bs <=
    present_weight (fun item => length (code _ _ _ (snd item))) (blocks _ _ _ p)).
  { unfold bs; rewrite first_blocks_selected; apply selected_blocks_weight. }
  eapply Nat.le_trans; [exact Hcount|]. apply Nat.mul_le_mono_l.
  clear Hcount. unfold function_size, present_weight in *. lia.
Qed.


Lemma present_row_count_map {A B} (key : A -> positive) xs (rows : ptrie (list B)) :
  present_row_count (map key xs) rows =
    present_weight (fun x => length (index_row rows (key x))) xs.
Proof.
  rewrite <- (present_reader_length key xs rows). apply present_flat_length.
Qed.
Lemma listed_edge_args_nodup {A G} (kept : ptrie A) b (e : exit positive G) :
  NoDup (map fst (listed_edge_args kept b e)).
Proof.
  destruct e; cbn [listed_edge_args exit_edge_args filter edge_target fst map];
    repeat match goal with |- context [if ?flag then _ else _] => destruct flag end;
    repeat constructor; cbn; intuition discriminate.
Qed.

Lemma listed_edge_args_source {A G} (kept : ptrie A) b (e : exit positive G) row :
  In row (listed_edge_args kept b e) -> edge_source (fst row) = b.
Proof.
  intro Hin. apply filter_In in Hin as [Hin _].
  destruct row as [be args]. now apply exit_edge_args_shape in Hin as [Hin _].
Qed.

Lemma block_rows_nodup {A K G} (kept : ptrie A)
    (bs : list (positive * block positive K G)) : NoDup (map fst bs) ->
  NoDup (map fst (flat_map (fun item =>
    listed_edge_args kept (fst item) (term _ _ _ (snd item))) bs)).
Proof.
  induction bs as [|item rest IH]; intro Hdistinct; [constructor|].
  inversion Hdistinct as [|id ids Hfresh Hrest]; subst.
  cbn [flat_map]. rewrite map_app. apply NoDup_app.
  - apply listed_edge_args_nodup.
  - now apply IH.
  - intros edge Hitem Hin. apply in_map_iff in Hitem as [ri [Hei Hi]].
    apply in_map_iff in Hin as [ro [Heo Ho]].
    apply in_flat_map in Ho as [other [Hother Ho]].
    apply listed_edge_args_source in Hi. apply listed_edge_args_source in Ho.
    rewrite Hei in Hi. rewrite Heo in Ho.
    apply Hfresh. rewrite <- Hi, Ho. now apply in_map.
Qed.

Lemma lang_block_edges_nodup {K G} (p : func positive K G) :
  NoDup (lang_edges (lang_prepare p)).
Proof.
  change (NoDup (map fst (flat_map (fun item =>
    listed_edge_args (first_table PosKeyCode.encode
      (map (fun item => (fst item, params _ _ _ (snd item)))
        (first_blocks (blocks _ _ _ p)))) (fst item) (term _ _ _ (snd item)))
    (first_blocks (blocks _ _ _ p))))).
  apply block_rows_nodup. rewrite first_blocks_selected; apply selected_blocks_nodup.
Qed.

Lemma listed_edge_args_length {A G} (kept : ptrie A) b (e : exit positive G) :
  present_weight (fun row => length (snd row)) (listed_edge_args kept b e) <=
    length (exit_uses e).
Proof.
  destruct e; cbn [listed_edge_args exit_edge_args filter edge_target fst];
    repeat match goal with |- context [if ?flag then _ else _] => destruct flag end;
    unfold present_weight; cbn [fold_right snd exit_uses length];
    repeat rewrite length_app; lia.
Qed.

Lemma lang_block_rows_length {K G} (p : func positive K G) :
  present_row_count (map PosKeyCode.encode (lang_blocks (lang_prepare p)))
    (point_params (lang_point_tables (lang_prepare p))) +
  present_row_count (map BlockEdge.encode (lang_edges (lang_prepare p)))
    (point_args (lang_point_tables (lang_prepare p))) <= function_size p.
Proof.
  set (bs := first_blocks (blocks _ _ _ p)).
  set (kept := first_table PosKeyCode.encode
    (map (fun item => (fst item, params _ _ _ (snd item))) bs)).
  set (rows := flat_map (fun item => listed_edge_args kept (fst item)
    (term _ _ _ (snd item))) bs).
  assert (Hblocks : NoDup (map PosKeyCode.encode (map fst bs))).
  { apply present_map_injective_nodup; [intros x y H; exact H|].
    unfold bs; rewrite first_blocks_selected; apply selected_blocks_nodup. }
  assert (Hedges : NoDup (map BlockEdge.encode (map fst rows))).
  { apply present_map_injective_nodup; [apply BlockEdge.encode_inj|].
    apply (lang_block_edges_nodup p). }
  pose proof (present_first_table_count PosKeyCode.encode (map PosKeyCode.encode (map fst bs))
    (map (fun item => (fst item, params _ _ _ (snd item))) bs) Hblocks) as Hparams.
  pose proof (present_first_table_count BlockEdge.encode (map BlockEdge.encode (map fst rows))
    rows Hedges) as Hargs.
  change (present_row_count (map PosKeyCode.encode (map fst bs)) kept <=
    present_weight (fun row => length (snd row))
      (map (fun item => (fst item, params _ _ _ (snd item))) bs)) in Hparams.
  rewrite present_weight_map in Hparams; cbn [snd] in Hparams.
  change (present_row_count (map BlockEdge.encode (map fst rows)) (first_table BlockEdge.encode rows) <=
    present_weight (fun row => length (snd row)) rows) in Hargs.
  assert (Hsource : present_weight (fun item => length (params _ _ _ (snd item))) bs +
    present_weight (fun row => length (snd row)) rows <=
    length (flat_map (fun item => present_body_vars (snd item)) bs)).
  { unfold rows. rewrite present_weight_flat_map, <- present_weight_plus, present_flat_length.
    apply present_weight_mono. intros item Hin.
    pose proof (listed_edge_args_length kept (fst item) (term _ _ _ (snd item))) as Hexit.
    unfold present_body_vars; rewrite !length_app; lia. }
  assert (Hkept : length (flat_map (fun item => present_body_vars (snd item)) bs) <=
    function_size p).
  { unfold bs, function_size, function_vars. rewrite length_app, !present_flat_length,
      first_blocks_selected.
    pose proof (selected_blocks_weight (fun item => length (present_body_vars (snd item)))
      (blocks _ _ _ p) Empty) as Hselected.
    unfold present_body_vars in Hselected. unfold present_body_vars; lia. }
  change (present_row_count (map PosKeyCode.encode (map fst bs)) kept +
    present_row_count (map BlockEdge.encode (map fst rows)) (first_table BlockEdge.encode rows) <=
    function_size p).
  eapply Nat.le_trans; [apply Nat.add_le_mono; [exact Hparams|exact Hargs]|].
  eapply Nat.le_trans; [exact Hsource|exact Hkept].
Qed.


Lemma present_first_table_get {A B} (key : A -> positive) (rows : list (A * B)) k value :
  trie_get k (first_table key rows) = Some value ->
    exists a, In (a, value) rows /\ key a = k.
Proof.
  induction rows as [|[a v] rest IH]; intro Hget.
  - change (trie_get k Empty = Some value) in Hget. rewrite PTrie.get_empty in Hget; discriminate.
  - change (trie_get k (PTrieCode.set (key a) v (first_table key rest)) = Some value) in Hget.
    destruct (Pos.eq_dec k (key a)) as [Heq|Hneq].
    + subst k. rewrite PTrie.get_set_same in Hget. inversion Hget; subst v.
      exists a; split; [now left|reflexivity].
    + rewrite PTrie.get_set_other in Hget by exact Hneq.
      destruct (IH Hget) as [other [Hin Hkey]]. exists other; split; [now right|exact Hkey].
Qed.

Lemma present_first_table_in {A B} (key : A -> positive) (rows : list (A * list B)) k x :
  In x (index_row (first_table key rows) k) ->
    exists a values, In (a, values) rows /\ In x values.
Proof.
  unfold index_row. destruct (trie_get k (first_table key rows)) as [values|] eqn:Hget;
    intro Hin; [|contradiction].
  destruct (present_first_table_get _ _ _ _ Hget) as [a [Hrow Hkey]].
  exists a, values; auto.
Qed.

Lemma code_rows_vars_in {K} b i (cs : list (positive * K * list positive)) row x :
  In row (fst (code_rows b i cs)) -> In x (snd (fst row) ++ snd row) ->
    In x (flat_map (fun '(x, _, ys) => x :: ys) cs).
Proof.
  revert i; induction cs as [|[[y op] ys] rest IH]; intros i Hrow Hx; [contradiction|].
  cbn [code_rows fst] in Hrow. destruct Hrow as [Heq|Hrow].
  - subst row. cbn [fst snd] in Hx. apply in_app_or in Hx as [Hys|Hy].
    + change (In x ((y :: ys) ++ flat_map (fun '(x, _, ys) => x :: ys) rest)).
      apply in_or_app; left; now right.
    + cbn in Hy. destruct Hy as [Heq|Hfalse]; [subst x|contradiction]. now left.
  - change (In x ((y :: ys) ++ flat_map (fun '(x, _, ys) => x :: ys) rest)).
    apply in_or_app; right. now apply (IH (N.succ i)).
Qed.

Lemma exit_edge_args_vars {G} b (e : exit positive G) be args x :
  In (be, args) (exit_edge_args b e) ->
  In x (guard_uses e ++ args) -> In x (exit_uses e).
Proof.
  destruct e as [target ys|guard xs yes yes_args no no_args|returns].
  - cbn [exit_edge_args]. intros [Heq|Hfalse] Hx; [|contradiction].
    inversion Heq; subst. cbn [guard_uses app] in Hx. exact Hx.
  - cbn [exit_edge_args]. intros [Heq|[Heq|Hfalse]] Hx; try contradiction;
      inversion Heq; subst; cbn [guard_uses] in Hx; cbn [exit_uses].
    + apply in_app_or in Hx as [Hg|Ha].
      * apply in_or_app; left; exact Hg.
      * apply in_or_app; right; apply in_or_app; left; exact Ha.
    + apply in_app_or in Hx as [Hg|Ha].
      * apply in_or_app; left; exact Hg.
      * apply in_or_app; right; apply in_or_app; right; exact Ha.
  - cbn [exit_edge_args]; contradiction.

Qed.

Lemma summary_vars_in {A K G} (kept : ptrie A)
    (item : positive * block positive K G) row x :
  In row (summary_internal (summarize kept item) ++ summary_outgoing (summarize kept item)) ->
  In x (snd (fst row) ++ snd row) -> In x (present_body_vars (snd item)).
Proof.
  intros Hrow Hx. apply in_app_or in Hrow as [Hi|Ho].
  - change (In row ((PointEdge (fst item, 0%N) (fst item, 1%N) None,
      [], params _ _ _ (snd item)) :: fst (code_rows (fst item) 1%N (code _ _ _ (snd item))))) in Hi.
    destruct Hi as [Heq|Hi].
    + subst row. cbn [fst snd app] in Hx. unfold present_body_vars.
      apply in_or_app; left; exact Hx.
    + pose proof (code_rows_vars_in _ _ _ _ x Hi Hx) as Hvars. unfold present_body_vars.
      apply in_or_app; right; apply in_or_app; left; exact Hvars.
  - change (In row (map (fun ea =>
      (PointEdge (summary_exit (summarize kept item)) (edge_target (fst ea), 0%N)
        (Some (fst ea)), guard_uses (term _ _ _ (snd item)) ++ snd ea, ([] : list positive)))
      (listed_edge_args kept (fst item) (term _ _ _ (snd item))))) in Ho.
    apply in_map_iff in Ho as [[be args] [Heq Hin]]. subst row.
    cbn [fst snd] in Hx; rewrite app_nil_r in Hx.
    apply filter_In in Hin as [Hin _].
    pose proof (exit_edge_args_vars _ _ _ _ _ Hin Hx) as Hexit.
    unfold present_body_vars. apply in_or_app; right; apply in_or_app; right; exact Hexit.
Qed.

Lemma summary_returns_in {A K G} (kept : ptrie A)
    (item : positive * block positive K G) x :
  In x (summary_returns (summarize kept item)) -> In x (present_body_vars (snd item)).
Proof.
  change (In x (exit_returns (term _ _ _ (snd item))) -> In x (present_body_vars (snd item))).
  intro Hin. unfold present_body_vars. apply in_or_app; right; apply in_or_app; right.
  destruct (term _ _ _ (snd item)); cbn [exit_returns exit_uses] in *;
    first [contradiction|exact Hin].
Qed.

Lemma kept_body_vars_in_function {K G} (p : func positive K G) item x :
  In item (first_blocks (blocks _ _ _ p)) -> In x (present_body_vars (snd item)) ->
    In x (function_vars p).
Proof.
  intros Hitem Hx. rewrite first_blocks_selected in Hitem.
  apply selected_blocks_in in Hitem as [Hitem _].
  unfold function_vars. apply in_or_app; right. apply in_flat_map.
  exists item; split; [exact Hitem|exact Hx].
Qed.

Lemma lang_occurrences_vars {K G} (p : func positive K G) x :
  In x (flat_map (fun e =>
    index_row (edge_uses (lang_vars (lang_prepare p))) (PointEdge.encode e) ++
    index_row (edge_defs (lang_vars (lang_prepare p))) (PointEdge.encode e))
      (lang_point_edges (lang_prepare p)) ++
    flat_map (fun n => index_row (node_exits (lang_vars (lang_prepare p))) (PointKey.encode n))
      (lang_points (lang_prepare p))) -> In x (function_vars p).
Proof.
  set (bs := first_blocks (blocks _ _ _ p)).
  set (kept := first_table PosKeyCode.encode
    (map (fun item => (fst item, params _ _ _ (snd item))) bs)).
  set (ss := map (summarize kept) bs).
  set (rows := flat_map (fun s => summary_internal s ++ summary_outgoing s) ss).
  assert (Hrow : forall row, In row rows ->
    In x (snd (fst row) ++ snd row) -> In x (function_vars p)).
  { intros row Hin Hx. unfold rows in Hin. apply in_flat_map in Hin as [s [Hs Hin]].
    unfold ss in Hs. apply in_map_iff in Hs as [item [Heq Hitem]]. subst s.
    eapply kept_body_vars_in_function; [exact Hitem|]. now apply (summary_vars_in kept item row). }
  assert (Hret : forall s, In s ss -> In x (summary_returns s) -> In x (function_vars p)).
  { intros s Hs Hx. unfold ss in Hs. apply in_map_iff in Hs as [item [Heq Hitem]]. subst s.
    eapply kept_body_vars_in_function; [exact Hitem|]. now apply (summary_returns_in kept item). }
  intro Hin. apply in_app_or in Hin as [Hedge|Hnode].
  - apply in_flat_map in Hedge as [e [He Hx]]. apply in_app_or in Hx as [Hu|Hd].
    + change (In x (index_row (first_table PointEdge.encode
        (map (fun row => (fst (fst row), snd (fst row))) rows)) (PointEdge.encode e))) in Hu.
      apply present_first_table_in in Hu as [key [values [Hstored Hx]]].
      apply in_map_iff in Hstored as [row [Heq Hin]]. inversion Heq; subst values.
      apply (Hrow row Hin). apply in_or_app; left; exact Hx.
    + change (In x (index_row (first_table PointEdge.encode
        (map (fun row => (fst (fst row), snd row)) rows)) (PointEdge.encode e))) in Hd.
      apply present_first_table_in in Hd as [key [values [Hstored Hx]]].
      apply in_map_iff in Hstored as [row [Heq Hin]]. inversion Heq; subst values.
      apply (Hrow row Hin). apply in_or_app; right; exact Hx.
  - apply in_flat_map in Hnode as [n [Hn Hx]].
    change (In x (index_row (first_table PointKey.encode
      (map (fun s => (summary_exit s, summary_returns s)) ss)) (PointKey.encode n))) in Hx.
    apply present_first_table_in in Hx as [key [values [Hstored Hx]]].
    apply in_map_iff in Hstored as [s [Heq Hin]]. inversion Heq; subst values.
    now apply (Hret s Hin).
Qed.

Lemma present_max_bound {A} (weight : A -> nat) xs bound :
  (forall x, In x xs -> weight x <= bound) ->
  fold_right Nat.max 0 (map weight xs) <= bound.
Proof.
  induction xs as [|x rest IH]; intro Hbound; [cbn; lia|].
  cbn [map fold_right]. apply Nat.max_lub; [apply Hbound; now left|].
  apply IH. intros y Hin. apply Hbound; now right.
Qed.


(** A unique encoded-key row is returned by the first-row table. *)
Lemma present_table_lookup_unique {A B} (key : A -> positive) rows a (value : B) :
  NoDup (map (fun row => key (fst row)) rows) -> In (a, value) rows ->
  trie_get (key a) (first_table key rows) = Some value.
Proof.
  induction rows as [|[head stored] rest IH]; intros Hunique Hin; [contradiction|].
  inversion Hunique as [|encoded encoded_rest Hfresh Hrest]; subst.
  change (trie_get (key a) (PTrieCode.set (key head) stored (first_table key rest)) = Some value).
  destruct Hin as [Heq|Hin].
  - inversion Heq; subst head stored. apply PTrie.get_set_same.
  - rewrite PTrie.get_set_other.
    + now apply IH.
    + intro Heq. apply Hfresh. apply in_map_iff.
      exists (a, value); split; [exact Heq|exact Hin].
Qed.

(** A block-item table agrees with first source lookup even before deduplication. *)
Lemma present_block_table_lookup {K G A} (f : positive * block positive K G -> A) bs b :
  trie_get b (first_table PosKeyCode.encode (map (fun item => (fst item, f item)) bs)) =
    option_map (fun body => f (b, body)) (find_block b bs).
Proof.
  induction bs as [|[a body] rest IH].
  - change (trie_get b (@Empty A) = None). apply PTrie.get_empty.
  - change (trie_get b (PTrieCode.set a (f (a, body))
      (first_table PosKeyCode.encode (map (fun item => (fst item, f item)) rest))) =
      option_map (fun body => f (b, body))
        (if Pos.eqb b a then Some body else find_block b rest)).
    destruct (Pos.eqb b a) eqn:Hsame.
    + apply Pos.eqb_eq in Hsame; subst a. rewrite PTrie.get_set_same; reflexivity.
    + rewrite PTrie.get_set_other by now apply Pos.eqb_neq. exact IH.
Qed.

(** Every block reader can use the original selected item, not just its identifier. *)
Lemma present_block_table_item {K G A} (f : positive * block positive K G -> A) bs b body :
  NoDup (map fst bs) -> In (b, body) bs ->
  trie_get b (first_table PosKeyCode.encode (map (fun item => (fst item, f item)) bs)) =
    Some (f (b, body)).
Proof.
  intros Hunique Hin.
  change (trie_get (PosKeyCode.encode b)
    (first_table PosKeyCode.encode (map (fun item => (fst item, f item)) bs)) = Some (f (b, body))).
  apply present_table_lookup_unique.
  - rewrite map_map. exact Hunique.
  - apply in_map_iff. exists (b, body); split; [reflexivity|exact Hin].
Qed.

(** A multitable is exactly the original list filtered by its encoded key. *)
Lemma present_multi_table_filter {A} (key : A -> positive) rows x :
  index_row (multi_table key rows) x = filter (fun row => Pos.eqb (key row) x) rows.
Proof.
  induction rows as [|a rest IH].
  - unfold multi_table, index_row; cbn [fold_right filter].
    rewrite PTrie.get_empty; reflexivity.
  - change (index_row
      (PTrieCode.set (key a) (a :: index_row (multi_table key rest) (key a))
        (multi_table key rest)) x =
      if Pos.eqb (key a) x then a :: filter (fun row => Pos.eqb (key row) x) rest
      else filter (fun row => Pos.eqb (key row) x) rest).
    destruct (Pos.eqb (key a) x) eqn:Hsame.
    + apply Pos.eqb_eq in Hsame; subst x. unfold index_row at 1.
      rewrite PTrie.get_set_same. cbn. now rewrite IH.
    + apply Pos.eqb_neq in Hsame. unfold index_row at 1.
      rewrite PTrie.get_set_other by congruence. exact IH.
Qed.

Lemma present_multi_table_nodup {A} (key : A -> positive) rows x :
  NoDup rows -> NoDup (index_row (multi_table key rows) x).
Proof.
  intro Hunique; rewrite present_multi_table_filter; now apply NoDup_filter.
Qed.
(** Code rows form the chain of consecutive instruction positions. *)
Lemma present_code_chain {K} b : forall (cs : list (positive * K * list positive)) i edges,
  incl (map (fun row => fst (fst row)) (fst (code_rows b i cs))) edges ->
  presentation_chain edges point_src point_dst
    ((b, i) :: map (fun row => point_dst (fst (fst row))) (fst (code_rows b i cs)))
    (map (fun row => fst (fst row)) (fst (code_rows b i cs))).
Proof.
  induction cs as [|[[x op] xs] rest IH]; intros i edges Hin.
  - cbn [code_rows fst map]; constructor.
  - cbn [code_rows fst snd map] in Hin |- *.
    eapply Chain_next.
    + apply Hin; left; reflexivity.
    + reflexivity.
    + reflexivity.
    + apply IH. intros edge Hedge; apply Hin; right; exact Hedge.
Qed.

Lemma present_summary_chain {A K G} (kept : ptrie A)
    (item : positive * block positive K G) edges :
  incl (map (fun row => fst (fst row)) (summary_internal (summarize kept item))) edges ->
  presentation_chain edges point_src point_dst (summary_points (summarize kept item))
    (map (fun row => fst (fst row)) (summary_internal (summarize kept item))).
Proof.
  intro Hin.
  change (presentation_chain edges point_src point_dst
    ((fst item, 0%N) :: (fst item, 1%N) ::
      map (fun row => point_dst (fst (fst row)))
        (fst (code_rows (fst item) 1%N (code _ _ _ (snd item)))))
    (PointEdge (fst item, 0%N) (fst item, 1%N) None ::
      map (fun row => fst (fst row))
        (fst (code_rows (fst item) 1%N (code _ _ _ (snd item)))))).
  eapply Chain_next.
  - apply Hin; left; reflexivity.
  - reflexivity.
  - reflexivity.
  - apply present_code_chain. intros edge Hedge; apply Hin; right; exact Hedge.
Qed.

Lemma present_code_last {K} b : forall (cs : list (positive * K * list positive)) i default,
  last ((b, i) :: map (fun row => point_dst (fst (fst row))) (fst (code_rows b i cs))) default =
    (b, snd (code_rows b i cs)).
Proof.
  induction cs as [|[[x op] xs] rest IH]; intros i default.
  - reflexivity.
  - change (last ((b, N.succ i) :: map (fun row => point_dst (fst (fst row)))
      (fst (code_rows b (N.succ i) rest))) default =
      (b, snd (code_rows b (N.succ i) rest))).
    apply IH.
Qed.

Lemma present_summary_last {A K G} (kept : ptrie A)
    (item : positive * block positive K G) default :
  last (summary_points (summarize kept item)) default = summary_exit (summarize kept item).
Proof.
  change (last ((fst item, 1%N) :: map (fun row => point_dst (fst (fst row)))
    (fst (code_rows (fst item) 1%N (code _ _ _ (snd item))))) default =
    (fst item, snd (code_rows (fst item) 1%N (code _ _ _ (snd item))))).
  apply present_code_last.
Qed.

Lemma present_summary_first {A K G} (kept : ptrie A)
    (item : positive * block positive K G) :
  nth_error (summary_points (summarize kept item)) 0 = Some (fst item, 0%N).
Proof.
  reflexivity.
Qed.
Lemma present_summary_parameter {A K G} (kept : ptrie A)
    (item : positive * block positive K G) :
  nth_error (map (fun row => fst (fst row)) (summary_internal (summarize kept item))) 0 =
    Some (PointEdge (fst item, 0%N) (fst item, 1%N) None).
Proof.
  reflexivity.
Qed.
Lemma present_summary_nonempty {A K G} (kept : ptrie A)
    (item : positive * block positive K G) : summary_points (summarize kept item) <> [].
Proof.
  discriminate.
Qed.
(** A functional partial table preserves absence of a value at every matching key. *)
Lemma present_partial_table_none {A B} (key : A -> positive) (f : A -> option B)
    (Hkey : forall x y, key x = key y -> x = y) rows a :
  f a = None ->
  trie_get (key a) (first_table key (flat_map (fun x =>
    match f x with Some v => [(x, v)] | None => [] end) rows)) = None.
Proof.
  intro Hnone; induction rows as [|x rest IH].
  - apply PTrie.get_empty.
  - cbn [flat_map]. destruct (f x) as [v|] eqn:Hx; [|exact IH].
    change (trie_get (key a) (PTrieCode.set (key x) v
      (first_table key (flat_map (fun y =>
        match f y with Some z => [(y, z)] | None => [] end) rest))) = None).
    rewrite PTrie.get_set_other; [exact IH|].
    intro Heq; apply Hkey in Heq; subst x; congruence.
Qed.

(** A functional partial table returns a listed key's value without a uniqueness premise. *)
Lemma present_partial_table {A B} (key : A -> positive) (f : A -> option B)
    (Hkey : forall x y, key x = key y -> x = y) rows a :
  In a rows ->
  trie_get (key a) (first_table key (flat_map (fun x =>
    match f x with Some v => [(x, v)] | None => [] end) rows)) = f a.
Proof.
  destruct (f a) as [value|] eqn:Ha.
  - induction rows as [|x rest IH]; intro Hin; [contradiction|].
    cbn [flat_map]. destruct (f x) as [v|] eqn:Hx.
    + change (trie_get (key a) (PTrieCode.set (key x) v
        (first_table key (flat_map (fun y =>
          match f y with Some z => [(y, z)] | None => [] end) rest))) = Some value).
      destruct (Pos.eq_dec (key a) (key x)) as [Heq|Hneq].
      * apply Hkey in Heq; subst x. rewrite PTrie.get_set_same; congruence.
      * rewrite PTrie.get_set_other by exact Hneq. apply IH.
        destruct Hin as [Heq|Hin]; [subst x; contradiction|exact Hin].
    + apply IH. destruct Hin as [Heq|Hin]; [subst x; congruence|exact Hin].
  - intro Hin; now apply present_partial_table_none.
Qed.

(** Flattening pairs preserves the first projection as the flattened source list. *)
Lemma present_owner_keys {A B} (rows : list (A * list B)) :
  map fst (flat_map (fun row => map (fun x => (x, fst row)) (snd row)) rows) =
    flat_map snd rows.
Proof.
  induction rows as [|[owner xs] rest IH]; cbn [flat_map fst snd]; [reflexivity|].
  rewrite map_app, map_map, IH.
  change (map (fun x : B => x) xs ++ flat_map snd rest = xs ++ flat_map snd rest).
  now rewrite map_id.
Qed.

Lemma present_summary_owner_keys (ss : list block_summary) :
  map fst (flat_map (fun s => map (fun n => (n, summary_block s)) (summary_points s)) ss) =
    flat_map summary_points ss.
Proof.
  induction ss as [|s rest IH]; cbn [flat_map]; [reflexivity|].
  rewrite map_app, map_map, IH.
  change (map (fun n : point_key => n) (summary_points s) ++ flat_map summary_points rest =
    summary_points s ++ flat_map summary_points rest).
  now rewrite map_id.
Qed.

Lemma present_exit_shape_args {K G} (p : func positive K G) source e be args :
  exit_shape p e -> In (be, args) (exit_edge_args source e) -> edge_shape p (edge_target be) args.
Proof.
  destruct e as [target values|guard values yes yesargs no noargs|values];
    cbn [exit_shape exit_edge_args In].
  - intros Hshape [Heq|[]]. inversion Heq; subst; exact Hshape.
  - intros [Hyes Hno] [Heq|[Heq|[]]]; inversion Heq; subst; assumption.
  - intros _ [].
Qed.

(** * Preparation clock combinators *)

Lemma prep_fold_right_uniform {A B} (f : A -> B -> B) Tf xs bound :
  (forall x, In x xs -> forall acc, (Tf x acc <= bound)%N) -> forall acc,
  (List.T_fold_right f Tf acc xs <= (bound + 1) * N.of_nat (length xs) + 1)%N.
Proof.
  induction xs as [|x rest IH]; intros Hbound acc.
  - time_step.
  - pose proof (Hbound x (or_introl eq_refl) (fold_right f acc rest)) as Hhead.
    specialize (IH ltac:(intros y Hy state; apply Hbound; now right) acc). time_step.
Qed.

Lemma prep_fold_left_uniform {A B} (f : A -> B -> A) Tf xs bound :
  (forall acc x, In x xs -> (Tf acc x <= bound)%N) -> forall acc,
  (List.T_fold_left f Tf xs acc <= (bound + 1) * N.of_nat (length xs) + 1)%N.
Proof.
  induction xs as [|x rest IH]; intros Hbound acc.
  - time_step.
  - pose proof (Hbound acc x (or_introl eq_refl)) as Hhead.
    specialize (IH ltac:(intros state y Hy; apply Hbound; now right) (f acc x)). time_step.
Qed.

Lemma prep_map_uniform {A B} (f : A -> B) Tf xs bound :
  (forall x, In x xs -> (Tf x <= bound)%N) ->
  (ListDef.T_map f Tf xs <= (bound + 1) * N.of_nat (length xs) + 1)%N.
Proof.
  induction xs as [|x rest IH]; intro Hbound.
  - time_step.
  - pose proof (Hbound x (or_introl eq_refl)) as Hhead.
    specialize (IH ltac:(intros y Hy; apply Hbound; now right)). time_step.
Qed.

Lemma prep_map_weight {A B} (f : A -> B) Tf charge xs bound :
  (forall x, In x xs -> 1 <= charge x) ->
  (forall x, In x xs -> (Tf x <= bound * N.of_nat (charge x))%N) ->
  (ListDef.T_map f Tf xs <=
    (bound + 1) * N.of_nat (present_weight charge xs) + 1)%N.
Proof.
  induction xs as [|x rest IH]; intros Hpositive Hbound.
  - time_step.
  - pose proof (Hpositive x (or_introl eq_refl)) as Hcharge.
    pose proof (Hbound x (or_introl eq_refl)) as Hhead.
    specialize (IH ltac:(intros y Hy; apply Hpositive; now right)
      ltac:(intros y Hy; apply Hbound; now right)).
    time_unfold @ListDef.T_map. cbn [present_weight fold_right].
    fold (present_weight charge rest).
    rewrite Nat2N.inj_add. nia.
Qed.

Lemma prep_flat_weight {A B} (f : A -> list B) Tf charge xs bound :
  (forall x, In x xs -> 1 <= charge x) ->
  (forall x, In x xs ->
    (Tf x + N.of_nat (length (f x) + 1) <= bound * N.of_nat (charge x))%N) ->
  (Code.List.T_flat_map f Tf xs <=
    (bound + 1) * N.of_nat (present_weight charge xs) + 1)%N.
Proof.
  induction xs as [|x rest IH]; intros Hpositive Hbound.
  - time_step.
  - pose proof (Hpositive x (or_introl eq_refl)) as Hcharge.
    pose proof (Hbound x (or_introl eq_refl)) as Hhead.
    specialize (IH ltac:(intros y Hy; apply Hpositive; now right)
      ltac:(intros y Hy; apply Hbound; now right)).
    pose proof (Datatypes.T_app_le (f x) (flat_map f rest)) as Happend.
    time_unfold @Code.List.T_flat_map. cbn [present_weight fold_right].
    fold (present_weight charge rest).
    rewrite !Nat2N.inj_add in *. nia.
Qed.

Lemma prep_first_table_clock {A B} (key : A -> positive) Tkey rows bound :
  (1 <= bound)%N ->
  (forall row, In row rows -> (Tkey (fst row) <= bound)%N) ->
  (forall row, In row rows -> forall table : ptrie B,
    (PTrieCode.T_set (key (fst row)) (snd row) table <= bound)%N) ->
  (T_first_table key Tkey rows <= 8 * bound * N.of_nat (length rows + 1))%N.
Proof.
  intros Hpositive Hkey Hset. time_unfold @T_first_table.
  match goal with
  | |- context [List.T_fold_right ?step ?clock Empty rows] =>
    assert (Hfold : (List.T_fold_right step clock Empty rows <=
      (5 * bound + 1) * N.of_nat (length rows) + 1)%N)
  end.
  { apply prep_fold_right_uniform. intros row Hin table.
    pose proof (Hkey row Hin) as Hencode. pose proof (Hset row Hin table) as Hinsert.
    time_simpl. nia. }
  assert (Hslope : ((5 * bound + 1) * N.of_nat (length rows) <=
    8 * bound * N.of_nat (length rows))%N) by (apply N.mul_le_mono_r; lia).
  rewrite Nat2N.inj_add. nia.
Qed.

Lemma prep_multi_table_clock {A} (key : A -> positive) Tkey rows bound :
  (1 <= bound)%N ->
  (forall row, In row rows -> (Tkey row <= bound)%N) ->
  (forall row, In row rows -> forall table : ptrie (list A),
    (T_index_row table (key row) <= bound)%N) ->
  (forall row, In row rows -> forall table : ptrie (list A),
    (PTrieCode.T_set (key row) (row :: index_row table (key row)) table <= bound)%N) ->
  (T_multi_table key Tkey rows <= 8 * bound * N.of_nat (length rows + 1))%N.
Proof.
  intros Hpositive Hkey Hrow Hset. time_unfold @T_multi_table.
  match goal with
  | |- context [List.T_fold_right ?step ?clock Empty rows] =>
    assert (Hfold : (List.T_fold_right step clock Empty rows <=
      (5 * bound + 1) * N.of_nat (length rows) + 1)%N)
  end.
  { apply prep_fold_right_uniform. intros row Hin table.
    pose proof (Hkey row Hin) as Hencode. pose proof (Hrow row Hin table) as Hlookup.
    pose proof (Hset row Hin table) as Hinsert. time_simpl. nia. }
  assert (Hslope : ((5 * bound + 1) * N.of_nat (length rows) <=
    8 * bound * N.of_nat (length rows))%N) by (apply N.mul_le_mono_r; lia).
  rewrite Nat2N.inj_add. nia.
Qed.

Lemma prep_first_blocks_clock {K G} (bs : list (positive * block positive K G)) width :
  (forall b body, In (b, body) bs -> Pos.size_nat b <= width) ->
  (T_first_blocks bs <=
    (PTrieT.c_trie + 16) * N.of_nat (length bs + 1) * N.of_nat (width + 1))%N.
Proof.
  intro Hwidth. time_unfold @T_first_blocks; time_simpl.
  lazymatch goal with
  | |- context [List.T_fold_left ?f ?Tf bs (Empty, [])] =>
    pose proof (prep_fold_left_uniform f Tf bs
      ((PTrieT.c_trie + 12) * N.of_nat (width + 1))%N
      ltac:(intros [seen kept] [b body] Hin;
        pose proof (Hwidth b body Hin) as Hb;
        pose proof (PTrieT.T_set_le unit b tt seen) as Hset;
        time_cbn; PTrieT.trie_get_le;
        destruct (trie_get b seen); time_simpl; time_cbn; nia) (Empty, [])) as Hfold
  end.
  lazymatch goal with
  | |- context [List.T_rev_append ?items []] =>
    assert (Hlength : length items <= length bs)
      by (rewrite first_blocks_fold, app_nil_r, length_rev; apply selected_blocks_length);
    pose proof (List.T_rev_append_le items []) as Hrev
  end.
  rewrite !Nat2N.inj_add in *; time_cbn_all; nia.
Qed.

(** * Preparation counters and list primitives *)

(** The positive source-width budget also covers empty syntax. *)
Definition prep_width {K G} (p : func positive K G) := N.of_nat (function_width p + 1).

Lemma prep_width_positive {K G} (p : func positive K G) : (1 <= prep_width p)%N.
Proof.
  unfold prep_width. rewrite Nat2N.inj_add. lia.
Qed.

Lemma prep_counter_bits i : N.size_nat i <= Pos.size_nat (N.succ_pos i).
Proof.
  destruct i as [|p]; [cbn; lia|].
  change (Pos.size_nat p <= Pos.size_nat (Pos.succ p)).
  induction p as [p IH|p IH|]; cbn [Pos.succ Pos.size_nat]; lia.
Qed.

Lemma prep_counter_clock {K G} (p : func positive K G) i :
  (i <= N.of_nat (function_size p + 1))%N ->
  (N.T_succ i <= 4 * prep_width p)%N.
Proof.
  intro Hindex. pose proof (function_index_width p i Hindex) as Hwidth.
  pose proof (prep_counter_bits i) as Hbits.
  pose proof (N.T_succ_le i) as Hclock.
  unfold prep_width. rewrite !Nat2N.inj_add in *. nia.
Qed.

Lemma prep_code_rows_clock {K G} (p : func positive K G) b i
    (cs : list (positive * K * list positive)) :
  (i + N.of_nat (length cs) <= N.of_nat (function_size p + 1))%N ->
  (T_code_rows b i cs <= 16 * prep_width p * N.of_nat (length cs + 1))%N.
Proof.
  revert i. induction cs as [|[[x op] ys] rest IH]; intros i Hindex.
  - pose proof (prep_width_positive p) as Hpositive. time_step.
  - assert (Hcurrent : (i <= N.of_nat (function_size p + 1))%N) by lia.
    pose proof (prep_counter_clock p i Hcurrent) as Hsucc.
    assert (Hnext : (N.succ i + N.of_nat (length rest) <=
      N.of_nat (function_size p + 1))%N).
    { cbn [length] in Hindex. rewrite Nat2N.inj_succ in Hindex. lia. }
    specialize (IH (N.succ i) Hnext).
    pose proof (prep_width_positive p) as Hpositive.
    time_unfold @T_code_rows. time_simpl. cbn [length].
    rewrite !Nat2N.inj_add in *. nia.
Qed.

Lemma prep_pair_args_clock xs ys :
  (T_pair_args xs ys <= 2 * N.of_nat (length ys + 1))%N.
Proof.
  revert xs. induction ys as [|y rest IH]; intros [|x xs]; time_step.
Qed.

Lemma prep_pair_args_length xs ys : length (pair_args xs ys) <= length ys.
Proof.
  revert xs. induction ys as [|y rest IH]; intros [|x xs]; cbn [pair_args length];
    [lia|lia|lia|pose proof (IH xs); lia].
Qed.

Lemma prep_param_defs_clock {K} b i xs :
  (@T_param_defs K b i xs <= 2 * N.of_nat (length xs + 1))%N.
Proof.
  revert i. induction xs as [|x rest IH]; intro i.
  - time_step.
  - specialize (IH (S i)). time_step.
Qed.

Lemma prep_param_defs_length {K} b i xs : length (@param_defs K b i xs) = length xs.
Proof.
  revert i. induction xs as [|x rest IH]; intro i; cbn [param_defs length];
    [reflexivity|now rewrite IH].
Qed.

(** * Preparation key budgets *)

(** The common scale contains every key and trie coefficient used during preparation. *)
Definition prep_scale : N :=
  (PTrieT.c_trie + PointKey.c_key + PointEdge.c_key + BlockEdge.c_key + 16)%N.

(** One syntax item pays for any encoded-key lookup or insertion at its source width. *)
Definition prep_atom {K G} (p : func positive K G) : N :=
  (1024 * prep_scale * prep_width p)%N.

(** The tuple encodings used by preparation stay within this uniform width allowance. *)
Definition prep_key_bounded {K G} (p : func positive K G) (key : positive) : Prop :=
  Pos.size_nat key <= 128 * (function_width p + 1).

Lemma prep_scale_positive : (16 <= prep_scale)%N.
Proof.
  unfold prep_scale. lia.
Qed.

Lemma prep_atom_positive {K G} (p : func positive K G) : (1 <= prep_atom p)%N.
Proof.
  pose proof prep_scale_positive as Hscale. pose proof (prep_width_positive p) as Hwidth.
  unfold prep_atom. change (1 * 1 * 1 <= 1024 * prep_scale * prep_width p)%N.
  repeat apply N.mul_le_mono; lia.
Qed.

Lemma prep_width_atom {K G} (p : func positive K G) : (prep_width p <= prep_atom p)%N.
Proof.
  pose proof prep_scale_positive as Hscale. unfold prep_atom.
  rewrite <- (N.mul_1_l (prep_width p)) at 1. apply N.mul_le_mono_r.
  nia.
Qed.

Lemma prep_units_inflation {K G} (p : func positive K G) units :
  (N.of_nat units <= prep_atom p * N.of_nat units)%N.
Proof.
  rewrite <- (N.mul_1_l (N.of_nat units)) at 1. apply N.mul_le_mono_r.
  apply prep_atom_positive.
Qed.

Lemma prep_units_positive {K G} (p : func positive K G) units :
  1 <= units -> (1 <= prep_atom p * N.of_nat units)%N.
Proof.
  intro Hpositive. eapply N.le_trans; [|apply prep_units_inflation]. lia.
Qed.

Lemma prep_product {K G} (p : func positive K G) c units :
  (c <= prep_scale -> units <= 129 * prep_width p -> c * units <= prep_atom p)%N.
Proof.
  intros Hc Hu. eapply N.le_trans.
  - apply N.mul_le_mono; [exact Hc|exact Hu].
  - unfold prep_atom. replace (prep_scale * (129 * prep_width p))%N with
      (129 * (prep_scale * prep_width p))%N by ring.
    replace (1024 * prep_scale * prep_width p)%N with
      (1024 * (prep_scale * prep_width p))%N by ring.
    apply N.mul_le_mono_r. lia.
Qed.

Lemma prep_key_units {K G} (p : func positive K G) key : prep_key_bounded p key ->
  (N.of_nat (Pos.size_nat key + 1) <= 129 * prep_width p)%N.
Proof.
  intro Hkey. unfold prep_key_bounded in Hkey. unfold prep_width.
  rewrite Nat2N.inj_add. lia.
Qed.

Lemma prep_set_clock {K G A} (p : func positive K G) key (value : A) table :
  prep_key_bounded p key -> (PTrieCode.T_set key value table <= prep_atom p)%N.
Proof.
  intro Hkey. eapply N.le_trans; [apply PTrieT.T_set_le|]. apply prep_product.
  - unfold prep_scale; lia.
  - now apply prep_key_units.
Qed.

Lemma prep_get_clock {K G A} (p : func positive K G) key (table : ptrie A) :
  prep_key_bounded p key -> (T_trie_get key table <= prep_atom p)%N.
Proof.
  intro Hkey. eapply N.le_trans; [apply PTrieT.T_trie_get_le|].
  apply prep_product; [pose proof prep_scale_positive; lia|].
  pose proof (prep_key_units p key Hkey). lia.
Qed.

Lemma prep_row_clock {K G A} (p : func positive K G) key (table : ptrie (list A)) :
  prep_key_bounded p key -> (T_index_row table key <= 2 * prep_atom p)%N.
Proof.
  intro Hkey. pose proof (prep_get_clock p key table Hkey) as Hget.
  pose proof (prep_atom_positive p) as Hpositive. time_unfold @T_index_row.
  destruct (trie_get key table); nia.
Qed.

Lemma prep_listed_clock {K G A} (p : func positive K G) key (table : ptrie A) :
  prep_key_bounded p key -> (T_is_listed table key <= 2 * prep_atom p)%N.
Proof.
  intro Hkey. pose proof (prep_get_clock p key table Hkey) as Hget.
  pose proof (prep_atom_positive p) as Hpositive. time_unfold @T_is_listed.
  destruct (trie_get key table); nia.
Qed.

Lemma prep_id_key {K G} (p : func positive K G) x :
  In x (function_ids p) -> prep_key_bounded p x.
Proof.
  intro Hin. pose proof (function_id_width p x Hin). unfold prep_key_bounded; lia.
Qed.

Lemma prep_entry_key {K G} (p : func positive K G) :
  prep_key_bounded p (entry _ _ _ p).
Proof.
  apply prep_id_key. unfold function_ids; now left.
Qed.

Lemma prep_block_key {K G} (p : func positive K G) b body :
  In (b, body) (blocks _ _ _ p) -> prep_key_bounded p b.
Proof.
  intro Hin. apply prep_id_key. now apply (block_id_in_function p b body).
Qed.

Lemma prep_var_key {K G} (p : func positive K G) x :
  In x (function_vars p) -> prep_key_bounded p x.
Proof.
  intro Hin. apply prep_id_key. unfold function_ids; right. apply in_or_app; now left.
Qed.

Lemma prep_point_key {K G} (p : func positive K G) n :
  In n (lang_points (lang_prepare p)) -> prep_key_bounded p (PointKey.encode n).
Proof.
  intro Hin. pose proof (lang_point_key_width p n Hin) as Hwidth.
  change (Pos.size_nat (PointKey.encode n) <= 4 * (function_width p + 1)) in Hwidth.
  unfold prep_key_bounded. lia.
Qed.

Lemma prep_point_edge_key {K G} (p : func positive K G) e :
  In e (lang_point_edges (lang_prepare p)) -> prep_key_bounded p (PointEdge.encode e).
Proof.
  intro Hin. destruct (lang_point_edges_nodes _ _ Hin) as [Hsrc Hdst].
  pose proof (lang_point_key_width _ _ Hsrc) as Hsrc_key.
  pose proof (lang_point_key_width _ _ Hdst) as Hdst_key.
  assert (Hblock : forall be, point_block_edge e = Some be ->
    BlockEdge.bits be <= 4 * (function_width p + 1)).
  { intros be Hbe. destruct (lang_point_edge_block_sides _ _ _ Hin Hbe) as [Hs Ht].
    destruct (lang_point_bounds _ _ Hsrc) as [Hsrc_block _].
    destruct (lang_point_bounds _ _ Hdst) as [Hdst_block _].
    apply block_edge_width_from_ends; [now rewrite Hs|now rewrite Ht]. }
  change (PointEdge.bits e <= 128 * (function_width p + 1)).
  unfold PointEdge.bits, PointEdge.encode, point_edge_tuple,
    PointEdgeTupleKey.encode, PointTargetEdgeKey.encode, pair_code.
  cbn [fst snd]. rewrite !glue_bits.
  fold (PointKey.bits (point_src e)). fold (PointKey.bits (point_dst e)).
  destruct (point_block_edge e) as [be|] eqn:Hbe.
  - specialize (Hblock be eq_refl). cbn [OptionalBlockEdgeKey.encode option_code Pos.size_nat].
    fold (BlockEdge.bits be). lia.
  - cbn [OptionalBlockEdgeKey.encode option_code Pos.size_nat]. lia.
Qed.

Lemma prep_point_encode {K G} (p : func positive K G) n :
  In n (lang_points (lang_prepare p)) -> (PointKey.T_encode n <= prep_atom p)%N.
Proof.
  intro Hin. eapply N.le_trans; [apply PointKey.T_encode_le|]. apply prep_product.
  - unfold prep_scale; lia.
  - apply prep_key_units. now apply prep_point_key.
Qed.

Lemma prep_point_edge_encode {K G} (p : func positive K G) e :
  In e (lang_point_edges (lang_prepare p)) -> (PointEdge.T_encode e <= prep_atom p)%N.
Proof.
  intro Hin. eapply N.le_trans; [apply PointEdge.T_encode_le|]. apply prep_product.
  - unfold prep_scale; lia.
  - apply prep_key_units. now apply prep_point_edge_key.
Qed.

(** * Preparation syntax counts *)

(** A retained block pays for its header, instructions, and variable occurrences. *)
Definition prep_body_units {K G} (body : block positive K G) : nat :=
  1 + length (code _ _ _ body) + length (present_body_vars body).

Lemma prep_weight_one {A} (xs : list A) : present_weight (fun _ => 1) xs = length xs.
Proof.
  induction xs as [|x rest IH]; [reflexivity|].
  change (S (present_weight (fun _ : A => 1) rest) = S (length rest)).
  now rewrite IH.
Qed.

Lemma prep_source_units {K G} (p : func positive K G) :
  present_weight (fun item => prep_body_units (snd item)) (blocks _ _ _ p) <=
    function_size p.
Proof.
  unfold prep_body_units. rewrite !present_weight_plus, prep_weight_one.
  unfold function_size, function_vars. rewrite length_app, present_flat_length.
  unfold present_body_vars, present_weight. lia.
Qed.

Lemma prep_kept_units {K G} (p : func positive K G) :
  present_weight (fun item => prep_body_units (snd item))
    (first_blocks (blocks _ _ _ p)) <= function_size p.
Proof.
  rewrite first_blocks_selected. eapply Nat.le_trans; [apply selected_blocks_weight|].
  apply prep_source_units.
Qed.

Lemma prep_weight_length {A} (weight : A -> nat) xs :
  (forall x, In x xs -> 1 <= weight x) -> length xs <= present_weight weight xs.
Proof.
  induction xs as [|x rest IH]; intro Hpositive; [reflexivity|].
  pose proof (Hpositive x (or_introl eq_refl)) as Hhead.
  specialize (IH ltac:(intros y Hy; apply Hpositive; now right)).
  change (S (length rest) <= weight x + present_weight weight rest). lia.
Qed.

Lemma prep_kept_length {K G} (p : func positive K G) :
  length (first_blocks (blocks _ _ _ p)) <= function_size p.
Proof.
  eapply Nat.le_trans; [|apply prep_kept_units]. apply prep_weight_length.
  intros item Hin. unfold prep_body_units; lia.
Qed.

Lemma prep_kept_original {K G} (p : func positive K G) item :
  In item (first_blocks (blocks _ _ _ p)) -> In item (blocks _ _ _ p).
Proof.
  rewrite first_blocks_selected. intro Hin. now apply selected_blocks_in in Hin as [Hin _].
Qed.

Lemma prep_kept_body_vars {K G} (p : func positive K G) :
  length (flat_map (fun item => present_body_vars (snd item))
    (first_blocks (blocks _ _ _ p))) <= function_size p.
Proof.
  rewrite present_flat_length. eapply Nat.le_trans; [|apply prep_kept_units].
  apply present_weight_mono. intros item Hin. unfold prep_body_units; lia.
Qed.

Lemma prep_input_length {K G} (p : func positive K G) :
  length (inputs _ _ _ p) <= function_size p.
Proof.
  unfold function_size, function_vars. rewrite length_app. lia.
Qed.

Lemma prep_source_length {K G} (p : func positive K G) :
  length (blocks _ _ _ p) <= function_size p.
Proof.
  unfold function_size; lia.
Qed.

Lemma prep_kept_key {K G} (p : func positive K G) item :
  In item (first_blocks (blocks _ _ _ p)) -> prep_key_bounded p (fst item).
Proof.
  intro Hin. apply prep_kept_original in Hin.
  destruct item as [b body]; cbn [fst]. now apply (prep_block_key p b body).
Qed.

Lemma prep_kept_var_key {K G} (p : func positive K G) item x :
  In item (first_blocks (blocks _ _ _ p)) -> In x (present_body_vars (snd item)) ->
  prep_key_bounded p x.
Proof.
  intros Hitem Hx. apply prep_var_key. now apply (kept_body_vars_in_function p item x).
Qed.

Lemma prep_block_edge_key {K G} (p : func positive K G) edge :
  In edge (lang_edges (lang_prepare p)) -> prep_key_bounded p (BlockEdge.encode edge).
Proof.
  intro Hin. destruct (lang_edges_shape p edge Hin) as [body [Hsource [Htarget Hlisted]]].
  apply prep_kept_original in Hsource.
  pose proof (function_id_width p (edge_source edge)
    (block_id_in_function p (edge_source edge) body Hsource)) as Hsrc.
  pose proof (function_id_width p (edge_target edge)
    (target_in_function p (edge_source edge) body (edge_target edge) Hsource Htarget)) as Hdst.
  pose proof (block_edge_width_from_ends edge (function_width p) Hsrc Hdst) as Hwidth.
  change (BlockEdge.bits edge <= 128 * (function_width p + 1)). lia.
Qed.

Lemma prep_block_edge_encode {K G} (p : func positive K G) edge :
  In edge (lang_edges (lang_prepare p)) -> (BlockEdge.T_encode edge <= prep_atom p)%N.
Proof.
  intro Hin. eapply N.le_trans; [apply BlockEdge.T_encode_le|]. apply prep_product.
  - unfold prep_scale; lia.
  - apply prep_key_units. now apply prep_block_edge_key.
Qed.

Lemma prep_block_args_count {A K G} (kept : ptrie A)
    (bs : list (positive * block positive K G)) :
  present_weight (fun row => length (snd row))
    (flat_map (fun item => listed_edge_args kept (fst item) (term _ _ _ (snd item))) bs) <=
    length (flat_map (fun item => present_body_vars (snd item)) bs).
Proof.
  rewrite present_weight_flat_map, present_flat_length. apply present_weight_mono.
  intros item Hin. pose proof (listed_edge_args_length kept (fst item)
    (term _ _ _ (snd item))) as Hargs.
  unfold present_body_vars. rewrite !length_app. lia.
Qed.

Lemma prep_params_row_length {K G} (p : func positive K G) key :
  length (index_row (first_table PosKeyCode.encode
    (map (fun item => (fst item, params _ _ _ (snd item)))
      (first_blocks (blocks _ _ _ p)))) key) <= function_size p.
Proof.
  pose proof (present_first_table_count PosKeyCode.encode [key]
    (map (fun item => (fst item, params _ _ _ (snd item)))
      (first_blocks (blocks _ _ _ p)))
    ltac:(constructor; [tauto|constructor])) as Hcount.
  change (length (index_row (first_table PosKeyCode.encode
    (map (fun item => (fst item, params _ _ _ (snd item)))
      (first_blocks (blocks _ _ _ p)))) key) + 0 <=
    present_weight (fun row => length (snd row))
      (map (fun item => (fst item, params _ _ _ (snd item)))
        (first_blocks (blocks _ _ _ p)))) in Hcount.
  rewrite present_weight_map in Hcount. cbn [snd] in Hcount.
  rewrite Nat.add_0_r in Hcount.
  eapply Nat.le_trans; [exact Hcount|]. eapply Nat.le_trans; [|apply prep_kept_units].
  apply present_weight_mono. intros item Hin. unfold prep_body_units, present_body_vars.
  rewrite !length_app. lia.
Qed.

Lemma prep_pipeline_counts {K G} (p : func positive K G) :
  let bs := first_blocks (blocks _ _ _ p) in
  let kept := first_table PosKeyCode.encode
    (map (fun item => (fst item, params _ _ _ (snd item))) bs) in
  let ss := map (summarize kept) bs in
  let block_rows := flat_map (fun item =>
    listed_edge_args kept (fst item) (term _ _ _ (snd item))) bs in
  let rows := flat_map (fun s => summary_internal s ++ summary_outgoing s) ss in
  length bs <= function_size p /\
  length ss <= function_size p /\
  length block_rows <= 2 * function_size p /\
  length rows <= 5 * function_size p /\
  length (flat_map summary_points ss) <= 5 * function_size p /\
  present_weight present_row_vars rows <= 2 * function_size p /\
  present_weight (fun s => length (summary_returns s)) ss <= 2 * function_size p /\
  present_weight (fun row => length (snd row)) block_rows <= function_size p.
Proof.
  cbn zeta.
  set (bs := first_blocks (blocks _ _ _ p)).
  set (kept := first_table PosKeyCode.encode
    (map (fun item => (fst item, params _ _ _ (snd item))) bs)).
  set (ss := map (summarize kept) bs).
  set (block_rows := flat_map (fun item =>
    listed_edge_args kept (fst item) (term _ _ _ (snd item))) bs).
  set (rows := flat_map (fun s => summary_internal s ++ summary_outgoing s) ss).
  pose proof (prep_kept_length p) as Hblocks. fold bs in Hblocks.
  assert (Hsummaries : length ss = length bs) by (unfold ss; apply length_map).
  pose proof (prep_kept_body_vars p) as Hbodyvars. fold bs in Hbodyvars.
  pose proof (lang_edges_length p) as Hedges.
  change (length (map fst block_rows) <= 2 * length (map fst bs)) in Hedges.
  rewrite !length_map in Hedges.
  pose proof (lang_structure_length p) as Hstructure.
  change (length (flat_map summary_points ss) +
    length (map (fun row => fst (fst row)) rows) <= 5 * function_size p) in Hstructure.
  rewrite length_map in Hstructure.
  pose proof (summaries_vars_count kept bs) as Hvars. fold ss rows in Hvars.
  pose proof (prep_block_args_count kept bs) as Hargs. fold block_rows in Hargs.
  change (length bs <= function_size p /\
    length ss <= function_size p /\
    length block_rows <= 2 * function_size p /\
    length rows <= 5 * function_size p /\
    length (flat_map summary_points ss) <= 5 * function_size p /\
    present_weight present_row_vars rows <= 2 * function_size p /\
    present_weight (fun s => length (summary_returns s)) ss <= 2 * function_size p /\
    present_weight (fun row => length (snd row)) block_rows <= function_size p).
  repeat split; try lia.
  eapply Nat.le_trans; [apply Nat.le_add_l|exact Hstructure].
Qed.

(** * Preparation exit clocks *)

Lemma prep_filter_uniform {A} (predicate : A -> bool) Tpredicate xs bound :
  (forall x, In x xs -> (Tpredicate x <= bound)%N) ->
  (List.T_filter predicate Tpredicate xs <= (bound + 1) * N.of_nat (length xs) + 1)%N.
Proof.
  induction xs as [|x rest IH]; intro Hbound.
  - time_step.
  - pose proof (Hbound x (or_introl eq_refl)) as Hhead.
    specialize (IH ltac:(intros y Hy; apply Hbound; now right)).
    time_unfold @List.T_filter. destruct (predicate x);
      change (1 + (Tpredicate x + List.T_filter predicate Tpredicate rest) <=
        (bound + 1) * N.of_nat (S (length rest)) + 1)%N;
      rewrite Nat2N.inj_succ; nia.
Qed.

Lemma prep_exit_args_clock {G} b (e : exit positive G) : T_exit_edge_args b e = 1%N.
Proof.
  destruct e; reflexivity.
Qed.

Lemma prep_exit_guards_clock {G} b (e : exit positive G) : T_exit_guards b e = 1%N.
Proof.
  destruct e; reflexivity.
Qed.

Lemma prep_guard_uses_clock {G} (e : exit positive G) : T_guard_uses e = 1%N.
Proof.
  destruct e; reflexivity.
Qed.

Lemma prep_exit_returns_clock {G} (e : exit positive G) : T_exit_returns e = 1%N.
Proof.
  destruct e; reflexivity.
Qed.

Lemma prep_exit_args_length {G} b (e : exit positive G) : length (exit_edge_args b e) <= 2.
Proof.
  destruct e; cbn [exit_edge_args length]; lia.
Qed.

Lemma prep_exit_guards_length {G} b (e : exit positive G) : length (exit_guards b e) <= 2.
Proof.
  destruct e; cbn [exit_guards length]; lia.
Qed.

Lemma prep_listed_args_clock {K G A} (p : func positive K G) (kept : ptrie A) b
    (e : exit positive G) :
  (forall target, In target (exit_targets e) -> prep_key_bounded p target) ->
  (T_listed_edge_args kept b e <= 16 * prep_atom p)%N.
Proof.
  intro Htargets. pose proof (prep_atom_positive p) as Hpositive.
  pose proof (prep_exit_args_length b e) as Hlength.
  time_unfold @T_listed_edge_args. rewrite prep_exit_args_clock.
  lazymatch goal with
  | |- context [List.T_filter ?predicate ?clock (exit_edge_args b e)] =>
    assert (Hfilter : (List.T_filter predicate clock (exit_edge_args b e) <=
      (5 * prep_atom p + 1) * N.of_nat (length (exit_edge_args b e)) + 1)%N)
  end.
  { apply prep_filter_uniform. intros [edge args] Hin.
    destruct (exit_edge_args_shape b e edge args Hin) as [_ Htarget].
    pose proof (prep_listed_clock p (edge_target edge) kept (Htargets _ Htarget)) as Hlisted.
    time_simpl. cbn [fst snd]. nia. }
  assert (Hsmall : ((5 * prep_atom p + 1) * N.of_nat (length (exit_edge_args b e)) <=
    (5 * prep_atom p + 1) * 2)%N) by (apply N.mul_le_mono_l; lia).
  nia.
Qed.

Lemma prep_exit_guard_target {G} b (e : exit positive G) edge guards :
  In (edge, guards) (exit_guards b e) -> In (edge_target edge) (exit_targets e).
Proof.
  destruct e; cbn [exit_guards exit_targets]; intro Hin.
  - destruct Hin as [Heq|[]]; inversion Heq; subst; cbn; auto.
  - destruct Hin as [Heq|[Heq|[]]]; inversion Heq; subst; cbn; auto.
  - contradiction.
Qed.

Lemma prep_listed_guards_clock {K G A} (p : func positive K G) (kept : ptrie A) b
    (e : exit positive G) :
  (forall target, In target (exit_targets e) -> prep_key_bounded p target) ->
  (T_listed_guards kept b e <= 16 * prep_atom p)%N.
Proof.
  intro Htargets. pose proof (prep_atom_positive p) as Hpositive.
  pose proof (prep_exit_guards_length b e) as Hlength.
  time_unfold @T_listed_guards. rewrite prep_exit_guards_clock.
  lazymatch goal with
  | |- context [List.T_filter ?predicate ?clock (exit_guards b e)] =>
    assert (Hfilter : (List.T_filter predicate clock (exit_guards b e) <=
      (5 * prep_atom p + 1) * N.of_nat (length (exit_guards b e)) + 1)%N)
  end.
  { apply prep_filter_uniform. intros [edge guards] Hin.
    pose proof (prep_exit_guard_target b e edge guards Hin) as Htarget.
    pose proof (prep_listed_clock p (edge_target edge) kept (Htargets _ Htarget)) as Hlisted.
    time_simpl. cbn [fst snd]. nia. }
  assert (Hsmall : ((5 * prep_atom p + 1) * N.of_nat (length (exit_guards b e)) <=
    (5 * prep_atom p + 1) * 2)%N) by (apply N.mul_le_mono_l; lia).
  nia.
Qed.

Lemma prep_listed_args_length {A G} (kept : ptrie A) b (e : exit positive G) :
  length (listed_edge_args kept b e) <= 2.
Proof.
  unfold listed_edge_args. eapply Nat.le_trans; [apply filter_length_le|].
  apply prep_exit_args_length.
Qed.

Lemma prep_listed_guards_length {A G} (kept : ptrie A) b (e : exit positive G) :
  length (listed_guards kept b e) <= 2.
Proof.
  unfold listed_guards. eapply Nat.le_trans; [apply filter_length_le|].
  apply prep_exit_guards_length.
Qed.

Lemma prep_guard_uses_length {G} (e : exit positive G) :
  length (guard_uses e) <= length (exit_uses e).
Proof.
  destruct e; cbn [guard_uses exit_uses length]; repeat rewrite length_app; lia.
Qed.

Lemma prep_guard_edge_keys {A G} (kept : ptrie A) b (e : exit positive G) :
  map fst (listed_guards kept b e) = map fst (listed_edge_args kept b e).
Proof.
  destruct e; cbn [listed_guards listed_edge_args exit_guards exit_edge_args filter
    fst edge_target]; repeat match goal with
    | |- context [if ?flag then _ else _] => destruct flag
    end; reflexivity.
Qed.

(** * Preparation definition clocks *)

Lemma prep_block_defs_length {K G} (body : block positive K G) :
  length (block_defs body) = length (params _ _ _ body) + length (code _ _ _ body).
Proof.
  unfold block_defs. now rewrite length_app, length_map.
Qed.

Lemma prep_block_defs_vars {K G} (body : block positive K G) x :
  In x (block_defs body) -> In x (present_body_vars body).
Proof.
  unfold block_defs, present_body_vars. intro Hin. apply in_app_or in Hin as [Hparam|Hcode].
  - apply in_or_app; now left.
  - apply in_or_app; right. apply in_or_app; left.
    apply in_map_iff in Hcode as [[[dst op] args] [Heq Hin]]. cbn in Heq; subst dst.
    apply in_flat_map; exists (x, op, args). split; [exact Hin|now left].
Qed.

Lemma prep_block_defs_units {K G} (body : block positive K G) :
  length (block_defs body) + 1 <= prep_body_units body.
Proof.
  rewrite prep_block_defs_length. unfold prep_body_units, present_body_vars.
  rewrite !length_app. lia.
Qed.

Lemma prep_param_defs_keys {K} b i xs : map fst (@param_defs K b i xs) = xs.
Proof.
  revert i. induction xs as [|x rest IH]; intro i; cbn [param_defs map fst];
    [reflexivity|now rewrite IH].
Qed.

Lemma prep_value_defs_keys {K G} (item : positive * block positive K G) :
  map fst (block_value_defs item) = block_defs (snd item).
Proof.
  unfold block_value_defs, block_defs. rewrite map_app, prep_param_defs_keys, map_map.
  reflexivity.
Qed.

Lemma prep_value_defs_length {K G} (item : positive * block positive K G) :
  length (block_value_defs item) = length (block_defs (snd item)).
Proof.
  rewrite <- prep_value_defs_keys, length_map. reflexivity.
Qed.

Lemma prep_homes_keys {K G} (item : positive * block positive K G) :
  map fst (block_homes item) = block_defs (snd item).
Proof.
  unfold block_homes. rewrite map_map. apply map_id.
Qed.

Lemma prep_homes_length {K G} (item : positive * block positive K G) :
  length (block_homes item) = length (block_defs (snd item)).
Proof.
  unfold block_homes. apply length_map.
Qed.

Lemma prep_block_defs_clock {K G} (body : block positive K G) :
  (T_block_defs body <=
    8 * N.of_nat (length (params _ _ _ body) + length (code _ _ _ body) + 1))%N.
Proof.
  pose proof (Datatypes.T_app_le (params _ _ _ body)
    (map (fun instruction => fst (fst instruction)) (code _ _ _ body))) as Happend.
  time_unfold @T_block_defs. time_simpl.
  lazymatch goal with
  | |- context [ListDef.T_map ?f ?Tf (code _ _ _ body)] =>
    pose proof (prep_map_uniform f Tf (code _ _ _ body) 3%N
      ltac:(intros item Hin; time_simpl; lia)) as Hmap
  end.
  rewrite !Nat2N.inj_add in *. lia.
Qed.

Lemma prep_block_homes_clock {K G} (item : positive * block positive K G) :
  (T_block_homes item <= 16 * N.of_nat (prep_body_units (snd item)))%N.
Proof.
  pose proof (prep_block_defs_clock (snd item)) as Hdefs.
  pose proof (prep_block_defs_units (snd item)) as Hcount.
  pose proof (prep_block_defs_length (snd item)) as Hlength.
  time_unfold @T_block_homes. time_simpl.
  lazymatch goal with
  | |- context [ListDef.T_map ?f ?Tf (block_defs (snd item))] =>
    pose proof (prep_map_uniform f Tf (block_defs (snd item)) 2%N
      ltac:(intros x Hin; time_simpl; lia)) as Hmap
  end.
  rewrite !Nat2N.inj_add in *. lia.
Qed.

Lemma prep_block_values_clock {K G} (item : positive * block positive K G) :
  (T_block_value_defs item <= 16 * N.of_nat (prep_body_units (snd item)))%N.
Proof.
  pose proof (prep_param_defs_clock (K := K) (fst item) 0
    (params _ _ _ (snd item))) as Hparams.
  pose proof (Datatypes.T_app_le (param_defs (K := K) (fst item) 0
    (params _ _ _ (snd item)))
    (map (fun i => (fst (fst i), Op (snd (fst i)) (snd i))) (code _ _ _ (snd item))))
    as Happend.
  rewrite prep_param_defs_length in Happend.
  pose proof (prep_block_defs_units (snd item)) as Hcount.
  rewrite prep_block_defs_length in Hcount.
  time_unfold @T_block_value_defs. time_simpl.
  lazymatch goal with
  | |- context [ListDef.T_map ?f ?Tf (code _ _ _ (snd item))] =>
    pose proof (prep_map_uniform f Tf (code _ _ _ (snd item)) 6%N
      ltac:(intros instruction Hin; time_simpl; lia)) as Hmap
  end.
  rewrite !Nat2N.inj_add in *. lia.
Qed.

(** * Preparation table clocks *)

Lemma prep_first_clock {K G A B} (p : func positive K G) (key : A -> positive)
    Tkey (rows : list (A * B)) :
  (forall row, In row rows -> (Tkey (fst row) <= prep_atom p)%N) ->
  (forall row, In row rows -> prep_key_bounded p (key (fst row))) ->
  (T_first_table key Tkey rows <= 8 * prep_atom p * N.of_nat (length rows + 1))%N.
Proof.
  intros Hclock Hwidth. apply prep_first_table_clock; [apply prep_atom_positive|exact Hclock|].
  intros row Hin table. apply prep_set_clock. now apply Hwidth.
Qed.

Lemma prep_multi_clock {K G A} (p : func positive K G) (key : A -> positive)
    Tkey (rows : list A) :
  (forall row, In row rows -> (Tkey row <= 4 * prep_atom p)%N) ->
  (forall row, In row rows -> prep_key_bounded p (key row)) ->
  (T_multi_table key Tkey rows <= 32 * prep_atom p * N.of_nat (length rows + 1))%N.
Proof.
  intros Hclock Hwidth. pose proof (prep_atom_positive p) as Hpositive.
  replace (32 * prep_atom p * N.of_nat (length rows + 1))%N with
    (8 * (4 * prep_atom p) * N.of_nat (length rows + 1))%N by ring.
  apply prep_multi_table_clock; [lia|exact Hclock| |].
  - intros row Hin table. pose proof (prep_row_clock p (key row) table (Hwidth row Hin)); lia.
  - intros row Hin table. pose proof (prep_set_clock p (key row)
      (row :: index_row table (key row)) table (Hwidth row Hin)); lia.
Qed.

Lemma prep_first_positive_clock {K G A} (p : func positive K G)
    (rows : list (positive * A)) :
  (forall row, In row rows -> prep_key_bounded p (fst row)) ->
  (T_first_table PosKeyCode.encode PosKeyT.T_encode rows <=
    8 * prep_atom p * N.of_nat (length rows + 1))%N.
Proof.
  intro Hwidth. apply prep_first_clock; [|exact Hwidth].
  intros row Hin. time_simpl. apply prep_atom_positive.
Qed.

Lemma prep_first_point_clock {K G A} (p : func positive K G)
    (rows : list (point_key * A)) :
  (forall row, In row rows -> In (fst row) (lang_points (lang_prepare p))) ->
  (T_first_table PointKey.encode PointKey.T_encode rows <=
    8 * prep_atom p * N.of_nat (length rows + 1))%N.
Proof.
  intro Hkeys. apply prep_first_clock.
  - intros row Hin. apply prep_point_encode. now apply Hkeys.
  - intros row Hin. apply prep_point_key. now apply Hkeys.
Qed.

Lemma prep_first_point_edge_clock {K G A} (p : func positive K G)
    (rows : list (point_edge * A)) :
  (forall row, In row rows -> In (fst row) (lang_point_edges (lang_prepare p))) ->
  (T_first_table PointEdge.encode PointEdge.T_encode rows <=
    8 * prep_atom p * N.of_nat (length rows + 1))%N.
Proof.
  intro Hkeys. apply prep_first_clock.
  - intros row Hin. apply prep_point_edge_encode. now apply Hkeys.
  - intros row Hin. apply prep_point_edge_key. now apply Hkeys.
Qed.

Lemma prep_first_block_edge_clock {K G A} (p : func positive K G)
    (rows : list (block_edge * A)) :
  (forall row, In row rows -> In (fst row) (lang_edges (lang_prepare p))) ->
  (T_first_table BlockEdge.encode BlockEdge.T_encode rows <=
    8 * prep_atom p * N.of_nat (length rows + 1))%N.
Proof.
  intro Hkeys. apply prep_first_clock.
  - intros row Hin. apply prep_block_edge_encode. now apply Hkeys.
  - intros row Hin. apply prep_block_edge_key. now apply Hkeys.
Qed.

(** * Preparation aggregate budgets *)

(** The total preparation budget charges each source item once at the common key cost. *)
Definition prep_total {K G} (p : func positive K G) : N :=
  (prep_atom p * N.of_nat (function_size p + 1))%N.

Lemma prep_total_positive {K G} (p : func positive K G) : (1 <= prep_total p)%N.
Proof.
  unfold prep_total. apply prep_units_positive. lia.
Qed.

Lemma prep_atom_total {K G} (p : func positive K G) : (prep_atom p <= prep_total p)%N.
Proof.
  unfold prep_total. rewrite <- (N.mul_1_r (prep_atom p)) at 1.
  apply N.mul_le_mono_l. lia.
Qed.

Lemma prep_count_cost {K G} (p : func positive K G) time price count factor :
  (time <= price * prep_atom p * N.of_nat (count + 1))%N ->
  count <= factor * function_size p ->
  (time <= price * N.of_nat (factor + 1) * prep_total p)%N.
Proof.
  intros Htime Hcount.
  assert (Hcount' : count + 1 <= (factor + 1) * (function_size p + 1)) by nia.
  apply time_of_nat_le in Hcount'. rewrite Nat2N.inj_mul in Hcount'.
  eapply N.le_trans; [exact Htime|].
  replace (price * N.of_nat (factor + 1) * prep_total p)%N with
    (price * prep_atom p * (N.of_nat (factor + 1) * N.of_nat (function_size p + 1)))%N
    by (unfold prep_total; ring).
  now apply N.mul_le_mono_l.
Qed.

Lemma prep_weight_cost {K G} (p : func positive K G) time price units :
  (time <= (price * prep_atom p + 1) * N.of_nat units + 1)%N ->
  units <= function_size p ->
  (time <= (price + 2) * prep_total p)%N.
Proof.
  intros Htime Hcount. pose proof (prep_atom_positive p) as Hatom.
  pose proof (prep_total_positive p) as Htotal.
  assert (Hcoefficient : (price * prep_atom p + 1 <= (price + 1) * prep_atom p)%N) by nia.
  assert (Hwork : ((price * prep_atom p + 1) * N.of_nat units <=
    (price + 1) * prep_total p)%N).
  { unfold prep_total. rewrite N.mul_assoc.
    apply N.mul_le_mono; [exact Hcoefficient|lia]. }
  replace ((price + 2) * prep_total p)%N with
    ((price + 1) * prep_total p + prep_total p)%N by ring.
  lia.
Qed.

Lemma prep_weight_factor_cost {K G} (p : func positive K G) time price units factor :
  (time <= (price * prep_atom p + 1) * N.of_nat units + 1)%N ->
  units <= factor * function_size p ->
  (time <= (price + 2) * N.of_nat (factor + 1) * prep_total p)%N.
Proof.
  intros Htime Hcount. pose proof (prep_atom_positive p) as Hatom.
  pose proof (prep_units_inflation p units) as Hunits.
  apply (prep_count_cost p time (price + 2)%N units factor); [|exact Hcount].
  rewrite Nat2N.inj_add. nia.
Qed.

Lemma prep_map_total {K G A B} (p : func positive K G) (f : A -> B) Tf xs price factor :
  (forall x, In x xs -> (Tf x <= price * prep_atom p)%N) ->
  length xs <= factor * function_size p ->
  (ListDef.T_map f Tf xs <= (price + 2) * N.of_nat (factor + 1) * prep_total p)%N.
Proof.
  intros Hclock Hcount. apply (prep_weight_factor_cost p _ price (length xs) factor).
  - now apply prep_map_uniform.
  - exact Hcount.
Qed.

Lemma prep_map_weight_total {K G A B} (p : func positive K G) (f : A -> B)
    Tf charge xs price factor :
  (forall x, In x xs -> 1 <= charge x) ->
  (forall x, In x xs -> (Tf x <= price * prep_atom p * N.of_nat (charge x))%N) ->
  present_weight charge xs <= factor * function_size p ->
  (ListDef.T_map f Tf xs <= (price + 2) * N.of_nat (factor + 1) * prep_total p)%N.
Proof.
  intros Hpositive Hclock Hcount.
  apply (prep_weight_factor_cost p _ price (present_weight charge xs) factor).
  - now apply prep_map_weight.
  - exact Hcount.
Qed.

Lemma prep_flat_total {K G A B} (p : func positive K G) (f : A -> list B)
    Tf charge xs price factor :
  (forall x, In x xs -> 1 <= charge x) ->
  (forall x, In x xs -> (Tf x + N.of_nat (length (f x) + 1) <=
    price * prep_atom p * N.of_nat (charge x))%N) ->
  present_weight charge xs <= factor * function_size p ->
  (Code.List.T_flat_map f Tf xs <=
    (price + 2) * N.of_nat (factor + 1) * prep_total p)%N.
Proof.
  intros Hpositive Hclock Hcount.
  apply (prep_weight_factor_cost p _ price (present_weight charge xs) factor).
  - now apply prep_flat_weight.
  - exact Hcount.
Qed.

Lemma prep_row_defs_charge (rows : list point_row) :
  present_weight (fun row => 1 + length (snd row)) rows <=
    length rows + present_weight present_row_vars rows.
Proof.
  rewrite present_weight_plus, prep_weight_one. apply Nat.add_le_mono_l.
  apply present_weight_mono. intros row Hin. unfold present_row_vars; lia.
Qed.

Lemma prep_summary_points_charge (ss : list block_summary) :
  present_weight (fun s => 1 + length (summary_points s)) ss =
    length ss + length (flat_map summary_points ss).
Proof.
  rewrite present_weight_plus, prep_weight_one, present_flat_length. reflexivity.
Qed.

Lemma prep_summary_internal_charge (ss : list block_summary) :
  present_weight (fun s => 1 + length (summary_internal s)) ss <=
    length ss + length (flat_map (fun s => summary_internal s ++ summary_outgoing s) ss).
Proof.
  rewrite present_weight_plus, prep_weight_one, present_flat_length.
  apply Nat.add_le_mono_l. apply present_weight_mono. intros s Hin. rewrite length_app; lia.
Qed.

(** * Preparation summary clocks *)

Lemma prep_summarize_clock {K G A} (p : func positive K G) (kept : ptrie A) item :
  In item (blocks _ _ _ p) ->
  (T_summarize kept item <=
    128 * prep_atom p * N.of_nat (prep_body_units (snd item)))%N.
Proof.
  destruct item as [b body]. intro Hitem. cbn [snd].
  set (units := prep_body_units body).
  set (budget := (prep_atom p * N.of_nat units)%N).
  set (cr := code_rows b 1%N (code _ _ _ body)).
  set (internal := (PointEdge (b, 0%N) (b, 1%N) None, [], params _ _ _ body) :: fst cr).
  assert (Hunits : 1 <= units) by (unfold units, prep_body_units; lia).
  assert (Hbudget : (1 <= budget)%N) by now apply prep_units_positive.
  assert (Hunitpaid : (N.of_nat units <= budget)%N) by apply prep_units_inflation.
  assert (Hatompaid : (prep_atom p <= budget)%N).
  { unfold budget. rewrite <- (N.mul_1_r (prep_atom p)) at 1.
    apply N.mul_le_mono_l. lia. }
  assert (Hcodecount : length (code _ _ _ body) + 1 <= units)
    by (unfold units, prep_body_units; lia).
  assert (Hguardcount : length (guard_uses (term _ _ _ body)) + 1 <= units).
  { pose proof (prep_guard_uses_length (term _ _ _ body)) as Hguard.
    unfold units, prep_body_units, present_body_vars. rewrite !length_app. lia. }
  assert (Hguardpaid : (N.of_nat (length (guard_uses (term _ _ _ body)) + 1) <= budget)%N)
    by (eapply N.le_trans; [|exact Hunitpaid]; lia).
  pose proof (block_code_size p b body Hitem) as Hcodesize.
  pose proof (prep_code_rows_clock p b 1%N (code _ _ _ body)
    ltac:(rewrite Nat2N.inj_add; lia)) as Hcode.
  assert (Hcodepaid : (T_code_rows b 1%N (code _ _ _ body) <= 16 * budget)%N).
  { eapply N.le_trans; [exact Hcode|]. unfold budget.
    replace (16 * (prep_atom p * N.of_nat units))%N with
      (16 * prep_atom p * N.of_nat units)%N by ring.
    apply N.mul_le_mono; [apply N.mul_le_mono_l; apply prep_width_atom|lia]. }
  assert (Htargets : forall target, In target (exit_targets (term _ _ _ body)) ->
    prep_key_bounded p target).
  { intros target Htarget. apply prep_id_key.
    exact (target_in_function p b body target Hitem Htarget). }
  pose proof (prep_listed_args_clock p kept b (term _ _ _ body) Htargets) as Hlisted.
  assert (Hlistedpaid : (T_listed_edge_args kept b (term _ _ _ body) <= 16 * budget)%N).
  { eapply N.le_trans; [exact Hlisted|]. now apply N.mul_le_mono_l. }
  assert (Hinternal : length internal <= units).
  { unfold internal, cr. cbn [length]. rewrite code_rows_length. lia. }
  pose proof (prep_listed_args_length kept b (term _ _ _ body)) as Houtlength.
  time_unfold @T_summarize. cbn beta zeta. time_simpl. cbn [fst snd].
  fold cr internal. rewrite ?prep_guard_uses_clock, ?prep_exit_returns_clock.
  lazymatch goal with
  | |- context [ListDef.T_map ?f ?Tf internal] =>
    assert (Hpoints : (ListDef.T_map f Tf internal <= 6 * budget)%N)
  end.
  { eapply N.le_trans.
    - apply prep_map_uniform with (bound := 4%N). intros row Hin; time_simpl; lia.
    - lia. }
  lazymatch goal with
  | |- context [ListDef.T_map ?f ?Tf (listed_edge_args kept b (term _ _ _ body))] =>
    assert (Houtgoing : (ListDef.T_map f Tf
      (listed_edge_args kept b (term _ _ _ body)) <= 36 * budget)%N)
  end.
  { eapply N.le_trans.
    - apply prep_map_uniform with (bound := (16 * budget)%N).
      intros row Hin. pose proof (Datatypes.T_app_le (guard_uses (term _ _ _ body))
        (snd row)) as Happend. time_simpl. rewrite ?prep_guard_uses_clock.
      rewrite Nat2N.inj_add in Hguardpaid. lia.
    - assert (Hsmall : ((16 * budget + 1) *
        N.of_nat (length (listed_edge_args kept b (term _ _ _ body))) <=
        (16 * budget + 1) * 2)%N) by (apply N.mul_le_mono_l; lia).
      lia. }
  replace (128 * prep_atom p * N.of_nat units)%N with (128 * budget)%N by
    (unfold budget; ring).
  clearbody budget.
  clear - p b body kept units budget cr internal Hbudget Hcodepaid Hlistedpaid Hpoints Houtgoing.
  lia.
Qed.

(** * Preparation block traversal clocks *)

Lemma prep_first_blocks_total {K G} (p : func positive K G) :
  (T_first_blocks (blocks _ _ _ p) <= prep_total p)%N.
Proof.
  pose proof (prep_first_blocks_clock (blocks _ _ _ p) (function_width p)
    ltac:(intros b body Hin; apply function_id_width;
      now apply (block_id_in_function p b body))) as Hfirst.
  assert (Hfactor : ((PTrieT.c_trie + 16) * prep_width p <= prep_atom p)%N).
  { apply prep_product; [unfold prep_scale; lia|].
    rewrite <- (N.mul_1_l (prep_width p)) at 1. apply N.mul_le_mono_r; lia. }
  pose proof (prep_source_length p) as Hlength.
  eapply N.le_trans; [exact Hfirst|]. fold (prep_width p).
  replace ((PTrieT.c_trie + 16) * N.of_nat (length (blocks _ _ _ p) + 1) *
    prep_width p)%N with
    (((PTrieT.c_trie + 16) * prep_width p) *
      N.of_nat (length (blocks _ _ _ p) + 1))%N by ring.
  unfold prep_total. apply N.mul_le_mono; [exact Hfactor|lia].
Qed.

Lemma prep_summaries_total {K G A} (p : func positive K G) (kept : ptrie A) :
  (ListDef.T_map (summarize kept) (fun item => T_summarize kept item)
    (first_blocks (blocks _ _ _ p)) <= 130 * prep_total p)%N.
Proof.
  apply (prep_weight_cost p _ 128%N
    (present_weight (fun item => prep_body_units (snd item))
      (first_blocks (blocks _ _ _ p)))); [|apply prep_kept_units].
  apply prep_map_weight.
  - intros item Hin. unfold prep_body_units; lia.
  - intros item Hin. apply prep_summarize_clock. now apply prep_kept_original.
Qed.

Lemma prep_block_rows_total {K G A} (p : func positive K G) (kept : ptrie A) :
  (Code.List.T_flat_map
    (fun item => listed_edge_args kept (fst item) (term _ _ _ (snd item)))
    (fun item => 1 + (Datatypes.T_fst item +
      (Datatypes.T_snd item + T_term _ _ _ (snd item)) +
      T_listed_edge_args kept (fst item) (term _ _ _ (snd item))))%N
    (first_blocks (blocks _ _ _ p)) <= 26 * prep_total p)%N.
Proof.
  pose proof (prep_atom_positive p) as Hpositive.
  apply (prep_weight_cost p _ 24%N (length (first_blocks (blocks _ _ _ p))));
    [|apply prep_kept_length].
  rewrite <- (prep_weight_one (first_blocks (blocks _ _ _ p))).
  apply prep_flat_weight; [intros; lia|]. intros [b body] Hin.
  assert (Hbody : In (b, body) (blocks _ _ _ p)) by now apply prep_kept_original.
  assert (Htargets : forall t, In t (exit_targets (term _ _ _ body)) -> prep_key_bounded p t).
  { intros t Ht. apply prep_id_key. now apply (target_in_function p b body t). }
  pose proof (prep_listed_args_clock p kept b (term _ _ _ body) Htargets) as Hlisted.
  pose proof (prep_listed_args_length kept b (term _ _ _ body)) as Hlength.
  time_simpl. cbn [fst snd]. lia.
Qed.

Lemma prep_guards_total {K G A} (p : func positive K G) (kept : ptrie A) :
  (Code.List.T_flat_map
    (fun item => listed_guards kept (fst item) (term _ _ _ (snd item)))
    (fun item => 1 + (Datatypes.T_fst item +
      (Datatypes.T_snd item + T_term _ _ _ (snd item)) +
      T_listed_guards kept (fst item) (term _ _ _ (snd item))))%N
    (first_blocks (blocks _ _ _ p)) <= 26 * prep_total p)%N.
Proof.
  pose proof (prep_atom_positive p) as Hpositive.
  apply (prep_weight_cost p _ 24%N (length (first_blocks (blocks _ _ _ p))));
    [|apply prep_kept_length].
  rewrite <- (prep_weight_one (first_blocks (blocks _ _ _ p))).
  apply prep_flat_weight; [intros; lia|]. intros [b body] Hin.
  assert (Hbody : In (b, body) (blocks _ _ _ p)) by now apply prep_kept_original.
  assert (Htargets : forall t, In t (exit_targets (term _ _ _ body)) -> prep_key_bounded p t).
  { intros t Ht. apply prep_id_key. now apply (target_in_function p b body t). }
  pose proof (prep_listed_guards_clock p kept b (term _ _ _ body) Htargets) as Hlisted.
  pose proof (prep_listed_guards_length kept b (term _ _ _ body)) as Hlength.
  time_simpl. cbn [fst snd]. lia.
Qed.

Lemma prep_defs_flat_length {K G} (p : func positive K G) :
  length (flat_map (fun item => block_defs (snd item))
    (first_blocks (blocks _ _ _ p))) <= function_size p.
Proof.
  rewrite present_flat_length. eapply Nat.le_trans; [|apply prep_kept_units].
  apply present_weight_mono. intros item Hin.
  pose proof (prep_block_defs_units (snd item)); lia.
Qed.

Lemma prep_values_flat_length {K G} (p : func positive K G) :
  length (flat_map block_value_defs (first_blocks (blocks _ _ _ p))) <= function_size p.
Proof.
  rewrite present_flat_length. eapply Nat.le_trans; [|apply prep_kept_units].
  apply present_weight_mono. intros item Hin. rewrite prep_value_defs_length.
  pose proof (prep_block_defs_units (snd item)); lia.
Qed.

Lemma prep_homes_flat_length {K G} (p : func positive K G) :
  length (flat_map block_homes (first_blocks (blocks _ _ _ p))) <= function_size p.
Proof.
  rewrite present_flat_length. eapply Nat.le_trans; [|apply prep_kept_units].
  apply present_weight_mono. intros item Hin. rewrite prep_homes_length.
  pose proof (prep_block_defs_units (snd item)); lia.
Qed.

Lemma prep_defs_flat_total {K G} (p : func positive K G) :
  (Code.List.T_flat_map (fun item => block_defs (snd item))
    (fun item => 1 + (Datatypes.T_snd item + T_block_defs (snd item)))%N
    (first_blocks (blocks _ _ _ p)) <= 18 * prep_total p)%N.
Proof.
  apply (prep_weight_cost p _ 16%N
    (present_weight (fun item => prep_body_units (snd item))
      (first_blocks (blocks _ _ _ p)))); [|apply prep_kept_units].
  apply prep_flat_weight; [intros; unfold prep_body_units; lia|].
  intros item Hin. pose proof (prep_block_defs_clock (snd item)) as Hdefs.
  pose proof (prep_block_defs_units (snd item)) as Hunits.
  pose proof (prep_units_inflation p (prep_body_units (snd item))) as Hpaid.
  rewrite prep_block_defs_length in Hunits |- *. time_simpl.
  rewrite !Nat2N.inj_add in *. nia.
Qed.

Lemma prep_values_flat_total {K G} (p : func positive K G) :
  (Code.List.T_flat_map block_value_defs (fun item => T_block_value_defs item)
    (first_blocks (blocks _ _ _ p)) <= 22 * prep_total p)%N.
Proof.
  apply (prep_weight_cost p _ 20%N
    (present_weight (fun item => prep_body_units (snd item))
      (first_blocks (blocks _ _ _ p)))); [|apply prep_kept_units].
  apply prep_flat_weight; [intros; unfold prep_body_units; lia|].
  intros item Hin. pose proof (prep_block_values_clock item) as Hvalues.
  pose proof (prep_block_defs_units (snd item)) as Hunits.
  pose proof (prep_units_inflation p (prep_body_units (snd item))) as Hpaid.
  rewrite prep_value_defs_length. nia.
Qed.

Lemma prep_homes_flat_total {K G} (p : func positive K G) :
  (Code.List.T_flat_map block_homes (fun item => T_block_homes item)
    (first_blocks (blocks _ _ _ p)) <= 22 * prep_total p)%N.
Proof.
  apply (prep_weight_cost p _ 20%N
    (present_weight (fun item => prep_body_units (snd item))
      (first_blocks (blocks _ _ _ p)))); [|apply prep_kept_units].
  apply prep_flat_weight; [intros; unfold prep_body_units; lia|].
  intros item Hin. pose proof (prep_block_homes_clock item) as Hhomes.
  pose proof (prep_block_defs_units (snd item)) as Hunits.
  pose proof (prep_units_inflation p (prep_body_units (snd item))) as Hpaid.
  rewrite prep_homes_length. nia.
Qed.

Lemma prep_values_flat_key {K G} (p : func positive K G) row :
  In row (flat_map block_value_defs (first_blocks (blocks _ _ _ p))) ->
  prep_key_bounded p (fst row).
Proof.
  intro Hin. apply in_flat_map in Hin as [item [Hitem Hrow]].
  apply (prep_kept_var_key p item (fst row) Hitem). apply prep_block_defs_vars.
  rewrite <- prep_value_defs_keys. now apply in_map.
Qed.

Lemma prep_homes_flat_key {K G} (p : func positive K G) row :
  In row (flat_map block_homes (first_blocks (blocks _ _ _ p))) ->
  prep_key_bounded p (fst row).
Proof.
  intro Hin. apply in_flat_map in Hin as [item [Hitem Hrow]].
  apply (prep_kept_var_key p item (fst row) Hitem). apply prep_block_defs_vars.
  rewrite <- prep_homes_keys. now apply in_map.
Qed.

(** * Preparation definition row clocks *)

Lemma prep_guard_rows_length {A K G} (kept : ptrie A)
    (bs : list (positive * block positive K G)) :
  length (flat_map (fun item => listed_guards kept (fst item) (term _ _ _ (snd item))) bs) <=
    2 * length bs.
Proof.
  induction bs as [|item rest IH]; [reflexivity|].
  cbn [flat_map length]. rewrite length_app.
  pose proof (prep_listed_guards_length kept (fst item) (term _ _ _ (snd item))); lia.
Qed.

Lemma prep_guard_rows_keys {A K G} (kept : ptrie A)
    (bs : list (positive * block positive K G)) :
  map fst (flat_map (fun item => listed_guards kept (fst item) (term _ _ _ (snd item))) bs) =
  map fst (flat_map (fun item => listed_edge_args kept (fst item) (term _ _ _ (snd item))) bs).
Proof.
  induction bs as [|item rest IH]; [reflexivity|].
  cbn [flat_map]. rewrite !map_app, prep_guard_edge_keys, IH. reflexivity.
Qed.

Lemma prep_owner_rows_length (ss : list block_summary) :
  length (flat_map (fun s => map (fun n => (n, summary_block s)) (summary_points s)) ss) =
    length (flat_map summary_points ss).
Proof.
  induction ss as [|s rest IH]; [reflexivity|].
  cbn [flat_map]. rewrite !length_app, length_map, IH. reflexivity.
Qed.

Lemma prep_owner_rows_point (ss : list block_summary) n b :
  In (n, b) (flat_map (fun s => map (fun m => (m, summary_block s)) (summary_points s)) ss) ->
  In n (flat_map summary_points ss).
Proof.
  intro Hin. apply in_flat_map in Hin as [s [Hs Hin]].
  apply in_map_iff in Hin as [m [Heq Hm]]. inversion Heq; subst.
  apply in_flat_map. exists s; now split.
Qed.

Lemma prep_projection_rows_length (rows : list point_row) :
  length (flat_map (fun r => match point_block_edge (fst (fst r)) with
    | Some be => [(fst (fst r), be)] | None => [] end) rows) <= length rows.
Proof.
  rewrite present_flat_length, <- (prep_weight_one rows). apply present_weight_mono.
  intros row Hin. destruct (point_block_edge (fst (fst row))); cbn [length]; lia.
Qed.

Lemma prep_projection_rows_edge (rows : list point_row) edge be :
  In (edge, be) (flat_map (fun r => match point_block_edge (fst (fst r)) with
    | Some owner => [(fst (fst r), owner)] | None => [] end) rows) ->
  In edge (map (fun r => fst (fst r)) rows).
Proof.
  intro Hin. apply in_flat_map in Hin as [row [Hrow Hin]].
  destruct (point_block_edge (fst (fst row))); [|contradiction].
  destruct Hin as [Heq|[]]. inversion Heq; subst.
  apply in_map_iff. exists row; now split.
Qed.

Lemma prep_point_defs_length (rows : list point_row) :
  length (flat_map (fun r => map (fun x => (x, point_src (fst (fst r)))) (snd r)) rows) =
    present_weight (fun r => length (snd r)) rows.
Proof.
  rewrite present_flat_length. apply Nat.le_antisymm; apply present_weight_mono;
    intros row Hin; rewrite length_map; reflexivity.
Qed.

Lemma prep_point_defs_count (rows : list point_row) :
  length (flat_map (fun r => map (fun x => (x, point_src (fst (fst r)))) (snd r)) rows) <=
    present_weight present_row_vars rows.
Proof.
  rewrite prep_point_defs_length. apply present_weight_mono.
  intros row Hin. unfold present_row_vars; lia.
Qed.

Lemma prep_pair_row_budget {K G A} (p : func positive K G) (table : ptrie (list A))
    target (args : list positive) :
  prep_key_bounded p target ->
  (T_index_row table target <= 2 * prep_atom p * N.of_nat (length args + 1))%N.
Proof.
  intro Htarget. eapply N.le_trans; [exact (prep_row_clock p target table Htarget)|].
  rewrite <- (N.mul_1_r (2 * prep_atom p)) at 1. apply N.mul_le_mono_l; lia.
Qed.

Lemma prep_entry_params_total {K G} (p : func positive K G) :
  let kept := first_table PosKeyCode.encode
    (map (fun item => (fst item, params _ _ _ (snd item)))
      (first_blocks (blocks _ _ _ p))) in
  (Code.List.T_flat_map (index_row kept) (fun b => T_index_row kept b)
    (if is_listed kept (entry _ _ _ p) then [entry _ _ _ p] else []) <=
    8 * prep_total p)%N.
Proof.
  cbn zeta. set (kept := first_table PosKeyCode.encode
    (map (fun item => (fst item, params _ _ _ (snd item)))
      (first_blocks (blocks _ _ _ p)))).
  pose proof (prep_row_clock p (entry _ _ _ p) kept (prep_entry_key p)) as Hrow.
  pose proof (prep_params_row_length p (entry _ _ _ p)) as Hlength. fold kept in Hlength.
  pose proof (prep_atom_total p) as Hatom. pose proof (prep_total_positive p) as Htotal.
  pose proof (prep_units_inflation p (function_size p + 1)) as Hsize.
  fold (prep_total p) in Hsize.
  pose proof (Datatypes.T_app_le (index_row kept (entry _ _ _ p)) []) as Happend.
  destruct (is_listed kept (entry _ _ _ p)).
  - change (1 + (T_index_row kept (entry _ _ _ p) + 1 +
      Datatypes.T_app (index_row kept (entry _ _ _ p)) []) <= 8 * prep_total p)%N.
    lia.
  - change (1 <= 8 * prep_total p)%N. lia.
Qed.

(** * Preparation nested row clocks *)

Lemma prep_summary_rows_total {K G} (p : func positive K G) ss :
  length ss <= function_size p ->
  length (flat_map (fun s => summary_internal s ++ summary_outgoing s) ss) <=
    5 * function_size p ->
  (Code.List.T_flat_map (fun s => summary_internal s ++ summary_outgoing s)
    (fun s => 1 + (T_summary_internal s + T_summary_outgoing s +
      Datatypes.T_app (summary_internal s) (summary_outgoing s)))%N ss <=
    70 * prep_total p)%N.
Proof.
  intros Hss Hrows.
  apply (prep_flat_total p _ _
    (fun s => 1 + length (summary_internal s ++ summary_outgoing s)) ss 8%N 6).
  - intros; lia.
  - intros s Hin.
    pose proof (Datatypes.T_app_le (summary_internal s) (summary_outgoing s)) as Happ.
    pose proof (prep_units_inflation p
      (1 + length (summary_internal s ++ summary_outgoing s))) as Hpaid.
    rewrite length_app in *. time_simpl. rewrite !Nat2N.inj_add in *. nia.
  - rewrite present_weight_plus, prep_weight_one, <- present_flat_length. lia.
Qed.

Lemma prep_summary_points_total {K G} (p : func positive K G) ss :
  length ss <= function_size p ->
  length (flat_map summary_points ss) <= 5 * function_size p ->
  (Code.List.T_flat_map summary_points (fun s => T_summary_points s) ss <=
    28 * prep_total p)%N.
Proof.
  intros Hss Hpoints.
  apply (prep_flat_total p _ _ (fun s => 1 + length (summary_points s)) ss 2%N 6).
  - intros; lia.
  - intros s Hin.
    pose proof (prep_units_inflation p (1 + length (summary_points s))) as Hpaid.
    time_simpl. rewrite !Nat2N.inj_add in *. nia.
  - rewrite prep_summary_points_charge. lia.
Qed.

Lemma prep_internal_map_total {K G} (p : func positive K G) ss :
  length ss <= function_size p ->
  length (flat_map (fun s => summary_internal s ++ summary_outgoing s) ss) <=
    5 * function_size p ->
  (ListDef.T_map
    (fun s => (summary_block s, map (fun r => fst (fst r)) (summary_internal s)))
    (fun s => 1 + (T_summary_block s + (T_summary_internal s +
      ListDef.T_map (fun r : point_row => fst (fst r))
        (fun r => 1 + (Datatypes.T_fst r + Datatypes.T_fst (fst r)))
        (summary_internal s))))%N ss <= 70 * prep_total p)%N.
Proof.
  intros Hss Hrows.
  apply (prep_map_weight_total p _ _ (fun s => 1 + length (summary_internal s))
    ss 8%N 6).
  - intros; lia.
  - intros s Hin.
    pose proof (prep_map_uniform (fun r : point_row => fst (fst r))
      (fun r => 1 + (Datatypes.T_fst r + Datatypes.T_fst (fst r)))%N
      (summary_internal s) 3%N ltac:(intros; time_simpl; lia)) as Hmap.
    pose proof (prep_units_inflation p (1 + length (summary_internal s))) as Hpaid.
    revert Hmap; time_simpl; intro Hmap. rewrite !Nat2N.inj_add in *. nia.
  - pose proof (prep_summary_internal_charge ss). lia.
Qed.

Lemma prep_owner_flat_total {K G} (p : func positive K G) ss :
  length ss <= function_size p ->
  length (flat_map summary_points ss) <= 5 * function_size p ->
  (Code.List.T_flat_map
    (fun s => map (fun n => (n, summary_block s)) (summary_points s))
    (fun s => 1 + (T_summary_points s +
      ListDef.T_map (fun n => (n, summary_block s))
        (fun _ => 1 + T_summary_block s) (summary_points s)))%N ss <=
    70 * prep_total p)%N.
Proof.
  intros Hss Hpoints.
  apply (prep_flat_total p _ _ (fun s => 1 + length (summary_points s)) ss 8%N 6).
  - intros; lia.
  - intros s Hin.
    pose proof (prep_map_uniform (fun n => (n, summary_block s))
      (fun _ => 1 + T_summary_block s)%N (summary_points s) 2%N
      ltac:(intros; time_simpl; lia)) as Hmap.
    pose proof (prep_units_inflation p (1 + length (summary_points s))) as Hpaid.
    rewrite length_map. revert Hmap; time_simpl; intro Hmap.
    rewrite !Nat2N.inj_add in *. nia.
  - rewrite prep_summary_points_charge. lia.
Qed.

Lemma prep_projection_flat_total {K G} (p : func positive K G) rows :
  length rows <= 5 * function_size p ->
  (Code.List.T_flat_map
    (fun r : point_row => match point_block_edge (fst (fst r)) with
      | Some be => [(fst (fst r), be)] | None => [] end)
    (fun r => 1 + (Datatypes.T_fst r + Datatypes.T_fst (fst r) +
      T_point_block_edge (fst (fst r)) +
      match point_block_edge (fst (fst r)) with
      | Some _ => Datatypes.T_fst r + Datatypes.T_fst (fst r) | None => 0 end))%N
    rows <= 60 * prep_total p)%N.
Proof.
  intro Hrows.
  apply (prep_flat_total p _ _ (fun _ => 1) rows 8%N 5).
  - intros; lia.
  - intros row Hin. pose proof (prep_atom_positive p) as Hatom.
    time_simpl. destruct (point_block_edge (fst (fst row))); cbn [length]; nia.
  - now rewrite prep_weight_one.
Qed.

Lemma prep_point_defs_flat_total {K G} (p : func positive K G) rows :
  length rows <= 5 * function_size p ->
  present_weight present_row_vars rows <= 2 * function_size p ->
  (Code.List.T_flat_map
    (fun r : point_row => map (fun x => (x, point_src (fst (fst r)))) (snd r))
    (fun r => 1 + (Datatypes.T_snd r +
      ListDef.T_map (fun x => (x, point_src (fst (fst r))))
        (fun _ => 1 + (Datatypes.T_fst r + Datatypes.T_fst (fst r) +
          T_point_src (fst (fst r)))) (snd r)))%N rows <=
    80 * prep_total p)%N.
Proof.
  intros Hrows Hvars.
  apply (prep_flat_total p _ _ (fun r => 1 + length (snd r)) rows 8%N 7).
  - intros; lia.
  - intros row Hin.
    pose proof (prep_map_uniform (fun x => (x, point_src (fst (fst row))))
      (fun _ => 1 + (Datatypes.T_fst row + Datatypes.T_fst (fst row) +
        T_point_src (fst (fst row))))%N (snd row) 4%N
      ltac:(intros; time_simpl; lia)) as Hmap.
    pose proof (prep_units_inflation p (1 + length (snd row))) as Hpaid.
    rewrite length_map. revert Hmap; time_simpl; intro Hmap.
    rewrite !Nat2N.inj_add in *. nia.
  - pose proof (prep_row_defs_charge rows). lia.
Qed.

Lemma prep_phi_map_total {K G} (p : func positive K G) (kept : ptrie (list positive)) rows :
  length rows <= 2 * function_size p ->
  present_weight (fun row => length (snd row)) rows <= function_size p ->
  (forall row, In row rows -> prep_key_bounded p (edge_target (fst row))) ->
  (ListDef.T_map
    (fun r => (fst r, pair_args (index_row kept (edge_target (fst r))) (snd r)))
    (fun r => 1 + (Datatypes.T_fst r + (Datatypes.T_fst r + T_edge_target (fst r) +
      T_index_row kept (edge_target (fst r)) + Datatypes.T_snd r +
      T_pair_args (index_row kept (edge_target (fst r))) (snd r))))%N rows <=
    56 * prep_total p)%N.
Proof.
  intros Hrows Hargs Hkeys.
  apply (prep_map_weight_total p _ _ (fun r => 1 + length (snd r)) rows 12%N 3).
  - intros; lia.
  - intros row Hin.
    pose proof (prep_row_clock p (edge_target (fst row)) kept (Hkeys row Hin)) as Hrow.
    pose proof (prep_pair_args_clock (index_row kept (edge_target (fst row))) (snd row)) as Hpair.
    pose proof (prep_units_inflation p (1 + length (snd row))) as Hpaid.
    pose proof (prep_atom_positive p) as Hatom.
    time_simpl. rewrite !Nat2N.inj_add in *. nia.
  - rewrite present_weight_plus, prep_weight_one. lia.
Qed.

Lemma prep_phi_flat_total {K G} (p : func positive K G) (kept : ptrie (list positive)) rows :
  length rows <= 2 * function_size p ->
  present_weight (fun row => length (snd row)) rows <= function_size p ->
  (forall row, In row rows -> prep_key_bounded p (edge_target (fst row))) ->
  (Code.List.T_flat_map
    (fun r => map (pair (fst r))
      (pair_args (index_row kept (edge_target (fst r))) (snd r)))
    (fun r => 1 + (Datatypes.T_fst r + (Datatypes.T_fst r + T_edge_target (fst r) +
      T_index_row kept (edge_target (fst r)) + Datatypes.T_snd r +
      T_pair_args (index_row kept (edge_target (fst r))) (snd r)) +
      ListDef.T_map (pair (fst r)) (fun _ => 1)
        (pair_args (index_row kept (edge_target (fst r))) (snd r))))%N rows <=
    72 * prep_total p)%N.
Proof.
  intros Hrows Hargs Hkeys.
  apply (prep_flat_total p _ _ (fun r => 1 + length (snd r)) rows 16%N 3).
  - intros; lia.
  - intros row Hin.
    pose proof (prep_row_clock p (edge_target (fst row)) kept (Hkeys row Hin)) as Hrow.
    pose proof (prep_pair_args_clock (index_row kept (edge_target (fst row))) (snd row)) as Hpair.
    pose proof (prep_pair_args_length
      (index_row kept (edge_target (fst row))) (snd row)) as Hlength.
    pose proof (prep_map_uniform (pair (fst row)) (fun _ => 1%N)
      (pair_args (index_row kept (edge_target (fst row))) (snd row)) 1%N
      ltac:(intros; apply N.le_refl)) as Hmap.
    pose proof (prep_units_inflation p (1 + length (snd row))) as Hpaid.
    pose proof (prep_atom_positive p) as Hatom.
    rewrite length_map. time_simpl. rewrite !Nat2N.inj_add in *. nia.
  - rewrite present_weight_plus, prep_weight_one. lia.
Qed.

(** * Preparation table key bounds *)

Lemma prep_block_edge_sides {K G} (p : func positive K G) edge :
  In edge (lang_edges (lang_prepare p)) ->
  prep_key_bounded p (edge_source edge) /\ prep_key_bounded p (edge_target edge).
Proof.
  intro Hin. destruct (lang_edges_shape p edge Hin) as [body [Hsource [Htarget _]]].
  apply prep_kept_original in Hsource. split.
  - now apply (prep_block_key p (edge_source edge) body).
  - apply prep_id_key. now apply (target_in_function p (edge_source edge) body).
Qed.

Lemma prep_summary_block_key {K G A} (p : func positive K G) (kept : ptrie A) s :
  In s (map (summarize kept) (first_blocks (blocks _ _ _ p))) ->
  prep_key_bounded p (summary_block s).
Proof.
  intro Hin. apply in_map_iff in Hin as [item [Heq Hitem]]. subst s.
  change (prep_key_bounded p (fst item)). now apply prep_kept_key.
Qed.

Lemma prep_summary_exit_in {K G} (p : func positive K G) s :
  In s (map (summarize (first_table PosKeyCode.encode
    (map (fun item => (fst item, params _ _ _ (snd item)))
      (first_blocks (blocks _ _ _ p))))) (first_blocks (blocks _ _ _ p))) ->
  In (summary_exit s) (lang_points (lang_prepare p)).
Proof.
  intro Hin. apply in_map_iff in Hin as [item [Heq Hitem]]. subst s.
  eapply lang_summary_points; [exact Hitem|apply summarize_exit_listed].
Qed.

Lemma prep_raw_point_var_key {K G} (p : func positive K G) row x :
  In row (flat_map (fun s => summary_internal s ++ summary_outgoing s)
    (map (summarize (first_table PosKeyCode.encode
      (map (fun item => (fst item, params _ _ _ (snd item)))
        (first_blocks (blocks _ _ _ p))))) (first_blocks (blocks _ _ _ p)))) ->
  In x (snd row) -> prep_key_bounded p x.
Proof.
  intros Hrow Hx. apply in_flat_map in Hrow as [s [Hs Hrow]].
  apply in_map_iff in Hs as [item [Heq Hitem]]. subst s.
  eapply prep_kept_var_key; [exact Hitem|].
  eapply summary_vars_in; [exact Hrow|]. apply in_or_app; now right.
Qed.

Lemma prep_first_total {K G A B} (p : func positive K G) (key : A -> positive)
    Tkey (rows : list (A * B)) :
  (forall row, In row rows -> (Tkey (fst row) <= prep_atom p)%N) ->
  (forall row, In row rows -> prep_key_bounded p (key (fst row))) ->
  length rows <= 7 * function_size p ->
  (T_first_table key Tkey rows <= 256 * prep_total p)%N.
Proof.
  intros Hclock Hwidth Hcount.
  pose proof (prep_first_clock p key Tkey rows Hclock Hwidth) as Htime.
  pose proof (prep_count_cost p _ 8%N (length rows) 7 Htime Hcount) as Htotal.
  lia.
Qed.

Lemma prep_multi_total {K G A} (p : func positive K G) (key : A -> positive)
    Tkey (rows : list A) :
  (forall row, In row rows -> (Tkey row <= 4 * prep_atom p)%N) ->
  (forall row, In row rows -> prep_key_bounded p (key row)) ->
  length rows <= 7 * function_size p ->
  (T_multi_table key Tkey rows <= 256 * prep_total p)%N.
Proof.
  intros Hclock Hwidth Hcount.
  pose proof (prep_multi_clock p key Tkey rows Hclock Hwidth) as Htime.
  exact (prep_count_cost p _ 32%N (length rows) 7 Htime Hcount).
Qed.

Lemma prep_positive_total {K G A} (p : func positive K G) (rows : list (positive * A)) :
  (forall row, In row rows -> prep_key_bounded p (fst row)) ->
  length rows <= 7 * function_size p ->
  (T_first_table PosKeyCode.encode (fun x => PosKeyT.T_encode x) rows <=
    256 * prep_total p)%N.
Proof.
  intros Hkeys Hcount. apply prep_first_total; [|exact Hkeys|exact Hcount].
  intros; time_simpl; apply prep_atom_positive.
Qed.

Lemma prep_point_total {K G A} (p : func positive K G) (rows : list (point_key * A)) :
  (forall row, In row rows -> In (fst row) (lang_points (lang_prepare p))) ->
  length rows <= 7 * function_size p ->
  (T_first_table PointKey.encode (fun x => PointKey.T_encode x) rows <=
    256 * prep_total p)%N.
Proof.
  intros Hkeys Hcount. apply prep_first_total; [| |exact Hcount].
  - intros; apply prep_point_encode; now apply Hkeys.
  - intros; apply prep_point_key; now apply Hkeys.
Qed.

Lemma prep_point_edge_total {K G A} (p : func positive K G) (rows : list (point_edge * A)) :
  (forall row, In row rows -> In (fst row) (lang_point_edges (lang_prepare p))) ->
  length rows <= 7 * function_size p ->
  (T_first_table PointEdge.encode (fun x => PointEdge.T_encode x) rows <=
    256 * prep_total p)%N.
Proof.
  intros Hkeys Hcount. apply prep_first_total; [| |exact Hcount].
  - intros; apply prep_point_edge_encode; now apply Hkeys.
  - intros; apply prep_point_edge_key; now apply Hkeys.
Qed.

Lemma prep_block_edge_total {K G A} (p : func positive K G) (rows : list (block_edge * A)) :
  (forall row, In row rows -> In (fst row) (lang_edges (lang_prepare p))) ->
  length rows <= 7 * function_size p ->
  (T_first_table BlockEdge.encode (fun x => BlockEdge.T_encode x) rows <=
    256 * prep_total p)%N.
Proof.
  intros Hkeys Hcount. apply prep_first_total; [| |exact Hcount].
  - intros; apply prep_block_edge_encode; now apply Hkeys.
  - intros; apply prep_block_edge_key; now apply Hkeys.
Qed.

(** * Preparation pipeline clock *)

(** Replace one derived subclock by its established common pipeline budget. *)
Local Ltac prep_clock_bound p term solver :=
  let clock := fresh "clock" in let Hclock := fresh "Hclock" in
  set (clock := term);
  assert (Hclock : (clock <= 256 * prep_total p)%N) by (unfold clock; solver);
  clearbody clock.

(** Compose the stored row counts without unfolding their locally named lists. *)
Local Ltac prep_count_bound :=
  repeat first [rewrite length_map | rewrite length_app | rewrite prep_owner_rows_length];
  first [assumption | lia |
    eapply Nat.le_trans; [eassumption |
      first [lia | eapply Nat.le_trans; [eassumption | lia]]]].

(** All prepared tables share a linear syntax-and-key budget, including malformed inputs. *)
Lemma prep_lang_prepare_bound {K G} (p : func positive K G) :
  (T_lang_prepare p <= 16384 * prep_total p)%N.
Proof.
  set (bs := first_blocks (blocks _ _ _ p)).
  set (kept := first_table PosKeyCode.encode
    (map (fun item => (fst item, params _ _ _ (snd item))) bs)).
  set (ss := map (summarize kept) bs).
  set (block_rows := flat_map (fun item =>
    listed_edge_args kept (fst item) (term _ _ _ (snd item))) bs).
  set (edges := map fst block_rows).
  set (rows := flat_map (fun s => summary_internal s ++ summary_outgoing s) ss).
  set (pedges := map (fun r => fst (fst r)) rows).
  set (entries := if is_listed kept (entry _ _ _ p) then [entry _ _ _ p] else []).
  pose proof (prep_pipeline_counts p) as Hcounts.
  change (length bs <= function_size p /\ length ss <= function_size p /\
    length block_rows <= 2 * function_size p /\ length rows <= 5 * function_size p /\
    length (flat_map summary_points ss) <= 5 * function_size p /\
    present_weight present_row_vars rows <= 2 * function_size p /\
    present_weight (fun s => length (summary_returns s)) ss <= 2 * function_size p /\
    present_weight (fun row => length (snd row)) block_rows <= function_size p) in Hcounts.
  destruct Hcounts as [Hbs [Hss [Hbr [Hrows [Hpoints [Hvars [Hreturns Hargs]]]]]]].
  assert (Hedges : length edges <= 2 * function_size p)
    by (unfold edges; rewrite length_map; exact Hbr).
  assert (Hpedges : length pedges <= 5 * function_size p)
    by (unfold pedges; rewrite length_map; exact Hrows).
  pose proof (prep_atom_positive p) as Hatom.
  pose proof (prep_total_positive p) as Htotal.
  pose proof (prep_atom_total p) as Hatomtotal.
  pose proof (prep_input_length p) as Hinputs.
  pose proof (prep_values_flat_length p) as Hvalues; fold bs in Hvalues.
  pose proof (prep_homes_flat_length p) as Hhomes; fold bs in Hhomes.
  pose proof (prep_guard_rows_length kept bs) as Hguards.
  pose proof (prep_projection_rows_length rows) as Hprojection.
  pose proof (prep_point_defs_count rows) as Hpointdefs.
  assert (Hblockrow : forall row, In row block_rows ->
    In (fst row) (lang_edges (lang_prepare p))).
  { intros row Hin. change (In (fst row) (map fst block_rows)). now apply in_map. }
  assert (Hedge : forall edge, In edge edges ->
    prep_key_bounded p (edge_source edge) /\ prep_key_bounded p (edge_target edge)).
  { intros edge Hin. apply prep_block_edge_sides. exact Hin. }
  assert (Htarget : forall row, In row block_rows -> prep_key_bounded p (edge_target (fst row))).
  { intros row Hin. exact (proj2 (prep_block_edge_sides p (fst row) (Hblockrow row Hin))). }
  assert (Hrow : forall row, In row rows -> In (fst (fst row)) (lang_point_edges (lang_prepare p))).
  { intros row Hin. change (In (fst (fst row)) (map (fun r => fst (fst r)) rows)).
    apply in_map_iff. exists row; now split. }
  assert (Hsummary : forall s, In s ss -> prep_key_bounded p (summary_block s)).
  { intros s Hin. apply (prep_summary_block_key p kept s). exact Hin. }
  assert (Hexit : forall s, In s ss -> In (summary_exit s) (lang_points (lang_prepare p))).
  { intros s Hin. now apply prep_summary_exit_in. }
  assert (Hkept : forall item, In item bs -> prep_key_bounded p (fst item)).
  { intros item Hin. now apply prep_kept_key. }
  assert (Hvaluekeys : forall row, In row (flat_map block_value_defs bs) ->
    prep_key_bounded p (fst row)).
  { intros row Hin. now apply prep_values_flat_key. }
  assert (Hhomekeys : forall row,
    In row (map (fun x => (x, entry _ _ _ p)) (inputs _ _ _ p) ++ flat_map block_homes bs) ->
    prep_key_bounded p (fst row)).
  { intros row Hin. apply in_app_or in Hin as [Hin|Hin].
    - apply in_map_iff in Hin as [x [<- Hx]]. cbn [fst]. apply prep_var_key.
      unfold function_vars. apply in_or_app; now left.
    - now apply prep_homes_flat_key. }
  assert (Hguardkeys : forall row,
    In row (flat_map (fun item => listed_guards kept (fst item) (term _ _ _ (snd item))) bs) ->
    In (fst row) (lang_edges (lang_prepare p))).
  { intros row Hin. change (In (fst row) (map fst block_rows)). unfold block_rows.
    rewrite <- prep_guard_rows_keys. now apply in_map. }
  assert (Hownerkeys : forall row,
    In row (flat_map (fun s => map (fun n => (n, summary_block s)) (summary_points s)) ss) ->
    In (fst row) (lang_points (lang_prepare p))).
  { intros [n b] Hin. change (In n (flat_map summary_points ss)).
    now apply (prep_owner_rows_point ss n b). }
  assert (Hprojectionkeys : forall row,
    In row (flat_map (fun r => match point_block_edge (fst (fst r)) with
      | Some be => [(fst (fst r), be)] | None => [] end) rows) ->
    In (fst row) (lang_point_edges (lang_prepare p))).
  { intros [edge be] Hin. change (In edge (map (fun r => fst (fst r)) rows)).
    now apply (prep_projection_rows_edge rows edge be). }
  assert (Hpointdefkeys : forall out,
    In out (flat_map (fun r => map (fun x => (x, point_src (fst (fst r)))) (snd r)) rows) ->
    prep_key_bounded p (fst out)).
  { intros out Hin. apply in_flat_map in Hin as [row [Hrowin Hin]].
    apply in_map_iff in Hin as [x [<- Hx]]. cbn [fst].
    eapply prep_raw_point_var_key; [exact Hrowin|exact Hx]. }
  assert (Hpends : forall edge, In edge pedges ->
    In (point_src edge) (lang_points (lang_prepare p)) /\
    In (point_dst edge) (lang_points (lang_prepare p))).
  { intros edge Hin. now apply lang_point_edges_nodes. }
  time_unfold @T_lang_prepare. cbn beta zeta.
  fold bs kept ss block_rows edges rows pedges entries.
  repeat lazymatch goal with
  | |- context [T_first_table ?key ?Tkey ?rs] =>
    prep_clock_bound p (T_first_table key Tkey rs)
      ltac:(first
        [ apply prep_positive_total
        | apply prep_point_total
        | apply prep_point_edge_total
        | apply prep_block_edge_total ];
        [ intros out Hin;
          try solve [eauto];
          apply in_map_iff in Hin as [source [<- Hin]];
          cbn [fst snd]; eauto
        | prep_count_bound ])
  end.
  repeat lazymatch goal with
  | |- context [T_multi_table ?key ?Tkey ?rs] =>
    prep_clock_bound p (T_multi_table key Tkey rs)
      ltac:(apply prep_multi_total;
        [ intros edge Hin; first
          [ time_simpl; lia
          | let H := fresh in
            assert (H : (PointKey.T_encode (point_src edge) <= prep_atom p)%N)
              by (apply prep_point_encode; exact (proj1 (Hpends edge Hin)));
            time_simpl; lia
          | let H := fresh in
            assert (H : (PointKey.T_encode (point_dst edge) <= prep_atom p)%N)
              by (apply prep_point_encode; exact (proj2 (Hpends edge Hin)));
            time_simpl; lia ]
        | intros edge Hin; first
          [ exact (proj1 (Hedge edge Hin)) | exact (proj2 (Hedge edge Hin))
          | apply prep_point_key; exact (proj1 (Hpends edge Hin))
          | apply prep_point_key; exact (proj2 (Hpends edge Hin)) ]
        | prep_count_bound ])
  end.
  repeat lazymatch goal with
  | |- context [Code.List.T_flat_map ?f ?Tf ?xs] =>
    prep_clock_bound p (Code.List.T_flat_map f Tf xs)
      ltac:(first
        [ solve [eapply N.le_trans; [apply (prep_block_rows_total p) | lia]]
        | solve [eapply N.le_trans; [apply (prep_summary_rows_total p); eassumption | lia]]
        | solve [eapply N.le_trans; [apply (prep_summary_points_total p); eassumption | lia]]
        | solve [eapply N.le_trans; [apply (prep_defs_flat_total p) | lia]]
        | solve [eapply N.le_trans; [apply (prep_entry_params_total p) | lia]]
        | solve [eapply N.le_trans; [apply (prep_phi_flat_total p); eassumption | lia]]
        | solve [eapply N.le_trans; [apply (prep_values_flat_total p) | lia]]
        | solve [eapply N.le_trans; [apply (prep_homes_flat_total p) | lia]]
        | solve [eapply N.le_trans; [apply (prep_guards_total p) | lia]]
        | solve [eapply N.le_trans; [apply (prep_owner_flat_total p); eassumption | lia]]
        | solve [eapply N.le_trans; [apply (prep_projection_flat_total p); eassumption | lia]]
        | solve [eapply N.le_trans; [apply (prep_point_defs_flat_total p); eassumption | lia]] ])
  end.
  repeat lazymatch goal with
  | |- context [ListDef.T_map ?f ?Tf ?xs] =>
    prep_clock_bound p (ListDef.T_map f Tf xs)
      ltac:(first
        [ solve [eapply N.le_trans; [apply (prep_summaries_total p) | lia]]
        | solve [eapply N.le_trans; [apply (prep_internal_map_total p); eassumption | lia]]
        | solve [eapply N.le_trans; [apply (prep_phi_map_total p); eassumption | lia]]
        | solve [eapply N.le_trans;
            [ eapply (prep_map_total p f Tf xs 8%N 7);
              [ intros; time_simpl; lia | prep_count_bound ] | lia ]] ])
  end.
  pose proof (prep_first_blocks_total p) as Hfirst. fold bs in Hfirst.
  pose proof (prep_listed_clock p (entry _ _ _ p) kept (prep_entry_key p)) as Hlisted.
  pose proof (Datatypes.T_app_le (inputs _ _ _ p)
    (flat_map (fun item => block_defs (snd item)) bs)) as Happdefs.
  pose proof (Datatypes.T_app_le
    (map (fun x => (x, entry _ _ _ p)) (inputs _ _ _ p))
    (flat_map block_homes bs)) as Happhomes.
  rewrite length_map in Happhomes.
  pose proof (prep_units_inflation p (function_size p + 1)) as Hsize.
  fold (prep_total p) in Hsize.
  cbv beta iota zeta delta [T_blocks T_entry T_inputs].
  destruct (is_listed kept (entry _ _ _ p)); try lia.
Qed.

Module PrepareT (O : OPS) (Q : TYPE with Definition t := lang_prepared O.K O.G)
    <: LANG_PREPARE_T O Q.
  Include PrepareCode O Q.
  TimeFun prepare.
  Definition c_prepare : N := (33554432 * prep_scale)%N.
  (** Preparation reads the complete source within the published linear bit-cost bound. *)
  Lemma T_prepare_le : forall p,
    (T_prepare p <= c_prepare * N.of_nat (function_size p + 1) *
      N.of_nat (function_width p + 1))%N.
  Proof.
    intro p. pose proof (prep_lang_prepare_bound p) as Hprepare.
    pose proof (prep_total_positive p) as Hpositive.
    replace (c_prepare * N.of_nat (function_size p + 1) *
      N.of_nat (function_width p + 1))%N with (32768 * prep_total p)%N
      by (unfold c_prepare, prep_total, prep_atom, prep_width; ring).
    time_unfold T_prepare. lia.
  Qed.
  (** The concrete preparation clock has the published asymptotic bound. *)
  Lemma prepare_complexity :
    T_prepare p ∈ 𝑂(N.of_nat ((function_size p + 1) * (function_width p + 1))) for p.
  Proof.
    unfold bigO. exists c_prepare. intros p Hdomain.
    pose proof (T_prepare_le p) as Htime. rewrite Nat2N.inj_mul.
    replace (c_prepare *
      (N.of_nat (function_size p + 1) * N.of_nat (function_width p + 1) + 1))%N with
      (c_prepare * N.of_nat (function_size p + 1) * N.of_nat (function_width p + 1) +
        c_prepare)%N by ring.
    lia.
  Qed.
End PrepareT.

(** Unique source definitions retain their order, owner, and exact prepared lookup. *)
Lemma pl_param_defs_keys {K} b i xs : map fst (@param_defs K b i xs) = xs.
Proof.
  revert i. induction xs as [|x rest IH]; intro i; cbn [param_defs map fst];
    [reflexivity|now rewrite IH].
Qed.

Lemma pl_block_value_keys {K G} (item : positive * block positive K G) :
  map fst (block_value_defs item) = block_defs (snd item).
Proof.
  unfold block_value_defs, block_defs. rewrite map_app, pl_param_defs_keys, map_map.
  reflexivity.
Qed.

Lemma pl_block_home_keys {K G} (item : positive * block positive K G) :
  map fst (block_homes item) = block_defs (snd item).
Proof.
  unfold block_homes. rewrite map_map. apply map_id.
Qed.
(** A source with distinct labels is retained without deleting any block. *)
Lemma pl_selected_identity {K G} (bs : list (positive * block positive K G)) seen :
  NoDup (map fst bs) ->
  (forall b, In b (map fst bs) -> trie_get b seen = None) ->
  selected_blocks seen bs = bs.
Proof.
  revert seen. induction bs as [|[b body] rest IH]; intros seen Hdistinct Hfresh;
    [reflexivity|].
  inversion Hdistinct as [|head tail Hnot Htail]; subst.
  cbn [selected_blocks fst]. rewrite Hfresh by now left. f_equal.
  apply IH; [exact Htail|]. intros x Hx.
  rewrite PTrie.get_set_other; [apply Hfresh; now right|].
  intro Heq; subst x; contradiction.
Qed.

Lemma pl_first_identity {K G} (bs : list (positive * block positive K G)) :
  NoDup (map fst bs) -> first_blocks bs = bs.
Proof.
  intro Hdistinct. rewrite first_blocks_selected. apply pl_selected_identity;
    [exact Hdistinct|]. intros b Hin; apply PTrie.get_empty.
Qed.

(** A table with distinct encoded keys returns exactly its listed row. *)
Lemma pl_first_lookup {A B} (key : A -> positive) rows a (value : B) :
  (forall x y, key x = key y -> x = y) -> NoDup (map key (map fst rows)) ->
  (trie_get (key a) (first_table key rows) = Some value <-> In (a, value) rows).
Proof.
  intros Hinj Hdistinct. rewrite map_map in Hdistinct. split.
  - intro Hget. destruct (present_first_table_get key rows (key a) value Hget)
      as [found [Hrow Hkey]].
    apply Hinj in Hkey. now subst found.
  - intro Hin. now apply present_table_lookup_unique.
Qed.

(** Parameter-definition rows preserve both the parameter position and the block label. *)
Lemma pl_param_rows {K} b start xs x d :
  In (x, d) (@param_defs K b start xs) <->
  exists i, nth_error xs i = Some x /\ d = Param b (start + i).
Proof.
  revert start. induction xs as [|a rest IH]; intro start.
  - cbn [param_defs]. split; [contradiction|]. intros [i [Hnth _]].
    destruct i; discriminate.
  - cbn [param_defs]. split.
    + intros [Heq|Hin].
      * inversion Heq; subst. exists 0; split; [reflexivity|]. now rewrite Nat.add_0_r.
      * apply IH in Hin as [i [Hnth Hd]]. exists (S i); split; [exact Hnth|].
        rewrite Hd. f_equal; lia.
    + intros [[|i] [Hnth Hd]].
      * cbn in Hnth. inversion Hnth; subst x. left. rewrite Hd, Nat.add_0_r. reflexivity.
      * right. apply IH. exists i; split; [exact Hnth|]. rewrite Hd. f_equal; lia.
Qed.

Lemma pl_value_rows {K G} (item : positive * block positive K G) x d :
  In (x, d) (block_value_defs item) <->
  (exists i, nth_error (params _ _ _ (snd item)) i = Some x /\ d = Param (fst item) i) \/
  (exists op args, In (x, op, args) (code _ _ _ (snd item)) /\ d = Op op args).
Proof.
  unfold block_value_defs. rewrite in_app_iff, pl_param_rows. cbn [Nat.add].
  split.
  - intros [Hparam|Hcode]; [now left|]. right.
    apply in_map_iff in Hcode as [[[dst op] args] [Heq Hin]].
    cbn [fst snd] in Heq. inversion Heq; subst. exists op, args; now split.
  - intros [Hparam|[op [args [Hin Hd]]]]; [now left|]. right.
    apply in_map_iff. exists (x, op, args). split; [now rewrite Hd|exact Hin].
Qed.

(** Every block definition appears once in the definition-table key list. *)
Lemma pl_values_keys {K G} (bs : list (positive * block positive K G)) :
  map fst (flat_map block_value_defs bs) = flat_map (fun item => block_defs (snd item)) bs.
Proof.
  induction bs as [|item rest IH]; [reflexivity|].
  cbn [flat_map]. rewrite map_app, pl_block_value_keys, IH. reflexivity.
Qed.

Lemma pl_homes_keys {K G} (bs : list (positive * block positive K G)) :
  map fst (flat_map block_homes bs) = flat_map (fun item => block_defs (snd item)) bs.
Proof.
  induction bs as [|item rest IH]; [reflexivity|].
  cbn [flat_map]. rewrite map_app, pl_block_home_keys, IH. reflexivity.
Qed.

Lemma pl_home_rows {K G} (bs : list (positive * block positive K G)) x b :
  In (x, b) (flat_map block_homes bs) <->
  exists body, In (b, body) bs /\ In x (block_defs body).
Proof.
  split.
  - intro Hin. apply in_flat_map in Hin as [[id body] [Hbody Hin]].
    unfold block_homes in Hin. apply in_map_iff in Hin as [y [Heq Hy]].
    cbn [fst snd] in Heq, Hy. inversion Heq; subst. exists body; now split.
  - intros [body [Hbody Hx]]. apply in_flat_map. exists (b, body); split; [exact Hbody|].
    unfold block_homes. apply in_map_iff. exists x; now split.
Qed.

(** The source inventory supplies a natural-number rank for every defined value. *)
Fixpoint pl_rank (xs : list positive) (x : positive) : nat :=
  match xs with [] => 0 | y :: rest => if Pos.eqb x y then 0 else S (pl_rank rest x) end.

Lemma pl_rank_nth xs x i : NoDup xs -> nth_error xs i = Some x -> pl_rank xs x = i.
Proof.
  revert i; induction xs as [|y rest IH]; intros [|i] Hunique Hnth; try discriminate.
  - cbn [nth_error] in Hnth; inversion Hnth; subst y.
    cbn [pl_rank]. now rewrite Pos.eqb_refl.
  - inversion Hunique as [|head tail Hfresh Htail]; subst.
    cbn [nth_error] in Hnth. cbn [pl_rank].
    assert (Hneq : Pos.eqb x y = false).
    { apply Pos.eqb_neq; intro Heq; subst x; apply Hfresh; now apply nth_error_In in Hnth. }
    rewrite Hneq. f_equal; now apply IH.
Qed.

Lemma pl_rank_segment whole pre xs post x i : NoDup whole -> whole = pre ++ xs ++ post ->
  nth_error xs i = Some x -> pl_rank whole x = length pre + i.
Proof.
  intros Hunique Hwhole Hnth. apply pl_rank_nth; [exact Hunique|].
  rewrite Hwhole, nth_error_app2 by lia.
  replace (length pre + i - length pre) with i by lia.
  rewrite nth_error_app1; [exact Hnth|]. apply nth_error_Some; rewrite Hnth; discriminate.
Qed.

Lemma pl_code_def_nth {K G} (body : block positive K G) i x op args :
  nth_error (code _ _ _ body) i = Some (x, op, args) ->
  nth_error (block_defs body) (length (params _ _ _ body) + i) = Some x.
Proof.
  intro Hnth; unfold block_defs. rewrite nth_error_app2 by lia.
  replace (length (params _ _ _ body) + i - length (params _ _ _ body)) with i by lia.
  rewrite nth_error_map, Hnth; reflexivity.
Qed.

Lemma pl_pair_args_fst xs ys : length xs = length ys -> map fst (pair_args xs ys) = xs.
Proof.
  revert ys; induction xs as [|x rest IH]; intros [|y tail] Hlength; try discriminate;
    [reflexivity|]. cbn [pair_args map fst]. f_equal; apply IH; cbn in Hlength; lia.
Qed.

Lemma pl_pair_args_second xs ys x y : In (x, y) (pair_args xs ys) -> In y ys.
Proof.
  revert ys; induction xs as [|a rest IH]; intros [|b tail] Hin; try contradiction.
  cbn [pair_args In] in Hin; destruct Hin as [Heq|Hin].
  - inversion Heq; now left.
  - right; now apply IH in Hin.
Qed.

Lemma pl_exit_arg_use {G} source (ending : exit positive G) be args x :
  In (be, args) (exit_edge_args source ending) -> In x args -> In x (exit_uses ending).
Proof.
  destruct ending as [target values|guard values yes yesargs no noargs|values];
    cbn [exit_edge_args exit_uses In].
  - intros [Heq|[]] Hx; inversion Heq; subst; exact Hx.
  - intros [Heq|[Heq|[]]] Hx; inversion Heq; subst;
      apply in_or_app; right; apply in_or_app; [now left|now right].
  - intros [] .
Qed.

Lemma pl_exit_guard_use {G} source (ending : exit positive G) be guards guard args x :
  In (be, guards) (exit_guards source ending) -> In (guard, args) guards -> In x args ->
    In x (exit_uses ending).
Proof.
  destruct ending as [target values|test values yes yesargs no noargs|values];
    cbn [exit_guards exit_uses In].
  - intros [Heq|[]] Hguard Hx; inversion Heq; subst; contradiction.
  - intros [Heq|[Heq|[]]] Hguard Hx; inversion Heq; subst.
    + destruct Hguard as [Hsame|[]]; inversion Hsame; subst.
      apply in_or_app; now left.
    + contradiction.
  - intros [] .
Qed.

Lemma pl_exit_guard_source {G} source (ending : exit positive G) be guards :
  In (be, guards) (exit_guards source ending) -> edge_source be = source.
Proof.
  destruct ending; cbn [exit_guards In].
  - intros [Heq|[]]; inversion Heq; reflexivity.
  - intros [Heq|[Heq|[]]]; inversion Heq; reflexivity.
  - intros [].
Qed.

Lemma pl_param_def_nth {K G} (body : block positive K G) i x :
  nth_error (params _ _ _ body) i = Some x -> nth_error (block_defs body) i = Some x.
Proof.
  intro Hnth; unfold block_defs; rewrite nth_error_app1; [exact Hnth|].
  apply nth_error_Some; rewrite Hnth; discriminate.
Qed.

Lemma pl_flat_map_ext_in {A B} (f g : A -> list B) xs :
  (forall x, In x xs -> f x = g x) -> flat_map f xs = flat_map g xs.
Proof.
  intro Hpoint; induction xs as [|x rest IH]; [reflexivity|].
  cbn [flat_map]; rewrite Hpoint by now left.
  f_equal; apply IH; intros y Hy; apply Hpoint; now right.
Qed.

Module PresentT (O : OPS)
    (K : KEY_T with Definition t := O.K) (G : KEY_T with Definition t := O.G).
  Module Q := Prepared O.
  Module R := PrepareT O Q.
  Module BC := BlockCfgT O Q.
  Module C := PointCfgT O Q.
  Module VD := PresentVarsData O Q.
  Module U := VarsT Q PointKey PointEdge C PosKeyT VD.
  Module SD := PresentSsaData O K G Q.
  Module S := SsaT Q PosKeyT BlockEdge BC PosKeyT K G SD.
  Module PD := PresentPointsData O Q.
  Module SP := SsaPointsT Q PosKeyT BlockEdge BC PointKey PointEdge C PosKeyT U PD.

  Module Link <: LANG_SSA_LINK O K G Q R BlockEdge BC S.
    Lemma entries_agree : forall p, In (entry _ _ _ p) (map fst (blocks _ _ _ p)) ->
      BC.entries (R.prepare p) = [entry _ _ _ p].
    Proof.
      intros p Hin.
      change ((if is_listed (first_table PosKeyCode.encode
        (map (fun item => (fst item, params _ _ _ (snd item)))
          (first_blocks (blocks _ _ _ p)))) (entry _ _ _ p)
        then [entry _ _ _ p] else []) = [entry _ _ _ p]).
      assert (Hlisted : is_listed (first_table PosKeyCode.encode
        (map (fun item => (fst item, params _ _ _ (snd item)))
          (first_blocks (blocks _ _ _ p)))) (entry _ _ _ p) = true).
      { apply block_table_listed. apply find_block_exists.
        rewrite first_blocks_find. now apply find_block_exists. }
      now rewrite Hlisted.
    Qed.
    Lemma nodes_agree : forall p,
      BC.nodes (R.prepare p) = map fst (first_blocks (blocks _ _ _ p)).
    Proof.
      reflexivity.
    Qed.
    (** Each presented edge targets an exit of a listed source block. *)
    Lemma edges_syntax : forall p e, In e (BC.edges (R.prepare p)) ->
      exists body, In (BC.src (R.prepare p) e, body) (blocks _ _ _ p) /\
        In (BC.dst (R.prepare p) e) (exit_targets (term _ _ _ body)).
    Proof.
      intros p e Hin. destruct (lang_edges_shape _ _ Hin) as [body [Hsource [Htarget _]]].
      exists body; split; [|exact Htarget].
      rewrite first_blocks_selected in Hsource.
      now apply selected_blocks_in in Hsource as [Hsource _].
    Qed.
    Lemma paths_agree : forall p a route b, NoDup (map fst (blocks _ _ _ p)) ->
      targets_listed p ->
      (presentation_path (BC.edges (R.prepare p)) (BC.src (R.prepare p))
        (BC.dst (R.prepare p)) a route b <-> Lang.path p a route b).
    Proof.
      intros p a route b Hdistinct Htargets; split; intro Hpath.
      - induction Hpath as [n|e rest target Hedge Hpath IH].
        + constructor.
        + destruct (edges_syntax p e Hedge) as [body [Hsource Htarget]].
          eapply path_next; [exact Hsource| |exact IH].
          now apply exit_targets_successor.
      - induction Hpath as [n|id body next rest target Hbody Hnext Hpath IH].
        + constructor.
        + destruct (lang_edges_successor p id body next Hdistinct Htargets Hbody Hnext)
            as [edge [Hedge [Hsrc Hdst]]].
          change (presentation_path (lang_edges (lang_prepare p)) edge_source edge_target
            id (id :: rest) target).
          rewrite <- Hsrc. econstructor; [exact Hedge|].
          rewrite Hdst. exact IH.
    Qed.
    Lemma params_agree : forall p b, S.params (R.prepare p) b =
      match find_block b (blocks _ _ _ p) with
      | Some body => Lang.params _ _ _ body
      | None => []
      end.
    Proof.
      intros p b. change (index_row (first_table PosKeyCode.encode
        (map (fun item => (fst item, params _ _ _ (snd item)))
          (first_blocks (blocks _ _ _ p)))) b =
        match find_block b (blocks _ _ _ p) with
        | Some body => Lang.params _ _ _ body
        | None => []
        end).
      unfold index_row. rewrite block_table_get, first_blocks_find.
      destruct (find_block b (blocks _ _ _ p)); reflexivity.
    Qed.
    Definition pl_defs (p : func positive O.K O.G) := flat_map block_value_defs (blocks _ _ _ p).
    Definition pl_homes (p : func positive O.K O.G) :=
      map (fun x => (x, entry _ _ _ p)) (inputs _ _ _ p) ++ flat_map block_homes (blocks _ _ _ p).

    Lemma pl_values p : ssa_wf p ->
      S.values (R.prepare p) = inputs _ _ _ p ++ flat_map (fun item => block_defs (snd item)) (blocks _ _ _ p).
    Proof.
      intros [Hunique _].
      change (inputs _ _ _ p ++ flat_map (fun item => block_defs (snd item)) (first_blocks (blocks _ _ _ p)) =
        inputs _ _ _ p ++ flat_map (fun item => block_defs (snd item)) (blocks _ _ _ p)).
      now rewrite pl_first_identity.
    Qed.

    Lemma pl_values_unique p : ssa_wf p -> NoDup (S.values (R.prepare p)).
    Proof.
      intro Hssa; rewrite pl_values by exact Hssa.
      rewrite flat_map_concat_map; exact (proj1 (proj2 Hssa)).
    Qed.

    Lemma pl_def_keys p : ssa_wf p -> NoDup (map (fun row => PosKeyCode.encode (fst row)) (pl_defs p)).
    Proof.
      intro Hssa. change (NoDup (map fst (pl_defs p))). unfold pl_defs.
      rewrite pl_values_keys, flat_map_concat_map.
      eapply NoDup_app_remove_l; exact (proj1 (proj2 Hssa)).
    Qed.

    Lemma pl_home_keys p : ssa_wf p -> NoDup (map (fun row => PosKeyCode.encode (fst row)) (pl_homes p)).
    Proof.
      intro Hssa. change (NoDup (map fst (pl_homes p))). unfold pl_homes.
      rewrite map_app, map_map, pl_homes_keys.
      change (NoDup (map (fun x : positive => x) (inputs _ _ _ p) ++
        flat_map (fun item => block_defs (snd item)) (blocks _ _ _ p))).
      rewrite map_id, flat_map_concat_map; exact (proj1 (proj2 Hssa)).
    Qed.

    Lemma pl_def_reader p x : ssa_wf p ->
      S.def (R.prepare p) x = match trie_get x (first_table PosKeyCode.encode (pl_defs p)) with
        | Some d => d | None => Arbitrary end.
    Proof.
      intros [Hunique _]. unfold pl_defs.
      lazymatch goal with |- _ = ?rhs => change ((match trie_get x (first_table PosKeyCode.encode
        (flat_map block_value_defs (first_blocks (blocks _ _ _ p)))) with
        Some d => d | None => Arbitrary end) = rhs) end.
      now rewrite pl_first_identity.
    Qed.

    Lemma pl_home_reader p x : ssa_wf p ->
      S.home (R.prepare p) x = match trie_get x (first_table PosKeyCode.encode (pl_homes p)) with
        | Some b => b | None => entry _ _ _ p end.
    Proof.
      intros [Hunique _]. unfold pl_homes.
      lazymatch goal with |- _ = ?rhs => change ((match trie_get x (first_table PosKeyCode.encode
        (map (fun x => (x, entry _ _ _ p)) (inputs _ _ _ p) ++
          flat_map block_homes (first_blocks (blocks _ _ _ p)))) with
        | Some b => b | None => entry _ _ _ p end) = rhs) end.
      now rewrite pl_first_identity.
    Qed.

    Lemma pl_home_input p x : ssa_wf p -> In x (inputs _ _ _ p) ->
      S.home (R.prepare p) x = entry _ _ _ p.
    Proof.
      intros Hssa Hx; rewrite pl_home_reader by exact Hssa.
      assert (Hget : trie_get x (first_table PosKeyCode.encode (pl_homes p)) = Some (entry _ _ _ p)).
      { change (trie_get (PosKeyCode.encode x) (first_table PosKeyCode.encode (pl_homes p)) = Some (entry _ _ _ p)).
        apply present_table_lookup_unique; [now apply pl_home_keys|].
        unfold pl_homes; apply in_or_app; left; apply in_map_iff.
        exists x; now split. }
      now rewrite Hget.
    Qed.

    Lemma pl_home_block p b body x : ssa_wf p -> In (b, body) (blocks _ _ _ p) ->
      In x (block_defs body) -> S.home (R.prepare p) x = b.
    Proof.
      intros Hssa Hbody Hx; rewrite pl_home_reader by exact Hssa.
      assert (Hget : trie_get x (first_table PosKeyCode.encode (pl_homes p)) = Some b).
      { change (trie_get (PosKeyCode.encode x) (first_table PosKeyCode.encode (pl_homes p)) = Some b).
        apply present_table_lookup_unique; [now apply pl_home_keys|].
        unfold pl_homes; apply in_or_app; right; apply pl_home_rows; exists body; now split. }
      now rewrite Hget.
    Qed.

    Lemma pl_block_value p b body x : ssa_wf p -> In (b, body) (blocks _ _ _ p) ->
      In x (block_defs body) -> In x (S.values (R.prepare p)).
    Proof.
      intros Hssa Hbody Hx; rewrite pl_values by exact Hssa.
      apply in_or_app; right; apply in_flat_map; exists (b, body); now split.
    Qed.

    Lemma pl_body_node p b body : ssa_wf p -> In (b, body) (blocks _ _ _ p) ->
      In b (BC.nodes (R.prepare p)).
    Proof.
      intros Hssa Hbody; rewrite nodes_agree, pl_first_identity by exact (proj1 Hssa).
      apply in_map_iff; exists (b, body); now split.
    Qed.

    Lemma pl_home_listed p x : ssa_wf p -> In x (S.values (R.prepare p)) ->
      In (S.home (R.prepare p) x) (BC.nodes (R.prepare p)).
    Proof.
      intros Hssa Hx; rewrite pl_values in Hx by exact Hssa.
      apply in_app_or in Hx as [Hinput|Hdef].
      - rewrite pl_home_input by assumption.
        destruct Hssa as [Hu [Hv [Huses [[body Hbody] Hshapes]]]].
        rewrite nodes_agree, pl_first_identity by exact Hu.
        apply in_map_iff; exists (entry _ _ _ p, body); now split.
      - apply in_flat_map in Hdef as [[b body] [Hbody Hdef]].
        rewrite (pl_home_block p b body x Hssa Hbody Hdef).
        now apply pl_body_node with (body := body).
    Qed.

    Lemma pl_param_def p x b i : ssa_wf p ->
      (S.def (R.prepare p) x = Param b i <-> nth_error (S.params (R.prepare p) b) i = Some x).
    Proof.
      intro Hssa; split.
      - intro Hdef; rewrite pl_def_reader in Hdef by exact Hssa.
        destruct (trie_get x (first_table PosKeyCode.encode (pl_defs p))) as [d|] eqn:Hget;
          [subst d|discriminate].
        destruct (present_first_table_get PosKeyCode.encode (pl_defs p) x (Param b i) Hget)
          as [found [Hrow Hkey]]. change (found = x) in Hkey; subst found.
        unfold pl_defs in Hrow; apply in_flat_map in Hrow as [[owner body] [Hbody Hrow]].
        apply pl_value_rows in Hrow as [[j [Hnth Heq]]|[op [args [Hcode Heq]]]];
          [|discriminate]. cbn [fst snd] in Heq, Hnth. inversion Heq; subst.
        rewrite params_agree, (find_block_of_in _ _ _ (proj1 Hssa) Hbody); exact Hnth.
      - intro Hnth; rewrite params_agree in Hnth.
        destruct (find_block b (blocks _ _ _ p)) as [body|] eqn:Hfind;
          [|destruct i; discriminate].
        assert (Hrow : In (x, Param b i) (pl_defs p)).
        { unfold pl_defs; apply in_flat_map; exists (b, body); split.
          - now apply find_block_in.
          - apply pl_value_rows; left; exists i; now split. }
        assert (Hget : trie_get x (first_table PosKeyCode.encode (pl_defs p)) = Some (Param b i)).
        { change (trie_get (PosKeyCode.encode x) (first_table PosKeyCode.encode (pl_defs p)) = Some (Param b i)).
          apply present_table_lookup_unique; [now apply pl_def_keys|exact Hrow]. }
        rewrite pl_def_reader by exact Hssa; now rewrite Hget.
    Qed.

    Lemma pl_param_source p b x : In x (S.params (R.prepare p) b) ->
      exists body, In (b, body) (blocks _ _ _ p) /\ In x (params _ _ _ body).
    Proof.
      rewrite params_agree; destruct (find_block b (blocks _ _ _ p)) as [body|] eqn:Hfind;
        [|contradiction]. intro Hx; exists body; split; [now apply find_block_in|exact Hx].
    Qed.

    Lemma pl_param_home p b x : ssa_wf p -> In x (S.params (R.prepare p) b) ->
      S.home (R.prepare p) x = b.
    Proof.
      intros Hssa Hx; apply pl_param_source in Hx as [body [Hbody Hx]].
      eapply pl_home_block; [exact Hssa|exact Hbody|]. unfold block_defs; apply in_or_app; now left.
    Qed.

    Lemma pl_param_listed p b x : ssa_wf p -> In x (S.params (R.prepare p) b) ->
      In x (S.values (R.prepare p)).
    Proof.
      intros Hssa Hx; apply pl_param_source in Hx as [body [Hbody Hx]].
      eapply pl_block_value; [exact Hssa|exact Hbody|]. unfold block_defs; apply in_or_app; now left.
    Qed.

    Lemma pl_op_source p x op args : ssa_wf p -> S.def (R.prepare p) x = Op op args ->
      exists b body i, In (b, body) (blocks _ _ _ p) /\
        nth_error (code _ _ _ body) i = Some (x, op, args).
    Proof.
      intros Hssa Hdef; rewrite pl_def_reader in Hdef by exact Hssa.
      destruct (trie_get x (first_table PosKeyCode.encode (pl_defs p))) as [d|] eqn:Hget;
        [subst d|discriminate].
      destruct (present_first_table_get PosKeyCode.encode (pl_defs p) x (Op op args) Hget)
        as [found [Hrow Hkey]]. change (found = x) in Hkey; subst found.
      unfold pl_defs in Hrow; apply in_flat_map in Hrow as [[b body] [Hbody Hrow]].
      apply pl_value_rows in Hrow as [[j [Hnth Heq]]|[op' [args' [Hcode Heq]]]];
        [discriminate|]. inversion Heq; subst op' args'.
      apply In_nth_error in Hcode as [i Hnth]. exists b, body, i; now split.
    Qed.

    Lemma pl_targets (p : func positive O.K O.G) : ssa_wf p -> targets_listed p.
    Proof.
      intros [_ [_ [_ [_ Hshape]]]] b body target Hbody Htarget.
      specialize (Hshape b body Hbody).
      destruct (term _ _ _ body) as [dst args|g xs yes ya no na|xs];
        cbn [exit_targets exit_shape In] in Htarget, Hshape.
      - destruct Htarget as [Heq|[]]; subst target; destruct Hshape as [target [Hin _]].
        apply in_map_iff; exists (dst, target); now split.
      - destruct Hshape as [[yb [Hyb _]] [nb [Hnb _]]].
        destruct Htarget as [Heq|[Heq|[]]]; subst target; apply in_map_iff;
          [exists (yes, yb)|exists (no, nb)]; now split.
      - contradiction.
    Qed.

    Lemma pl_path_start (p : func positive O.K O.G) a route b : Lang.path p a route b -> In a route.
    Proof.
      intro Hpath; destruct Hpath; now left.
    Qed.

    Lemma pl_path_end (p : func positive O.K O.G) a route b : Lang.path p a route b -> In b route.
    Proof.
      intro Hpath; induction Hpath; [now left|now right].
    Qed.

    (** Source availability gives both a listed value and dominance of its home. *)
    Lemma pl_use_home p b body x i : ssa_wf p -> In (b, body) (blocks _ _ _ p) ->
      use_at body x i ->
      In x (S.values (R.prepare p)) /\ forall route,
        Lang.path p (entry _ _ _ p) route b -> In (S.home (R.prepare p) x) route.
    Proof.
      intros Hssa Hbody Huse.
      pose proof (proj1 (proj2 (proj2 Hssa)) b body x i Hbody Huse) as Havailable.
      destruct Havailable as [Hinput|[Hlocal|[owner [source [Hsource [Hother [Hdef Hdom]]]]]]].
      - split.
        + rewrite pl_values by exact Hssa; apply in_or_app; now left.
        + intros route Hpath; rewrite pl_home_input by assumption; now apply pl_path_start in Hpath.
      - assert (Hdef : In x (block_defs body)).
        { destruct Hlocal as [Hparam|[j [op [args [Hbefore Hnth]]]]].
          - unfold block_defs; apply in_or_app; now left.
          - pose proof (pl_code_def_nth body j x op args Hnth) as Hd.
            now apply nth_error_In in Hd. }
        split; [now apply pl_block_value with (b := b) (body := body)|].
        intros route Hpath; rewrite (pl_home_block p b body x Hssa Hbody Hdef).
        now apply pl_path_end in Hpath.
      - split; [now apply pl_block_value with (b := owner) (body := source)|].
        intros route Hpath; rewrite (pl_home_block p owner source x Hssa Hsource Hdef).
        now apply Hdom.
    Qed.

    Lemma pl_presented_use_home p b body x i : ssa_wf p -> In (b, body) (blocks _ _ _ p) ->
      use_at body x i ->
      In x (S.values (R.prepare p)) /\ forall start route, In start (BC.entries (R.prepare p)) ->
        presentation_path (BC.edges (R.prepare p)) (BC.src (R.prepare p)) (BC.dst (R.prepare p))
          start route b -> In (S.home (R.prepare p) x) route.
    Proof.
      intros Hssa Hbody Huse. destruct (pl_use_home p b body x i Hssa Hbody Huse) as [Hx Hdom].
      split; [exact Hx|]. intros start route Hstart Hpath.
      assert (Hentry : In (entry _ _ _ p) (map fst (blocks _ _ _ p))).
      { destruct (proj1 (proj2 (proj2 (proj2 Hssa)))) as [eb Heb].
        apply in_map_iff; exists (entry _ _ _ p, eb); now split. }
      rewrite entries_agree in Hstart by exact Hentry.
      destruct Hstart as [Heq|[]]; subst start.
      apply Hdom; apply (proj1 (paths_agree p _ _ _ (proj1 Hssa) (pl_targets p Hssa))); exact Hpath.
    Qed.

    Definition pl_kept (p : func positive O.K O.G) := first_blocks (blocks _ _ _ p).
    Definition pl_params (p : func positive O.K O.G) := first_table PosKeyCode.encode
      (map (fun item => (fst item, params _ _ _ (snd item))) (pl_kept p)).
    Definition pl_block_rows (p : func positive O.K O.G) :=
      flat_map (fun item => listed_edge_args (pl_params p) (fst item) (term _ _ _ (snd item))) (pl_kept p).

    Lemma pl_args_lookup p be args : In (be, args) (pl_block_rows p) ->
      S.args (R.prepare p) be = pair_args (index_row (pl_params p) (edge_target be)) args.
    Proof.
      intro Hrow.
      set (rows := map (fun r =>
        (fst r, pair_args (index_row (pl_params p) (edge_target (fst r))) (snd r))) (pl_block_rows p)).
      assert (Hkeys : NoDup (map (fun row => BlockEdge.encode (fst row)) rows)).
      { unfold rows; rewrite map_map.
        change (NoDup (map (fun row => BlockEdge.encode (fst row)) (pl_block_rows p))).
        rewrite <- map_map with (f := fst) (g := BlockEdge.encode).
        apply present_map_injective_nodup; [exact BlockEdge.encode_inj|].
        exact (lang_block_edges_nodup p). }
      assert (Hget : trie_get (BlockEdge.encode be) (first_table BlockEdge.encode rows) =
        Some (pair_args (index_row (pl_params p) (edge_target be)) args)).
      { apply present_table_lookup_unique; [exact Hkeys|]. unfold rows; apply in_map_iff.
        exists (be, args); now split. }
      change (index_row (first_table BlockEdge.encode rows) (BlockEdge.encode be) =
        pair_args (index_row (pl_params p) (edge_target be)) args).
      unfold index_row; now rewrite Hget.
    Qed.

    Lemma pl_edge_row p be : In be (BC.edges (R.prepare p)) ->
      exists args, In (be, args) (pl_block_rows p).
    Proof.
      intro Hin; change (In be (map fst (pl_block_rows p))) in Hin.
      apply in_map_iff in Hin as [[edge args] [Heq Hrow]].
      cbn in Heq; subst edge; now exists args.
    Qed.

    Lemma pl_row_source p be args : In (be, args) (pl_block_rows p) ->
      exists body, In (edge_source be, body) (blocks _ _ _ p) /\
        In (be, args) (exit_edge_args (edge_source be) (term _ _ _ body)).
    Proof.
      unfold pl_block_rows; intro Hrow.
      apply in_flat_map in Hrow as [[b body] [Hbody Hrow]].
      apply filter_In in Hrow as [Hsyntax _].
      pose proof (proj1 (exit_edge_args_shape b _ be args Hsyntax)) as Hsource.
      cbn [fst snd] in Hsource, Hsyntax. exists body; rewrite Hsource; split; [|exact Hsyntax].
      unfold pl_kept in Hbody; rewrite first_blocks_selected in Hbody.
      now apply selected_blocks_in in Hbody as [Hbody _].
    Qed.

    Lemma pl_args_params p be : ssa_wf p -> In be (BC.edges (R.prepare p)) ->
      map fst (S.args (R.prepare p) be) = S.params (R.prepare p) (BC.dst (R.prepare p) be).
    Proof.
      intros Hssa Hbe; destruct (pl_edge_row p be Hbe) as [args Hrow].
      rewrite (pl_args_lookup p be args Hrow).
      change (map fst (pair_args (S.params (R.prepare p) (edge_target be)) args) =
        S.params (R.prepare p) (edge_target be)).
      apply pl_pair_args_fst.
      destruct (pl_row_source p be args Hrow) as [body [Hbody Hsyntax]].
      destruct (present_exit_shape_args p (edge_source be) (term _ _ _ body) be args
        (proj2 (proj2 (proj2 (proj2 Hssa))) _ _ Hbody) Hsyntax) as [target [Htarget Hlength]].
      rewrite params_agree, (find_block_of_in _ _ _ (proj1 Hssa) Htarget).
      symmetry; exact Hlength.
    Qed.

    Lemma pl_args_dominate p be x y : ssa_wf p -> In be (BC.edges (R.prepare p)) ->
      In (x, y) (S.args (R.prepare p) be) ->
      In y (S.values (R.prepare p)) /\ forall start route, In start (BC.entries (R.prepare p)) ->
        presentation_path (BC.edges (R.prepare p)) (BC.src (R.prepare p)) (BC.dst (R.prepare p))
          start route (BC.src (R.prepare p) be) -> In (S.home (R.prepare p) y) route.
    Proof.
      intros Hssa Hbe Hpair. destruct (pl_edge_row p be Hbe) as [args Hrow].
      rewrite (pl_args_lookup p be args Hrow) in Hpair; apply pl_pair_args_second in Hpair.
      destruct (pl_row_source p be args Hrow) as [body [Hbody Hsyntax]].
      eapply pl_presented_use_home; [exact Hssa|exact Hbody|].
      right; split; [reflexivity|]. eapply pl_exit_arg_use; eassumption.
    Qed.

    Definition pl_guard_rows (p : func positive O.K O.G) :=
      flat_map (fun item => listed_guards (pl_params p) (fst item) (term _ _ _ (snd item))) (pl_kept p).

    Lemma pl_guard_source p be g xs : In (g, xs) (S.guards (R.prepare p) be) ->
      exists body guards, In (edge_source be, body) (blocks _ _ _ p) /\
        In (be, guards) (exit_guards (edge_source be) (term _ _ _ body)) /\ In (g, xs) guards.
    Proof.
      intro Hguard; change (In (g, xs) (index_row (first_table BlockEdge.encode (pl_guard_rows p))
        (BlockEdge.encode be))) in Hguard.
      unfold index_row in Hguard. destruct (trie_get (BlockEdge.encode be)
        (first_table BlockEdge.encode (pl_guard_rows p))) as [guards|] eqn:Hget;
        [|contradiction].
      destruct (present_first_table_get BlockEdge.encode (pl_guard_rows p) _ _ Hget)
        as [edge [Hrow Hkey]]. apply BlockEdge.encode_inj in Hkey; subst edge.
      unfold pl_guard_rows in Hrow; apply in_flat_map in Hrow as [[b body] [Hbody Hrow]].
      apply filter_In in Hrow as [Hsyntax _].
      pose proof (pl_exit_guard_source b (term _ _ _ body) be guards Hsyntax) as Hsource.
      exists body, guards. rewrite Hsource. split.
      - unfold pl_kept in Hbody; rewrite first_blocks_selected in Hbody.
        now apply selected_blocks_in in Hbody as [Hbody _].
      - now split.
    Qed.

    Lemma pl_guards_dominate p be g xs x : ssa_wf p -> In (g, xs) (S.guards (R.prepare p) be) ->
      In x xs -> In x (S.values (R.prepare p)) /\
        forall start route, In start (BC.entries (R.prepare p)) ->
        presentation_path (BC.edges (R.prepare p)) (BC.src (R.prepare p)) (BC.dst (R.prepare p))
          start route (BC.src (R.prepare p) be) -> In (S.home (R.prepare p) x) route.
    Proof.
      intros Hssa Hguard Hx.
      destruct (pl_guard_source p be g xs Hguard) as [body [guards [Hbody [Hsyntax Hmember]]]].
      eapply pl_presented_use_home; [exact Hssa|exact Hbody|].
      right; split; [reflexivity|]. eapply pl_exit_guard_use; eassumption.
    Qed.

    Lemma pl_op_args_dominate p x op args y : ssa_wf p -> S.def (R.prepare p) x = Op op args ->
      In y args -> In y (S.values (R.prepare p)) /\
        forall start route, In start (BC.entries (R.prepare p)) ->
        presentation_path (BC.edges (R.prepare p)) (BC.src (R.prepare p)) (BC.dst (R.prepare p))
          start route (S.home (R.prepare p) x) -> In (S.home (R.prepare p) y) route.
    Proof.
      intros Hssa Hdef Hy. destruct (pl_op_source p x op args Hssa Hdef) as [b [body [i [Hbody Hnth]]]].
      pose proof (pl_code_def_nth body i x op args Hnth) as Hx; apply nth_error_In in Hx.
      rewrite (pl_home_block p b body x Hssa Hbody Hx).
      eapply pl_presented_use_home with (i := i); [exact Hssa|exact Hbody|].
      left; exists op, args, x; now split.
    Qed.

    (** A block occupies one contiguous segment after the input values. *)
    Lemma pl_block_ranks p b body : ssa_wf p -> In (b, body) (blocks _ _ _ p) ->
      exists base, length (inputs _ _ _ p) <= base /\ forall x i,
        nth_error (block_defs body) i = Some x -> pl_rank (S.values (R.prepare p)) x = base + i.
    Proof.
      intros Hssa Hbody. apply in_split in Hbody as [before [after Hsplit]].
      set (pre := inputs _ _ _ p ++ flat_map (fun item => block_defs (snd item)) before).
      assert (Hwhole : S.values (R.prepare p) =
        pre ++ block_defs body ++ flat_map (fun item => block_defs (snd item)) after).
      { rewrite pl_values by exact Hssa. rewrite Hsplit, flat_map_app.
        cbn [flat_map snd]; unfold pre; now rewrite app_assoc. }
      exists (length pre); split.
      - unfold pre; rewrite length_app; lia.
      - intros x i Hnth. eapply pl_rank_segment; [now apply pl_values_unique|exact Hwhole|exact Hnth].
    Qed.

    Lemma pl_input_rank p x i : ssa_wf p -> nth_error (inputs _ _ _ p) i = Some x ->
      pl_rank (S.values (R.prepare p)) x = i.
    Proof.
      intros Hssa Hnth.
      apply (pl_rank_segment (S.values (R.prepare p)) [] (inputs _ _ _ p)
        (flat_map (fun item => block_defs (snd item)) (blocks _ _ _ p)) x i).
      - now apply pl_values_unique.
      - cbn [app]; now rewrite pl_values by exact Hssa.
      - exact Hnth.
    Qed.

    Lemma pl_dependency_rank p y x : ssa_wf p -> S.home (R.prepare p) y = S.home (R.prepare p) x ->
      (exists op args, S.def (R.prepare p) x = Op op args /\ In y args) ->
      pl_rank (S.values (R.prepare p)) y < pl_rank (S.values (R.prepare p)) x.
    Proof.
      intros Hssa Hsame [op [args [Hdef Hy]]].
      destruct (pl_op_source p x op args Hssa Hdef) as [b [body [i [Hbody Hcode]]]].
      destruct (pl_block_ranks p b body Hssa Hbody) as [base [Hbase Hranks]].
      pose proof (pl_code_def_nth body i x op args Hcode) as Hx.
      pose proof (Hranks _ _ Hx) as Hrankx.
      assert (Hhome : S.home (R.prepare p) x = b).
      { eapply pl_home_block; [exact Hssa|exact Hbody|now apply nth_error_In in Hx]. }
      assert (Huse : use_at body y i) by (left; exists op, args, x; now split).
      pose proof (proj1 (proj2 (proj2 Hssa)) b body y i Hbody Huse) as Havailable.
      destruct Havailable as [Hinput|[Hlocal|[owner [source [Hsource [Hother [Hdefy Hdom]]]]]]].
      - apply In_nth_error in Hinput as [j Hnth].
        pose proof (pl_input_rank p y j Hssa Hnth) as Hranky.
        assert (Hj : j < length (inputs _ _ _ p)).
        { apply nth_error_Some; rewrite Hnth; discriminate. }
        lia.
      - destruct Hlocal as [Hparam|[j [op' [args' [Hbefore Hnth]]]]].
        + apply In_nth_error in Hparam as [j Hnth].
          pose proof (pl_param_def_nth body j y Hnth) as Hydef.
          pose proof (Hranks _ _ Hydef) as Hranky.
          assert (Hj : j < length (params _ _ _ body)).
          { apply nth_error_Some; rewrite Hnth; discriminate. }
          lia.
        + pose proof (pl_code_def_nth body j y op' args' Hnth) as Hydef.
          pose proof (Hranks _ _ Hydef) as Hranky; lia.
      - pose proof (pl_home_block p owner source y Hssa Hsource Hdefy) as Hhomey.
        congruence.
    Qed.

    Lemma pl_dependencies_wf p : ssa_wf p -> well_founded (fun y x =>
      In x (S.values (R.prepare p)) /\ S.home (R.prepare p) y = S.home (R.prepare p) x /\
        exists op args, S.def (R.prepare p) x = Op op args /\ In y args).
    Proof.
      intro Hssa. apply well_founded_lt_compat with (f := pl_rank (S.values (R.prepare p))).
      intros y x [_ [Hsame Hdef]]; now apply pl_dependency_rank.
    Qed.

    Lemma pl_entry_params p : S.entry_params (R.prepare p) =
      flat_map (S.params (R.prepare p)) (BC.entries (R.prepare p)).
    Proof.
      reflexivity.
    Qed.

    Lemma pl_arg_rows p : S.arg_rows (R.prepare p) =
      flat_map (fun be => map (pair be) (S.args (R.prepare p) be)) (BC.edges (R.prepare p)).
    Proof.
      change (flat_map (fun r => map (pair (fst r))
          (pair_args (index_row (pl_params p) (edge_target (fst r))) (snd r))) (pl_block_rows p) =
        flat_map (fun be => map (pair be) (S.args (R.prepare p) be)) (map fst (pl_block_rows p))).
      rewrite flat_map_after_map. apply pl_flat_map_ext_in.
      intros [be args] Hrow; cbn [fst snd]. now rewrite (pl_args_lookup p be args Hrow).
    Qed.

    Lemma pl_wf_complete p : ssa_wf p -> S.wf (R.prepare p).
    Proof.
      intro Hssa; unfold S.wf.
      split; [reflexivity|].
      split; [now apply pl_values_unique|].
      split; [intros x Hx; now apply pl_home_listed|].
      split; [intros x b i; now apply pl_param_def|].
      split; [intros b x Hx; now apply pl_param_home|].
      split; [intros b x Hb Hx; now apply pl_param_listed with (b := b)|].
      split; [intros be Hbe; now apply pl_args_params|].
      split; [intros be x y Hbe Hxy; now apply pl_args_dominate with (x := x)|].
      split; [intros be g xs x Hbe Hg Hx; now apply pl_guards_dominate with (g := g) (xs := xs)|].
      split; [intros x op args y Hx Hdef Hy; now apply pl_op_args_dominate with (op := op) (args := args)|].
      split; [now apply pl_dependencies_wf|].
      split; [apply pl_entry_params|apply pl_arg_rows].
    Qed.

    Lemma wf_from_lang : forall p, ssa_wf p -> S.wf (R.prepare p).
    Proof.
      exact pl_wf_complete.
    Qed.
  End Link.

  Module Budget <: LANG_PRESENT_BUDGET O Q R BlockEdge PointEdge PointKey BC C U SP.
    Definition c_present : N := 128.

  (** Both prepared graphs are well formed for every raw function. *)
  Lemma prepared_wf : forall p, BC.wf (R.prepare p) /\ C.wf (R.prepare p).
  Proof.
    intro p; split; reflexivity.
  Qed.
  Definition pp_kept (p : func positive O.K O.G) := first_blocks (blocks _ _ _ p).
  Definition pp_params (p : func positive O.K O.G) :=
    first_table PosKeyCode.encode (map (fun item => (fst item, params _ _ _ (snd item))) (pp_kept p)).
  Definition pp_summaries (p : func positive O.K O.G) := map (summarize (pp_params p)) (pp_kept p).

  Lemma pp_kept_unique p : NoDup (map fst (pp_kept p)).
  Proof.
    unfold pp_kept; rewrite first_blocks_selected; apply selected_blocks_nodup.
  Qed.
  Lemma pp_points_lookup p b : SP.points_in_block (R.prepare p) b =
    match find_block b (blocks _ _ _ p) with
    | Some body => summary_points (summarize (pp_params p) (b, body))
    | None => []
    end.
  Proof.
    lazymatch goal with |- _ = ?rhs =>
      change (index_row (first_table PosKeyCode.encode
        (map (fun s => (summary_block s, summary_points s)) (pp_summaries p))) b = rhs) end.
    unfold pp_summaries; rewrite map_map.
    lazymatch goal with |- _ = ?rhs =>
      change (index_row (first_table PosKeyCode.encode
        (map (fun item => (fst item, summary_points (summarize (pp_params p) item))) (pp_kept p))) b = rhs) end.
    unfold index_row; rewrite present_block_table_lookup.
    unfold pp_kept; rewrite first_blocks_find.
    destruct (find_block b (blocks _ _ _ p)); reflexivity.
  Qed.

  Lemma pp_instruction_lookup p b : SP.instruction_edges (R.prepare p) b =
    match find_block b (blocks _ _ _ p) with
    | Some body => map (fun row => fst (fst row)) (summary_internal (summarize (pp_params p) (b, body)))
    | None => []
    end.
  Proof.
    lazymatch goal with |- _ = ?rhs =>
      change (index_row (first_table PosKeyCode.encode
      (map (fun s => (summary_block s, map (fun row => fst (fst row)) (summary_internal s)))
        (pp_summaries p))) b = rhs) end.
    unfold pp_summaries; rewrite map_map.
    lazymatch goal with |- _ = ?rhs =>
      change (index_row (first_table PosKeyCode.encode
      (map (fun item => (fst item,
        map (fun row => fst (fst row)) (summary_internal (summarize (pp_params p) item))))
        (pp_kept p))) b = rhs) end.
    unfold index_row; rewrite present_block_table_lookup.
    unfold pp_kept; rewrite first_blocks_find.
    destruct (find_block b (blocks _ _ _ p)); reflexivity.
  Qed.

  Lemma pp_parameter_lookup p b body : find_block b (blocks _ _ _ p) = Some body ->
    SP.parameter_edge (R.prepare p) b = PointEdge (b, 0%N) (b, 1%N) None.
  Proof.
    intro Hfind.
    lazymatch goal with |- _ = ?rhs =>
      change ((match trie_get b (first_table PosKeyCode.encode
      (map (fun s => (summary_block s,
        PointEdge (summary_block s, 0%N) (summary_block s, 1%N) None)) (pp_summaries p))) with
      | Some e => e
      | None => PointEdge (entry _ _ _ p, 0%N) (entry _ _ _ p, 1%N) None
      end) = rhs) end.
    unfold pp_summaries; rewrite map_map.
    lazymatch goal with |- _ = ?rhs =>
      change ((match trie_get b (first_table PosKeyCode.encode
      (map (fun item => (fst item, PointEdge (fst item, 0%N) (fst item, 1%N) None)) (pp_kept p))) with
      | Some e => e
      | None => PointEdge (entry _ _ _ p, 0%N) (entry _ _ _ p, 1%N) None
      end) = rhs) end.
    rewrite present_block_table_lookup. unfold pp_kept; rewrite first_blocks_find, Hfind.
    reflexivity.
  Qed.

  Lemma pp_listed_find p b : In b (BC.nodes (R.prepare p)) ->
    exists body, find_block b (blocks _ _ _ p) = Some body /\ In (b, body) (pp_kept p).
  Proof.
    rewrite Link.nodes_agree. intro Hin; apply find_block_exists in Hin as [body Hfind].
    exists body; split.
    - rewrite first_blocks_find in Hfind; exact Hfind.
    - now apply find_block_in.
  Qed.

  Lemma pp_point_out_unique p n : NoDup (C.out (R.prepare p) n).
  Proof.
    change (NoDup (index_row
      (multi_table (fun e => PointKey.encode (point_src e)) (lang_point_edges (lang_prepare p)))
      (PointKey.encode n))).
    apply present_multi_table_nodup, lang_point_edges_nodup.
  Qed.

  Lemma pp_block_out_unique p b : NoDup (BC.out (R.prepare p) b).
  Proof.
    change (NoDup (index_row (multi_table edge_source (lang_edges (lang_prepare p))) b)).
    apply present_multi_table_nodup, lang_block_edges_nodup.
  Qed.

  Lemma pp_points_unique p b : NoDup (SP.points_in_block (R.prepare p) b).
  Proof.
    rewrite pp_points_lookup. destruct (find_block b (blocks _ _ _ p)).
    - apply summarize_points_nodup.
    - constructor.
  Qed.

  Lemma pp_points_nonempty p b : In b (BC.nodes (R.prepare p)) ->
    SP.points_in_block (R.prepare p) b <> [].
  Proof.
    intro Hin; destruct (pp_listed_find p b Hin) as [body [Hfind _]].
    rewrite pp_points_lookup, Hfind; apply present_summary_nonempty.
  Qed.

  Lemma pp_parameter_first p b : In b (BC.nodes (R.prepare p)) ->
    nth_error (SP.instruction_edges (R.prepare p) b) 0 = Some (SP.parameter_edge (R.prepare p) b).
  Proof.
    intro Hin; destruct (pp_listed_find p b Hin) as [body [Hfind _]].
    rewrite pp_instruction_lookup, Hfind, (pp_parameter_lookup p b body Hfind).
    apply present_summary_parameter.
  Qed.

  Definition pp_rows (p : func positive O.K O.G) :=
    flat_map (fun s => summary_internal s ++ summary_outgoing s) (pp_summaries p).

  Lemma pp_points_covered p n :
    In n (C.nodes (R.prepare p)) <->
    exists b, In b (BC.nodes (R.prepare p)) /\ In n (SP.points_in_block (R.prepare p) b).
  Proof.
    split.
    - intro Hin. change (In n (flat_map summary_points (pp_summaries p))) in Hin.
      apply in_flat_map in Hin as [s [Hs Hpoint]].
      unfold pp_summaries in Hs; apply in_map_iff in Hs as [[b body] [Heq Hitem]].
      subst s. exists b; split.
      + change (In b (map fst (pp_kept p))). now apply in_map with (f := fst) in Hitem.
      + rewrite pp_points_lookup.
        assert (Hfind : find_block b (blocks _ _ _ p) = Some body).
        { rewrite <- first_blocks_find. apply find_block_of_in; [apply pp_kept_unique|exact Hitem]. }
        now rewrite Hfind.
    - intros [b [Hb Hpoint]]. destruct (pp_listed_find p b Hb) as [body [Hfind Hitem]].
      rewrite pp_points_lookup, Hfind in Hpoint.
      apply (lang_summary_points p (b, body) n Hitem Hpoint).
  Qed.

  Lemma pp_point_owner p b n : In b (BC.nodes (R.prepare p)) ->
    In n (SP.points_in_block (R.prepare p) b) -> SP.block_of_point (R.prepare p) n = b.
  Proof.
    intros Hb Hpoint. destruct (pp_listed_find p b Hb) as [body [Hfind Hitem]].
    rewrite pp_points_lookup, Hfind in Hpoint.
    assert (Hlookup : trie_get (PointKey.encode n)
      (first_table PointKey.encode (flat_map
        (fun s => map (fun x => (x, summary_block s)) (summary_points s)) (pp_summaries p))) = Some b).
    { apply present_table_lookup_unique.
      - rewrite <- map_map with (f := fst) (g := PointKey.encode).
        apply present_map_injective_nodup; [exact PointKey.encode_inj|].
        rewrite present_summary_owner_keys. exact (C.nodes_nodup (R.prepare p) (proj2 (prepared_wf p))).
      - apply in_flat_map. exists (summarize (pp_params p) (b, body)); split.
        + unfold pp_summaries. now apply in_map.
        + apply in_map_iff. exists n; split; [reflexivity|exact Hpoint]. }
    change ((match trie_get (PointKey.encode n)
      (first_table PointKey.encode (flat_map
        (fun s => map (fun x => (x, summary_block s)) (summary_points s)) (pp_summaries p))) with
      | Some owner => owner | None => entry _ _ _ p end) = b).
    now rewrite Hlookup.
  Qed.

  Lemma pp_point_owner_fst p n : In n (C.nodes (R.prepare p)) ->
    SP.block_of_point (R.prepare p) n = fst n.
  Proof.
    intro Hin; apply pp_points_covered in Hin as [b [Hb Hpoint]].
    rewrite (pp_point_owner p b n Hb Hpoint).
    destruct (pp_listed_find p b Hb) as [body [Hfind _]].
    rewrite pp_points_lookup, Hfind in Hpoint.
    symmetry. exact (summarize_point_owner (pp_params p) (b, body) n Hpoint).
  Qed.

  Lemma pp_internal_row_listed p item row : In item (pp_kept p) ->
    In row (summary_internal (summarize (pp_params p) item)) -> In row (pp_rows p).
  Proof.
    intros Hitem Hrow. unfold pp_rows. apply in_flat_map.
    exists (summarize (pp_params p) item); split.
    - unfold pp_summaries. now apply in_map.
    - apply in_or_app; now left.
  Qed.

  Lemma pp_instruction_listed p b e : In b (BC.nodes (R.prepare p)) ->
    In e (SP.instruction_edges (R.prepare p) b) -> In e (C.edges (R.prepare p)).
  Proof.
    intros Hb He. destruct (pp_listed_find p b Hb) as [body [Hfind Hitem]].
    rewrite pp_instruction_lookup, Hfind in He.
    apply in_map_iff in He as [row [Heq Hrow]]; subst e.
    change (In (fst (fst row)) (map (fun r => fst (fst r)) (pp_rows p))).
    apply in_map_iff. exists row; split; [reflexivity|].
    now apply pp_internal_row_listed with (item := (b, body)).
  Qed.

  Lemma pp_points_ordered p b : In b (BC.nodes (R.prepare p)) ->
    presentation_chain (C.edges (R.prepare p)) (C.src (R.prepare p)) (C.dst (R.prepare p))
      (SP.points_in_block (R.prepare p) b) (SP.instruction_edges (R.prepare p) b).
  Proof.
    intro Hb. destruct (pp_listed_find p b Hb) as [body [Hfind Hitem]].
    rewrite pp_points_lookup, pp_instruction_lookup, Hfind.
    apply present_summary_chain. intros e He. apply pp_instruction_listed with (b := b);
      [exact Hb|]. now rewrite pp_instruction_lookup, Hfind.
  Qed.

  Lemma pp_block_projection p e : In e (C.edges (R.prepare p)) ->
    SP.block_edge_of (R.prepare p) e = point_block_edge e.
  Proof.
    intro Hin. change (In e (map (fun row => fst (fst row)) (pp_rows p))) in Hin.
    pose proof (present_partial_table PointEdge.encode point_block_edge PointEdge.encode_inj
      (map (fun row => fst (fst row)) (pp_rows p)) e Hin) as Hlookup.
    rewrite flat_map_after_map in Hlookup. exact Hlookup.
  Qed.

  Lemma pp_instruction_internal p b e : In b (BC.nodes (R.prepare p)) ->
    In e (SP.instruction_edges (R.prepare p) b) -> SP.block_edge_of (R.prepare p) e = None.
  Proof.
    intros Hb He. rewrite pp_block_projection by (eapply pp_instruction_listed; eauto).
    destruct (pp_listed_find p b Hb) as [body [Hfind _]].
    rewrite pp_instruction_lookup, Hfind in He.
    apply in_map_iff in He as [row [Heq Hrow]]; subst e.
    now apply summarize_internal_no_block in Hrow.
  Qed.

  Lemma pp_instruction_complete p e : In e (C.edges (R.prepare p)) ->
    SP.block_edge_of (R.prepare p) e = None ->
    In e (SP.instruction_edges (R.prepare p) (SP.block_of_point (R.prepare p) (C.src (R.prepare p) e))).
  Proof.
    intros He Hprojection. rewrite pp_block_projection in Hprojection by exact He.
    rewrite pp_point_owner_fst by
      (exact (proj1 (C.edges_nodes (R.prepare p) e (proj2 (prepared_wf p)) He))).
    change (In e (map (fun row => fst (fst row)) (pp_rows p))) in He.
    apply in_map_iff in He as [row [Heq Hrow]]; subst e.
    unfold pp_rows in Hrow; apply in_flat_map in Hrow as [s [Hs Hrow]].
    unfold pp_summaries in Hs; apply in_map_iff in Hs as [[b body] [Heq Hitem]]; subst s.
    assert (Howner : fst (point_src (fst (fst row))) = b).
    { apply (summarize_edge_owner (pp_params p) (b, body) row Hrow). }
    change (In (fst (fst row)) (SP.instruction_edges (R.prepare p)
      (fst (point_src (fst (fst row)))))).
    rewrite Howner, pp_instruction_lookup.
    assert (Hfind : find_block b (blocks _ _ _ p) = Some body).
    { rewrite <- first_blocks_find. apply find_block_of_in; [apply pp_kept_unique|exact Hitem]. }
    rewrite Hfind. apply in_map_iff. exists row; split; [reflexivity|].
    apply in_app_or in Hrow as [Hinternal|Houtgoing]; [exact Hinternal|].
    destruct (summarize_outgoing_block (pp_params p) (b, body) row Houtgoing)
      as [be Hbe]. congruence.
  Qed.

  Lemma pp_row_keys_unique p :
    NoDup (map (fun row => PointEdge.encode (fst (fst row))) (pp_rows p)).
  Proof.
    rewrite <- map_map with (f := fun row => fst (fst row)) (g := PointEdge.encode).
    apply present_map_injective_nodup; [exact PointEdge.encode_inj|].
    exact (lang_point_edges_nodup p).
  Qed.

  Lemma pp_uses_lookup p row : In row (pp_rows p) ->
    U.uses (R.prepare p) (fst (fst row)) = snd (fst row).
  Proof.
    intro Hrow.
    assert (Hlookup : trie_get (PointEdge.encode (fst (fst row)))
      (first_table PointEdge.encode (map (fun r => (fst (fst r), snd (fst r))) (pp_rows p))) =
      Some (snd (fst row))).
    { apply present_table_lookup_unique.
      - rewrite map_map. apply pp_row_keys_unique.
      - apply in_map_iff. exists row; now split. }
    change (index_row (first_table PointEdge.encode
      (map (fun r => (fst (fst r), snd (fst r))) (pp_rows p))) (PointEdge.encode (fst (fst row))) =
      snd (fst row)).
    unfold index_row; now rewrite Hlookup.
  Qed.

  Lemma pp_defs_lookup p row : In row (pp_rows p) ->
    U.defs (R.prepare p) (fst (fst row)) = snd row.
  Proof.
    intro Hrow.
    assert (Hlookup : trie_get (PointEdge.encode (fst (fst row)))
      (first_table PointEdge.encode (map (fun r => (fst (fst r), snd r)) (pp_rows p))) = Some (snd row)).
    { apply present_table_lookup_unique.
      - rewrite map_map. apply pp_row_keys_unique.
      - apply in_map_iff. exists row; now split. }
    change (index_row (first_table PointEdge.encode
      (map (fun r => (fst (fst r), snd r)) (pp_rows p))) (PointEdge.encode (fst (fst row))) = snd row).
    unfold index_row; now rewrite Hlookup.
  Qed.

  Lemma pp_parameter_defs p b x : In b (BC.nodes (R.prepare p)) ->
    (In x (U.defs (R.prepare p) (SP.parameter_edge (R.prepare p) b)) <->
      In x (SP.block_params (R.prepare p) b)).
  Proof.
    intro Hb. destruct (pp_listed_find p b Hb) as [body [Hfind Hitem]].
    assert (Hrow : In (PointEdge (b, 0%N) (b, 1%N) None, [], params _ _ _ body) (pp_rows p)).
    { eapply pp_internal_row_listed; [exact Hitem|]. left; reflexivity. }
    pose proof (pp_defs_lookup p _ Hrow) as Hdefs.
    rewrite (pp_parameter_lookup p b body Hfind).
    change (U.defs (R.prepare p) (PointEdge (b, 0%N) (b, 1%N) None) = params _ _ _ body) in Hdefs.
    rewrite Hdefs.
    change (In x (params _ _ _ body) <-> In x (S.params (R.prepare p) b)).
    rewrite Link.params_agree, Hfind; reflexivity.
  Qed.

  Definition pp_block_rows (p : func positive O.K O.G) :=
    flat_map (fun item => listed_edge_args (pp_params p) (fst item) (term _ _ _ (snd item))) (pp_kept p).

  Lemma pp_block_args_lookup p be args : In (be, args) (pp_block_rows p) ->
    SP.block_edge_args (R.prepare p) be = args.
  Proof.
    intro Hrow.
    assert (Hlookup : trie_get (BlockEdge.encode be) (first_table BlockEdge.encode (pp_block_rows p)) = Some args).
    { apply present_table_lookup_unique.
      - rewrite <- map_map with (f := fst) (g := BlockEdge.encode).
        apply present_map_injective_nodup; [exact BlockEdge.encode_inj|].
        exact (lang_block_edges_nodup p).
      - exact Hrow. }
    change (index_row (first_table BlockEdge.encode (pp_block_rows p)) (BlockEdge.encode be) = args).
    unfold index_row; now rewrite Hlookup.
  Qed.

  Lemma pp_outgoing_shape p e be : In e (C.edges (R.prepare p)) ->
    point_block_edge e = Some be ->
    exists body args, In (edge_source be, body) (pp_kept p) /\
      In (be, args) (listed_edge_args (pp_params p) (edge_source be) (term _ _ _ body)) /\
      e = PointEdge (summary_exit (summarize (pp_params p) (edge_source be, body)))
        (edge_target be, 0%N) (Some be) /\
      In (e, guard_uses (term _ _ _ body) ++ args, []) (pp_rows p).
  Proof.
    intros He Hbe.
    change (In e (map (fun row => fst (fst row)) (pp_rows p))) in He.
    apply in_map_iff in He as [row [Heq Hrow]]; subst e.
    pose proof Hrow as Hglobal. unfold pp_rows in Hrow.
    apply in_flat_map in Hrow as [s [Hs Hrow]].
    unfold pp_summaries in Hs; apply in_map_iff in Hs as [[b body] [Heq Hitem]]; subst s.
    apply in_app_or in Hrow as [Hinternal|Houtgoing].
    - rewrite (summarize_internal_no_block _ _ _ Hinternal) in Hbe; discriminate.
    - change (In row (map (fun ea =>
        (PointEdge (summary_exit (summarize (pp_params p) (b, body)))
          (edge_target (fst ea), 0%N) (Some (fst ea)),
          guard_uses (term _ _ _ body) ++ snd ea, []))
        (listed_edge_args (pp_params p) b (term _ _ _ body)))) in Houtgoing.
      apply in_map_iff in Houtgoing as [[be' args] [Heq Hedge]]; subst row.
      cbn [fst point_block_edge] in Hbe; inversion Hbe; subst be'.
      assert (Hsource : edge_source be = b).
      { apply filter_In in Hedge as [Hsyntax _].
        exact (proj1 (exit_edge_args_shape b _ be args Hsyntax)). }
      exists body, args. rewrite Hsource. repeat split; try assumption; reflexivity.
  Qed.

  Lemma pp_point_projection p e : In e (C.edges (R.prepare p)) ->
    match SP.block_edge_of (R.prepare p) e with
    | None => SP.block_of_point (R.prepare p) (C.src (R.prepare p) e) =
        SP.block_of_point (R.prepare p) (C.dst (R.prepare p) e)
    | Some be => In be (BC.edges (R.prepare p)) /\
        BC.src (R.prepare p) be = SP.block_of_point (R.prepare p) (C.src (R.prepare p) e) /\
        BC.dst (R.prepare p) be = SP.block_of_point (R.prepare p) (C.dst (R.prepare p) e) /\
        last (SP.points_in_block (R.prepare p) (SP.block_of_point (R.prepare p) (C.src (R.prepare p) e)))
          (C.src (R.prepare p) e) = C.src (R.prepare p) e /\
        nth_error (SP.points_in_block (R.prepare p) (BC.dst (R.prepare p) be)) 0 =
          Some (C.dst (R.prepare p) e)
    end.
  Proof.
    intro He. rewrite pp_block_projection by exact He.
    destruct (C.edges_nodes (R.prepare p) e (proj2 (prepared_wf p)) He) as [Hsrc Hdst].
    rewrite (pp_point_owner_fst p _ Hsrc), (pp_point_owner_fst p _ Hdst).
    destruct (point_block_edge e) as [be|] eqn:Hbe.
    - destruct (pp_outgoing_shape p e be He Hbe) as [body [args [Hitem [Hargs [Heq Hrow]]]]].
      assert (Hb : In be (BC.edges (R.prepare p))).
      { change (In be (map fst (pp_block_rows p))). apply in_map_iff.
        exists (be, args); split; [reflexivity|].
        unfold pp_block_rows; apply in_flat_map. exists (edge_source be, body); now split. }
      assert (Hfind : find_block (edge_source be) (blocks _ _ _ p) = Some body).
      { rewrite <- first_blocks_find. apply find_block_of_in; [apply pp_kept_unique|exact Hitem]. }
      destruct (pp_listed_find p (edge_target be)
        (proj2 (BC.edges_nodes (R.prepare p) be (proj1 (prepared_wf p)) Hb)))
        as [target [Htarget _]].
      subst e. change (In be (BC.edges (R.prepare p)) /\ edge_source be = edge_source be /\
        edge_target be = edge_target be /\
        last (SP.points_in_block (R.prepare p) (edge_source be))
          (summary_exit (summarize (pp_params p) (edge_source be, body))) =
          summary_exit (summarize (pp_params p) (edge_source be, body)) /\
        nth_error (SP.points_in_block (R.prepare p) (edge_target be)) 0 = Some (edge_target be, 0%N)).
      rewrite !pp_points_lookup, Hfind, Htarget.
      split; [exact Hb|].
      split; [reflexivity|].
      split; [reflexivity|].
      split; [apply present_summary_last|apply present_summary_first].
    - change (In e (map (fun row => fst (fst row)) (pp_rows p))) in He.
      apply in_map_iff in He as [row [Heq Hrow]]; subst e.
      unfold pp_rows in Hrow; apply in_flat_map in Hrow as [s [Hs Hrow]].
      unfold pp_summaries in Hs; apply in_map_iff in Hs as [item [Heq Hitem]]; subst s.
      apply in_app_or in Hrow as [Hi|Ho].
      + destruct (summarize_internal_endpoints _ _ _ Hi) as [Hs Hd].
        apply summarize_point_owner in Hs. apply summarize_point_owner in Hd.
        change (fst (point_src (fst (fst row))) = fst (point_dst (fst (fst row)))).
        transitivity (fst item); [exact Hs|symmetry; exact Hd].
      + destruct (summarize_outgoing_block _ _ _ Ho) as [be Hsome]; congruence.
  Qed.

  Lemma pp_phi_arity p be : ssa_wf p -> In be (BC.edges (R.prepare p)) ->
    length (SP.block_edge_args (R.prepare p) be) =
      length (SP.block_params (R.prepare p) (BC.dst (R.prepare p) be)).
  Proof.
    intros [Hunique [_ [_ [_ Hshapes]]]] Hbe.
    change (In be (map fst (pp_block_rows p))) in Hbe.
    apply in_map_iff in Hbe as [[edge args] [Heq Hrow]]; cbn in Heq; subst edge.
    rewrite (pp_block_args_lookup p be args Hrow).
    unfold pp_block_rows in Hrow; apply in_flat_map in Hrow as [[b body] [Hitem Hedge]].
    assert (Hraw : In (b, body) (blocks _ _ _ p)).
    { unfold pp_kept in Hitem. rewrite first_blocks_selected in Hitem.
      now apply selected_blocks_in in Hitem as [Hitem _]. }
    apply filter_In in Hedge as [Hsyntax _].
    destruct (present_exit_shape_args p b (term _ _ _ body) be args (Hshapes b body Hraw) Hsyntax)
      as [target [Htarget Hlength]].
    change (length args = length (S.params (R.prepare p) (edge_target be))).
    rewrite Link.params_agree, (find_block_of_in _ _ _ Hunique Htarget).
    exact Hlength.
  Qed.

  Lemma pp_phi_edge_use p e be x : In e (C.edges (R.prepare p)) ->
    SP.block_edge_of (R.prepare p) e = Some be -> In x (SP.block_edge_args (R.prepare p) be) ->
    In x (U.uses (R.prepare p) e).
  Proof.
    intros He Hprojection Hx. rewrite pp_block_projection in Hprojection by exact He.
    destruct (pp_outgoing_shape p e be He Hprojection) as [body [args [Hitem [Hargs [Heq Hrow]]]]].
    assert (Hblockrow : In (be, args) (pp_block_rows p)).
    { unfold pp_block_rows; apply in_flat_map. exists (edge_source be, body); now split. }
    rewrite (pp_block_args_lookup p be args Hblockrow) in Hx.
    pose proof (pp_uses_lookup p _ Hrow) as Huses.
    change (U.uses (R.prepare p) e = guard_uses (term _ _ _ body) ++ args) in Huses.
    rewrite Huses. apply in_or_app; now right.
  Qed.

  Lemma pp_block_edge_covered p be : In be (BC.edges (R.prepare p)) ->
    exists e, In e (C.edges (R.prepare p)) /\ SP.block_edge_of (R.prepare p) e = Some be.
  Proof.
    intro Hbe. change (In be (map fst (pp_block_rows p))) in Hbe.
    apply in_map_iff in Hbe as [[edge args] [Heq Hrow]]; cbn in Heq; subst edge.
    unfold pp_block_rows in Hrow; apply in_flat_map in Hrow as [item [Hitem Hedge]].
    set (e := PointEdge (summary_exit (summarize (pp_params p) item)) (edge_target be, 0%N) (Some be)).
    assert (He : In e (C.edges (R.prepare p))).
    { change (In e (map (fun r => fst (fst r)) (pp_rows p))).
      apply in_map_iff. exists (e, guard_uses (term _ _ _ (snd item)) ++ args, []); split; [reflexivity|].
      unfold pp_rows; apply in_flat_map. exists (summarize (pp_params p) item); split.
      - unfold pp_summaries; now apply in_map.
      - apply in_or_app; right.
        change (In (e, guard_uses (term _ _ _ (snd item)) ++ args, ([] : list positive))
          (map (fun ea =>
            (PointEdge (summary_exit (summarize (pp_params p) item)) (edge_target (fst ea), 0%N)
              (Some (fst ea)), guard_uses (term _ _ _ (snd item)) ++ snd ea, ([] : list positive)))
            (listed_edge_args (pp_params p) (fst item) (term _ _ _ (snd item))))).
        apply in_map_iff. exists (be, args); now split. }
    exists e; split; [exact He|]. rewrite pp_block_projection by exact He; reflexivity.
  Qed.

  Lemma pp_block_edge_unique p e1 e2 be : In e1 (C.edges (R.prepare p)) ->
    In e2 (C.edges (R.prepare p)) -> SP.block_edge_of (R.prepare p) e1 = Some be ->
    SP.block_edge_of (R.prepare p) e2 = Some be -> e1 = e2.
  Proof.
    intros H1 H2 Hbe1 Hbe2.
    rewrite pp_block_projection in Hbe1 by exact H1.
    rewrite pp_block_projection in Hbe2 by exact H2.
    destruct (pp_outgoing_shape p e1 be H1 Hbe1) as [body1 [args1 [Hi1 [Ha1 [He1 Hr1]]]]].
    destruct (pp_outgoing_shape p e2 be H2 Hbe2) as [body2 [args2 [Hi2 [Ha2 [He2 Hr2]]]]].
    assert (Hbody : body1 = body2).
    { pose proof (find_block_of_in (pp_kept p) (edge_source be) body1 (pp_kept_unique p) Hi1) as Hfind1.
      pose proof (find_block_of_in (pp_kept p) (edge_source be) body2 (pp_kept_unique p) Hi2) as Hfind2.
      congruence. }
    subst body2. now rewrite He1, He2.
  Qed.

  Lemma pp_points_wf_complete p : ssa_wf p -> SP.wf (R.prepare p).
  Proof.
    intro Hssa. unfold SP.wf.
    split; [pose proof (prepared_wf p); tauto|].
    split; [exact (pp_point_out_unique p)|].
    split; [exact (pp_block_out_unique p)|].
    split; [exact (pp_points_covered p)|].
    split; [exact (pp_points_unique p)|].
    split; [exact (pp_point_owner p)|].
    split; [exact (pp_points_nonempty p)|].
    split; [exact (pp_points_ordered p)|].
    split; [exact (pp_instruction_internal p)|].
    split; [exact (pp_instruction_complete p)|].
    split; [exact (pp_parameter_first p)|].
    split; [exact (pp_parameter_defs p)|].
    split; [exact (pp_point_projection p)|].
    split; [intros be Hbe; exact (pp_phi_arity p be Hssa Hbe)|].
    split; [exact (pp_phi_edge_use p)|].
    split; [exact (pp_block_edge_covered p)|].
    exact (pp_block_edge_unique p).
  Qed.

  (** The point laws hold on the prepared form of an SSA function. *)
  Lemma points_wf : forall p, ssa_wf p -> SP.wf (R.prepare p).
  Proof.
    exact pp_points_wf_complete.
  Qed.
  (** The block presentation lists each block identifier at most once per listed block. *)
  Lemma block_nodes_le : forall p,
    length (BC.nodes (R.prepare p)) <= length (blocks _ _ _ p).
  Proof.
    intro p. rewrite Link.nodes_agree, length_map, first_blocks_selected.
    apply selected_blocks_length.
  Qed.
  (** Each listed block contributes at most its two exit edges. *)
  Lemma block_edges_le : forall p,
    length (BC.edges (R.prepare p)) <= 2 * length (BC.nodes (R.prepare p)).
  Proof.
    apply lang_edges_length.
  Qed.
  (** Presented block identifiers are identifiers of the syntax. *)
  Lemma block_bits_le : forall p b,
    (In b (BC.nodes (R.prepare p)) \/ exists e, In e (BC.edges (R.prepare p)) /\
      (BC.src (R.prepare p) e = b \/ BC.dst (R.prepare p) e = b)) ->
    PosKeyT.bits b <= function_width p.
  Proof.
    intros p b [Hnode|[e [Hedge Hside]]]; change (Pos.size_nat b <= function_width p).
    - apply function_id_width. rewrite Link.nodes_agree in Hnode.
      apply in_map_iff in Hnode. destruct Hnode as [[id body] [Heq Hin]].
      cbn in Heq; subst id. rewrite first_blocks_selected in Hin.
      apply selected_blocks_in in Hin as [Hin _].
      now apply (block_id_in_function p b body).
    - destruct (Link.edges_syntax p e Hedge) as [body [Hsource Htarget]].
      apply function_id_width. destruct Hside as [Heq|Heq]; subst b.
      + now apply (block_id_in_function p (BC.src (R.prepare p) e) body).
      + now apply (target_in_function p (BC.src (R.prepare p) e) body).
  Qed.
  (** Parameter rows of listed blocks and argument rows of listed edges are syntax. *)
  Lemma block_rows_le : forall p,
    fold_right (fun b n => length (SP.block_params (R.prepare p) b) + n) 0
      (BC.nodes (R.prepare p)) +
    fold_right (fun be n => length (SP.block_edge_args (R.prepare p) be) + n) 0
      (BC.edges (R.prepare p)) <= function_size p.
  Proof.
    intro p. pose proof (lang_block_rows_length p) as Hrows.
    rewrite !present_row_count_map in Hrows. exact Hrows.
  Qed.
  (** Points, point edges and variable occurrences are linear in the syntax. *)
  Lemma points_le : forall p,
    (N.of_nat (length (C.nodes (R.prepare p)) + length (C.edges (R.prepare p)) +
      length (U.occurrences (R.prepare p))) <=
      c_present * N.of_nat (function_size p + 1))%N.
  Proof.
    intro p. pose proof (lang_structure_length p) as Hstructure.
    change (length (C.nodes (R.prepare p)) + length (C.edges (R.prepare p)) <=
      5 * function_size p) in Hstructure.
    assert (Hocc : length (U.occurrences (R.prepare p)) <= 2 * length (function_vars p)).
    { exact (lang_occurrences_length p). }
    assert (Hsyntax : length (function_vars p) <= function_size p).
    { unfold function_size; lia. }
    assert (Hcount : length (C.nodes (R.prepare p)) + length (C.edges (R.prepare p)) +
      length (U.occurrences (R.prepare p)) <= 128 * (function_size p + 1)) by lia.
    unfold c_present. apply time_of_nat_le in Hcount.
    now rewrite Nat2N.inj_mul in Hcount.
  Qed.
  (** Occurring variables are identifiers of the syntax. *)
  Lemma occurrence_width_le : forall p,
    U.occurrence_width (R.prepare p) <= function_width p.
  Proof.
    intro p. unfold U.occurrence_width. apply present_max_bound.
    intros x Hin. change (Pos.size_nat x <= function_width p).
    apply function_id_width. unfold function_ids. right.
    apply in_or_app; left. apply (lang_occurrences_vars p x). exact Hin.
  Qed.
  (** Listed point keys are within a constant factor of the syntax width. *)
  Lemma point_bits_le : forall p n, In n (C.nodes (R.prepare p)) ->
    (N.of_nat (PointKey.bits n) <= c_present * N.of_nat (function_width p + 1))%N.
  Proof.
    intros p n Hin. pose proof (lang_point_key_width _ _ Hin) as Hwidth.
    unfold c_present. apply time_of_nat_le in Hwidth. rewrite Nat2N.inj_mul in Hwidth.
    nia.
  Qed.
  (** Listed edge keys are within a constant factor of the syntax width. *)
  Lemma edge_bits_le : forall p e, In e (C.edges (R.prepare p)) ->
    (N.of_nat (PointEdge.bits e) <= c_present * N.of_nat (function_width p + 1))%N.
  Proof.
    intros p e Hin. destruct (lang_point_edges_nodes _ _ Hin) as [Hsrc Hdst].
    pose proof (lang_point_key_width _ _ Hsrc) as Hsrc_key.
    pose proof (lang_point_key_width _ _ Hdst) as Hdst_key.
    assert (Hblock : forall be, point_block_edge e = Some be ->
      BlockEdge.bits be <= 4 * (function_width p + 1)).
    { intros be Hbe. destruct (lang_point_edge_block_sides _ _ _ Hin Hbe) as [Hs Ht].
      destruct (lang_point_bounds _ _ Hsrc) as [Hsrc_block _].
      destruct (lang_point_bounds _ _ Hdst) as [Hdst_block _].
      apply block_edge_width_from_ends; [now rewrite Hs|now rewrite Ht]. }
    assert (Hwidth : PointEdge.bits e <= 128 * (function_width p + 1)).
    { unfold PointEdge.bits, PointEdge.encode, point_edge_tuple,
        PointEdgeTupleKey.encode, PointTargetEdgeKey.encode, pair_code.
      cbn [fst snd]. rewrite !glue_bits.
      fold (PointKey.bits (point_src e)). fold (PointKey.bits (point_dst e)).
      destruct (point_block_edge e) as [be|] eqn:Hbe.
      - specialize (Hblock be eq_refl). cbn [OptionalBlockEdgeKey.encode option_code Pos.size_nat].
        fold (BlockEdge.bits be). lia.
      - cbn [OptionalBlockEdgeKey.encode option_code Pos.size_nat]. lia. }
    unfold c_present. apply time_of_nat_le in Hwidth.
    now rewrite Nat2N.inj_mul in Hwidth.
  Qed.
  (** Listed block-edge keys are within a constant factor of the syntax width. *)
  Lemma block_edge_bits_le : forall p e, In e (BC.edges (R.prepare p)) ->
    (N.of_nat (BlockEdge.bits e) <= c_present * N.of_nat (function_width p + 1))%N.
  Proof.
    intros p e Hin.
    assert (Hsource : Pos.size_nat (edge_source e) <= function_width p).
    { apply (block_bits_le p (edge_source e)). right; exists e; split; [exact Hin|].
      left; reflexivity. }
    assert (Htarget : Pos.size_nat (edge_target e) <= function_width p).
    { apply (block_bits_le p (edge_target e)). right; exists e; split; [exact Hin|].
      right; reflexivity. }
    unfold c_present.
    assert (Hbits : BlockEdge.bits e <= 128 * (function_width p + 1)).
    { unfold BlockEdge.bits, BlockEdge.encode, block_edge_tuple,
        EdgeTupleKey.encode, EdgeArmTargetKey.encode, pair_code.
      cbn [fst snd PosKeyT.encode]. rewrite !glue_bits.
      destruct (edge_arm e); cbn [ArmKeyT.encode Pos.size_nat]; lia. }
    apply time_of_nat_le in Hbits. rewrite Nat2N.inj_mul in Hbits. exact Hbits.
  Qed.

  End Budget.
End PresentT.
