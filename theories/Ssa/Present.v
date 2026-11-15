(** * Language control-flow occurrences

    Edges retain the source block and the selected exit arm.
    For example, two arms aimed at the same block remain distinct.
    Builds on: Ssa.Lang. *)

From Stdlib Require Import List PArith NArith ZArith Bool Lia Arith.
From Argent Require Import Time Tactics Std BigO.
From Galois.Base Require Import Code KeySig Key Trie.
From Galois.Graph Require Import DigraphSig.
From Galois.Program Require Import CfgSig VarsSig Vars SsaSig Ssa.
From Galois.Ssa Require Import Lang LiveSig ValidateSig.
Import List.ListNotations.

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

(** A multi-table lists every row of a key in row order. *)
Definition multi_table {A} (key : A -> positive) (rows : list A) : ptrie (list A) :=
  fold_right (fun r m => PTrieCode.set (key r) (r :: index_row m (key r)) m) Empty rows.
TimeFun multi_table.

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

Module PrepareT (O : OPS) (Q : TYPE with Definition t := lang_prepared O.K O.G)
    <: LANG_PREPARE_T O Q.
  Include PrepareCode O Q.
  TimeFun prepare.
  Definition c_prepare : N := 1. (* STUB *)
  Lemma T_prepare_le : forall p,
    (T_prepare p <= c_prepare * N.of_nat (function_size p + 1) *
      N.of_nat (function_width p + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma prepare_bigO : bigO (fun _ : func positive O.K O.G => True)
    (fun p => N.of_nat ((function_size p + 1) * (function_width p + 1))) T_prepare.
  Proof. Admitted. (* STUB *)
End PrepareT.

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

(* F2-100 retires the former edge, adjacency and parameter scan SIG-QUESTIONs. *)
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
    time_unfold PosKeyT.T_encode. rewrite PTrieT.trie_get_clock.
    rewrite !Nat2N.inj_add. time_cbn.
    unfold PosKeyT.bits, PosKeyT.encode, PosKeyCode.encode; nia.
  Qed.
  Lemma T_inc_le : forall p n,
    (T_inc p n <= c_cfg_adj * N.of_nat (PosKeyT.bits n + length (inc p n) + 1))%N.
  Proof.
    intros p n. unfold c_cfg_adj. time_unfold T_inc.
    time_unfold @T_lang_inc. time_unfold @T_index_row.
    time_unfold PosKeyT.T_encode. rewrite PTrieT.trie_get_clock.
    rewrite !Nat2N.inj_add. time_cbn.
    unfold PosKeyT.bits, PosKeyT.encode, PosKeyCode.encode; nia.
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
    rewrite PTrieT.trie_get_clock.
    change (1 + (1 + PointKey.T_encode n +
      (1 + 2 * N.of_nat (PointKey.bits n))) <=
      8 * (PointKey.c_key + 1) *
      N.of_nat (PointKey.bits n + length (out p n) + 1))%N.
    rewrite !Nat2N.inj_add in *; nia.
  Qed.
  Lemma T_inc_le : forall p n,
    (T_inc p n <= c_cfg_adj * N.of_nat (PointKey.bits n + length (inc p n) + 1))%N.
  Proof.
    intros p n. pose proof (PointKey.T_encode_le n) as Hkey.
    unfold c_cfg_adj. time_unfold T_inc.
    time_unfold @T_lang_point_inc. time_unfold @T_index_row.
    rewrite PTrieT.trie_get_clock.
    change (1 + (1 + PointKey.T_encode n +
      (1 + 2 * N.of_nat (PointKey.bits n))) <=
      8 * (PointKey.c_key + 1) *
      N.of_nat (PointKey.bits n + length (inc p n) + 1))%N.
    rewrite !Nat2N.inj_add in *; nia.
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
    Lemma wf_from_lang : forall p, ssa_wf p -> S.wf (R.prepare p).
    Proof. Admitted. (* STUB *)
  End Link.

  Module Budget <: LANG_PRESENT_BUDGET O Q R BlockEdge PointEdge PointKey BC C U SP.
    Definition c_present : N := 128.

  (** Both prepared graphs are well formed for every raw function. *)
  Lemma prepared_wf : forall p, BC.wf (R.prepare p) /\ C.wf (R.prepare p).
  Proof.
    intro p; split; reflexivity.
  Qed.
  (** The point laws hold on the prepared form of an SSA function. *)
  Lemma points_wf : forall p, ssa_wf p -> SP.wf (R.prepare p).
  Proof. Admitted. (* STUB *)
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
