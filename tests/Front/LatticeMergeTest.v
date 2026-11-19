(** * Lawful merges of lattice tables

    The merges of [LatticeMerge.v] on two programs: shortest paths over [positive] with the
    merge [Pos.min], and reaching definitions over [N] with the merge [N.lor]. A lawful merge
    agrees with the merge of the primitives on encodings, so the glue lemmas and the proof that
    shortest paths are monotone move to it, and the theorems of [LatticeReadSig.v] apply to a
    value module with it. For example, the lawful merge of [N.lor] takes the encodings of the
    sets [1] and [2] to the encoding of [3], as the primitive does.

    Groups:
    - [LiftTests] The lawful merge of [N.lor] on encodings, on positives that encode no value
      and at another code.
    - [RunTests] Runs with the lawful merges store the values of the runs with the merges of the
      primitives.
    - [TransferTests] The glue of both programs and the monotonicity of shortest paths move to
      the lawful merges, and the completeness of lattice reads applies to shortest paths.

    Builds on: the lawful merges, the derive command, the meaning of lattice reads, the theorems
    of lattice reads, the runner and the engine. *)

From Stdlib Require Import List PArith NArith Lia.
From Galois.Base Require Import Key.
From Galois.Egglog Require Import ValueSig Syntax Model Index Join Database Run.
From Galois.Front Require Import Spec SpecLattice LowerSig Lower RunnerSig Runner RunnerFacts
  Derive Encode LatticeReadSig LatticeRead LatticeMergeSig LatticeMerge.
Import List.ListNotations.

(** * Fixtures *)

(** Addition and the minimum of positives. *)
Egglog Primitives Ops Pos.add Pos.min.

(** An edge from a source node to a target node, with a weight. *)
Inductive edge : Type :=
  | Edge (source target weight : positive).

(** [dist edges a b d] says that some path from [a] to [b] has length [d]. *)
Inductive dist (edges : list edge) : positive -> positive -> positive -> Prop :=
  | dist_edge a b w : In (Edge a b w) edges -> dist edges a b w
  | dist_step a b c d w : dist edges a b d -> In (Edge b c w) edges ->
      dist edges a c (Pos.add d w).

Egglog Paths from dist with Ops merge dist Pos.min.

(** The union of two sets of definitions, as the bitwise or of their bits. *)
Egglog Primitives SetOps N.lor.

(** Node [n] defines the set [s] of variables, as bits, or control flows between two nodes. *)
Inductive flow_fact : Type :=
  | Gen (node : positive) (defs : N)
  | Flow (source target : positive).

(** [reaching facts n s] says that the definitions of [s] may reach node [n]. *)
Inductive reaching (facts : list flow_fact) : positive -> N -> Prop :=
  | reaching_gen n s : In (Gen n s) facts -> reaching facts n s
  | reaching_flow m n s : reaching facts m s -> In (Flow m n) facts -> reaching facts n s
  | reaching_union n s t : reaching facts n s -> reaching facts n t ->
      reaching facts n (N.lor s t).

Egglog Reaching from reaching with SetOps merge reaching N.lor.

(** The minimum of positives, at the code of [Pos.min]. *)
Module MinJoin <: DECODED Ops PosEncode.
  Definition code := Ops.min_code.
  Definition join := Pos.min.

  Lemma join_comm : forall a b, join a b = join b a.
  Proof.
    exact Pos.min_comm.
  Qed.

  Lemma join_assoc : forall a b c, join a (join b c) = join (join a b) c.
  Proof.
    exact Pos.min_assoc.
  Qed.

  Lemma join_idem : forall a, join a a = a.
  Proof.
    exact Pos.min_id.
  Qed.

  Lemma prim_join : forall x y,
    Ops.prim code [PosEncode.encode x; PosEncode.encode y] = Some (PosEncode.encode (join x y)).
  Proof.
    reflexivity.
  Qed.
End MinJoin.

Module PathMerge0 := MaxMerge Ops.
Module PathMerge := DecodedMerge Ops PathMerge0 PosEncode MinJoin.

(** The values of shortest paths, with the lawful merge of [Pos.min]. *)
Module PathValue := MergeValue Ops PathMerge.

(** The union of sets of bits, at the code of [N.lor]. *)
Module LorJoin <: DECODED SetOps NEncode.
  Definition code := SetOps.lor_code.
  Definition join := N.lor.

  Lemma join_comm : forall a b, join a b = join b a.
  Proof.
    exact N.lor_comm.
  Qed.

  Lemma join_assoc : forall a b c, join a (join b c) = join (join a b) c.
  Proof.
    exact N.lor_assoc.
  Qed.

  Lemma join_idem : forall a, join a a = a.
  Proof.
    exact N.lor_diag.
  Qed.

  Lemma prim_join : forall x y,
    SetOps.prim code [NEncode.encode x; NEncode.encode y] = Some (NEncode.encode (join x y)).
  Proof.
    intros [| p] [| q]; reflexivity.
  Qed.
End LorJoin.

Module SetMerge0 := MaxMerge SetOps.
Module SetMerge := DecodedMerge SetOps SetMerge0 NEncode LorJoin.

(** The values of reaching definitions, with the lawful merge of [N.lor]. *)
Module SetValue := MergeValue SetOps SetMerge.

Module PathIndex := IndexCode PathValue.
Module PathJoin := JoinCode PathValue PathIndex.
Module PathDatabase := DatabaseCode PathValue PathIndex.
Module PathRun := RunCode PathValue PathIndex PathJoin PathDatabase.
Module PathRunner := RunnerCode PathValue PathIndex PathJoin PathDatabase PathRun.

Module SetIndex := IndexCode SetValue.
Module SetJoin := JoinCode SetValue SetIndex.
Module SetDatabase := DatabaseCode SetValue SetIndex.
Module SetRun := RunCode SetValue SetIndex SetJoin SetDatabase.
Module SetRunner := RunnerCode SetValue SetIndex SetJoin SetDatabase SetRun.

(** The value that a database of shortest paths stores at a key, if it stores one. *)
Definition path_stored (f : positive) (ks : list positive) (db : PathDatabase.t) :
    option positive :=
  match fst (PathDatabase.lookup f (map Val ks) db) with
  | Some (Some (Val v)) => Some v
  | _ => None
  end.

(** The value that a database of reaching definitions stores at a key, if it stores one. *)
Definition set_stored (f : positive) (ks : list positive) (db : SetDatabase.t) :
    option positive :=
  match fst (SetDatabase.lookup f (map Val ks) db) with
  | Some (Some (Val v)) => Some v
  | _ => None
  end.

(** Saturation stops after at most 50 iterations and allocates at most 1000 identifiers. *)
Definition example_limits : limits := Limits 50%N 1000%N.

(** The edges from 1 to 2 and from 2 to 3 of weight 1, and the edge from 1 to 3 of weight 5. *)
Definition triangle : list edge := [Edge 1 2 1; Edge 2 3 1; Edge 1 3 5].

(** Node 1 defines the set {0} and node 2 the set {1}, as bits, and both flow into node 3. *)
Definition join_facts : list flow_fact := [Gen 1 1%N; Gen 2 2%N; Flow 1 3; Flow 2 3].

(** * Lifted joins *)

Module LiftTests.

  Local Open Scope positive_scope.

  (** The lawful merge takes the encodings of {0} and {1} to the encoding of {0, 1}. *)
  Example union_of_encodings :
    SetValue.merge SetOps.lor_code (NEncode.encode 1%N) (NEncode.encode 2%N) =
      NEncode.encode 3%N.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The positive 3 encodes no value of [N], so it is below the encoding of {0}. *)
  Example non_encoding_is_below_an_encoding :
    SetValue.merge SetOps.lor_code 3 (NEncode.encode 1%N) = NEncode.encode 1%N.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Two positives that encode no value merge to the larger one, in either order. *)
  Example non_encodings_merge_to_the_larger :
    SetValue.merge SetOps.lor_code 3 5 = 5 /\ SetValue.merge SetOps.lor_code 5 3 = 5.
  Proof.
    vm_compute. auto.
  Qed.

  (** The merge of the primitives returns its first argument on the same two positives, so it
      is not commutative. *)
  Example primitive_merge_keeps_the_first :
    prim_merge SetOps.prim SetOps.lor_code 3 5 = 3 /\
    prim_merge SetOps.prim SetOps.lor_code 5 3 = 5.
  Proof.
    vm_compute. auto.
  Qed.

  (** At a code without a join, the lawful merge is the maximum. *)
  Example other_code_merges_by_maximum :
    SetValue.merge (Pos.succ SetOps.lor_code) (NEncode.encode 1%N) (NEncode.encode 2%N) =
      NEncode.encode 2%N.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** At the code of [Pos.min], the lawful merge of positives is the minimum. *)
  Example positives_merge_by_minimum :
    PathValue.merge Ops.min_code 7 4 = 4.
  Proof.
    vm_compute. reflexivity.
  Qed.

End LiftTests.

(** * Runs *)

Module RunTests.

  Local Open Scope positive_scope.

  (** The run of shortest paths on the triangle with the lawful merge. *)
  Definition triangle_run : stop * PathDatabase.t :=
    PathRunner.solve Paths.program (Paths.facts triangle) example_limits.

  (** The run of reaching definitions on the joined flows with the lawful merge. *)
  Definition union_run : stop * SetDatabase.t :=
    SetRunner.solve Reaching.program (Reaching.facts join_facts) example_limits.

  (** The run of shortest paths saturates. *)
  Example paths_saturate :
    fst triangle_run = Saturated.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The path through 2 gives the stored distance 2 from 1 to 3. *)
  Example shortest_distance_is_stored :
    path_stored Paths.dist_code [1; 3] (snd triangle_run) = Some 2.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The run of reaching definitions saturates. *)
  Example sets_saturate :
    fst union_run = Saturated.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Node 3 stores the union {0, 1} of the two sets that reach it. *)
  Example union_is_stored :
    set_stored Reaching.reaching_code [3] (snd union_run) = Some (NEncode.encode 3%N).
  Proof.
    vm_compute. reflexivity.
  Qed.

End RunTests.

(** * Transfer *)

Module TransferTests.

  Local Open Scope positive_scope.

  (** The merge code of each lattice table of shortest paths is the code of [Pos.min]. *)
  Lemma paths_merge_at_min : forall f m,
    lookup_kind (tables Paths.spec) f = Some (OLat m) -> m = Ops.min_code.
  Proof.
    intros f m Hkind.
    pose proof (lookup_kind_lat_codes _ f m Hkind) as Hin.
    vm_compute in Hin.
    destruct Hin as [Hm | []].
    symmetry. exact Hm.
  Qed.

  (** The merge code of each lattice table of reaching definitions is the code of [N.lor]. *)
  Lemma sets_merge_at_lor : forall f m,
    lookup_kind (tables Reaching.spec) f = Some (OLat m) -> m = SetOps.lor_code.
  Proof.
    intros f m Hkind.
    pose proof (lookup_kind_lat_codes _ f m Hkind) as Hin.
    vm_compute in Hin.
    destruct Hin as [Hm | []].
    symmetry. exact Hm.
  Qed.

  (** The merge of the primitives at the code of [Pos.min] is the minimum. *)
  Lemma min_code_merges_by_min : forall a b, prim_merge Ops.prim Ops.min_code a b = Pos.min a b.
  Proof.
    reflexivity.
  Qed.

  (** The primitive at the code of [Pos.add] adds. *)
  Lemma add_code_adds : forall a b, Ops.prim Ops.add_code [a; b] = Some (Pos.add a b).
  Proof.
    reflexivity.
  Qed.

  (** At the code of [Pos.min], the lawful merge agrees with the merge of the primitives at
      every value, because every positive encodes itself. *)
  Lemma path_merges_agree : forall f m a b, lookup_kind (tables Paths.spec) f = Some (OLat m) ->
    prim_merge Ops.prim m a b = PathValue.merge m a b.
  Proof.
    intros f m a b Hkind.
    rewrite (paths_merge_at_min f m Hkind).
    symmetry. exact (PathMerge.merge_agrees_code a b).
  Qed.

  (** Case on an environment [e'] that raises the reads of [e], at a variable [x] that the goal
      reads. Either [e'] agrees with [e] there, or the body of the clause reads [x], which gives
      its table, its merge and the order of the two values. *)
  Local Ltac raise_at Hbelow Hvalue x :=
    let Hx := fresh "Hx" in
    let Hread := fresh "Hread" in
    let Hkind := fresh "Hkind" in
    let He := fresh "He" in
    let He' := fresh "He'" in
    let Hle := fresh "Hle" in
    destruct (Hbelow x) as [Hx | [? [? [? [? [? [Hread [Hkind [He [He' Hle]]]]]]]]]];
    [ rewrite Hx
    | simpl in Hread;
      repeat match type of Hread with
             | _ \/ _ => destruct Hread as [Hread | Hread]
             end;
      try contradiction; try discriminate Hread;
      injection Hread; intros; subst;
      simpl in Hkind; injection Hkind; intros; subst;
      rewrite He'; rewrite He in Hvalue; rewrite min_code_merges_by_min in Hle ].

  (** Shortest paths is monotone with the merge of the primitives: a longer distance read gives
      a longer distance assigned, in the order of [Pos.min]. *)
  Lemma paths_monotone : monotone Ops.prim (prim_merge Ops.prim) Paths.spec.
  Proof.
    intros c f args v m e e' u Hin Hhead Hkind Hbelow Hvalue.
    simpl in Hin.
    destruct Hin as [Hc | [Hc | []]]; subst c; simpl in Hhead;
      injection Hhead as Hf Hargs Hv; subst f args v; simpl in Hkind;
      injection Hkind as Hm; subst m; cbn [pat_value] in Hvalue |- *;
      repeat match goal with
             | |- context [e' ?x] => raise_at Hbelow Hvalue x
             end.
    all: first
      [ solve [exists u; split; [exact Hvalue | rewrite min_code_merges_by_min; apply Pos.min_id]]
      | cbv beta iota in Hvalue |- *;
        repeat match goal with
               | H : context [match ?read with _ => _ end] |- _ =>
                   lazymatch read with
                   | ?env _ => is_var env
                   end;
                   destruct read eqn:?; cbv beta iota in Hvalue |- *; try discriminate Hvalue
               end;
        rewrite add_code_adds in Hvalue; rewrite add_code_adds;
        injection Hvalue as Hu; subst u;
        eexists; split; [reflexivity |];
        rewrite min_code_merges_by_min; apply Pos.min_r;
        match goal with
        | Hle : Pos.min _ _ = _ |- _ => apply Pos.min_r_iff in Hle
        end;
        lia ].
  Qed.

  (** [monotone_agrees] moves the monotonicity of shortest paths to the lawful merge. *)
  Example paths_monotone_lawful :
    monotone Ops.prim PathValue.merge Paths.spec.
  Proof.
    exact (monotone_agrees Ops.prim (prim_merge Ops.prim) PathValue.merge Paths.spec
      path_merges_agree paths_monotone).
  Qed.

  (** [lat_merge_agrees_on] moves the glue of shortest paths to the lawful merge, with a
      predicate that holds of every positive. *)
  Example dist_spec_lawful : forall edges a b d,
    dist edges a b d <->
      lat_assigned Ops.prim PathValue.merge Paths.spec (Paths.inputs edges) Paths.dist_code
        [a; b] d.
  Proof.
    intros edges a b d.
    rewrite (Paths.dist_spec edges a b d).
    apply (lat_merge_agrees_on Ops.prim (prim_merge Ops.prim) PathValue.merge (fun _ => True)).
    - intros f m x y Hkind _ _. exact (path_merges_agree f m x y Hkind).
    - intros. exact I.
    - intros. exact I.
  Qed.

  (** [lat_merge_agrees_on] moves the glue of reaching definitions to the lawful merge, with the
      predicate of the encodings of [N], which [Reaching.closed] gives for every assigned
      value. *)
  Example reaching_spec_lawful : forall facts n s,
    reaching facts n s <->
      lat_assigned SetOps.prim SetValue.merge Reaching.spec (Reaching.inputs facts)
        Reaching.reaching_code [n] (NEncode.encode s).
  Proof.
    intros facts n s.
    rewrite (Reaching.reaching_spec facts n s).
    apply (lat_merge_agrees_on SetOps.prim (prim_merge SetOps.prim) SetValue.merge
      (fun v => exists x, v = NEncode.encode x)).
    - intros f m a b Hkind [x Hx] [y Hy].
      rewrite (sets_merge_at_lor f m Hkind).
      subst a b.
      symmetry. exact (SetMerge.merge_agrees_code x y).
    - intros f m a b Hkind [x Hx] [y Hy].
      rewrite (sets_merge_at_lor f m Hkind).
      subst a b.
      exists (N.lor x y). exact (SetMerge.prim_merge_code x y).
    - intros f ks w Hw.
      destruct (proj2 (Reaching.closed facts) f ks w Hw) as [_ [k [x [_ [Hx _]]]]].
      exists x. exact Hx.
  Qed.

  (** [MergeValue.lat_merge_moves] moves the glue of reaching definitions as well, from the
      codes of the lawful merge and the encodings at them. *)
  Example reaching_spec_moved : forall facts n s,
    reaching facts n s <->
      lat_assigned SetOps.prim SetValue.merge Reaching.spec (Reaching.inputs facts)
        Reaching.reaching_code [n] (NEncode.encode s).
  Proof.
    intros facts n s.
    rewrite (Reaching.reaching_spec facts n s).
    apply SetValue.lat_merge_moves.
    - intros f m Hkind.
      apply (lat_codes_covered (tables Reaching.spec) SetMerge.codes f m);
        [vm_compute; reflexivity | exact Hkind].
    - intros f m ks w Hkind Hw.
      rewrite (sets_merge_at_lor f m Hkind).
      apply SetMerge.encoded_code.
      destruct (proj2 (Reaching.closed facts) f ks w Hw) as [_ [k [x [_ [Hx _]]]]].
      exists x. exact Hx.
  Qed.

  Module PathIndexLaws := Index PathValue.
  Module PathJoinLaws := Join PathValue PathIndexLaws.
  Module PathDatabaseLaws := Database PathValue PathIndexLaws.
  Module PathRunLaws := Run PathValue PathIndexLaws PathJoinLaws PathDatabaseLaws.
  Module PathRunnerLaws :=
    Runner PathValue PathIndexLaws PathJoinLaws PathDatabaseLaws PathRunLaws.
  Module PathFacts :=
    RunnerFacts PathValue PathIndexLaws PathJoinLaws PathDatabaseLaws PathRunLaws PathRunnerLaws.
  Module PathTheorems := LatticeRead PathValue PathIndexLaws PathJoinLaws PathDatabaseLaws
    PathRunLaws PathRunnerLaws PathFacts LowerLaws LowerPlan.

  (** With the lawful merge, [solve_complete] says that a saturated run stores at [[1; 3]] a
      distance below the length of every path from 1 to 3. *)
  Example stored_distance_is_shortest : forall db d,
    PathRunnerLaws.solve Paths.program (Paths.facts triangle) example_limits =
      (Saturated, db) ->
    dist triangle 1 3 d ->
    exists v, row (PathDatabaseLaws.view db) Paths.dist_code [Val 1; Val 3] (Some (Val v)) /\
      PathValue.merge Ops.min_code d v = v.
  Proof.
    intros db d Hsolve Hd.
    apply (PathTheorems.solve_complete Paths.spec (Paths.facts triangle) example_limits db
      Paths.dist_code Ops.min_code [1; 3] d).
    - vm_compute. reflexivity.
    - vm_compute. reflexivity.
    - vm_compute. reflexivity.
    - vm_compute. reflexivity.
    - exact paths_monotone_lawful.
    - vm_compute. reflexivity.
    - exact Hsolve.
    - exact (proj1 (dist_spec_lawful triangle 1 3 d) Hd).
  Qed.

End TransferTests.
