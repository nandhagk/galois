(** * Lattice tables in derived programs

    Programs with lattice tables, written as inductives and derived with
    [Egglog P from R with Ops merge R g]. A lattice table keeps at each key the merge of the
    values that its constructors assign there, and a premise over it reads the stored value.
    [dist] is shortest paths, with [Pos.min] as its merge, [heaviest] keeps the heaviest edge out
    of each node with [Pos.max], and [longest] is the longest path with [Pos.max]. [reaching] joins
    sets of definitions with [N.lor], a merge that in general returns neither of its arguments.
    For example, the edges from 1 to 2 and from 2 to 3 of weight 1 and the edge from 1 to 3 of
    weight 5 give the stored distance 2 from 1 to 3.

    Groups:
    - [DeclarationTests] A lattice relation is a table of kind [OLat] with the code of its merge,
      its constructors assign values and its premises read them.
    - [ShortestPathTests] The stored distances are the shortest ones.
    - [RowTests] A relation over values derives its rows from the values that it reads.
    - [AggregationTests] A maximum over the inputs, without reads.
    - [UnionTests] A merge that returns neither of its arguments.
    - [SaturationTests] A run saturates only when each key has a merge above every value.
    - [GlueTests] The generated lemmas relate the inductives and the meaning of the tables.
    - [ConditionTests] The conditions of the theorems of [LatticeReadSig.v], and a saturated
      run that misses a value when a read value is a key.
    - [RejectionTests] The command stops at a malformed declaration of a lattice table.

    Builds on: the derive command, the meaning of lattice reads, the conditions of their
    theorems, the runner and the engine. *)

From Stdlib Require Import List PArith NArith ZArith Lia.
From Galois.Base Require Import Key.
From Galois.Egglog Require Import ValueSig Syntax Model Index Join Database Run.
From Galois.Front Require Import Spec SpecLattice LowerSig RunnerSig Runner Derive Encode
  LatticeSig LatticeReadSig.
Import List.ListNotations.

(** * Fixtures *)

(** Addition, the minimum and the maximum of positives. *)
Egglog Primitives Ops Pos.add Pos.min Pos.max.

(** An edge from a source node to a target node, with a weight. *)
Inductive edge : Type :=
  | Edge (source target weight : positive).

(** [dist edges a b d] says that some path from [a] to [b] has length [d]. *)
Inductive dist (edges : list edge) : positive -> positive -> positive -> Prop :=
  | dist_edge a b w : In (Edge a b w) edges -> dist edges a b w
  | dist_step a b c d w : dist edges a b d -> In (Edge b c w) edges ->
      dist edges a c (Pos.add d w).

Egglog Paths from dist with Ops merge dist Pos.min.

(** [reach edges a b] says that some path leads from [a] to [b]. It reads the distances. *)
Inductive reach (edges : list edge) : positive -> positive -> Prop :=
  | reach_dist a b d : dist edges a b d -> reach edges a b.

Egglog Reach from dist reach with Ops merge dist Pos.min.

(** [heaviest edges a w] says that some edge out of [a] has the weight [w]. *)
Inductive heaviest (edges : list edge) : positive -> positive -> Prop :=
  | heaviest_edge a b w : In (Edge a b w) edges -> heaviest edges a w.

Egglog Heaviest from heaviest with Ops merge heaviest Pos.max.

(** [longest edges a b d] says that some path from [a] to [b] has length [d]. Its merge keeps
    the longest length. *)
Inductive longest (edges : list edge) : positive -> positive -> positive -> Prop :=
  | longest_edge a b w : In (Edge a b w) edges -> longest edges a b w
  | longest_step a b c d w : longest edges a b d -> In (Edge b c w) edges ->
      longest edges a c (Pos.add d w).

Egglog Longest from longest with Ops merge longest Pos.max.

(** The union of two sets of definitions, as the bitwise or of their bits. *)
Egglog Primitives SetOps N.lor.

(** A fact of a flow graph: node [n] defines the set [s], as bits, or control flows from one
    node to another. *)
Inductive flow_fact : Type :=
  | Gen (node : positive) (defs : N)
  | Flow (source target : positive).

(** [reaching facts n s] says that the definitions of [s] may reach node [n]. Two sets that
    reach a node reach it together. *)
Inductive reaching (facts : list flow_fact) : positive -> N -> Prop :=
  | reaching_gen n s : In (Gen n s) facts -> reaching facts n s
  | reaching_flow m n s : reaching facts m s -> In (Flow m n) facts -> reaching facts n s
  | reaching_union n s t : reaching facts n s -> reaching facts n t ->
      reaching facts n (N.lor s t).

Egglog Reaching from reaching with SetOps merge reaching N.lor.

(** The values of [Ops] are positives, and the merge of a lattice table is its primitive. *)
Module OpsValue <: VALUE_OPS.
  Include PosKeyCode.
  Definition prim := Ops.prim.
  Definition merge := prim_merge Ops.prim.
End OpsValue.

Module OpsIndex := IndexCode OpsValue.
Module OpsJoin := JoinCode OpsValue OpsIndex.
Module OpsDatabase := DatabaseCode OpsValue OpsIndex.
Module OpsRun := RunCode OpsValue OpsIndex OpsJoin OpsDatabase.
Module OpsRunner := RunnerCode OpsValue OpsIndex OpsJoin OpsDatabase OpsRun.

(** The values of [SetOps] are encodings of natural numbers. *)
Module SetValue <: VALUE_OPS.
  Include PosKeyCode.
  Definition prim := SetOps.prim.
  Definition merge := prim_merge SetOps.prim.
End SetValue.

Module SetIndex := IndexCode SetValue.
Module SetJoin := JoinCode SetValue SetIndex.
Module SetDatabase := DatabaseCode SetValue SetIndex.
Module SetRun := RunCode SetValue SetIndex SetJoin SetDatabase.
Module SetRunner := RunnerCode SetValue SetIndex SetJoin SetDatabase SetRun.

(** The value that a database of [Ops] stores at a key of a lattice table, if it stores one. *)
Definition stored (f : positive) (ks : list positive) (db : OpsDatabase.t) : option positive :=
  match fst (OpsDatabase.lookup f (map Val ks) db) with
  | Some (Some (Val v)) => Some v
  | _ => None
  end.

(** The value that a database of [SetOps] stores at a key of a lattice table, if it stores
    one. *)
Definition set_stored (f : positive) (ks : list positive) (db : SetDatabase.t) :
    option positive :=
  match fst (SetDatabase.lookup f (map Val ks) db) with
  | Some (Some (Val v)) => Some v
  | _ => None
  end.

(** Saturation stops after at most 50 iterations and allocates at most 1000 identifiers. *)
Definition example_limits : limits := Limits 50%N 1000%N.

(** The edges from 1 to 2 and from 2 to 3 of weight 1, and the edge from 1 to 3 of weight 5.
    The path through 2 is shorter than the direct edge. *)
Definition triangle : list edge := [Edge 1 2 1; Edge 2 3 1; Edge 1 3 5].

(** The edges from 1 to 2 and from 2 to 1, of weight 1 each. *)
Definition cycle : list edge := [Edge 1 2 1; Edge 2 1 1].

(** Node 1 defines the set {0} and node 2 the set {1}, as bits, and both flow into node 3. *)
Definition join_facts : list flow_fact := [Gen 1 1%N; Gen 2 2%N; Flow 1 3; Flow 2 3].

(** * Declarations *)

Module DeclarationTests.

  (** The kind of the head of a clause. *)
  Variant head_kind : Type :=
    | KindDerive
    | KindAssign
    | KindOther.

  Definition kind_of (c : clause positive) : head_kind :=
    match head c with
    | Derive _ _ => KindDerive
    | Assign _ _ _ => KindAssign
    | _ => KindOther
    end.

  (** The tables that the premises of a clause read as lattice values, in order. *)
  Definition read_tables (c : clause positive) : list positive :=
    flat_map (fun p => match p with Equals f _ _ => [f] | _ => [] end) (body c).

  (** The lattice relation is a table of kind [OLat] with the code of [Pos.min], and the input
      list is a relation. *)
  Example dist_is_a_lattice_table :
    map out (tables Paths.spec) = [OLat Ops.min_code; ORel].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The keys of the lattice table are the indices before its value. *)
  Example keys_are_the_first_indices :
    map arg_sorts (tables Paths.spec) = [[SVal; SVal]; [SVal; SVal; SVal]].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Both constructors of the lattice relation assign a value. *)
  Example constructors_assign_values :
    map kind_of (clauses Paths.spec) = [KindAssign; KindAssign].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The step constructor reads the lattice table, and the edge constructor reads none. *)
  Example step_reads_the_distances :
    map read_tables (clauses Paths.spec) = [[]; [Paths.dist_code]].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A relation that reads a lattice table derives rows. *)
  Example relation_beside_a_lattice_derives_rows :
    map kind_of (clauses Reach.spec) = [KindAssign; KindAssign; KindDerive].
  Proof.
    vm_compute. reflexivity.
  Qed.

End DeclarationTests.

(** * Shortest paths *)

Module ShortestPathTests.

  Local Open Scope positive_scope.

  (** The run of shortest paths on the triangle. *)
  Definition triangle_run : stop * OpsDatabase.t :=
    OpsRunner.solve Paths.program (Paths.facts triangle) example_limits.

  (** The edges from 1 to 2 of weight 5, from 1 to 3 and from 3 to 2 of weight 1, and from 2
      to 4 of weight 1. The distance to 2 shrinks after the run first reaches 4. *)
  Definition detour : list edge := [Edge 1 2 5; Edge 1 3 1; Edge 3 2 1; Edge 2 4 1].

  (** The run of shortest paths on the detour. *)
  Definition detour_run : stop * OpsDatabase.t :=
    OpsRunner.solve Paths.program (Paths.facts detour) example_limits.

  (** The run of shortest paths on the cycle. *)
  Definition cycle_run : stop * OpsDatabase.t :=
    OpsRunner.solve Paths.program (Paths.facts cycle) example_limits.

  (** No rule changes a stored distance at the end, so the run saturates. *)
  Example triangle_saturates :
    fst triangle_run = Saturated.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The path through 2, of length 2, gives the stored distance from 1 to 3. *)
  Example shortest_distance_is_stored :
    stored Paths.dist_code [1; 3] (snd triangle_run) = Some 2.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The direct edge from 1 to 3 is a longer path, and its length 5 is not stored. *)
  Example longer_path_is_not_stored :
    stored Paths.dist_code [1; 3] (snd triangle_run) <> Some 5.
  Proof.
    vm_compute. discriminate.
  Qed.

  (** No path leads from 3 back to 1, so no distance is stored there. *)
  Example unreachable_pair_has_no_distance :
    stored Paths.dist_code [3; 1] (snd triangle_run) = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The shorter distance to 2 through 3 reaches 4 as well, so the distance from 1 to 4 is 3
      and not 6. *)
  Example shorter_distance_propagates :
    stored Paths.dist_code [1; 4] (snd detour_run) = Some 3.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The paths around a cycle grow without bound, and the minimum still stops the run. *)
  Example cycle_saturates :
    fst cycle_run = Saturated.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The shortest path from 1 back to 1 goes around the cycle once. *)
  Example shortest_cycle_is_stored :
    stored Paths.dist_code [1; 1] (snd cycle_run) = Some 2.
  Proof.
    vm_compute. reflexivity.
  Qed.

End ShortestPathTests.

(** * Rows that read lattice values *)

Module RowTests.

  Local Open Scope positive_scope.

  (** The run of reachability through the distances on the triangle. *)
  Definition reach_run : stop * OpsDatabase.t :=
    OpsRunner.solve Reach.program (Reach.facts triangle) example_limits.

  (** A pair with a stored distance is reachable. *)
  Example pair_with_a_distance_is_reachable :
    OpsRunner.holds Reach.reach_code [1; 3] (snd reach_run) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A pair without a stored distance is not reachable. *)
  Example pair_without_a_distance_is_not_reachable :
    OpsRunner.holds Reach.reach_code [3; 1] (snd reach_run) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

End RowTests.

(** * Aggregation *)

Module AggregationTests.

  Local Open Scope positive_scope.

  (** The run of the heaviest edges on the triangle. *)
  Definition heaviest_run : stop * OpsDatabase.t :=
    OpsRunner.solve Heaviest.program (Heaviest.facts triangle) example_limits.

  (** The edges out of 1 weigh 1 and 5, so the stored weight is 5. *)
  Example heaviest_edge_is_stored :
    stored Heaviest.heaviest_code [1] (snd heaviest_run) = Some 5.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Node 3 has no edge out of it, so no weight is stored there. *)
  Example node_without_edges_has_no_weight :
    stored Heaviest.heaviest_code [3] (snd heaviest_run) = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

End AggregationTests.

(** * Unions *)

Module UnionTests.

  Local Open Scope positive_scope.

  (** The run of reaching definitions on the joined flows. *)
  Definition union_run : stop * SetDatabase.t :=
    SetRunner.solve Reaching.program (Reaching.facts join_facts) example_limits.

  (** The sets stop growing, so the run saturates. *)
  Example union_saturates :
    fst union_run = Saturated.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Node 3 stores the union {0, 1} of the two sets that reach it, which is neither of them. *)
  Example union_of_both_sets_is_stored :
    set_stored Reaching.reaching_code [3] (snd union_run) = Some (NEncode.encode 3%N).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Node 1 stores its own set only. *)
  Example source_keeps_its_own_set :
    set_stored Reaching.reaching_code [1] (snd union_run) = Some (NEncode.encode 1%N).
  Proof.
    vm_compute. reflexivity.
  Qed.

End UnionTests.

(** * Saturation *)

Module SaturationTests.

  Local Open Scope positive_scope.

  (** The run of the longest paths on the triangle. *)
  Definition longest_run : stop * OpsDatabase.t :=
    OpsRunner.solve Longest.program (Longest.facts triangle) example_limits.

  (** Without a cycle the lengths of the paths are finite, so the run saturates. *)
  Example longest_paths_saturate_without_a_cycle :
    fst longest_run = Saturated.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The direct edge from 1 to 3, of length 5, is the longest path there. *)
  Example longest_distance_is_stored :
    stored Longest.longest_code [1; 3] (snd longest_run) = Some 5.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Around a cycle no path is the longest, so each round stores a longer one and the run
      stops at its iteration limit. *)
  Example longest_paths_never_saturate_on_a_cycle :
    fst (OpsRunner.solve Longest.program (Longest.facts cycle) (Limits 10%N 1000%N)) =
      IterLimit.
  Proof.
    vm_compute. reflexivity.
  Qed.

End SaturationTests.

(** * Glue *)

Module GlueTests.

  Local Open Scope positive_scope.

  (** The path through 2 gives the assigned value 2 at the key [[1; 3]]. *)
  Example path_gives_assigned_value :
    lat_assigned Ops.prim (prim_merge Ops.prim) Paths.spec (Paths.inputs triangle)
      Paths.dist_code [1; 3] 2.
  Proof.
    apply (proj1 (Paths.dist_spec triangle 1 3 2)).
    apply (dist_step triangle 1 2 3 1 1).
    - apply dist_edge. simpl. auto.
    - simpl. auto.
  Qed.

  (** An assigned value gives back a path of that length. *)
  Example assigned_value_gives_path :
    lat_assigned Ops.prim (prim_merge Ops.prim) Paths.spec (Paths.inputs triangle)
      Paths.dist_code [1; 3] 5 -> dist triangle 1 3 5.
  Proof.
    intros Hvalue.
    exact (proj2 (Paths.dist_spec triangle 1 3 5) Hvalue).
  Qed.

  (** The shorter of two path lengths is a path length, which the command proves because
      [Pos.min] returns one of its arguments. *)
  Example minimum_of_two_paths_is_a_path :
    dist triangle 1 3 2 -> dist triangle 1 3 5 -> dist triangle 1 3 (Pos.min 2 5).
  Proof.
    exact (Paths.dist_merges triangle 1 3 2 5).
  Qed.

  (** A relation beside a lattice table relates to its derived rows. *)
  Example reach_gives_derived_row :
    lat_derived Ops.prim (prim_merge Ops.prim) Reach.spec (Reach.inputs triangle)
      Reach.reach_code [1; 3].
  Proof.
    apply (proj1 (Reach.reach_spec triangle 1 3)).
    apply (reach_dist triangle 1 3 5).
    apply dist_edge. simpl. auto.
  Qed.

  (** The union of the sets that reach node 3 is assigned there, by the constructor that
      merges. *)
  Example union_gives_assigned_value :
    lat_assigned SetOps.prim (prim_merge SetOps.prim) Reaching.spec (Reaching.inputs join_facts)
      Reaching.reaching_code [3] (NEncode.encode 3%N).
  Proof.
    apply (proj1 (Reaching.reaching_spec join_facts 3 3%N)).
    apply (reaching_union join_facts 3 1%N 2%N).
    - apply (reaching_flow join_facts 1 3 1%N).
      + apply reaching_gen. simpl. auto.
      + simpl. auto.
    - apply (reaching_flow join_facts 2 3 2%N).
      + apply reaching_gen. simpl. auto.
      + simpl. auto.
  Qed.

End GlueTests.

(** * Conditions *)

Module ConditionTests.

  Local Open Scope positive_scope.

  (** [hop edges a b d] keeps the shortest edges, and reads a weight [d] as a node. *)
  Inductive hop (edges : list edge) : positive -> positive -> positive -> Prop :=
    | hop_edge a b w : In (Edge a b w) edges -> hop edges a b w
    | hop_back a b d : hop edges a b d -> hop edges d a d.

  Egglog Hops from hop with Ops merge hop Pos.min.

  (** The merge of the code of [Pos.min] is [Pos.min]. *)
  Example min_code_merges_by_min :
    forall a b, prim_merge Ops.prim Ops.min_code a b = Pos.min a b.
  Proof.
    intros a b. reflexivity.
  Qed.

  (** The engine accepts the sorts and the kinds of the program of shortest paths. *)
  Example paths_are_well_sorted :
    spec_ok Paths.spec = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Shortest paths has no constructor table and only rows and assigned values as heads. *)
  Example paths_read_lattice_tables :
    lattice_reads Paths.spec = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Each read of shortest paths is a variable that occurs once in its body and in no key of
      its head. *)
  Example paths_read_in_a_monotone_frame :
    reads_ok Paths.spec = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A read value that is a key of the head breaks the frame. *)
  Example read_key_breaks_the_frame :
    reads_ok Hops.spec = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Two edges from 1 to 2, of weights 5 and 3. *)
  Definition parallel : list edge := [Edge 1 2 5; Edge 1 2 3].

  (** The run of [hop] on the two parallel edges. *)
  Definition parallel_run : stop * OpsDatabase.t :=
    OpsRunner.solve Hops.program (Hops.facts parallel) example_limits.

  (** The run of [hop] on the parallel edges saturates. *)
  Example read_key_run_saturates :
    fst parallel_run = Saturated.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The edge of weight 5 gives [hop parallel 5 1 5] by [hop_back]. *)
  Example missed_value_holds :
    hop parallel 5 1 5.
  Proof.
    apply (hop_back parallel 1 2 5).
    apply hop_edge. simpl. auto.
  Qed.

  (** The run reads only the stored weight 3 at [[1; 2]], so it stores no value at [[5; 1]],
      although [missed_value_holds] gives one. *)
  Example read_key_misses_a_value :
    stored Hops.hop_code [5; 1] (snd parallel_run) = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A program without reads has the meaning of [derived] and [assigned]. *)
  Example aggregation_reads_nothing :
    no_reads Heaviest.spec = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A derived program without reads is a lattice specification of [LatticeSig.v]. *)
  Example aggregation_is_a_lattice_specification :
    lattice_spec Heaviest.spec = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Shortest paths read the distances. *)
  Example paths_read_the_distances :
    no_reads Paths.spec = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The primitive of the code of [Pos.add] adds. *)
  Example add_code_adds :
    forall a b, Ops.prim Ops.add_code [a; b] = Some (Pos.add a b).
  Proof.
    intros a b. reflexivity.
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

  (** Shortest paths is monotone: a longer distance read gives a longer distance assigned, in
      the order of [Pos.min]. *)
  Example shortest_paths_are_monotone :
    monotone Ops.prim (prim_merge Ops.prim) Paths.spec.
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
      [ (* The value that the clause reads is unchanged, so its assigned value is too. *)
        solve [exists u; split; [exact Hvalue | rewrite min_code_merges_by_min; apply Pos.min_id]]
      | (* A longer distance is read, so a longer distance is assigned. *)
        cbv beta iota in Hvalue |- *;
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

End ConditionTests.

(** * Rejections *)

Module RejectionTests.

  (** [reaching_bare] lacks the constructor that merges two sets, and [N.lor] returns neither of
      its arguments. *)
  Inductive reaching_bare (facts : list flow_fact) : positive -> N -> Prop :=
    | reaching_bare_gen n s : In (Gen n s) facts -> reaching_bare facts n s
    | reaching_bare_flow m n s : reaching_bare facts m s -> In (Flow m n) facts ->
        reaching_bare facts n s.

  (** The successor and the addition of positives, and the minimum of integers. *)
  Egglog Primitives Steps Pos.succ Pos.add.

  Egglog Primitives IntMin Z.min Pos.add.

  (** Numbers and their sums, for an equation beside a lattice table. *)
  Inductive num_term : Type :=
    | Lit (n : positive)
    | Plus (a b : num_term).

  (** Two numbers joined by an edge are equal. *)
  Inductive joined (edges : list edge) : num_term -> num_term -> Prop :=
    | joined_refl a : joined edges a a
    | joined_edge a b w : In (Edge a b w) edges -> joined edges (Lit a) (Lit b).

  (** A clause reads a lattice table whose relation is not closed under its merge. *)
  Fail Egglog Bare from reaching_bare with SetOps merge reaching_bare N.lor.

  (** The merge is not a primitive of the set. *)
  Fail Egglog Times from dist with Ops merge dist Pos.mul.

  (** The lattice table is not a relation that the command reads. *)
  Fail Egglog Elsewhere from dist with Ops merge reach Pos.min.

  (** A lattice table needs a primitive set for its merge. *)
  Fail Egglog Unset from dist merge dist Pos.min.

  (** The merge takes one argument. *)
  Fail Egglog Unary from dist with Steps merge dist Pos.succ.

  (** The merge is over integers, and the values of [dist] are positives. *)
  Fail Egglog Integers from dist with IntMin merge dist Z.min.

  (** The declaration lacks its merge. *)
  Fail Egglog Truncated from dist with Ops merge dist.

  (** The same table is declared twice. *)
  Fail Egglog Twice from dist with Ops merge dist Pos.min merge dist Pos.max.

  (** An equation beside a lattice table. *)
  Fail Egglog Mixed from dist joined with Ops merge dist Pos.min.

  (** A relation named before the lattice table that its premise reads. *)
  Fail Egglog Backwards from reach dist with Ops merge dist Pos.min.

End RejectionTests.
