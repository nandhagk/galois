(** * Checked SSA construction

    This module supplies a checked construction interface.
    Every candidate passes both translation and SSA validation before it is returned.
    Builds on: BuildSig. *)

From Stdlib Require Import List PArith NArith Bool Lia.
From Argent Require Import Time Tactics Std BigO Loop.
From Galois.Base Require Import Code KeySig Key Trie.
From Galois.Graph Require Import Data Spec DigraphSig DomSig FrontierSig.
From Galois.Program Require Import CfgSig VarsSig SsaSig.
From Galois.Ssa Require Import Lang LiveSig ValidateSig Validate BuildSig.
Import List.ListNotations.

Module BuildSig.
  TimeFun rename_bodies.
  TimeFun rename_stack.
  TimeFun renamed_blocks.
  TimeFun renamed_envs.
  TimeFun next_value.
End BuildSig.

(** A syntax scan emits each definition key once for the current block. *)
Fixpoint build_unique (xs : list positive) (seen : ptrie unit) : list positive :=
  match xs with
  | [] => []
  | x :: rest =>
    if val_mem seen x then build_unique rest seen
    else x :: build_unique rest (PTrieCode.set x tt seen)
  end.
TimeFun build_unique.

Definition build_def_rows (b : positive) (xs : list positive)
    (rows : ptrie (list positive)) : ptrie (list positive) :=
  fold_right (fun x acc => PTrieCode.set x (b :: index_row acc x) acc)
    rows (build_unique xs Empty).
TimeFun build_def_rows.

Lemma build_mem_set_false seen x y :
  val_mem (PTrieCode.set x tt seen) y = false <-> y <> x /\ val_mem seen y = false.
Proof.
  destruct (Pos.eq_dec y x) as [Heq|Hneq].
  - subst y. unfold val_mem at 1. rewrite PTrie.get_set_same. intuition discriminate.
  - unfold val_mem at 1. rewrite PTrie.get_set_other by exact Hneq.
    change (val_mem seen y = false <-> y <> x /\ val_mem seen y = false). tauto.
Qed.

(** Deduplication preserves every not-yet-seen key and emits it once. *)
Lemma build_unique_spec xs seen x :
  In x (build_unique xs seen) <-> In x xs /\ val_mem seen x = false.
Proof.
  revert seen; induction xs as [|a rest IH]; intro seen; cbn [build_unique In].
  - tauto.
  - destruct (val_mem seen a) eqn:Hseen.
    + rewrite IH. destruct (Pos.eq_dec x a) as [Heq|Hneq].
      * subst x; rewrite Hseen; intuition discriminate.
      * intuition congruence.
    + cbn [In]. rewrite IH, build_mem_set_false.
      destruct (Pos.eq_dec x a) as [Heq|Hneq].
      * subst x; rewrite Hseen; intuition.
      * intuition congruence.
Qed.

Lemma build_unique_nodup xs seen : NoDup (build_unique xs seen).
Proof.
  revert seen; induction xs as [|a rest IH]; intro seen; cbn [build_unique].
  - constructor.
  - destruct (val_mem seen a); [apply IH|]. constructor; [|apply IH].
    intro Hin. apply build_unique_spec in Hin as [_ Hfresh].
    apply build_mem_set_false in Hfresh as [Hneq _]. now apply Hneq.
Qed.

Lemma build_exists_spec xs x : existsb (Pos.eqb x) xs = true <-> In x xs.
Proof.
  rewrite existsb_exists. split.
  - intros [y [Hin Heq]]. apply Pos.eqb_eq in Heq; now subst y.
  - intro Hin. exists x; split; [exact Hin|apply Pos.eqb_refl].
Qed.

Lemma build_unique_exists xs x :
  existsb (Pos.eqb x) (build_unique xs Empty) = existsb (Pos.eqb x) xs.
Proof.
  apply eq_true_iff_eq. rewrite !build_exists_spec, build_unique_spec.
  unfold val_mem; rewrite PTrie.get_empty; tauto.
Qed.

(** Adding one block row for distinct keys changes precisely those lookup rows. *)
Lemma build_rows_lookup (ys : list positive) (b : positive)
    (rows : ptrie (list positive)) (x : positive) : NoDup ys ->
  index_row (fold_right (fun y acc => PTrieCode.set y (b :: index_row acc y) acc) rows ys) x =
    if existsb (Pos.eqb x) ys then b :: index_row rows x else index_row rows x.
Proof.
  induction ys as [|a rest IH]; intro Hdistinct; [reflexivity|].
  inversion Hdistinct as [|id ids Hfresh Hrest]; subst.
  cbn [fold_right existsb]. destruct (Pos.eqb x a) eqn:Hsame.
  - apply Pos.eqb_eq in Hsame; subst x. unfold index_row at 1.
    rewrite PTrie.get_set_same. cbn. rewrite IH by exact Hrest.
    assert (Hexists : existsb (Pos.eqb a) rest = false).
    { destruct (existsb (Pos.eqb a) rest) eqn:Hfound; [|reflexivity].
      apply build_exists_spec in Hfound; contradiction. }
    now rewrite Hexists.
  - apply Pos.eqb_neq in Hsame. unfold index_row at 1.
    rewrite PTrie.get_set_other by exact Hsame. apply IH; exact Hrest.
Qed.

Lemma build_def_rows_lookup b xs rows x :
  index_row (build_def_rows b xs rows) x =
    if existsb (Pos.eqb x) xs then b :: index_row rows x else index_row rows x.
Proof.
  unfold build_def_rows. rewrite build_rows_lookup by apply build_unique_nodup.
  now rewrite build_unique_exists.
Qed.

Lemma build_block_defs_lookup {K G} (bs : list (positive * block positive K G)) x :
  index_row (fold_right (fun item rows => build_def_rows (fst item) (block_defs (snd item)) rows)
    Empty bs) x = map fst (filter (fun item => existsb (Pos.eqb x) (block_defs (snd item))) bs).
Proof.
  induction bs as [|item rest IH].
  - unfold index_row; cbn [fold_right map filter]. now rewrite PTrie.get_empty.
  - cbn [fold_right filter]. rewrite build_def_rows_lookup, IH.
    destruct (existsb (Pos.eqb x) (block_defs (snd item))); reflexivity.
Qed.

(** Transposing placement sites adds the variable to exactly the selected block rows. *)
Lemma build_places_row_spec (sites : list positive) (x : positive)
    (rows : ptrie (list positive)) (b y : positive) :
  In y (index_row
    (fold_right (fun target acc => PTrieCode.set target (x :: index_row acc target) acc)
      rows sites) b) <->
    (In b sites /\ y = x) \/ In y (index_row rows b).
Proof.
  induction sites as [|a rest IH]; [cbn [fold_right In]; tauto|].
  cbn [fold_right]. destruct (Pos.eq_dec b a) as [Heq|Hneq].
  - subst b. unfold index_row at 1. rewrite PTrie.get_set_same. cbn [In].
    rewrite IH. cbn [In]; intuition congruence.
  - unfold index_row at 1. rewrite PTrie.get_set_other by exact Hneq.
    change (In y (index_row
      (fold_right (fun target acc => PTrieCode.set target (x :: index_row acc target) acc)
        rows rest) b) <-> (In b (a :: rest) /\ y = x) \/ In y (index_row rows b)).
    rewrite IH. cbn [In]; intuition congruence.
Qed.

(** A successor of the indexed CFG is the target of one supplied edge occurrence. *)
Lemma build_cfg_target {E} vs es (src dst : E -> positive) u v :
  Spec.edge (cfg_graph vs es src dst) u v -> exists e, In e es /\ dst e = v.
Proof.
  induction es as [|a rest IH].
  - change (In v (index_row Empty u) -> exists e, In e [] /\ dst e = v).
    unfold index_row; rewrite PTrie.get_empty; contradiction.
  - change (In v (index_row (PTrieCode.set (src a)
      (dst a :: succs (cfg_graph vs rest src dst) (src a))
      (succ (cfg_graph vs rest src dst))) u) -> exists e, In e (a :: rest) /\ dst e = v).
    unfold index_row at 1. destruct (Pos.eq_dec u (src a)) as [Heq|Hneq].
    + rewrite Heq, PTrie.get_set_same. intros [Htarget|Hin].
      * exists a; split; [now left|exact Htarget].
      * rewrite <- Heq in Hin. destruct (IH Hin) as [e [Hedge Htarget]].
        exists e; split; [now right|exact Htarget].
    + rewrite PTrie.get_set_other by exact Hneq. intro Hin.
      destruct (IH Hin) as [e [Hedge Htarget]]. exists e; split; [now right|exact Htarget].
Qed.

Definition build_input_name (x : positive) : positive := xO (xO x).
Definition build_phi_name (b x : positive) : positive := xI (xO (glue b x)).
Definition build_instruction_name (i : N) : positive := xO (xI (N.succ_pos i)).
TimeFun build_input_name.
TimeFun build_phi_name.
TimeFun build_instruction_name.

(** Operand rewriting fails immediately on an unavailable source name. *)
Fixpoint build_values (rho : ptrie positive) (xs : list positive) : option (list positive) :=
  match xs with
  | [] => Some []
  | x :: rest =>
    match trie_get x rho, build_values rho rest with
    | Some y, Some ys => Some (y :: ys)
    | _, _ => None
    end
  end.
TimeFun build_values.

(** Only the requested live bindings are copied into a successor task. *)
Fixpoint build_project (b : positive) (phis : ptrie unit) (xs : list positive)
    (rho inputs : ptrie positive) : option renaming :=
  match xs with
  | [] => Some []
  | x :: rest =>
    let name := if val_mem phis x then Some (build_phi_name b x)
      else match trie_get x rho with Some y => Some y | None => trie_get x inputs end in
    match name, build_project b phis rest rho inputs with
    | Some y, Some ys => Some ((x, y) :: ys)
    | _, _ => None
    end
  end.
TimeFun build_project.

(** Materialization restores the source block order, including malformed duplicate keys. *)
Fixpoint build_materialize {K G} (original : list (positive * block positive K G))
    (bodies : ptrie (block positive K G)) : option (list (positive * block positive K G)) :=
  match original with
  | [] => Some []
  | (b, _) :: rest =>
    match trie_get b bodies, build_materialize rest bodies with
    | Some body, Some bs => Some ((b, body) :: bs)
    | _, _ => None
    end
  end.
TimeFun build_materialize.

Module BuildCode (O : OPS)
    (K : KEY_OPS with Definition t := O.K) (G : KEY_OPS with Definition t := O.G)
    (P : TYPE with Definition t := func positive O.K O.G)
    (Q : TYPE) (R : LANG_PREPARE_OPS O Q) (BE E : TYPE) (N : KEY_OPS)
    (BC : CFG_INDEXED_OPS Q PosKeyCode BE) (C : CFG_INDEXED_OPS Q N E)
    (U : VARS_OPS Q N E C PosKeyCode)
    (SP : SSA_POINTS_OPS Q PosKeyCode BE BC N E C PosKeyCode U)
    (S : SSA_OPS Q PosKeyCode BE BC PosKeyCode K G)
    (DG : DIGRAPH_OPS) (D : DOM_OPS) (F : FRONTIER_OPS)
    (L : LIVE_OPS O P Q R BE E N BC C U SP)
    (Va : VALIDATE_OPS O K G P Q R BE BC S DG D) <: BUILD_OPS O K G P Q R BE E N BC C U SP S DG D F L Va.
  Definition graph p := DG.prepare (cfg_graph (BC.nodes (R.prepare p))
    (BC.edges (R.prepare p)) (BC.src (R.prepare p)) (BC.dst (R.prepare p))).
  Definition dom_result p := D.build (graph p) (entry _ _ _ p).
  Definition dom_tree p := D.tree (graph p) (entry _ _ _ p)
    (fst (dom_result p)) (snd (dom_result p)).
  Definition frontiers p := F.df (graph p) (dom_tree p).

  Definition def_index (p : P.t) : ptrie (list positive) :=
    build_def_rows (entry _ _ _ p) (inputs _ _ _ p)
      (fold_right (fun item rows => build_def_rows (fst item) (block_defs (snd item)) rows)
        Empty (blocks _ _ _ p)).

  Definition live_sets (rows : list (positive * list positive)) : ptrie (ptrie unit) :=
    fold_right (fun row acc => PTrieCode.set (fst row) (val_set (snd row)) acc) Empty rows.

  Definition place_var (frontier defs : ptrie (list positive))
      (live : ptrie (ptrie unit)) (x : positive) : list positive :=
    filter (fun b => match trie_get b live with Some xs => val_mem xs x | None => false end)
      (F.idf frontier (frontier_row defs x)).

  Definition placement_with (frontier defs : ptrie (list positive))
      (live : ptrie (ptrie unit)) (vars : list positive) : ptrie (list positive) :=
    fold_right (fun x rows =>
      fold_right (fun b acc => PTrieCode.set b (x :: index_row acc b) acc)
        rows (place_var frontier defs live x)) Empty vars.

  Definition placement (p : P.t) : ptrie (list positive) :=
    placement_with (frontiers p) (def_index p) (live_sets (L.live_in p))
      (U.universe (R.prepare p)).

  Fixpoint rename_code (cs : list (positive * O.K * list positive))
      (rho : ptrie positive) (names : renaming) (fresh : N)
      : option (list (positive * O.K * list positive) * ptrie positive * renaming * N) :=
    match cs with
    | [] => Some ([], rho, names, fresh)
    | (x, op, xs) :: rest =>
      match build_values rho xs with
      | None => None
      | Some ys =>
        let y := build_instruction_name fresh in
        match rename_code rest (PTrieCode.set x y rho) ((x, y) :: names) (N.succ fresh) with
        | Some (out, final, final_names, next) => Some ((y, op, ys) :: out, final, final_names, next)
        | None => None
        end
      end
    end.

  Definition rename_exit (e : exit positive O.G) (rows : ptrie (list positive))
      (rho : ptrie positive) : option (exit positive O.G) :=
    match e with
    | Jump target old =>
      match old, build_values rho (index_row rows target) with
      | [], Some args => Some (Jump target args)
      | _, _ => None
      end
    | Branch guard xs yes old_yes no old_no =>
      match old_yes, old_no, build_values rho xs,
        build_values rho (index_row rows yes), build_values rho (index_row rows no) with
      | [], [], Some args, Some yes_args, Some no_args =>
        Some (Branch guard args yes yes_args no no_args)
      | _, _, _, _, _ => None
      end
    | Return xs =>
      match build_values rho xs with Some args => Some (Return args) | None => None end
    end.

  Fixpoint rename_children (kids : list positive) (rows live : ptrie (list positive))
      (rho inputs : ptrie positive) : option (list (positive * renaming)) :=
    match kids with
    | [] => Some []
    | b :: rest =>
      match build_project b (val_set (index_row rows b)) (index_row live b) rho inputs,
        rename_children rest rows live rho inputs with
      | Some names, Some tasks => Some ((b, names) :: tasks)
      | _, _ => None
      end
    end.

  Definition rename_init (p : P.t) : rename_state O.K O.G :=
    RenameState O.K O.G (val_index (blocks _ _ _ p))
      ((entry _ _ _ p, map (fun x => (x, build_input_name x)) (inputs _ _ _ p)) ::
        map (fun item => (fst item, [])) (blocks _ _ _ p)) [] [] 0%N.

  Definition rename_step_indexed (p : P.t) (t : domtree)
      (rows live_index : ptrie (list positive)) (input_index : ptrie positive)
      (live : list (positive * list positive)) (st : rename_state O.K O.G)
      : rename_state O.K O.G + option (P.t * cert) :=
    match st with
    | RenameState _ _ bodies [] output envs fresh =>
      inr (match build_materialize (blocks _ _ _ p) (val_index output) with
        | Some bs => Some (Func positive O.K O.G (entry _ _ _ p)
            (map build_input_name (inputs _ _ _ p)) bs, (envs, live))
        | None => None
        end)
    | RenameState _ _ bodies ((b, inherited) :: tasks) output envs fresh =>
      match trie_get b bodies with
      | None => inl (RenameState O.K O.G bodies tasks output envs fresh)
      | Some body =>
        let phis := index_row rows b in
        let entry_names :=
          if Pos.eqb b (entry _ _ _ p) then
            match phis with [] => Some inherited | _ => None end
          else build_project b (val_set phis) (index_row live_index b)
            (val_index inherited) input_index in
        match params _ _ _ body, entry_names with
        | [], Some names =>
          match rename_code (code _ _ _ body) (val_index names) names fresh with
          | Some (cs, final, final_names, next) =>
            match rename_exit (term _ _ _ body) rows final,
              rename_children (children t b) rows live_index final input_index with
            | Some e, Some kids =>
              inl (RenameState O.K O.G (PTrieCode.remove b bodies) (kids ++ tasks)
                ((b, Block positive O.K O.G (map (build_phi_name b) phis) cs e) :: output)
                ((b, names) :: envs) next)
            | _, _ => inr None
            end
          | None => inr None
          end
        | _, _ => inr None
        end
      end
    end.

  Definition rename_step (p : P.t) (t : domtree) (rows : ptrie (list positive))
      (live : list (positive * list positive)) (st : rename_state O.K O.G)
      : rename_state O.K O.G + option (P.t * cert) :=
    rename_step_indexed p t rows (val_index live)
      (val_index (map (fun x => (x, build_input_name x)) (inputs _ _ _ p))) live st.

  Definition rename (p : P.t) (t : domtree) (rows : ptrie (list positive))
      (live : list (positive * list positive)) : option (P.t * cert) :=
    let live_index := val_index live in
    let input_index := val_index (map (fun x => (x, build_input_name x)) (inputs _ _ _ p)) in
    match loop_fuel (rename_step_indexed p t rows live_index input_index live)
      (2 * length (blocks _ _ _ p) + 1) (rename_init p) with
    | inl _ => None
    | inr answer => answer
    end.

  Definition produce (p : P.t) : option (P.t * cert) :=
    let q := R.prepare p in
    let g := DG.prepare (cfg_graph (BC.nodes q) (BC.edges q) (BC.src q) (BC.dst q)) in
    let result := D.build g (entry _ _ _ p) in
    if D.check g (entry _ _ _ p) (fst result) (snd result) then
      let t := D.tree g (entry _ _ _ p) (fst result) (snd result) in
      let frontier := F.df g t in
      let live := L.live_in p in
      let defs := def_index p in
      let sets := live_sets live in
      let rows := placement_with frontier defs sets (U.universe q) in
      rename p t rows live
    else None.
  Definition build (p : P.t) : option P.t :=
    match produce p with
    | None => None
    | Some (s, c) => if andb (Va.check p s c) (Va.check_ssa s) then Some s else None
    end.
End BuildCode.

Module Build (O : OPS)
    (K : KEY with Definition t := O.K) (G : KEY with Definition t := O.G)
    (P : TYPE with Definition t := func positive O.K O.G)
    (Q : TYPE) (R : LANG_PREPARE_OPS O Q) (BE E : TYPE) (N : KEY)
    (BC : CFG Q PosKey BE) (C : CFG Q N E)
    (U : VARS Q N E C PosKey)
    (SP : SSA_POINTS Q PosKey BE BC N E C PosKey U)
    (S : SSA Q PosKey BE BC PosKey K G)
    (DG : DIGRAPH) (D : DOM) (F : FRONTIER)
    (L : LIVE O P Q R BE E N BC C U SP)
    (B : LANG_SSA_LINK O K G Q R BE BC S)
    (Va : VALIDATE O K G P Q R BE BC S DG D B) <: BUILD O K G P Q R BE E N BC C U SP S DG D F L B Va.
  Include BuildCode O K G P Q R BE E N BC C U SP S DG D F L Va.

  (** The live-row index keeps the same first row as certificate lookup. *)
  Lemma live_sets_lookup : forall rows b,
    trie_get b (live_sets rows) = option_map val_set (lookup b rows).
  Proof.
    induction rows as [|[id xs] rest IH]; intro b.
    - apply PTrie.get_empty.
    - change (trie_get b (PTrieCode.set id (val_set xs) (live_sets rest)) =
        option_map val_set (if Pos.eqb b id then Some xs else lookup b rest)).
      destruct (Pos.eqb b id) eqn:Heq.
      + apply Pos.eqb_eq in Heq; subst b. apply PTrie.get_set_same.
      + apply Pos.eqb_neq in Heq. rewrite PTrie.get_set_other by exact Heq. apply IH.
  Qed.

  Lemma placement_with_spec : forall frontier defs live vars b x,
    In x (index_row (placement_with frontier defs live vars) b) <->
      In x vars /\ In b (place_var frontier defs live x).
  Proof.
    intros frontier defs live vars b x; induction vars as [|y rest IH].
    - unfold placement_with, index_row; cbn [fold_right In].
      rewrite PTrie.get_empty; cbn [In]; tauto.
    - change (In x (index_row
        (fold_right (fun target acc => PTrieCode.set target (y :: index_row acc target) acc)
          (placement_with frontier defs live rest) (place_var frontier defs live y)) b) <->
        In x (y :: rest) /\ In b (place_var frontier defs live x)).
      rewrite build_places_row_spec, IH. cbn [In]; intuition congruence.
  Qed.

  Lemma build_checked : forall p, build p =
    match produce p with
    | None => None
    | Some (s, c) => if andb (Va.check p s c) (Va.check_ssa s) then Some s else None
    end.
  Proof.
    reflexivity.
  Qed.
  Lemma build_correct : forall p s, imp_form p -> build p = Some s ->
    ssa_wf s /\ forall n ins, run_with O.eval O.test n s ins = run_with O.eval O.test n p ins.
  Proof.
    intros p s Himp Hbuild. rewrite build_checked in Hbuild.
    destruct (produce p) as [[candidate certificate]|] eqn:Hproduce; [|discriminate].
    destruct (andb (Va.check p candidate certificate) (Va.check_ssa candidate))
      eqn:Hchecked; [|discriminate].
    inversion Hbuild; subst candidate.
    apply andb_true_iff in Hchecked as [Htranslation Hssa].
    split; [now apply Va.check_ssa_sound|].
    intros n ins. now apply (Va.check_sound p s certificate Himp Htranslation).
  Qed.
End Build.

Module BuildT (O : OPS)
    (K : KEY_T with Definition t := O.K) (G : KEY_T with Definition t := O.G)
    (P : TYPE with Definition t := func positive O.K O.G)
    (Q : TYPE) (R : LANG_PREPARE_T O Q) (BE E N : KEY_T)
    (BC : CFG_T Q PosKeyT BE) (C : CFG_T Q N E)
    (U : VARS_T Q N E C PosKeyT)
    (SP : SSA_POINTS_T Q PosKeyT BE BC N E C PosKeyT U)
    (PB : LANG_PRESENT_BUDGET O Q R BE E N BC C U SP)
    (S : SSA_T Q PosKeyT BE BC PosKeyT K G)
    (DG : DIGRAPH_T) (D : DOM_T) (F : FRONTIER_T)
    (L : LIVE_T O P Q R BE E N BC C U SP PB)
    (B : LANG_SSA_LINK O K G Q R BE BC S)
    (Va : VALIDATE_T O K G P Q R BE BC S DG D B) <: BUILD_ALL O K G P Q R BE E N BC C U SP PB S DG D F L B Va.
  Include Build O K G P Q R BE E N BC C U SP S DG D F L B Va.
  TimeFun graph.
  TimeFun dom_result.
  TimeFun dom_tree.
  TimeFun frontiers.
  TimeFun def_index.
  TimeFun live_sets.
  TimeFun place_var.
  TimeFun placement_with.
  TimeFun placement.
  TimeFun rename_code.
  TimeFun rename_exit.
  TimeFun rename_children.
  TimeFun rename_init.
  TimeFun rename_step_indexed.
  TimeFun rename_step.
  TimeFun rename.
  TimeFun produce.
  TimeFun build.
  Definition c_build : N := 1. (* STUB *)
  Definition df_size p := F.df_size (graph p) (dom_tree p).
  Definition phi_sites p x := F.idf (frontiers p) (definition_blocks p x).
  Definition placement_work p := fold_right (fun x n =>
    fold_right (fun b m => 1 + length (frontier_row (frontiers p) b) + m) 0 (phi_sites p x) + n)
    0 (U.universe (R.prepare p)).
  Definition phi_args p :=
    match produce p with Some (s, _) => function_edge_args s | None => 0 end.
  Definition dom_work p :=
    (graph_n (base (graph p)) + graph_e (base (graph p)) + 1) *
      (Nat.log2 (graph_n (base (graph p))) + 1).
  Definition build_work p := function_size p + length (BC.nodes (R.prepare p)) + length (BC.edges (R.prepare p)) +
    dom_work p + df_size p + placement_work p + L.live_size p + phi_args p + 1.
  (** Construction keeps the published dominator, placement, liveness and argument budget. *)
  Lemma T_build_le : forall p,
    (T_build p <= c_build * N.of_nat (build_work p) * N.of_nat (function_width p + 1) +
      c_build * N.of_nat (Va.op_bits p + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma build_bigO : bigO (fun _ : P.t => True)
    (fun p => N.of_nat (build_work p * (function_width p + 1) + Va.op_bits p + 1)) T_build.
  Proof. Admitted. (* STUB *)
  Definition k_graph : N := 1. (* STUB *)
  Definition k_place : N := 1. (* STUB *)
  Definition k_rename : N := 1. (* STUB *)
  Definition k_wrap : N := 1. (* STUB *)
  Definition k_size : N := 1. (* STUB *)
  Definition placed p x :=
    place_var (frontiers p) (def_index p) (live_sets (L.live_in p)) x.

  (** The definition index lists each variable's definition blocks. *)
  Lemma F1_graph_wf : forall p, wf_graph (base (graph p)).
  Proof.
    intro p. destruct (PB.prepared_wf p) as [Hblocks _].
    unfold graph. rewrite DG.prepare_base. split.
    - apply BC.nodes_nodup; exact Hblocks.
    - intros u v Hu Hedge. destruct (build_cfg_target _ _ _ _ _ _ Hedge)
        as [e [Hin Htarget]]. subst v.
      exact (proj2 (BC.edges_nodes (R.prepare p) e Hblocks Hin)).
  Qed.
  Lemma F2a_def_index : forall p x,
    frontier_row (def_index p) x = definition_blocks p x.
  Proof.
    intros p x. change (index_row (def_index p) x = definition_blocks p x).
    unfold def_index, definition_blocks.
    rewrite build_def_rows_lookup, build_block_defs_lookup.
    destruct (existsb (Pos.eqb x) (inputs _ _ _ p)); reflexivity.
  Qed.
  (** The live sets answer certificate membership. *)
  Lemma F2b_live_sets : forall rows b x,
    (exists m, trie_get b (live_sets rows) = Some m /\ trie_get x m = Some tt) <->
      In x (cert_live ([], rows) b).
  Proof.
    intros rows b x. rewrite live_sets_lookup. unfold cert_live; cbn [snd].
    destruct (lookup b rows) as [xs|] eqn:Hlookup; cbn [option_map].
    - split.
      + intros [m [Heq Hget]]. inversion Heq; subst m.
        apply val_set_member. unfold val_mem. now rewrite Hget.
      + intro Hin. exists (val_set xs); split; [reflexivity|].
        apply val_set_member in Hin. unfold val_mem in Hin.
        destruct (trie_get x (val_set xs)) as [[]|]; [reflexivity|discriminate].
    - split; [intros [m [Heq _]]; discriminate|contradiction].
  Qed.
  (** Every variable enters a placement worklist at most once per block. *)
  Lemma F2_place_unique : forall p x, NoDup (placed p x).
  Proof.
    intros p x. unfold placed, place_var. apply NoDup_filter, F.idf_unique.
  Qed.
  (** Pruned placement uses iterated-frontier blocks with a certified live entry. *)
  Lemma F3_place_region : forall p x b, In b (placed p x) ->
    In b (phi_sites p x) /\ In x (cert_live ([], L.live_in p) b).
  Proof.
    intros p x b Hin. unfold placed, place_var in Hin.
    apply filter_In in Hin as [Hregion Hlive]. split.
    - unfold phi_sites. now rewrite F2a_def_index in Hregion.
    - apply (proj1 (F2b_live_sets (L.live_in p) b x)).
      destruct (trie_get b (live_sets (L.live_in p))) as [xs|] eqn:Hrow;
        [|discriminate].
      exists xs; split; [reflexivity|]. unfold val_mem in Hlive.
      destruct (trie_get x xs) as [[]|]; [reflexivity|discriminate].
  Qed.
  (** The placement table lists exactly the placed variables of each block. *)
  Lemma F3a_placement : forall p b x,
    In x (frontier_row (placement p) b) <->
      In x (U.universe (R.prepare p)) /\ In b (placed p x).
  Proof.
    intros p b x. unfold placement, placed.
    apply placement_with_spec.
  Qed.
  (** Renaming uses a bounded explicit stack with one entering and one leaving visit per block. *)
  Lemma F4_rename_loop : forall p t rows live,
    rename p t rows live =
      match loop_fuel (rename_step p t rows live) (2 * length (blocks _ _ _ p) + 1)
        (rename_init p) with
      | inl _ => None
      | inr answer => answer
      end.
  Proof.
    reflexivity.
  Qed.
  (** The producer checks dominators before using their numbered tree. *)
  Lemma F5_produce_checked : forall p s c, produce p = Some (s, c) ->
    D.check (graph p) (entry _ _ _ p) (fst (dom_result p)) (snd (dom_result p)) = true /\
    rename p (dom_tree p) (placement p) (L.live_in p) = Some (s, c).
  Proof.
    intros p s c. change ((if D.check (graph p) (entry _ _ _ p)
      (fst (dom_result p)) (snd (dom_result p)) then
      rename p (dom_tree p) (placement p) (L.live_in p) else None) = Some (s, c) ->
      D.check (graph p) (entry _ _ _ p) (fst (dom_result p)) (snd (dom_result p)) = true /\
      rename p (dom_tree p) (placement p) (L.live_in p) = Some (s, c)).
    destruct (D.check (graph p) (entry _ _ _ p) (fst (dom_result p)) (snd (dom_result p)))
      eqn:Hchecked; [intro Hrename; now split|discriminate].
  Qed.
  (** The two indexes charge syntax and emitted live rows once. *)
  Lemma T0_indexes : forall p,
    (T_def_index p + T_live_sets (L.live_in p) <= k_place *
      N.of_nat (function_size p + L.live_size p + 1) * N.of_nat (function_width p + 1))%N.
  Proof. Admitted. (* STUB *)
  (** One placement search charges seed and discovered-frontier incidences. *)
  Lemma T1_place_var : forall p x, In x (U.universe (R.prepare p)) ->
    (T_place_var (frontiers p) (def_index p) (live_sets (L.live_in p)) x <= k_place *
      N.of_nat (length (definition_blocks p x) +
        fold_right (fun b n => (1 + length (frontier_row (frontiers p) b) + n)%nat)
          0%nat (phi_sites p x) + 1) * N.of_nat (function_width p + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Placement indexes the rows once and sums the indexed variable searches. *)
  Lemma T1a_placement : forall p,
    (T_placement p <= k_place * N.of_nat (function_size p + placement_work p + 1) *
      N.of_nat (function_width p + 1) +
      fold_right N.add 0%N (map
        (T_place_var (frontiers p) (def_index p) (live_sets (L.live_in p)))
        (U.universe (R.prepare p))))%N.
  Proof. Admitted. (* STUB *)
  (** Initialization charges the source inventory at its syntax width. *)
  Lemma T2a_rename_init : forall p,
    (T_rename_init p <= k_rename * N.of_nat (function_size p + 1) *
      N.of_nat (function_width p + 1))%N.
  Proof. Admitted. (* STUB *)
  (** The driver charges the clock of its actual bounded rename loop. *)
  Lemma T2b_rename_driver : forall p,
    (T_rename p (dom_tree p) (placement p) (L.live_in p) <= T_rename_init p +
      T_loop_fuel (rename_step p (dom_tree p) (placement p) (L.live_in p))
        (T_rename_step p (dom_tree p) (placement p) (L.live_in p))
        (2 * length (blocks _ _ _ p) + 1) (rename_init p) +
      k_rename * N.of_nat (length (blocks _ _ _ p) + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Both visits to each block charge their statements and emitted incoming arguments. *)
  Lemma T2c_rename_loop : forall p,
    (T_loop_fuel (rename_step p (dom_tree p) (placement p) (L.live_in p))
      (T_rename_step p (dom_tree p) (placement p) (L.live_in p))
      (2 * length (blocks _ _ _ p) + 1) (rename_init p) <=
      k_rename * N.of_nat (function_size p + placement_work p + phi_args p + 1) *
        N.of_nat (function_width p + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Renaming charges statements and the incoming arguments it emits. *)
  Lemma T2_rename : forall p,
    (T_rename p (dom_tree p) (placement p) (L.live_in p) <=
      k_rename * N.of_nat (function_size p + placement_work p + phi_args p + 1) *
        N.of_nat (function_width p + 1))%N.
  Proof. Admitted. (* STUB *)
  (** A candidate keeps the source blocks and stays within the published work and width. *)
  Lemma F6_produce_size : forall p s c, produce p = Some (s, c) ->
    map fst (blocks _ _ _ s) = map fst (blocks _ _ _ p) /\
    (N.of_nat (function_size s + cert_size c) <= k_size * N.of_nat (build_work p))%N /\
    (N.of_nat (function_width s + vertex_width (cert_ids c)) <=
      k_size * N.of_nat (function_width p + 1))%N.
  Proof. Admitted. (* STUB *)
  (** The producer checks the graph before preparing it and stops at the first rejection. *)
  Lemma T3_produce : forall p,
    (T_produce p <= R.T_prepare p + k_graph +
      k_graph * N.of_nat (length (BC.nodes (R.prepare p)) +
        length (BC.edges (R.prepare p)) + 1) * N.of_nat (function_width p + 1) +
      DG.T_prepare (cfg_graph (BC.nodes (R.prepare p)) (BC.edges (R.prepare p))
        (BC.src (R.prepare p)) (BC.dst (R.prepare p))) +
      D.T_build (graph p) (entry _ _ _ p) +
      D.T_check (graph p) (entry _ _ _ p) (fst (dom_result p)) (snd (dom_result p)) +
      (if D.check (graph p) (entry _ _ _ p) (fst (dom_result p)) (snd (dom_result p))
       then D.T_tree (graph p) (entry _ _ _ p) (fst (dom_result p)) (snd (dom_result p)) +
         F.T_df (graph p) (dom_tree p) + L.T_live_in p + T_def_index p +
         T_live_sets (L.live_in p) + T_placement p +
         T_rename p (dom_tree p) (placement p) (L.live_in p)
       else 0))%N.
  Proof. Admitted. (* STUB *)
  (** The wrapper charges the actual certificate and candidate validators. *)
  Lemma T4_wrapper : forall p,
    (T_build p <= T_produce p +
      match produce p with
      | None => k_wrap
      | Some (s, c) => Va.T_check p s c + Va.T_check_ssa s + k_wrap
      end)%N.
  Proof. Admitted. (* STUB *)
End BuildT.
