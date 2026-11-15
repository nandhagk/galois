(** * Checked SSA construction

    This module supplies a checked construction interface.
    Every candidate passes both translation and SSA validation before it is returned.
    Builds on: BuildSig. *)

From Stdlib Require Import List Arith PArith NArith Bool Lia.
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

(** Duplicate block identifiers stop the producer before any frontier search. *)
Fixpoint build_blocks_unique {K G} (bs : list (positive * block positive K G))
    (seen : ptrie unit) : bool :=
  match bs with
  | [] => true
  | (b, _) :: rest =>
    if val_mem seen b then false else build_blocks_unique rest (PTrieCode.set b tt seen)
  end.
TimeFun build_blocks_unique.

Lemma build_blocks_unique_map {K G} (bs : list (positive * block positive K G)) seen :
  build_blocks_unique bs seen = val_unique (map fst bs) seen.
Proof.
  revert seen; induction bs as [|[b body] rest IH]; intro seen; [reflexivity|].
  cbn [build_blocks_unique val_unique map fst].
  destruct (val_mem seen b); [reflexivity|apply IH].
Qed.

Definition build_live_rows_size (rows : list (positive * list positive)) : nat :=
  fold_right (fun row n => 1 + length (snd row) + n) 0 rows.
TimeFun build_live_rows_size.

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

(** A weighted inventory retains every listed occurrence. *)
Definition build_sum {A} (weight : A -> nat) (xs : list A) : nat :=
  fold_right (fun x n => weight x + n) 0 xs.

(** Code size counts every destination and operand occurrence. *)
Definition build_code_vars {K} (cs : list (positive * K * list positive)) : nat :=
  length (flat_map (fun '(x, _, xs) => x :: xs) cs).

(** Exit observations exclude outgoing block argument rows. *)
Definition build_exit_base {G} (e : exit positive G) : nat :=
  match e with
  | Jump _ _ => 0
  | Branch _ xs _ _ _ _ => length xs
  | Return xs => length xs
  end.

(** A block's unchanged payload consists of its code and exit observations. *)
Definition build_core_size {K G} (body : block positive K G) : nat :=
  build_code_vars (code _ _ _ body) + build_exit_base (term _ _ _ body) +
    length (code _ _ _ body).

(** Every successful environment lookup returns a value within the given width. *)
Definition build_range_width (rho : ptrie positive) (width : nat) : Prop :=
  forall x y, trie_get x rho = Some y -> Pos.size_nat y <= width.

(** The values of a certificate row fit the given width. *)
Definition build_names_width (names : renaming) (width : nat) : Prop :=
  forall x y, In (x, y) names -> Pos.size_nat y <= width.

(** Mapping an inventory transports its weight function. *)
Lemma build_sum_map {A B} (f : A -> B) weight xs :
  build_sum weight (map f xs) = build_sum (fun x => weight (f x)) xs.
Proof.
  unfold build_sum; induction xs; cbn [map fold_right]; congruence.
Qed.

(** A constant weight contributes once per listed item. *)
Lemma build_sum_const {A} (xs : list A) n : build_sum (fun _ => n) xs = length xs * n.
Proof.
  unfold build_sum; induction xs; cbn [fold_right length]; lia.
Qed.

(** Pointwise addition separates into the two weighted totals. *)
Lemma build_sum_add {A} (f g : A -> nat) xs :
  build_sum (fun x => f x + g x) xs = build_sum f xs + build_sum g xs.
Proof.
  apply val_sum_add.
Qed.

(** Weights that agree on the inventory have equal totals. *)
Lemma build_sum_ext {A} (f g : A -> nat) xs :
  (forall x, In x xs -> f x = g x) -> build_sum f xs = build_sum g xs.
Proof.
  intro Hsame; induction xs as [|x rest IH]; [reflexivity|].
  cbn [build_sum fold_right]. rewrite Hsame by (left; reflexivity).
  f_equal; apply IH. intros y Hin; apply Hsame; right; exact Hin.
Qed.

(** An inventory with distinct keys selects its listed value at each key. *)
Lemma build_lookup_present {A} : forall (xs : list (positive * A)) x value,
  NoDup (map fst xs) -> In (x, value) xs -> lookup x xs = Some value.
Proof.
  induction xs as [|[a item] rest IH]; intros x value Hunique Hin; [contradiction|].
  inversion Hunique as [|? ? Hfresh Htail]; subst.
  destruct Hin as [Heq|Hin].
  - inversion Heq; subst. cbn [lookup]. now rewrite Pos.eqb_refl.
  - cbn [lookup]. destruct (Pos.eqb x a) eqn:Heq.
    + apply Pos.eqb_eq in Heq; subst x. exfalso; apply Hfresh.
      apply in_map with (f := fst) in Hin; exact Hin.
    + apply IH; assumption.
Qed.

(** Materialization preserves the source block identifiers and their order. *)
Lemma build_materialize_keys {K G} : forall original bodies result,
  @build_materialize K G original bodies = Some result -> map fst result = map fst original.
Proof.
  induction original as [|[b body] rest IH]; intros bodies result Hrun.
  - cbn [build_materialize] in Hrun; inversion Hrun; reflexivity.
  - cbn [build_materialize] in Hrun.
    destruct (trie_get b bodies) as [out|] eqn:Hout; [|discriminate].
    destruct (build_materialize rest bodies) as [tail|] eqn:Htail; [|discriminate].
    inversion Hrun; subst result; cbn [map fst]. f_equal. now apply IH in Htail.
Qed.

(** Every materialized block comes from the indexed output body at its source key. *)
Lemma build_materialize_member {K G} : forall original bodies result b body,
  @build_materialize K G original bodies = Some result -> In (b, body) result ->
  In b (map fst original) /\ trie_get b bodies = Some body.
Proof.
  induction original as [|[a item] rest IH]; intros bodies result b body Hrun Hin.
  - cbn [build_materialize] in Hrun; inversion Hrun; subst; contradiction.
  - cbn [build_materialize] in Hrun.
    destruct (trie_get a bodies) as [out|] eqn:Hout; [|discriminate].
    destruct (build_materialize rest bodies) as [tail|] eqn:Htail; [|discriminate].
    inversion Hrun; subst result. destruct Hin as [Heq|Hin].
    + inversion Heq; subst. split; [left; reflexivity|assumption].
    + destruct (IH _ _ _ _ Htail Hin) as [Hmember Hget].
      split; [right; exact Hmember|exact Hget].
Qed.

(** Successful operand rewriting preserves arity. *)
Lemma build_values_length : forall xs rho ys,
  build_values rho xs = Some ys -> length ys = length xs.
Proof.
  induction xs as [|x rest IH]; intros rho ys Hrun.
  - cbn [build_values] in Hrun; inversion Hrun; reflexivity.
  - cbn [build_values] in Hrun.
    destruct (trie_get x rho) as [y|]; [|discriminate].
    destruct (build_values rho rest) as [tail|] eqn:Htail; [|discriminate].
    inversion Hrun; subst ys. cbn [length]; f_equal. now apply IH in Htail.
Qed.

(** Operand rewriting retains the width bound of the source environment. *)
Lemma build_values_width : forall xs rho ys width,
  build_range_width rho width -> build_values rho xs = Some ys ->
  forall y, In y ys -> Pos.size_nat y <= width.
Proof.
  induction xs as [|x rest IH]; intros rho ys width Hwidth Hrun value Hin.
  - cbn [build_values] in Hrun; inversion Hrun; subst; contradiction.
  - cbn [build_values] in Hrun.
    destruct (trie_get x rho) as [y|] eqn:Hget; [|discriminate].
    destruct (build_values rho rest) as [tail|] eqn:Htail; [|discriminate].
    inversion Hrun; subst ys. destruct Hin as [Heq|Hin].
    + subst value. now apply (Hwidth x y).
    + exact (IH _ _ _ Hwidth Htail _ Hin).
Qed.

(** Projection retains exactly the requested old variable row. *)
Lemma build_project_keys : forall xs b phis rho inputs names,
  build_project b phis xs rho inputs = Some names -> map fst names = xs.
Proof.
  induction xs as [|x rest IH]; intros b phis rho inputs names Hrun.
  - cbn [build_project] in Hrun; inversion Hrun; reflexivity.
  - cbn [build_project] in Hrun.
    destruct (if val_mem phis x then Some (build_phi_name b x)
      else match trie_get x rho with Some y => Some y | None => trie_get x inputs end)
      as [y|] eqn:Hname; [|discriminate].
    destruct (build_project b phis rest rho inputs) as [tail|] eqn:Htail; [|discriminate].
    inversion Hrun; subst names. cbn [map fst]; f_equal. now apply IH in Htail.
Qed.

(** Projected values come from bounded environments or bounded parameter names. *)
Lemma build_project_width : forall xs b phis rho inputs names width,
  (forall x, In x xs -> Pos.size_nat (build_phi_name b x) <= width) ->
  build_range_width rho width -> build_range_width inputs width ->
  build_project b phis xs rho inputs = Some names -> build_names_width names width.
Proof.
  induction xs as [|x rest IH]; intros b phis rho inputs names width Hphi Hrho Hinputs Hrun.
  - cbn [build_project] in Hrun; inversion Hrun; subst. intros a y Hin; contradiction.
  - cbn [build_project] in Hrun.
    destruct (if val_mem phis x then Some (build_phi_name b x)
      else match trie_get x rho with Some y => Some y | None => trie_get x inputs end)
      as [y|] eqn:Hname; [|discriminate].
    destruct (build_project b phis rest rho inputs) as [tail|] eqn:Htail; [|discriminate].
    inversion Hrun; subst names. intros a value Hin; destruct Hin as [Heq|Hin].
    + inversion Heq; subst a value. destruct (val_mem phis x) eqn:Hmem.
      * inversion Hname; subst y. apply Hphi; left; reflexivity.
      * destruct (trie_get x rho) as [old|] eqn:Hget.
        -- inversion Hname; subst y. now apply (Hrho x old).
        -- now apply (Hinputs x y).
    + eapply IH; [|exact Hrho|exact Hinputs|exact Htail|exact Hin].
      intros z Hz; apply Hphi; right; exact Hz.
Qed.

(** Indexing a bounded renaming preserves its value width bound. *)
Lemma build_index_width names width :
  build_names_width names width -> build_range_width (val_index names) width.
Proof.
  intros Hwidth x y Hget. rewrite val_index_lookup in Hget.
  apply val_lookup_in in Hget. exact (Hwidth x y Hget).
Qed.

(** Installing one bounded value preserves an environment's range bound. *)
Lemma build_set_width rho x y width : build_range_width rho width ->
  Pos.size_nat y <= width -> build_range_width (PTrieCode.set x y rho) width.
Proof.
  intros Hwidth Hy a value Hget. destruct (Pos.eq_dec a x) as [Heq|Hneq].
  - subst a; rewrite PTrie.get_set_same in Hget; inversion Hget; subst; exact Hy.
  - rewrite PTrie.get_set_other in Hget by exact Hneq. now apply (Hwidth a value).
Qed.

(** Exit-variable occurrences split into observations and outgoing arguments. *)
Lemma build_exit_length {G} (e : exit positive G) :
  length (exit_uses e) = build_exit_base e + exit_arg_count e.
Proof.
  destruct e; cbn [exit_uses build_exit_base exit_arg_count]; rewrite ?length_app; lia.
Qed.

(** Function size is its input count plus the complete contribution of each block. *)
Lemma build_function_sum {K G} (p : func positive K G) :
  function_size p = length (inputs _ _ _ p) +
    build_sum (fun item => 1 + length (params _ _ _ (snd item)) +
      build_core_size (snd item) + exit_arg_count (term _ _ _ (snd item))) (blocks _ _ _ p).
Proof.
  unfold function_size, function_vars, build_core_size, build_code_vars, build_sum.
  rewrite length_app. induction (blocks _ _ _ p) as [|[b body] rest IH].
  - cbn [flat_map fold_right length]; lia.
  - cbn [flat_map fold_right length snd]. rewrite !length_app, build_exit_length. lia.
Qed.

(** Every instruction contributes to its block's unchanged payload size. *)
Lemma build_core_code {K G} (body : block positive K G) :
  length (code _ _ _ body) <= build_core_size body.
Proof.
  unfold build_core_size; lia.
Qed.

(** An identifier fitting the given width is below the corresponding power of two. *)
Lemma build_positive_value x width : Pos.size_nat x <= width -> Pos.to_nat x < 2 ^ width.
Proof.
  intro Hwidth. pose proof (Pos.size_nat_upper x).
  pose proof (Nat.pow_le_mono_r 2 (Pos.size_nat x) width ltac:(discriminate) Hwidth); lia.
Qed.

(** Injective conversion to unary naturals preserves distinct positive identifiers. *)
Lemma build_nodup_nat xs : NoDup xs -> NoDup (map Pos.to_nat xs).
Proof.
  intro Hunique; induction Hunique as [|x rest Hfresh Hunique IH]; [constructor|].
  cbn [map]; constructor; [|exact IH]. intro Hin; apply in_map_iff in Hin.
  destruct Hin as [y [Heq Hin]]. apply Pos2Nat.inj in Heq; subst y; contradiction.
Qed.

(** A distinct identifier inventory fitting a width has at most that many bit patterns. *)
Lemma build_width_length xs width : NoDup xs ->
  (forall x, In x xs -> Pos.size_nat x <= width) -> length xs <= 2 ^ width.
Proof.
  intros Hunique Hwidth.
  assert (Hincl : incl (map Pos.to_nat xs) (seq 0 (2 ^ width))).
  { intros n Hin; apply in_map_iff in Hin as [x [Heq Hin]]; subst n.
    apply in_seq. split; [lia|]. now apply build_positive_value, Hwidth. }
  pose proof (NoDup_incl_length (build_nodup_nat xs Hunique) Hincl) as Hlength.
  rewrite length_map, length_seq in Hlength; exact Hlength.
Qed.

(** The source width includes the bit size of its syntax count. *)
Lemma build_function_size_bits {K G} (p : func positive K G) :
  Pos.size_nat (Pos.of_succ_nat (function_size p)) <= function_width p.
Proof.
  unfold function_width; rewrite val_cfg_graph_max; apply Nat.le_max_r.
Qed.

(** The syntax count and its successor fit below the source width's power of two. *)
Lemma build_function_size_value {K G} (p : func positive K G) :
  function_size p + 1 < 2 ^ function_width p.
Proof.
  pose proof (build_positive_value _ _ (build_function_size_bits p)) as Hvalue.
  rewrite SuccNat2Pos.id_succ in Hvalue; lia.
Qed.

(** The total instruction count is bounded by function syntax size. *)
Lemma build_function_code_size {K G} (p : func positive K G) :
  build_sum (fun item => length (code _ _ _ (snd item))) (blocks _ _ _ p) <=
    function_size p.
Proof.
  unfold function_size, build_sum; lia.
Qed.

(** The positive allocation number denotes the counter's successor. *)
Lemma build_succ_pos_value i : Pos.to_nat (N.succ_pos i) = S (N.to_nat i).
Proof.
  destruct i; [reflexivity|]. cbn; now rewrite Pos2Nat.inj_succ.
Qed.

(** Instruction tags add two bits to a counter bounded by source syntax. *)
Lemma build_instruction_bits {K G} (p : func positive K G) i :
  N.to_nat i < function_size p ->
    Pos.size_nat (build_instruction_name i) <= function_width p + 2.
Proof.
  intro Hbound. unfold build_instruction_name; cbn [Pos.size_nat].
  pose proof (build_function_size_bits p) as Hsize.
  assert (Hlt : (N.succ_pos i < Pos.of_succ_nat (function_size p))%positive).
  { apply Pos2Nat.inj_lt. rewrite build_succ_pos_value, SuccNat2Pos.id_succ; lia. }
  pose proof (Pos.size_nat_monotone _ _ Hlt); lia.
Qed.

(** Input tags add two bits to a listed source variable. *)
Lemma build_input_bits {K G} (p : func positive K G) x :
  In x (inputs _ _ _ p) -> Pos.size_nat (build_input_name x) <= function_width p + 2.
Proof.
  intro Hin; pose proof (val_input_width p x Hin). unfold build_input_name.
  cbn [Pos.size_nat]; lia.
Qed.

(** Parameter names fit the combined widths of their block and source variable. *)
Lemma build_phi_bits b x width : Pos.size_nat b <= width -> Pos.size_nat x <= width ->
  Pos.size_nat (build_phi_name b x) <= 3 * width + 2.
Proof.
  intros Hb Hx. unfold build_phi_name; cbn [Pos.size_nat]. rewrite glue_bits; lia.
Qed.

(** This inventory includes every parameter, destination and use in a block. *)
Definition build_body_vars {K G} (body : block positive K G) : list positive :=
  params _ _ _ body ++ flat_map (fun '(x, _, xs) => x :: xs) (code _ _ _ body) ++
    exit_uses (term _ _ _ body).

(** Both the old keys and new values of a renaming fit the given width. *)
Definition build_names_bounded (names : renaming) (width : nat) : Prop :=
  forall x y, In (x, y) names -> Pos.size_nat x <= width /\ Pos.size_nat y <= width.

(** A bound on both components also bounds a renaming's new values. *)
Lemma build_bounded_values names width :
  build_names_bounded names width -> build_names_width names width.
Proof.
  intros Hbound x y Hin; exact (proj2 (Hbound x y Hin)).
Qed.

(** Projection preserves bounded old keys and produces bounded new values. *)
Lemma build_project_bounded xs b phis rho inputs names width :
  (forall x, In x xs -> Pos.size_nat x <= width) ->
  (forall x, In x xs -> Pos.size_nat (build_phi_name b x) <= width) ->
  build_range_width rho width -> build_range_width inputs width ->
  build_project b phis xs rho inputs = Some names -> build_names_bounded names width.
Proof.
  intros Hkeys Hphi Hrho Hinputs Hrun x y Hin. split.
  - apply Hkeys. rewrite <- (build_project_keys _ _ _ _ _ _ Hrun).
    apply in_map with (f := fst) in Hin; exact Hin.
  - exact (build_project_width _ _ _ _ _ _ _ Hphi Hrho Hinputs Hrun x y Hin).
Qed.

(** A uniform item bound multiplies by the inventory length. *)
Lemma build_sum_bound {A} (f : A -> nat) xs amount :
  (forall x, In x xs -> f x <= amount) -> build_sum f xs <= length xs * amount.
Proof.
  intro Hbound. rewrite <- build_sum_const.
  apply val_sum_mono; exact Hbound.
Qed.

(** Matching distinct source keys transfers any preserved payload weight. *)
Lemma build_corresponding_sum {A B} (source : list (positive * A))
    (target : list (positive * B)) (before : A -> nat) (after : B -> nat) :
  NoDup (map fst source) -> map fst target = map fst source ->
  (forall b value, In (b, value) target -> exists original,
    lookup b source = Some original /\ after value = before original) ->
  build_sum (fun item => after (snd item)) target =
    build_sum (fun item => before (snd item)) source.
Proof.
  intros Hunique Hkeys Hvalues.
  set (weight := fun b => match lookup b source with Some a => before a | None => 0 end).
  assert (Htarget : build_sum (fun item => after (snd item)) target =
      build_sum weight (map fst target)).
  { rewrite build_sum_map. apply build_sum_ext; intros [b value] Hin; cbn [fst snd].
    destruct (Hvalues b value Hin) as [original [Hlookup Hweight]].
    unfold weight; rewrite Hlookup; exact Hweight. }
  rewrite Htarget, Hkeys, build_sum_map.
  apply build_sum_ext; intros [b value] Hin; cbn [fst snd].
  unfold weight; rewrite (build_lookup_present _ _ _ Hunique Hin); reflexivity.
Qed.

(** Syntax size separates parameters, unchanged payload and outgoing arguments. *)
Lemma build_function_decompose {K G} (p : func positive K G) :
  function_size p = length (inputs _ _ _ p) + length (blocks _ _ _ p) +
    build_sum (fun item => length (params _ _ _ (snd item))) (blocks _ _ _ p) +
    build_sum (fun item => build_core_size (snd item)) (blocks _ _ _ p) + function_edge_args p.
Proof.
  rewrite build_function_sum. unfold function_edge_args.
  fold (build_sum (fun item => exit_arg_count (term _ _ _ (snd item))) (blocks _ _ _ p)).
  rewrite !build_sum_add, build_sum_const; lia.
Qed.

(** Certificate size counts row headers and the two components of every environment pair. *)
Lemma build_cert_decompose c :
  cert_size c = length (fst c) +
    2 * build_sum (fun row => length (snd row)) (fst c) + build_live_rows_size (snd c).
Proof.
  unfold cert_size, build_live_rows_size, build_sum.
  induction (fst c) as [|[b row] rest IH]; cbn [fold_right length snd] in *; lia.
Qed.

(** A block exit has at most two target occurrences. *)
Lemma build_exit_target_count {G} (ending : exit positive G) : length (exit_targets ending) <= 2.
Proof.
  destruct ending; cbn [exit_targets length]; lia.
Qed.



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

  (** A conservative guard caps repeated frontier scans by already charged input and rows. *)
  Definition placement_allowed (p : P.t) (q : Q.t) (frontier : ptrie (list positive))
      (live : list (positive * list positive)) (vars : list positive) : bool :=
    let entries := fold_right (fun b n => length (frontier_row frontier b) + n) 0 (BC.nodes q) in
    N.leb (N.of_nat (length vars) * N.of_nat entries)
      (8 * N.of_nat (function_size p + build_live_rows_size live + entries + 1)).

  Definition produce (p : P.t) : option (P.t * cert) :=
    let q := R.prepare p in
    if build_blocks_unique (blocks _ _ _ p) Empty then
    let g := DG.prepare (cfg_graph (BC.nodes q) (BC.edges q) (BC.src q) (BC.dst q)) in
    let result := D.build g (entry _ _ _ p) in
    if D.check g (entry _ _ _ p) (fst result) (snd result) then
      let t := D.tree g (entry _ _ _ p) (fst result) (snd result) in
      let frontier := F.df g t in
      let live := L.live_in p in
      let vars := U.universe q in
      if placement_allowed p q frontier live vars then
        let defs := def_index p in
        let sets := live_sets live in
        let rows := placement_with frontier defs sets vars in
        rename p t rows live
      else None
    else None
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
  TimeFun placement_allowed.
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
  Definition k_wrap : N := 16.
  Definition k_size : N := 16.
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
    intros p s c. unfold produce.
    destruct (build_blocks_unique (blocks _ _ _ p) Empty); [|discriminate].
    change ((if D.check (graph p) (entry _ _ _ p)
      (fst (dom_result p)) (snd (dom_result p)) then
      if placement_allowed p (R.prepare p) (frontiers p) (L.live_in p)
        (U.universe (R.prepare p)) then
        rename p (dom_tree p) (placement p) (L.live_in p) else None
      else None) = Some (s, c) ->
      D.check (graph p) (entry _ _ _ p) (fst (dom_result p)) (snd (dom_result p)) = true /\
      rename p (dom_tree p) (placement p) (L.live_in p) = Some (s, c)).
    destruct (D.check (graph p) (entry _ _ _ p) (fst (dom_result p)) (snd (dom_result p)))
      eqn:Hchecked; [|discriminate].
    destruct (placement_allowed p (R.prepare p) (frontiers p) (L.live_in p)
      (U.universe (R.prepare p))); [intro Hrename; now split|discriminate].
  Qed.

  (** Renaming preserves code arities and allocates exactly one counter value per instruction. *)
  Lemma rename_code_shape : forall cs rho names fresh out final final_names next,
    rename_code cs rho names fresh = Some (out, final, final_names, next) ->
    length out = length cs /\ build_code_vars out = build_code_vars cs /\
    N.to_nat next = N.to_nat fresh + length cs.
  Proof.
    induction cs as [|[[x op] xs] rest IH];
      intros rho names fresh out final final_names next Hrun.
    - cbn [rename_code] in Hrun; inversion Hrun; subst. cbn; auto.
    - cbn [rename_code] in Hrun.
      destruct (build_values rho xs) as [ys|] eqn:Hvalues; [|discriminate].
      destruct (rename_code rest (PTrieCode.set x (build_instruction_name fresh) rho)
        ((x, build_instruction_name fresh) :: names) (N.succ fresh))
        as [[[[tail rho'] names'] next']|] eqn:Htail; [|discriminate].
      inversion Hrun; subst out final final_names next.
      destruct (IH _ _ _ _ _ _ _ Htail) as [Hlength [Hvars Hnext]].
      pose proof (build_values_length _ _ _ Hvalues) as Hargs.
      cbn [length]. unfold build_code_vars at 1 2.
      cbn [flat_map]. rewrite !length_app. cbn [length].
      fold (@build_code_vars O.K tail) (@build_code_vars O.K rest).
      rewrite N2Nat.inj_succ in Hnext. repeat split; lia.
  Qed.

  (** Renaming preserves exit observations and supplies the target parameter row arities. *)
  Lemma rename_exit_shape : forall ending rows rho out,
    rename_exit ending rows rho = Some out ->
    build_exit_base out = build_exit_base ending /\ exit_targets out = exit_targets ending /\
    exit_arg_count out = build_sum (fun b => length (index_row rows b)) (exit_targets ending).
  Proof.
    intros ending rows rho out Hrun; destruct ending as [b old|g xs b old c old'|xs].
    - destruct old as [|x rest]; [|discriminate].
      cbn [rename_exit] in Hrun.
      destruct (build_values rho (index_row rows b)) as [args|] eqn:Hargs; [|discriminate].
      inversion Hrun; subst out. pose proof (build_values_length _ _ _ Hargs).
      cbn [build_exit_base exit_targets exit_arg_count build_sum fold_right].
      repeat split; congruence || lia.
    - destruct old as [|x rest], old' as [|y tail]; try discriminate.
      cbn [rename_exit] in Hrun.
      destruct (build_values rho xs) as [args|] eqn:Hargs; [|discriminate].
      destruct (build_values rho (index_row rows b)) as [yes_args|] eqn:Hyes;
        [|discriminate].
      destruct (build_values rho (index_row rows c)) as [no_args|] eqn:Hno;
        [|discriminate].
      inversion Hrun; subst out. pose proof (build_values_length _ _ _ Hargs).
      pose proof (build_values_length _ _ _ Hyes).
      pose proof (build_values_length _ _ _ Hno).
      cbn [build_exit_base exit_targets exit_arg_count build_sum fold_right].
      repeat split; congruence || lia.
    - cbn [rename_exit] in Hrun.
      destruct (build_values rho xs) as [args|] eqn:Hargs; [|discriminate].
      inversion Hrun; subst out. pose proof (build_values_length _ _ _ Hargs).
      cbn [build_exit_base exit_targets exit_arg_count build_sum fold_right].
      repeat split; congruence || lia.
  Qed.

  (** A source block pays for exactly the instructions in its selected body. *)
  Definition source_code_weight (p : P.t) (b : positive) : nat :=
    match lookup b (blocks _ _ _ p) with
    | Some body => length (code _ _ _ body)
    | None => 0
    end.

  (** Each cached body is a source body that has not been emitted;
      emitted rows pay for fresh IDs. *)
  Definition rename_cache (p : P.t) (st : rename_state O.K O.G) : Prop :=
    NoDup (map fst (renamed_blocks _ _ st)) /\
    (forall b body, trie_get b (rename_bodies _ _ st) = Some body ->
      lookup b (blocks _ _ _ p) = Some body /\ ~ In b (map fst (renamed_blocks _ _ st))) /\
    N.to_nat (next_value _ _ st) =
      build_sum (source_code_weight p) (map fst (renamed_blocks _ _ st)).

  (** The initial cache contains source bodies and has allocated no instruction names. *)
  Lemma rename_cache_init p : rename_cache p (rename_init p).
  Proof.
    unfold rename_cache, rename_init; cbn [renamed_blocks rename_bodies next_value map].
    split; [constructor|]. split; [|reflexivity].
    intros b body Hget; rewrite val_index_lookup in Hget; split; [exact Hget|tauto].
  Qed.

  (** Removing an emitted body preserves cache ownership and the allocation account. *)
  Lemma rename_cache_emit p bodies tasks output envs fresh b body kids names cs e next :
    rename_cache p (RenameState O.K O.G bodies tasks output envs fresh) ->
    trie_get b bodies = Some body ->
    N.to_nat next = N.to_nat fresh + length (code _ _ _ body) ->
    rename_cache p (RenameState O.K O.G (PTrieCode.remove b bodies) (kids ++ tasks)
      ((b, Block positive O.K O.G names cs e) :: output) ((b, []) :: envs) next).
  Proof.
    intros [Hdistinct [Hcache Hfresh]] Hget Hnext.
    destruct (Hcache b body Hget) as [Hsource Hunused].
    unfold rename_cache; cbn [rename_bodies renamed_blocks next_value map fst].
    split; [constructor; assumption|]. split.
    - intros a original Hremaining. destruct (Pos.eq_dec a b) as [Heq|Hneq].
      + subst a; rewrite PTrie.get_remove_same in Hremaining; discriminate.
      + rewrite PTrie.get_remove_other in Hremaining by exact Hneq.
        destruct (Hcache a original Hremaining) as [Horiginal Habsent].
        split; [exact Horiginal|]. cbn [In]; intuition congruence.
    - cbn [build_sum fold_right]. unfold source_code_weight at 1. rewrite Hsource.
      cbn [next_value renamed_blocks] in Hfresh. unfold build_sum in Hfresh; lia.
  Qed.

  (** Every continuing rename step preserves the cache and allocation invariant. *)
  Lemma rename_cache_step p t rows live_index inputs live st next :
    rename_cache p st ->
    rename_step_indexed p t rows live_index inputs live st = inl next -> rename_cache p next.
  Proof.
    destruct st as [bodies tasks output envs fresh].
    destruct tasks as [|[b inherited] tasks]; [discriminate|].
    intros Hcache Hstep; cbn [rename_step_indexed] in Hstep.
    destruct (trie_get b bodies) as [body|] eqn:Hget.
    - destruct (params _ _ _ body) as [|x rest]; [|discriminate].
      destruct (if Pos.eqb b (entry _ _ _ p) then
        match index_row rows b with [] => Some inherited | _ => None end
        else build_project b (val_set (index_row rows b)) (index_row live_index b)
          (val_index inherited) inputs) as [names|] eqn:Hnames; [|discriminate].
      destruct (rename_code (code _ _ _ body) (val_index names) names fresh)
        as [[[[cs final] final_names] last]|] eqn:Hcode; [|discriminate].
      destruct (rename_exit (term _ _ _ body) rows final) as [ending|] eqn:Hexit;
        [|discriminate].
      destruct (rename_children (children t b) rows live_index final inputs)
        as [kids|] eqn:Hkids; [|discriminate].
      inversion Hstep; subst next.
      pose proof (rename_code_shape _ _ _ _ _ _ _ _ Hcode) as [_ [_ Hlast]].
      exact (rename_cache_emit p bodies tasks output envs fresh b body kids
        (map (build_phi_name b) (index_row rows b)) cs ending last Hcache Hget Hlast).
    - inversion Hstep; subst next; exact Hcache.
  Qed.

  (** Distinct emitted blocks bound the allocation counter by the source instruction count. *)
  Lemma rename_cache_counter p st : rename_cache p st ->
    N.to_nat (next_value _ _ st) <=
      build_sum (fun item => length (code _ _ _ (snd item))) (blocks _ _ _ p).
  Proof.
    intros [Hunique [_ Hcounter]]. rewrite Hcounter.
    exact (val_lookup_sum (blocks _ _ _ p) (map fst (renamed_blocks _ _ st))
      (fun body => length (code _ _ _ body)) Hunique).
  Qed.

  (** A cached block's instructions still fit in the remaining source allocation budget. *)
  Lemma rename_cache_next p st b body : rename_cache p st ->
    trie_get b (rename_bodies _ _ st) = Some body ->
    N.to_nat (next_value _ _ st) + length (code _ _ _ body) <=
      build_sum (fun item => length (code _ _ _ (snd item))) (blocks _ _ _ p).
  Proof.
    intros [Hunique [Hcache Hcounter]] Hget.
    destruct (Hcache b body Hget) as [Hsource Hunused].
    assert (Hnew_unique : NoDup (b :: map fst (renamed_blocks _ _ st)))
      by (constructor; assumption).
    pose proof (val_lookup_sum (blocks _ _ _ p) (b :: map fst (renamed_blocks _ _ st))
      (fun body => length (code _ _ _ body)) Hnew_unique) as Hbound.
    cbn [fold_right] in Hbound; rewrite Hsource in Hbound.
    rewrite Hcounter. unfold build_sum, source_code_weight; lia.
  Qed.

  (** Every universe variable occurs in the prepared syntax inventory. *)
  Lemma universe_occurs p x : In x (U.universe (R.prepare p)) ->
    In x (U.occurrences (R.prepare p)).
  Proof.
    intro Hin; apply U.universe_spec in Hin. unfold U.occurrences.
    destruct Hin as [[e [He [Hu|Hd]]]|[n [Hn Hx]]].
    - apply in_or_app; left; apply in_flat_map. exists e; split; [exact He|].
      apply in_or_app; now left.
    - apply in_or_app; left; apply in_flat_map. exists e; split; [exact He|].
      apply in_or_app; now right.
    - apply in_or_app; right; apply in_flat_map. exists n; auto.
  Qed.

  (** Universe variables fit the source function's identifier width. *)
  Lemma universe_width p x : In x (U.universe (R.prepare p)) ->
    Pos.size_nat x <= function_width p.
  Proof.
    intro Hin. pose proof (PB.occurrence_width_le p) as Hbound.
    assert (Hx : Pos.size_nat x <= U.occurrence_width (R.prepare p)).
    { apply universe_occurs in Hin. unfold U.occurrence_width.
      change (Pos.size_nat x <= fold_right Nat.max 0
        (map Pos.size_nat (U.occurrences (R.prepare p)))).
      induction (U.occurrences (R.prepare p)) as [|a rest IH]; [contradiction|].
      cbn [map fold_right]. destruct Hin as [Heq|Hin].
      - subst a; apply Nat.le_max_l.
      - eapply Nat.le_trans; [apply IH; exact Hin|apply Nat.le_max_r]. }
    lia.
  Qed.

  (** The distinct source universe is bounded by the number of available identifier bit patterns. *)
  Lemma universe_count p : length (U.universe (R.prepare p)) <= 2 ^ function_width p.
  Proof.
    apply build_width_length; [apply U.universe_nodup|apply universe_width].
  Qed.

  (** Every variable in a selected live row fits the source width. *)
  Lemma live_row_width p b x : In x (index_row (val_index (L.live_in p)) b) ->
    Pos.size_nat x <= function_width p.
  Proof.
    unfold index_row; rewrite val_index_lookup.
    destruct (lookup b (L.live_in p)) as [row|] eqn:Hrow; [|contradiction].
    intro Hin. apply val_lookup_in in Hrow.
    destruct (L.live_in_ids p (b, row) Hrow) as [_ Hvars].
    apply universe_width; apply Hvars; exact Hin.
  Qed.

  (** Each variable adds at most one entry to a particular parameter row. *)
  Lemma placement_row_length frontier defs live vars b :
    length (index_row (placement_with frontier defs live vars) b) <= length vars.
  Proof.
    induction vars as [|x rest IH].
    - unfold placement_with, index_row; cbn [fold_right]; rewrite PTrie.get_empty; cbn; lia.
    - change (length (index_row
        (fold_right (fun target acc => PTrieCode.set target (x :: index_row acc target) acc)
          (placement_with frontier defs live rest) (place_var frontier defs live x)) b) <=
        S (length rest)).
      rewrite build_rows_lookup.
      + destruct (existsb (Pos.eqb b) (place_var frontier defs live x)); cbn [length]; lia.
      + unfold place_var; apply NoDup_filter; apply F.idf_unique.
  Qed.

  (** Every placed variable fits the source width. *)
  Lemma placement_row_width p b x : In x (index_row (placement p) b) ->
    Pos.size_nat x <= function_width p.
  Proof.
    intro Hin; apply F3a_placement in Hin as [Hin _]; now apply universe_width.
  Qed.

  (** Distinct source variables produce distinct parameter rows. *)
  Lemma placement_with_unique frontier defs live vars : NoDup vars ->
    forall b, NoDup (index_row (placement_with frontier defs live vars) b).
  Proof.
    intro Hvars; induction Hvars as [|x rest Hfresh Hvars IH]; intro b.
    - unfold placement_with, index_row; cbn [fold_right].
      rewrite PTrie.get_empty; constructor.
    - change (NoDup (index_row
        (fold_right (fun target acc => PTrieCode.set target (x :: index_row acc target) acc)
          (placement_with frontier defs live rest) (place_var frontier defs live x)) b)).
      rewrite build_rows_lookup by
        (unfold place_var; apply NoDup_filter; apply F.idf_unique).
      destruct (existsb (Pos.eqb b) (place_var frontier defs live x)); [constructor|apply IH].
      + intro Hin; apply placement_with_spec in Hin as [Hin _]; contradiction.
      + apply IH.
  Qed.

  (** Every produced parameter row contains each old variable at most once. *)
  Lemma placement_row_unique p b : NoDup (index_row (placement p) b).
  Proof.
    unfold placement; apply placement_with_unique, U.universe_nodup.
  Qed.

  (** Adding one row entry increases a total over distinct keys by at most one. *)
  Lemma row_sum_set ids (rows : ptrie (list positive)) b x : NoDup ids ->
    build_sum (fun a => length (index_row (PTrieCode.set b (x :: index_row rows b) rows) a)) ids <=
      1 + build_sum (fun a => length (index_row rows a)) ids.
  Proof.
    intro Hunique.
    assert (Heq : build_sum
      (fun a => length (index_row (PTrieCode.set b (x :: index_row rows b) rows) a)) ids =
      build_sum (fun a => (if Pos.eqb a b then 1 else 0) + length (index_row rows a)) ids).
    { apply build_sum_ext; intros a Hin. destruct (Pos.eqb a b) eqn:Hsame.
      - apply Pos.eqb_eq in Hsame; subst a; unfold index_row at 1.
        rewrite PTrie.get_set_same; reflexivity.
      - apply Pos.eqb_neq in Hsame; unfold index_row at 1.
        rewrite PTrie.get_set_other by exact Hsame; reflexivity. }
    rewrite Heq, build_sum_add. pose proof (val_sum_single ids b 1 Hunique).
    unfold build_sum; lia.
  Qed.

  (** Adding one variable at several sites charges at most one entry per site occurrence. *)
  Lemma row_sum_sites ids sites (rows : ptrie (list positive)) x : NoDup ids ->
    build_sum (fun b => length (index_row
      (fold_right (fun target acc => PTrieCode.set target (x :: index_row acc target) acc)
        rows sites) b)) ids <=
      length sites + build_sum (fun b => length (index_row rows b)) ids.
  Proof.
    intro Hunique; induction sites as [|b rest IH]; [cbn [fold_right length]; lia|].
    cbn [fold_right length]. eapply Nat.le_trans; [apply row_sum_set; exact Hunique|lia].
  Qed.

  (** The total parameter row size is bounded by the number of placement incidences. *)
  Lemma placement_rows_size frontier defs live vars ids : NoDup ids ->
    build_sum (fun b => length (index_row (placement_with frontier defs live vars) b)) ids <=
      build_sum (fun x => length (place_var frontier defs live x)) vars.
  Proof.
    intro Hunique; induction vars as [|x rest IH].
    - unfold placement_with; cbn [fold_right].
      assert (Hzero : build_sum (fun b => length (index_row (@Empty (list positive)) b)) ids = 0).
      { clear Hunique; induction ids as [|b rest IHids]; [reflexivity|].
        cbn [build_sum fold_right]. unfold index_row at 1. rewrite PTrie.get_empty; exact IHids. }
      rewrite Hzero; reflexivity.
    - change (build_sum (fun b => length (index_row
        (fold_right (fun target acc => PTrieCode.set target (x :: index_row acc target) acc)
          (placement_with frontier defs live rest) (place_var frontier defs live x)) b)) ids <=
        length (place_var frontier defs live x) +
          build_sum (fun x => length (place_var frontier defs live x)) rest).
      eapply Nat.le_trans; [apply row_sum_sites; exact Hunique|lia].
  Qed.

  (** Distinct source blocks charge their parameter rows to the published placement work. *)
  Lemma placement_source_size p : NoDup (map fst (blocks _ _ _ p)) ->
    build_sum (fun b => length (index_row (placement p) b)) (map fst (blocks _ _ _ p)) <=
      placement_work p.
  Proof.
    intro Hunique. unfold placement.
    eapply Nat.le_trans; [apply placement_rows_size; exact Hunique|].
    unfold placement_work, build_sum. apply val_sum_mono; intros x Hin.
    unfold place_var. rewrite F2a_def_index. eapply Nat.le_trans; [apply filter_length_le|].
    unfold phi_sites.
    induction (F.idf (frontiers p) (definition_blocks p x)); cbn [length fold_right]; lia.
  Qed.

  (** A block's operator budget counts instruction symbols and its optional branch guard. *)
  Definition block_op_bits (body : block positive O.K O.G) : nat :=
    build_sum (fun i => K.bits (snd (fst i))) (code _ _ _ body) +
      match term _ _ _ body with Branch g _ _ _ _ _ => G.bits g | _ => 0 end.

  (** Code renaming preserves the instruction symbol bit total exactly. *)
  Lemma rename_code_op_bits : forall cs rho names fresh out final final_names next,
    rename_code cs rho names fresh = Some (out, final, final_names, next) ->
    build_sum (fun i => K.bits (snd (fst i))) out =
      build_sum (fun i => K.bits (snd (fst i))) cs.
  Proof.
    induction cs as [|[[x op] xs] rest IH];
      intros rho names fresh out final final_names next Hrun.
    - cbn [rename_code] in Hrun; inversion Hrun; reflexivity.
    - cbn [rename_code] in Hrun.
      destruct (build_values rho xs) as [ys|]; [|discriminate].
      destruct (rename_code rest (PTrieCode.set x (build_instruction_name fresh) rho)
        ((x, build_instruction_name fresh) :: names) (N.succ fresh))
        as [[[[tail rho'] names'] next']|] eqn:Htail; [|discriminate].
      inversion Hrun; subst out final final_names next.
      change (K.bits op + build_sum (fun i => K.bits (snd (fst i))) tail =
        K.bits op + build_sum (fun i => K.bits (snd (fst i))) rest).
      f_equal. exact (IH _ _ _ _ _ _ _ Htail).
  Qed.

  (** Exit renaming preserves the guard symbol bit total exactly. *)
  Lemma rename_exit_guard : forall ending rows rho out,
    rename_exit ending rows rho = Some out ->
    (match out with Branch g _ _ _ _ _ => G.bits g | _ => 0 end) =
      (match ending with Branch g _ _ _ _ _ => G.bits g | _ => 0 end).
  Proof.
    intros ending rows rho out Hrun; destruct ending as [b old|g xs b old c old'|xs].
    - destruct old as [|x rest]; [|discriminate]. cbn [rename_exit] in Hrun.
      destruct (build_values rho (index_row rows b)); [|discriminate].
      inversion Hrun; reflexivity.
    - destruct old as [|x rest], old' as [|y tail]; try discriminate.
      cbn [rename_exit] in Hrun.
      destruct (build_values rho xs); [|discriminate].
      destruct (build_values rho (index_row rows b)); [|discriminate].
      destruct (build_values rho (index_row rows c)); [|discriminate].
      inversion Hrun; reflexivity.
    - cbn [rename_exit] in Hrun. destruct (build_values rho xs); [|discriminate].
      inversion Hrun; reflexivity.
  Qed.

  (** An emitted body retains its source payload and uses the requested parameter arities. *)
  Definition renamed_body (p : P.t) (rows : ptrie (list positive)) b
      (out : block positive O.K O.G) : Prop :=
    exists original, lookup b (blocks _ _ _ p) = Some original /\
      length (params _ _ _ out) = length (index_row rows b) /\
      build_core_size out = build_core_size original /\
      exit_targets (term _ _ _ out) = exit_targets (term _ _ _ original) /\
      exit_arg_count (term _ _ _ out) =
        build_sum (fun target => length (index_row rows target))
          (exit_targets (term _ _ _ original)) /\ block_op_bits out = block_op_bits original.

  (** After its initial task, the entry has no cached body and cannot emit another environment. *)
  Definition rename_entry_phase (p : P.t) (st : rename_state O.K O.G) : Prop :=
    st = rename_init p \/ trie_get (entry _ _ _ p) (rename_bodies _ _ st) = None.

  (** Emitted payloads retain their source, and environment rows charge inputs or live rows. *)
  Definition rename_syntax (p : P.t) rows (live : list (positive * list positive))
      (st : rename_state O.K O.G) : Prop :=
    (forall b body, In (b, body) (renamed_blocks _ _ st) -> renamed_body p rows b body) /\
    map fst (renamed_envs _ _ st) = map fst (renamed_blocks _ _ st) /\
    (forall b names, In (b, names) (renamed_envs _ _ st) ->
      length names <= (if Pos.eqb b (entry _ _ _ p) then length (inputs _ _ _ p) else 0) +
        length (index_row (val_index live) b)) /\ rename_entry_phase p st.

  (** The loop tracks cache ownership together with syntax and certificate inventories. *)
  Definition rename_info (p : P.t) rows live st : Prop :=
    rename_cache p st /\ rename_syntax p rows live st.

  (** Initialization establishes the cache, syntax and certificate invariants. *)
  Lemma rename_info_init p rows live : rename_info p rows live (rename_init p).
  Proof.
    split; [apply rename_cache_init|]. unfold rename_syntax, rename_init.
    cbn [renamed_blocks renamed_envs map]. split; [intros b body Hin; contradiction|].
    split; [reflexivity|]. split; [intros b names Hin; contradiction|]. now left.
  Qed.

  (** The only task that can emit the entry inherits the original input renaming. *)
  Lemma rename_entry_inherited p bodies b inherited tasks output envs fresh body :
    rename_entry_phase p
      (RenameState O.K O.G bodies ((b, inherited) :: tasks) output envs fresh) ->
    trie_get b bodies = Some body -> b = entry _ _ _ p ->
    inherited = map (fun x => (x, build_input_name x)) (inputs _ _ _ p).
  Proof.
    intros [Hinitial|Hnone] Hget Hentry.
    - unfold rename_init in Hinitial. inversion Hinitial; reflexivity.
    - subst b; cbn [rename_bodies] in Hnone; congruence.
  Qed.

  (** Emitting a body leaves the entry retired after its initial task. *)
  Lemma rename_entry_phase_remove p bodies b inherited tasks output envs fresh body kids
      params' cs ending names next :
    rename_entry_phase p
      (RenameState O.K O.G bodies ((b, inherited) :: tasks) output envs fresh) ->
    trie_get b bodies = Some body ->
    rename_entry_phase p (RenameState O.K O.G (PTrieCode.remove b bodies) (kids ++ tasks)
      ((b, Block positive O.K O.G params' cs ending) :: output) ((b, names) :: envs) next).
  Proof.
    intros Hphase Hget; right; cbn [rename_bodies].
    destruct (Pos.eq_dec (entry _ _ _ p) b) as [Heq|Hneq].
    - subst b; apply PTrie.get_remove_same.
    - rewrite PTrie.get_remove_other by exact Hneq. destruct Hphase as [Hinitial|Hnone].
      + unfold rename_init in Hinitial; inversion Hinitial; congruence.
      + exact Hnone.
  Qed.

  (** Skipping a missing body also retires the initial entry task. *)
  Lemma rename_entry_phase_skip p bodies b inherited tasks output envs fresh :
    rename_entry_phase p
      (RenameState O.K O.G bodies ((b, inherited) :: tasks) output envs fresh) ->
    trie_get b bodies = None ->
    rename_entry_phase p (RenameState O.K O.G bodies tasks output envs fresh).
  Proof.
    intros [Hinitial|Hnone] Hget; right; [|exact Hnone].
    unfold rename_init in Hinitial; inversion Hinitial; subst; exact Hget.
  Qed.

  (** A successfully renamed block has the required source payload and target-row shape. *)
  Lemma renamed_body_emit p rows b body names fresh cs final final_names next ending :
    lookup b (blocks _ _ _ p) = Some body ->
    rename_code (code _ _ _ body) (val_index names) names fresh =
      Some (cs, final, final_names, next) ->
    rename_exit (term _ _ _ body) rows final = Some ending ->
    renamed_body p rows b
      (Block positive O.K O.G (map (build_phi_name b) (index_row rows b)) cs ending).
  Proof.
    intros Hsource Hcode Hexit. exists body; split; [exact Hsource|].
    pose proof (rename_code_shape _ _ _ _ _ _ _ _ Hcode) as [Hlength [Hvars Hnext]].
    pose proof (rename_code_op_bits _ _ _ _ _ _ _ _ Hcode) as Hops.
    pose proof (rename_exit_shape _ _ _ _ Hexit) as [Hbase [Htargets Hargs]].
    pose proof (rename_exit_guard _ _ _ _ Hexit) as Hguard.
    cbn [params code term]. rewrite length_map.
    unfold build_core_size, block_op_bits; cbn [code term].
    repeat split; congruence.
  Qed.

  (** An entry environment charges inputs, and every other environment charges its live row. *)
  Lemma rename_names_length p bodies b inherited tasks output envs fresh body rows live names :
    rename_entry_phase p
      (RenameState O.K O.G bodies ((b, inherited) :: tasks) output envs fresh) ->
    trie_get b bodies = Some body ->
    (if Pos.eqb b (entry _ _ _ p) then
      match index_row rows b with [] => Some inherited | _ => None end
      else build_project b (val_set (index_row rows b)) (index_row (val_index live) b)
        (val_index inherited)
        (val_index (map (fun x => (x, build_input_name x)) (inputs _ _ _ p)))) = Some names ->
    length names <= (if Pos.eqb b (entry _ _ _ p) then length (inputs _ _ _ p) else 0) +
      length (index_row (val_index live) b).
  Proof.
    intros Hphase Hget Hnames. destruct (Pos.eqb b (entry _ _ _ p)) eqn:Hentry.
    - destruct (index_row rows b) as [|x rest]; [|discriminate].
      inversion Hnames; subst names.
      apply Pos.eqb_eq in Hentry.
      rewrite (rename_entry_inherited _ _ _ _ _ _ _ _ _ Hphase Hget Hentry), length_map; lia.
    - apply build_project_keys in Hnames. apply f_equal with (f := @length positive) in Hnames.
      rewrite length_map in Hnames; lia.
  Qed.

  (** A continuing step preserves source payloads and the certificate row accounts. *)
  Lemma rename_syntax_step p t rows live st next :
    rename_info p rows live st -> rename_step p t rows live st = inl next ->
    rename_syntax p rows live next.
  Proof.
    destruct st as [bodies tasks output envs fresh].
    destruct tasks as [|[b inherited] tasks]; [discriminate|].
    intros [[Hunique [Hcache Hcounter]] [Hbodies [Henvs [Hnames Hphase]]]] Hstep.
    cbn [renamed_envs renamed_blocks] in Henvs.
    unfold rename_step in Hstep; cbn [rename_step_indexed] in Hstep.
    destruct (trie_get b bodies) as [body|] eqn:Hget.
    - destruct (params _ _ _ body) as [|x rest]; [|discriminate].
      destruct (if Pos.eqb b (entry _ _ _ p) then
        match index_row rows b with [] => Some inherited | _ => None end
        else build_project b (val_set (index_row rows b)) (index_row (val_index live) b)
          (val_index inherited)
          (val_index (map (fun x => (x, build_input_name x)) (inputs _ _ _ p))))
        as [names|] eqn:Hentry; [|discriminate].
      destruct (rename_code (code _ _ _ body) (val_index names) names fresh)
        as [[[[cs final] final_names] last]|] eqn:Hcode; [|discriminate].
      destruct (rename_exit (term _ _ _ body) rows final) as [ending|] eqn:Hexit;
        [|discriminate].
      destruct (rename_children (children t b) rows (val_index live) final
        (val_index (map (fun x => (x, build_input_name x)) (inputs _ _ _ p))))
        as [kids|] eqn:Hkids; [|discriminate].
      inversion Hstep; subst next.
      unfold rename_syntax; cbn [renamed_blocks renamed_envs map fst].
      split.
      + intros a out Hin; destruct Hin as [Heq|Hin].
        * inversion Heq; subst a out. eapply renamed_body_emit; [|exact Hcode|exact Hexit].
          exact (proj1 (Hcache b body Hget)).
        * exact (Hbodies _ _ Hin).
      + split; [now rewrite Henvs|]. split.
        * intros a row Hin; destruct Hin as [Heq|Hin].
          -- inversion Heq; subst a row.
             exact (rename_names_length _ _ _ _ _ _ _ _ _ _ _ _ Hphase Hget Hentry).
          -- exact (Hnames _ _ Hin).
        * eapply rename_entry_phase_remove; eassumption.
    - inversion Hstep; subst next. unfold rename_syntax.
      split; [exact Hbodies|]. split; [exact Henvs|]. split; [exact Hnames|].
      eapply rename_entry_phase_skip; eassumption.
  Qed.

  (** The cached rename loop preserves its complete inventory invariant. *)
  Lemma rename_info_step p t rows live st next :
    rename_info p rows live st -> rename_step p t rows live st = inl next ->
    rename_info p rows live next.
  Proof.
    intros Hinfo Hstep; split.
    - eapply rename_cache_step; [exact (proj1 Hinfo)|exact Hstep].
    - eapply rename_syntax_step; eassumption.
  Qed.

  (** Successful renaming restores source block order and exports distinct environment rows. *)
  Definition rename_result_info (p : P.t) rows live (s : P.t) (c : cert) : Prop :=
    entry _ _ _ s = entry _ _ _ p /\ inputs _ _ _ s = map build_input_name (inputs _ _ _ p) /\
    snd c = live /\ map fst (blocks _ _ _ s) = map fst (blocks _ _ _ p) /\
    (forall b body, In (b, body) (blocks _ _ _ s) -> renamed_body p rows b body) /\
    NoDup (map fst (fst c)) /\ incl (map fst (fst c)) (map fst (blocks _ _ _ p)) /\
    forall b names, In (b, names) (fst c) ->
      length names <= (if Pos.eqb b (entry _ _ _ p) then length (inputs _ _ _ p) else 0) +
        length (index_row (val_index live) b).

  (** A successful stop materializes the maintained inventory in source block order. *)
  Lemma rename_stop_info p t rows live st s c : rename_info p rows live st ->
    rename_step p t rows live st = inr (Some (s, c)) -> rename_result_info p rows live s c.
  Proof.
    destruct st as [bodies tasks output envs fresh].
    intros [[Hunique [Hcache Hcounter]] [Hbodies [Henvs [Hnames Hphase]]]] Hstop.
    cbn [renamed_envs renamed_blocks] in Henvs.
    unfold rename_step in Hstop. destruct tasks as [|[b inherited] tasks].
    - cbn [rename_step_indexed] in Hstop.
      destruct (build_materialize (blocks _ _ _ p) (val_index output)) as [bs|] eqn:Hout;
        [|discriminate].
      inversion Hstop; subst s c. unfold rename_result_info; cbn [entry inputs blocks fst snd].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [eapply build_materialize_keys; exact Hout|]. split.
      + intros b body Hin. destruct (build_materialize_member _ _ _ _ _ Hout Hin)
          as [_ Hget]. rewrite val_index_lookup in Hget. apply val_lookup_in in Hget.
        exact (Hbodies b body Hget).
      + split; [now rewrite Henvs|]. split; [|exact Hnames].
        rewrite Henvs. intros b Hin; apply in_map_iff in Hin as [[a body] [Heq Hin]].
        cbn [fst] in Heq; subst a.
        destruct (Hbodies b body Hin) as [original [Hsource _]].
        apply val_lookup_in in Hsource. apply in_map with (f := fst) in Hsource; exact Hsource.
    - cbn [rename_step_indexed] in Hstop.
      destruct (trie_get b bodies) as [body|]; [|discriminate].
      destruct (params _ _ _ body) as [|x rest]; [|discriminate].
      destruct (if Pos.eqb b (entry _ _ _ p) then
        match index_row rows b with [] => Some inherited | _ => None end
        else build_project b (val_set (index_row rows b)) (index_row (val_index live) b)
          (val_index inherited)
          (val_index (map (fun x => (x, build_input_name x)) (inputs _ _ _ p)))) as [names|];
        [|discriminate].
      destruct (rename_code (code _ _ _ body) (val_index names) names fresh)
        as [[[[cs final] final_names] last]|]; [|discriminate].
      destruct (rename_exit (term _ _ _ body) rows final); [|discriminate].
      destruct (rename_children (children t b) rows (val_index live) final
        (val_index (map (fun x => (x, build_input_name x)) (inputs _ _ _ p)))); discriminate.
  Qed.

  (** The bounded loop transfers its inventory invariant to every successful result. *)
  Lemma rename_loop_info p t rows live : forall fuel st s c,
    rename_info p rows live st ->
    loop_fuel (rename_step p t rows live) fuel st = inr (Some (s, c)) ->
    rename_result_info p rows live s c.
  Proof.
    induction fuel as [|fuel IH]; intros st s c Hinfo Hrun; [discriminate|].
    cbn [loop_fuel] in Hrun.
    destruct (rename_step p t rows live st) as [next|answer] eqn:Hstep.
    - eapply IH; [eapply rename_info_step; eassumption|exact Hrun].
    - inversion Hrun; subst answer. eapply rename_stop_info; eassumption.
  Qed.

  (** Every successful rename has the source block inventory and bounded environment rows. *)
  Lemma rename_inventory p t rows live s c : rename p t rows live = Some (s, c) ->
    rename_result_info p rows live s c.
  Proof.
    rewrite F4_rename_loop.
    destruct (loop_fuel (rename_step p t rows live)
      (2 * length (blocks _ _ _ p) + 1) (rename_init p)) as [next|answer] eqn:Hrun;
      [discriminate|].
    intro Hanswer; subst answer. eapply rename_loop_info; [apply rename_info_init|exact Hrun].
  Qed.

  (** Three source widths and two tag bits cover all generated value names. *)
  Definition rename_value_width (p : P.t) := 3 * function_width p + 2.

  (** A selected source block identifier fits the source width. *)
  Lemma source_lookup_width (p : P.t) b body : lookup b (blocks _ _ _ p) = Some body ->
    Pos.size_nat b <= function_width p.
  Proof.
    intro Hget; apply val_lookup_in in Hget; exact (val_block_width p b body Hget).
  Qed.

  (** The initial old variable and tagged input pairs fit the common value budget. *)
  Lemma input_names_bounded p :
    build_names_bounded (map (fun x => (x, build_input_name x)) (inputs _ _ _ p))
      (rename_value_width p).
  Proof.
    intros x y Hin; apply in_map_iff in Hin as [a [Heq Hin]]. inversion Heq; subst x y.
    pose proof (val_input_width p a Hin). pose proof (build_input_bits p a Hin).
    unfold rename_value_width; split; lia.
  Qed.

  (** Indexing the initial inputs preserves the common value budget. *)
  Lemma input_index_bounded p : build_range_width
    (val_index (map (fun x => (x, build_input_name x)) (inputs _ _ _ p)))
    (rename_value_width p).
  Proof.
    apply build_index_width, build_bounded_values, input_names_bounded.
  Qed.

  (** Code renaming preserves bounded values while its allocation counter fits the source budget. *)
  Lemma rename_code_width : forall cs rho names fresh out final final_names next width limit,
    build_range_width rho width ->
    N.to_nat fresh + length cs <= limit ->
    (forall i, N.to_nat i < limit -> Pos.size_nat (build_instruction_name i) <= width) ->
    rename_code cs rho names fresh = Some (out, final, final_names, next) ->
    build_range_width final width /\
      forall x, In x (flat_map (fun '(y, _, xs) => y :: xs) out) -> Pos.size_nat x <= width.
  Proof.
    induction cs as [|[[x op] xs] rest IH];
      intros rho names fresh out final final_names next width limit Hrho Hlimit Hfresh Hrun.
    - cbn [rename_code] in Hrun; inversion Hrun; subst.
      split; [exact Hrho|intros x Hin; contradiction].
    - cbn [rename_code] in Hrun.
      destruct (build_values rho xs) as [ys|] eqn:Hvalues; [|discriminate].
      destruct (rename_code rest (PTrieCode.set x (build_instruction_name fresh) rho)
        ((x, build_instruction_name fresh) :: names) (N.succ fresh))
        as [[[[tail rho'] names'] next']|] eqn:Htail; [|discriminate].
      inversion Hrun; subst out final final_names next.
      assert (Hnew : Pos.size_nat (build_instruction_name fresh) <= width)
        by (apply Hfresh; cbn [length] in Hlimit; lia).
      destruct (IH _ _ (N.succ fresh) _ _ _ _ width limit
        (build_set_width _ _ _ _ Hrho Hnew)
        ltac:(rewrite N2Nat.inj_succ; cbn [length] in Hlimit; lia) Hfresh Htail)
        as [Hfinal Htail_width].
      split; [exact Hfinal|]. intros value Hin; cbn [flat_map] in Hin.
      apply in_app_or in Hin as [[Heq|Hin]|Hin].
      + subst value; exact Hnew.
      + exact (build_values_width _ _ _ _ Hrho Hvalues value Hin).
      + exact (Htail_width value Hin).
  Qed.

  (** Every emitted exit variable is read from the bounded final environment. *)
  Lemma rename_exit_width : forall ending rows rho out width,
    build_range_width rho width -> rename_exit ending rows rho = Some out ->
    forall x, In x (exit_uses out) -> Pos.size_nat x <= width.
  Proof.
    intros ending rows rho out width Hrho Hrun x Hin.
    destruct ending as [b old|g xs b old c old'|xs].
    - destruct old as [|a rest]; [|discriminate]. cbn [rename_exit] in Hrun.
      destruct (build_values rho (index_row rows b)) as [args|] eqn:Hargs; [|discriminate].
      inversion Hrun; subst out. exact (build_values_width _ _ _ _ Hrho Hargs x Hin).
    - destruct old as [|a rest], old' as [|a' rest']; try discriminate.
      cbn [rename_exit] in Hrun.
      destruct (build_values rho xs) as [args|] eqn:Hargs; [|discriminate].
      destruct (build_values rho (index_row rows b)) as [yes_args|] eqn:Hyes; [|discriminate].
      destruct (build_values rho (index_row rows c)) as [no_args|] eqn:Hno; [|discriminate].
      inversion Hrun; subst out. cbn [exit_uses] in Hin.
      apply in_app_or in Hin as [Hin|Hin].
      + exact (build_values_width _ _ _ _ Hrho Hargs x Hin).
      + apply in_app_or in Hin as [Hin|Hin].
        * exact (build_values_width _ _ _ _ Hrho Hyes x Hin).
        * exact (build_values_width _ _ _ _ Hrho Hno x Hin).
    - cbn [rename_exit] in Hrun.
      destruct (build_values rho xs) as [args|] eqn:Hargs; [|discriminate].
      inversion Hrun; subst out. exact (build_values_width _ _ _ _ Hrho Hargs x Hin).
  Qed.

  (** A listed block's projected entry names fit the common value budget. *)
  Lemma projected_names_bounded p b body phis inherited names :
    lookup b (blocks _ _ _ p) = Some body ->
    build_names_bounded inherited (rename_value_width p) ->
    build_project b phis (index_row (val_index (L.live_in p)) b) (val_index inherited)
      (val_index (map (fun x => (x, build_input_name x)) (inputs _ _ _ p))) = Some names ->
    build_names_bounded names (rename_value_width p).
  Proof.
    intros Hsource Hinherited Hrun. eapply build_project_bounded; [| | | |exact Hrun].
    - intros x Hin; pose proof (live_row_width p b x Hin); unfold rename_value_width; lia.
    - intros x Hin. apply build_phi_bits; [exact (source_lookup_width p b body Hsource)|].
      exact (live_row_width p b x Hin).
    - apply build_index_width, build_bounded_values; exact Hinherited.
    - apply input_index_bounded.
  Qed.

  (** Projected child tasks for listed source blocks contain bounded renamings. *)
  Lemma rename_children_bounded p rows rho : forall kids tasks,
    build_range_width rho (rename_value_width p) ->
    rename_children kids rows (val_index (L.live_in p)) rho
      (val_index (map (fun x => (x, build_input_name x)) (inputs _ _ _ p))) = Some tasks ->
    forall b names body, In (b, names) tasks -> lookup b (blocks _ _ _ p) = Some body ->
      build_names_bounded names (rename_value_width p).
  Proof.
    induction kids as [|a rest IH]; intros tasks Hrho Hrun b names body Hin Hsource.
    - cbn [rename_children] in Hrun; inversion Hrun; subst; contradiction.
    - cbn [rename_children] in Hrun.
      destruct (build_project a (val_set (index_row rows a))
        (index_row (val_index (L.live_in p)) a) rho
        (val_index (map (fun x => (x, build_input_name x)) (inputs _ _ _ p))))
        as [entry_names|] eqn:Hentry; [|discriminate].
      destruct (rename_children rest rows (val_index (L.live_in p)) rho
        (val_index (map (fun x => (x, build_input_name x)) (inputs _ _ _ p))))
        as [tail|] eqn:Htail; [|discriminate].
      inversion Hrun; subst tasks. destruct Hin as [Heq|Hin].
      + inversion Heq; subst a entry_names.
        eapply build_project_bounded; [| |exact Hrho|apply input_index_bounded|exact Hentry].
        * intros x Hx; pose proof (live_row_width p b x Hx); unfold rename_value_width; lia.
        * intros x Hx; apply build_phi_bits; [exact (source_lookup_width p b body Hsource)|].
          exact (live_row_width p b x Hx).
      + exact (IH tail Hrho eq_refl b names body Hin Hsource).
  Qed.

  (** Emitted names are bounded, and pending names need the bound when their block is listed. *)
  Definition rename_width (p : P.t) (st : rename_state O.K O.G) : Prop :=
    (forall b body, In (b, body) (renamed_blocks _ _ st) ->
      forall x, In x (build_body_vars body) -> Pos.size_nat x <= rename_value_width p) /\
    (forall b names, In (b, names) (renamed_envs _ _ st) ->
      build_names_bounded names (rename_value_width p)) /\
    forall b names body, In (b, names) (rename_stack _ _ st) ->
      lookup b (blocks _ _ _ p) = Some body -> build_names_bounded names (rename_value_width p).

  (** Initial input and block tasks satisfy the common value width invariant. *)
  Lemma rename_width_init p : rename_width p (rename_init p).
  Proof.
    unfold rename_width, rename_init; cbn [renamed_blocks renamed_envs rename_stack].
    split; [intros b body Hin; contradiction|]. split; [intros b names Hin; contradiction|].
    intros b names body Hin Hsource. destruct Hin as [Heq|Hin].
    - inversion Heq; subst names; apply input_names_bounded.
    - apply in_map_iff in Hin as [[a original] [Heq Hin]]. inversion Heq; subst names.
      intros x y Hxy; contradiction.
  Qed.

  (** A continuing rename step preserves bounded emitted and pending names. *)
  Lemma rename_width_step p t st next :
    rename_info p (placement p) (L.live_in p) st -> rename_width p st ->
    rename_step p t (placement p) (L.live_in p) st = inl next -> rename_width p next.
  Proof.
    destruct st as [bodies tasks output envs fresh].
    destruct tasks as [|[b inherited] tasks]; [discriminate|].
    intros Hinfo [Hout [Henv Htasks]] Hstep.
    unfold rename_step in Hstep; cbn [rename_step_indexed] in Hstep.
    destruct (trie_get b bodies) as [body|] eqn:Hget.
    - pose proof (proj1 Hinfo) as Hcache.
      destruct Hcache as [Hunique [Hremaining Hcounter]].
      destruct (Hremaining b body Hget) as [Hsource Hunused].
      assert (Hinherited : build_names_bounded inherited (rename_value_width p)).
      { exact (Htasks b inherited body (or_introl eq_refl) Hsource). }
      destruct (params _ _ _ body) as [|x rest]; [|discriminate].
      destruct (if Pos.eqb b (entry _ _ _ p) then
        match index_row (placement p) b with [] => Some inherited | _ => None end
        else build_project b (val_set (index_row (placement p) b))
          (index_row (val_index (L.live_in p)) b) (val_index inherited)
          (val_index (map (fun x => (x, build_input_name x)) (inputs _ _ _ p))))
        as [names|] eqn:Hnames; [|discriminate].
      assert (Hnames_width : build_names_bounded names (rename_value_width p)).
      { destruct (Pos.eqb b (entry _ _ _ p));
          [destruct (index_row (placement p) b); [inversion Hnames; subst; exact Hinherited|
            discriminate]|].
        eapply projected_names_bounded; eassumption. }
      destruct (rename_code (code _ _ _ body) (val_index names) names fresh)
        as [[[[cs final] final_names] last]|] eqn:Hcode; [|discriminate].
      destruct (rename_exit (term _ _ _ body) (placement p) final) as [ending|] eqn:Hexit;
        [|discriminate].
      destruct (rename_children (children t b) (placement p) (val_index (L.live_in p)) final
        (val_index (map (fun x => (x, build_input_name x)) (inputs _ _ _ p))))
        as [kids|] eqn:Hkids; [|discriminate].
      assert (Hlimit : N.to_nat fresh + length (code _ _ _ body) <= function_size p).
      { pose proof (rename_cache_next p
          (RenameState O.K O.G bodies ((b, inherited) :: tasks) output envs fresh)
          b body (proj1 Hinfo) Hget) as Hnext_size.
        eapply Nat.le_trans; [exact Hnext_size|].
        apply build_function_code_size. }
      destruct (rename_code_width _ _ _ _ _ _ _ _ (rename_value_width p) (function_size p)
        (build_index_width _ _ (build_bounded_values _ _ Hnames_width)) Hlimit
        ltac:(intros i Hi; pose proof (build_instruction_bits p i Hi);
          unfold rename_value_width; lia) Hcode) as [Hfinal Hcode_width].
      pose proof (rename_exit_width _ _ _ _ _ Hfinal Hexit) as Hexit_width.
      inversion Hstep; subst next. unfold rename_width.
      cbn [renamed_blocks renamed_envs rename_stack]. split.
      + intros a out Hin value Hvalue; destruct Hin as [Heq|Hin].
        * inversion Heq; subst a out. unfold build_body_vars in Hvalue.
          cbn [params code term] in Hvalue.
          apply in_app_or in Hvalue as [Hvalue|Hvalue].
          -- apply in_map_iff in Hvalue as [x [Hname Hx]]; subst value.
             apply build_phi_bits; [exact (source_lookup_width p b body Hsource)|].
             exact (placement_row_width p b x Hx).
          -- apply in_app_or in Hvalue as [Hvalue|Hvalue]; [apply Hcode_width|apply Hexit_width];
               exact Hvalue.
        * exact (Hout a out Hin value Hvalue).
      + split.
        * intros a row Hin; destruct Hin as [Heq|Hin].
          -- inversion Heq; subst; exact Hnames_width.
          -- exact (Henv a row Hin).
        * intros a row original Hin Hlookup; apply in_app_or in Hin as [Hin|Hin].
          -- exact (rename_children_bounded p (placement p) final _ _ Hfinal Hkids
               a row original Hin Hlookup).
          -- apply (Htasks a row original); [right; exact Hin|exact Hlookup].
    - inversion Hstep; subst next. split; [exact Hout|]. split; [exact Henv|].
      intros a names body Hin Hsource.
      apply (Htasks a names body); [right; exact Hin|exact Hsource].
  Qed.

  (** Returned block variables and certificate pairs satisfy the common value width bound. *)
  Definition rename_result_values (p s : P.t) (c : cert) : Prop :=
    (forall b body, In (b, body) (blocks _ _ _ s) ->
      forall x, In x (build_body_vars body) -> Pos.size_nat x <= rename_value_width p) /\
    forall b names, In (b, names) (fst c) -> build_names_bounded names (rename_value_width p).

  (** Materialization preserves the maintained variable and certificate width bounds. *)
  Lemma rename_stop_values p t st s c : rename_width p st ->
    rename_step p t (placement p) (L.live_in p) st = inr (Some (s, c)) ->
    rename_result_values p s c.
  Proof.
    destruct st as [bodies tasks output envs fresh]; intros [Hout [Henv Htasks]] Hstop.
    unfold rename_step in Hstop; destruct tasks as [|[b inherited] tasks].
    - cbn [rename_step_indexed] in Hstop.
      destruct (build_materialize (blocks _ _ _ p) (val_index output)) as [bs|] eqn:Hbs;
        [|discriminate].
      inversion Hstop; subst s c. split; [|exact Henv].
      intros b body Hin x Hx. destruct (build_materialize_member _ _ _ _ _ Hbs Hin) as [_ Hget].
      rewrite val_index_lookup in Hget; apply val_lookup_in in Hget. exact (Hout b body Hget x Hx).
    - cbn [rename_step_indexed] in Hstop.
      destruct (trie_get b bodies) as [body|]; [|discriminate].
      destruct (params _ _ _ body) as [|x rest]; [|discriminate].
      destruct (if Pos.eqb b (entry _ _ _ p) then
        match index_row (placement p) b with [] => Some inherited | _ => None end
        else build_project b (val_set (index_row (placement p) b))
          (index_row (val_index (L.live_in p)) b) (val_index inherited)
          (val_index (map (fun x => (x, build_input_name x)) (inputs _ _ _ p)))) as [names|];
        [|discriminate].
      destruct (rename_code (code _ _ _ body) (val_index names) names fresh)
        as [[[[cs final] final_names] last]|]; [|discriminate].
      destruct (rename_exit (term _ _ _ body) (placement p) final); [|discriminate].
      destruct (rename_children (children t b) (placement p) (val_index (L.live_in p)) final
        (val_index (map (fun x => (x, build_input_name x)) (inputs _ _ _ p)))); discriminate.
  Qed.

  (** Every successful bounded loop result preserves the value width invariant. *)
  Lemma rename_loop_values p t : forall fuel st s c,
    rename_info p (placement p) (L.live_in p) st -> rename_width p st ->
    loop_fuel (rename_step p t (placement p) (L.live_in p)) fuel st = inr (Some (s, c)) ->
    rename_result_values p s c.
  Proof.
    induction fuel as [|fuel IH]; intros st s c Hinfo Hwidth Hrun; [discriminate|].
    cbn [loop_fuel] in Hrun.
    destruct (rename_step p t (placement p) (L.live_in p) st) as [next|answer] eqn:Hstep.
    - eapply IH; [eapply rename_info_step; eassumption|
        eapply rename_width_step; eassumption|exact Hrun].
    - inversion Hrun; subst answer. eapply rename_stop_values; eassumption.
  Qed.

  (** Every successful producer renaming contains only bounded variables and certificate pairs. *)
  Lemma rename_values p t s c : rename p t (placement p) (L.live_in p) = Some (s, c) ->
    rename_result_values p s c.
  Proof.
    rewrite F4_rename_loop.
    destruct (loop_fuel (rename_step p t (placement p) (L.live_in p))
      (2 * length (blocks _ _ _ p) + 1) (rename_init p)) as [next|answer] eqn:Hrun;
      [discriminate|].
    intro Hanswer; subst answer. eapply rename_loop_values;
      [apply rename_info_init|apply rename_width_init|exact Hrun].
  Qed.

  (** Restoring source block order preserves the total unchanged payload size. *)
  Lemma rename_core_size p t rows live s c : NoDup (map fst (blocks _ _ _ p)) ->
    rename p t rows live = Some (s, c) ->
    build_sum (fun item => build_core_size (snd item)) (blocks _ _ _ s) =
      build_sum (fun item => build_core_size (snd item)) (blocks _ _ _ p).
  Proof.
    intros Hunique Hrun. destruct (rename_inventory _ _ _ _ _ _ Hrun)
      as [_ [_ [_ [Hkeys [Hbodies _]]]]].
    eapply build_corresponding_sum; [exact Hunique|exact Hkeys|].
    intros b body Hin. destruct (Hbodies b body Hin) as [original [Hsource [_ [Hcore _]]]].
    exists original; auto.
  Qed.

  (** Successful renaming preserves the complete instruction and guard bit total. *)
  Lemma rename_operation_bits p t rows live s c : NoDup (map fst (blocks _ _ _ p)) ->
    rename p t rows live = Some (s, c) -> Va.op_bits s = Va.op_bits p.
  Proof.
    intros Hunique Hrun. destruct (rename_inventory _ _ _ _ _ _ Hrun)
      as [_ [_ [_ [Hkeys [Hbodies _]]]]].
    change (build_sum (fun item => block_op_bits (snd item)) (blocks _ _ _ s) =
      build_sum (fun item => block_op_bits (snd item)) (blocks _ _ _ p)).
    eapply build_corresponding_sum; [exact Hunique|exact Hkeys|].
    intros b body Hin. destruct (Hbodies b body Hin)
      as [original [Hsource [_ [_ [_ [_ Hops]]]]]]. exists original; auto.
  Qed.

  (** The candidate's parameters are exactly the source blocks' placement-row inventory. *)
  Lemma rename_parameter_size p t rows live s c : rename p t rows live = Some (s, c) ->
    build_sum (fun item => length (params _ _ _ (snd item))) (blocks _ _ _ s) =
      build_sum (fun b => length (index_row rows b)) (map fst (blocks _ _ _ p)).
  Proof.
    intro Hrun. destruct (rename_inventory _ _ _ _ _ _ Hrun)
      as [_ [_ [_ [Hkeys [Hbodies _]]]]].
    rewrite <- Hkeys, build_sum_map. apply build_sum_ext; intros [b body] Hin; cbn [fst snd].
    destruct (Hbodies b body Hin) as [original [_ [Hparams _]]]; exact Hparams.
  Qed.

  (** At most two outgoing rows per source block bound emitted argument occurrences. *)
  Lemma rename_edge_arg_size p t rows live s c bound :
    rename p t rows live = Some (s, c) ->
    (forall b, length (index_row rows b) <= bound) ->
    function_edge_args s <= 2 * length (blocks _ _ _ p) * bound.
  Proof.
    intros Hrun Hrows. destruct (rename_inventory _ _ _ _ _ _ Hrun)
      as [_ [_ [_ [Hkeys [Hbodies _]]]]].
    assert (Hcount : length (blocks _ _ _ s) = length (blocks _ _ _ p)).
    { apply f_equal with (f := @length positive) in Hkeys. now rewrite !length_map in Hkeys. }
    unfold function_edge_args. change (build_sum
      (fun item => exit_arg_count (term _ _ _ (snd item))) (blocks _ _ _ s) <=
      2 * length (blocks _ _ _ p) * bound).
    eapply Nat.le_trans; [apply build_sum_bound with (amount := 2 * bound)|].
    - intros [b body] Hin; cbn [fst snd]. destruct (Hbodies b body Hin)
        as [original [_ [_ [_ [_ [Hargs _]]]]]]. rewrite Hargs.
      eapply Nat.le_trans; [apply build_sum_bound; intros a Ha; apply Hrows|].
      pose proof (build_exit_target_count (term _ _ _ original)); nia.
    - rewrite Hcount; lia.
  Qed.

  (** Candidate syntax charges source payloads, placement rows and emitted arguments. *)
  Lemma rename_syntax_size p t s c : NoDup (map fst (blocks _ _ _ p)) ->
    rename p t (placement p) (L.live_in p) = Some (s, c) ->
    function_size s <= function_size p + placement_work p + function_edge_args s.
  Proof.
    intros Hunique Hrun.
    pose proof (rename_core_size _ _ _ _ _ _ Hunique Hrun) as Hcore.
    pose proof (rename_parameter_size _ _ _ _ _ _ Hrun) as Hparams.
    pose proof (placement_source_size p Hunique) as Hplacements.
    destruct (rename_inventory _ _ _ _ _ _ Hrun) as [_ [Hinputs [_ [Hkeys _]]]].
    apply f_equal with (f := @length positive) in Hinputs.
    apply f_equal with (f := @length positive) in Hkeys.
    rewrite !length_map in Hinputs. rewrite !length_map in Hkeys.
    rewrite build_function_decompose. rewrite Hinputs, Hkeys, Hcore, Hparams.
    pose proof (build_function_decompose p) as Hsource.
    unfold build_sum in Hplacements, Hsource |- *.
    lia.
  Qed.

  (** Candidate size is polynomial in source size and the distinct variable universe. *)
  Lemma rename_syntax_quadratic p t s c : NoDup (map fst (blocks _ _ _ p)) ->
    rename p t (placement p) (L.live_in p) = Some (s, c) ->
    function_size s <= function_size p +
      3 * function_size p * length (U.universe (R.prepare p)).
  Proof.
    intros Hunique Hrun.
    assert (Hrows : forall b, length (index_row (placement p) b) <=
        length (U.universe (R.prepare p))).
    { intro b; unfold placement; apply placement_row_length. }
    pose proof (rename_edge_arg_size _ _ _ _ _ _ _ Hrun Hrows) as Hargs.
    pose proof (rename_core_size _ _ _ _ _ _ Hunique Hrun) as Hcore.
    pose proof (rename_parameter_size _ _ _ _ _ _ Hrun) as Hparams.
    pose proof (build_sum_bound (fun b => length (index_row (placement p) b))
      (map fst (blocks _ _ _ p)) (length (U.universe (R.prepare p)))
      ltac:(intros b Hb; apply Hrows)) as Hplacements.
    rewrite length_map in Hplacements.
    destruct (rename_inventory _ _ _ _ _ _ Hrun) as [_ [Hinputs [_ [Hkeys _]]]].
    apply f_equal with (f := @length positive) in Hinputs.
    apply f_equal with (f := @length positive) in Hkeys.
    rewrite !length_map in Hinputs. rewrite !length_map in Hkeys.
    pose proof (build_function_decompose p) as Hsource.
    rewrite build_function_decompose, Hinputs, Hkeys, Hcore, Hparams.
    assert (Hblocks : length (blocks _ _ _ p) <= function_size p) by
      (unfold function_size; lia).
    nia.
  Qed.

  (** Certificate environments charge each input or selected live row at most once. *)
  Lemma rename_environment_size p t rows live s c : rename p t rows live = Some (s, c) ->
    cert_size c <= length (blocks _ _ _ p) + 2 * length (inputs _ _ _ p) +
      3 * build_live_rows_size live.
  Proof.
    intro Hrun. destruct (rename_inventory _ _ _ _ _ _ Hrun)
      as [_ [_ [Hlive [_ [_ [Hunique [Hkeys Hnames]]]]]]].
    assert (Hcount : length (fst c) <= length (blocks _ _ _ p)).
    { pose proof (NoDup_incl_length Hunique Hkeys) as Hlength.
      now rewrite !length_map in Hlength. }
    assert (Hsum : build_sum (fun row => length (snd row)) (fst c) <=
      build_sum (fun b => if Pos.eqb b (entry _ _ _ p) then length (inputs _ _ _ p) else 0)
        (map fst (fst c)) +
      build_sum (fun b => length (index_row (val_index live) b)) (map fst (fst c))).
    { rewrite <- build_sum_add, build_sum_map. apply val_sum_mono.
      intros [b names] Hin; exact (Hnames b names Hin). }
    pose proof (val_sum_single (map fst (fst c)) (entry _ _ _ p)
      (length (inputs _ _ _ p)) Hunique) as Hinput.
    pose proof (val_lookup_sum live (map fst (fst c)) (@length positive) Hunique) as Hrows.
    assert (Hlookup : build_sum (fun b => length (index_row (val_index live) b))
        (map fst (fst c)) = build_sum
        (fun b => match lookup b live with Some row => length row | None => 0 end)
        (map fst (fst c))).
    { apply build_sum_ext; intros b Hb; unfold index_row; rewrite val_index_lookup.
      destruct (lookup b live); reflexivity. }
    rewrite Hlookup in Hsum.
    assert (Hmass : build_sum (fun row => length (snd row)) live <= build_live_rows_size live).
    { unfold build_sum, build_live_rows_size; apply val_sum_mono; intros row Hin; lia. }
    rewrite build_cert_decompose, Hlive. unfold build_sum in Hsum, Hmass |- *; lia.
  Qed.

  (** The published liveness budget bounds the complete certificate size. *)
  Lemma rename_certificate_size p t s c :
    rename p t (placement p) (L.live_in p) = Some (s, c) ->
    cert_size c <= 4 * function_size p + 3 * L.live_size p.
  Proof.
    intro Hrun. pose proof (rename_environment_size _ _ _ _ _ _ Hrun) as Hcert.
    pose proof (L.live_in_size p) as Hlive.
    change (build_live_rows_size (L.live_in p) <= length (blocks _ _ _ p) + L.live_size p)
      in Hlive.
    pose proof (build_function_decompose p); lia.
  Qed.

  (** A successful producer has passed the distinct source-block guard. *)
  Lemma produce_unique p s c : produce p = Some (s, c) -> NoDup (map fst (blocks _ _ _ p)).
  Proof.
    unfold produce. destruct (build_blocks_unique (blocks _ _ _ p) Empty) eqn:Hunique;
      [|discriminate].
    intro Hrun. rewrite build_blocks_unique_map in Hunique.
    exact (proj1 (val_unique_sound _ _ Hunique)).
  Qed.

  (** The producer preserves source operator and guard bit totals exactly. *)
  Lemma produce_operation_bits p s c : produce p = Some (s, c) -> Va.op_bits s = Va.op_bits p.
  Proof.
    intro Hrun. pose proof (produce_unique _ _ _ Hrun) as Hunique.
    apply F5_produce_checked in Hrun as [_ Hrename].
    eapply rename_operation_bits; eassumption.
  Qed.

  (** All returned function and certificate identifiers fit the common value budget. *)
  Lemma rename_identifier_width p t s c :
    rename p t (placement p) (L.live_in p) = Some (s, c) ->
    vertex_width (function_ids s) <= rename_value_width p /\
      vertex_width (cert_ids c) <= rename_value_width p.
  Proof.
    intro Hrun. pose proof (rename_values _ _ _ _ Hrun) as [Hvalues Henvvalues].
    destruct (rename_inventory _ _ _ _ _ _ Hrun)
      as [Hentry [Hinputs [Hlive [Hkeys [Hbodies [Hunique [Henvkeys Hnames]]]]]]].
    assert (Hlisted : forall b, In b (map fst (blocks _ _ _ p)) ->
        Pos.size_nat b <= rename_value_width p).
    { intros b Hin; apply in_map_iff in Hin as [[a body] [Heq Hin]].
      cbn [fst] in Heq; subst a. pose proof (val_block_width p b body Hin).
      unfold rename_value_width; lia. }
    assert (Hvariables : forall x, In x (function_vars s) ->
        Pos.size_nat x <= rename_value_width p).
    { intros x Hin; unfold function_vars in Hin; apply in_app_or in Hin as [Hin|Hin].
      - rewrite Hinputs in Hin; apply in_map_iff in Hin as [y [Heq Hin]]; subst x.
        pose proof (build_input_bits p y Hin); unfold rename_value_width; lia.
      - apply in_flat_map in Hin as [[b body] [Hin Hx]]. exact (Hvalues b body Hin x Hx). }
    split; apply val_cfg_vertex_width_le.
    - intros x Hin; unfold function_ids in Hin. destruct Hin as [Heq|Hin].
      + subst x; rewrite Hentry. pose proof (val_entry_width p); unfold rename_value_width; lia.
      + apply in_app_or in Hin as [Hin|Hin]; [apply Hvariables; exact Hin|].
        apply in_flat_map in Hin as [[b body] [Hbody Hin]]. cbn [fst snd] in Hin.
        destruct Hin as [Heq|Hin].
        * subst x; apply Hlisted; rewrite <- Hkeys.
          apply in_map with (f := fst) in Hbody; exact Hbody.
        * destruct (Hbodies b body Hbody) as [original [Hsource [_ [_ [Htargets _]]]]].
          rewrite Htargets in Hin. apply val_lookup_in in Hsource.
          pose proof (val_target_width p b original x Hsource Hin); unfold rename_value_width; lia.
    - intros x Hin; unfold cert_ids in Hin; apply in_app_or in Hin as [Hin|Hin].
      + apply in_flat_map in Hin as [[b names] [Hrow Hin]]. cbn [fst snd] in Hin.
        destruct Hin as [Heq|Hin].
        * subst x; apply Hlisted, Henvkeys. apply in_map with (f := fst) in Hrow; exact Hrow.
        * apply in_flat_map in Hin as [[a y] [Hpair Hin]]. cbn [fst snd In] in Hin.
          destruct (Henvvalues b names Hrow a y Hpair) as [Ha Hy].
          destruct Hin as [Heq|[Heq|Hin]]; [now subst x|now subst x|contradiction].
      + rewrite Hlive in Hin. apply in_flat_map in Hin as [[b row] [Hrow Hin]].
        destruct (L.live_in_ids p (b, row) Hrow) as [Hblock Hvars]. cbn [fst snd] in Hin.
        destruct Hin as [Heq|Hin].
        * subst x. pose proof (PB.block_bits_le p b (or_introl Hblock)) as Hwidth.
          change (Pos.size_nat b <= function_width p) in Hwidth. unfold rename_value_width; lia.
        * pose proof (universe_width p x (Hvars x Hin)); unfold rename_value_width; lia.
  Qed.

  (** The candidate's identifiers and size field fit a fixed multiple of source width. *)
  Lemma rename_result_width p t s c : NoDup (map fst (blocks _ _ _ p)) ->
    rename p t (placement p) (L.live_in p) = Some (s, c) ->
    function_width s + vertex_width (cert_ids c) <= 16 * (function_width p + 1).
  Proof.
    intros Hunique Hrun.
    destruct (rename_identifier_width _ _ _ _ Hrun) as [Hids Hcert].
    pose proof (rename_syntax_quadratic _ _ _ _ Hunique Hrun) as Hsize.
    pose proof (universe_count p) as Huniverse.
    pose proof (build_function_size_value p) as Hsource.
    assert (Hvalue : function_size s + 1 < 2 ^ (2 * function_width p + 3)).
    { replace (2 * function_width p + 3) with
        (function_width p + function_width p + 3) by lia.
      rewrite !Nat.pow_add_r. cbn [Nat.pow]. nia. }
    assert (Hsize_bits : Pos.size_nat (Pos.of_succ_nat (function_size s)) <=
        2 * function_width p + 3).
    { apply Pos.size_nat_least. rewrite SuccNat2Pos.id_succ; lia. }
    unfold function_width at 1. rewrite val_cfg_graph_max.
    assert (Hwidth : Nat.max (vertex_width (function_ids s))
        (Pos.size_nat (Pos.of_succ_nat (function_size s))) <= 3 * function_width p + 3).
    { apply Nat.max_lub; unfold rename_value_width in Hids; lia. }
    unfold rename_value_width in Hcert; lia.
  Qed.

  (** Every successful producer satisfies the inventory, size and width contract with constant
      16. *)
  Lemma produce_size_checked p s c : produce p = Some (s, c) ->
    map fst (blocks _ _ _ s) = map fst (blocks _ _ _ p) /\
    (N.of_nat (function_size s + cert_size c) <= 16 * N.of_nat (build_work p))%N /\
    (N.of_nat (function_width s + vertex_width (cert_ids c)) <=
      16 * N.of_nat (function_width p + 1))%N.
  Proof.
    intro Hproduce. pose proof (produce_unique _ _ _ Hproduce) as Hunique.
    pose proof (F5_produce_checked _ _ _ Hproduce) as [_ Hrename].
    pose proof (rename_inventory _ _ _ _ _ _ Hrename) as [_ [_ [_ [Hkeys _]]]].
    split; [exact Hkeys|]. split.
    - pose proof (rename_syntax_size _ _ _ _ Hunique Hrename) as Hsyntax.
      pose proof (rename_certificate_size _ _ _ _ Hrename) as Hcert.
      assert (Hnat : function_size s + cert_size c <= 16 * build_work p).
      { unfold build_work, phi_args; rewrite Hproduce; lia. }
      change (N.of_nat (function_size s + cert_size c) <=
        N.of_nat 16 * N.of_nat (build_work p))%N.
      rewrite <- Nat2N.inj_mul. now apply time_of_nat_le.
    - change (N.of_nat (function_width s + vertex_width (cert_ids c)) <=
        N.of_nat 16 * N.of_nat (function_width p + 1))%N.
      rewrite <- Nat2N.inj_mul. apply time_of_nat_le.
      eapply rename_result_width; eassumption.
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
  Proof.
    intros p s c Hproduce. unfold k_size. now apply produce_size_checked.
  Qed.
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
  Proof.
    intro p. unfold k_wrap. time_unfold T_build.
    destruct (produce p) as [[s c]|]; time_simpl; time_cbn.
    - destruct (andb (Va.check p s c) (Va.check_ssa s)); lia.
    - lia.
  Qed.
End BuildT.
