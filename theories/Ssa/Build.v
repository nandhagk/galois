(** * Checked SSA construction

    This module supplies a checked construction interface.
    Every candidate passes both translation and SSA validation before it is returned.
    Builds on: BuildSig. *)

From Stdlib Require Import List Arith PArith NArith Bool Lia.
From Argent Require Import Time Tactics Std BigO Loop.
From Galois.Base Require Import Code KeySig Key Trie.
From Galois.Graph Require Import Data Spec DigraphSig DomSig FrontierSig.
From Galois.Program Require Import CfgSig VarsSig SsaSig.
From Galois.Ssa Require Import Lang LiveSig Live ValidateSig Validate BuildSig.
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



(** A path starting at a listed vertex stays within a well-formed graph. *)
Lemma build_path_listed g start vertices finish : wf_graph g ->
  Spec.path g start vertices finish -> In start (verts g) -> In finish (verts g).
Proof.
  intros Hwf Hpath; induction Hpath as [v|u v vs target Hedge Hpath IH]; intro Hstart.
  - exact Hstart.
  - apply IH. exact (proj2 Hwf u v Hstart Hedge).
Qed.

(** Reachability from listed roots stays within a well-formed graph. *)
Lemma build_reach_listed g roots v : wf_graph g -> incl roots (verts g) ->
  reach g roots v -> In v (verts g).
Proof.
  intros Hwf Hroots [root [vertices [Hroot Hpath]]].
  eapply build_path_listed; [exact Hwf|exact Hpath|now apply Hroots].
Qed.

(** Distinct parent rows cannot contain the same child of a functional parent map. *)
Lemma build_child_rows_unique (rows : positive -> list positive) parents ids :
  NoDup ids -> (forall b, NoDup (rows b)) ->
  (forall b child, In child (rows b) -> trie_get child parents = Some b) ->
  NoDup (flat_map rows ids).
Proof.
  intros Hids Hrows Hparent; induction Hids as [|b rest Hfresh Hids IH]; [constructor|].
  cbn [flat_map]. apply NoDup_app; [apply Hrows|exact IH|].
  intros child Hhead Htail; apply in_flat_map in Htail as [other [Hother Hchild]].
  pose proof (Hparent b child Hhead) as Hleft.
  pose proof (Hparent other child Hchild) as Hright.
  assert (b = other) by congruence. subst other; contradiction.
Qed.

(** Every successful rewritten operand came from the supplied environment domain. *)
Lemma build_values_domain xs rho ys domain :
  (forall x y, trie_get x rho = Some y -> In x domain) ->
  build_values rho xs = Some ys -> incl xs domain.
Proof.
  revert ys; induction xs as [|x rest IH]; intros ys Hdomain Hrun value Hin;
    [contradiction|].
  cbn [build_values] in Hrun.
  destruct (trie_get x rho) as [y|] eqn:Hget; [|discriminate].
  destruct (build_values rho rest) as [tail|] eqn:Htail; [|discriminate].
  destruct Hin as [Heq|Hin]; [subst value; now apply (Hdomain x y)|].
  exact (IH tail Hdomain eq_refl value Hin).
Qed.

(** An index contains only keys present in its source list. *)
Lemma build_index_domain {A} (rows : list (positive * A)) x value :
  trie_get x (val_index rows) = Some value -> In x (map fst rows).
Proof.
  rewrite val_index_lookup; intro Hget; apply val_lookup_in in Hget.
  apply in_map with (f := fst) in Hget; exact Hget.
Qed.

(** Rewriting operands scans their keys once at the common identifier width. *)
Lemma build_values_time : forall xs rho w,
  (forall x, In x xs -> Pos.size_nat x <= w) ->
  (T_build_values rho xs <= 8 * N.of_nat (length xs + 1) * N.of_nat (w + 1))%N.
Proof.
  induction xs as [|x rest IH]; intros rho w Hwidth.
  - time_step.
  - assert (Hx : Pos.size_nat x <= w) by (apply Hwidth; now left).
    specialize (IH rho w ltac:(intros y Hin; apply Hwidth; now right)).
    time_unfold T_build_values; rewrite PTrieT.trie_get_clock.
    destruct (trie_get x rho), (build_values rho rest); time_cbn; nia.
Qed.

(** A tagged input is formed in constant time. *)
Lemma build_input_time x : (T_build_input_name x <= 2)%N.
Proof.
  time_step.
Qed.

(** A phi name traverses only its block identifier. *)
Lemma build_phi_time b x w : Pos.size_nat b <= w ->
  (T_build_phi_name b x <= (c_glue + 2) * N.of_nat (w + 1))%N.
Proof.
  intro Hwidth; pose proof (T_glue_le b x) as Hglue.
  time_unfold T_build_phi_name; time_cbn; nia.
Qed.

(** Projection scans each requested live key and creates at most one phi name. *)
Lemma build_project_time : forall xs b phis rho inputs w,
  Pos.size_nat b <= w -> (forall x, In x xs -> Pos.size_nat x <= w) ->
  (T_build_project b phis xs rho inputs <=
    16 * (c_glue + 1) * N.of_nat (length xs + 1) * N.of_nat (w + 1))%N.
Proof.
  induction xs as [|x rest IH]; intros b phis rho inputs w Hb Hwidth.
  - time_step.
  - assert (Hx : Pos.size_nat x <= w) by (apply Hwidth; now left).
    specialize (IH b phis rho inputs w Hb
      ltac:(intros y Hin; apply Hwidth; now right)).
    pose proof (val_mem_time phis x w Hx) as Hmem.
    pose proof (build_phi_time b x w Hb) as Hphi.
    time_unfold T_build_project; rewrite !PTrieT.trie_get_clock.
    destruct (val_mem phis x), (trie_get x rho), (trie_get x inputs),
      (build_project b phis rest rho inputs); time_cbn; nia.
Qed.

(** Materialization scans each requested source block identifier once. *)
Lemma build_materialize_time {K G} : forall
    (original : list (positive * block positive K G)) bodies w,
  (forall b body, In (b, body) original -> Pos.size_nat b <= w) ->
  (T_build_materialize original bodies <=
    8 * N.of_nat (length original + 1) * N.of_nat (w + 1))%N.
Proof.
  induction original as [|[b body] rest IH]; intros bodies w Hwidth.
  - time_step.
  - assert (Hb : Pos.size_nat b <= w) by (apply (Hwidth b body); now left).
    specialize (IH bodies w ltac:(intros key value Hin; apply (Hwidth key value); now right)).
    time_unfold @T_build_materialize; rewrite PTrieT.trie_get_clock.
    destruct (trie_get b bodies), (build_materialize rest bodies); time_cbn; nia.
Qed.

(** The remaining cache budget sums only bodies that can still be emitted. *)
Definition build_remaining {A} (weight : positive -> nat) ids (bodies : ptrie A) : nat :=
  build_sum (fun b => match trie_get b bodies with Some _ => weight b | None => 0 end) ids.

(** Removing a key outside the inventory leaves the remaining budget unchanged. *)
Lemma build_remaining_remove_absent {A} weight ids (bodies : ptrie A) b :
  ~ In b ids -> build_remaining weight ids (PTrieCode.remove b bodies) =
    build_remaining weight ids bodies.
Proof.
  intro Habsent; unfold build_remaining; apply build_sum_ext; intros a Hin.
  rewrite PTrie.get_remove_other; [reflexivity|].
  intro Heq; subst a; contradiction.
Qed.

(** Removing a present distinct inventory key spends exactly its cached body budget. *)
Lemma build_remaining_remove {A} weight ids (bodies : ptrie A) b body :
  NoDup ids -> In b ids -> trie_get b bodies = Some body ->
  build_remaining weight ids bodies =
    weight b + build_remaining weight ids (PTrieCode.remove b bodies).
Proof.
  intros Hunique; induction Hunique as [|a rest Hfresh Hunique IH]; intros Hin Hget;
    [contradiction|].
  destruct Hin as [Heq|Hin].
  - subst a. unfold build_remaining at 1 2; cbn [build_sum fold_right].
    rewrite Hget, PTrie.get_remove_same.
    change (weight b + build_remaining weight rest bodies =
      weight b + (0 + build_remaining weight rest (PTrieCode.remove b bodies))).
    rewrite build_remaining_remove_absent by exact Hfresh; lia.
  - unfold build_remaining at 1 2; cbn [build_sum fold_right].
    assert (Hneq : a <> b) by (intro Heq; subst a; contradiction).
    rewrite PTrie.get_remove_other by exact Hneq.
    change ((match trie_get a bodies with Some _ => weight a | None => 0 end) +
      build_remaining weight rest bodies = weight b +
      ((match trie_get a bodies with Some _ => weight a | None => 0 end) +
        build_remaining weight rest (PTrieCode.remove b bodies))).
    rewrite (IH Hin Hget). destruct (trie_get a bodies); lia.
Qed.

(** Cached bodies never carry more work than the complete source inventory. *)
Lemma build_remaining_bound {A} weight ids (bodies : ptrie A) :
  build_remaining weight ids bodies <= build_sum weight ids.
Proof.
  unfold build_remaining, build_sum; apply val_sum_mono; intros b Hin.
  destruct (trie_get b bodies); lia.
Qed.

(** A budget sum distributes over concatenated inventories. *)
Lemma build_sum_app {A} (weight : A -> nat) left right :
  build_sum weight (left ++ right) = build_sum weight left + build_sum weight right.
Proof.
  unfold build_sum; induction left as [|x rest IH]; cbn [fold_right app]; lia.
Qed.

(** Summing child rows is the same as summing their flattened inventory. *)
Lemma build_sum_flat_map {A B} (rows : A -> list B) weight ids :
  build_sum (fun b => build_sum weight (rows b)) ids =
    build_sum weight (flat_map rows ids).
Proof.
  induction ids as [|b rest IH]; [reflexivity|].
  change (build_sum weight (rows b) + build_sum (fun b => build_sum weight (rows b)) rest =
    build_sum weight (rows b ++ flat_map rows rest)).
  now rewrite build_sum_app, IH.
Qed.

(** A maintained potential pays continuation steps and reserves one terminal scan. *)
Lemma build_loop_budget {State Result} (step : State -> State + Result) Tstep
    (invariant : State -> Prop) (credit : State -> nat) k reserve :
  (forall st next, invariant st -> step st = inl next -> invariant next /\
    (Tstep st + k * N.of_nat (credit next) <= k * N.of_nat (credit st) + k)%N) ->
  (forall st answer, invariant st -> step st = inr answer ->
    (Tstep st <= k * N.of_nat (credit st + reserve + 1))%N) ->
  forall fuel st, invariant st ->
    (T_loop_fuel step Tstep fuel st <=
      (k + 1) * N.of_nat fuel + k * N.of_nat (credit st + reserve) + 1)%N.
Proof.
  intros Hcontinue Hfinish fuel; induction fuel as [|fuel IH]; intros st Hinv.
  - time_unfold @T_loop_fuel; nia.
  - time_unfold @T_loop_fuel; destruct (step st) as [next|answer] eqn:Hstep.
    + destruct (Hcontinue st next Hinv Hstep) as [Hnext Hcost].
      specialize (IH next Hnext). rewrite !Nat2N.inj_add, !Nat2N.inj_succ in *; nia.
    + pose proof (Hfinish st answer Hinv Hstep) as Hcost.
      rewrite !Nat2N.inj_add, !Nat2N.inj_succ in *; nia.
Qed.

(** Allocating an instruction name traverses at most the current counter width. *)
Lemma build_instruction_time fresh w : N.size_nat fresh <= w ->
  (T_build_instruction_name fresh <= 4 * N.of_nat (w + 1))%N.
Proof.
  intro Hwidth; pose proof (N.T_succ_pos_le fresh) as Hsucc.
  time_unfold T_build_instruction_name; time_cbn; nia.
Qed.

(** Reading a tree's child row traverses the queried block identifier. *)
Lemma build_children_time t b w : Pos.size_nat b <= w ->
  (T_children t b <= 4 * N.of_nat (w + 1))%N.
Proof.
  destruct t as [parents rows before after]; intro Hwidth.
  time_unfold T_children; rewrite PTrieT.trie_get_clock.
  destruct (trie_get b rows); time_cbn; nia.
Qed.

(** Forming input bindings takes constant time per original input. *)
Lemma build_input_pairs_time xs :
  (ListDef.T_map (fun x => (x, build_input_name x))
    (fun x => 1 + T_build_input_name x)%N xs <= 4 * N.of_nat (length xs) + 1)%N.
Proof.
  apply (ListDef.T_map_le _ _ 3%N xs).
  intro x; pose proof (build_input_time x); lia.
Qed.

(** Forming the returned input list takes constant time per original input. *)
Lemma build_input_list_time xs :
  (ListDef.T_map build_input_name T_build_input_name xs <=
    3 * N.of_nat (length xs) + 1)%N.
Proof.
  apply (ListDef.T_map_le _ _ 2%N xs); apply build_input_time.
Qed.

(** A parameter row is mapped to tagged phi names at its block's width. *)
Lemma build_phi_list_time b xs w : Pos.size_nat b <= w ->
  (ListDef.T_map (build_phi_name b) (T_build_phi_name b) xs <=
    (c_glue + 4) * N.of_nat (length xs + 1) * N.of_nat (w + 1))%N.
Proof.
  intro Hb.
  pose proof (ListDef.T_map_le (build_phi_name b) (T_build_phi_name b)
    ((c_glue + 2) * N.of_nat (w + 1))%N xs
    ltac:(intro x; apply build_phi_time; exact Hb)) as Hmap.
  rewrite !Nat2N.inj_add; nia.
Qed.

(** A counted component can be charged to a larger positive common budget. *)
Lemma build_component_budget time coefficient extra count total width common scale :
  (time <= coefficient * N.of_nat count * width + extra)%N ->
  count <= total -> 1 <= total -> (1 <= width)%N ->
  (coefficient + extra <= scale * common)%N ->
  (time <= scale * (common * (N.of_nat total * width)))%N.
Proof.
  intros Htime Hcount Htotal Hwidth Hcoefficient.
  eapply N.le_trans; [eapply val_positive_cost; eassumption|].
  replace (scale * (common * (N.of_nat total * width)))%N with
    ((scale * common) * (N.of_nat total * width))%N by ring.
  apply N.mul_le_mono_r; exact Hcoefficient.
Qed.

(** A trie observation traverses only the queried key. *)
Lemma build_lookup_time {A} (rho : ptrie A) x w : Pos.size_nat x <= w ->
  (T_trie_get x rho <= 3 * N.of_nat (w + 1))%N.
Proof.
  intro Hwidth; rewrite PTrieT.trie_get_clock; time_cbn; nia.
Qed.

(** One inventory member contributes no more than the complete nonnegative sum. *)
Lemma build_sum_member {A} (weight : A -> nat) xs x : In x xs -> weight x <= build_sum weight xs.
Proof.
  induction xs as [|a rest IH]; [intro Hnone; contradiction|].
  intros [Heq|Hin]; change (weight x <= weight a + build_sum weight rest).
  - subst a; lia.
  - specialize (IH Hin); lia.
Qed.

(** A linear unscaled scan can use the same positive common bit budget. *)
Lemma build_unscaled_budget time coefficient extra count total width common scale :
  (time <= coefficient * N.of_nat count + extra)%N ->
  count <= total -> 1 <= total -> (1 <= width)%N ->
  (coefficient + extra <= scale * common)%N ->
  (time <= scale * (common * (N.of_nat total * width)))%N.
Proof.
  intros Htime Hcount Htotal Hwidth Hcoefficient.
  eapply N.le_trans; [eapply val_unscaled_cost; eassumption|].
  replace (scale * (common * (N.of_nat total * width)))%N with
    ((scale * common) * (N.of_nat total * width))%N by ring.
  apply N.mul_le_mono_r; exact Hcoefficient.
Qed.

(** Literal record-access clocks leave the surrounding budgets folded. *)
Ltac build_projection_clocks :=
  cbv beta iota zeta delta [T_blocks T_entry T_inputs T_params T_code T_term].


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

(** A weighted fold charges one structural step to each positive row weight. *)
Lemma build_place_fold_clock {A B} : forall (f : A -> B -> B) Tf weight xs c w,
  (1 <= w)%N -> (forall x, In x xs -> 1 <= weight x) ->
  (forall x acc, In x xs -> (Tf x acc <= c * N.of_nat (weight x) * w)%N) ->
  forall initial, (List.T_fold_right f Tf initial xs <=
    (c + 2) * N.of_nat (fold_right (fun x n => (weight x + n)%nat) 0%nat xs) * w + 1)%N.
Proof.
  intros f Tf weight xs; induction xs as [|x rest IH]; intros c w Hw Hpositive Hcost initial.
  - time_step.
  - pose proof (Hcost x (fold_right f initial rest) (or_introl eq_refl)) as Hhead.
    pose proof (Hpositive x (or_introl eq_refl)) as Hweight.
    specialize (IH c w Hw ltac:(intros y Hin; apply Hpositive; now right)
      ltac:(intros y acc Hin; apply Hcost; now right) initial).
    time_unfold @List.T_fold_right; cbn [fold_right]; rewrite Nat2N.inj_add.
    time_simpl; nia.
Qed.

(** Deduplication retains no more elements than its input inventory. *)
Lemma build_place_unique_length xs seen : length (build_unique xs seen) <= length xs.
Proof.
  apply NoDup_incl_length; [apply build_unique_nodup|].
  intros x Hin; apply build_unique_spec in Hin; tauto.
Qed.

(** Deduplication inspects each variable at the supplied identifier width. *)
Lemma build_place_unique_clock : forall xs seen w,
  (forall x, In x xs -> Pos.size_nat x <= w) ->
  (T_build_unique xs seen <= (PTrieT.c_trie + 8) *
    N.of_nat (length xs) * N.of_nat (w + 1) + 1)%N.
Proof.
  induction xs as [|x rest IH]; intros seen w Hwidth; [time_step|].
  pose proof (Hwidth x (or_introl eq_refl)) as Hx.
  pose proof (val_mem_time seen x w Hx) as Hmem.
  pose proof (PTrieT.T_set_le unit x tt seen) as Hset.
  assert (Htail : forall y, In y rest -> Pos.size_nat y <= w)
    by (intros y Hin; apply Hwidth; now right).
  time_unfold T_build_unique; time_simpl; cbn [length]; rewrite Nat2N.inj_succ.
  destruct (val_mem seen x).
  - specialize (IH seen w Htail); nia.
  - specialize (IH (PTrieCode.set x tt seen) w Htail).
    rewrite Nat2N.inj_add in Hset; change (N.of_nat 1) with 1%N in Hset.
    nia.
Qed.

(** A definition row deduplicates its variables and inserts each retained binding once. *)
Lemma build_place_def_rows_clock b xs rows w :
  (forall x, In x xs -> Pos.size_nat x <= w) ->
  (T_build_def_rows b xs rows <= (4 * PTrieT.c_trie + 32) *
    N.of_nat (length xs + 1) * N.of_nat (w + 1))%N.
Proof.
  intro Hwidth; pose proof (build_place_unique_clock xs Empty w Hwidth) as Hunique.
  pose proof (build_place_unique_length xs Empty) as Hlength.
  assert (Hw : (1 <= N.of_nat (w + 1))%N) by lia.
  time_unfold T_build_def_rows; time_simpl.
  lazymatch goal with
  | |- context [List.T_fold_right ?f ?Tf ?initial ?keys] =>
    pose proof (val_fold_right_uniform f Tf keys
      ((PTrieT.c_trie + 8) * N.of_nat (w + 1))%N
      ltac:(intros x acc Hin;
        apply build_unique_spec in Hin as [Hin _];
        pose proof (Hwidth x Hin) as Hx;
        pose proof (val_row_time acc x w Hx) as Hrow;
        pose proof (PTrieT.T_set_le (list positive) x (b :: index_row acc x) acc) as Hset;
        time_simpl; rewrite Nat2N.inj_add in Hset;
        change (N.of_nat 1) with 1%N in Hset;
        unfold PTrieT.c_trie in *; nia) initial) as Hfold
  end.
  rewrite Nat2N.inj_add; change (N.of_nat 1) with 1%N.
  unfold PTrieT.c_trie in *; nia.
Qed.

(** Definition occurrences and block headers fit the source syntax inventory. *)
Lemma build_place_defs_weight {K G} (p : func positive K G) :
  fold_right (fun item n => length (block_defs (snd item)) + 1 + n) 0
    (blocks _ _ _ p) <= function_size p.
Proof.
  eapply Nat.le_trans; [|apply val_function_units].
  apply val_sum_mono; intros [b body] Hin; cbn [snd].
  pose proof (val_block_defs_count body); unfold val_body_units; lia.
Qed.

(** A duplicate-free subinventory has at most the weight of the inventory containing it. *)
Lemma build_place_sum_incl {A} (weight : A -> nat) xs ys :
  NoDup xs -> incl xs ys -> build_sum weight xs <= build_sum weight ys.
Proof.
  intro Hunique; revert ys.
  induction Hunique as [|x xs Hnone Hunique IH]; intros ys Hincl.
  - cbn [build_sum fold_right]; lia.
  - destruct (in_split x ys (Hincl x (or_introl eq_refl))) as [before [after Hys]].
    subst ys.
    assert (Htail : incl xs (before ++ after)).
    { intros y Hy. specialize (Hincl y (or_intror Hy)).
      apply in_app_iff in Hincl as [Hbefore|Hrest].
      - apply in_or_app; now left.
      - destruct Hrest as [Heq|Hafter].
        + subst y; contradiction.
        + apply in_or_app; now right. }
    specialize (IH _ Htail). unfold build_sum in *.
    rewrite val_sum_app in IH |- *; cbn [fold_right] in *; lia.
Qed.

(** Filtering keeps distinct mapped keys distinct. *)
Lemma build_place_nodup_map_filter {A B} (f : A -> B) test xs :
  NoDup (map f xs) -> NoDup (map f (filter test xs)).
Proof.
  induction xs as [|x rest IH]; intro Hunique; [constructor|].
  inversion Hunique as [|? ? Hnone Htail]; subst.
  cbn [filter]; destruct (test x); [|apply IH; exact Htail].
  cbn [map]; constructor; [|apply IH; exact Htail].
  intro Hin; apply Hnone. apply in_map_iff in Hin as [y [Heq Hin]].
  apply filter_In in Hin as [Hin _]. apply in_map_iff; exists y; auto.
Qed.

(** A Boolean count is the length of the selected sublist. *)
Lemma build_place_filter_count {A} (test : A -> bool) xs :
  length (filter test xs) = build_sum (fun x => if test x then 1 else 0) xs.
Proof.
  induction xs as [|x rest IH]; [reflexivity|].
  change (length (if test x then x :: filter test rest else filter test rest) =
    (if test x then 1 else 0) + build_sum (fun y => if test y then 1 else 0) rest).
  destruct (test x).
  - change (S (length (filter test rest)) =
      S (build_sum (fun y => if test y then 1 else 0) rest)).
    now rewrite IH.
  - exact IH.
Qed.

(** Distinct queried variables can match at most the supplied variable occurrences. *)
Lemma build_place_exists_count ids values : NoDup ids ->
  build_sum (fun x => if existsb (Pos.eqb x) values then 1 else 0) ids <= length values.
Proof.
  intro Hunique; rewrite <- build_place_filter_count.
  apply NoDup_incl_length; [apply NoDup_filter; exact Hunique|].
  intros x Hin; apply filter_In in Hin as [_ Hyes].
  apply existsb_exists in Hyes as [y [Hin Heq]].
  apply Pos.eqb_eq in Heq; now subst y.
Qed.

(** Finite sums may be exchanged without changing the occurrence count. *)
Lemma build_place_sum_swap {A B} (weight : A -> B -> nat) xs ys :
  build_sum (fun x => build_sum (weight x) ys) xs =
    build_sum (fun y => build_sum (fun x => weight x y) xs) ys.
Proof.
  induction xs as [|x rest IH].
  - change (0 = build_sum (fun _ : B => 0) ys).
    rewrite build_sum_const; lia.
  - change (build_sum (weight x) ys +
      build_sum (fun x => build_sum (weight x) ys) rest =
      build_sum (fun y => weight x y + build_sum (fun x => weight x y) rest) ys).
    rewrite build_sum_add, IH; reflexivity.
Qed.

(** Concatenated row lengths equal the sum of the row lengths. *)
Lemma build_place_flat_length {A B} (rows : A -> list B) xs :
  length (flat_map rows xs) = build_sum (fun x => length (rows x)) xs.
Proof.
  induction xs as [|x rest IH]; [reflexivity|].
  cbn [flat_map build_sum fold_right]; rewrite length_app, IH; reflexivity.
Qed.

(** Summing definition-block counts over distinct variables charges source occurrences once. *)
Lemma build_place_definitions_count {K G} (p : func positive K G) vars : NoDup vars ->
  build_sum (fun x => length (definition_blocks p x)) vars <= function_size p.
Proof.
  intro Hunique.
  assert (Hcounts : build_sum (fun x => length (definition_blocks p x)) vars =
    build_sum (fun x => if existsb (Pos.eqb x) (inputs _ _ _ p) then 1 else 0) vars +
    build_sum (fun item => build_sum
      (fun x => if existsb (Pos.eqb x) (block_defs (snd item)) then 1 else 0) vars)
      (blocks _ _ _ p)).
  { transitivity (build_sum (fun x =>
      (if existsb (Pos.eqb x) (inputs _ _ _ p) then 1 else 0) +
      build_sum (fun item => if existsb (Pos.eqb x) (block_defs (snd item))
        then 1 else 0) (blocks _ _ _ p)) vars).
    - apply build_sum_ext; intros x Hin; unfold definition_blocks.
      rewrite length_app, length_map, build_place_filter_count.
      destruct (existsb (Pos.eqb x) (inputs _ _ _ p)); reflexivity.
    - rewrite build_sum_add, build_place_sum_swap; reflexivity. }
  rewrite Hcounts.
  pose proof (build_place_exists_count vars (inputs _ _ _ p) Hunique) as Hinputs.
  assert (Hblocks : build_sum (fun item => build_sum
    (fun x => if existsb (Pos.eqb x) (block_defs (snd item)) then 1 else 0) vars)
      (blocks _ _ _ p) <= build_sum (fun item => length (block_defs (snd item)))
      (blocks _ _ _ p)).
  { apply val_sum_mono; intros item Hin; apply build_place_exists_count; exact Hunique. }
  pose proof (val_function_defs_count p) as Hdefs.
  rewrite length_app, build_place_flat_length in Hdefs.
  unfold function_size; lia.
Qed.

(** A path from a listed vertex remains inside a well-formed graph. *)
Lemma build_place_path_listed g u trace v : wf_graph g -> In u (verts g) ->
  Spec.path g u trace v -> In v (verts g).
Proof.
  intros Hwf Hin Hpath; revert Hin.
  induction Hpath as [v|u v trace w Hedge Hpath IH]; intro Hin; [exact Hin|].
  apply IH; exact (proj2 Hwf u v Hin Hedge).
Qed.

(** Every semantic frontier target is listed when the root is listed. *)
Lemma build_place_frontier_listed g root x y : wf_graph g -> In root (verts g) ->
  in_frontier g root x y -> In y (verts g).
Proof.
  intros Hwf Hroot [[predecessor [Hreach [Hedge _]]] _].
  destruct Hreach as [r [trace [[Heq|Hnone] Hpath]]]; [subst r|contradiction].
  apply (proj2 Hwf predecessor y); [|exact Hedge].
  eapply build_place_path_listed; eauto.
Qed.

(** Every target in the iterated frontier is a listed frontier target. *)
Lemma build_place_iterated_listed g root seeds y : wf_graph g -> In root (verts g) ->
  in_iterated_frontier g root seeds y -> In y (verts g).
Proof.
  intros Hwf Hroot Hiter; destruct Hiter;
    eapply build_place_frontier_listed; eauto.
Qed.

(** Definition seeds retain the source identifier width. *)
Lemma build_place_seed_width {K G} (p : func positive K G) x b :
  In b (definition_blocks p x) -> Pos.size_nat b <= function_width p.
Proof.
  unfold definition_blocks; intro Hin; apply in_app_iff in Hin as [Hinput|Hbody].
  - destruct (existsb (Pos.eqb x) (inputs _ _ _ p)); [|contradiction].
    destruct Hinput as [Heq|Hnone]; [subst b; apply val_entry_width|contradiction].
  - apply in_map_iff in Hbody as [[id body] [Heq Hin]].
    cbn [fst] in Heq; subst id. apply filter_In in Hin as [Hin _].
    exact (val_block_width p b body Hin).
Qed.

(** Filtering inspects each member once, using its member-specific predicate bound. *)
Lemma build_place_filter_clock {A} (f : A -> bool) Tf xs bound :
  (forall x, In x xs -> (Tf x <= bound)%N) ->
  (List.T_filter f Tf xs <= (bound + 2) * N.of_nat (length xs) + 1)%N.
Proof.
  induction xs as [|x rest IH]; intro Hcost; [time_step|].
  pose proof (Hcost x (or_introl eq_refl)) as Hhead.
  specialize (IH ltac:(intros y Hin; apply Hcost; now right)).
  time_unfold @List.T_filter; cbn [length]; rewrite Nat2N.inj_succ.
  destruct (f x); time_simpl; nia.
Qed.

(** Set bits release the credit needed by binary carries. *)
Fixpoint build_place_positive_credit (p : positive) : N :=
  match p with
  | xH => 1%N
  | xO q => build_place_positive_credit q
  | xI q => (1 + build_place_positive_credit q)%N
  end.

(** Incrementing a binary counter spends constant amortized carry credit. *)
Lemma build_place_positive_succ_credit p :
  (Pos.T_succ p + build_place_positive_credit (Pos.succ p) <=
    2 + build_place_positive_credit p)%N.
Proof.
  induction p as [p IH|p IH|]; time_unfold Pos.T_succ;
    cbn [Pos.succ build_place_positive_credit]; lia.
Qed.

(** Unary conversion performs a sequence of amortized binary increments. *)
Lemma build_place_succ_nat_credit n :
  (Pos.T_of_succ_nat n + build_place_positive_credit (Pos.of_succ_nat n) <=
    3 * N.of_nat n + 2)%N.
Proof.
  induction n as [|n IH]; time_unfold Pos.T_of_succ_nat.
  - reflexivity.
  - pose proof (build_place_positive_succ_credit (Pos.of_succ_nat n)) as Hcarry.
    cbn [Pos.of_succ_nat]; lia.
Qed.

(** Binary conversion has linear cost in its unary input. *)
Lemma build_place_of_nat_clock n :
  (TimeHelpers.N.T_of_nat n <= 3 * N.of_nat n + 2)%N.
Proof.
  destruct n as [|n]; time_unfold TimeHelpers.N.T_of_nat; [lia|].
  pose proof (build_place_succ_nat_credit n); lia.
Qed.

(** Multiplication retains the generated clock and charges both operand widths. *)
Lemma build_place_mul_clock n m :
  (Code.N.T_mul n m <= N.of_nat (N.size_nat n) *
    (N.of_nat (N.size_nat n) + 2 * N.of_nat (N.size_nat m) + 2) + 1)%N.
Proof.
  destruct n as [|p], m as [|q]; time_unfold Code.N.T_mul; cbn [N.size_nat]; try lia.
  pose proof (Pos.T_mul_le p q); lia.
Qed.

(** The number of positive bits is no larger than the represented positive value. *)
Lemma build_place_positive_bits p : Pos.size_nat p <= Pos.to_nat p.
Proof.
  induction p as [p IH|p IH|]; cbn [Pos.size_nat];
    rewrite ?Pos2Nat.inj_xI, ?Pos2Nat.inj_xO, ?Pos2Nat.inj_1; lia.
Qed.

(** A converted natural's bit count is bounded by its unary value. *)
Lemma build_place_nat_bits_value n : N.size_nat (N.of_nat n) <= n.
Proof.
  pose proof (Nat2N.id n) as Hvalue.
  destruct (N.of_nat n) as [|p] eqn:Hn; cbn [N.size_nat] in *; [lia|].
  change (Pos.to_nat p = n) in Hvalue.
  rewrite <- Hvalue; apply build_place_positive_bits.
Qed.

(** A strict power-of-two bound controls the width of unary conversion. *)
Lemma build_place_nat_bits_bound n w : n < 2 ^ w -> N.size_nat (N.of_nat n) <= w.
Proof.
  intro Hbound; pose proof (Nat2N.id n) as Hvalue.
  destruct (N.of_nat n) as [|p] eqn:Hn; cbn [N.size_nat]; [lia|].
  apply Pos.size_nat_least.
  change (Pos.to_nat p = n) in Hvalue; lia.
Qed.

(** Product widths add even when either operand is zero. *)
Lemma build_place_mul_bits n m : N.size_nat (n * m) <= N.size_nat n + N.size_nat m.
Proof.
  destruct n as [|p], m as [|q]; cbn [N.mul N.size_nat]; try lia.
  apply Pos.size_nat_mul.
Qed.

(** Syntax inventory construction copies each variable occurrence a constant number of times. *)
Lemma build_place_function_vars_clock {K G} (p : func positive K G) :
  (T_function_vars p <= 128 * N.of_nat (function_size p + 1))%N.
Proof.
  pose proof (Datatypes.T_app_le (inputs _ _ _ p)
    (flat_map (fun item => val_body_vars (snd item)) (blocks _ _ _ p))) as Hinputs.
  time_unfold @T_function_vars; time_simpl.
  lazymatch goal with |- context [Code.List.T_flat_map ?f ?Tf ?xs] =>
    pose proof (val_flat_map_output_clock f Tf 64%N xs
      ltac:(intros [b body] Hin; time_simpl; cbn [fst snd];
        pose proof (val_exit_uses_clock (term _ _ _ body)) as Hexit;
        pose proof (Datatypes.T_app_le (params _ _ _ body)
          (flat_map (fun '(x, _, args) => x :: args) (code _ _ _ body) ++
            exit_uses (term _ _ _ body))) as Hparams;
        pose proof (Datatypes.T_app_le
          (flat_map (fun '(x, _, args) => x :: args) (code _ _ _ body))
          (exit_uses (term _ _ _ body))) as Hcodeapp;
        lazymatch goal with |- context [Code.List.T_flat_map ?g ?Tg ?code] =>
          pose proof (val_flat_map_output_clock g Tg 2%N code
            ltac:(intros [[dst op] args] Hmember; time_simpl; cbn [length]; nia))
            as Hcode
        end;
        pose proof (val_code_vars_length (code _ _ _ body)) as Hcodecount;
        rewrite !length_app, !Nat2N.inj_add in *;
        change (N.of_nat 1) with 1%N in *; nia)) as Houter
  end.
  unfold val_body_vars in Hinputs.
  unfold function_size, function_vars; rewrite !length_app, !Nat2N.inj_add in *.
  change (N.of_nat 1) with 1%N in *; lia.
Qed.

(** Counting syntax charges variable occurrences, blocks and instructions once. *)
Lemma build_place_function_size_clock {K G} (p : func positive K G) :
  (T_function_size p <= 512 * N.of_nat (function_size p + 1))%N.
Proof.
  pose proof (build_place_function_vars_clock p) as Hvars.
  pose proof (Datatypes.T_length_le (function_vars p)) as Hvarslen.
  pose proof (Datatypes.T_length_le (blocks _ _ _ p)) as Hblockslen.
  pose proof (Nat.T_add_le (length (function_vars p)) (length (blocks _ _ _ p))) as Hadd1.
  pose proof (Nat.T_add_le (length (function_vars p) + length (blocks _ _ _ p))
    (fold_right (fun item n => length (code _ _ _ (snd item)) + n) 0 (blocks _ _ _ p)))
    as Hadd2.
  time_unfold @T_function_size; time_simpl.
  lazymatch goal with |- context [List.T_fold_right ?f ?Tf ?initial ?xs] =>
    pose proof (build_place_fold_clock f Tf
      (fun item => length (code _ _ _ (snd item)) + 1) xs 8%N 1%N ltac:(lia)
      ltac:(intros; cbn beta; lia)
      ltac:(intros [b body] acc Hin;
        pose proof (Datatypes.T_length_le (code _ _ _ body)) as Hlength;
        pose proof (Nat.T_add_le (length (code _ _ _ body)) acc) as Hadd;
        time_simpl; cbn [snd]; rewrite Nat2N.inj_add;
        change (N.of_nat 1) with 1%N; nia) initial) as Hfold
  end.
  cbn beta in Hfold.
  assert (Hweight : fold_right (fun item n => length (code _ _ _ (snd item)) + 1 + n)
    0 (blocks _ _ _ p) <= function_size p).
  { change (build_sum (fun item => length (code _ _ _ (snd item)) + 1)
      (blocks _ _ _ p) <= function_size p).
    rewrite build_sum_add, build_sum_const. unfold function_size, build_sum; lia. }
  apply val_nat_mono in Hweight.
  unfold function_size in Hvars, Hweight |- *; rewrite !Nat2N.inj_add in *.
  change (N.of_nat 1) with 1%N in *; nia.
Qed.

(** Counting live rows charges each row header and each emitted variable once. *)
Lemma build_place_live_rows_clock rows :
  (T_build_live_rows_size rows <= 16 * N.of_nat (build_live_rows_size rows + 1))%N.
Proof.
  time_unfold T_build_live_rows_size; time_simpl.
  lazymatch goal with |- context [List.T_fold_right ?f ?Tf ?initial ?xs] =>
    pose proof (build_place_fold_clock f Tf (fun row => 1 + length (snd row)) xs
      8%N 1%N ltac:(lia) ltac:(intros; cbn beta; lia)
      ltac:(intros [b values] acc Hin;
        pose proof (Datatypes.T_length_le values) as Hlength;
        pose proof (Nat.T_add_le 1 (length values)) as Hadd1;
        pose proof (Nat.T_add_le (1 + length values) acc) as Hadd2;
        time_simpl; cbn [snd]; rewrite !Nat2N.inj_add in *;
        change (N.of_nat 1) with 1%N in *; nia) initial) as Hfold
  end.
  lazymatch type of Hfold with (?clock <= _)%N =>
    change (clock <= (8 + 2) * N.of_nat (build_live_rows_size rows) * 1 + 1)%N in Hfold
  end.
  eapply N.le_trans; [apply N.add_le_mono; [apply N.le_refl|exact Hfold]|].
  rewrite Nat2N.inj_add; change (N.of_nat 1) with 1%N; lia.
Qed.

(** A small constant multiplier charges the value width at most linearly in the value. *)
Lemma build_place_eight_mul_clock n :
  (Code.N.T_mul 8 (N.of_nat n) <= 32 * N.of_nat (n + 1))%N.
Proof.
  pose proof (build_place_mul_clock 8 (N.of_nat n)) as Hclock.
  change (Code.N.T_mul 8 (N.of_nat n) <= 4 *
    (4 + 2 * N.of_nat (N.size_nat (N.of_nat n)) + 2) + 1)%N in Hclock.
  pose proof (build_place_nat_bits_value n) as Hbits.
  rewrite Nat2N.inj_add; change (N.of_nat 1) with 1%N; lia.
Qed.

(** Counting frontier entries scans every listed row header and row member once. *)
Lemma build_place_frontier_entries_clock rows ids w :
  (forall b, In b ids -> Pos.size_nat b <= w) ->
  (T_frontier_entries rows ids <= 32 *
    N.of_nat (length ids + frontier_entries rows ids + 1) * N.of_nat (w + 1))%N.
Proof.
  intro Hwidth; assert (Hw : (1 <= N.of_nat (w + 1))%N) by lia.
  time_unfold T_frontier_entries; time_simpl.
  lazymatch goal with |- context [List.T_fold_right ?f ?Tf ?initial ?xs] =>
    pose proof (build_place_fold_clock f Tf
      (fun b => 1 + length (frontier_row rows b)) xs 16%N (N.of_nat (w + 1)) Hw
      ltac:(intros; cbn beta; lia)
      ltac:(intros b acc Hin;
        assert (Hrow : (T_frontier_row rows b <= 3 * N.of_nat (w + 1))%N)
          by (exact (val_row_time rows b w (Hwidth b Hin)));
        pose proof (Datatypes.T_length_le (frontier_row rows b)) as Hlength;
        pose proof (Nat.T_add_le (length (frontier_row rows b)) acc) as Hadd;
        time_simpl; rewrite !Nat2N.inj_add;
        change (N.of_nat 1) with 1%N; nia) initial) as Hfold
  end.
  assert (Hweight : fold_right (fun b n => 1 + length (frontier_row rows b) + n) 0 ids =
    length ids + frontier_entries rows ids).
  { rewrite val_sum_add, val_sum_one; reflexivity. }
  cbn beta in Hfold; rewrite Hweight in Hfold.
  rewrite !Nat2N.inj_add in *; change (N.of_nat 1) with 1%N in *; nia.
Qed.

(** Linear unary work lifts to the common positive size and bit-width budget. *)
Lemma build_place_linear_charge clock count total coefficient extra factor width :
  (clock <= coefficient * N.of_nat count + extra)%N -> count <= factor * total ->
  1 <= total -> (1 <= width)%N ->
  (clock <= (coefficient * N.of_nat factor + extra) * N.of_nat total * width)%N.
Proof.
  intros Hclock Hcount Htotal Hwidth.
  apply val_nat_mono in Hcount; rewrite Nat2N.inj_mul in Hcount.
  assert (Hunit : (1 <= N.of_nat total)%N) by lia.
  assert (Hextra : (extra <= extra * N.of_nat total)%N).
  { replace extra with (extra * 1)%N at 1 by ring.
    apply N.mul_le_mono_l; exact Hunit. }
  assert (Hflat : (clock <= (coefficient * N.of_nat factor + extra) * N.of_nat total)%N).
  { eapply N.le_trans; [exact Hclock|].
    replace ((coefficient * N.of_nat factor + extra) * N.of_nat total)%N with
      (coefficient * (N.of_nat factor * N.of_nat total) + extra * N.of_nat total)%N by ring.
    apply N.add_le_mono; [apply N.mul_le_mono_l; exact Hcount|exact Hextra]. }
  eapply N.le_trans; [exact Hflat|].
  replace ((coefficient * N.of_nat factor + extra) * N.of_nat total)%N with
    (((coefficient * N.of_nat factor + extra) * N.of_nat total) * 1)%N at 1 by ring.
  apply N.mul_le_mono_l; exact Hwidth.
Qed.


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


  (** Definition indexing charges source variable occurrences at source width. *)
  Lemma place_def_index_clock p :
    (T_def_index p <= (16 * PTrieT.c_trie + 256) *
      N.of_nat (function_size p + 1) * N.of_nat (function_width p + 1))%N.
  Proof.
    set (w := function_width p).
    set (width := N.of_nat (w + 1)).
    set (budget := (N.of_nat (function_size p + 1) * width)%N).
    assert (Hw : (1 <= width)%N) by (unfold width; lia).
    assert (Hbudget : (1 <= budget)%N) by (unfold budget; nia).
    assert (Hinput : forall x, In x (inputs _ _ _ p) -> Pos.size_nat x <= w)
      by (intros x Hin; exact (val_input_width p x Hin)).
    assert (Hinputlen : length (inputs _ _ _ p) + 1 <= function_size p + 1)
      by (unfold function_size, function_vars; rewrite length_app; lia).
    assert (Hinputclock : forall rows, (T_build_def_rows (entry _ _ _ p)
      (inputs _ _ _ p) rows <= (4 * PTrieT.c_trie + 32) * budget)%N).
    { intro rows; eapply N.le_trans; [apply build_place_def_rows_clock; exact Hinput|].
      unfold budget; rewrite N.mul_assoc; apply N.mul_le_mono_r;
        apply N.mul_le_mono_l; apply val_nat_mono; exact Hinputlen. }
    pose proof (build_place_defs_weight p) as Hweight.
    lazymatch goal with |- (_ <= ?rhs)%N =>
      replace rhs with ((16 * PTrieT.c_trie + 256) * budget)%N
        by (unfold budget, width, w; ring) end.
    time_unfold T_def_index; time_simpl.
    lazymatch goal with
    | |- context [List.T_fold_right ?f ?Tf ?initial ?xs] =>
      pose proof (build_place_fold_clock f Tf
        (fun item => length (block_defs (snd item)) + 1) xs
        (4 * PTrieT.c_trie + 48)%N width Hw ltac:(intros; cbn beta; lia)
        ltac:(intros [b body] acc Hin; cbn [fst snd];
          pose proof (val_block_defs_clock body) as Hdefs;
          pose proof (build_place_def_rows_clock b (block_defs body) acc w
            ltac:(intros x Hx; eapply val_body_var_width; [exact Hin|];
              apply val_block_defs_vars; exact Hx)) as Hrows;
          time_simpl; unfold width in *; unfold PTrieT.c_trie in *; nia)
        initial) as Hfold
    end.
    assert (Hfold' : (List.T_fold_right
      (fun item rows => build_def_rows (fst item) (block_defs (snd item)) rows)
      (fun item rows => (1 + (Datatypes.T_fst item + (Datatypes.T_snd item +
        T_block_defs (snd item)) + T_build_def_rows (fst item) (block_defs (snd item)) rows))%N)
      Empty (blocks _ _ _ p) <= (4 * PTrieT.c_trie + 51) * budget)%N).
    { replace ((4 * PTrieT.c_trie + 51) * budget)%N with
        ((4 * PTrieT.c_trie + 48 + 2 + 1) *
          (N.of_nat (function_size p + 1) * width))%N by (unfold budget; ring).
      exact (val_common_cost _ _ _ _ _ _ Hfold Hweight Hw). }
    lazymatch goal with |- context [T_build_def_rows ?b ?xs ?rows] =>
      pose proof (Hinputclock rows) as Hstart end.
    clear Hfold Hinputclock Hinput Hinputlen Hweight.
    revert Hfold'; time_simpl; intro Hfold'.
    clearbody budget width w; unfold PTrieT.c_trie in *; lia.
  Qed.

  (** Live-set indexing charges every row header and variable occurrence once. *)
  Lemma place_live_sets_clock rows w :
    (forall b xs, In (b, xs) rows -> Pos.size_nat b <= w /\
      forall x, In x xs -> Pos.size_nat x <= w) ->
    (T_live_sets rows <= (4 * PTrieT.c_trie + 32) *
      N.of_nat (build_live_rows_size rows + 1) * N.of_nat (w + 1))%N.
  Proof.
    intro Hwidth; assert (Hw : (1 <= N.of_nat (w + 1))%N) by lia.
    time_unfold T_live_sets; time_simpl.
    lazymatch goal with
    | |- context [List.T_fold_right ?f ?Tf ?initial ?xs] =>
      pose proof (build_place_fold_clock f Tf (fun row => 1 + length (snd row)) xs
        (2 * PTrieT.c_trie + 16)%N (N.of_nat (w + 1)) Hw ltac:(intros; cbn beta; lia)
        ltac:(intros [b values] acc Hin; destruct (Hwidth b values Hin) as [Hb Hvalues];
          pose proof (val_set_time values w Hvalues) as Hvalues_clock;
          pose proof (PTrieT.T_set_le (ptrie unit) b (val_set values) acc) as Hset;
          time_simpl; cbn [fst snd]; rewrite !Nat2N.inj_add in *;
          change (N.of_nat 1) with 1%N in *;
          unfold PTrieT.c_trie in *; nia) initial) as Hfold
    end.
    lazymatch type of Hfold with (?clock <= _)%N =>
      change (clock <= (2 * PTrieT.c_trie + 16 + 2) *
        N.of_nat (build_live_rows_size rows) * N.of_nat (w + 1) + 1)%N in Hfold
    end.
    eapply N.le_trans;
      [apply N.add_le_mono; [apply N.le_refl|exact Hfold]|].
    rewrite Nat2N.inj_add; change (N.of_nat 1) with 1%N.
    unfold PTrieT.c_trie; nia.
  Qed.

  Definition place_index_coefficient : N := 64 * (PTrieT.c_trie + 32).

  (** Both indexes fit the source and emitted-live-row inventory. *)
  Lemma place_indexes_clock p :
    (T_def_index p + T_live_sets (L.live_in p) <= place_index_coefficient *
      N.of_nat (function_size p + L.live_size p + 1) * N.of_nat (function_width p + 1))%N.
  Proof.
    pose proof (place_def_index_clock p) as Hdefs.
    pose proof (place_live_sets_clock (L.live_in p) (function_width p)
      ltac:(intros b xs Hin; destruct (L.live_in_ids p (b, xs) Hin) as [Hb Hxs];
        split; [apply PB.block_bits_le; now left|
          intros x Hx; apply universe_width, Hxs; exact Hx])) as Hlive.
    pose proof (L.live_in_size p) as Hrows.
    change (build_live_rows_size (L.live_in p) <= length (blocks _ _ _ p) + L.live_size p)
      in Hrows.
    assert (Hblocks : length (blocks _ _ _ p) <= function_size p)
      by (unfold function_size; lia).
    set (budget := (N.of_nat (function_size p + L.live_size p + 1) *
      N.of_nat (function_width p + 1))%N).
    assert (Hdefs' : (T_def_index p <= (16 * PTrieT.c_trie + 256) * budget)%N).
    { eapply N.le_trans; [exact Hdefs|]. unfold budget; rewrite N.mul_assoc;
        apply N.mul_le_mono_r; apply N.mul_le_mono_l; apply val_nat_mono; lia. }
    assert (Hlive' : (T_live_sets (L.live_in p) <= (4 * PTrieT.c_trie + 32) * budget)%N).
    { eapply N.le_trans; [exact Hlive|]. unfold budget; rewrite N.mul_assoc;
        apply N.mul_le_mono_r; apply N.mul_le_mono_l; apply val_nat_mono; lia. }
    lazymatch goal with |- (_ <= ?rhs)%N =>
      replace rhs with (place_index_coefficient * budget)%N by (unfold budget; ring) end.
    clear Hdefs Hlive Hrows Hblocks; clearbody budget.
    unfold place_index_coefficient, PTrieT.c_trie in *; lia.
  Qed.

  (** A candidate keeps the source blocks and stays within the published work and width. *)
  Lemma F6_produce_size : forall p s c, produce p = Some (s, c) ->
    map fst (blocks _ _ _ s) = map fst (blocks _ _ _ p) /\
    (N.of_nat (function_size s + cert_size c) <= k_size * N.of_nat (build_work p))%N /\
    (N.of_nat (function_width s + vertex_width (cert_ids c)) <=
      k_size * N.of_nat (function_width p + 1))%N.
  Proof.
    intros p s c Hproduce. unfold k_size. now apply produce_size_checked.
  Qed.
  (** The prepared graph node list is the source graph vertex list. *)
  Lemma place_nodes_base g : nodes g = verts (base g).
  Proof. destruct g as [[vs outgoing] incoming vertices edges]; reflexivity. Qed.

  (** The producer graph lists exactly the prepared block nodes. *)
  Lemma place_graph_nodes p : nodes (graph p) = BC.nodes (R.prepare p).
  Proof.
    rewrite place_nodes_base.
    unfold graph; rewrite DG.prepare_base; reflexivity.
  Qed.

  (** Every listed block node retains the source identifier width. *)
  Lemma place_node_width p b : In b (nodes (graph p)) -> Pos.size_nat b <= function_width p.
  Proof.
    rewrite place_graph_nodes; intro Hin; apply PB.block_bits_le; now left.
  Qed.

  (** Distinct universe variables fit the presentation occurrence budget. *)
  Lemma place_universe_inventory p :
    (N.of_nat (length (U.universe (R.prepare p))) <=
      PB.c_present * N.of_nat (function_size p + 1))%N.
  Proof.
    assert (Hlength : length (U.universe (R.prepare p)) <=
      length (U.occurrences (R.prepare p))).
    { apply NoDup_incl_length; [apply U.universe_nodup|].
      intros x Hin; apply universe_occurs; exact Hin. }
    eapply N.le_trans; [|apply PB.points_le].
    apply val_nat_mono; lia.
  Qed.

  (** Every source block identifier occurs in the prepared producer graph. *)
  Lemma place_source_listed p b : In b (map fst (blocks _ _ _ p)) ->
    In b (nodes (graph p)).
  Proof.
    intro Hin; rewrite place_graph_nodes, B.nodes_agree.
    now apply val_first_blocks_ids.
  Qed.

  (** An accepted dominator certificate lists the source entry. *)
  Lemma place_root_listed p :
    D.check (graph p) (entry _ _ _ p) (fst (dom_result p)) (snd (dom_result p)) = true ->
    In (entry _ _ _ p) (nodes (graph p)).
  Proof.
    intro Hcheck; rewrite place_nodes_base; exact (proj1 (D.tree_exact _ _ _ _ Hcheck)).
  Qed.

  (** A seed list contains one optional entry and a distinct subset of source blocks. *)
  Lemma place_seed_rows p x : NoDup (map fst (blocks _ _ _ p)) ->
    D.check (graph p) (entry _ _ _ p) (fst (dom_result p)) (snd (dom_result p)) = true ->
    build_sum (fun b => length (frontier_row (frontiers p) b)) (definition_blocks p x)
      <= 2 * df_size p.
  Proof.
    intros Hunique Hcheck.
    set (tail := map fst (filter
      (fun item => existsb (Pos.eqb x) (block_defs (snd item))) (blocks _ _ _ p))).
    assert (Htail_unique : NoDup tail)
      by (unfold tail; apply build_place_nodup_map_filter; exact Hunique).
    assert (Htail_listed : incl tail (nodes (graph p))).
    { intros b Hin; apply place_source_listed. unfold tail in Hin.
      apply in_map_iff in Hin as [item [Heq Hin]]. apply filter_In in Hin as [Hin _].
      apply in_map_iff; exists item; auto. }
    pose proof (build_place_sum_incl (fun b => length (frontier_row (frontiers p) b))
      tail (nodes (graph p)) Htail_unique Htail_listed) as Htail.
    change (build_sum (fun b => length (frontier_row (frontiers p) b)) tail <= df_size p)
      in Htail.
    assert (Hentry : length (frontier_row (frontiers p) (entry _ _ _ p)) <= df_size p).
    { pose proof (build_place_sum_incl (fun b => length (frontier_row (frontiers p) b))
        [entry _ _ _ p] (nodes (graph p)) ltac:(constructor; [simpl; tauto|constructor])
        ltac:(intros b [Heq|Hnone]; [subst b; apply place_root_listed; exact Hcheck|contradiction]))
        as Hsingle.
      change (length (frontier_row (frontiers p) (entry _ _ _ p)) + 0 <= df_size p) in Hsingle.
      lia. }
    unfold definition_blocks, build_sum; rewrite val_sum_app; fold tail.
    destruct (existsb (Pos.eqb x) (inputs _ _ _ p)); cbn [fold_right].
    - unfold build_sum in Htail; lia.
    - unfold build_sum in Htail; lia.
  Qed.

  (** Checked frontier rows contain only listed graph vertices. *)
  Lemma place_frontier_listed p x y :
    D.check (graph p) (entry _ _ _ p) (fst (dom_result p)) (snd (dom_result p)) = true ->
    In y (frontier_row (frontiers p) x) -> In y (nodes (graph p)).
  Proof.
    intros Hcheck Hin.
    assert (Hexact : domtree_exact (graph p) (entry _ _ _ p) (dom_tree p))
      by (apply D.tree_exact; exact Hcheck).
    apply (proj1 (F.df_spec (graph p) (dom_tree p) (entry _ _ _ p) x y
      (F1_graph_wf p) (DG.prepare_correct _) Hexact)) in Hin.
    rewrite place_nodes_base.
    eapply build_place_frontier_listed; [apply F1_graph_wf|exact (proj1 Hexact)|].
    exact Hin.
  Qed.

  (** Checked iterated frontiers contain only listed graph vertices. *)
  Lemma place_phi_listed p x b :
    D.check (graph p) (entry _ _ _ p) (fst (dom_result p)) (snd (dom_result p)) = true ->
    In b (phi_sites p x) -> In b (nodes (graph p)).
  Proof.
    intros Hcheck Hin.
    assert (Hexact : domtree_exact (graph p) (entry _ _ _ p) (dom_tree p))
      by (apply D.tree_exact; exact Hcheck).
    apply (proj1 (F.idf_spec (graph p) (dom_tree p) (entry _ _ _ p)
      (definition_blocks p x) b (F1_graph_wf p) (DG.prepare_correct _) Hexact)) in Hin.
    rewrite place_nodes_base.
    eapply build_place_iterated_listed; [apply F1_graph_wf|exact (proj1 Hexact)|].
    exact Hin.
  Qed.

  (** Checked frontier targets retain the source identifier width. *)
  Lemma place_frontier_width p x y :
    D.check (graph p) (entry _ _ _ p) (fst (dom_result p)) (snd (dom_result p)) = true ->
    In y (frontier_row (frontiers p) x) -> Pos.size_nat y <= function_width p.
  Proof.
    intros Hcheck Hin; apply place_node_width; eapply place_frontier_listed; eauto.
  Qed.

  (** Checked placement candidates retain the source identifier width. *)
  Lemma place_phi_width p x b :
    D.check (graph p) (entry _ _ _ p) (fst (dom_result p)) (snd (dom_result p)) = true ->
    In b (phi_sites p x) -> Pos.size_nat b <= function_width p.
  Proof.
    intros Hcheck Hin; apply place_node_width; eapply place_phi_listed; eauto.
  Qed.

  (** Every key visited by an indexed IDF search fits the source width. *)
  Lemma place_iteration_width p x :
    D.check (graph p) (entry _ _ _ p) (fst (dom_result p)) (snd (dom_result p)) = true ->
    vertex_width (definition_blocks p x ++ flat_map (frontier_row (frontiers p))
      (definition_blocks p x ++ phi_sites p x)) <= function_width p.
  Proof.
    intro Hcheck; apply val_cfg_vertex_width_le; intros b Hin.
    apply in_app_iff in Hin as [Hseed|Hrow]; [exact (build_place_seed_width p x b Hseed)|].
    apply in_flat_map in Hrow as [a [_ Hin]].
    eapply place_frontier_width; eauto.
  Qed.

  (** A successful guard charges every variable's repeated seed scans to existing work. *)
  Lemma place_allowed_charge p :
    placement_allowed p (R.prepare p) (frontiers p) (L.live_in p)
      (U.universe (R.prepare p)) = true ->
    (N.of_nat (length (U.universe (R.prepare p))) * N.of_nat (df_size p) <=
      16 * N.of_nat (function_size p + L.live_size p + df_size p + 1))%N.
  Proof.
    unfold placement_allowed; rewrite <- place_graph_nodes.
    change (N.leb (N.of_nat (length (U.universe (R.prepare p))) * N.of_nat (df_size p))
      (8 * N.of_nat (function_size p + build_live_rows_size (L.live_in p) + df_size p + 1)) =
      true -> (N.of_nat (length (U.universe (R.prepare p))) * N.of_nat (df_size p) <=
        16 * N.of_nat (function_size p + L.live_size p + df_size p + 1))%N).
    rewrite N.leb_le; intro Hguard.
    pose proof (L.live_in_size p) as Hrows.
    change (build_live_rows_size (L.live_in p) <= length (blocks _ _ _ p) + L.live_size p)
      in Hrows.
    assert (Hblocks : length (blocks _ _ _ p) <= function_size p)
      by (unfold function_size; lia).
    eapply N.le_trans; [exact Hguard|].
    rewrite !Nat2N.inj_add; change (N.of_nat 1) with 1%N.
    nia.
  Qed.

  Lemma place_universe_numeric_width p :
    N.size_nat (N.of_nat (length (U.universe (R.prepare p)))) <= function_width p + 1.
  Proof.
    apply build_place_nat_bits_bound.
    pose proof (universe_count p) as Hcount.
    rewrite Nat.pow_add_r; cbn [Nat.pow].
    pose proof (Nat.pow_nonzero 2 (function_width p) ltac:(lia)); nia.
  Qed.

  (** Guard multiplication charges one source width per variable and frontier entry. *)
  Lemma place_guard_mul_clock p :
    (Code.N.T_mul (N.of_nat (length (U.universe (R.prepare p)))) (N.of_nat (df_size p)) <=
      8 * N.of_nat (length (U.universe (R.prepare p)) + df_size p + 1) *
        N.of_nat (function_width p + 1))%N.
  Proof.
    pose proof (build_place_mul_clock (N.of_nat (length (U.universe (R.prepare p))))
      (N.of_nat (df_size p))) as Hclock.
    pose proof (place_universe_numeric_width p) as Hleft.
    pose proof (build_place_nat_bits_value (df_size p)) as Hright.
    pose proof (build_place_nat_bits_value (length (U.universe (R.prepare p)))) as Hvalue.
    rewrite !Nat2N.inj_add; change (N.of_nat 1) with 1%N.
    nia.
  Qed.

  Lemma place_guard_compare_clock p limit :
    (N.T_leb (N.of_nat (length (U.universe (R.prepare p))) * N.of_nat (df_size p)) limit <=
      8 * N.of_nat (df_size p + 1) * N.of_nat (function_width p + 1))%N.
  Proof.
    pose proof (N.T_leb_le (N.of_nat (length (U.universe (R.prepare p))) *
      N.of_nat (df_size p)) limit) as Hclock.
    pose proof (build_place_mul_bits (N.of_nat (length (U.universe (R.prepare p))))
      (N.of_nat (df_size p))) as Hbits.
    pose proof (place_universe_numeric_width p) as Hleft.
    pose proof (build_place_nat_bits_value (df_size p)) as Hright.
    rewrite !Nat2N.inj_add; change (N.of_nat 1) with 1%N; nia.
  Qed.

  Definition place_guard_coefficient : N :=
    1024 + 4 * BC.c_cfg_adj + 64 * PB.c_present.

  (** The generated guard clock reads both inventories and evaluates its binary comparison. *)
  Lemma place_guard_clock_parts p :
    T_placement_allowed p (R.prepare p) (frontiers p) (L.live_in p)
      (U.universe (R.prepare p)) =
    (BC.T_nodes (R.prepare p) + T_frontier_entries (frontiers p) (nodes (graph p)) +
      Datatypes.T_length (U.universe (R.prepare p)) +
      TimeHelpers.N.T_of_nat (length (U.universe (R.prepare p))) +
      TimeHelpers.N.T_of_nat (df_size p) +
      Code.N.T_mul (N.of_nat (length (U.universe (R.prepare p)))) (N.of_nat (df_size p)) +
      T_function_size p + T_build_live_rows_size (L.live_in p) +
      Nat.T_add (function_size p) (build_live_rows_size (L.live_in p)) +
      Nat.T_add (function_size p + build_live_rows_size (L.live_in p)) (df_size p) +
      Nat.T_add (function_size p + build_live_rows_size (L.live_in p) + df_size p) 1 +
      TimeHelpers.N.T_of_nat
        (function_size p + build_live_rows_size (L.live_in p) + df_size p + 1) +
      Code.N.T_mul 8
        (N.of_nat (function_size p + build_live_rows_size (L.live_in p) + df_size p + 1)) +
      N.T_leb (N.of_nat (length (U.universe (R.prepare p))) * N.of_nat (df_size p))
        (8 * N.of_nat (function_size p + build_live_rows_size (L.live_in p) + df_size p + 1)))%N.
  Proof.
    time_unfold T_placement_allowed; unfold T_frontier_entries.
    rewrite <- place_graph_nodes.
    unfold df_size, F.df_size, frontiers.
    cbv beta delta [PosKeyT.t PosKey.t PosKeyCode.t].
    ring.
  Qed.

  (** The guard charges syntax, live rows and frontier entries on every outcome. *)
  Lemma place_guard_clock p :
    (T_placement_allowed p (R.prepare p) (frontiers p) (L.live_in p)
      (U.universe (R.prepare p)) <= place_guard_coefficient *
      N.of_nat (function_size p + L.live_size p + df_size p + 1) *
        N.of_nat (function_width p + 1))%N.
  Proof.
    set (total := function_size p + L.live_size p + df_size p + 1).
    set (width := N.of_nat (function_width p + 1)).
    set (budget := (N.of_nat total * width)%N).
    assert (Htotal : 1 <= total) by (unfold total; lia).
    assert (Hw : (1 <= width)%N) by (unfold width; lia).
    assert (Hbudget : (1 <= budget)%N) by (unfold budget; nia).
    assert (Hwidth : (width <= budget)%N) by (unfold budget; nia).
    pose proof (L.live_in_size p) as Hlive_size.
    change (build_live_rows_size (L.live_in p) <= length (blocks _ _ _ p) + L.live_size p)
      in Hlive_size.
    pose proof (PB.block_nodes_le p) as Hnodes_size.
    assert (Hblocks_size : length (blocks _ _ _ p) <= function_size p)
      by (unfold function_size; lia).
    assert (Hsource : function_size p + 1 <= total) by (unfold total; lia).
    assert (Hlive : build_live_rows_size (L.live_in p) + 1 <= total) by (unfold total; lia).
    assert (Hnodes : length (BC.nodes (R.prepare p)) + 1 <= total) by (unfold total; lia).
    assert (Hfrontier : df_size p + 1 <= total) by (unfold total; lia).
    assert (Hcombined : function_size p + build_live_rows_size (L.live_in p) + df_size p + 1
      <= 2 * total) by (unfold total; lia).
    pose proof (place_universe_inventory p) as Hvars_size.
    assert (Hvars : ((N.of_nat (length (U.universe (R.prepare p))) + 1) * width <=
      (PB.c_present + 1) * budget)%N).
    { unfold budget; rewrite N.mul_assoc; apply N.mul_le_mono_r.
      pose proof (val_nat_mono _ _ Hsource) as HsourceN.
      assert (Hone : (1 <= N.of_nat total)%N) by lia. nia. }
    assert (Hnative : (T_function_size p <= 512 * budget)%N).
    { eapply N.le_trans; [apply build_place_function_size_clock|].
      unfold budget; pose proof (val_nat_mono _ _ Hsource); nia. }
    assert (Hlive_clock : (T_build_live_rows_size (L.live_in p) <= 16 * budget)%N).
    { eapply N.le_trans; [apply build_place_live_rows_clock|].
      unfold budget; pose proof (val_nat_mono _ _ Hlive); nia. }
    assert (Hnode_clock : (BC.T_nodes (R.prepare p) <= BC.c_cfg_adj * budget)%N).
    { eapply N.le_trans; [apply BC.T_nodes_le|].
      unfold budget; apply N.mul_le_mono_l.
      eapply N.le_trans; [apply val_nat_mono; exact Hnodes|].
      replace (N.of_nat total) with (N.of_nat total * 1)%N at 1 by ring.
      apply N.mul_le_mono_l; exact Hw. }
    assert (Hscan : (T_frontier_entries (frontiers p) (nodes (graph p)) <= 32 * budget)%N).
    { eapply N.le_trans; [apply build_place_frontier_entries_clock; apply place_node_width|].
      change (32 * N.of_nat (length (nodes (graph p)) + df_size p + 1) * width <=
        32 * budget)%N.
      unfold budget; rewrite N.mul_assoc; apply N.mul_le_mono_r; apply N.mul_le_mono_l.
      apply val_nat_mono; rewrite place_graph_nodes; unfold total.
      apply Nat.add_le_mono_r; apply Nat.add_le_mono_r.
      eapply Nat.le_trans; [exact Hnodes_size|]; lia. }
    assert (Hvar_length : (Datatypes.T_length (U.universe (R.prepare p)) <=
      (PB.c_present + 1) * budget)%N).
    { eapply N.le_trans; [apply Datatypes.T_length_le|]. nia. }
    assert (Hvar_convert : (TimeHelpers.N.T_of_nat (length (U.universe (R.prepare p))) <=
      (3 * (PB.c_present + 1)) * budget)%N).
    { eapply N.le_trans; [apply build_place_of_nat_clock|]. nia. }
    assert (Hvar_product : (Code.N.T_mul (N.of_nat (length (U.universe (R.prepare p))))
      (N.of_nat (df_size p)) <= (8 * (PB.c_present + 2)) * budget)%N).
    { eapply N.le_trans; [apply place_guard_mul_clock|].
      rewrite !Nat2N.inj_add; change (N.of_nat 1) with 1%N; fold width.
      pose proof (val_nat_mono _ _ Hfrontier) as HfrontierN.
      assert (Hdf : (N.of_nat (df_size p) * width <= budget)%N)
        by (unfold budget; apply N.mul_le_mono_r; lia).
      nia. }
    assert (Hdf_convert : (TimeHelpers.N.T_of_nat (df_size p) <= 5 * budget)%N).
    { unfold budget; rewrite N.mul_assoc. eapply build_place_linear_charge with (coefficient := 3%N)
        (extra := 2%N) (factor := 1); [apply build_place_of_nat_clock|lia|exact Htotal|exact Hw]. }
    assert (Hcombined_convert : (TimeHelpers.N.T_of_nat
      (function_size p + build_live_rows_size (L.live_in p) + df_size p + 1) <=
      8 * budget)%N).
    { unfold budget; rewrite N.mul_assoc. eapply build_place_linear_charge with (coefficient := 3%N)
        (extra := 2%N) (factor := 2);
        [apply build_place_of_nat_clock|exact Hcombined|exact Htotal|exact Hw]. }
    assert (Hlimit_product : (Code.N.T_mul 8
      (N.of_nat (function_size p + build_live_rows_size (L.live_in p) + df_size p + 1)) <=
      96 * budget)%N).
    { unfold budget; rewrite N.mul_assoc. eapply build_place_linear_charge with (coefficient := 32%N)
        (extra := 0%N) (factor := 3)
        (count := function_size p + build_live_rows_size (L.live_in p) + df_size p + 1 + 1).
      - pose proof (build_place_eight_mul_clock
          (function_size p + build_live_rows_size (L.live_in p) + df_size p + 1)); lia.
      - lia.
      - exact Htotal.
      - exact Hw. }
    assert (Hcomparison : forall limit,
      (N.T_leb (N.of_nat (length (U.universe (R.prepare p))) * N.of_nat (df_size p)) limit <=
        8 * budget)%N).
    { intro limit; eapply N.le_trans; [apply place_guard_compare_clock|].
      unfold budget; rewrite N.mul_assoc; apply N.mul_le_mono_r; apply N.mul_le_mono_l.
      apply val_nat_mono; exact Hfrontier. }
    assert (Hadd : forall n m, n <= 2 * total -> (Nat.T_add n m <= 3 * budget)%N).
    { intros n m Hcount; unfold budget; rewrite N.mul_assoc.
      eapply build_place_linear_charge with (coefficient := 1%N) (extra := 1%N)
        (factor := 2) (count := n);
        [pose proof (Nat.T_add_le n m); lia|exact Hcount|exact Htotal|exact Hw]. }
    pose proof (Hadd (function_size p) (build_live_rows_size (L.live_in p)) ltac:(lia)) as Hadd1.
    pose proof (Hadd (function_size p + build_live_rows_size (L.live_in p)) (df_size p)
      ltac:(lia)) as Hadd2.
    pose proof (Hadd (function_size p + build_live_rows_size (L.live_in p) + df_size p) 1
      ltac:(lia)) as Hadd3.
    specialize (Hcomparison
      (8 * N.of_nat (function_size p + build_live_rows_size (L.live_in p) + df_size p + 1))%N).
    lazymatch goal with |- (_ <= ?rhs)%N =>
      replace rhs with (place_guard_coefficient * budget)%N by
        (unfold budget, total, width; ring) end.
    rewrite place_guard_clock_parts.
    clear Hlive_size Hnodes_size Hblocks_size Hsource Hlive Hnodes Hfrontier Hcombined
      Hvars_size Hvars Hadd.
    clearbody budget width total. unfold place_guard_coefficient. nia.
  Qed.

  Definition place_variable_work p x :=
    length (definition_blocks p x) +
    build_sum (fun b => length (frontier_row (frontiers p) b)) (definition_blocks p x) +
    build_sum (fun b => 1 + length (frontier_row (frontiers p) b)) (phi_sites p x) + 1.

  Definition place_variable_coefficient : N := F.c_frontier + 32.

  Lemma place_variable_positive p x : 1 <= place_variable_work p x.
  Proof. unfold place_variable_work; lia. Qed.

  Lemma place_variable_sites p x : length (phi_sites p x) + 1 <= place_variable_work p x.
  Proof.
    unfold place_variable_work.
    assert (Hsites : length (phi_sites p x) <=
      build_sum (fun b => 1 + length (frontier_row (frontiers p) b)) (phi_sites p x)).
    { rewrite <- val_sum_one at 1; apply val_sum_mono; intros; lia. }
    lia.
  Qed.

  Lemma place_idf_clock p x :
    D.check (graph p) (entry _ _ _ p) (fst (dom_result p)) (snd (dom_result p)) = true ->
    (F.T_idf (frontiers p) (definition_blocks p x) <= F.c_frontier *
      N.of_nat (place_variable_work p x) * N.of_nat (function_width p + 1))%N.
  Proof.
    intro Hcheck; pose proof (place_iteration_width p x Hcheck) as Hwidth.
    eapply N.le_trans; [apply F.T_idf_le|].
    apply N.mul_le_mono.
    - apply N.mul_le_mono_l; apply val_nat_mono.
      unfold idf_work, place_variable_work; rewrite val_sum_app.
      fold (phi_sites p x). unfold build_sum.
      assert (Hrows : fold_right (fun b n => length (frontier_row (frontiers p) b) + n)
        0 (phi_sites p x) <= fold_right
        (fun b n => 1 + length (frontier_row (frontiers p) b) + n) 0 (phi_sites p x))
        by (apply val_sum_mono; intros; lia).
      lia.
    - apply val_nat_mono; change (vertex_width
        (definition_blocks p x ++ flat_map (frontier_row (frontiers p))
          (definition_blocks p x ++ phi_sites p x)) + 1 <= function_width p + 1).
      lia.
  Qed.

  (** A variable search charges all seed rows and all newly discovered rows. *)
  Lemma place_variable_clock p x : In x (U.universe (R.prepare p)) ->
    D.check (graph p) (entry _ _ _ p) (fst (dom_result p)) (snd (dom_result p)) = true ->
    (T_place_var (frontiers p) (def_index p) (live_sets (L.live_in p)) x <=
      place_variable_coefficient * N.of_nat (place_variable_work p x) *
        N.of_nat (function_width p + 1))%N.
  Proof.
    intros Hx Hcheck.
    set (width := N.of_nat (function_width p + 1)).
    set (work := place_variable_work p x).
    set (budget := (N.of_nat work * width)%N).
    assert (Hw : (1 <= width)%N) by (unfold width; lia).
    assert (Hwork : 1 <= work) by apply place_variable_positive.
    assert (Hbudget : (1 <= budget)%N) by (unfold budget; nia).
    assert (Hxwidth : Pos.size_nat x <= function_width p) by (apply universe_width; exact Hx).
    pose proof (place_idf_clock p x Hcheck) as Hidf.
    rewrite <- N.mul_assoc in Hidf.
    change (F.T_idf (frontiers p) (definition_blocks p x) <= F.c_frontier * budget)%N in Hidf.
    assert (Hlookup : (T_frontier_row (def_index p) x <= 3 * width)%N).
    { exact (val_row_time (def_index p) x (function_width p) Hxwidth). }
    lazymatch goal with |- (_ <= ?rhs)%N =>
      replace rhs with (place_variable_coefficient * budget)%N by
        (unfold budget, work, width; ring) end.
    time_unfold T_place_var; time_simpl; rewrite F2a_def_index.
    lazymatch goal with |- context [List.T_filter ?f ?Tf ?xs] =>
      pose proof (build_place_filter_clock f Tf xs (8 * width)%N
        ltac:(intros b Hin;
          change (In b (phi_sites p x)) in Hin;
          pose proof (place_phi_width p x b Hcheck Hin) as Hb;
          time_simpl; rewrite PTrieT.trie_get_clock;
          destruct (trie_get b (live_sets (L.live_in p))) as [values|];
          [pose proof (val_mem_time values x (function_width p) Hxwidth)|];
          unfold width; nia)) as Hfilter
    end.
    assert (Hfilter' : (List.T_filter
      (fun b => match trie_get b (live_sets (L.live_in p)) with
        | Some values => val_mem values x | None => false end)
      (fun b => (1 + (T_trie_get b (live_sets (L.live_in p)) +
        match trie_get b (live_sets (L.live_in p)) with
        | Some values => T_val_mem values x | None => 0 end))%N)
      (phi_sites p x) <= 11 * budget)%N).
    { eapply val_exact_cost with (coefficient := 10%N) (extra := 1%N)
        (count := length (phi_sites p x)); [| |exact Hwork|exact Hw].
      - eapply N.le_trans; [exact Hfilter|].
        replace (10 * N.of_nat (length (phi_sites p x)) * width + 1)%N with
          ((10 * width) * N.of_nat (length (phi_sites p x)) + 1)%N by ring.
        apply N.add_le_mono_r; apply N.mul_le_mono_r; nia.
      - pose proof (place_variable_sites p x); unfold work; lia. }
    clear Hfilter. fold (phi_sites p x).
    assert (Hwidth_budget : (width <= budget)%N) by (unfold budget; nia).
    clearbody budget width work.
    unfold place_variable_coefficient; nia.
  Qed.

  (** The guarded total search work consists of source, live rows, frontiers and placements. *)
  Lemma place_search_inventory p : NoDup (map fst (blocks _ _ _ p)) ->
    D.check (graph p) (entry _ _ _ p) (fst (dom_result p)) (snd (dom_result p)) = true ->
    placement_allowed p (R.prepare p) (frontiers p) (L.live_in p)
      (U.universe (R.prepare p)) = true ->
    (N.of_nat (build_sum (place_variable_work p) (U.universe (R.prepare p))) <=
      (PB.c_present + 40) * N.of_nat
        (function_size p + L.live_size p + df_size p + placement_work p + 1))%N.
  Proof.
    intros Hunique Hcheck Hguard.
    pose proof (build_place_definitions_count p (U.universe (R.prepare p))
      (U.universe_nodup _)) as Hseeds.
    pose proof (place_allowed_charge p Hguard) as Hscan.
    pose proof (place_universe_inventory p) as Hvars.
    assert (Hrows : build_sum
      (fun x => build_sum (fun b => length (frontier_row (frontiers p) b))
        (definition_blocks p x)) (U.universe (R.prepare p)) <=
      length (U.universe (R.prepare p)) * (2 * df_size p)).
    { apply build_sum_bound; intros x Hin; apply place_seed_rows; assumption. }
    assert (Hsplit : build_sum (place_variable_work p) (U.universe (R.prepare p)) =
      build_sum (fun x => length (definition_blocks p x)) (U.universe (R.prepare p)) +
      build_sum (fun x => build_sum (fun b => length (frontier_row (frontiers p) b))
        (definition_blocks p x)) (U.universe (R.prepare p)) +
      placement_work p + length (U.universe (R.prepare p))).
    { unfold place_variable_work.
      rewrite build_sum_add, build_sum_add, build_sum_add, build_sum_const.
      unfold placement_work, build_sum.
      cbv beta delta [PosKeyT.t PosKey.t PosKeyCode.t].
      ring. }
    rewrite Hsplit, !Nat2N.inj_add.
    apply val_nat_mono in Hseeds; apply val_nat_mono in Hrows.
    rewrite !Nat2N.inj_mul in Hrows; change (N.of_nat 2) with 2%N in Hrows.
    rewrite !Nat2N.inj_add in Hscan, Hvars; change (N.of_nat 1) with 1%N in *.
    set (source := N.of_nat (function_size p)).
    set (live := N.of_nat (L.live_size p)).
    set (frontier := N.of_nat (df_size p)).
    set (placed := N.of_nat (placement_work p)).
    fold source live frontier placed in Hscan, Hvars, Hseeds, Hrows.
    nia.
  Qed.

  Definition place_driver_coefficient : N :=
    128 * (place_variable_coefficient + PTrieT.c_trie + 32) * (PB.c_present + 1).

  (** The outer placement fold charges each selected site once after its indexed search. *)
  Lemma place_with_clock p : NoDup (map fst (blocks _ _ _ p)) ->
    D.check (graph p) (entry _ _ _ p) (fst (dom_result p)) (snd (dom_result p)) = true ->
    placement_allowed p (R.prepare p) (frontiers p) (L.live_in p)
      (U.universe (R.prepare p)) = true ->
    (T_placement_with (frontiers p) (def_index p) (live_sets (L.live_in p))
      (U.universe (R.prepare p)) <= place_driver_coefficient *
      N.of_nat (function_size p + L.live_size p + df_size p + placement_work p + 1) *
        N.of_nat (function_width p + 1))%N.
  Proof.
    intros Hunique Hcheck Hguard.
    set (width := N.of_nat (function_width p + 1)).
    set (total := function_size p + L.live_size p + df_size p + placement_work p + 1).
    set (budget := (N.of_nat total * width)%N).
    assert (Hw : (1 <= width)%N) by (unfold width; lia).
    assert (Htotal : 1 <= total) by (unfold total; lia).
    assert (Hbudget : (1 <= budget)%N) by (unfold budget; nia).
    pose proof (place_search_inventory p Hunique Hcheck Hguard) as Hwork.
    fold total in Hwork.
    lazymatch goal with |- (_ <= ?rhs)%N =>
      replace rhs with (place_driver_coefficient * budget)%N by
        (unfold budget, total, width; ring) end.
    time_unfold T_placement_with; time_simpl.
    lazymatch goal with |- context [List.T_fold_right ?f ?Tf ?initial ?vars] =>
      pose proof (build_place_fold_clock f Tf (place_variable_work p) vars
        (place_variable_coefficient + PTrieT.c_trie + 32)%N width Hw
        ltac:(intros x Hin; apply place_variable_positive)
        ltac:(intros x rows Hin;
          pose proof (place_variable_clock p x Hin Hcheck) as Hvar;
          pose proof (place_variable_positive p x) as Hpositive;
          pose proof (place_variable_sites p x) as Hsites;
          assert (Hcount : length (place_var (frontiers p) (def_index p)
            (live_sets (L.live_in p)) x) <= length (phi_sites p x))
            by (unfold place_var; rewrite F2a_def_index; apply filter_length_le);
          time_simpl;
          lazymatch goal with |- context [List.T_fold_right ?g ?Tg ?state ?sites] =>
            pose proof (val_fold_right_uniform g Tg sites
              ((PTrieT.c_trie + 8) * width)%N
              ltac:(intros b acc Hmember;
                assert (Hb : Pos.size_nat b <= function_width p)
                  by (eapply place_phi_width; [exact Hcheck|];
                    exact (proj1 (F3_place_region p x b Hmember)));
                pose proof (val_row_time acc b (function_width p) Hb) as Hrow;
                pose proof (PTrieT.T_set_le (list positive) b (x :: index_row acc b) acc)
                  as Hset;
                time_simpl; rewrite Nat2N.inj_add in Hset;
                change (N.of_nat 1) with 1%N in Hset;
                unfold width; unfold PTrieT.c_trie in *; nia) state) as Hinsert
          end;
          fold width in Hvar;
          unfold PTrieT.c_trie in *;
          nia) initial) as Hfold
    end.
    set (coefficient := (place_variable_coefficient + PTrieT.c_trie + 32 + 2)%N).
    lazymatch type of Hfold with (?clock <= _)%N =>
      change (clock <= coefficient *
        N.of_nat (build_sum (place_variable_work p) (U.universe (R.prepare p))) * width + 1)%N
        in Hfold
    end.
    assert (Hscaled : (coefficient *
      N.of_nat (build_sum (place_variable_work p) (U.universe (R.prepare p))) * width <=
      coefficient * (PB.c_present + 40) * budget)%N).
    { unfold budget; rewrite <- !N.mul_assoc.
      apply N.mul_le_mono_l. rewrite !N.mul_assoc.
      apply N.mul_le_mono_r; exact Hwork. }
    assert (Hcoefficient : (coefficient * (PB.c_present + 40) + 2 <=
      place_driver_coefficient)%N).
    { unfold coefficient, place_driver_coefficient, place_variable_coefficient.
      unfold PTrieT.c_trie; nia. }
    clearbody coefficient budget width total.
    clear Hwork. nia.
  Qed.


  (** Every child in the checked tree is a prepared block node. *)
  Lemma rename_tree_children_in (p : P.t) b child :
    D.check (graph p) (entry _ _ _ p) (fst (dom_result p)) (snd (dom_result p)) = true ->
    In child (children (dom_tree p) b) -> In child (BC.nodes (R.prepare p)).
  Proof.
    intros Hchecked Hin.
    pose proof (D.kids_spec (graph p) (entry _ _ _ p) (fst (dom_result p))
      (snd (dom_result p)) Hchecked b) as [Hparents Hrest].
    apply Hparents in Hin.
    pose proof (D.check_sound _ _ _ _ Hchecked) as [Hparent _].
    pose proof (proj1 (proj2 (Hparent child b Hin))) as Hreach.
    pose proof (proj1 (D.tree_exact _ _ _ _ Hchecked)) as Hentry.
    assert (Hlisted : In child (verts (base (graph p)))).
    { eapply build_reach_listed; [apply F1_graph_wf| |exact Hreach].
      intros root [Heq|Hnone]; [now subst root|contradiction]. }
    unfold graph in Hlisted; rewrite DG.prepare_base in Hlisted; exact Hlisted.
  Qed.

  (** Checked dominator children fit the source identifier width. *)
  Lemma rename_tree_children_width (p : P.t) b child :
    D.check (graph p) (entry _ _ _ p) (fst (dom_result p)) (snd (dom_result p)) = true ->
    In child (children (dom_tree p) b) -> Pos.size_nat child <= function_width p.
  Proof.
    intros Hchecked Hin. apply PB.block_bits_le; left.
    eapply rename_tree_children_in; eassumption.
  Qed.

  (** Each child is charged at most once across distinct source parent identifiers. *)
  Lemma rename_tree_children_unique (p : P.t) : NoDup (map fst (blocks _ _ _ p)) ->
    D.check (graph p) (entry _ _ _ p) (fst (dom_result p)) (snd (dom_result p)) = true ->
    NoDup (flat_map (children (dom_tree p)) (map fst (blocks _ _ _ p))).
  Proof.
    intros Hunique Hchecked.
    apply build_child_rows_unique with (parents := fst (dom_result p)); [exact Hunique| |].
    - intro b. exact (proj1 (proj2 (D.kids_spec _ _ _ _ Hchecked b))).
    - intros b child Hin. exact (proj1 (proj1 (D.kids_spec _ _ _ _ Hchecked b) child) Hin).
  Qed.

  (** The total checked child inventory has at most one entry per source block. *)
  Lemma rename_tree_children_count (p : P.t) : NoDup (map fst (blocks _ _ _ p)) ->
    D.check (graph p) (entry _ _ _ p) (fst (dom_result p)) (snd (dom_result p)) = true ->
    length (flat_map (children (dom_tree p)) (map fst (blocks _ _ _ p))) <=
      length (blocks _ _ _ p).
  Proof.
    intros Hunique Hchecked. eapply Nat.le_trans; [|apply PB.block_nodes_le].
    apply NoDup_incl_length; [now apply rename_tree_children_unique|].
    intros child Hin; apply in_flat_map in Hin as [b [Hb Hchild]].
    eapply rename_tree_children_in; eassumption.
  Qed.

  (** Instruction renaming extends its explicit environment by one binding per instruction. *)
  Lemma rename_code_environment : forall cs names fresh out final final_names next,
    rename_code cs (val_index names) names fresh = Some (out, final, final_names, next) ->
    final = val_index final_names /\ length final_names = length names + length cs.
  Proof.
    induction cs as [|[[x op] xs] rest IH];
      intros names fresh out final final_names next Hrun.
    - cbn [rename_code] in Hrun; inversion Hrun; subst; auto.
    - cbn [rename_code] in Hrun.
      destruct (build_values (val_index names) xs) as [ys|]; [|discriminate].
      destruct (rename_code rest
        (PTrieCode.set x (build_instruction_name fresh) (val_index names))
        ((x, build_instruction_name fresh) :: names) (N.succ fresh))
        as [[[[tail final'] names'] next']|] eqn:Htail; [|discriminate].
      inversion Hrun; subst out final final_names next.
      destruct (IH ((x, build_instruction_name fresh) :: names) (N.succ fresh)
        tail final' names' next' Htail) as [Hindex Hlength].
      split; [exact Hindex|cbn [length] in Hlength |- *; lia].
  Qed.

  (** Every target row of a successful exit was completely rewritten. *)
  Lemma rename_exit_values ending rows rho out : rename_exit ending rows rho = Some out ->
    forall target, In target (exit_targets ending) ->
      exists args, build_values rho (index_row rows target) = Some args.
  Proof.
    intro Hrun; destruct ending as [b old|g xs b old c old'|xs].
    - destruct old as [|x rest]; [|discriminate]. cbn [rename_exit] in Hrun.
      destruct (build_values rho (index_row rows b)) as [args|] eqn:Hargs;
        [|discriminate].
      intros target [Heq|Hnone]; [subst target; eauto|contradiction].
    - destruct old as [|x rest], old' as [|y tail]; try discriminate.
      cbn [rename_exit] in Hrun.
      destruct (build_values rho xs); [|discriminate].
      destruct (build_values rho (index_row rows b)) as [left_args|] eqn:Hleft;
        [|discriminate].
      destruct (build_values rho (index_row rows c)) as [right_args|] eqn:Hright;
        [|discriminate].
      intros target [Heq|[Heq|Hnone]]; [subst target; eauto|subst target; eauto|contradiction].
    - intros target Hnone; contradiction.
  Qed.

  (** Distinct successful edge arguments fit the explicit environment's domain. *)
  Lemma rename_exit_row_size ending rows names out :
    (forall target, NoDup (index_row rows target)) ->
    rename_exit ending rows (val_index names) = Some out ->
    build_sum (fun target => length (index_row rows target)) (exit_targets ending) <=
      2 * length names.
  Proof.
    intros Hunique Hrun.
    eapply Nat.le_trans; [apply build_sum_bound with (amount := length names)|].
    - intros target Hin.
      destruct (rename_exit_values _ _ _ _ Hrun target Hin) as [args Hargs].
      rewrite <- (length_map fst names).
      apply NoDup_incl_length; [apply Hunique|].
      eapply build_values_domain; [intros x y Hget; eapply build_index_domain; exact Hget|].
      exact Hargs.
    - pose proof (build_exit_target_count ending); nia.
  Qed.

  (** Each queued child receives precisely its requested live-row number of bindings. *)
  Lemma rename_children_lengths rows live rho inputs : forall kids tasks,
    rename_children kids rows live rho inputs = Some tasks ->
    forall b names, In (b, names) tasks -> length names = length (index_row live b).
  Proof.
    induction kids as [|child rest IH]; intros tasks Hrun b names Hin.
    - cbn [rename_children] in Hrun; inversion Hrun; subst tasks; contradiction.
    - cbn [rename_children] in Hrun.
      destruct (build_project child (val_set (index_row rows child))
        (index_row live child) rho inputs) as [projected|] eqn:Hproject; [|discriminate].
      destruct (rename_children rest rows live rho inputs) as [tail|] eqn:Htail;
        [|discriminate].
      inversion Hrun; subst tasks. destruct Hin as [Heq|Hin].
      + inversion Heq; subst b names.
        pose proof (build_project_keys _ _ _ _ _ _ Hproject) as Hkeys.
        apply f_equal with (f := @length positive) in Hkeys.
        now rewrite length_map in Hkeys.
      + exact (IH tail eq_refl b names Hin).
  Qed.

  (** Child projection preserves the exact child identifier order. *)
  Lemma rename_children_keys rows live rho inputs : forall kids tasks,
    rename_children kids rows live rho inputs = Some tasks -> map fst tasks = kids.
  Proof.
    induction kids as [|child rest IH]; intros tasks Hrun.
    - cbn [rename_children] in Hrun; inversion Hrun; subst tasks; reflexivity.
    - cbn [rename_children] in Hrun.
      destruct (build_project child (val_set (index_row rows child))
        (index_row live child) rho inputs); [|discriminate].
      destruct (rename_children rest rows live rho inputs) as [tail|] eqn:Htail;
        [|discriminate].
      inversion Hrun; subst tasks; cbn [map fst]; f_equal; apply IH; reflexivity.
  Qed.

  (** Distinct queried blocks charge their live rows at most once. *)
  Lemma rename_live_rows_sum live ids : NoDup ids ->
    build_sum (fun b => length (index_row (val_index live) b)) ids <=
      build_live_rows_size live.
  Proof.
    intro Hunique.
    assert (Hrows : build_sum (fun b => length (index_row (val_index live) b)) ids =
      build_sum (fun b => match lookup b live with Some row => length row | None => 0 end)
        ids).
    { apply build_sum_ext; intros b Hin; unfold index_row; rewrite val_index_lookup.
      destruct (lookup b live); reflexivity. }
    rewrite Hrows. eapply Nat.le_trans; [apply val_lookup_sum; exact Hunique|].
    unfold build_sum, build_live_rows_size; apply val_sum_mono; intros row Hin; lia.
  Qed.

  (** Distinct queried parameter rows charge the published placement work at most once. *)
  Lemma rename_placement_rows_sum p ids : NoDup ids ->
    build_sum (fun b => length (index_row (placement p) b)) ids <= placement_work p.
  Proof.
    intro Hunique; unfold placement.
    eapply Nat.le_trans; [apply placement_rows_size; exact Hunique|].
    unfold placement_work, build_sum; apply val_sum_mono; intros x Hin.
    unfold place_var; rewrite F2a_def_index.
    eapply Nat.le_trans; [apply filter_length_le|].
    unfold phi_sites.
    induction (F.idf (frontiers p) (definition_blocks p x)); cbn [length fold_right]; lia.
  Qed.

  (** A child projection pays for one child, its live row and its parameter row. *)
  Definition rename_child_work (p : P.t) b : nat :=
    1 + length (index_row (val_index (L.live_in p)) b) +
      length (index_row (placement p) b).

  (** Checked tree rows charge each child projection once across all source blocks. *)
  Lemma rename_child_work_total p : NoDup (map fst (blocks _ _ _ p)) ->
    D.check (graph p) (entry _ _ _ p) (fst (dom_result p)) (snd (dom_result p)) = true ->
    build_sum (fun b => build_sum (rename_child_work p) (children (dom_tree p) b))
      (map fst (blocks _ _ _ p)) <=
      length (blocks _ _ _ p) + build_live_rows_size (L.live_in p) + placement_work p.
  Proof.
    intros Hunique Hchecked; rewrite build_sum_flat_map.
    pose proof (rename_tree_children_unique p Hunique Hchecked) as Hchildren.
    pose proof (rename_tree_children_count p Hunique Hchecked) as Hcount.
    pose proof (rename_live_rows_sum (L.live_in p) _ Hchildren) as Hlive.
    pose proof (rename_placement_rows_sum p _ Hchildren) as Hplaced.
    unfold rename_child_work; rewrite !build_sum_add, build_sum_const; lia.
  Qed.

  (** One cached body pays for source syntax, entry bindings and its child projections. *)
  Definition rename_body_work (p : P.t) b : nat :=
    1 +
    (match lookup b (blocks _ _ _ p) with Some body => build_core_size body | None => 0 end) +
    (if Pos.eqb b (entry _ _ _ p) then length (inputs _ _ _ p) else 0) +
    length (index_row (val_index (L.live_in p)) b) +
    length (index_row (placement p) b) +
    build_sum (rename_child_work p) (children (dom_tree p) b).

  (** The initial body budget is bounded by source syntax, liveness and placement work. *)
  Lemma rename_body_work_total p : NoDup (map fst (blocks _ _ _ p)) ->
    D.check (graph p) (entry _ _ _ p) (fst (dom_result p)) (snd (dom_result p)) = true ->
    build_sum (rename_body_work p) (map fst (blocks _ _ _ p)) <=
      8 * (function_size p + L.live_size p + placement_work p + 1).
  Proof.
    intros Hunique Hchecked.
    pose proof (val_lookup_sum (blocks _ _ _ p) (map fst (blocks _ _ _ p))
      (@build_core_size O.K O.G) Hunique) as Hsyntax.
    pose proof (val_sum_single (map fst (blocks _ _ _ p)) (entry _ _ _ p)
      (length (inputs _ _ _ p)) Hunique) as Hinputs.
    pose proof (rename_live_rows_sum (L.live_in p) _ Hunique) as Hlive.
    pose proof (rename_placement_rows_sum p _ Hunique) as Hplaced.
    pose proof (rename_child_work_total p Hunique Hchecked) as Hchildren.
    pose proof (L.live_in_size p) as Hrows.
    change (build_live_rows_size (L.live_in p) <= length (blocks _ _ _ p) + L.live_size p)
      in Hrows.
    pose proof (build_function_decompose p) as Hsource.
    unfold rename_body_work; rewrite !build_sum_add, build_sum_const, length_map.
    unfold build_sum in Hsyntax, Hinputs, Hlive, Hplaced, Hchildren, Hsource |- *; lia.
  Qed.

  (** Renaming code scans source operands and allocates each instruction exactly once. *)
  Lemma rename_code_time : forall cs rho names fresh w limit,
    (forall x, In x (flat_map (fun i => fst (fst i) :: snd i) cs) ->
      Pos.size_nat x <= w) ->
    N.to_nat fresh + length cs <= limit ->
    (forall i, N.to_nat i < limit -> N.size_nat i <= w) ->
    (T_rename_code cs rho names fresh <=
      64 * (PTrieT.c_trie + 1) *
        N.of_nat (build_code_vars cs + length cs + 1) * N.of_nat (w + 1))%N.
  Proof.
    induction cs as [|[[x op] xs] rest IH]; intros rho names fresh w limit Hwidth Hlimit Hcounter.
    - time_step.
    - assert (Hx : Pos.size_nat x <= w).
      { apply Hwidth; cbn [flat_map]; now left. }
      assert (Hxs : forall y, In y xs -> Pos.size_nat y <= w).
      { intros y Hin; apply Hwidth; cbn [flat_map]; right; apply in_or_app; now left. }
      assert (Hrest : forall y, In y (flat_map (fun i => fst (fst i) :: snd i) rest) ->
          Pos.size_nat y <= w).
      { intros y Hin; apply Hwidth; cbn [flat_map]; right; apply in_or_app; now right. }
      assert (Hfresh : N.size_nat fresh <= w) by (apply Hcounter; cbn [length] in Hlimit; lia).
      assert (Hnext : N.to_nat (N.succ fresh) + length rest <= limit).
      { rewrite N2Nat.inj_succ; cbn [length] in Hlimit; lia. }
      pose proof (build_values_time xs rho w Hxs) as Hvalues.
      pose proof (build_instruction_time fresh w Hfresh) as Hname.
      pose proof (PTrieT.T_set_le positive x (build_instruction_name fresh) rho) as Hset.
      pose proof (N.T_succ_le fresh) as Hsucc.
      specialize (IH (PTrieCode.set x (build_instruction_name fresh) rho)
        ((x, build_instruction_name fresh) :: names) (N.succ fresh) w limit
        Hrest Hnext Hcounter).
      assert (Hset' : (PTrieCode.T_set x (build_instruction_name fresh) rho <=
          PTrieT.c_trie * N.of_nat (w + 1))%N).
      { eapply N.le_trans; [exact Hset|]. apply N.mul_le_mono_l, time_of_nat_le; lia. }
      assert (Hsucc' : (N.T_succ fresh <= N.of_nat (w + 1))%N).
      { clear - Hsucc Hfresh. rewrite Nat2N.inj_add; lia. }
      pose proof (N.add_le_mono _ _ _ _
        (N.add_le_mono _ _ _ _ (N.add_le_mono _ _ _ _ Hvalues Hname) Hset') Hsucc')
        as Hhead.
      pose proof (N.add_le_mono _ _ _ _ Hhead IH) as Hall.
      unfold build_code_vars at 1; cbn [flat_map]; rewrite length_app;
        cbn [length]; fold (@build_code_vars O.K rest).
      eapply N.le_trans with (m := (1 + T_build_values rho xs +
        T_build_instruction_name fresh + PTrieCode.T_set x (build_instruction_name fresh) rho +
        N.T_succ fresh + T_rename_code rest
          (PTrieCode.set x (build_instruction_name fresh) rho)
          ((x, build_instruction_name fresh) :: names) (N.succ fresh))%N).
      + time_unfold T_rename_code; destruct (build_values rho xs); lia.
      + clear - Hall. unfold PTrieT.c_trie in *.
        rewrite !Nat2N.inj_add, !Nat2N.inj_succ in *; nia.
  Qed.

  (** Exit rewriting scans its original operands and the supplied target parameter rows. *)
  Lemma rename_exit_time ending rows rho w :
    (forall target, In target (exit_targets ending) -> Pos.size_nat target <= w) ->
    (forall x, In x (exit_uses ending) -> Pos.size_nat x <= w) ->
    (forall target x, In x (index_row rows target) -> Pos.size_nat x <= w) ->
    (T_rename_exit ending rows rho <=
      64 * N.of_nat (build_exit_base ending +
        build_sum (fun target => length (index_row rows target)) (exit_targets ending) + 1) *
        N.of_nat (w + 1))%N.
  Proof.
    intros Htargets Huses Hrows; destruct ending as [b old|g xs b old c old'|xs].
    - pose proof (val_row_time rows b w ltac:(apply Htargets; now left)) as Hrow.
      pose proof (build_values_time (index_row rows b) rho w (Hrows b)) as Hvalues.
      time_unfold T_rename_exit; destruct old, (build_values rho (index_row rows b));
        cbn [build_exit_base build_sum exit_targets fold_right]; time_cbn; nia.
    - assert (Hxs : forall x, In x xs -> Pos.size_nat x <= w).
      { intros x Hin; apply Huses; cbn [exit_uses]; apply in_or_app; now left. }
      pose proof (build_values_time xs rho w Hxs) as Hguard.
      pose proof (val_row_time rows b w ltac:(apply Htargets; now left)) as Hleft.
      pose proof (val_row_time rows c w ltac:(apply Htargets; right; now left)) as Hright.
      pose proof (build_values_time (index_row rows b) rho w (Hrows b)) as Hleft_values.
      pose proof (build_values_time (index_row rows c) rho w (Hrows c)) as Hright_values.
      time_unfold T_rename_exit;
        destruct old, old', (build_values rho xs), (build_values rho (index_row rows b)),
          (build_values rho (index_row rows c));
        cbn [build_exit_base build_sum exit_targets fold_right]; time_cbn; nia.
    - pose proof (build_values_time xs rho w Huses) as Hvalues.
      time_unfold T_rename_exit; destruct (build_values rho xs);
        cbn [build_exit_base build_sum exit_targets fold_right]; time_cbn; nia.
  Qed.

  (** Child projection scans each child's live and parameter row once. *)
  Lemma rename_children_time p : forall kids rho inputs w,
    function_width p <= w -> (forall b, In b kids -> Pos.size_nat b <= w) ->
    (T_rename_children kids (placement p) (val_index (L.live_in p)) rho inputs <=
      64 * (PTrieT.c_trie + c_glue + 1) *
        N.of_nat (build_sum (rename_child_work p) kids + 1) * N.of_nat (w + 1))%N.
  Proof.
    induction kids as [|b rest IH]; intros rho inputs w Hsource Hkids.
    - time_step.
    - assert (Hb : Pos.size_nat b <= w) by (apply Hkids; now left).
      assert (Hphis : forall x, In x (index_row (placement p) b) -> Pos.size_nat x <= w).
      { intros x Hin; pose proof (placement_row_width p b x Hin); lia. }
      assert (Hlive : forall x, In x (index_row (val_index (L.live_in p)) b) ->
          Pos.size_nat x <= w).
      { intros x Hin; pose proof (live_row_width p b x Hin); lia. }
      pose proof (val_row_time (placement p) b w Hb) as Hrow.
      pose proof (val_row_time (val_index (L.live_in p)) b w Hb) as Hlive_row.
      pose proof (val_set_time (index_row (placement p) b) w Hphis) as Hset.
      pose proof (build_project_time (index_row (val_index (L.live_in p)) b) b
        (val_set (index_row (placement p) b)) rho inputs w Hb Hlive) as Hproject.
      specialize (IH rho inputs w Hsource ltac:(intros child Hin; apply Hkids; now right)).
      set (unit := ((PTrieT.c_trie + c_glue + 1) *
        (N.of_nat (rename_child_work p b) * N.of_nat (w + 1)))%N).
      assert (Hcount : 1 <= rename_child_work p b) by (unfold rename_child_work; lia).
      assert (Hunit : (1 <= unit)%N).
      { unfold unit; clear - Hcount; nia. }
      assert (Hrow' : (T_index_row (placement p) b <= 3 * unit)%N).
      { eapply build_component_budget with (coefficient := 3%N) (extra := 0%N)
          (count := 1).
        - change (T_index_row (placement p) b <= (3 * 1) * N.of_nat (w + 1) + 0)%N.
          rewrite N.mul_1_r, N.add_0_r; exact Hrow.
        - exact Hcount.
        - exact Hcount.
        - lia.
        - lia. }
      assert (Hlive_row' :
          (T_index_row (val_index (L.live_in p)) b <= 3 * unit)%N).
      { eapply build_component_budget with (coefficient := 3%N) (extra := 0%N)
          (count := 1).
        - change (T_index_row (val_index (L.live_in p)) b <=
            (3 * 1) * N.of_nat (w + 1) + 0)%N.
          rewrite N.mul_1_r, N.add_0_r; exact Hlive_row.
        - exact Hcount.
        - exact Hcount.
        - lia.
        - lia. }
      assert (Hset' : (T_val_set (index_row (placement p) b) <= 4 * unit)%N).
      { eapply build_component_budget with (coefficient := (PTrieT.c_trie + 2)%N)
          (extra := 1%N) (count := length (index_row (placement p) b)).
        - exact Hset.
        - unfold rename_child_work; lia.
        - exact Hcount.
        - lia.
        - lia. }
      assert (Hproject' : (T_build_project b (val_set (index_row (placement p) b))
        (index_row (val_index (L.live_in p)) b) rho inputs <= 16 * unit)%N).
      { eapply build_component_budget with (coefficient := (16 * (c_glue + 1))%N)
          (extra := 0%N) (count := length (index_row (val_index (L.live_in p)) b) + 1).
        - rewrite N.add_0_r; exact Hproject.
        - unfold rename_child_work; lia.
        - exact Hcount.
        - lia.
        - lia. }
      assert (Hhead : (1 + T_index_row (placement p) b +
        T_val_set (index_row (placement p) b) + T_index_row (val_index (L.live_in p)) b +
        T_build_project b (val_set (index_row (placement p) b))
          (index_row (val_index (L.live_in p)) b) rho inputs <= 64 * unit)%N) by lia.
      eapply N.le_trans with (m := (1 + T_index_row (placement p) b +
        T_val_set (index_row (placement p) b) + T_index_row (val_index (L.live_in p)) b +
        T_build_project b (val_set (index_row (placement p) b))
          (index_row (val_index (L.live_in p)) b) rho inputs +
        T_rename_children rest (placement p) (val_index (L.live_in p)) rho inputs)%N).
      + time_unfold T_rename_children.
        destruct (build_project b (val_set (index_row (placement p) b))
          (index_row (val_index (L.live_in p)) b) rho inputs); lia.
      + eapply N.le_trans; [apply N.add_le_mono; [exact Hhead|exact IH]|].
        unfold unit; cbn [build_sum fold_right]; fold (build_sum (rename_child_work p) rest).
        rewrite !Nat2N.inj_add; ring_simplify; apply N.le_refl.
  Qed.

  (** Counters bounded by source syntax fit within the source's explicit size width. *)
  Lemma rename_counter_width (p : P.t) i : N.to_nat i <= function_size p ->
    N.size_nat i <= function_width p.
  Proof.
    destruct i as [|value]; intro Hlimit; [cbn [N.size_nat]; lia|].
    cbn [N.size_nat]. eapply Nat.le_trans; [|apply build_function_size_bits].
    apply Pos.size_nat_monotone, Pos2Nat.inj_lt.
    rewrite SuccNat2Pos.id_succ; cbn [N.to_nat] in Hlimit; lia.
  Qed.

  (** Source block code variables are covered by the function's identifier width. *)
  Lemma rename_source_code_width (p : P.t) b body x :
    lookup b (blocks _ _ _ p) = Some body ->
    In x (flat_map (fun i => fst (fst i) :: snd i) (code _ _ _ body)) ->
    Pos.size_nat x <= function_width p.
  Proof.
    intros Hsource Hvar; apply val_lookup_in in Hsource.
    eapply val_body_var_width; [exact Hsource|].
    unfold val_body_vars; apply in_or_app; right; apply in_or_app; left.
    apply in_flat_map in Hvar as [instruction [Hin Hvar]].
    apply in_flat_map; exists instruction; split; [exact Hin|].
    destruct instruction as [[y op] xs]; exact Hvar.
  Qed.

  (** Source block exit operands are covered by the function's identifier width. *)
  Lemma rename_source_exit_width (p : P.t) b body x :
    lookup b (blocks _ _ _ p) = Some body -> In x (exit_uses (term _ _ _ body)) ->
    Pos.size_nat x <= function_width p.
  Proof.
    intros Hsource Hvar; apply val_lookup_in in Hsource.
    eapply val_body_var_width; [exact Hsource|].
    unfold val_body_vars; apply in_or_app; right; apply in_or_app; now right.
  Qed.

  (** A cached body's instruction scan fits its original payload and source width. *)
  Lemma rename_cached_code_time p st b body names : rename_cache p st ->
    trie_get b (rename_bodies _ _ st) = Some body ->
    (T_rename_code (code _ _ _ body) (val_index names) names (next_value _ _ st) <=
      64 * (PTrieT.c_trie + 1) *
        N.of_nat (build_core_size body + 1) * N.of_nat (rename_value_width p + 1))%N.
  Proof.
    intros Hcache Hbody.
    pose proof (proj1 (proj1 (proj2 Hcache) b body Hbody)) as Hsource.
    assert (Hlimit : N.to_nat (next_value _ _ st) + length (code _ _ _ body) <=
        function_size p).
    { eapply Nat.le_trans; [eapply rename_cache_next; eassumption|apply build_function_code_size]. }
    pose proof (rename_code_time (code _ _ _ body) (val_index names) names
      (next_value _ _ st) (rename_value_width p) (function_size p)
      ltac:(intros x Hin; pose proof (rename_source_code_width p b body x Hsource Hin);
        unfold rename_value_width; lia) Hlimit
      ltac:(intros i Hi; pose proof (rename_counter_width p i ltac:(lia));
        unfold rename_value_width; lia)) as Hcode.
    eapply N.le_trans; [exact Hcode|].
    apply N.mul_le_mono_r, N.mul_le_mono_l, time_of_nat_le.
    unfold build_core_size; lia.
  Qed.

  (** Initial indexing and task creation are linear in source syntax at source width. *)
  Lemma rename_initial_time p :
    (T_rename_init p <= 64 * (PTrieT.c_trie + 1) *
      N.of_nat (function_size p + 1) * N.of_nat (function_width p + 1))%N.
  Proof.
    pose proof (val_index_time (blocks _ _ _ p) (function_width p)
      ltac:(intros b body Hin; eapply val_block_width; exact Hin)) as Hindex.
    pose proof (build_input_pairs_time (inputs _ _ _ p)) as Hinputs.
    assert (Htask : forall item : positive * block positive O.K O.G,
      (1 + Datatypes.T_fst item <= 2)%N).
    { intro item; pose proof (Datatypes.T_fst_le item) as Hfst; lia. }
    pose proof (ListDef.T_map_le
      (fun item : positive * block positive O.K O.G => (fst item, @nil (positive * positive)))
      (fun item => 1 + Datatypes.T_fst item)%N 2%N (blocks _ _ _ p)
      Htask) as Htasks.
    pose proof (build_function_decompose p) as Hsize.
    time_unfold T_rename_init; build_projection_clocks; unfold PTrieT.c_trie in *.
    rewrite !Nat2N.inj_add in *.
    nia.
  Qed.

  (** Pending tasks carry source-width labels and only their requested live bindings. *)
  Definition rename_task_budget (p : P.t) (st : rename_state O.K O.G) : Prop :=
    forall b names, In (b, names) (rename_stack _ _ st) ->
      Pos.size_nat b <= function_width p /\
      length names <=
        (if Pos.eqb b (entry _ _ _ p) then length (inputs _ _ _ p) else 0) +
          length (index_row (val_index (L.live_in p)) b).

  (** Initial tasks consist of one tagged input environment and empty fallback tasks. *)
  Lemma rename_task_budget_init p : rename_task_budget p (rename_init p).
  Proof.
    intros b names Hin; cbn [rename_init rename_stack] in Hin.
    destruct Hin as [Heq|Hin].
    - inversion Heq; subst b names; split; [apply val_entry_width|].
      rewrite Pos.eqb_refl, length_map; lia.
    - apply in_map_iff in Hin as [[a body] [Heq Hin]].
      inversion Heq; subst b names; split; [eapply val_block_width; exact Hin|cbn; lia].
  Qed.

  (** Successful child projection preserves the pending-task budget. *)
  Lemma rename_task_budget_step p st next :
    D.check (graph p) (entry _ _ _ p) (fst (dom_result p)) (snd (dom_result p)) = true ->
    rename_task_budget p st ->
    rename_step p (dom_tree p) (placement p) (L.live_in p) st = inl next ->
    rename_task_budget p next.
  Proof.
    destruct st as [bodies tasks output envs fresh]; intros Hchecked Htasks Hstep.
    unfold rename_step in Hstep; destruct tasks as [|[b inherited] tasks].
    - cbn [rename_step_indexed] in Hstep.
      destruct (build_materialize (blocks _ _ _ p) (val_index output)); discriminate.
    - cbn [rename_step_indexed] in Hstep.
      destruct (trie_get b bodies) as [body|] eqn:Hbody.
      + destruct (params _ _ _ body) as [|x rest]; [|discriminate].
        destruct (if Pos.eqb b (entry _ _ _ p) then
          match index_row (placement p) b with [] => Some inherited | _ => None end
          else build_project b (val_set (index_row (placement p) b))
            (index_row (val_index (L.live_in p)) b) (val_index inherited)
            (val_index (map (fun x => (x, build_input_name x)) (inputs _ _ _ p))))
          as [names|] eqn:Hnames; [|discriminate].
        destruct (rename_code (code _ _ _ body) (val_index names) names fresh)
          as [[[[cs final] final_names] last]|] eqn:Hcode; [|discriminate].
        destruct (rename_exit (term _ _ _ body) (placement p) final) as [ending|];
          [|discriminate].
        destruct (rename_children (children (dom_tree p) b) (placement p)
          (val_index (L.live_in p)) final
          (val_index (map (fun x => (x, build_input_name x)) (inputs _ _ _ p))))
          as [kids|] eqn:Hkids; [|discriminate].
        inversion Hstep; subst next; intros a row Hin; cbn [rename_stack] in Hin.
        apply in_app_or in Hin as [Hin|Hin].
        * pose proof (rename_children_lengths _ _ _ _ _ _ Hkids a row Hin) as Hlength.
          assert (Hchild : In a (children (dom_tree p) b)).
          { rewrite <- (rename_children_keys _ _ _ _ _ _ Hkids).
            apply in_map with (f := fst) in Hin; exact Hin. }
          split; [eapply rename_tree_children_width; eassumption|rewrite Hlength; lia].
        * apply Htasks; right; exact Hin.
      + inversion Hstep; subst next; intros a row Hin; apply Htasks; right; exact Hin.
  Qed.

  (** The cached runtime combines syntax, value widths and pending-task bounds. *)
  Definition rename_runtime (p : P.t) (st : rename_state O.K O.G) : Prop :=
    rename_info p (placement p) (L.live_in p) st /\
      rename_width p st /\ rename_task_budget p st.

  (** Initial renaming satisfies every runtime invariant. *)
  Lemma rename_runtime_init p : rename_runtime p (rename_init p).
  Proof.
    split; [apply rename_info_init|].
    split; [apply rename_width_init|apply rename_task_budget_init].
  Qed.

  (** Every continuing cached step preserves the runtime invariant. *)
  Lemma rename_runtime_step p st next :
    D.check (graph p) (entry _ _ _ p) (fst (dom_result p)) (snd (dom_result p)) = true ->
    rename_runtime p st ->
    rename_step p (dom_tree p) (placement p) (L.live_in p) st = inl next ->
    rename_runtime p next.
  Proof.
    intros Hchecked [Hinfo [Hwidth Htasks]] Hstep; split.
    - eapply rename_info_step; eassumption.
    - split.
      + eapply rename_width_step; eassumption.
      + eapply rename_task_budget_step; eassumption.
  Qed.

  (** The actual cached entry-name expression is shared by the clock proof. *)
  Definition rename_entry_names (p : P.t) b inherited : option renaming :=
    if Pos.eqb b (entry _ _ _ p) then
      match index_row (placement p) b with [] => Some inherited | _ => None end
    else build_project b (val_set (index_row (placement p) b))
      (index_row (val_index (L.live_in p)) b) (val_index inherited)
      (val_index (map (fun x => (x, build_input_name x)) (inputs _ _ _ p))).

  (** Successful active entry names have bounded keys and values. *)
  Lemma rename_active_names_width p bodies b inherited tasks output envs fresh body names :
    rename_runtime p
      (RenameState O.K O.G bodies ((b, inherited) :: tasks) output envs fresh) ->
    trie_get b bodies = Some body -> rename_entry_names p b inherited = Some names ->
    build_names_bounded names (rename_value_width p).
  Proof.
    intros [Hinfo [[Hout [Henv Htasks]] Hbudget]] Hget Hnames.
    pose proof (proj1 (proj1 (proj2 (proj1 Hinfo)) b body Hget)) as Hsource.
    assert (Hinherited : build_names_bounded inherited (rename_value_width p)).
    { exact (Htasks b inherited body (or_introl eq_refl) Hsource). }
    unfold rename_entry_names in Hnames; destruct (Pos.eqb b (entry _ _ _ p)).
    - destruct (index_row (placement p) b); [inversion Hnames; now subst names|discriminate].
    - eapply projected_names_bounded; eassumption.
  Qed.

  (** Successful active entry names fit the source input or this block's live row. *)
  Lemma rename_active_names_length p bodies b inherited tasks output envs fresh body names :
    rename_runtime p
      (RenameState O.K O.G bodies ((b, inherited) :: tasks) output envs fresh) ->
    trie_get b bodies = Some body -> rename_entry_names p b inherited = Some names ->
    length names <=
      (if Pos.eqb b (entry _ _ _ p) then length (inputs _ _ _ p) else 0) +
        length (index_row (val_index (L.live_in p)) b).
  Proof.
    intros [Hinfo Hrest] Hbody Hnames.
    eapply (rename_names_length p bodies b inherited tasks output envs fresh body
      (placement p) (L.live_in p) names).
    - exact (proj2 (proj2 (proj2 (proj2 Hinfo)))).
    - exact Hbody.
    - exact Hnames.
  Qed.

  (** An exit's row work counts every supplied outgoing parameter occurrence. *)
  Definition rename_exit_row_work (p : P.t) (body : block positive O.K O.G) : nat :=
    build_sum (fun target => length (index_row (placement p) target))
      (exit_targets (term _ _ _ body)).

  (** A successful exit charges its rows to the entry bindings and fresh definitions. *)
  Lemma rename_success_rows p body names fresh cs final final_names next ending :
    rename_code (code _ _ _ body) (val_index names) names fresh =
      Some (cs, final, final_names, next) ->
    rename_exit (term _ _ _ body) (placement p) final = Some ending ->
    rename_exit_row_work p body <= 2 * (length names + length (code _ _ _ body)).
  Proof.
    intros Hcode Hexit.
    destruct (rename_code_environment _ _ _ _ _ _ _ Hcode) as [Hindex Hlength].
    rewrite Hindex in Hexit.
    pose proof (rename_exit_row_size _ _ _ _ (placement_row_unique p) Hexit) as Hrows.
    unfold rename_exit_row_work; rewrite <- Hlength; exact Hrows.
  Qed.

  (** An arbitrary terminal exit can scan at most two complete placement rows. *)
  Lemma rename_terminal_rows p body : rename_exit_row_work p body <= 2 * placement_work p.
  Proof.
    unfold rename_exit_row_work.
    eapply Nat.le_trans; [apply build_sum_bound with (amount := placement_work p)|].
    - intros target Hin.
      pose proof (rename_placement_rows_sum p [target]
        ltac:(constructor; [intro Hnone; contradiction|constructor])) as Hrow.
      cbn [build_sum fold_right] in Hrow; lia.
    - pose proof (build_exit_target_count (term _ _ _ body)); nia.
  Qed.

  (** The cached body budget absorbs all rows of a continuing successful exit. *)
  Lemma rename_success_rows_paid p bodies b inherited tasks output envs fresh body names
      cs final final_names next ending :
    rename_runtime p
      (RenameState O.K O.G bodies ((b, inherited) :: tasks) output envs fresh) ->
    trie_get b bodies = Some body -> rename_entry_names p b inherited = Some names ->
    rename_code (code _ _ _ body) (val_index names) names fresh =
      Some (cs, final, final_names, next) ->
    rename_exit (term _ _ _ body) (placement p) final = Some ending ->
    rename_exit_row_work p body <= 2 * rename_body_work p b.
  Proof.
    intros Hruntime Hbody Hnames Hcode Hexit.
    pose proof (rename_success_rows _ _ _ _ _ _ _ _ _ Hcode Hexit) as Hrows.
    pose proof (rename_active_names_length _ _ _ _ _ _ _ _ _ _
      Hruntime Hbody Hnames) as Hlength.
    pose proof (proj1 (proj1 (proj2 (proj1 (proj1 Hruntime))) b body Hbody)) as Hsource.
    unfold rename_body_work; rewrite Hsource; unfold build_core_size; lia.
  Qed.

  (** Every emitted body keeps a source identifier and no source identifier is repeated. *)
  Lemma rename_emitted_inventory p st :
    rename_info p (placement p) (L.live_in p) st ->
    length (renamed_blocks _ _ st) <= length (blocks _ _ _ p) /\
    forall b body, In (b, body) (renamed_blocks _ _ st) -> Pos.size_nat b <= function_width p.
  Proof.
    intros [Hcache Hsyntax].
    assert (Hsource : forall b body, In (b, body) (renamed_blocks _ _ st) ->
        exists original, lookup b (blocks _ _ _ p) = Some original).
    { intros b body Hin; destruct (proj1 Hsyntax b body Hin) as [original [Hlookup Hrest]].
      now exists original. }
    split.
    - rewrite <- (length_map fst (renamed_blocks _ _ st)),
        <- (length_map fst (blocks _ _ _ p)).
      apply NoDup_incl_length; [exact (proj1 Hcache)|].
      intros b Hin; apply in_map_iff in Hin as [[a body] [Heq Hin]]; cbn [fst] in Heq; subst a.
      destruct (Hsource b body Hin) as [original Hlookup]; apply val_lookup_in in Hlookup.
      apply in_map with (f := fst) in Hlookup; exact Hlookup.
    - intros b body Hin; destruct (Hsource b body Hin) as [original Hlookup].
      exact (source_lookup_width p b original Hlookup).
  Qed.

  (** Final materialization and indexing scan only the source block inventory. *)
  Lemma rename_finish_time p bodies output envs fresh :
    rename_info p (placement p) (L.live_in p)
      (RenameState O.K O.G bodies [] output envs fresh) ->
    (T_rename_step_indexed p (dom_tree p) (placement p) (val_index (L.live_in p))
      (val_index (map (fun x => (x, build_input_name x)) (inputs _ _ _ p))) (L.live_in p)
      (RenameState O.K O.G bodies [] output envs fresh) <=
      64 * (PTrieT.c_trie + 1) *
        N.of_nat (function_size p + 1) * N.of_nat (rename_value_width p + 1))%N.
  Proof.
    intro Hinfo; destruct (rename_emitted_inventory _ _ Hinfo) as [Hcount Hwidth].
    cbn [renamed_blocks] in Hcount, Hwidth.
    pose proof (build_function_decompose p) as Hsize.
    set (unit := ((PTrieT.c_trie + 1) *
      (N.of_nat (function_size p + 1) * N.of_nat (function_width p + 1)))%N).
    assert (Hunit : (1 <= unit)%N) by (unfold unit; nia).
    assert (Hindex : (T_val_index output <= 4 * unit)%N).
    { eapply build_component_budget with (coefficient := (PTrieT.c_trie + 2)%N)
        (extra := 1%N) (count := length output).
      - apply val_index_time; exact Hwidth.
      - lia.
      - lia.
      - lia.
      - lia. }
    assert (Hmaterialize : (T_build_materialize (blocks _ _ _ p) (val_index output) <=
        8 * unit)%N).
    { eapply build_component_budget with (coefficient := 8%N) (extra := 0%N)
        (count := length (blocks _ _ _ p) + 1).
      - rewrite N.add_0_r; apply build_materialize_time.
        intros b body Hin; eapply val_block_width; exact Hin.
      - lia.
      - lia.
      - lia.
      - lia. }
    assert (Hinputs : (ListDef.T_map build_input_name (fun x => T_build_input_name x)
      (inputs _ _ _ p) <= 4 * unit)%N).
    { eapply build_unscaled_budget with (coefficient := 3%N) (extra := 1%N)
        (count := length (inputs _ _ _ p)).
      - apply build_input_list_time.
      - lia.
      - lia.
      - lia.
      - lia. }
    eapply N.le_trans with (m := (64 * unit)%N).
    - time_unfold T_rename_step_indexed.
      destruct (build_materialize (blocks _ _ _ p) (val_index output));
        build_projection_clocks; lia.
    - unfold unit; rewrite <- N.mul_assoc, <- N.mul_assoc.
      apply N.mul_le_mono_l, N.mul_le_mono_l, N.mul_le_mono_l, time_of_nat_le.
      unfold rename_value_width; lia.
  Qed.

  (** A task whose body has already been emitted pays only for its cache lookup. *)
  Lemma rename_skip_time p bodies b inherited tasks output envs fresh :
    rename_task_budget p
      (RenameState O.K O.G bodies ((b, inherited) :: tasks) output envs fresh) ->
    trie_get b bodies = None ->
    (T_rename_step_indexed p (dom_tree p) (placement p) (val_index (L.live_in p))
      (val_index (map (fun x => (x, build_input_name x)) (inputs _ _ _ p))) (L.live_in p)
      (RenameState O.K O.G bodies ((b, inherited) :: tasks) output envs fresh) <=
      4 * N.of_nat (function_width p + 1))%N.
  Proof.
    intros Htasks Hbody; pose proof (proj1 (Htasks b inherited (or_introl eq_refl))) as Hb.
    time_unfold T_rename_step_indexed; rewrite Hbody, PTrieT.trie_get_clock.
    build_projection_clocks; nia.
  Qed.

  (** The common bit unit dominates every fixed primitive coefficient in cached renaming. *)
  Definition rename_clock_common : N := (PTrieT.c_trie + c_glue + 1)%N.

  (** One active cached body is charged before successful-edge domain refinement. *)
  Lemma rename_active_time p bodies b inherited tasks output envs fresh body :
    D.check (graph p) (entry _ _ _ p) (fst (dom_result p)) (snd (dom_result p)) = true ->
    rename_runtime p
      (RenameState O.K O.G bodies ((b, inherited) :: tasks) output envs fresh) ->
    trie_get b bodies = Some body ->
    (T_rename_step_indexed p (dom_tree p) (placement p) (val_index (L.live_in p))
      (val_index (map (fun x => (x, build_input_name x)) (inputs _ _ _ p))) (L.live_in p)
      (RenameState O.K O.G bodies ((b, inherited) :: tasks) output envs fresh) <=
      4096 * (rename_clock_common *
        (N.of_nat (rename_body_work p b + rename_exit_row_work p body + 1) *
          N.of_nat (rename_value_width p + 1))))%N.
  Proof.
    intros Hchecked Hruntime Hbody.
    pose proof Hruntime as [Hinfo [Hwidth Htasks]].
    pose proof (proj1 (proj1 (proj2 (proj1 Hinfo)) b body Hbody)) as Hsource.
    destruct (Htasks b inherited (or_introl eq_refl)) as [Hb Hinherited_length].
    pose proof (proj2 (proj2 Hwidth) b inherited body (or_introl eq_refl) Hsource)
      as Hinherited_width.
    set (w := rename_value_width p).
    set (total := rename_body_work p b + rename_exit_row_work p body + 1).
    set (budget := (rename_clock_common * (N.of_nat total * N.of_nat (w + 1)))%N).
    assert (Hwidth_source : function_width p <= w) by (unfold w, rename_value_width; lia).
    assert (Hb_width : Pos.size_nat b <= w) by lia.
    assert (Htotal : 1 <= total) by (unfold total; lia).
    assert (Hwidth_positive : (1 <= N.of_nat (w + 1))%N) by lia.
    assert (Hbudget : (1 <= budget)%N).
    { unfold budget, rename_clock_common; clear - Htotal Hwidth_positive; nia. }
    assert (Hwork : 1 + build_core_size body +
      (if Pos.eqb b (entry _ _ _ p) then length (inputs _ _ _ p) else 0) +
      length (index_row (val_index (L.live_in p)) b) +
      length (index_row (placement p) b) +
      build_sum (rename_child_work p) (children (dom_tree p) b) = rename_body_work p b).
    { unfold rename_body_work; now rewrite Hsource. }
    assert (Hphis_width : forall x, In x (index_row (placement p) b) -> Pos.size_nat x <= w).
    { intros x Hin; pose proof (placement_row_width p b x Hin); lia. }
    assert (Hlive_width : forall x, In x (index_row (val_index (L.live_in p)) b) ->
        Pos.size_nat x <= w).
    { intros x Hin; pose proof (live_row_width p b x Hin); lia. }
    assert (Hkids_width : forall child, In child (children (dom_tree p) b) ->
        Pos.size_nat child <= w).
    { intros child Hin; pose proof (rename_tree_children_width p b child Hchecked Hin); lia. }
    assert (Hget : (T_trie_get b bodies <= 3 * budget)%N).
    { eapply build_component_budget with (coefficient := 3%N) (extra := 0%N) (count := 1);
        try exact Htotal; try exact Hwidth_positive; try (unfold rename_clock_common; lia).
      rewrite N.add_0_r; exact (build_lookup_time bodies b w Hb_width). }
    assert (Hrow : (T_index_row (placement p) b <= 3 * budget)%N).
    { eapply build_component_budget with (coefficient := 3%N) (extra := 0%N) (count := 1);
        try exact Htotal; try exact Hwidth_positive; try (unfold rename_clock_common; lia).
      rewrite N.add_0_r; exact (val_row_time (placement p) b w Hb_width). }
    assert (Hlive_row : (T_index_row (val_index (L.live_in p)) b <= 3 * budget)%N).
    { eapply build_component_budget with (coefficient := 3%N) (extra := 0%N) (count := 1);
        try exact Htotal; try exact Hwidth_positive; try (unfold rename_clock_common; lia).
      rewrite N.add_0_r; exact (val_row_time (val_index (L.live_in p)) b w Hb_width). }
    assert (Hset : (T_val_set (index_row (placement p) b) <= 4 * budget)%N).
    { eapply build_component_budget with (coefficient := (PTrieT.c_trie + 2)%N)
        (extra := 1%N) (count := length (index_row (placement p) b));
        try exact Htotal; try exact Hwidth_positive; try (unfold total; lia);
        try (unfold rename_clock_common; lia).
      exact (val_set_time _ _ Hphis_width). }
    assert (Hinherited : (T_val_index inherited <= 4 * budget)%N).
    { eapply build_component_budget with (coefficient := (PTrieT.c_trie + 2)%N)
        (extra := 1%N) (count := length inherited);
        try exact Htotal; try exact Hwidth_positive; try (unfold total; lia);
        try (unfold rename_clock_common; lia).
      apply val_index_time; intros x y Hin; exact (proj1 (Hinherited_width x y Hin)). }
    assert (Hproject : (T_build_project b (val_set (index_row (placement p) b))
      (index_row (val_index (L.live_in p)) b) (val_index inherited)
      (val_index (map (fun x => (x, build_input_name x)) (inputs _ _ _ p))) <=
      16 * budget)%N).
    { eapply build_component_budget with (coefficient := (16 * (c_glue + 1))%N)
        (extra := 0%N) (count := length (index_row (val_index (L.live_in p)) b) + 1);
        try exact Htotal; try exact Hwidth_positive; try (unfold total; lia);
        try (unfold rename_clock_common; lia).
      rewrite N.add_0_r; apply build_project_time; assumption. }
    assert (Hcompare : (Pos.T_eqb b (entry _ _ _ p) <= budget)%N).
    { pose proof (Pos.T_eqb_le b (entry _ _ _ p)) as Hcompare.
      unfold budget, rename_clock_common; clear - Hcompare Hb_width Htotal; nia. }
    time_unfold T_rename_step_indexed; cbn beta iota zeta; rewrite Hbody.
    fold (rename_entry_names p b inherited).
    destruct (params _ _ _ body) as [|first rest] eqn:Hparams;
      [|destruct (Pos.eqb b (entry _ _ _ p)); build_projection_clocks; lia].
    destruct (rename_entry_names p b inherited) as [names|] eqn:Hnames;
      [|destruct (Pos.eqb b (entry _ _ _ p)); build_projection_clocks; lia].
    pose proof (rename_active_names_width _ _ _ _ _ _ _ _ _ _ Hruntime Hbody Hnames)
      as Hnames_width.
    pose proof (rename_active_names_length _ _ _ _ _ _ _ _ _ _ Hruntime Hbody Hnames)
      as Hnames_length.
    assert (Hindex_names : (T_val_index names <= 4 * budget)%N).
    { eapply build_component_budget with (coefficient := (PTrieT.c_trie + 2)%N)
        (extra := 1%N) (count := length names);
        try exact Htotal; try exact Hwidth_positive; try (unfold total; lia);
        try (unfold rename_clock_common; lia).
      apply val_index_time; intros x y Hin; exact (proj1 (Hnames_width x y Hin)). }
    assert (Hcode : (T_rename_code (code _ _ _ body) (val_index names) names fresh <=
        64 * budget)%N).
    { eapply build_component_budget with (coefficient := (64 * (PTrieT.c_trie + 1))%N)
        (extra := 0%N) (count := build_core_size body + 1);
        try exact Htotal; try exact Hwidth_positive; try (unfold total; lia);
        try (unfold rename_clock_common; lia).
      rewrite N.add_0_r; exact (rename_cached_code_time p
        (RenameState O.K O.G bodies ((b, inherited) :: tasks) output envs fresh)
        b body names (proj1 Hinfo) Hbody). }
    destruct (rename_code (code _ _ _ body) (val_index names) names fresh)
      as [[[[cs final] final_names] next]|] eqn:Hcode_run;
      [|destruct (Pos.eqb b (entry _ _ _ p)); build_projection_clocks; lia].
    assert (Hexit : (T_rename_exit (term _ _ _ body) (placement p) final <=
        64 * budget)%N).
    { eapply build_component_budget with (coefficient := 64%N) (extra := 0%N)
        (count := build_exit_base (term _ _ _ body) + rename_exit_row_work p body + 1);
        try exact Htotal; try exact Hwidth_positive;
        try (unfold total; unfold build_core_size in Hwork; lia);
        try (unfold rename_clock_common; lia).
      rewrite N.add_0_r; apply rename_exit_time.
      - intros target Hin; pose proof (val_target_width p b body target
          (val_lookup_in _ _ _ Hsource) Hin); lia.
      - intros x Hin; pose proof (rename_source_exit_width p b body x Hsource Hin); lia.
      - intros target x Hin; pose proof (placement_row_width p target x Hin); lia. }
    destruct (rename_exit (term _ _ _ body) (placement p) final) as [ending|] eqn:Hexit_run;
      [|destruct (Pos.eqb b (entry _ _ _ p)); build_projection_clocks; lia].
    assert (Hchildren : (T_children (dom_tree p) b <= 4 * budget)%N).
    { eapply build_component_budget with (coefficient := 4%N) (extra := 0%N) (count := 1);
        try exact Htotal; try exact Hwidth_positive; try (unfold rename_clock_common; lia).
      rewrite N.add_0_r; apply build_children_time; exact Hb_width. }
    assert (Hchildren_scan : (T_rename_children (children (dom_tree p) b) (placement p)
      (val_index (L.live_in p)) final
      (val_index (map (fun x => (x, build_input_name x)) (inputs _ _ _ p))) <=
      64 * budget)%N).
    { eapply build_component_budget with
        (coefficient := (64 * (PTrieT.c_trie + c_glue + 1))%N) (extra := 0%N)
        (count := build_sum (rename_child_work p) (children (dom_tree p) b) + 1);
        try exact Htotal; try exact Hwidth_positive; try (unfold total; lia);
        try (unfold rename_clock_common; lia).
      rewrite N.add_0_r; apply rename_children_time; assumption. }
    destruct (rename_children (children (dom_tree p) b) (placement p)
      (val_index (L.live_in p)) final
      (val_index (map (fun x => (x, build_input_name x)) (inputs _ _ _ p))))
      as [kids|] eqn:Hkids;
      [|destruct (Pos.eqb b (entry _ _ _ p)); build_projection_clocks; lia].
    assert (Hremove : (PTrieCode.T_remove b bodies <= budget)%N).
    { pose proof (PTrieT.T_remove_le _ b bodies) as Hremove.
      unfold budget, rename_clock_common; clear - Hremove Hb_width Htotal; nia. }
    assert (Hkids_count : length kids <= build_sum (rename_child_work p) (children (dom_tree p) b)).
    { pose proof (rename_children_keys _ _ _ _ _ _ Hkids) as Hkeys.
      apply f_equal with (f := @length positive) in Hkeys; rewrite length_map in Hkeys.
      rewrite Hkeys; unfold build_sum; apply val_sum_ge_length.
      intros child Hin; unfold rename_child_work; lia. }
    assert (Happend : (Datatypes.T_app kids tasks <= 2 * budget)%N).
    { eapply build_unscaled_budget with (coefficient := 1%N) (extra := 1%N)
        (count := length kids).
      - rewrite N.mul_1_l; apply Datatypes.T_app_le.
      - unfold total; lia.
      - exact Htotal.
      - exact Hwidth_positive.
      - unfold rename_clock_common; lia. }
    assert (Hphi_names : (ListDef.T_map (build_phi_name b) (fun x => T_build_phi_name b x)
      (index_row (placement p) b) <= 4 * budget)%N).
    { eapply build_component_budget with (coefficient := (c_glue + 4)%N) (extra := 0%N)
        (count := length (index_row (placement p) b) + 1);
        try exact Htotal; try exact Hwidth_positive; try (unfold total; lia);
        try (unfold rename_clock_common; lia).
      rewrite N.add_0_r; apply build_phi_list_time; exact Hb_width. }
    destruct (Pos.eqb b (entry _ _ _ p)); build_projection_clocks; lia.
  Qed.

  (** The clock used by the actual loop reads indexes that were constructed once. *)
  Definition rename_cached_clock (p : P.t) st : N :=
    T_rename_step_indexed p (dom_tree p) (placement p) (val_index (L.live_in p))
      (val_index (map (fun x => (x, build_input_name x)) (inputs _ _ _ p))) (L.live_in p) st.

  (** Remaining cached source bodies hold the amortized continuation credit. *)
  Definition rename_remaining (p : P.t) (st : rename_state O.K O.G) : nat :=
    build_remaining (rename_body_work p) (map fst (blocks _ _ _ p)) (rename_bodies _ _ st).

  (** The private runtime budget includes the requested liveness output. *)
  Definition rename_total_work (p : P.t) : nat :=
    function_size p + L.live_size p + placement_work p + 1.

  (** Four active-body allowances absorb successful outgoing-row rewriting. *)
  Definition rename_runtime_scale (p : P.t) : N :=
    (16384 * rename_clock_common * N.of_nat (rename_value_width p + 1))%N.

  (** A successful exit turns the active-body bound into one cached-body charge. *)
  Lemma rename_active_charge p bodies b inherited tasks output envs fresh body names
      cs final final_names next ending :
    D.check (graph p) (entry _ _ _ p) (fst (dom_result p)) (snd (dom_result p)) = true ->
    rename_runtime p
      (RenameState O.K O.G bodies ((b, inherited) :: tasks) output envs fresh) ->
    trie_get b bodies = Some body -> rename_entry_names p b inherited = Some names ->
    rename_code (code _ _ _ body) (val_index names) names fresh =
      Some (cs, final, final_names, next) ->
    rename_exit (term _ _ _ body) (placement p) final = Some ending ->
    (rename_cached_clock p
      (RenameState O.K O.G bodies ((b, inherited) :: tasks) output envs fresh) <=
      rename_runtime_scale p * N.of_nat (rename_body_work p b + 1))%N.
  Proof.
    intros Hchecked Hruntime Hbody Hnames Hcode Hexit.
    pose proof (rename_success_rows_paid _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      Hruntime Hbody Hnames Hcode Hexit) as Hrows.
    eapply N.le_trans; [eapply rename_active_time; eassumption|].
    unfold rename_runtime_scale.
    replace (16384 * rename_clock_common * N.of_nat (rename_value_width p + 1) *
      N.of_nat (rename_body_work p b + 1))%N with
      (4096 * (rename_clock_common *
        (N.of_nat (4 * (rename_body_work p b + 1)) *
          N.of_nat (rename_value_width p + 1))))%N
      by (rewrite Nat2N.inj_mul; change (N.of_nat 4) with 4%N; ring).
    apply N.mul_le_mono_l, N.mul_le_mono_l, N.mul_le_mono_r.
    apply time_of_nat_le; lia.
  Qed.

  (** A continuing cached step spends one body's credit or one failed-lookup allowance. *)
  Lemma rename_continue_charge p st next : NoDup (map fst (blocks _ _ _ p)) ->
    D.check (graph p) (entry _ _ _ p) (fst (dom_result p)) (snd (dom_result p)) = true ->
    rename_runtime p st ->
    rename_step p (dom_tree p) (placement p) (L.live_in p) st = inl next ->
    (rename_cached_clock p st + rename_runtime_scale p * N.of_nat (rename_remaining p next) <=
      rename_runtime_scale p * N.of_nat (rename_remaining p st) + rename_runtime_scale p)%N.
  Proof.
    intros Hunique Hchecked Hruntime Hstep; destruct st as [bodies tasks output envs fresh].
    destruct tasks as [|[b inherited] tasks].
    - unfold rename_step in Hstep; cbn [rename_step_indexed] in Hstep.
      destruct (build_materialize (blocks _ _ _ p) (val_index output)); discriminate.
    - unfold rename_step in Hstep; cbn [rename_step_indexed] in Hstep.
      destruct (trie_get b bodies) as [body|] eqn:Hbody.
      + pose proof (proj1 (proj1 (proj2 (proj1 (proj1 Hruntime))) b body Hbody)) as Hsource.
        assert (Hin : In b (map fst (blocks _ _ _ p))).
        { apply val_lookup_in in Hsource; apply in_map with (f := fst) in Hsource; exact Hsource. }
        destruct (params _ _ _ body) as [|x rest]; [|discriminate].
        fold (rename_entry_names p b inherited) in Hstep.
        destruct (rename_entry_names p b inherited) as [names|] eqn:Hnames; [|discriminate].
        destruct (rename_code (code _ _ _ body) (val_index names) names fresh)
          as [[[[cs final] final_names] last]|] eqn:Hcode; [|discriminate].
        destruct (rename_exit (term _ _ _ body) (placement p) final) as [ending|] eqn:Hexit;
          [|discriminate].
        destruct (rename_children (children (dom_tree p) b) (placement p)
          (val_index (L.live_in p)) final
          (val_index (map (fun x => (x, build_input_name x)) (inputs _ _ _ p))))
          as [kids|] eqn:Hkids; [|discriminate].
        pose proof (rename_active_charge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          Hchecked Hruntime Hbody Hnames Hcode Hexit) as Hcharge.
        pose proof (build_remaining_remove (rename_body_work p) (map fst (blocks _ _ _ p))
          bodies b body Hunique Hin Hbody) as Hspent.
        inversion Hstep; subst next; unfold rename_remaining; cbn [rename_bodies].
        rewrite Hspent, Nat2N.inj_add; rewrite Nat2N.inj_add in Hcharge; nia.
      + pose proof (rename_skip_time _ _ _ _ _ _ _ _ (proj2 (proj2 Hruntime)) Hbody) as Hskip.
        inversion Hstep; subst next; unfold rename_remaining; cbn [rename_bodies].
        unfold rename_cached_clock in *; unfold rename_runtime_scale, rename_clock_common,
          rename_value_width; rewrite !Nat2N.inj_add, !Nat2N.inj_mul in *; nia.
  Qed.

  (** Every cached source body is bounded by the complete source/liveness/placement budget. *)
  Lemma rename_body_work_bound p st b body : NoDup (map fst (blocks _ _ _ p)) ->
    D.check (graph p) (entry _ _ _ p) (fst (dom_result p)) (snd (dom_result p)) = true ->
    rename_runtime p st -> trie_get b (rename_bodies _ _ st) = Some body ->
    rename_body_work p b <= 8 * rename_total_work p.
  Proof.
    intros Hunique Hchecked Hruntime Hbody.
    pose proof (proj1 (proj1 (proj2 (proj1 (proj1 Hruntime))) b body Hbody)) as Hsource.
    assert (Hin : In b (map fst (blocks _ _ _ p))).
    { apply val_lookup_in in Hsource; apply in_map with (f := fst) in Hsource; exact Hsource. }
    eapply Nat.le_trans; [apply build_sum_member; exact Hin|].
    exact (rename_body_work_total p Hunique Hchecked).
  Qed.

  (** One terminal failed attempt is charged once to the complete available row budget. *)
  Lemma rename_terminal_charge p st answer : NoDup (map fst (blocks _ _ _ p)) ->
    D.check (graph p) (entry _ _ _ p) (fst (dom_result p)) (snd (dom_result p)) = true ->
    rename_runtime p st ->
    rename_step p (dom_tree p) (placement p) (L.live_in p) st = inr answer ->
    (rename_cached_clock p st <=
      rename_runtime_scale p * N.of_nat (rename_remaining p st + 16 * rename_total_work p + 1))%N.
  Proof.
    intros Hunique Hchecked Hruntime Hstep; destruct st as [bodies tasks output envs fresh].
    destruct tasks as [|[b inherited] tasks].
    - pose proof (rename_finish_time _ _ _ _ _ (proj1 Hruntime)) as Hfinish.
      unfold rename_cached_clock; eapply N.le_trans; [exact Hfinish|].
      unfold rename_runtime_scale, rename_clock_common, rename_total_work.
      rewrite !Nat2N.inj_add, !Nat2N.inj_mul; nia.
    - destruct (trie_get b bodies) as [body|] eqn:Hbody.
      + pose proof (rename_body_work_bound p
          (RenameState O.K O.G bodies ((b, inherited) :: tasks) output envs fresh)
          b body Hunique Hchecked Hruntime Hbody) as Hwork.
        pose proof (rename_terminal_rows p body) as Hrows.
        eapply N.le_trans; [eapply rename_active_time; eassumption|].
        unfold rename_runtime_scale.
        replace (16384 * rename_clock_common * N.of_nat (rename_value_width p + 1) *
          N.of_nat (rename_remaining p
            (RenameState O.K O.G bodies ((b, inherited) :: tasks) output envs fresh) +
              16 * rename_total_work p + 1))%N with
          (4096 * (rename_clock_common *
            (N.of_nat (4 * (rename_remaining p
              (RenameState O.K O.G bodies ((b, inherited) :: tasks) output envs fresh) +
                16 * rename_total_work p + 1)) * N.of_nat (rename_value_width p + 1))))%N
          by (rewrite Nat2N.inj_mul; change (N.of_nat 4) with 4%N; ring).
        apply N.mul_le_mono_l, N.mul_le_mono_l, N.mul_le_mono_r.
        apply time_of_nat_le; unfold rename_total_work in *; lia.
      + unfold rename_step in Hstep; cbn [rename_step_indexed] in Hstep.
        rewrite Hbody in Hstep; discriminate.
  Qed.

  (** The initial cached-body credit fits the same total work budget. *)
  Lemma rename_remaining_initial p : NoDup (map fst (blocks _ _ _ p)) ->
    D.check (graph p) (entry _ _ _ p) (fst (dom_result p)) (snd (dom_result p)) = true ->
    rename_remaining p (rename_init p) <= 8 * rename_total_work p.
  Proof.
    intros Hunique Hchecked; unfold rename_remaining.
    eapply Nat.le_trans; [apply build_remaining_bound|].
    exact (rename_body_work_total p Hunique Hchecked).
  Qed.

  (** Cached loop fuel and body credit bound the complete loop, including failure. *)
  Lemma rename_cached_loop_time p : NoDup (map fst (blocks _ _ _ p)) ->
    D.check (graph p) (entry _ _ _ p) (fst (dom_result p)) (snd (dom_result p)) = true ->
    (T_loop_fuel (rename_step p (dom_tree p) (placement p) (L.live_in p))
      (rename_cached_clock p) (2 * length (blocks _ _ _ p) + 1) (rename_init p) <=
      1500000 * (rename_clock_common *
        (N.of_nat (rename_total_work p) * N.of_nat (function_width p + 1))))%N.
  Proof.
    intros Hunique Hchecked.
    pose proof (build_loop_budget
      (rename_step p (dom_tree p) (placement p) (L.live_in p)) (rename_cached_clock p)
      (rename_runtime p) (rename_remaining p) (rename_runtime_scale p) (16 * rename_total_work p)
      ltac:(intros st next Hinv Hstep; split;
        [eapply rename_runtime_step; eassumption|eapply rename_continue_charge; eassumption])
      ltac:(intros st answer Hinv Hstep; eapply rename_terminal_charge; eassumption)
      (2 * length (blocks _ _ _ p) + 1) (rename_init p) (rename_runtime_init p)) as Hloop.
    pose proof (rename_remaining_initial p Hunique Hchecked) as Hremaining.
    pose proof (build_function_decompose p) as Hsource.
    assert (Hfuel : 2 * length (blocks _ _ _ p) + 1 <= 3 * rename_total_work p).
    { unfold rename_total_work; lia. }
    assert (Htotal : 1 <= rename_total_work p) by (unfold rename_total_work; lia).
    set (unit := (rename_clock_common * N.of_nat (function_width p + 1))%N).
    assert (Hunit : (1 <= unit)%N) by (unfold unit, rename_clock_common; nia).
    assert (Hscale : rename_runtime_scale p = (49152 * unit)%N).
    { unfold rename_runtime_scale, unit, rename_value_width.
      rewrite !Nat2N.inj_add, !Nat2N.inj_mul. cbn [N.of_nat]; ring. }
    rewrite Hscale in Hloop.
    assert (Hfuel_N : (N.of_nat (2 * length (blocks _ _ _ p) + 1) <=
        3 * N.of_nat (rename_total_work p))%N).
    { change (N.of_nat (2 * length (blocks _ _ _ p) + 1) <=
        N.of_nat 3 * N.of_nat (rename_total_work p))%N.
      rewrite <- Nat2N.inj_mul; now apply time_of_nat_le. }
    assert (Hcredit_N : (N.of_nat (rename_remaining p (rename_init p) +
        16 * rename_total_work p) <= 24 * N.of_nat (rename_total_work p))%N).
    { change (N.of_nat (rename_remaining p (rename_init p) + 16 * rename_total_work p) <=
        N.of_nat 24 * N.of_nat (rename_total_work p))%N.
      rewrite <- Nat2N.inj_mul; apply time_of_nat_le; lia. }
    pose proof (N.mul_le_mono_l _ _ (49152 * unit + 1)%N Hfuel_N) as Hfuel_cost.
    pose proof (N.mul_le_mono_l _ _ (49152 * unit)%N Hcredit_N) as Hcredit_cost.
    replace (1500000 * (rename_clock_common *
      (N.of_nat (rename_total_work p) * N.of_nat (function_width p + 1))))%N with
      (1500000 * unit * N.of_nat (rename_total_work p))%N by (unfold unit; ring).
    nia.
  Qed.

  (** Preparing unary loop fuel is linear in the source block count. *)
  Lemma rename_fuel_time p :
    (T_blocks positive O.K O.G p + Datatypes.T_length (blocks _ _ _ p) +
      Nat.T_mul 2 (length (blocks _ _ _ p)) +
      Nat.T_add (2 * length (blocks _ _ _ p)) 1 <=
      16 * N.of_nat (length (blocks _ _ _ p) + 1))%N.
  Proof.
    pose proof (Datatypes.T_length_le (blocks _ _ _ p)) as Hlength.
    pose proof (Nat.T_mul_le 2 (length (blocks _ _ _ p))) as Hmul.
    pose proof (Nat.T_add_le (2 * length (blocks _ _ _ p)) 1) as Hadd.
    build_projection_clocks; rewrite !Nat2N.inj_add, !Nat2N.inj_mul in *; nia.
  Qed.

  (** The cached live-row index is constructed once from the supplied liveness result. *)
  Lemma rename_live_index_time p :
    (T_val_index (L.live_in p) <= 4 * (rename_clock_common *
      (N.of_nat (rename_total_work p) * N.of_nat (function_width p + 1))))%N.
  Proof.
    pose proof (L.live_in_size p) as Hlive.
    unfold L.rows_size in Hlive.
    pose proof (val_rows_length (L.live_in p)) as Hrows.
    pose proof (build_function_decompose p) as Hsource.
    assert (Hcount : length (L.live_in p) <= rename_total_work p).
    { unfold rename_total_work; lia. }
    eapply build_component_budget with (coefficient := (PTrieT.c_trie + 2)%N)
      (extra := 1%N) (count := length (L.live_in p));
      try exact Hcount; try (unfold rename_total_work; lia);
      try (unfold rename_clock_common; lia).
    apply val_index_time; intros b row Hin.
    destruct (L.live_in_ids p (b, row) Hin) as [Hnode Hvars].
    apply PB.block_bits_le; now left.
  Qed.

  (** The cached original-input index is constructed once at source-key width. *)
  Lemma rename_input_index_time p :
    (T_val_index (map (fun x => (x, build_input_name x)) (inputs _ _ _ p)) <=
      4 * (rename_clock_common *
        (N.of_nat (rename_total_work p) * N.of_nat (function_width p + 1))))%N.
  Proof.
    pose proof (build_function_decompose p) as Hsource.
    eapply build_component_budget with (coefficient := (PTrieT.c_trie + 2)%N)
      (extra := 1%N)
      (count := length (map (fun x => (x, build_input_name x)) (inputs _ _ _ p)));
      try (rewrite length_map; unfold rename_total_work; lia);
      try (unfold rename_total_work; lia); try (unfold rename_clock_common; lia).
    apply val_index_time; intros x y Hin.
    apply in_map_iff in Hin as [a [Heq Hin]]; inversion Heq; subst x y.
    now apply val_input_width.
  Qed.

  (** The complete private cached-renamer coefficient includes fixed setup and loop costs. *)
  Definition rename_cached_coefficient : N := (2097152 * rename_clock_common)%N.

  (** The actual cached renamer uses source syntax, liveness and placement work even on failure. *)
  Lemma rename_cached_time p : NoDup (map fst (blocks _ _ _ p)) ->
    D.check (graph p) (entry _ _ _ p) (fst (dom_result p)) (snd (dom_result p)) = true ->
    (T_rename p (dom_tree p) (placement p) (L.live_in p) <=
      rename_cached_coefficient *
        N.of_nat (function_size p + L.live_size p + placement_work p + 1) *
        N.of_nat (function_width p + 1))%N.
  Proof.
    intros Hunique Hchecked.
    pose proof (rename_live_index_time p) as Hlive.
    pose proof (rename_input_index_time p) as Hinputs.
    pose proof (rename_cached_loop_time p Hunique Hchecked) as Hloop.
    pose proof (build_function_decompose p) as Hsource.
    set (budget := (rename_clock_common *
      (N.of_nat (rename_total_work p) * N.of_nat (function_width p + 1)))%N).
    assert (Hunit : (1 <= budget)%N).
    { unfold budget, rename_clock_common, rename_total_work; nia. }
    assert (Hinput_map : (ListDef.T_map (fun x => (x, build_input_name x))
      (fun x => 1 + T_build_input_name x)%N (inputs _ _ _ p) <= 5 * budget)%N).
    { eapply build_unscaled_budget with (coefficient := 4%N) (extra := 1%N)
        (count := length (inputs _ _ _ p));
        try (unfold rename_total_work; lia); try (unfold rename_clock_common; lia).
      apply build_input_pairs_time. }
    assert (Hfuel : (T_blocks positive O.K O.G p + Datatypes.T_length (blocks _ _ _ p) +
      Nat.T_mul 2 (length (blocks _ _ _ p)) +
      Nat.T_add (2 * length (blocks _ _ _ p)) 1 <= 16 * budget)%N).
    { eapply build_unscaled_budget with (coefficient := 16%N) (extra := 0%N)
        (count := length (blocks _ _ _ p) + 1);
        try (unfold rename_total_work; lia); try (unfold rename_clock_common; lia).
      rewrite N.add_0_r; apply rename_fuel_time. }
    assert (Hinit : (T_rename_init p <= 64 * budget)%N).
    { eapply build_component_budget with (coefficient := (64 * (PTrieT.c_trie + 1))%N)
        (extra := 0%N) (count := function_size p + 1);
        try (unfold rename_total_work; lia); try (unfold rename_clock_common; lia).
      rewrite N.add_0_r; apply rename_initial_time. }
    fold budget in Hlive, Hinputs, Hloop.
    time_unfold T_rename; build_projection_clocks.
    fold (rename_cached_clock p).
    change ((1 + (T_val_index (L.live_in p) +
      (1 + ListDef.T_map (fun x => (x, build_input_name x))
        (fun x => 1 + T_build_input_name x)%N (inputs _ _ _ p) +
      T_val_index (map (fun x => (x, build_input_name x)) (inputs _ _ _ p)) +
      (1 + Datatypes.T_length (blocks _ _ _ p) + Nat.T_mul 2 (length (blocks _ _ _ p)) +
      Nat.T_add (2 * length (blocks _ _ _ p)) 1 + T_rename_init p +
      T_loop_fuel (rename_step p (dom_tree p) (placement p) (L.live_in p))
        (rename_cached_clock p) (2 * length (blocks _ _ _ p) + 1) (rename_init p)))) <=
      rename_cached_coefficient * N.of_nat (rename_total_work p) *
        N.of_nat (function_width p + 1))%N).
    replace (rename_cached_coefficient * N.of_nat (rename_total_work p) *
      N.of_nat (function_width p + 1))%N with (2097152 * budget)%N
      by (unfold rename_cached_coefficient, budget; ring).
    cbn [T_blocks] in Hfuel; clearbody budget; lia.
  Qed.

  Module Clock := ValidateT O K G P Q R BE BC S DG D B.

  Lemma budget_graph_width p : graph_width (base (graph p)) <= function_width p.
  Proof.
    exact (Clock.ssa_graph_width p).
  Qed.
  (** Each source block occurs in the graph when source identifiers are distinct. *)
  Lemma budget_graph_count p : NoDup (map fst (blocks _ _ _ p)) ->
    graph_n (base (graph p)) = length (blocks _ _ _ p).
  Proof.
    intro Hunique. rewrite Clock.ssa_graph_nodes.
    apply Nat.le_antisymm; [apply PB.block_nodes_le|].
    assert (Hlength : length (map fst (blocks _ _ _ p)) <=
      length (BC.nodes (R.prepare p))).
    { apply NoDup_incl_length; [exact Hunique|].
      rewrite B.nodes_agree. intros b Hin. now apply val_first_blocks_ids. }
    now rewrite length_map in Hlength.
  Qed.

  (** The published dominator budget contains the unweighted graph inventory. *)
  Lemma budget_dom_lower p :
    graph_n (base (graph p)) + graph_e (base (graph p)) + 1 <= dom_work p.
  Proof.
    unfold dom_work; nia.
  Qed.
  Lemma budget_size_lower p : 1 <= build_work p /\ function_size p + 1 <= build_work p.
  Proof.
    unfold build_work; lia.
  Qed.
  Lemma budget_graph_inventory p :
    function_size p + graph_n (base (graph p)) + graph_e (base (graph p)) + 1 <=
      build_work p.
  Proof.
    rewrite Clock.ssa_graph_nodes, Clock.ssa_graph_edges. unfold build_work; lia.
  Qed.
  Lemma budget_graph_clock p :
    (T_graph p <= Clock.ssa_graph_coefficient * N.of_nat (build_work p) *
      N.of_nat (function_width p + 1))%N.
  Proof.
    eapply N.le_trans; [exact (Clock.ssa_graph_clock p)|].
    apply N.mul_le_mono_r; apply N.mul_le_mono_l.
    apply time_of_nat_le, budget_graph_inventory.
  Qed.

  Lemma budget_prepare_clock p :
    (R.T_prepare p <= R.c_prepare * N.of_nat (build_work p) *
      N.of_nat (function_width p + 1))%N.
  Proof.
    eapply N.le_trans; [apply R.T_prepare_le|].
    apply N.mul_le_mono_r; apply N.mul_le_mono_l.
    apply time_of_nat_le. exact (proj2 (budget_size_lower p)).
  Qed.

  Lemma budget_dom_build_clock p :
    (D.T_build (graph p) (entry _ _ _ p) <= D.c_dom * N.of_nat (build_work p) *
      N.of_nat (function_width p + 1))%N.
  Proof.
    eapply N.le_trans; [apply D.T_build_le, Clock.ssa_graph_prepared|].
    apply N.mul_le_mono.
    - rewrite <- N.mul_assoc, <- Nat2N.inj_mul.
      apply N.mul_le_mono_l; apply time_of_nat_le.
      change (dom_work p <= build_work p). unfold build_work; lia.
    - apply time_of_nat_le. pose proof (budget_graph_width p); lia.
  Qed.

  Lemma budget_dom_check_clock p m order :
    (D.T_check (graph p) (entry _ _ _ p) m order <= D.c_dom * N.of_nat (build_work p) *
      N.of_nat (function_width p + 1))%N.
  Proof.
    eapply N.le_trans; [apply D.T_check_le|]. apply N.mul_le_mono.
    - apply N.mul_le_mono_l; apply time_of_nat_le.
      pose proof (budget_dom_lower p). unfold build_work; lia.
    - apply time_of_nat_le. pose proof (budget_graph_width p); lia.
  Qed.

  Lemma budget_dom_tree_clock p m order :
    D.check (graph p) (entry _ _ _ p) m order = true ->
    (D.T_tree (graph p) (entry _ _ _ p) m order <= D.c_dom * N.of_nat (build_work p) *
      N.of_nat (function_width p + 1))%N.
  Proof.
    intro Hcheck. eapply N.le_trans; [apply D.T_tree_le; exact Hcheck|].
    apply N.mul_le_mono.
    - apply N.mul_le_mono_l; apply time_of_nat_le.
      pose proof (budget_dom_lower p). unfold build_work; lia.
    - apply time_of_nat_le. pose proof (budget_graph_width p); lia.
  Qed.

  Lemma budget_frontier_clock p :
    D.check (graph p) (entry _ _ _ p) (fst (dom_result p)) (snd (dom_result p)) = true ->
    (F.T_df (graph p) (dom_tree p) <= F.c_frontier * N.of_nat (build_work p) *
      N.of_nat (function_width p + 1))%N.
  Proof.
    intro Hcheck. eapply N.le_trans.
    - eapply F.T_df_le; [apply F1_graph_wf|apply Clock.ssa_graph_prepared|].
      apply D.tree_exact; exact Hcheck.
    - apply N.mul_le_mono.
      + apply N.mul_le_mono_l; apply time_of_nat_le.
        rewrite Clock.ssa_graph_nodes, Clock.ssa_graph_edges.
        unfold build_work, df_size; lia.
      + apply time_of_nat_le. pose proof (budget_graph_width p); lia.
  Qed.

  (** Successful renaming leaves the dominator node count unchanged. *)
  Lemma budget_candidate_nodes p s c : produce p = Some (s, c) ->
    graph_n (base (graph s)) = graph_n (base (graph p)).
  Proof.
    intro Hproduce. pose proof (produce_unique _ _ _ Hproduce) as Hunique.
    destruct (produce_size_checked _ _ _ Hproduce) as [Hids _].
    rewrite !budget_graph_count by (try rewrite Hids; exact Hunique).
    apply f_equal with (f := @length positive) in Hids.
    now rewrite !length_map in Hids.
  Qed.

  Lemma budget_candidate_dom p s c : produce p = Some (s, c) ->
    (Va.dom_bound s <= 3 * N.of_nat (dom_work p))%N.
  Proof.
    intro Hproduce. pose proof (PB.block_edges_le s) as Hedges.
    rewrite <- Clock.ssa_graph_nodes, <- Clock.ssa_graph_edges in Hedges.
    change (graph_e (base (graph s)) <= 2 * graph_n (base (graph s))) in Hedges.
    pose proof (budget_candidate_nodes _ _ _ Hproduce) as Hnodes.
    change (N.of_nat ((graph_n (base (graph s)) + graph_e (base (graph s)) + 1) *
      (Nat.log2 (graph_n (base (graph s))) + 1)) <= 3 * N.of_nat (dom_work p))%N.
    change (N.of_nat ((graph_n (base (graph s)) + graph_e (base (graph s)) + 1) *
      (Nat.log2 (graph_n (base (graph s))) + 1)) <= N.of_nat 3 * N.of_nat (dom_work p))%N.
    rewrite <- Nat2N.inj_mul. apply time_of_nat_le. rewrite Hnodes in *.
    unfold dom_work. nia.
  Qed.

  Lemma budget_candidate_sizes p s c : produce p = Some (s, c) ->
    function_size p + function_size s + cert_size c + 1 <= 17 * build_work p /\
    Va.check_width p s c + 1 <= 17 * (function_width p + 1) /\
    function_size s + 1 <= 17 * build_work p /\
    function_width s + 1 <= 17 * (function_width p + 1).
  Proof.
    intro Hproduce. destruct (produce_size_checked _ _ _ Hproduce) as [_ [Hsize Hwidth]].
    assert (Hs : function_size s + cert_size c <= 16 * build_work p).
    { assert (HsN : (N.of_nat (function_size s + cert_size c) <=
        N.of_nat (16 * build_work p))%N) by (rewrite Nat2N.inj_mul; exact Hsize).
      lia. }
    assert (Hw : function_width s + vertex_width (cert_ids c) <= 16 * (function_width p + 1)).
    { assert (HwN : (N.of_nat (function_width s + vertex_width (cert_ids c)) <=
        N.of_nat (16 * (function_width p + 1)))%N)
        by (rewrite Nat2N.inj_mul; exact Hwidth). lia. }
    pose proof (budget_size_lower p) as Hlower. unfold Va.check_width; lia.
  Qed.

  Lemma budget_translation_clock p s c : produce p = Some (s, c) ->
    (Va.T_check p s c <= 512 * Va.c_val * N.of_nat (build_work p) *
      N.of_nat (function_width p + 1) + Va.c_val * N.of_nat (Va.op_bits p + 1))%N.
  Proof.
    intro Hproduce. destruct (budget_candidate_sizes _ _ _ Hproduce) as [Hs [Hw _]].
    eapply N.le_trans; [apply Va.T_check_le|]. apply N.add_le_mono_r.
    eapply N.le_trans with (m := (Va.c_val * N.of_nat (17 * build_work p) *
      N.of_nat (17 * (function_width p + 1)))%N).
    - apply N.mul_le_mono; [apply N.mul_le_mono_l|]; now apply time_of_nat_le.
    - rewrite !Nat2N.inj_mul.
      change (N.of_nat 17) with 17%N.
      replace (Va.c_val * (17 * N.of_nat (build_work p)) *
        (17 * N.of_nat (function_width p + 1)))%N with
        (289 * (Va.c_val * N.of_nat (build_work p) * N.of_nat (function_width p + 1)))%N
        by ring.
      replace (512 * Va.c_val * N.of_nat (build_work p) *
        N.of_nat (function_width p + 1))%N with
        (512 * (Va.c_val * N.of_nat (build_work p) * N.of_nat (function_width p + 1)))%N
        by ring.
      apply N.mul_le_mono_r; lia.
  Qed.

  Lemma budget_candidate_ssa_clock p s c : produce p = Some (s, c) ->
    (Va.T_check_ssa s <= 512 * Va.c_val * N.of_nat (build_work p) *
      N.of_nat (function_width p + 1))%N.
  Proof.
    intro Hproduce. destruct (budget_candidate_sizes _ _ _ Hproduce) as [_ [_ [Hs Hw]]].
    pose proof (budget_candidate_dom _ _ _ Hproduce) as Hd.
    assert (Hdom : (N.of_nat (dom_work p) <= N.of_nat (build_work p))%N)
      by (apply time_of_nat_le; unfold build_work; lia).
    assert (Htotal : (N.of_nat (function_size s + 1) + Va.dom_bound s <=
      20 * N.of_nat (build_work p))%N).
    { apply time_of_nat_le in Hs. rewrite Nat2N.inj_mul in Hs.
      change (N.of_nat 17) with 17%N in Hs. lia. }
    eapply N.le_trans; [apply Va.T_check_ssa_le|].
    eapply N.le_trans with (m := (Va.c_val * (20 * N.of_nat (build_work p)) *
      N.of_nat (17 * (function_width p + 1)))%N).
    - apply N.mul_le_mono; [now apply N.mul_le_mono_l|now apply time_of_nat_le].
    - rewrite Nat2N.inj_mul. change (N.of_nat 17) with 17%N.
      replace (Va.c_val * (20 * N.of_nat (build_work p)) *
        (17 * N.of_nat (function_width p + 1)))%N with
        (340 * (Va.c_val * N.of_nat (build_work p) * N.of_nat (function_width p + 1)))%N
        by ring.
      replace (512 * Va.c_val * N.of_nat (build_work p) *
        N.of_nat (function_width p + 1))%N with
        (512 * (Va.c_val * N.of_nat (build_work p) * N.of_nat (function_width p + 1)))%N
        by ring.
      apply N.mul_le_mono_r; lia.
  Qed.

  Lemma budget_live_clock p :
    (L.T_live_in p <= L.c_live * N.of_nat (build_work p) *
      N.of_nat (function_width p + 1))%N.
  Proof.
    eapply N.le_trans; [apply L.T_live_in_le|].
    apply N.mul_le_mono_r; apply N.mul_le_mono_l; apply time_of_nat_le.
    unfold build_work; lia.
  Qed.

  (** Rejection of repeated source identifiers costs at most one syntax scan. *)
  Lemma budget_unique_clock : forall (bs : list (positive * block positive O.K O.G)) seen w,
    (forall b body, In (b, body) bs -> Pos.size_nat b <= w) ->
    (T_build_blocks_unique bs seen <= (PTrieT.c_trie + 16) *
      N.of_nat (length bs + 1) * N.of_nat (w + 1))%N.
  Proof.
    induction bs as [|[b body] rest IH]; intros seen w Hwidth.
    - time_step.
    - assert (Hb : Pos.size_nat b <= w) by (apply (Hwidth b body); left; reflexivity).
      specialize (IH (PTrieCode.set b tt seen) w
        ltac:(intros a other Hin; apply (Hwidth a other); right; exact Hin)).
      pose proof (val_mem_time seen b w Hb) as Hmem.
      pose proof (PTrieT.T_set_le unit b tt seen) as Hset.
      time_unfold @T_build_blocks_unique.
      destruct (val_mem seen b); time_cbn; nia.
  Qed.

  Lemma budget_source_unique_clock p :
    (T_build_blocks_unique (blocks _ _ _ p) Empty <=
      (PTrieT.c_trie + 16) * N.of_nat (build_work p) * N.of_nat (function_width p + 1))%N.
  Proof.
    eapply N.le_trans.
    - apply budget_unique_clock; intros b body Hin; now apply (val_block_width p b body).
    - apply N.mul_le_mono_r; apply N.mul_le_mono_l; apply time_of_nat_le.
      pose proof (val_ssa_counts p). unfold build_work; lia.
  Qed.
  (** The producer pays only the phases reached before rejection. *)
  Lemma budget_produce_parts p :
    (T_produce p <= R.T_prepare p + T_build_blocks_unique (blocks _ _ _ p) Empty +
      (if build_blocks_unique (blocks _ _ _ p) Empty then
        T_graph p + D.T_build (graph p) (entry _ _ _ p) +
        D.T_check (graph p) (entry _ _ _ p) (fst (dom_result p)) (snd (dom_result p)) +
        (if D.check (graph p) (entry _ _ _ p) (fst (dom_result p)) (snd (dom_result p)) then
          D.T_tree (graph p) (entry _ _ _ p) (fst (dom_result p)) (snd (dom_result p)) +
          F.T_df (graph p) (dom_tree p) + L.T_live_in p + U.T_universe (R.prepare p) +
          T_placement_allowed p (R.prepare p) (frontiers p) (L.live_in p)
            (U.universe (R.prepare p)) +
          (if placement_allowed p (R.prepare p) (frontiers p) (L.live_in p)
            (U.universe (R.prepare p)) then
            T_def_index p + T_live_sets (L.live_in p) +
            T_placement_with (frontiers p) (def_index p) (live_sets (L.live_in p))
              (U.universe (R.prepare p)) +
            T_rename p (dom_tree p) (placement p) (L.live_in p)
          else 0)
        else 0)
      else 0) + 1024)%N.
  Proof.
    time_unfold T_produce. time_unfold T_graph. time_simpl.
    unfold placement, frontiers, dom_tree, dom_result, graph.
    set (q := R.prepare p).
    set (g := DG.prepare (cfg_graph (BC.nodes q) (BC.edges q) (BC.src q) (BC.dst q))).
    set (result := D.build g (entry _ _ _ p)).
    set (tree := D.tree g (entry _ _ _ p) (fst result) (snd result)).
    set (frontier := F.df g tree).
    destruct (build_blocks_unique (blocks _ _ _ p) Empty); [|lia].
    destruct (D.check g (entry _ _ _ p) (fst result) (snd result)); [|lia].
    destruct (placement_allowed p q frontier (L.live_in p) (U.universe q)); lia.
  Qed.

  Module UniverseClock := LiveT O P Q R BE E N BC C U SP PB.
  Definition budget_universe_coefficient : N :=
    (2048 * UniverseClock.live_clock_scale * UniverseClock.live_clock_scale *
      UniverseClock.live_clock_scale * UniverseClock.live_clock_scale)%N.

  (** Universe readers have the same syntax budget as the Live driver. *)
  Lemma budget_universe_clock p :
    (U.T_universe (R.prepare p) <= budget_universe_coefficient *
      N.of_nat (build_work p) * N.of_nat (function_width p + 1))%N.
  Proof.
    pose proof (UniverseClock.live_graph_load_bound p) as Hload.
    assert (Hloadpaid : (N.of_nat (UniverseClock.live_graph_load (R.prepare p)) <=
      2 * UniverseClock.live_clock_scale * N.of_nat (build_work p))%N).
    { eapply N.le_trans; [exact Hload|]. apply N.mul_le_mono_l.
      apply time_of_nat_le. exact (proj2 (budget_size_lower p)). }
    eapply N.le_trans; [apply UniverseClock.live_universe_atom|].
    unfold budget_universe_coefficient, UniverseClock.live_clock_atom,
      UniverseClock.live_clock_width.
    replace (2048 * UniverseClock.live_clock_scale * UniverseClock.live_clock_scale *
      UniverseClock.live_clock_scale * UniverseClock.live_clock_scale *
      N.of_nat (build_work p) * N.of_nat (function_width p + 1))%N with
      ((16 * (64 * UniverseClock.live_clock_scale * UniverseClock.live_clock_scale *
        N.of_nat (function_width p + 1)) * UniverseClock.live_clock_scale) *
        (2 * UniverseClock.live_clock_scale * N.of_nat (build_work p)))%N by ring.
    apply N.mul_le_mono_l. exact Hloadpaid.
  Qed.

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

  (** Every component inventory is a sub-budget of the published build work. *)
  Lemma budget_component_clock p cost coefficient size : size <= build_work p ->
    (cost <= coefficient * N.of_nat size * N.of_nat (function_width p + 1))%N ->
    (cost <= coefficient * N.of_nat (build_work p) * N.of_nat (function_width p + 1))%N.
  Proof.
    intros Hsize Hcost; eapply N.le_trans; [exact Hcost|].
    apply N.mul_le_mono_r; apply N.mul_le_mono_l; now apply time_of_nat_le.
  Qed.

  Definition budget_producer_coefficient : N :=
    (2048 + R.c_prepare + PTrieT.c_trie + 16 + Clock.ssa_graph_coefficient +
      3 * D.c_dom + F.c_frontier + L.c_live + budget_universe_coefficient +
      place_guard_coefficient + place_index_coefficient + place_driver_coefficient +
      rename_cached_coefficient)%N.

  (** The producer evaluates each successful phase once and charges all rejected prefixes. *)
  Lemma budget_producer_clock p :
    (T_produce p <= budget_producer_coefficient * N.of_nat (build_work p) *
      N.of_nat (function_width p + 1))%N.
  Proof.
    pose proof (budget_produce_parts p) as Hparts.
    pose proof (budget_prepare_clock p) as Hprepare.
    pose proof (budget_source_unique_clock p) as Huniqueclock.
    pose proof (budget_graph_clock p) as Hgraph.
    pose proof (budget_dom_build_clock p) as Hbuild.
    pose proof (budget_dom_check_clock p (fst (dom_result p)) (snd (dom_result p))) as Hcheckclock.
    pose proof (budget_live_clock p) as Hlive.
    pose proof (budget_universe_clock p) as Huniverse.
    assert (Hguardclock : (T_placement_allowed p (R.prepare p) (frontiers p) (L.live_in p)
      (U.universe (R.prepare p)) <= place_guard_coefficient * N.of_nat (build_work p) *
        N.of_nat (function_width p + 1))%N).
    { eapply budget_component_clock; [|apply place_guard_clock]. unfold build_work; lia. }
    assert (Hindexes : (T_def_index p + T_live_sets (L.live_in p) <=
      place_index_coefficient * N.of_nat (build_work p) * N.of_nat (function_width p + 1))%N).
    { eapply budget_component_clock; [|apply place_indexes_clock]. unfold build_work; lia. }
    assert (Hunit : (1 <= N.of_nat (build_work p) * N.of_nat (function_width p + 1))%N).
    { pose proof (budget_size_lower p). rewrite !Nat2N.inj_add; nia. }
    destruct (build_blocks_unique (blocks _ _ _ p) Empty) eqn:Hunique.
    - assert (Hdistinct : NoDup (map fst (blocks _ _ _ p))).
      { rewrite build_blocks_unique_map in Hunique.
        exact (proj1 (val_unique_sound _ _ Hunique)). }
      destruct (D.check (graph p) (entry _ _ _ p) (fst (dom_result p))
        (snd (dom_result p))) eqn:Hcheck.
      + pose proof (budget_dom_tree_clock p _ _ Hcheck) as Htree.
        pose proof (budget_frontier_clock p Hcheck) as Hfrontier.
        destruct (placement_allowed p (R.prepare p) (frontiers p) (L.live_in p)
          (U.universe (R.prepare p))) eqn:Hguard.
        * assert (Hplacement : (T_placement_with (frontiers p) (def_index p)
            (live_sets (L.live_in p))
            (U.universe (R.prepare p)) <= place_driver_coefficient *
              N.of_nat (build_work p) * N.of_nat (function_width p + 1))%N).
          { eapply budget_component_clock; [|now apply place_with_clock]. unfold build_work; lia. }
          assert (Hrename : (T_rename p (dom_tree p) (placement p) (L.live_in p) <=
            rename_cached_coefficient * N.of_nat (build_work p) *
              N.of_nat (function_width p + 1))%N).
          { eapply budget_component_clock; [|now apply rename_cached_time].
            unfold build_work; lia. }
          unfold budget_producer_coefficient.
          rewrite !N.mul_add_distr_r, <- !N.mul_assoc in *; lia.
        * unfold budget_producer_coefficient.
          rewrite !N.mul_add_distr_r, <- !N.mul_assoc in *; lia.
      + unfold budget_producer_coefficient.
        rewrite !N.mul_add_distr_r, <- !N.mul_assoc in *; lia.
    - unfold budget_producer_coefficient.
      rewrite !N.mul_add_distr_r, <- !N.mul_assoc in *; lia.
  Qed.

  Definition k_graph : N := budget_producer_coefficient.
  Definition k_place : N := (place_index_coefficient + place_variable_coefficient)%N.
  Definition k_rename : N := rename_cached_coefficient.

  (** The two indexes charge syntax and emitted live rows once. *)
  Lemma T0_indexes : forall p,
    (T_def_index p + T_live_sets (L.live_in p) <= k_place *
      N.of_nat (function_size p + L.live_size p + 1) * N.of_nat (function_width p + 1))%N.
  Proof.
    intro p; eapply N.le_trans; [exact (place_indexes_clock p)|].
    apply N.mul_le_mono_r, N.mul_le_mono_r; unfold k_place; lia.
  Qed.
  (** One placement search for a variable of the universe charges its seeds, their frontier
      rows and the discovered frontier rows. *)
  Lemma T1_place_var : forall p x, In x (U.universe (R.prepare p)) ->
    D.check (graph p) (entry _ _ _ p) (fst (dom_result p)) (snd (dom_result p)) = true ->
    (T_place_var (frontiers p) (def_index p) (live_sets (L.live_in p)) x <= k_place *
      N.of_nat (length (definition_blocks p x) +
        fold_right (fun b n => (length (frontier_row (frontiers p) b) + n)%nat)
          0%nat (definition_blocks p x) +
        fold_right (fun b n => (1 + length (frontier_row (frontiers p) b) + n)%nat)
          0%nat (phi_sites p x) + 1) * N.of_nat (function_width p + 1))%N.
  Proof.
    intros p x Hx Hcheck; eapply N.le_trans; [exact (place_variable_clock p x Hx Hcheck)|].
    apply N.mul_le_mono_r, N.mul_le_mono_r; unfold k_place; lia.
  Qed.
  (** Initialization charges the source inventory at its syntax width. *)
  Lemma T2a_rename_init : forall p,
    (T_rename_init p <= k_rename * N.of_nat (function_size p + 1) *
      N.of_nat (function_width p + 1))%N.
  Proof.
    intro p; eapply N.le_trans; [exact (rename_initial_time p)|].
    apply N.mul_le_mono_r, N.mul_le_mono_r.
    unfold k_rename, rename_cached_coefficient, rename_clock_common; lia.
  Qed.
  (** Renaming distinct blocks along a checked dominator tree charges the source, the live
      rows and the placement work. *)
  Lemma T2_rename : forall p, NoDup (map fst (blocks _ _ _ p)) ->
    D.check (graph p) (entry _ _ _ p) (fst (dom_result p)) (snd (dom_result p)) = true ->
    (T_rename p (dom_tree p) (placement p) (L.live_in p) <=
      k_rename * N.of_nat (function_size p + L.live_size p + placement_work p + 1) *
        N.of_nat (function_width p + 1))%N.
  Proof.
    intros p Hunique Hcheck; unfold k_rename; exact (rename_cached_time p Hunique Hcheck).
  Qed.
  (** The producer stays within the published construction work at the source width. *)
  Lemma T3_produce : forall p,
    (T_produce p <= k_graph * N.of_nat (build_work p) * N.of_nat (function_width p + 1))%N.
  Proof.
    intro p; unfold k_graph; exact (budget_producer_clock p).
  Qed.

  Definition c_build : N :=
    (budget_producer_coefficient + 1024 * Va.c_val + 16)%N.

  (** Construction keeps the published dominator, placement, liveness and argument budget. *)
  Lemma T_build_le : forall p,
    (T_build p <= c_build * N.of_nat (build_work p) * N.of_nat (function_width p + 1) +
      c_build * N.of_nat (Va.op_bits p + 1))%N.
  Proof.
    intro p. pose proof (T4_wrapper p) as Hwrapper.
    pose proof (budget_producer_clock p) as Hproducer.
    assert (Hunit : (1 <= N.of_nat (build_work p) * N.of_nat (function_width p + 1))%N).
    { pose proof (budget_size_lower p). rewrite !Nat2N.inj_add; nia. }
    destruct (produce p) as [[s c]|] eqn:Hproduce.
    - pose proof (budget_translation_clock p s c Hproduce) as Htranslation.
      pose proof (budget_candidate_ssa_clock p s c Hproduce) as Hssa.
      assert (Hop : (Va.c_val * N.of_nat (Va.op_bits p + 1) <=
        c_build * N.of_nat (Va.op_bits p + 1))%N).
      { apply N.mul_le_mono_r. unfold c_build; lia. }
      unfold k_wrap in Hwrapper.
      unfold c_build at 1; rewrite !N.mul_add_distr_r, <- !N.mul_assoc in *; lia.
    - unfold k_wrap in Hwrapper.
      unfold c_build; rewrite !N.mul_add_distr_r, <- !N.mul_assoc in *; lia.
  Qed.

  (** Construction has the published asymptotic syntax and operation-bit budget. *)
  Lemma build_bigO : bigO (fun _ : P.t => True)
    (fun p => N.of_nat (build_work p * (function_width p + 1) + Va.op_bits p + 1)) T_build.
  Proof.
    exists c_build; intros p Htrue.
    eapply N.le_trans; [apply T_build_le|].
    lazymatch goal with |- (?lhs <= ?rhs)%N =>
      replace rhs with (lhs + c_build)%N by
        (rewrite !Nat2N.inj_add, !Nat2N.inj_mul, !Nat2N.inj_add;
          replace (N.of_nat 1) with 1%N by reflexivity; ring)
    end.
    apply N.le_add_r.
  Qed.
End BuildT.
