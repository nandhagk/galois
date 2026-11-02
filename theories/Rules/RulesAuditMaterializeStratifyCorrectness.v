(** * Stratification trace correctness and work bounds

    The counted stratifier preserves native results and bounds the work of its actual trace.
    For example, duplicate rules add traversal work while completed states retain fuel calls.
    Builds on: RulesAuditMaterializeStratify, CollectionsAuditTrieAdequacy
    and CollectionsAuditElementsAdequacy. *)

From Stdlib Require Import List Bool NArith ZArith PeanoNat Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditTrie CollectionsAuditTrieAdequacy CollectionsAuditElements
  CollectionsAuditElementsAdequacy CollectionsAuditCost CollectionsTrie.
From Galois.Rules Require Import RulesSyntax RulesStratify RulesAuditMaterializePrelude
  RulesAuditMaterializeStratify.
Import List.ListNotations.

(** Every program has a counted stratification result and trace. *)
Theorem mat_stratify_total : mat_stratify_total_statement.
Proof.
  intros P prog.
  destruct (mat_stratify prog) as [out trace] eqn:Hrun.
  exists out, trace.
  reflexivity.
Qed.

(** A program determines both the stratification result and its trace. *)
Theorem mat_stratify_unique : mat_stratify_unique_statement.
Proof.
  intros P prog r1 t1 r2 t2 Hfirst Hsecond.
  rewrite Hfirst in Hsecond.
  inversion Hsecond.
  split; reflexivity.
Qed.

(** Erasing a counted map preserves its element results and order. *)
Lemma mat_map_erases A B (f : A -> mat_run B) xs :
  fst (mat_map f xs) = List.map (fun x => fst (f x)) xs.
Proof.
  induction xs as [|x xs IH].
  - reflexivity.
  - cbn [mat_map mat_mark].
    destruct (f x) as [value events] eqn:Hfirst.
    destruct (mat_map f xs) as [values tail_events] eqn:Htail.
    cbn [mat_bind mat_return fst] in *.
    rewrite IH.
    change (value :: List.map (fun y => fst (f y)) xs =
      fst (f x) :: List.map (fun y => fst (f y)) xs).
    rewrite Hfirst. reflexivity.
Qed.

(** Erasing a counted append preserves the two input lists. *)
Lemma mat_append_erases A (xs ys : list A) : fst (mat_append xs ys) = xs ++ ys.
Proof.
  induction xs as [|x xs IH].
  - reflexivity.
  - cbn [mat_append mat_mark].
    destruct (mat_append xs ys) as [tail events] eqn:Htail.
    cbn [mat_bind mat_return fst] in IH |- *.
    rewrite IH.
    reflexivity.
Qed.

(** Erasing counted flat-map preserves every returned list. *)
Lemma mat_flatmap_erases A B (f : A -> mat_run (list B)) xs :
  fst (mat_flatmap f xs) = List.flat_map (fun x => fst (f x)) xs.
Proof.
  induction xs as [|x xs IH].
  - reflexivity.
  - cbn [mat_flatmap mat_mark].
    destruct (f x) as [first first_events] eqn:Hfirst.
    destruct (mat_flatmap f xs) as [later later_events] eqn:Hlater.
    cbn [mat_bind fst] in IH |- *.
    pose proof (mat_append_erases B first later) as Happ.
    destruct (mat_append first later) as [result events] eqn:Happend.
    cbn [fst] in Happ.
    rewrite Happ, IH.
    change (first ++ List.flat_map (fun y => fst (f y)) xs =
      fst (f x) ++ List.flat_map (fun y => fst (f y)) xs).
    now rewrite Hfirst.
Qed.

(** Erasing a counted left fold preserves its accumulator transitions. *)
Lemma mat_foldl_erases A B (f : B -> A -> mat_run B) xs initial :
  fst (mat_foldl f xs initial) = List.fold_left (fun acc x => fst (f acc x)) xs initial.
Proof.
  revert initial.
  induction xs as [|x xs IH]; intro initial.
  - reflexivity.
  - cbn [mat_foldl mat_mark].
    destruct (f initial x) as [next events] eqn:Hnext.
    destruct (mat_foldl f xs next) as [out tail_events] eqn:Htail.
    specialize (IH next). rewrite Htail in IH.
    cbn [mat_bind fst] in IH |- *.
    rewrite Htail.
    change (out = List.fold_left (fun acc y => fst (f acc y)) xs (fst (f initial x))).
    rewrite IH, Hnext. reflexivity.
Qed.

(** Erasing a counted right fold preserves its accumulator transitions. *)
Lemma mat_foldr_erases A B (f : A -> B -> mat_run B) xs initial :
  fst (mat_foldr f xs initial) = List.fold_right (fun x acc => fst (f x acc)) initial xs.
Proof.
  induction xs as [|x xs IH].
  - reflexivity.
  - cbn [mat_foldr mat_mark].
    destruct (mat_foldr f xs initial) as [before events] eqn:Hbefore.
    cbn [mat_bind fst] in IH |- *.
    destruct (f x before) as [out tail_events] eqn:Hout.
    cbn [fst].
    change (out = fst (f x (List.fold_right (fun y acc => fst (f y acc)) initial xs))).
    rewrite <- IH, Hout. reflexivity.
Qed.

(** Erasing a counted Boolean fold preserves its strict result. *)
Lemma mat_all_erases A (f : A -> mat_run bool) xs :
  fst (mat_all f xs) = List.forallb (fun x => fst (f x)) xs.
Proof.
  induction xs as [|x xs IH].
  - reflexivity.
  - cbn [mat_all mat_mark].
    destruct (f x) as [first events] eqn:Hfirst.
    destruct (mat_all f xs) as [later tail_events] eqn:Hlater.
    cbn [mat_bind mat_return fst] in IH |- *.
    rewrite IH.
    change (first && List.forallb (fun y => fst (f y)) xs =
      fst (f x) && List.forallb (fun y => fst (f y)) xs).
    now rewrite Hfirst.
Qed.

(** Counted rule edges preserve the native literal order and polarity. *)
Lemma mat_rule_edges_erases P (r : rule P) : fst (mat_rule_edges r) = rule_edges r.
Proof.
  unfold mat_rule_edges, rule_edges.
  rewrite mat_map_erases.
  reflexivity.
Qed.

(** Counted program edges preserve the native rule traversal. *)
Lemma mat_program_edges_erases P (prog : program P) :
  fst (mat_program_edges prog) = program_edges prog.
Proof.
  unfold mat_program_edges, program_edges.
  rewrite mat_flatmap_erases.
  induction (rules prog) as [|r rs IH].
  - reflexivity.
  - cbn [List.flat_map]. rewrite mat_rule_edges_erases, IH. reflexivity.
Qed.

(** Counted rule predicates preserve the native head and body order. *)
Lemma mat_rule_predicates_erases P (r : rule P) :
  fst (mat_rule_predicates r) = rule_predicates r.
Proof.
  unfold mat_rule_predicates, rule_predicates.
  pose proof (mat_map_erases _ _ (fun lit => mat_return (pred (lit_atom lit))) (body r)) as Hmap.
  destruct (mat_map (fun lit => mat_return (pred (lit_atom lit))) (body r)) as [tail events].
  cbn [fst] in Hmap.
  unfold mat_bind, mat_return.
  cbn [fst]. now rewrite Hmap.
Qed.

(** Counted updates preserve the exact key and value at the encoded position. *)
Lemma mat_set_erases P V (E : encoding P) key value (input : Map.t P V) :
  fst (mat_set E key value input) = Map.set E key value input.
Proof.
  unfold mat_set, mat_encode, mat_bind, Map.set.
  pose proof (audit_trie_set_erases (P * V)%type (encode E key) (key, value) input) as Hset.
  destruct (audit_trie_set (encode E key) (key, value) input) as [out events].
  cbn [fst] in Hset |- *.
  exact Hset.
Qed.

(** Counted lookups preserve the native map result. *)
Lemma mat_get_erases P V (E : encoding P) key (input : Map.t P V) :
  fst (mat_get E key input) = Map.get E key input.
Proof.
  unfold mat_get, mat_encode, mat_bind, Map.get.
  pose proof (audit_map_code_get_erases P V (encode E key) input) as Hget.
  destruct (audit_map_code_get (encode E key) input) as [out events].
  cbn [fst] in Hget |- *.
  exact Hget.
Qed.

(** Building the counted predicate set agrees with the native left fold. *)
Lemma mat_predicate_set_erases P (E : encoding P) keys :
  fst (mat_predicate_set_encoded (mat_encode E) keys) = FinSet.of_list E keys.
Proof.
  unfold mat_predicate_set_encoded, FinSet.of_list.
  rewrite mat_foldl_erases.
  change (List.fold_left (fun set key => fst (mat_set E key tt set)) keys Map.empty =
    List.fold_left (fun set key => FinSet.add E key set) keys Map.empty).
  generalize (Map.empty : Map.t P unit).
  induction keys as [|key keys IH]; intro set.
  - reflexivity.
  - cbn [List.fold_left]. rewrite mat_set_erases. apply IH.
Qed.

(** The counted predicate enumeration returns the native distinct node list. *)
Lemma mat_rule_nodes_erases P (prog : program P) :
  fst (mat_rule_nodes prog) = rule_nodes prog.
Proof.
  unfold mat_rule_nodes, rule_nodes.
  pose proof (mat_flatmap_erases _ _ mat_rule_predicates (rules prog)) as Hflat.
  destruct (mat_flatmap mat_rule_predicates (rules prog)) as [keys events] eqn:Hkeys.
  cbn [fst] in Hflat.
  assert (Hnative : keys = List.flat_map rule_predicates (rules prog)).
  { rewrite Hflat. clear Hflat Hkeys.
    induction (rules prog) as [|r rs IH].
    - reflexivity.
    - cbn [List.flat_map]. rewrite mat_rule_predicates_erases, IH. reflexivity. }
  pose proof (mat_predicate_set_erases P (penc prog) keys) as Hset.
  destruct (mat_predicate_set_encoded (mat_encode (penc prog)) keys) as [set set_events]
    eqn:Hset_run.
  cbn [fst] in Hset.
  pose proof (audit_finset_elements_erases P set) as Helements.
  unfold mat_elements, mat_lift.
  destruct (audit_finset_elements set) as [out enum_events] eqn:Henum.
  cbn [fst] in Helements.
  unfold mat_bind.
  cbn [fst].
  rewrite Hset_run, Henum. cbn [fst].
  now rewrite Helements, Hset, Hnative.
Qed.

(** Counted level lookup has the native default for absent keys. *)
Lemma mat_level_at_erases P (E : encoding P) (m : Map.t P nat) p :
  fst (mat_level_at E m p) = level_at E m p.
Proof.
  unfold mat_level_at, level_at.
  pose proof (mat_get_erases P nat E p m) as Hget.
  destruct (mat_get E p m) as [found events].
  cbn [fst] in Hget.
  unfold mat_bind, mat_return.
  cbn [fst]. now rewrite Hget.
Qed.

(** Discarding a writer trace preserves the result of sequential composition. *)
Lemma mat_bind_erases A B (run : mat_run A) (f : A -> mat_run B) :
  fst (mat_bind run f) = fst (f (fst run)).
Proof.
  destruct run as [value events].
  destruct (f value) as [result tail_events] eqn:Hresult.
  unfold mat_bind. rewrite Hresult. cbn [fst]. rewrite Hresult.
  reflexivity.
Qed.

(** Counted edge checks return the same Boolean as native checks. *)
Lemma mat_edge_ok_erases P (E : encoding P) m e :
  fst (mat_edge_ok E m e) = edge_ok E m e.
Proof.
  unfold mat_edge_ok, edge_ok.
  repeat rewrite mat_bind_erases.
  cbn [mat_nat mat_nat_test fst].
  now rewrite !mat_level_at_erases.
Qed.

(** Counted edge updates preserve the native map. *)
Lemma mat_raise_edge_erases P (E : encoding P) m e :
  fst (mat_raise_edge E m e) = raise_edge E m e.
Proof.
  unfold mat_raise_edge, raise_edge.
  repeat rewrite mat_bind_erases.
  cbn [mat_nat fst].
  rewrite !mat_level_at_erases.
  apply mat_set_erases.
Qed.

(** A counted stratification step returns the native state transition. *)
Lemma mat_stratify_tick_erases P (prog : program P) state :
  fst (mat_stratify_tick prog state) = stratify_step prog state.
Proof.
  destruct state as [levels done].
  destruct done.
  - reflexivity.
  - unfold mat_stratify_tick, stratify_step.
    cbn [mat_mark fst].
    repeat rewrite mat_bind_erases.
    rewrite mat_program_edges_erases, mat_all_erases.
    assert (Hready : List.forallb
      (fun e => fst (mat_edge_ok (penc prog) levels e)) (program_edges prog) =
      levels_ok prog levels).
    { unfold levels_ok. induction (program_edges prog) as [|e es IH].
      - reflexivity.
      - cbn [List.forallb]. rewrite mat_edge_ok_erases, IH. reflexivity. }
    rewrite Hready.
    destruct (levels_ok prog levels).
    + reflexivity.
    + repeat rewrite mat_bind_erases.
      rewrite mat_program_edges_erases, mat_foldl_erases.
      unfold raise_pass.
      clear Hready.
      generalize levels.
      induction (program_edges prog) as [|e es IH]; intro acc.
      * reflexivity.
      * cbn [List.fold_left]. rewrite mat_raise_edge_erases. apply IH.
Qed.

(** Counted positive iteration preserves every binary-fuel state transition. *)
Lemma mat_piter_erases A fuel (body : A -> mat_run A) step :
  (forall state, fst (body state) = step state) ->
  forall state, fst (mat_piter fuel body state) = Pos.iter step state fuel.
Proof.
  intro Hbody.
  induction fuel as [fuel IH | fuel IH |]; intro state.
  - cbn [mat_piter mat_mark fst Pos.iter].
    repeat rewrite mat_bind_erases.
    rewrite !IH, Hbody. reflexivity.
  - cbn [mat_piter mat_mark fst Pos.iter].
    rewrite mat_bind_erases, !IH. reflexivity.
  - cbn [mat_piter mat_mark fst Pos.iter]. apply Hbody.
Qed.

(** Counted binary iteration agrees with the native iteration, including zero fuel. *)
Lemma mat_niter_erases A fuel (body : A -> mat_run A) step :
  (forall state, fst (body state) = step state) ->
  forall state, fst (mat_niter fuel body state) = N.iter fuel step state.
Proof.
  intros Hbody state. destruct fuel as [|fuel].
  - reflexivity.
  - change (fst (mat_piter fuel body state) = Pos.iter step state fuel).
    now apply mat_piter_erases.
Qed.

(** Counted stratification preserves rejection, the returned bound, and every predicate level. *)
Theorem mat_stratify_erases : mat_stratify_erases_statement.
Proof.
  intros P prog.
  unfold mat_stratify, stratify, stratify_state.
  repeat rewrite mat_bind_erases.
  rewrite mat_rule_nodes_erases.
  cbn [mat_emit fst].
  assert (Hiter : forall fuel state,
    fst (mat_niter fuel (mat_stratify_tick prog) state) =
      N.iter fuel (stratify_step prog) state).
  { intros fuel state. apply mat_niter_erases. apply mat_stratify_tick_erases. }
  rewrite Hiter.
  destruct (N.iter
    (N.succ (N.of_nat (length (rule_nodes prog)) * N.of_nat (length (rule_nodes prog))))
    (stratify_step prog) (Map.empty, false)) as [levels done].
  destruct done.
  - cbn [mat_mark fst].
    repeat rewrite mat_bind_erases.
    rewrite mat_rule_nodes_erases, mat_map_erases, mat_foldr_erases.
    assert (Hvalues : List.map (fun p => fst (mat_level_at (penc prog) levels p))
      (rule_nodes prog) = List.map (level_at (penc prog) levels) (rule_nodes prog)).
    { induction (rule_nodes prog) as [|p ps IH].
      - reflexivity.
      - cbn [List.map]. rewrite mat_level_at_erases, IH. reflexivity. }
    rewrite Hvalues.
    cbn [mat_return mat_nat mat_native_levels fst count level].
    rewrite Nat.add_1_r. split; reflexivity.
  - reflexivity.
Qed.

(** * Trace composition and strict traversal costs *)

(** Trace concatenation adds work. *)
Lemma mat_work_app xs ys : mat_work (xs ++ ys) = mat_work xs + mat_work ys.
Proof.
  unfold mat_work. induction xs as [|x xs IH]; cbn; [reflexivity |].
  rewrite IH. lia.
Qed.

(** Every trace width includes the unit baseline. *)
Lemma mat_width_positive xs : 1 <= mat_width xs.
Proof.
  unfold mat_width. induction xs as [|x xs IH]; [reflexivity |].
  cbn [fold_right].
  eapply Nat.le_trans; [exact IH | apply Nat.le_max_l].
Qed.

(** Each component's operand width is retained by concatenation. *)
Lemma mat_width_app xs ys :
  mat_width (xs ++ ys) = Nat.max (mat_width xs) (mat_width ys).
Proof.
  induction xs as [|x xs IH].
  - change (mat_width ys = Nat.max 1 (mat_width ys)).
    rewrite Nat.max_r; [reflexivity | apply mat_width_positive].
  - unfold mat_width in IH |- *. cbn [app fold_right]. rewrite IH. lia.
Qed.

(** A local cost remains valid when its trace is embedded in a wider execution. *)
Definition mat_cost {A} (run : mat_run A) (width budget : nat) : Prop :=
  mat_width (snd run) <= width -> mat_work (snd run) <= budget.

(** Sequential composition retains both local width bounds and adds their costs. *)
Lemma mat_bind_cost A B (run : mat_run A) (next : A -> mat_run B) width first second :
  mat_cost run width first -> (forall value, mat_cost (next value) width second) ->
  mat_cost (mat_bind run next) width (first + second).
Proof.
  destruct run as [value events].
  destruct (next value) as [out tail] eqn:Hnext.
  unfold mat_cost, mat_bind; rewrite Hnext; cbn [snd].
  rewrite mat_width_app, mat_work_app.
  intros Hfirst Hsecond Hwidth.
  specialize (Hsecond value). rewrite Hnext in Hsecond. cbn [snd] in Hsecond.
  apply Nat.add_le_mono; [apply Hfirst | apply Hsecond]; lia.
Qed.

(** A block marker contributes its fixed charge and preserves its body's width. *)
Lemma mat_mark_cost A site (run : mat_run A) width budget :
  mat_cost run width budget -> mat_cost (mat_mark site run) width (100 + budget).
Proof.
  destruct run as [out events]. unfold mat_cost, mat_mark.
  cbn [snd mat_width mat_work fold_right mat_frame_work]. intros Hcost Hwidth.
  specialize (Hcost ltac:(lia)). lia.
Qed.

(** A returned value has one fixed block charge. *)
Lemma mat_return_cost A (value : A) width : mat_cost (mat_return value) width 100.
Proof.
  unfold mat_cost. intro Hwidth. apply Nat.le_refl.
Qed.

(** A larger budget preserves a proved local cost. *)
Lemma mat_cost_mono A (run : mat_run A) width small large :
  mat_cost run width small -> small <= large -> mat_cost run width large.
Proof.
  unfold mat_cost. intros Hcost Hle Hwidth. specialize (Hcost Hwidth). lia.
Qed.

(** Strict mapping visits every list element and both terminal construction blocks. *)
Lemma mat_map_cost A B (f : A -> mat_run B) xs width price :
  (forall x, mat_cost (f x) width price) ->
  mat_cost (mat_map f xs) width (200 + length xs * (200 + price)).
Proof.
  intro Hf. induction xs as [|x xs IH].
  - cbn [mat_map]. apply mat_mark_cost, mat_return_cost.
  - cbn [mat_map].
    eapply mat_cost_mono.
    + apply mat_mark_cost. eapply mat_bind_cost; [apply Hf |]. intro value.
      eapply mat_bind_cost; [exact IH |]. intro values. apply mat_return_cost.
    + cbn [length]. nia.
Qed.

(** The strict Boolean fold pays for every callback even after a false result. *)
Lemma mat_all_cost A (f : A -> mat_run bool) xs width price :
  (forall x, mat_cost (f x) width price) ->
  mat_cost (mat_all f xs) width (200 + length xs * (200 + price)).
Proof.
  intro Hf. induction xs as [|x xs IH].
  - cbn [mat_all]. apply mat_mark_cost, mat_return_cost.
  - cbn [mat_all]. eapply mat_cost_mono.
    + apply mat_mark_cost. eapply mat_bind_cost; [apply Hf |]. intro value.
      eapply mat_bind_cost; [exact IH |]. intro values. apply mat_return_cost.
    + cbn [length]. nia.
Qed.

(** Left folds pay for all callbacks and keep every changing accumulator. *)
Lemma mat_foldl_cost A B (f : B -> A -> mat_run B) xs width price :
  (forall state x, mat_cost (f state x) width price) ->
  forall initial, mat_cost (mat_foldl f xs initial) width (200 + length xs * (100 + price)).
Proof.
  intro Hf. induction xs as [|x xs IH]; intro initial.
  - cbn [mat_foldl]. apply mat_mark_cost, mat_return_cost.
  - cbn [mat_foldl]. eapply mat_cost_mono.
    + apply mat_mark_cost. eapply mat_bind_cost; [apply Hf | apply IH].
    + cbn [length]. nia.
Qed.

(** Right folds retain the callback cost after each recursive result. *)
Lemma mat_foldr_cost A B (f : A -> B -> mat_run B) xs width price :
  (forall x state, mat_cost (f x state) width price) ->
  forall initial, mat_cost (mat_foldr f xs initial) width (200 + length xs * (100 + price)).
Proof.
  intro Hf. induction xs as [|x xs IH]; intro initial.
  - cbn [mat_foldr]. apply mat_mark_cost, mat_return_cost.
  - cbn [mat_foldr]. eapply mat_cost_mono.
    + apply mat_mark_cost. eapply mat_bind_cost; [apply IH |]. intro state. apply Hf.
    + cbn [length]. nia.
Qed.

(** Counted append visits just the first list. *)
Lemma mat_append_cost A (xs ys : list A) width :
  mat_cost (mat_append xs ys) width (200 + 200 * length xs).
Proof.
  induction xs as [|x xs IH].
  - cbn [mat_append]. apply mat_mark_cost, mat_return_cost.
  - cbn [mat_append]. eapply mat_cost_mono.
    + apply mat_mark_cost. eapply mat_bind_cost; [exact IH |]. intro tail.
      apply mat_return_cost.
    + cbn [length]. nia.
Qed.

(** Enumeration position lengths are bounded by the number of traversed trie nodes. *)
Lemma mat_elements_bits_bound A (node : Trie.ne A) :
  forall path depth,
  (forall p, Pos.size_nat (path p) <= depth + Pos.size_nat p) ->
  audit_elements_bits path node <= audit_elements_nodes node * (depth + audit_elements_nodes node).
Proof.
  induction node as [r IHr | v | v r IHr | l IHl | l IHl r IHr | l IHl v |
    l IHl v r IHr]; intros path depth Hpath;
    cbn [audit_elements_bits audit_elements_nodes].
  all: try (assert (Hl : forall p, Pos.size_nat (path (xO p)) <= S depth + Pos.size_nat p)
    by (intro p; specialize (Hpath (xO p)); cbn in Hpath; lia);
    specialize (IHl (fun p => path (xO p)) (S depth) Hl)).
  all: try (assert (Hr : forall p, Pos.size_nat (path (xI p)) <= S depth + Pos.size_nat p)
    by (intro p; specialize (Hpath (xI p)); cbn in Hpath; lia);
    specialize (IHr (fun p => path (xI p)) (S depth) Hr)).
  all: specialize (Hpath xH); cbn in Hpath; nia.
Qed.

(** Imported set enumeration includes all emitted position bits and both projections. *)
Lemma mat_elements_cost P (input : FinSet.t P) width :
  mat_cost (mat_elements input) width (26 * S width * S width).
Proof.
  pose proof (audit_finset_elements_work_bound P input) as Hwork.
  assert (Hbits : audit_trie_output_bits input <= audit_trie_nodes input * audit_trie_nodes input).
  { destruct input as [|node]; [reflexivity |].
    apply (mat_elements_bits_bound (P * unit)%type node (fun p => p) 0).
    intro p. lia. }
  unfold mat_cost, mat_elements, mat_lift.
  destruct (audit_finset_elements input) as [out events].
  cbn [snd] in Hwork |- *.
  change (Nat.max 1 (1 + length out + audit_trie_nodes input) <= width ->
    audit_set_elements_work events + 0 <= 26 * S width * S width).
  intro Hwidth. nia.
Qed.

(** Counted lookup uses the actual imported trie price and encoded key length. *)
Lemma mat_get_cost P V (E : encoding P) key (input : Map.t P V) width :
  mat_cost (mat_get E key input) width (6 * S width).
Proof.
  pose proof (audit_trie_get_trace_adequate (P * V)%type (encode E key) input) as Htrace.
  pose proof (audit_trie_get_source_work_bound (P * V)%type (encode E key) input) as Hwork.
  unfold mat_cost, mat_get, mat_encode, mat_bind, audit_map_code_get.
  destruct (audit_trie_get (encode E key) input) as [out events].
  cbn [snd] in Htrace.
  change (Nat.max (Nat.max 1 (1 + Pos.size_nat (encode E key) + audit_trie_nodes input))
    (Pos.size_nat (encode E key)) <= width ->
    1 + (audit_trie_get_trace_source_work events + 0) <= 6 * S width).
  intro Hwidth. nia.
Qed.

(** Counted update uses the original key and all strict constructor work. *)
Lemma mat_set_cost P V (E : encoding P) key value (input : Map.t P V) width :
  mat_cost (mat_set E key value input) width (17 * S width).
Proof.
  pose proof (audit_trie_update_trace_adequate (P * V)%type (encode E key)
    (Some (key, value)) input) as Htrace.
  pose proof (audit_trie_update_source_work_bound (P * V)%type (encode E key)
    (Some (key, value)) input) as Hwork.
  unfold mat_cost, mat_set, mat_encode, mat_bind, audit_trie_set.
  destruct (audit_trie_update (encode E key) (Some (key, value)) input) as [out events].
  cbn [snd] in Htrace.
  change (Nat.max (Nat.max 1 (1 + Pos.size_nat (encode E key) + audit_trie_nodes out))
    (Pos.size_nat (encode E key)) <= width ->
    1 + (audit_trie_update_trace_source_work events + 0) <= 17 * S width).
  intro Hwidth. nia.
Qed.

(** Nat frames retain precisely the operands that determine their charge. *)
Lemma mat_nat_cost site A (f : nat -> nat -> A) a b width :
  mat_cost (f a b, [MatNat site a b]) width (S width).
Proof.
  unfold mat_cost. change (Nat.max 1 (1 + a + b) <= width -> 1 + a + b + 0 <= S width).
  lia.
Qed.

(** A level lookup adds its default-selection block to the concrete lookup charge. *)
Lemma mat_level_at_cost P (E : encoding P) input key width :
  mat_cost (mat_level_at E input key) width (106 * S width).
Proof.
  unfold mat_level_at. eapply mat_cost_mono.
  - eapply mat_bind_cost; [apply mat_get_cost |]. intro found. apply mat_return_cost.
  - nia.
Qed.

(** Each edge check pays for both map reads and both arithmetic frames. *)
Lemma mat_edge_ok_cost P (E : encoding P) input edge width :
  mat_cost (mat_edge_ok E input edge) width (214 * S width).
Proof.
  unfold mat_edge_ok. eapply mat_cost_mono.
  - eapply mat_bind_cost; [apply mat_level_at_cost |]. intro source.
    eapply mat_bind_cost; [apply mat_nat_cost |]. intro required.
    eapply mat_bind_cost; [apply mat_level_at_cost |]. intro target. apply mat_nat_cost.
  - nia.
Qed.

(** Each raising edge pays for both reads, both arithmetic operations and its persistent update. *)
Lemma mat_raise_edge_cost P (E : encoding P) input edge width :
  mat_cost (mat_raise_edge E input edge) width (231 * S width).
Proof.
  unfold mat_raise_edge. eapply mat_cost_mono.
  - eapply mat_bind_cost; [apply mat_level_at_cost |]. intro target.
    eapply mat_bind_cost; [apply mat_level_at_cost |]. intro source.
    eapply mat_bind_cost; [apply mat_nat_cost |]. intro required.
    eapply mat_bind_cost; [apply mat_nat_cost |]. intro maximum. apply mat_set_cost.
  - nia.
Qed.

(** Sequential composition uses its actual returned value, including captured lists. *)
Lemma mat_bind_cost_at A B (run : mat_run A) (next : A -> mat_run B) width first second :
  mat_cost run width first -> mat_cost (next (fst run)) width second ->
  mat_cost (mat_bind run next) width (first + second).
Proof.
  destruct run as [value events]. destruct (next value) as [out tail] eqn:Hnext.
  unfold mat_cost, mat_bind; rewrite Hnext; cbn [fst snd].
  rewrite mat_width_app, mat_work_app. intros Hfirst Hsecond Hwidth.
  rewrite Hnext in Hsecond. cbn [snd] in Hsecond.
  apply Nat.add_le_mono; [apply Hfirst | apply Hsecond]; lia.
Qed.

(** Flat-map pays for every original occurrence and the append of its actual returned list. *)
Lemma mat_flatmap_cost A B (f : A -> mat_run (list B)) size xs width price :
  (forall x, length (fst (f x)) <= size x) ->
  (forall x, mat_cost (f x) width (price * S (size x))) ->
  mat_cost (mat_flatmap f xs) width
    (200 + (price + 300) * fold_right (fun x n => S (size x) + n) 0 xs).
Proof.
  intros Hlength Hf. induction xs as [|x xs IH].
  - cbn [mat_flatmap fold_right]. rewrite Nat.mul_0_r.
    apply mat_mark_cost, mat_return_cost.
  - cbn [mat_flatmap]. eapply mat_cost_mono.
    + apply mat_mark_cost. eapply mat_bind_cost_at; [apply Hf |].
      eapply mat_bind_cost; [exact IH |]. intro later. apply mat_append_cost.
    + pose proof (Hlength x). cbn [length fold_right]. nia.
Qed.

(** A rule's body mapping has one output per original literal. *)
Lemma mat_rule_edges_length P (r : rule P) :
  length (fst (mat_rule_edges r)) = length (body r).
Proof.
  unfold mat_rule_edges. rewrite mat_map_erases, length_map. reflexivity.
Qed.

(** One rule's edge construction visits every literal, including duplicates. *)
Lemma mat_rule_edges_cost P (r : rule P) width :
  mat_cost (mat_rule_edges r) width (300 * S (length (body r))).
Proof.
  unfold mat_rule_edges. eapply mat_cost_mono.
  - apply mat_map_cost. intro lit. apply mat_return_cost.
  - nia.
Qed.

(** Full edge construction is linear in original rule and body occurrence counts. *)
Lemma mat_program_edges_cost P (prog : program P) width :
  mat_cost (mat_program_edges prog) width (800 * S (mat_stratify_input_size prog)).
Proof.
  unfold mat_program_edges. eapply mat_cost_mono.
  - apply (mat_flatmap_cost _ _ _ (fun r => length (body r))).
    + intro r. rewrite mat_rule_edges_length. lia.
    + intro r. apply mat_rule_edges_cost.
  - unfold mat_stratify_input_size. nia.
Qed.

(** The edge list retains every original literal occurrence. *)
Lemma mat_program_edges_length P (prog : program P) :
  length (fst (mat_program_edges prog)) <= mat_stratify_input_size prog.
Proof.
  unfold mat_program_edges. rewrite mat_flatmap_erases.
  unfold mat_stratify_input_size. induction (rules prog) as [|r rs IH].
  - reflexivity.
  - cbn [flat_map fold_right]. rewrite length_app, mat_rule_edges_length. lia.
Qed.

(** A rule contributes its head and each original body predicate. *)
Lemma mat_rule_predicates_length P (r : rule P) :
  length (fst (mat_rule_predicates r)) = S (length (body r)).
Proof.
  rewrite mat_rule_predicates_erases. unfold rule_predicates. cbn [length].
  rewrite length_map. reflexivity.
Qed.

(** Rule predicate collection includes its final head-construction block. *)
Lemma mat_rule_predicates_cost P (r : rule P) width :
  mat_cost (mat_rule_predicates r) width (300 * S (length (body r))).
Proof.
  unfold mat_rule_predicates. eapply mat_cost_mono.
  - eapply mat_bind_cost.
    + apply mat_map_cost. intro lit. apply mat_return_cost.
    + intro tail. apply mat_return_cost.
  - nia.
Qed.

(** The original predicate occurrence list has exactly the published structural size. *)
Lemma mat_rule_predicates_flat_length P (prog : program P) :
  length (fst (mat_flatmap mat_rule_predicates (rules prog))) = mat_stratify_input_size prog.
Proof.
  rewrite mat_flatmap_erases. unfold mat_stratify_input_size.
  induction (rules prog) as [|r rs IH].
  - reflexivity.
  - cbn [flat_map fold_right]. rewrite length_app, mat_rule_predicates_length, IH. reflexivity.
Qed.

(** Predicate collection pays for the extra head in each appended list. *)
Lemma mat_rule_predicates_flat_cost P (prog : program P) width :
  mat_cost (mat_flatmap mat_rule_predicates (rules prog)) width
    (1400 * S (mat_stratify_input_size prog)).
Proof.
  eapply mat_cost_mono.
  - apply (mat_flatmap_cost _ _ _ (fun r => S (length (body r))) _ _ 300).
    + intro r. rewrite mat_rule_predicates_length. lia.
    + intro r. eapply mat_cost_mono; [apply mat_rule_predicates_cost |]. nia.
  - unfold mat_stratify_input_size.
    assert (Hcount : fold_right (fun r n => S (S (length (body r))) + n) 0 (rules prog) <=
      2 * fold_right (fun r n => S (length (body r)) + n) 0 (rules prog)).
    { induction (rules prog) as [|r rs IH]; cbn [fold_right]; nia. }
    nia.
Qed.

(** Predicate-set construction pays for each actual persistent update. *)
Lemma mat_predicate_set_cost P (E : encoding P) keys width :
  mat_cost (mat_predicate_set_encoded (mat_encode E) keys) width
    (200 + length keys * (100 + 17 * S width)).
Proof.
  unfold mat_predicate_set_encoded. apply mat_foldl_cost.
  intros input key. apply mat_set_cost.
Qed.

(** Node collection includes occurrence traversal, persistent insertion and full enumeration. *)
Lemma mat_rule_nodes_cost P (prog : program P) width :
  mat_cost (mat_rule_nodes prog) width
    (2000 * S (mat_stratify_input_size prog) * S width * S width).
Proof.
  unfold mat_rule_nodes. eapply mat_cost_mono.
  - eapply mat_bind_cost_at; [apply mat_rule_predicates_flat_cost |].
    eapply mat_bind_cost; [apply mat_predicate_set_cost |]. intro set. apply mat_elements_cost.
  - rewrite mat_rule_predicates_flat_length. nia.
Qed.

(** Each tick includes both edge-building passes when raising and the strict readiness fold. *)
Lemma mat_stratify_tick_cost P (prog : program P) state width :
  mat_cost (mat_stratify_tick prog state) width
    (4000 * S (mat_stratify_input_size prog) * S width).
Proof.
  destruct state as [levels done]. unfold mat_stratify_tick. apply mat_cost_mono with
    (small := 100 + (800 * S (mat_stratify_input_size prog) +
      (200 + mat_stratify_input_size prog * (200 + 214 * S width)) +
      (800 * S (mat_stratify_input_size prog) +
        (200 + mat_stratify_input_size prog * (100 + 231 * S width)) + 100)));
    [apply mat_mark_cost | nia].
  destruct done.
  - eapply mat_cost_mono; [apply mat_return_cost |]. nia.
  - eapply mat_cost_mono.
    + eapply mat_bind_cost_at; [apply mat_program_edges_cost |].
      eapply mat_bind_cost with
        (second := 800 * S (mat_stratify_input_size prog) +
          (200 + mat_stratify_input_size prog * (100 + 231 * S width)) + 100).
      * eapply mat_cost_mono with
          (large := 200 + mat_stratify_input_size prog * (200 + 214 * S width));
          [apply mat_all_cost; intro edge; apply mat_edge_ok_cost |].
        pose proof (mat_program_edges_length P prog). nia.
      * intro ready. destruct ready.
        -- eapply mat_cost_mono; [apply mat_return_cost |]. nia.
        -- eapply mat_cost_mono.
           ++ eapply mat_bind_cost_at; [apply mat_program_edges_cost |].
              eapply mat_bind_cost.
              ** eapply mat_cost_mono with
                   (large := 200 + mat_stratify_input_size prog * (100 + 231 * S width)).
                 --- apply mat_foldl_cost. intros input edge. apply mat_raise_edge_cost.
                 --- pose proof (mat_program_edges_length P prog). nia.
              ** intro next. apply mat_return_cost.
           ++ nia.
    + nia.
Qed.

(** Positive iteration includes every body call and every binary-recursion marker. *)
Lemma mat_piter_cost A fuel (body : A -> mat_run A) width price :
  (forall state, mat_cost (body state) width price) ->
  forall state, mat_cost (mat_piter fuel body state) width
    (price * Pos.to_nat fuel + 100 * (2 * Pos.to_nat fuel - 1)).
Proof.
  intro Hbody. induction fuel as [fuel IH | fuel IH |]; intro state.
  - cbn [mat_piter]. rewrite Pos2Nat.inj_xI.
    eapply mat_cost_mono.
    + apply mat_mark_cost. eapply mat_bind_cost; [apply IH |]. intro mid.
      eapply mat_bind_cost; [apply IH | apply Hbody].
    + pose proof (Pos2Nat.is_pos fuel). nia.
  - cbn [mat_piter]. rewrite Pos2Nat.inj_xO.
    eapply mat_cost_mono.
    + apply mat_mark_cost. eapply mat_bind_cost; [apply IH | apply IH].
    + pose proof (Pos2Nat.is_pos fuel). nia.
  - cbn [mat_piter].
    eapply mat_cost_mono; [apply mat_mark_cost, Hbody |]. cbn [Pos.to_nat]. lia.
Qed.

(** Binary iteration also charges the zero-fuel branch and its outer marker. *)
Lemma mat_niter_cost A fuel (body : A -> mat_run A) width price :
  (forall state, mat_cost (body state) width price) ->
  forall state, mat_cost (mat_niter fuel body state) width
    (200 + (price + 200) * N.to_nat fuel).
Proof.
  intros Hbody state. destruct fuel as [|fuel].
  - cbn [mat_niter N.to_nat]. rewrite Nat.mul_0_r.
    apply mat_mark_cost, mat_return_cost.
  - unfold mat_niter. eapply mat_cost_mono.
    + apply mat_mark_cost. apply mat_piter_cost, Hbody.
    + change (100 + (price * Pos.to_nat fuel + 100 * (2 * Pos.to_nat fuel - 1)) <=
        200 + (price + 200) * Pos.to_nat fuel). nia.
Qed.

(** Bit-length prices are bounded by their nonnegative mathematical operand. *)
Lemma mat_z_bits_bound n : audit_z_bits (Z.of_N n) <= S (N.to_nat n).
Proof.
  unfold audit_z_bits. rewrite Z.abs_eq by lia.
  apply le_n_S.
  assert (Hlog : (Z.log2 (Z.of_N n) <= Z.of_N n)%Z).
  { apply Z.log2_le_lin. lia. }
  apply Z2Nat.inj_le in Hlog; try apply Z.log2_nonneg; try lia.
Qed.

(** A bind's complete trace retains each of its actual local widths. *)
Lemma mat_bind_width A B (run : mat_run A) (next : A -> mat_run B) width :
  mat_width (snd (mat_bind run next)) <= width ->
  mat_width (snd run) <= width /\ mat_width (snd (next (fst run))) <= width.
Proof.
  destruct run as [value events]. destruct (next value) as [out tail] eqn:Hnext.
  unfold mat_bind. rewrite Hnext. cbn [fst snd]. rewrite Hnext.
  cbn [snd]. rewrite mat_width_app. lia.
Qed.

(** A bind's work is the sum of its actual source segments. *)
Lemma mat_bind_work A B (run : mat_run A) (next : A -> mat_run B) :
  mat_work (snd (mat_bind run next)) =
    mat_work (snd run) + mat_work (snd (next (fst run))).
Proof.
  destruct run as [value events]. destruct (next value) as [out tail] eqn:Hnext.
  unfold mat_bind. rewrite Hnext. cbn [fst snd]. rewrite Hnext.
  cbn [snd]. apply mat_work_app.
Qed.

(** Accepted finishing repeats node collection and reads every captured level before its maximum. *)
Lemma mat_stratify_finish_cost P (prog : program P) levels (done : bool) width :
  length (fst (mat_rule_nodes prog)) <= width ->
  mat_cost (mat_mark 86 (
    if done then
      nodes <- mat_rule_nodes prog;;
      values <- mat_map (mat_level_at (penc prog) levels) nodes;;
      maximum <- mat_foldr (fun n m => mat_nat 25 Nat.max n m) values 0%nat;;
      bound <- mat_nat 26 Nat.add maximum 1%nat;;
      mat_return (Some (MatCapturedLevels (penc prog) levels bound))
    else mat_return None)) width
    (3000 * S (mat_stratify_input_size prog) * S width * S width).
Proof.
  intro Hlength. destruct done.
  - eapply mat_cost_mono.
    + apply mat_mark_cost. eapply mat_bind_cost_at; [apply mat_rule_nodes_cost |].
      eapply mat_bind_cost_at.
      * apply mat_map_cost. intro key. apply mat_level_at_cost.
      * eapply mat_bind_cost.
        -- apply mat_foldr_cost. intros value acc. apply mat_nat_cost.
        -- intro maximum. eapply mat_bind_cost; [apply mat_nat_cost |]. intro bound.
           apply mat_return_cost.
    + rewrite mat_map_erases, length_map. nia.
  - eapply mat_cost_mono; [apply mat_mark_cost, mat_return_cost |]. nia.
Qed.

(** An emitted frame pays its fixed, actual work field. *)
Lemma mat_emit_cost frame width : mat_cost (mat_emit frame) width (mat_frame_work frame).
Proof.
  unfold mat_cost. intro Hwidth. change (mat_frame_work frame + 0 <= mat_frame_work frame). lia.
Qed.

(** Scalar composition covers setup, squared fuel, all ticks and the accepted finishing pass. *)
Lemma mat_stratify_scalar_cost size width count bits square_bits :
  count <= width -> bits <= S count -> square_bits <= S (count * count) ->
  2000 * S size * S width * S width +
    (1 + count + 0 + (S count + (1 + bits * bits +
      (1 + square_bits + 1 + (200 +
        (4000 * S size * S width + 200) * S (count * count) +
        3000 * S size * S width * S width))))) <=
    (2000 * 10) * S size * Nat.pow (S width) 4.
Proof.
  intros Hcount Hbits Hsquare.
  assert (Hbits2 : bits * bits <= S width * S width).
  { apply Nat.mul_le_mono; lia. }
  assert (Hfuel : S (count * count) <= S width * S width) by nia.
  assert (Hiteration : (4000 * S size * S width + 200) * S (count * count) <=
    4200 * S size * S width * (S width * S width)).
  { apply Nat.mul_le_mono; [nia | exact Hfuel]. }
  assert (Hbase : S width <= S width * S width) by nia.
  assert (Hgrow : S size * S width * S width <= S size * S width * (S width * S width)).
  { apply Nat.mul_le_mono_l. exact Hbase. }
  assert (Hpower : S width * (S width * S width) <=
    S width * (S width * (S width * (S width * 1)))).
  { nia. }
  pose proof (Nat.mul_le_mono_l _ _ (S size) Hpower) as Hscaled.
  cbn [Nat.pow]. nia.
Qed.

(** The whole source trace bounds all strict traversals and every binary-fuel call. *)
Lemma mat_stratify_cost P (prog : program P) width :
  mat_cost (mat_stratify prog) width
    ((2000 * 10) * S (mat_stratify_input_size prog) * Nat.pow (S width) 4).
Proof.
  unfold mat_cost. intro Hwidth.
  pose proof Hwidth as Hcount.
  unfold mat_stratify in Hcount.
  apply mat_bind_width in Hcount. destruct Hcount as [_ Hcount].
  apply mat_bind_width in Hcount. destruct Hcount as [Hcount _].
  change (Nat.max 1 (1 + length (fst (mat_rule_nodes prog)) + 0) <= width) in Hcount.
  assert (Hlength : length (fst (mat_rule_nodes prog)) <= width) by lia.
  assert (Hcost : mat_cost (mat_stratify prog) width
    ((2000 * 10) * S (mat_stratify_input_size prog) * Nat.pow (S width) 4)).
  { clear Hwidth Hcount. unfold mat_stratify. eapply mat_cost_mono.
    - eapply mat_bind_cost_at; [apply mat_rule_nodes_cost |].
      eapply mat_bind_cost_at; [apply mat_emit_cost |].
      eapply mat_bind_cost_at; [apply mat_emit_cost |].
      eapply mat_bind_cost_at; [apply mat_emit_cost |].
      eapply mat_bind_cost_at; [apply mat_emit_cost |].
      eapply mat_bind_cost.
      + apply mat_niter_cost. intro state. apply mat_stratify_tick_cost.
      + intros [levels done]. apply mat_stratify_finish_cost. exact Hlength.
    - cbn [fst mat_frame_work].
      rewrite N2Nat.inj_succ, N2Nat.inj_mul, Nat2N.id.
      pose proof (mat_z_bits_bound (N.of_nat (length (fst (mat_rule_nodes prog))))) as Hbits.
      pose proof (mat_z_bits_bound
        ((N.of_nat (length (fst (mat_rule_nodes prog))) *
          N.of_nat (length (fst (mat_rule_nodes prog)))))%N) as Hsquare.
      rewrite Nat2N.id in Hbits.
      rewrite N2Nat.inj_mul, !Nat2N.id in Hsquare.
      unfold audit_unary_conversion_weight, audit_multiply_weight, audit_binary_weight.
      change (audit_z_bits 0) with 1.
      apply mat_stratify_scalar_cost; assumption. }
  exact (Hcost Hwidth).
Qed.

(** Original occurrence counts, actual operand widths and fixed source prices bound work. *)
Theorem mat_stratify_bound : mat_stratify_bound_statement.
Proof.
  intros P prog.
  pose proof (mat_stratify_cost P prog (mat_width (snd (mat_stratify prog)))) as Hcost.
  unfold mat_cost in Hcost. specialize (Hcost (Nat.le_refl _)).
  assert (Hcoefficient : 2000 * 10 <= N.to_nat 100000000%N).
  { change (N.to_nat 20000%N <= N.to_nat 100000000%N).
    assert (Hcompare : Nat.compare (N.to_nat 20000%N) (N.to_nat 100000000%N) = Lt).
    { rewrite <- N2Nat.inj_compare. reflexivity. }
    apply Nat.compare_lt_iff in Hcompare. lia. }
  assert (Hpower : Nat.pow (S (mat_width (snd (mat_stratify prog)))) 4 <=
    Nat.pow (S (mat_width (snd (mat_stratify prog)))) 12).
  { apply Nat.pow_le_mono_r; lia. }
  destruct (mat_stratify prog) as [out events]. cbn [snd] in *.
  eapply Nat.le_trans; [exact Hcost |].
  apply Nat.mul_le_mono; [apply Nat.mul_le_mono_r; exact Hcoefficient | exact Hpower].
Qed.
