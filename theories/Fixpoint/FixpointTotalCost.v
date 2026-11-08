(** * Primitive budgets for unprioritized joining

    Numeric bounds compose encoder, metadata, query and lattice callback duties on finite keys.
    For example, repeated row occurrences are charged in both preparation and read incidence.
    Builds on: FixpointIndexCost, FixpointTotalPotential and public trie operation costs. *)

From Stdlib Require Import List Bool Arith NArith PArith Lia.
From Galois.Cost Require Import CostMonad CostList CostLoop CostBound.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet BaseIndex.
From Galois.Lattice Require Import LatticeCore LatticeHeight.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointEval FixpointIndex
  FixpointIndexCost FixpointAnalysis FixpointTotalQueue FixpointTotalKernel
  FixpointTotalInvariant FixpointTotalPotential FixpointTotal.
Import List.ListNotations Cost.Notations.
Open Scope N_scope.

Module TotalCost.

Module Budget.

(** Budgets bound primitive calls and selected query/output sizes, independently of complete runs. *)
Record t := Make {
  metadata : SystemIndexCost.Budget.t;
  row_encoder : N;
  row_digits : N;
  lattice_ticks : N;
  rhs_ticks : N;
  nodes : nat;
  continuation : N;
  outputs : nat
}.

Definition key b := 1 + SystemIndexCost.Budget.encoder_ticks (metadata b) +
  SystemIndexCost.Budget.key_digits (metadata b).
Definition row_key b := 1 + row_encoder b + row_digits b.
Definition enqueue b := 1 + 2 * row_key b.
Definition rule b := 2 + 2 * key b + 2 * lattice_ticks b.
Definition evaluation b := 2 + SystemIndexCost.Budget.target_ticks (metadata b) +
  rhs_ticks b + N.of_nat (nodes b) * (3 + key b + continuation b).
Definition update b rows := rule b + key b + N.of_nat rows * enqueue b.
Definition step b rows := row_key b + evaluation b +
  N.of_nat (outputs b) * (1 + update b rows).

End Budget.
Import Budget.

(** Metadata keys are finite declared inputs and outputs of listed source rows. *)
Definition key_domain {X C A} (a : Analysis.t X C A) x :=
  exists c, In c (System.constraints (Analysis.system a)) /\
    (In x (System.target (Analysis.system a) c :: side_targets (Analysis.static a) c) \/
      In x (deps (Analysis.static a) c)).

(** The model asks for primitive duties and never assumes any engine operation's cost. *)
Record model {X C A} (a : Analysis.t X C A) (b : Budget.t) : Prop := {
  metadata_model : SystemIndexCost.cost_model (Analysis.key_enc a) (Analysis.system a)
    (Analysis.static a) (System.constraints (Analysis.system a)) (Budget.metadata b);
  row_keys : forall c, In c (System.constraints (Analysis.system a)) ->
    Cost.ticks (encode_c (Analysis.row_enc a) c) <= Budget.row_encoder b /\
    key_bits (Analysis.row_enc a) c <= Budget.row_digits b;
  lattice_calls : forall x y,
    Cost.ticks (leb_c (Analysis.lat a) x y) <= Budget.lattice_ticks b /\
    Cost.ticks (join_c (Analysis.lat a) x y) <= Budget.lattice_ticks b;
  rhs_calls : forall c, In c (System.constraints (Analysis.system a)) ->
    Cost.ticks (System.rhs_c (Analysis.system a) c) <= Budget.rhs_ticks b;
  query_paths : forall c s, In c (System.constraints (Analysis.system a)) ->
    exists n, (n <= Budget.nodes b)%nat /\
      Query.within (Budget.continuation b) s n (System.rhs (Analysis.system a) c);
  output_sizes : forall c s, In c (System.constraints (Analysis.system a)) ->
    (length (fst (Eval.outputs (Analysis.system a) c s)) <= Budget.outputs b)%nat
}.

Arguments metadata_model {X C A a b}.
Arguments row_keys {X C A a b}.
Arguments lattice_calls {X C A a b}.
Arguments rhs_calls {X C A a b}.
Arguments query_paths {X C A a b}.
Arguments output_sizes {X C A a b}.

Section Costs.
Context {X C A : Type} (a : Analysis.t X C A) (HL : Analysis.laws a)
  (b : Budget.t) (HB : model a b).

Let EX := Analysis.key_enc a.
Let EC := Analysis.row_enc a.
Let L := Analysis.lat a.
Let S := Analysis.system a.
Let SS := Analysis.static a.
Let cs := System.constraints S.
Let ix := index_system EX S SS.
Let HI := index_system_laws EX (Analysis.key_laws HL) S SS.

Local Lemma key_bounds x :
  key_domain a x ->
  Cost.ticks (encode_c EX x) <= SystemIndexCost.Budget.encoder_ticks (Budget.metadata b) /\
  key_bits EX x <= SystemIndexCost.Budget.key_digits (Budget.metadata b).
Proof.
  intros [c [Hc Hkey]]; exact (SystemIndexCost.key_budget (metadata_model HB) c Hc x Hkey).
Qed.

(** Exact trie lookup cost needs only a finite queried-key budget. *)
Theorem lookup_cost m x :
  key_domain a x -> Cost.ticks (lookup_c EX L m x) <= Budget.key b.
Proof.
  intro Hkey; destruct (key_bounds x Hkey) as [He Hw].
  rewrite FixpointSystem.lookup_cost, Map.get_cost; fold (key_bits EX x).
  unfold Budget.key; lia.
Qed.

(** The shared update rule retains both lattice callbacks and its destination write. *)
Theorem rule_cost m x v :
  key_domain a x ->
  Cost.ticks (Update.rule_c EX L (join_c L) m x v) <= Budget.rule b.
Proof.
  intro Hkey; pose proof (lookup_cost m x Hkey) as Hlookup.
  destruct (key_bounds x Hkey) as [He Hw].
  pose proof (proj1 (lattice_calls HB v (lookup EX L m x))) as Hle.
  pose proof (proj2 (lattice_calls HB (lookup EX L m x) v)) as Hjoin.
  pose proof (Map.set_cost EX x (Cost.value (join_c L (lookup EX L m x) v)) m) as Hwrite.
  fold (key_bits EX x) in Hwrite.
  change (Cost.ticks (leb_c L v (lookup EX L m x)) <= Budget.lattice_ticks b) in Hle.
  change (Cost.ticks (join_c L (lookup EX L m x) v) <= Budget.lattice_ticks b) in Hjoin.
  rewrite Update.rule_cost; destruct (leb L v (lookup EX L m x));
    unfold Budget.rule, Budget.key in *; lia.
Qed.

(** Queue insertion is bounded by its membership and possible write operations. *)
Theorem push_cost c q :
  In c cs -> Cost.ticks (TotalQueue.push_c EC c q) <= 2 * Budget.row_key b.
Proof.
  intro Hc; destruct (row_keys HB c Hc) as [He Hw].
  change (Cost.ticks (encode_c EC c) <= Budget.row_encoder b) in He.
  change (key_bits EC c <= Budget.row_digits b) in Hw.
  rewrite TotalQueue.push_cost, FinSet.mem_cost.
  destruct (FinSet.mem EC c (TotalQueue.queued q)); rewrite ?FinSet.add_cost;
    fold (key_bits EC c); unfold Budget.row_key; lia.
Qed.

(** Batched enqueue charges every attempted occurrence and its traversal cell. *)
Theorem enqueue_cost rows q :
  incl rows cs ->
  Cost.ticks (TotalQueue.push_many_c EC rows q) <= N.of_nat (length rows) * Budget.enqueue b.
Proof.
  unfold TotalQueue.push_many_c; revert q.
  induction rows as [|c rows IH]; intros q Hrows.
  - rewrite ticks_fold_left_c_nil; cbn [length]; lia.
  - rewrite ticks_fold_left_c_cons; specialize (IH (TotalQueue.push EC c q)
      (fun d Hd => Hrows d (or_intror Hd))).
    pose proof (push_cost c q (Hrows c (or_introl eq_refl))) as Hpush.
    cbn [length]; rewrite Nat2N.inj_succ; unfold Budget.enqueue in *.
    fold (TotalQueue.push EC c q).
    nia.
Qed.

Local Lemma readers_length x : (length (readers_of EX ix x) <= length cs)%nat.
Proof.
  unfold ix; rewrite readers_occurrences by apply Analysis.key_laws, HL.
  apply List.filter_length_le.
Qed.

(** Reader requeue bounds use actual prepared bucket multiplicities. *)
Theorem update_cost s x v :
  key_domain a x ->
  Cost.ticks (TotalKernel.update_c a ix s (x, v)) <= Budget.update b (length cs).
Proof.
  intro Hx.
  pose proof (rule_cost (TotalKernel.current s) x v Hx) as Hrule.
  pose proof (enqueue_cost (readers_of EX ix x) (TotalKernel.queue s)
    (fun c Hc => proj1 (proj1 (readers_agree HI x c) Hc))) as Henqueue.
  pose proof (readers_length x) as Hlength.
  destruct (key_bounds x Hx) as [He Hw].
  assert (Hread : Cost.ticks (readers_of_c EX ix x) <= Budget.key b).
  { rewrite readers_cost, Map.get_cost; fold (key_bits EX x); unfold Budget.key; lia. }
  unfold TotalKernel.update_c; rewrite Cost.ticks_bind.
  cbn [fst snd]; fold EX EC L.
  fold (Update.rule EX L (join_c L) (TotalKernel.current s) x v).
  destruct (snd (Update.rule EX L (join_c L) (TotalKernel.current s) x v));
    rewrite ?Cost.ticks_bind, ?Cost.ticks_ret.
  - fold (readers_of EX ix x).
    unfold Budget.update; nia.
  - unfold Budget.update; nia.
Qed.

(** Applying a finite output list charges each shared-rule and requeue operation. *)
Theorem updates_cost outs s :
  (forall x v, In (x, v) outs -> key_domain a x) ->
  Cost.ticks (TotalKernel.updates_c a ix outs s) <=
    N.of_nat (length outs) * (1 + Budget.update b (length cs)).
Proof.
  unfold TotalKernel.updates_c; revert s.
  induction outs as [|[x v] outs IH]; intros s Hkeys.
  - rewrite ticks_fold_left_c_nil; cbn [length]; lia.
  - rewrite ticks_fold_left_c_cons.
    specialize (IH (TotalKernel.update a ix s (x, v))
      (fun y w Hw => Hkeys y w (or_intror Hw))).
    pose proof (update_cost s x v (Hkeys x v (or_introl eq_refl))) as Hupdate.
    cbn [length]; rewrite Nat2N.inj_succ.
    fold (TotalKernel.update a ix s (x, v)); nia.
Qed.

(** Evaluator budgets follow selected query paths and declared finite-key lookup duties. *)
Theorem evaluation_cost m c :
  In c cs -> Cost.ticks (Eval.outputs_c S (lookup_c EX L m) c) <= Budget.evaluation b.
Proof.
  intro Hc.
  destruct (query_paths HB c (lookup EX L m) Hc) as [n [Hn Hpath]].
  assert (Hlook : forall x, In x (Query.reads (System.rhs S c) (lookup EX L m)) ->
    Cost.ticks (lookup_c EX L m x) <= Budget.key b).
  { intros x Hx; apply lookup_cost; exists c; split; [exact Hc|right].
    exact (System.reads_within (Analysis.static_law HL) c (lookup EX L m) x Hx). }
  pose proof (Query.run_c_cost_on (System.rhs S c) (lookup_c EX L m) (lookup EX L m)
    n (Budget.continuation b) (Budget.key b) Hpath (fun _ => eq_refl) Hlook) as Hquery.
  destruct (SystemIndexCost.callback_budget (metadata_model HB) c Hc) as [Ht _].
  pose proof (rhs_calls HB c Hc) as Hrhs.
  change (Cost.ticks (System.target_c S c) <=
    SystemIndexCost.Budget.target_ticks (Budget.metadata b)) in Ht.
  change (Cost.ticks (System.rhs_c S c) <= Budget.rhs_ticks b) in Hrhs.
  rewrite Eval.outputs_cost; unfold Budget.evaluation; nia.
Qed.

Local Lemma output_key m c x v :
  In c cs -> In (x, v) (fst (Eval.outputs S c (lookup EX L m))) -> key_domain a x.
Proof.
  intros Hc Hin; exists c; split; [exact Hc|left].
  rewrite Eval.outputs_spec in Hin; cbn [fst] in Hin; destruct Hin as [Heq|Hin].
  - injection Heq as <- <-; now left.
  - right; apply (System.sides_within (Analysis.static_law HL) c (lookup EX L m)).
    apply in_map_iff; exists (x, v); split; [reflexivity|exact Hin].
Qed.

(** The complete transition bound is derived from primitive callbacks and numeric incidence. *)
Theorem step_cost HT s :
  TotalInvariant.invariant a HT s ->
  Cost.ticks (TotalKernel.step_c a ix s) <= Budget.step b (length cs).
Proof.
  intros [Hg [Hq [Hlisted Hvalid]]].
  unfold TotalKernel.step_c; rewrite Cost.ticks_bind; fold EC.
  fold (TotalQueue.pop EC (TotalKernel.queue s)).
  fold EX L S.
  rewrite TotalQueue.pop_cost.
  destruct (TotalQueue.pending (TotalKernel.queue s)) as [|c rest] eqn:Hpending.
  - rewrite TotalQueue.pop_equation, Hpending, Cost.ticks_ret; unfold Budget.step; lia.
  - assert (Hc : In c cs).
    { apply Hlisted; now left. }
    destruct (row_keys HB c Hc) as [He Hw].
    change (Cost.ticks (encode_c EC c) <= Budget.row_encoder b) in He.
    change (key_bits EC c <= Budget.row_digits b) in Hw.
    rewrite FinSet.remove_cost; fold (key_bits EC c).
    rewrite TotalQueue.pop_equation, Hpending.
    rewrite Cost.ticks_bind, Cost.ticks_map.
    rewrite (Eval.outputs_c_spec S c _ (lookup EX L (TotalKernel.current s))) by reflexivity.
    pose proof (evaluation_cost (TotalKernel.current s) c Hc) as Heval.
    pose proof (updates_cost (fst (Eval.outputs S c (lookup EX L (TotalKernel.current s))))
      (TotalKernel.State (TotalKernel.current s)
        (TotalQueue.Make rest (FinSet.remove EC c (TotalQueue.queued (TotalKernel.queue s)))))
      (fun x v Hin => output_key (TotalKernel.current s) c x v Hc Hin)) as Hupdates.
    pose proof (output_sizes HB c (lookup EX L (TotalKernel.current s)) Hc) as Houts.
    change (length (fst (Eval.outputs S c (lookup EX L (TotalKernel.current s)))) <=
      Budget.outputs b)%nat in Houts.
    unfold Budget.step, Budget.row_key; nia.
Qed.

End Costs.

End TotalCost.
Import TotalCost.
