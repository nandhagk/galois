(** * Fixed binary-credit memo producer

    This producer threads a binary credit and the exact persistent memo through every child.
    For example, a completed hit preserves its credit while a missing entry with positive credit
    consumes one credit before expansion.
    Builds on: memo branch rules and the well-founded order on binary credit. *)

From Stdlib Require Import List NArith PArith PeanoNat Wf_nat Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Graph Require Import GraphCore GraphPrepare.
From Galois.Views Require Import ViewsMemoryEffects.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryFlow AnalysesMemoryWalk
  AnalysesAuditMemoryState AnalysesAuditMemoryEncoding.
From Galois.Collections Require Import CollectionsAuditMap CollectionsAuditFinSet.
From Galois.Analyses Require Import AnalysesAuditMemoryMemo AnalysesAuditMemoryMemoPlain.
Import List.ListNotations.

Inductive audit_memo_control_event : Type :=
  | AuditMemoEnterCase
  | AuditMemoChildrenCase
  | AuditMemoCreditCase (input : N)
  | AuditMemoPredPositiveCase (input : positive)
  | AuditMemoPredDoubleCase (input : positive).

Fixpoint audit_memo_pred_double (input : positive)
    : positive * list audit_memo_control_event :=
  match input with
  | xH => (xH, [AuditMemoPredDoubleCase input])
  | xI p => (xI (xO p), [AuditMemoPredDoubleCase input])
  | xO p =>
      let '(result, events) := audit_memo_pred_double p in
      (xI result, AuditMemoPredDoubleCase input :: events)
  end.

Definition audit_memo_pred (input : N) : N * list audit_memo_control_event :=
  match input with
  | N0 => (N0, [AuditMemoCreditCase input])
  | Npos xH => (N0, [AuditMemoCreditCase input; AuditMemoPredPositiveCase xH])
  | Npos (xI p) =>
      (Npos (xO p), [AuditMemoCreditCase input; AuditMemoPredPositiveCase (xI p)])
  | Npos (xO p) =>
      let '(result, events) := audit_memo_pred_double p in
      (Npos result, [AuditMemoCreditCase input; AuditMemoPredPositiveCase (xO p)] ++ events)
  end.

(** The counted predecessor returns N.pred and its control-event charge is bounded by the input
    bit size. *)
Definition audit_memo_pred_correct_statement : Prop :=
  forall input, fst (audit_memo_pred input) = N.pred input /\
    2 * length (snd (audit_memo_pred input)) <=
      4 + 2 *
        match input with
        | N0 => 0
        | Npos p => Pos.size_nat p
        end.

Record audit_memo_execution (N E CV CK NE : Type) : Type := AuditMemoExecution {
  audit_memo_value : memory_clobber_result N E;
  audit_memo_cache : Map.t (positive * memory_version N E) (memo_entry N E);
  audit_memo_credit : BinNums.N;
  audit_memo_body_events : list (audit_memo_event N E CV CK NE);
  audit_memo_control_events : list audit_memo_control_event
}.

Arguments AuditMemoExecution {N E CV CK NE} _ _ _ _ _.
Arguments audit_memo_value {N E CV CK NE} _.
Arguments audit_memo_cache {N E CV CK NE} _.
Arguments audit_memo_credit {N E CV CK NE} _.
Arguments audit_memo_body_events {N E CV CK NE} _.
Arguments audit_memo_control_events {N E CV CK NE} _.

Section Execute.
  Context {N E CV CK NE : Type}.
  Let V := memory_version N E.
  Let M := Map.t (positive * V) (memo_entry N E).
  Let R := audit_memo_execution N E CV CK NE.
  Variable version_enc : V -> positive * list CV.
  Variable key_enc : (positive * V) -> positive * list CK.
  Variable scope : positive.
  Variable next : V -> list V * list NE.

  (** The remaining credit of an execution is at most its supplied fuel. *)
  Definition audit_memo_credit_bounded (fuel : BinNums.N) (run : R) : Prop :=
    (N.to_nat (audit_memo_credit run) <= N.to_nat fuel)%nat.

  (** Given credit below the bound and a smaller-credit oracle, child recursion returns credit
    bounded by its input. *)
  Fixpoint audit_memo_execute_children (bound : BinNums.N)
      (recur : forall credit, (N.to_nat credit < N.to_nat bound)%nat ->
        FinSet.t V -> M -> V -> {run : R | audit_memo_credit_bounded credit run})
      (active : FinSet.t V) (memo : M) (versions : list V) (credit : BinNums.N)
      (Hcredit : (N.to_nat credit < N.to_nat bound)%nat)
      {struct versions} : {run : R | audit_memo_credit_bounded credit run}.
  Proof.
    destruct versions as [| v rest].
    - exists (AuditMemoExecution (MemoryClobberResult [] true) memo credit []
        [AuditMemoChildrenCase]).
      apply Nat.le_refl.
    - destruct (recur credit Hcredit active memo v) as [one Hone].
      assert (Hsmaller : (N.to_nat (audit_memo_credit one) < N.to_nat bound)%nat).
      { unfold audit_memo_credit_bounded in Hone. lia. }
      destruct (audit_memo_execute_children bound recur active (audit_memo_cache one) rest
        (audit_memo_credit one) Hsmaller) as [tail Htail].
      destruct (audit_memo_union version_enc (clobber_roots (audit_memo_value one))
        (clobber_roots (audit_memo_value tail))) as [roots [build enumeration]].
      exists (AuditMemoExecution
        (MemoryClobberResult roots (andb (clobber_complete (audit_memo_value one))
          (clobber_complete (audit_memo_value tail))))
        (audit_memo_cache tail) (audit_memo_credit tail)
        (audit_memo_body_events one ++ audit_memo_body_events tail ++
          [AuditMemoUnion (clobber_roots (audit_memo_value one))
            (clobber_roots (audit_memo_value tail)) roots build enumeration])
        (AuditMemoChildrenCase :: audit_memo_control_events one ++ audit_memo_control_events tail)).
      unfold audit_memo_credit_bounded in *. cbn. lia.
  Defined.

  (** Given a smaller-credit oracle, the counted body returns remaining credit bounded by its
    fuel. *)
  Definition audit_memo_execute_body (fuel : BinNums.N)
      (recur : forall credit, (N.to_nat credit < N.to_nat fuel)%nat ->
        FinSet.t V -> M -> V -> {run : R | audit_memo_credit_bounded credit run})
      (active : FinSet.t V) (memo : M) (v : V) :
      {run : R | audit_memo_credit_bounded fuel run}.
  Proof.
    destruct (audit_finset_mem version_enc v active) as [is_active ae].
    destruct is_active.
    - exists (AuditMemoExecution (MemoryClobberResult [v] false) memo fuel
        [AuditMemoActive v true ae] [AuditMemoEnterCase]).
      apply Nat.le_refl.
    - destruct (audit_map_get key_enc (scope, v) memo) as [entry le].
      destruct entry as [[| roots] |].
      + exists (AuditMemoExecution (MemoryClobberResult [v] false) memo fuel
          [AuditMemoActive v false ae; AuditMemoLookup v (Some MemoBusy) le]
          [AuditMemoEnterCase]).
        apply Nat.le_refl.
      + exists (AuditMemoExecution (MemoryClobberResult roots true) memo fuel
          [AuditMemoActive v false ae; AuditMemoLookup v (Some (MemoDone roots)) le]
          [AuditMemoEnterCase]).
        apply Nat.le_refl.
      + destruct fuel as [| positive_fuel].
        * exists (AuditMemoExecution (MemoryClobberResult [v] false) memo 0%N
            [AuditMemoActive v false ae; AuditMemoLookup v None le]
            [AuditMemoEnterCase; AuditMemoCreditCase 0%N]).
          apply Nat.le_refl.
        * pose (credit := N.pred (Npos positive_fuel)).
          assert (Hcredit : (N.to_nat credit < N.to_nat (Npos positive_fuel))%nat).
          { unfold credit. rewrite N2Nat.inj_pred.
            cbn. pose proof (Pos2Nat.is_pos positive_fuel) as Hpositive. lia. }
          destruct (next v) as [successors ne].
          destruct successors as [| first rest].
          -- destruct (audit_map_set key_enc (scope, v) (MemoDone [v]) memo) as [final se].
             exists (AuditMemoExecution (MemoryClobberResult [v] true) final credit
               [AuditMemoActive v false ae; AuditMemoLookup v None le;
                AuditMemoExpand v [] ne; AuditMemoStore v [v] se]
               (AuditMemoEnterCase :: snd (audit_memo_pred (Npos positive_fuel)))).
             unfold audit_memo_credit_bounded. cbn. lia.
          -- destruct (audit_finset_add version_enc v active) as [active' adds].
             destruct (audit_memo_execute_children (Npos positive_fuel) recur active' memo
               (first :: rest) credit Hcredit) as [children Hchildren].
             pose (prefix := [AuditMemoActive v false ae; AuditMemoLookup v None le;
               AuditMemoExpand v (first :: rest) ne; AuditMemoAddActive v adds]).
             pose (controls := AuditMemoEnterCase :: snd (audit_memo_pred (Npos positive_fuel)) ++
               audit_memo_control_events children).
             destruct (clobber_complete (audit_memo_value children)).
             ++ destruct (audit_map_set key_enc (scope, v)
                  (MemoDone (clobber_roots (audit_memo_value children)))
                  (audit_memo_cache children)) as [final se].
                exists (AuditMemoExecution (audit_memo_value children) final
                  (audit_memo_credit children)
                  (prefix ++ audit_memo_body_events children ++
                    [AuditMemoStore v (clobber_roots (audit_memo_value children)) se]) controls).
                unfold audit_memo_credit_bounded in *. cbn. lia.
             ++ exists (AuditMemoExecution (audit_memo_value children) (audit_memo_cache children)
                  (audit_memo_credit children) (prefix ++ audit_memo_body_events children)
                    controls).
                unfold audit_memo_credit_bounded in *. cbn. lia.
  Defined.

  Definition audit_memo_execute (fuel : BinNums.N) (active : FinSet.t V) (memo : M) (v : V) : R :=
    proj1_sig (Fix (well_founded_ltof BinNums.N N.to_nat)
      (fun credit => forall active memo v,
        {run : R | audit_memo_credit_bounded credit run})
      audit_memo_execute_body fuel active memo v).

  (** Execution yields a memo-tree derivation with its result, final cache, remaining credit
    and body events. *)
  Definition audit_memo_execute_tree_at : Prop :=
    forall fuel active memo v,
      let run := audit_memo_execute fuel active memo v in
      audit_memo_tree version_enc key_enc scope next active memo v fuel
        (audit_memo_value run) (audit_memo_cache run) (audit_memo_credit run)
        (audit_memo_body_events run).
End Execute.

(** The computed memo run inhabits the tree relation at its exact returned endpoints. *)
Definition audit_memo_execute_tree_statement : Prop :=
  forall N E CV CK NE version_enc key_enc scope next,
    @audit_memo_execute_tree_at N E CV CK NE version_enc key_enc scope next.

(** This fixed public query uses the saved adjacency and effect table and updates only its memo. *)
Definition audit_memory_memo_query {N E T}
    (EN : CollectionsEncoding.encoding N) (EE : CollectionsEncoding.encoding E)
    (ET : CollectionsEncoding.encoding T) (g : GraphCore.Graph.t N E)
    (effects : E -> list (ViewsMemoryEffects.memory_effect T)) (mg : memory_graph N E)
    (state : memo_state EN g effects mg) (q : ViewsMemoryEffects.memory_scope T)
    (start : memory_version N E) (fuel : positive) :
    memory_clobber_result N E * memo_state EN g effects mg :=
  let next := memory_walk_raw_next EE ET (@memo_effect_index N E T EN g effects mg state)
    (pred_edges (@memo_adjacency N E T EN g effects mg state)) mg q in
  let run := audit_memo_compute (memory_version_encoding EN EE) (memo_key EN EE)
    (scope_code ET q) next (Npos fuel) FinSet.empty
    (@memo_entries N E T EN g effects mg state) start in
  (audit_plain_memo_value run,
    @MemoState N E T EN g effects mg (@memo_adjacency N E T EN g effects mg state)
      (@memo_effect_index N E T EN g effects mg state) (audit_plain_memo_cache run)).

(** The concrete query preserves valid caches, covers traces and supports complete results,
    execution witnesses, memo hits, storage and repeat queries. *)
Definition audit_memory_memo_query_semantics_statement : Prop :=
  memo_preserved_statement (@audit_memory_memo_query) /\
  memo_coverage_statement (@audit_memory_memo_query) /\
  memo_complete_statement (@audit_memory_memo_query) /\
  memo_execution_statement (@audit_memory_memo_query) /\
  memo_hit_statement (@audit_memory_memo_query) /\
  memo_store_complete_statement (@audit_memory_memo_query) /\
  memo_second_query_statement (@audit_memory_memo_query).

Example audit_memo_pred_borrow_fixture :
  audit_memo_pred 8%N =
    (7%N, [AuditMemoCreditCase 8%N; AuditMemoPredPositiveCase 8%positive;
      AuditMemoPredDoubleCase 4%positive; AuditMemoPredDoubleCase 2%positive;
      AuditMemoPredDoubleCase 1%positive]).
Proof.
  reflexivity.
Qed.

Example audit_memo_execute_zero_credit_fixture :
  let enc := fun _ : memory_version positive positive => (1%positive, @nil unit) in
  let key_enc := fun _ : positive * memory_version positive positive => (1%positive, @nil unit) in
  let next := fun _ : memory_version positive positive => ([], @nil unit) in
  let run := audit_memo_execute enc key_enc 1%positive next 0%N FinSet.empty Map.empty MemoryLive in
  audit_memo_value run = MemoryClobberResult [MemoryLive] false /\
  audit_memo_credit run = 0%N.
Proof.
  vm_compute.
  split; reflexivity.
Qed.

Example audit_memo_execute_terminal_fixture :
  let enc := fun _ : memory_version positive positive => (1%positive, @nil unit) in
  let key_enc := fun _ : positive * memory_version positive positive => (1%positive, @nil unit) in
  let next := fun _ : memory_version positive positive => ([], @nil unit) in
  let run := audit_memo_execute enc key_enc 1%positive next 1%N FinSet.empty Map.empty MemoryLive in
  audit_memo_value run = MemoryClobberResult [MemoryLive] true /\
  audit_memo_credit run = 0%N /\ length (audit_memo_control_events run) = 3.
Proof.
  vm_compute.
  repeat split; reflexivity.
Qed.

Example audit_memo_execute_done_preserves_credit_fixture :
  let enc := fun _ : memory_version positive positive => (1%positive, @nil unit) in
  let key_enc := fun _ : positive * memory_version positive positive => (1%positive, @nil unit) in
  let next := fun _ : memory_version positive positive => ([MemoryLive], @nil unit) in
  let saved := fst (audit_map_set key_enc (1%positive, MemoryLive) (MemoDone [MemoryLive])
    Map.empty) in
  let run := audit_memo_execute enc key_enc 1%positive next 8%N FinSet.empty saved MemoryLive in
  audit_memo_value run = MemoryClobberResult [MemoryLive] true /\
  audit_memo_credit run = 8%N /\ audit_memo_cache run = saved /\
  audit_memo_control_events run = [AuditMemoEnterCase].
Proof.
  vm_compute.
  repeat split; reflexivity.
Qed.
