(** * Untraced binary-credit memo computation

    This fixed computational body contains no source-event fields or log construction.
    For example, a completed cache hit returns its roots, original cache and unchanged credit.
    Builds on: memory versions, persistent maps and sets, and binary-credit well-founded
      recursion. *)

From Stdlib Require Import List NArith PArith PeanoNat Wf_nat Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryFlow AnalysesMemoryWalk
  AnalysesAuditMemoryState AnalysesAuditMemoryEncoding.
Import List.ListNotations.

Record audit_plain_memo_result (N E : Type) : Type := AuditPlainMemoResult {
  audit_plain_memo_value : memory_clobber_result N E;
  audit_plain_memo_cache : Map.t (positive * memory_version N E) (memo_entry N E);
  audit_plain_memo_credit : BinNums.N
}.
Arguments AuditPlainMemoResult {N E} _ _ _.
Arguments audit_plain_memo_value {N E} _.
Arguments audit_plain_memo_cache {N E} _.
Arguments audit_plain_memo_credit {N E} _.

Section PlainMemo.
  Context {N E : Type}.
  Let V := memory_version N E.
  Let M := Map.t (positive * V) (memo_entry N E).
  Let R := audit_plain_memo_result N E.
  Variable version_encoding : encoding V.
  Variable key_encoding : encoding (positive * V).
  Variable scope : positive.
  Variable next : V -> list V.

  (** Remaining credit in a plain memo execution does not exceed its input fuel. *)
  Definition audit_plain_memo_bounded (fuel : BinNums.N) (run : R) : Prop :=
    (N.to_nat (audit_plain_memo_credit run) <= N.to_nat fuel)%nat.

  (** Given credit below the bound and a smaller-credit oracle, child recursion returns credit
    bounded by its input. *)
  Fixpoint audit_plain_memo_children (bound : BinNums.N)
      (recur : forall credit, (N.to_nat credit < N.to_nat bound)%nat ->
        FinSet.t V -> M -> V -> {run : R | audit_plain_memo_bounded credit run})
      (active : FinSet.t V) (memo : M) (versions : list V) (credit : BinNums.N)
      (Hcredit : (N.to_nat credit < N.to_nat bound)%nat)
      {struct versions} : {run : R | audit_plain_memo_bounded credit run}.
  Proof.
    destruct versions as [| v rest].
    - exists (AuditPlainMemoResult (MemoryClobberResult [] true) memo credit).
      apply Nat.le_refl.
    - destruct (recur credit Hcredit active memo v) as [one Hone].
      assert (Hsmaller : (N.to_nat (audit_plain_memo_credit one) < N.to_nat bound)%nat).
      { unfold audit_plain_memo_bounded in Hone. lia. }
      destruct (audit_plain_memo_children bound recur active (audit_plain_memo_cache one) rest
        (audit_plain_memo_credit one) Hsmaller) as [tail Htail].
      let roots := constr:(FinSet.elements (FinSet.of_list version_encoding
        (clobber_roots (audit_plain_memo_value one) ++ clobber_roots (audit_plain_memo_value
          tail)))) in
      exists (AuditPlainMemoResult
        (MemoryClobberResult roots (andb (clobber_complete (audit_plain_memo_value one))
          (clobber_complete (audit_plain_memo_value tail))))
        (audit_plain_memo_cache tail) (audit_plain_memo_credit tail)).
      unfold audit_plain_memo_bounded in *. cbn. lia.
  Defined.

  (** Given a smaller-credit oracle, the plain body returns remaining credit bounded by its fuel. *)
  Definition audit_plain_memo_body (fuel : BinNums.N)
      (recur : forall credit, (N.to_nat credit < N.to_nat fuel)%nat ->
        FinSet.t V -> M -> V -> {run : R | audit_plain_memo_bounded credit run})
      (active : FinSet.t V) (memo : M) (v : V) :
      {run : R | audit_plain_memo_bounded fuel run}.
  Proof.
    destruct (FinSet.mem version_encoding v active).
    - exists (AuditPlainMemoResult (MemoryClobberResult [v] false) memo fuel).
      apply Nat.le_refl.
    - destruct (Map.get key_encoding (scope, v) memo) as [[| roots] |].
      + exists (AuditPlainMemoResult (MemoryClobberResult [v] false) memo fuel).
        apply Nat.le_refl.
      + exists (AuditPlainMemoResult (MemoryClobberResult roots true) memo fuel).
        apply Nat.le_refl.
      + destruct fuel as [| positive_fuel].
        * exists (AuditPlainMemoResult (MemoryClobberResult [v] false) memo 0%N).
          apply Nat.le_refl.
        * pose (credit := N.pred (Npos positive_fuel)).
          assert (Hcredit : (N.to_nat credit < N.to_nat (Npos positive_fuel))%nat).
          { unfold credit. rewrite N2Nat.inj_pred.
            cbn. pose proof (Pos2Nat.is_pos positive_fuel) as Hpositive. lia. }
          destruct (next v) as [| first rest].
          -- exists (AuditPlainMemoResult (MemoryClobberResult [v] true)
               (Map.set key_encoding (scope, v) (MemoDone [v]) memo) credit).
             unfold audit_plain_memo_bounded. cbn. lia.
          -- destruct (audit_plain_memo_children (Npos positive_fuel) recur
               (FinSet.add version_encoding v active) memo (first :: rest) credit Hcredit)
               as [children Hchildren].
             exists (AuditPlainMemoResult (audit_plain_memo_value children)
               (if clobber_complete (audit_plain_memo_value children) then
                  Map.set key_encoding (scope, v) (MemoDone (clobber_roots
                    (audit_plain_memo_value children))) (audit_plain_memo_cache children)
                else audit_plain_memo_cache children) (audit_plain_memo_credit children)).
             unfold audit_plain_memo_bounded in *. cbn. lia.
  Defined.

  Definition audit_memo_compute (fuel : BinNums.N) (active : FinSet.t V) (memo : M) (v : V) : R :=
    proj1_sig (Fix (well_founded_ltof BinNums.N N.to_nat)
      (fun credit => forall active memo v,
        {run : R | audit_plain_memo_bounded credit run}) audit_plain_memo_body fuel active memo v).
End PlainMemo.

Example audit_plain_memo_terminal_fixture :
  let version_encoding := memory_version_encoding positive_encoding positive_encoding in
  let key_encoding := pair_encoding positive_encoding version_encoding in
  let run := audit_memo_compute version_encoding key_encoding 1%positive
    (fun _ => []) 1%N FinSet.empty Map.empty MemoryLive in
  audit_plain_memo_value run = MemoryClobberResult [MemoryLive] true /\
    audit_plain_memo_credit run = 0%N.
Proof.
  vm_compute.
  split; reflexivity.
Qed.
