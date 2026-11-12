(** * Ordered memory presentations

    Edge effects are stored in a trie keyed by edge identity.
    For example, an absent binding gives an empty effect sequence.
    Builds on: Program.MemorySig and Base.Trie. *)

From Stdlib Require Import List.
From Galois.Base Require Import KeySig Trie.
From Galois.Program Require Import CfgSig MemorySig.

Module Type MEMORY_DATA (P : TYPE) (R : KEY_OPS).
  Parameter effect_table : P.t -> ptrie (list (effect R.t)).
End MEMORY_DATA.

Module MemoryCode (P : TYPE) (N : KEY_OPS) (E : KEY_OPS)
    (C : CFG_OPS P N E) (R : KEY_OPS) (A : ALIAS_OPS R)
    (D : MEMORY_DATA P R) <: MEMORY_OPS P N E C R A.
  Definition effects p e :=
    match trie_get (E.encode e) (D.effect_table p) with
    | Some es => es
    | None => nil
    end.
End MemoryCode.

Module Memory (P : TYPE) (N : KEY) (E : KEY)
    (C : CFG P N E) (R : KEY) (A : ALIAS R)
    (D : MEMORY_DATA P R) <: MEMORY P N E C R A.
  Include MemoryCode P N E C R A D.
  Include MEMORY_SPEC P N E C R A.
End Memory.

Record effect_flags := EffectFlags {
  flag_reads : bool;
  flag_writes : bool;
  flag_may_trap : bool;
  flag_may_diverge : bool;
  flag_may_stop : bool;
  flag_allocates : bool;
  flag_frees : bool;
  flag_calls : bool;
  flag_observes : bool
}.

Module Type EFFECTS_DATA (I : TYPE).
  Parameter flags : I.t -> effect_flags.
End EFFECTS_DATA.

Module EffectsCode (I : TYPE) (D : EFFECTS_DATA I) <: EFFECTS_OPS I.
  Definition reads i := flag_reads (D.flags i).
  Definition writes i := flag_writes (D.flags i).
  Definition may_trap i := flag_may_trap (D.flags i).
  Definition may_diverge i := flag_may_diverge (D.flags i).
  Definition may_stop i := flag_may_stop (D.flags i).
  Definition allocates i := flag_allocates (D.flags i).
  Definition frees i := flag_frees (D.flags i).
  Definition calls i := flag_calls (D.flags i).
  Definition observes i := flag_observes (D.flags i).
End EffectsCode.

Module MemoryEffectLaws (R : KEY) (A : ALIAS R) <: MEMORY_EFFECT_LAWS R A.
  Lemma barrier_read_write :
    effect_reads A.all Barrier = effect_reads A.all (ReadWrite A.all A.all) /\
    effect_writes A.all Barrier = effect_writes A.all (ReadWrite A.all A.all) /\
    effect_is_def (@Barrier R.t) = true.
  Proof.
    repeat split.
  Qed.

  Lemma effect_trace_states_trace : forall B (next : B -> effect R.t -> B -> Prop)
    b effects states b', effect_trace_states next b effects states b' ->
      effect_trace next b effects b'.
  Proof.
    intros B next b effects states b' Htrace.
    induction Htrace; econstructor; eassumption.
  Qed.
End MemoryEffectLaws.
