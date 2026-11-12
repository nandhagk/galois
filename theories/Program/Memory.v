(** * Ordered memory presentations

    Edge effects are stored in a trie keyed by edge identity.
    For example, an absent binding gives an empty effect sequence.
    Builds on: Program.MemorySig and Base.Trie. *)

From Stdlib Require Import List.
From Galois.Base Require Import KeySig Trie.
From Galois.Program Require Import CfgSig SemanticsSig MemorySig.

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

Module MemorySound (P : TYPE) (N : KEY) (E : TYPE) (C : CFG P N E)
    (R : KEY) (A : ALIAS R) (V : MEMORY P N E C R A)
    (M : SEMANTICS P) (T : TRACES P M) (L : CFG_LINK P N E C M) (Loc Val : TYPE)
    (B : MEMORY_LINK P N E C R A V M T L Loc Val)
    <: MEMORY_SOUND P N E C R A V M T L Loc Val B.
  Lemma trace_byte_covered :
    (forall x y : Val.t, {x = y} + {x <> y}) ->
    forall b effects states b', effect_trace_states B.effect_step b effects states b' ->
    forall l address, B.effect_address b l = Some address ->
      B.effect_value b' l <> B.effect_value b l ->
      exists a r, In a effects /\ In r (effect_writes A.all a) /\ B.region_holds r address.
  Proof.
    intros eq b effects states b' Htrace.
    induction Htrace as [b|b a middle rest states last Hstep Htrace IH];
      intros l address Hsite Hchanged.
    - exfalso; apply Hchanged; reflexivity.
    - destruct (eq (B.effect_value middle l) (B.effect_value b l)) as [Hequal|Hdifferent].
      + destruct (IH l address (B.effect_site_stable b a middle l address Hstep Hsite))
          as [writer [r [Hin [Hr Hcovers]]]].
        * rewrite Hequal; exact Hchanged.
        * exists writer, r; split; [right; exact Hin|split; assumption].
      + destruct (B.effect_byte_frame b a middle l address Hstep Hsite Hdifferent)
          as [r [Hr Hcovers]].
        exists a, r; split; [left; reflexivity|split; assumption].
  Qed.

  Lemma transition_byte_covered :
    (forall x y : Val.t, {x = y} + {x <> y}) ->
    forall p s tr t e l address,
      reachable (M.initial p) (M.step p) s -> T.lstep p s tr t -> L.taken p s t e ->
      B.effect_address (B.effect_snapshot s) l = Some address ->
      B.effect_value (B.effect_snapshot t) l <> B.effect_value (B.effect_snapshot s) l ->
      exists a r, In a (V.effects p e) /\ In r (effect_writes A.all a) /\
        B.region_holds r address.
  Proof.
    intros eq p s tr t e l address Hreachable Hstep Htaken Hsite Hchanged.
    destruct (B.effect_step_trace p s tr t e Hreachable Hstep Htaken)
      as [states [Htrace [Hreads Hwrites]]].
    eapply trace_byte_covered; eassumption.
  Qed.

  Lemma disjoint_region_frame :
    (forall x y : Val.t, {x = y} + {x <> y}) ->
    forall p s tr t e region l address,
      reachable (M.initial p) (M.step p) s -> T.lstep p s tr t -> L.taken p s t e ->
      B.effect_address (B.effect_snapshot s) l = Some address ->
      B.region_holds region address ->
      (forall a r, In a (V.effects p e) -> In r (effect_writes A.all a) ->
        A.disjoint region r = true) ->
      B.effect_value (B.effect_snapshot t) l = B.effect_value (B.effect_snapshot s) l.
  Proof. Admitted.

  Lemma transition_read_covered : forall p s tr t e l,
    reachable (M.initial p) (M.step p) s -> T.lstep p s tr t -> L.taken p s t e ->
    B.transition_read p s tr t l -> exists states i b a,
      effect_trace_states B.effect_step (B.effect_snapshot s) (V.effects p e) states
        (B.effect_snapshot t) /\ nth_error states i = Some b /\
      nth_error (V.effects p e) i = Some a /\ B.effect_read b a l /\
      forall address, B.effect_address b l = Some address ->
        exists r, In r (effect_reads A.all a) /\ B.region_holds r address.
  Proof. Admitted.

  Lemma transition_write_covered : forall p s tr t e address,
    reachable (M.initial p) (M.step p) s -> T.lstep p s tr t -> L.taken p s t e ->
    B.transition_write p s tr t address -> exists states i b a r,
      effect_trace_states B.effect_step (B.effect_snapshot s) (V.effects p e) states
        (B.effect_snapshot t) /\ nth_error states i = Some b /\
      nth_error (V.effects p e) i = Some a /\ B.effect_write b a address /\
      In r (effect_writes A.all a) /\ B.region_holds r address.
  Proof. Admitted.
End MemorySound.
