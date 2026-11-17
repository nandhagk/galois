(** * Ordered memory presentations

    Edge effects are stored in a trie keyed by edge identity.
    For example, an absent binding gives an empty effect sequence.
    Builds on: Program.MemorySig and Base.Trie. *)

From Stdlib Require Import List NArith Lia.
From Argent Require Import Time Tactics Std BigO.
From Galois.Base Require Import KeySig Trie Code.
From Galois.Program Require Import CfgSig SemanticsSig MemorySig.
Import Code.List.

Module Type MEMORY_DATA (P : TYPE) (R : KEY_OPS).
  Parameter effect_table : P.t -> ptrie (list (effect R.t)).
End MEMORY_DATA.

Module Type MEMORY_DATA_TIME (P : TYPE) (R : KEY_T)
    (Import D : MEMORY_DATA P R).
  Parameter T_effect_table : P.t -> N.
  Parameter c_effect_table : N.
  (** Reading the stored effect table has bounded cost. *)
  Parameter T_effect_table_le : forall p, (T_effect_table p <= c_effect_table)%N.
End MEMORY_DATA_TIME.

Module Type MEMORY_DATA_T (P : TYPE) (R : KEY_T) :=
  MEMORY_DATA P R <+ MEMORY_DATA_TIME P R.

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

Module MemoryT (P : TYPE) (N : KEY_T) (E : TYPE)
    (EKey : KEY_T with Definition t := E.t) (C : CFG_T P N E) (R : KEY_T)
    (A : ALIAS_T R) (D : MEMORY_DATA_T P R) <: MEMORY_T P N E C R A.
  Include Memory P N EKey C R A D.
  TimeFun effects.

  Definition c_effects : N := (EKey.c_key + D.c_effect_table + 3)%N.

  (** Effect lookup pays for the encoded edge key and the stored effect table. *)
  Lemma T_effects_le : forall p e,
    (T_effects p e <= c_effects *
      N.of_nat (EKey.bits e + length (effects p e) + 1))%N.
  Proof.
    intros p e. pose proof (D.T_effect_table_le p) as Htable.
    pose proof (EKey.T_encode_le e) as Hencode.
    unfold c_effects. time_unfold T_effects. PTrieT.trie_get_le.
    time_simpl; time_cbn; unfold EKey.bits in *; nia.
  Qed.

  (** Effect lookup is linear in the edge key and the returned effect sequence. *)
  Lemma effects_complexity : bigO (X := P.t * E.t) (fun _ => True)
    (fun '(p, e) => N.of_nat (EKey.bits e + length (effects p e)))
    (fun '(p, e) => T_effects p e).
  Proof.
    apply bigO_intro with (c := c_effects).
    intros [p e] _. pose proof (T_effects_le p e) as Heffects.
    cbn beta iota zeta in *. rewrite Nat2N.inj_add in Heffects. nia.
  Qed.

  TimeFun reads.
  TimeFun writes.
End MemoryT.

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

TimeFun flag_reads.
TimeFun flag_writes.
TimeFun flag_may_trap.
TimeFun flag_may_diverge.
TimeFun flag_may_stop.
TimeFun flag_allocates.
TimeFun flag_frees.
TimeFun flag_calls.
TimeFun flag_observes.

Module Type EFFECTS_DATA (I : TYPE).
  Parameter flags : I.t -> effect_flags.
End EFFECTS_DATA.

Module Type EFFECTS_DATA_TIME (I : TYPE) (Import D : EFFECTS_DATA I).
  Parameter T_flags : I.t -> N.
End EFFECTS_DATA_TIME.

Module Type EFFECTS_DATA_T (I : TYPE) := EFFECTS_DATA I <+ EFFECTS_DATA_TIME I.

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

Module EffectsT (I : TYPE) (D : EFFECTS_DATA_T I) <: EFFECTS_T I.
  Include EffectsCode I D.
  TimeFun reads.
  TimeFun writes.
  TimeFun may_trap.
  TimeFun may_diverge.
  TimeFun may_stop.
  TimeFun allocates.
  TimeFun frees.
  TimeFun calls.
  TimeFun observes.
End EffectsT.

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

  (** A region disjoint from every effect write retains its existing bytes. *)
  Lemma disjoint_region_frame :
    (forall x y : Val.t, {x = y} + {x <> y}) ->
    forall p s tr t e region l address,
      reachable (M.initial p) (M.step p) s -> T.lstep p s tr t -> L.taken p s t e ->
      B.effect_address (B.effect_snapshot s) l = Some address ->
      B.region_holds region address ->
      (forall a r, In a (V.effects p e) -> In r (effect_writes A.all a) ->
        A.disjoint region r = true) ->
      B.effect_value (B.effect_snapshot t) l = B.effect_value (B.effect_snapshot s) l.
  Proof.
    intros eq p s tr t e region l address Hreach Hstep Htaken Hsite Hregion Hdisjoint.
    destruct (eq (B.effect_value (B.effect_snapshot t) l)
      (B.effect_value (B.effect_snapshot s) l)) as [Hequal|Hchanged].
    - exact Hequal.
    - destruct (transition_byte_covered eq p s tr t e l address
        Hreach Hstep Htaken Hsite Hchanged) as [a [r [Ha [Hr Hcovered]]]].
      exfalso; exact (B.memory_disjoint_sound region r address
        (Hdisjoint a r Ha Hr) Hregion Hcovered).
  Qed.

  (** Every actual read retains its own incoming snapshot and covering effect. *)
  Lemma transition_read_covered : forall p s tr t e l,
    reachable (M.initial p) (M.step p) s -> T.lstep p s tr t -> L.taken p s t e ->
    B.transition_read p s tr t l -> exists states i b a,
      effect_trace_states B.effect_step (B.effect_snapshot s) (V.effects p e) states
        (B.effect_snapshot t) /\ nth_error states i = Some b /\
      nth_error (V.effects p e) i = Some a /\ B.effect_read b a l /\
      forall address, B.effect_address b l = Some address ->
        exists r, In r (effect_reads A.all a) /\ B.region_holds r address.
  Proof.
    intros p s tr t e l Hreach Hstep Htaken Hread.
    destruct (B.effect_step_trace p s tr t e Hreach Hstep Htaken)
      as [states [Htrace [Hreads Hwrites]]].
    destruct (Hreads l Hread) as [i [b [a [Hstate [Heffect Hlocal]]]]].
    exists states, i, b, a; split; [exact Htrace|].
    split; [exact Hstate|]; split; [exact Heffect|]; split; [exact Hlocal|].
    intros address Haddress; eapply B.effect_read_covered; eassumption.
  Qed.

  (** Every actual write is covered even when it leaves the stored byte unchanged. *)
  Lemma transition_write_covered : forall p s tr t e address,
    reachable (M.initial p) (M.step p) s -> T.lstep p s tr t -> L.taken p s t e ->
    B.transition_write p s tr t address -> exists states i b a r,
      effect_trace_states B.effect_step (B.effect_snapshot s) (V.effects p e) states
        (B.effect_snapshot t) /\ nth_error states i = Some b /\
      nth_error (V.effects p e) i = Some a /\ B.effect_write b a address /\
      In r (effect_writes A.all a) /\ B.region_holds r address.
  Proof.
    intros p s tr t e address Hreach Hstep Htaken Hwrite.
    destruct (B.effect_step_trace p s tr t e Hreach Hstep Htaken)
      as [states [Htrace [Hreads Hwrites]]].
    destruct (Hwrites address Hwrite) as [i [b [a [Hstate [Heffect Hlocal]]]]].
    destruct (B.effect_write_covered b a address Hlocal) as [r [Hr Hcovered]].
    exists states, i, b, a, r; repeat split; assumption.
  Qed.
End MemorySound.
