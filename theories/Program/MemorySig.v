(** * Alias oracles and ordered memory effects

    Effects retain the snapshot at each read and the historical address of existing bytes.
    For example, a barrier reads and writes the oracle's all-memory region.
    Builds on: Program.CfgSig and Program.SemanticsSig. *)

From Stdlib Require Import List NArith.
From Argent Require Import Time Std.
From Galois.Base Require Import KeySig.
From Galois.Program Require Import CfgSig SemanticsSig.

Inductive effect (R : Type) : Type :=
  | Read (region : R)
  | Write (region : R)
  | ReadWrite (read_region write_region : R)
  | Call (read_region write_region : R)
  | Alloc (region : R)
  | Free (region : R)
  | Barrier.

Arguments Read {R}.
Arguments Write {R}.
Arguments ReadWrite {R}.
Arguments Call {R}.
Arguments Alloc {R}.
Arguments Free {R}.
Arguments Barrier {R}.

(** Read projections include the all-memory region of a barrier. *)
Definition effect_reads {R} (all : R) (a : effect R) : list R :=
  match a with
  | Read r => r :: nil
  | ReadWrite r _ => r :: nil
  | Call r _ => r :: nil
  | Write _ => nil
  | Alloc _ => nil
  | Free _ => nil
  | Barrier => all :: nil
  end.

TimeFun effect_reads.

(** Allocation, freeing, calls and barriers are memory definitions. *)
Definition effect_writes {R} (all : R) (a : effect R) : list R :=
  match a with
  | Read _ => nil
  | Write r => r :: nil
  | ReadWrite _ r => r :: nil
  | Call _ r => r :: nil
  | Alloc r => r :: nil
  | Free r => r :: nil
  | Barrier => all :: nil
  end.

TimeFun effect_writes.

(** Every effect except a pure read defines memory. *)
Definition effect_is_def {R} (a : effect R) : bool :=
  match a with
  | Read _ => false
  | _ => true
  end.

TimeFun effect_is_def.

(** An effect trace records each incoming snapshot in the edge's effect order. *)
Inductive effect_trace_states {R B} (next : B -> effect R -> B -> Prop) :
    B -> list (effect R) -> list B -> B -> Prop :=
  | Effect_states_nil : forall b, effect_trace_states next b nil nil b
  | Effect_states_cons : forall b a b' rest states b'',
      next b a b' -> effect_trace_states next b' rest states b'' ->
      effect_trace_states next b (a :: rest) (b :: states) b''.

(** Forgetting the intermediate snapshots leaves the same ordered effect execution. *)
Inductive effect_trace {R B} (next : B -> effect R -> B -> Prop) :
    B -> list (effect R) -> B -> Prop :=
  | Effect_trace_nil : forall b, effect_trace next b nil b
  | Effect_trace_cons : forall b a b' rest b'',
      next b a b' -> effect_trace next b' rest b'' -> effect_trace next b (a :: rest) b''.

(** A within-frame divergence never drops below the supplied frame depth. *)
CoInductive diverges_within {S O} (step : S -> list O -> S -> Prop)
    (depth : S -> nat) (d : nat) : S -> Prop :=
  | Within_step : forall s tr t, step s tr t -> d <= depth t ->
      diverges_within step depth d t -> diverges_within step depth d s.

Module Type ALIAS_OPS (R : KEY_OPS).
  Parameter disjoint covers : R.t -> R.t -> bool.
  Parameter all : R.t.
End ALIAS_OPS.

Module Type ALIAS_LAWS (R : KEY) (Import A : ALIAS_OPS R).
  (* spec: state loc holds *)
  Parameter state loc : Type.
  Parameter holds : state -> R.t -> loc -> Prop.
  (** A successful disjointness answer excludes every shared location. *)
  Parameter disjoint_sound : forall s r q l, disjoint r q = true ->
    holds s r l -> holds s q l -> False.
  (** A successful coverage answer includes the second region in the first. *)
  Parameter covers_sound : forall s r q l, covers r q = true -> holds s q l -> holds s r l.
  (** The all-memory region contains every location. *)
  Parameter all_full : forall s l, holds s all l.
End ALIAS_LAWS.

Module Type ALIAS (R : KEY) := ALIAS_OPS R <+ ALIAS_LAWS R.

Module Type ALIAS_TIME (R : KEY_T) (Import A : ALIAS R).
  Parameter T_disjoint T_covers : R.t -> R.t -> N.
  (* SIG-QUESTION: the alias interface specifies sound answers but no reader complexity. *)
End ALIAS_TIME.

Module Type ALIAS_T (R : KEY_T) := ALIAS R <+ ALIAS_TIME R.

Module Type MEMORY_OPS (P : TYPE) (N : KEY_OPS) (E : TYPE)
    (C : CFG_OPS P N E) (R : KEY_OPS) (A : ALIAS_OPS R).
  Parameter effects : P.t -> E.t -> list (effect R.t).
End MEMORY_OPS.

Module Type MEMORY_SPEC (P : TYPE) (N : KEY_OPS) (E : TYPE)
    (C : CFG_OPS P N E) (R : KEY_OPS) (A : ALIAS_OPS R)
    (Import M : MEMORY_OPS P N E C R A).
  Definition reads p e := flat_map (effect_reads A.all) (effects p e).
  Definition writes p e := flat_map (effect_writes A.all) (effects p e).
End MEMORY_SPEC.

Module Type MEMORY (P : TYPE) (N : KEY) (E : TYPE)
    (C : CFG P N E) (R : KEY) (A : ALIAS R) :=
  MEMORY_OPS P N E C R A <+ MEMORY_SPEC P N E C R A.

Module Type MEMORY_TIME (P : TYPE) (N : KEY_T) (E : TYPE)
    (C : CFG_T P N E) (R : KEY_T) (A : ALIAS_T R)
    (Import M : MEMORY P N E C R A).
  Parameter T_effects : P.t -> E.t -> N.
  (* SIG-QUESTION: the memory presentation leaves the effect-reader complexity unspecified. *)
End MEMORY_TIME.

Module Type MEMORY_T (P : TYPE) (N : KEY_T) (E : TYPE)
    (C : CFG_T P N E) (R : KEY_T) (A : ALIAS_T R) :=
  MEMORY P N E C R A <+ MEMORY_TIME P N E C R A.

Module Type MEMORY_LINK (P : TYPE) (N : KEY) (E : TYPE)
    (C : CFG P N E) (R : KEY) (A : ALIAS R) (V : MEMORY P N E C R A)
    (M : SEMANTICS P) (T : TRACES P M) (L : CFG_LINK P N E C M) (Loc Val : TYPE).
  Parameter effect_snapshot : M.state -> A.state.
  Parameter effect_address : A.state -> Loc.t -> option A.loc.
  Parameter effect_value : A.state -> Loc.t -> Val.t.
  Parameter region_holds : R.t -> A.loc -> Prop.
  Parameter effect_step : A.state -> effect R.t -> A.state -> Prop.
  Parameter effect_read : A.state -> effect R.t -> Loc.t -> Prop.
  Parameter effect_write : A.state -> effect R.t -> A.loc -> Prop.
  Parameter transition_read : P.t -> M.state -> list T.event -> M.state -> Loc.t -> Prop.
  Parameter transition_write : P.t -> M.state -> list T.event -> M.state -> A.loc -> Prop.
  (** Disjointness is sound for the fixed historical-address denotation. *)
  Parameter memory_disjoint_sound : forall r q l, A.disjoint r q = true ->
    region_holds r l -> region_holds q l -> False.
  (** Coverage is sound for the fixed historical-address denotation. *)
  Parameter memory_covers_sound : forall r q l, A.covers r q = true ->
    region_holds q l -> region_holds r l.
  (** Every historical address belongs to the all-memory region. *)
  Parameter memory_all_full : forall l, region_holds A.all l.
  (** Actual edge reads are attached to their incoming snapshot in the same ordered trace. *)
  Parameter effect_step_trace : forall p s tr t e,
    reachable (M.initial p) (M.step p) s -> T.lstep p s tr t -> L.taken p s t e ->
    exists states,
      effect_trace_states effect_step (effect_snapshot s) (V.effects p e) states
        (effect_snapshot t) /\
      (forall l, transition_read p s tr t l -> exists i b a,
        nth_error states i = Some b /\ nth_error (V.effects p e) i = Some a /\
        effect_read b a l) /\
      (forall l, transition_write p s tr t l -> exists i b a,
        nth_error states i = Some b /\ nth_error (V.effects p e) i = Some a /\
        effect_write b a l).
  (** Each effect read is covered at its actual incoming historical address. *)
  Parameter effect_read_covered : forall b a l address,
    effect_read b a l -> effect_address b l = Some address ->
    exists r, In r (effect_reads A.all a) /\ region_holds r address.
  (** Each actual write is covered even when the stored byte retains its value. *)
  Parameter effect_write_covered : forall b a address,
    effect_write b a address ->
    exists r, In r (effect_writes A.all a) /\ region_holds r address.
  (* SIG-QUESTION: actual-write coverage has no landed provider beyond changed existing bytes. *)
  (** Existing historical addresses stay identifiable through each effect. *)
  Parameter effect_site_stable : forall b a b' l address,
    effect_step b a b' -> effect_address b l = Some address ->
    effect_address b' l = Some address.
  (** A changed existing byte belongs to a write region of that effect. *)
  Parameter effect_byte_frame : forall b a b' l address,
    effect_step b a b' -> effect_address b l = Some address ->
    effect_value b' l <> effect_value b l ->
    exists r, In r (effect_writes A.all a) /\ region_holds r address.
End MEMORY_LINK.

Module Type MEMORY_SOUND (P : TYPE) (N : KEY) (E : TYPE)
    (C : CFG P N E) (R : KEY) (A : ALIAS R) (V : MEMORY P N E C R A)
    (M : SEMANTICS P) (T : TRACES P M) (L : CFG_LINK P N E C M) (Loc Val : TYPE)
    (B : MEMORY_LINK P N E C R A V M T L Loc Val).
  (** A changed existing byte is covered by a write of the actual edge trace. *)
  Parameter transition_byte_covered :
    (forall x y : Val.t, {x = y} + {x <> y}) ->
    forall p s tr t e l address,
      reachable (M.initial p) (M.step p) s -> T.lstep p s tr t -> L.taken p s t e ->
      B.effect_address (B.effect_snapshot s) l = Some address ->
      B.effect_value (B.effect_snapshot t) l <> B.effect_value (B.effect_snapshot s) l ->
      exists a r, In a (V.effects p e) /\ In r (effect_writes A.all a) /\
        B.region_holds r address.
  (** A region disjoint from all edge writes retains every existing byte in that region. *)
  Parameter disjoint_region_frame :
    (forall x y : Val.t, {x = y} + {x <> y}) ->
    forall p s tr t e region l address,
      reachable (M.initial p) (M.step p) s -> T.lstep p s tr t -> L.taken p s t e ->
      B.effect_address (B.effect_snapshot s) l = Some address ->
      B.region_holds region address ->
      (forall a r, In a (V.effects p e) -> In r (effect_writes A.all a) ->
        A.disjoint region r = true) ->
      B.effect_value (B.effect_snapshot t) l = B.effect_value (B.effect_snapshot s) l.
  (** Every actual read is covered by its effect at that effect's incoming snapshot. *)
  Parameter transition_read_covered : forall p s tr t e l,
    reachable (M.initial p) (M.step p) s -> T.lstep p s tr t -> L.taken p s t e ->
    B.transition_read p s tr t l -> exists states i b a,
      effect_trace_states B.effect_step (B.effect_snapshot s) (V.effects p e) states
        (B.effect_snapshot t) /\ nth_error states i = Some b /\
      nth_error (V.effects p e) i = Some a /\ B.effect_read b a l /\
      forall address, B.effect_address b l = Some address ->
        exists r, In r (effect_reads A.all a) /\ B.region_holds r address.
  (** Every actual write is covered at its incoming snapshot in the edge's effect trace. *)
  Parameter transition_write_covered : forall p s tr t e address,
    reachable (M.initial p) (M.step p) s -> T.lstep p s tr t -> L.taken p s t e ->
    B.transition_write p s tr t address -> exists states i b a r,
      effect_trace_states B.effect_step (B.effect_snapshot s) (V.effects p e) states
        (B.effect_snapshot t) /\ nth_error states i = Some b /\
      nth_error (V.effects p e) i = Some a /\ B.effect_write b a address /\
      In r (effect_writes A.all a) /\ B.region_holds r address.
End MEMORY_SOUND.

Module Type MEMORY_EFFECT_LAWS (R : KEY) (A : ALIAS R).
  (** Barriers have the same read and write projections as an all-memory read/write. *)
  Parameter barrier_read_write :
    effect_reads A.all Barrier = effect_reads A.all (ReadWrite A.all A.all) /\
    effect_writes A.all Barrier = effect_writes A.all (ReadWrite A.all A.all) /\
    effect_is_def (@Barrier R.t) = true.
  (** Recorded effect snapshots forget to the same ordinary effect trace. *)
  Parameter effect_trace_states_trace : forall B (next : B -> effect R.t -> B -> Prop)
    b effects states b', effect_trace_states next b effects states b' ->
      effect_trace next b effects b'.
End MEMORY_EFFECT_LAWS.

Module Type EFFECTS_OPS (I : TYPE).
  Parameter reads writes may_trap may_diverge may_stop allocates frees calls observes :
    I.t -> bool.
End EFFECTS_OPS.

Module Type EFFECTS_TIME (I : TYPE) (Import E : EFFECTS_OPS I).
  Parameter T_reads T_writes T_may_trap T_may_diverge T_may_stop
    T_allocates T_frees T_calls T_observes : I.t -> N.
End EFFECTS_TIME.

Module Type EFFECTS_T (I : TYPE) := EFFECTS_OPS I <+ EFFECTS_TIME I.

Module Type EFFECTS_LINK (P I H : TYPE) (E : EFFECTS_OPS I)
    (M : SEMANTICS P) (T : TRACES P M).
  Parameter instr_at : M.state -> option I.t.
  Parameter heap : M.state -> H.t.
  Parameter heap_agree : M.state -> M.state -> Prop.
  Parameter depth : M.state -> nat.
  (** A non-observing instruction emits no events. *)
  Parameter silent : forall p s tr t i,
    reachable (M.initial p) (M.step p) s -> T.lstep p s tr t -> instr_at s = Some i ->
    E.observes i = false -> tr = nil.
  (** A reachable trap is covered by the instruction's trap flag. *)
  Parameter trap_covered : forall p s i,
    reachable (M.initial p) (M.step p) s -> instr_at s = Some i ->
    T.trapped p s -> E.may_trap i = true.
  (** A reachable resource stop is covered by the stop flag. *)
  Parameter stop_covered : forall p s i,
    reachable (M.initial p) (M.step p) s -> instr_at s = Some i ->
    T.stopped p s -> E.may_stop i = true.
  (** A step without writes, allocation or freeing retains the heap. *)
  Parameter heap_frame : forall p s tr t i,
    reachable (M.initial p) (M.step p) s -> T.lstep p s tr t -> instr_at s = Some i ->
    E.writes i = false -> E.allocates i = false -> E.frees i = false -> heap t = heap s.
  (** Heap-independent instructions reproduce their labelled transition on agreeing heaps. *)
  Parameter reads_frame : forall p s tr s' t i,
    reachable (M.initial p) (M.step p) s -> T.lstep p s tr s' -> instr_at s = Some i ->
    E.reads i = false -> heap_agree s t ->
    exists t', T.lstep p t tr t' /\ heap_agree s' t'.
  (** Heap-independent instructions have matching trap outcomes in agreeing reachable states. *)
  Parameter trap_frame : forall p s t i,
    reachable (M.initial p) (M.step p) s -> reachable (M.initial p) (M.step p) t ->
    instr_at s = Some i -> instr_at t = Some i -> E.reads i = false -> heap_agree s t ->
    (T.trapped p s <-> T.trapped p t).
  (** Heap-independent instructions have matching resource stops in agreeing reachable states. *)
  Parameter stop_frame : forall p s t i,
    reachable (M.initial p) (M.step p) s -> reachable (M.initial p) (M.step p) t ->
    instr_at s = Some i -> instr_at t = Some i -> E.reads i = false -> heap_agree s t ->
    (T.stopped p s <-> T.stopped p t).
  (** A non-call transition retains its frame depth. *)
  Parameter frame_frame : forall p s tr t i,
    reachable (M.initial p) (M.step p) s -> T.lstep p s tr t -> instr_at s = Some i ->
    E.calls i = false -> depth t = depth s.
  (** A terminating call cannot diverge forever inside its newly entered frame. *)
  Parameter call_returns : forall p s tr t i,
    reachable (M.initial p) (M.step p) s -> T.lstep p s tr t -> instr_at s = Some i ->
    E.calls i = true -> E.may_diverge i = false -> depth t = Datatypes.S (depth s) ->
    ~ diverges_within (T.lstep p) depth (depth t) t.
End EFFECTS_LINK.
