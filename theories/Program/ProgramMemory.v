(** * Abstract alias oracles and ordered memory effects

    Regions describe effects without choosing bytes, pointers or allocation sites.
    For example, a barrier reads and writes the oracle's all-memory region.
    Builds on: ProgramLink. *)

From Stdlib Require Import List NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding.
From Galois.Program Require Import ProgramSemantics ProgramSteps ProgramCfg ProgramLink.
Import List.ListNotations.

Module Alias.

(** An alias dictionary answers charged disjointness and coverage queries. *)
Record t (R : Type) := Make {
  disjoint_c : R -> R -> Cost.t bool;
  covers_c : R -> R -> Cost.t bool;
  all : R
}.
Arguments Make {R}.
Arguments disjoint_c {R}.
Arguments covers_c {R}.
Arguments all {R}.

Definition disjoint {R} (al : t R) r q := Cost.value (disjoint_c al r q).
Definition covers {R} (al : t R) r q := Cost.value (covers_c al r q).

(** Pure alias primitives charge one tick on each binary query. *)
Definition of_pure {R} disjoint covers all : t R :=
  Make (fun r => Cost.lift (fun _ => 1%N) (disjoint r))
    (fun r => Cost.lift (fun _ => 1%N) (covers r)) all.

End Alias.

(** True alias answers imply semantic disjointness or containment and [all] covers everything. *)
Record alias_laws {S L R} (al : Alias.t R) (holds : S -> R -> L -> Prop) : Prop := {
  disjoint_sound : forall s r q l, Alias.disjoint al r q = true ->
    holds s r l -> holds s q l -> False;
  covers_sound : forall s r q l, Alias.covers al r q = true -> holds s q l -> holds s r l;
  all_full : forall s l, holds s (Alias.all al) l
}.
Arguments disjoint_sound {S L R al holds}.
Arguments covers_sound {S L R al holds}.
Arguments all_full {S L R al holds}.

Module Memory.

(** Ordered effects distinguish observations from writes, calls and barriers. *)
Inductive effect (R : Type) :=
  | Read (r : R)
  | Write (w : R)
  | ReadWrite (r w : R)
  | Call (r w : R)
  | Barrier.
Arguments Read {R}.
Arguments Write {R}.
Arguments ReadWrite {R}.
Arguments Call {R}.
Arguments Barrier {R}.

(** Lists represent the absent read or write region without requiring an empty-region oracle. *)
Definition effect_reads {R} (al : Alias.t R) (a : effect R) : list R :=
  match a with
  | Read r | ReadWrite r _ | Call r _ => [r]
  | Write _ => []
  | Barrier => [Alias.all al]
  end.

Definition effect_writes {R} (al : Alias.t R) (a : effect R) : list R :=
  match a with
  | Write w | ReadWrite _ w | Call _ w => [w]
  | Read _ => []
  | Barrier => [Alias.all al]
  end.

Definition effect_is_def {R} (a : effect R) : bool :=
  match a with
  | Read _ => false
  | _ => true
  end.

(** A memory presentation supplies an oracle and an ordered effect list per edge. *)
Record t (N E R : Type) := Make {
  cfg : Cfg.t N E;
  region_enc : encoding R;
  alias : Alias.t R;
  effects_c : E -> Cost.t (list (effect R))
}.
Arguments Make {N E R}.
Arguments cfg {N E R}.
Arguments region_enc {N E R}.
Arguments alias {N E R}.
Arguments effects_c {N E R}.

Definition effects {N E R} (p : t N E R) e := Cost.value (effects_c p e).

(** Pure effect-list readers charge one primitive tick. *)
Definition of_pure {N E R} cfg enc alias effects : t N E R :=
  Make cfg enc alias (Cost.lift (fun _ => 1%N) effects).

(** Barrier projections coincide with an all-memory read/write effect. *)
Theorem barrier_read_write {R} (al : Alias.t R) :
  effect_reads al Barrier = effect_reads al (ReadWrite (Alias.all al) (Alias.all al)) /\
  effect_writes al Barrier = effect_writes al (ReadWrite (Alias.all al) (Alias.all al)) /\
  effect_is_def (@Barrier R) = true.
Proof.
  repeat split; reflexivity.
Qed.

End Memory.

Module MemoryLink.

(** Historical addresses and snapshots let clients state framing without a byte model.
    [T] is a stable address such as an allocation-site and offset pair.
    [L] is a concrete location and [B] is a snapshot. *)
Record t (S O N E R B L T C : Type) := Make {
  link : Link.t S O N E;
  effect_snapshot : S -> B;
  effect_address : B -> L -> option T;
  effect_value : B -> L -> C;
  region_holds : R -> T -> Prop;
  effect_step : B -> Memory.effect R -> B -> Prop;
  effect_read : B -> Memory.effect R -> L -> Prop;
  transition_read : S -> list O -> S -> L -> Prop
}.
Arguments Make {S O N E R B L T C}.
Arguments link {S O N E R B L T C}.
Arguments effect_snapshot {S O N E R B L T C}.
Arguments effect_address {S O N E R B L T C}.
Arguments effect_value {S O N E R B L T C}.
Arguments region_holds {S O N E R B L T C}.
Arguments effect_step {S O N E R B L T C}.
Arguments effect_read {S O N E R B L T C}.
Arguments transition_read {S O N E R B L T C}.

End MemoryLink.

(** An effect trace executes the list in edge order. *)
Inductive effect_trace {R B} (next : B -> Memory.effect R -> B -> Prop) :
    B -> list (Memory.effect R) -> B -> Prop :=
  | effect_trace_nil : forall b, effect_trace next b [] b
  | effect_trace_cons : forall b a b' rest b'',
      next b a b' -> effect_trace next b' rest b'' ->
      effect_trace next b (a :: rest) b''.

(** Recorded states are exactly the incoming snapshots of the ordered effects. *)
Inductive effect_trace_states {R B} (next : B -> Memory.effect R -> B -> Prop) :
    B -> list (Memory.effect R) -> list B -> B -> Prop :=
  | effect_states_nil : forall b, effect_trace_states next b [] [] b
  | effect_states_cons : forall b a b' rest states b'',
      next b a b' -> effect_trace_states next b' rest states b'' ->
      effect_trace_states next b (a :: rest) (b :: states) b''.

(** Actual reads share the edge's ordered trace and changed existing addresses are covered.
    The unrestricted [effect_no_stays] and local effect premises retain legacy domains. *)
Record memory_laws {S O N E R B L T C} (m : semantics S O) (p : Memory.t N E R)
    (v : MemoryLink.t S O N E R B L T C) : Prop := {
  effect_view_laws : link_laws m (Cfg.graph (Memory.cfg p)) (MemoryLink.link v);
  effect_no_stays : forall s tr s', ~ Link.stays (MemoryLink.link v) s tr s';
  memory_alias_ok : alias_laws (Memory.alias p)
    (fun (_ : B) => MemoryLink.region_holds v);
  effect_step_trace : forall e, on_steps m (fun s tr s' =>
    Link.taken (MemoryLink.link v) s tr s' e -> exists states,
      effect_trace_states (MemoryLink.effect_step v)
        (MemoryLink.effect_snapshot v s) (Memory.effects p e) states
        (MemoryLink.effect_snapshot v s') /\
      forall l, MemoryLink.transition_read v s tr s' l -> exists i b a,
        nth_error states i = Some b /\ nth_error (Memory.effects p e) i = Some a /\
        MemoryLink.effect_read v b a l);
  effect_read_covered : forall b a l t, MemoryLink.effect_read v b a l ->
    MemoryLink.effect_address v b l = Some t ->
    exists r, In r (Memory.effect_reads (Memory.alias p) a) /\ MemoryLink.region_holds v r t;
  effect_site_stable : forall b a b' l t, MemoryLink.effect_step v b a b' ->
    MemoryLink.effect_address v b l = Some t -> MemoryLink.effect_address v b' l = Some t;
  effect_byte_frame : forall b a b' l t, MemoryLink.effect_step v b a b' ->
    MemoryLink.effect_address v b l = Some t ->
    MemoryLink.effect_value v b' l <> MemoryLink.effect_value v b l ->
    exists r, In r (Memory.effect_writes (Memory.alias p) a) /\ MemoryLink.region_holds v r t
}.
Arguments effect_view_laws {S O N E R B L T C m p v}.
Arguments effect_no_stays {S O N E R B L T C m p v}.
Arguments memory_alias_ok {S O N E R B L T C m p v}.
Arguments effect_step_trace {S O N E R B L T C m p v}.
Arguments effect_read_covered {S O N E R B L T C m p v}.
Arguments effect_site_stable {S O N E R B L T C m p v}.
Arguments effect_byte_frame {S O N E R B L T C m p v}.

(** The indexed snapshot trace forgets to an ordinary ordered effect trace. *)
Theorem effect_trace_states_trace {R B} (next : B -> Memory.effect R -> B -> Prop)
    b effects states b' :
  effect_trace_states next b effects states b' -> effect_trace next b effects b'.
Proof.
  intro Htrace; induction Htrace; econstructor; eassumption.
Qed.

(** A changed existing address belongs to a write in the actual snapshot trace. *)
Theorem effect_trace_states_byte_covered {S O N E R B L T C} (m : semantics S O)
    (p : Memory.t N E R) (v : MemoryLink.t S O N E R B L T C)
    (Hlaws : memory_laws m p v) (eq : forall x y : C, {x = y} + {x <> y})
    b effects states b' :
  effect_trace_states (MemoryLink.effect_step v) b effects states b' ->
  forall l t, MemoryLink.effect_address v b l = Some t ->
    MemoryLink.effect_value v b' l <> MemoryLink.effect_value v b l ->
    exists a r, In a effects /\ In r (Memory.effect_writes (Memory.alias p) a) /\
      MemoryLink.region_holds v r t.
Proof.
  intro Htrace; induction Htrace as [b|b a middle rest states last Hstep Htrace IH];
    intros l t Hsite Hchanged.
  - exfalso; apply Hchanged; reflexivity.
  - destruct (eq (MemoryLink.effect_value v middle l) (MemoryLink.effect_value v b l))
      as [Hequal|Hdifferent].
    + destruct (IH l t (effect_site_stable Hlaws b a middle l t Hstep Hsite))
        as [writer [r [Hin [Hr Hcovers]]]].
      * rewrite Hequal; exact Hchanged.
      * exists writer, r; split; [right; exact Hin|split; assumption].
    + destruct (effect_byte_frame Hlaws b a middle l t Hstep Hsite Hdifferent)
        as [r [Hr Hcovers]].
      exists a, r; split; [left; reflexivity|split; assumption].
Qed.

(** A changed existing address is covered by a write of the taken edge. *)
Theorem effect_transition_byte_covered {S O N E R B L T C} (m : semantics S O)
    (p : Memory.t N E R) (v : MemoryLink.t S O N E R B L T C)
    (eq : forall x y : C, {x = y} + {x <> y}) :
  memory_laws m p v ->
  forall s tr s' e l t, reachable_state m s -> step m s tr s' ->
    Link.taken (MemoryLink.link v) s tr s' e ->
    MemoryLink.effect_address v (MemoryLink.effect_snapshot v s) l = Some t ->
    MemoryLink.effect_value v (MemoryLink.effect_snapshot v s') l <>
      MemoryLink.effect_value v (MemoryLink.effect_snapshot v s) l ->
    exists a r, In a (Memory.effects p e) /\
      In r (Memory.effect_writes (Memory.alias p) a) /\ MemoryLink.region_holds v r t.
Proof.
  intros Hlaws s tr s' e l t Hreachable Hstep Htaken Hsite Hchanged.
  destruct (effect_step_trace Hlaws e s tr s' Hreachable Hstep Htaken)
    as [states [Htrace Hreads]].
  eapply effect_trace_states_byte_covered; eassumption.
Qed.
