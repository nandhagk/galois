(** * Numbering presentations and observation laws

    Numbering reads SSA syntax without requiring a concrete semantics to run.
    For example, a client can mark addition pure and leave a volatile read impure.
    Builds on: ProgramSsa, ProgramStrict and GraphDomSpec. *)

From Stdlib Require Import List Bool NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding.
From Galois.Graph Require Import GraphModel GraphDomSpec.
From Galois.Program Require Import ProgramSemantics ProgramCfg ProgramLink ProgramSsa
  ProgramStrict.

Module Numbering.

(** A problem carries syntax and costed purity and operator-key dictionaries. *)
Record problem (N E V K G : Type) : Type := Problem {
  ssa : Ssa.t N E V K G;
  op_enc : encoding K;
  pure_c : K -> Cost.t bool
}.

Arguments Problem {N E V K G}.
Arguments ssa {N E V K G}.
Arguments op_enc {N E V K G}.
Arguments pure_c {N E V K G}.

(** Purity is the value returned by the client's costed callback. *)
Definition pure {N E V K G} (np : problem N E V K G) o :=
  Cost.value (pure_c np o).

(** Pure callback adapters charge one primitive tick for each purity query. *)
Definition of_pure {N E V K G} ssa op_enc pure : problem N E V K G :=
  Problem ssa op_enc (Cost.lift (fun _ => 1%N) pure).

(** Contexts distinguish visits to states and rank ready values by dependency depth. *)
Record obs (H S N E V : Type) : Type := Obs {
  observation_state : H -> S;
  observation_ready : H -> V -> Prop;
  observation_rank : H -> V -> nat;
  observation_previous : H -> N -> option (E * H)
}.

Arguments Obs {H S N E V}.
Arguments observation_state {H S N E V}.
Arguments observation_ready {H S N E V}.
Arguments observation_rank {H S N E V}.
Arguments observation_previous {H S N E V}.

(** Ready definitions are evaluated from smaller ready observations in the same history. *)
Record obs_laws {H S O N E V K G C} (m : semantics S O)
    (np : problem N E V K G) (sl : SsaLink.t S O N E V C)
    (eval : K -> list C -> option C) (ob : obs H S N E V) : Prop := {
  observed_op : forall h x o args c,
    observation_ready ob h x -> Ssa.def (ssa np) x = Op o args -> pure np o = true ->
    SsaLink.val sl (observation_state ob h) x = Some c ->
    exists cs, Forall2 (fun y d => observation_ready ob h y /\
      observation_rank ob h y < observation_rank ob h x /\
      SsaLink.val sl (observation_state ob h) y = Some d) args cs /\ eval o cs = Some c;
  observed_param : forall h x b i c,
    observation_ready ob h x -> Ssa.def (ssa np) x = Param b i ->
    ~ In b (Graph.entries (Cfg.graph (Ssa.cfg (ssa np)))) ->
    SsaLink.val sl (observation_state ob h) x = Some c ->
    exists e h' z l t tr, observation_previous ob h b = Some (e, h') /\
      In e (Cfg.edges (Ssa.cfg (ssa np))) /\
      Graph.target (Cfg.graph (Ssa.cfg (ssa np))) e = b /\
      nth_error (Ssa.args (ssa np) e) i = Some z /\ observation_ready ob h' z /\
      observation_rank ob h' z < observation_rank ob h x /\
      SsaLink.val sl (observation_state ob h') z = Some c /\
      reachable_state m (observation_state ob h') /\
      step m (observation_state ob h') l t /\
      Link.taken (SsaLink.link sl) (observation_state ob h') l t e /\
      exec m t tr (observation_state ob h)
}.

Arguments observed_op {H S O N E V K G C m np sl eval ob}.
Arguments observed_param {H S O N E V K G C m np sl eval ob}.

(** A changed pure binding is a successful evaluation in the preceding state. *)
Record loop_laws {S O N E V K G C} (m : semantics S O)
    (np : problem N E V K G) (sl : SsaLink.t S O N E V C)
    (eval : K -> list C -> option C) : Prop := {
  loop_op_binding : forall s l t x o args,
    reachable_state m s -> step m s l t -> Ssa.def (ssa np) x = Op o args ->
    pure np o = true -> SsaLink.val sl t x <> SsaLink.val sl s x ->
    exists cs c, Forall2 (fun y d => SsaLink.val sl s y = Some d) args cs /\
      eval o cs = Some c /\ SsaLink.val sl t x = Some c
}.

Arguments loop_op_binding {S O N E V K G C m np sl eval}.

(** A loop identifies its header and supplies a costed body-membership callback. *)
Record loop_info (N : Type) : Type := LoopInfo {
  header : N;
  body_c : N -> Cost.t bool
}.

Arguments LoopInfo {N}.
Arguments header {N}.
Arguments body_c {N}.

(** Body membership observes the client's charged callback. *)
Definition body {N} (lp : loop_info N) n := Cost.value (body_c lp n).

(** Loop bodies have a dominating header and a single entry from outside. *)
Record loop_info_wf {N E} (g : Graph.t N E) (lp : loop_info N) : Prop := {
  header_in_body : body lp (header lp) = true;
  header_dominates : forall n, body lp n = true -> dominates g (header lp) n;
  single_entry : forall e, In e (flat_map (Graph.out g) (Graph.nodes g)) ->
    body lp (Graph.target g e) = true ->
    body lp (Graph.source g e) = false -> Graph.target g e = header lp
}.

(** Direct operands keep their option-valued bindings throughout each restricted run. *)
Definition loop_operands_stable {S O N E V K G C} (m : semantics S O)
    (np : problem N E V K G) (sl : SsaLink.t S O N E V C)
    (lp : loop_info N) (x : V) : Prop :=
  forall o args y s tr t, body lp (Ssa.home (ssa np) x) = true ->
    Ssa.def (ssa np) x = Op o args -> pure np o = true -> In y args ->
    reachable_state m s ->
    exec_in m (fun u => body lp (Link.point (SsaLink.link sl) u) = true) s tr t ->
    SsaLink.val sl s y = SsaLink.val sl t y.

End Numbering.
