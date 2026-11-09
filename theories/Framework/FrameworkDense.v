(** * Dense edge constraints

    Dense problems seed entries forward and every listed node backward.
    For example, backward liveness may observe a variable at a nonterminal node.
    Builds on: FrameworkUtil, ProgramCfg and FixpointAnalysis. *)

From Stdlib Require Import List Bool NArith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding.
From Galois.Lattice Require Import LatticeCore.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramCfg.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointAnalysis.
From Galois.Framework Require Import FrameworkUtil.
Import List.ListNotations Cost.Notations.

(** Direction chooses which endpoint supplies the input of an edge transfer. *)
Inductive direction :=
  | Forward
  | Backward.

Module Dense.

(** Seeds precede flow rows and retain every presentation occurrence. *)
Inductive constraint (N E : Type) :=
  | Seed (n : N)
  | Flow (e : E).
Arguments Seed {N E}.
Arguments Flow {N E}.

Definition constraint_enc {N E} (EN : encoding N) (EE : encoding E) :=
  encoding_comap
    (fun c : constraint N E =>
      Cost.ret (match c with Seed n => inl n | Flow e => inr e end))
    (FrameworkKey.sum EN EE).

(** Dense row keys distinguish node seeds from edge flows. *)
Theorem constraint_enc_laws {N E} (EN : encoding N) (EE : encoding E) :
  encoding_laws EN -> encoding_laws EE -> encoding_laws (constraint_enc EN EE).
Proof.
  intros HN HE; apply encoding_comap_laws.
  - intros [n|e] [m|f] Heq; cbn in Heq; congruence.
  - apply FrameworkKey.sum_laws; assumption.
Qed.

(** Boundaries and transfers are charged client callbacks without semantic inputs. *)
Record t (N E A : Type) := Make {
  cfg : Cfg.t N E;
  dir : direction;
  lat : lattice A;
  boundary_c : N -> Cost.t (option A);
  transfer_c : E -> A -> Cost.t A
}.
Arguments Make {N E A}.
Arguments cfg {N E A}.
Arguments dir {N E A}.
Arguments lat {N E A}.
Arguments boundary_c {N E A}.
Arguments transfer_c {N E A}.

Definition boundary {N E A} (D : t N E A) n := Cost.value (boundary_c D n).
Definition transfer {N E A} (D : t N E A) e a := Cost.value (transfer_c D e a).

(** Pure adapters treat client readers and transfers as primitive callbacks. *)
Definition of_pure {N E A} cfg dir lat boundary transfer : t N E A :=
  Make cfg dir lat (fun n => Cost.step ;; Cost.ret (boundary n))
    (fun e a => Cost.step ;; Cost.ret (transfer e a)).

Definition seeds {N E A} (D : t N E A) :=
  match dir D with
  | Forward => Graph.entries (Cfg.graph (cfg D))
  | Backward => Graph.nodes (Cfg.graph (cfg D))
  end.

Definition from_c {N E A} (D : t N E A) :=
  match dir D with
  | Forward => Graph.source_c (Cfg.graph (cfg D))
  | Backward => Graph.target_c (Cfg.graph (cfg D))
  end.

Definition into_c {N E A} (D : t N E A) :=
  match dir D with
  | Forward => Graph.target_c (Cfg.graph (cfg D))
  | Backward => Graph.source_c (Cfg.graph (cfg D))
  end.

Definition from {N E A} (D : t N E A) e := Cost.value (from_c D e).
Definition into {N E A} (D : t N E A) e := Cost.value (into_c D e).

Definition target_c {N E A} (D : t N E A) (c : constraint N E) :=
  match c with
  | Seed n => Cost.ret n
  | Flow e => Cost.step ;; into_c D e
  end.

Definition rhs_c {N E A} (D : t N E A) (c : constraint N E) :=
  match c with
  | Seed n =>
    Cost.step ;;
    let* a := boundary_c D n in
    Cost.ret (Query.Ret (match a with Some a => a | None => bot (lat D) end))
  | Flow e =>
    Cost.step ;;
    let* n := from_c D e in
    Cost.ret (Query.Ask n (fun a =>
      Cost.step ;; Cost.map (@Query.Ret N A) (transfer_c D e a)))
  end.

(** Preparation enumerates rows once, preserving the legacy seed and edge order. *)
Definition system_c {N E A} (D : t N E A) :=
  let* es := fw_edges_c (cfg D) in
  let* ss := map_c (fun n => Cost.ret (Seed n)) (seeds D) in
  let* fs := map_c (fun e => Cost.ret (Flow e)) es in
  let* rows := app_c ss fs in
  Cost.ret (System.Make rows (target_c D) (rhs_c D)).

Definition system {N E A} (D : t N E A) := Cost.value (system_c D).

(** Dense rows seed the direction's boundary domain before all edge occurrences. *)
Theorem system_rows {N E A} (D : t N E A) :
  System.constraints (system D) =
    map Seed (seeds D) ++ map Flow (Cfg.edges (cfg D)).
Proof.
  unfold system, system_c; autorewrite with galois_cost.
  rewrite fw_edges_value; reflexivity.
Qed.

(** A row's query and target have no dependency on preparation work. *)
Theorem system_callbacks {N E A} (D : t N E A) c :
  System.target (system D) c =
    match c with Seed n => n | Flow e => into D e end /\
  System.rhs (system D) c =
    match c with
    | Seed n => Query.Ret (match boundary D n with Some a => a | None => bot (lat D) end)
    | Flow e => Query.Ask (from D e)
        (fun a => Cost.step ;; Cost.map (@Query.Ret N A) (transfer_c D e a))
    end.
Proof.
  destruct c; split; reflexivity.
Qed.

(** Dense query traces retain one flow read and no side contributions. *)
Theorem rhs_trace {N E A} (D : t N E A) c s :
  Query.run (System.rhs (system D) c) s =
    match c with
    | Seed n => Query.Trace
        (match boundary D n with Some a => a | None => bot (lat D) end) [] []
    | Flow e => Query.Trace (transfer D e (s (from D e))) [from D e] []
    end.
Proof.
  rewrite (proj2 (system_callbacks D c)); destruct c; rewrite Query.run_equation.
  - reflexivity.
  - autorewrite with galois_cost; rewrite Query.run_equation; reflexivity.
Qed.

(** The summary constructor uses the actually prepared system without inspecting or rebuilding it. *)
Definition static_for {N E A} (D : t N E A) (S : System.t N (constraint N E) A)
    : System.static S :=
  System.Static
    (fun c => match c with
      | Seed _ => Cost.ret []
      | Flow e => Cost.step ;; Cost.map (fun n => [n]) (from_c D e)
      end)
    (fun _ => Cost.ret []).

(** Static dependencies contain the single flow input and no side outputs. *)
Definition static {N E A} (D : t N E A) : System.static (system D) :=
  static_for D (system D).

(** The summary covers every selected read for every assignment. *)
Theorem static_laws {N E A} (D : t N E A) : System.static_laws (static D).
Proof.
  constructor; intros c s.
  - pose proof (f_equal (@Query.read_log N A)
      (Query.run_spec (System.rhs (system D) c) s)) as Hreads.
    rewrite rhs_trace in Hreads.
    destruct c as [n|e]; cbn [Query.read_log] in Hreads.
    + change (incl (Query.reads (System.rhs (system D) (Seed n)) s) []).
      rewrite <- Hreads; apply incl_refl.
    + change (incl (Query.reads (System.rhs (system D) (Flow e)) s) [from D e]).
      rewrite <- Hreads; apply incl_refl.
  - pose proof (f_equal (@Query.side_log N A)
      (Query.run_spec (System.rhs (system D) c) s)) as Hsides.
    rewrite rhs_trace in Hsides.
    destruct c as [n|e]; cbn [Query.side_log] in Hsides.
    + change (incl (map fst (Query.sides (System.rhs (system D) (Seed n)) s)) []).
      rewrite <- Hsides; apply incl_refl.
    + change (incl (map fst (Query.sides (System.rhs (system D) (Flow e)) s)) []).
      rewrite <- Hsides; apply incl_refl.
Qed.

(** Charged construction prepares the system once and attaches its computational summary. *)
Definition analysis_c {N E A} (D : t N E A) (pol : Policy.t N) :=
  let* sys := system_c D in
  Cost.ret (Analysis.Make (Cfg.node_enc (cfg D))
    (constraint_enc (Cfg.node_enc (cfg D)) (Cfg.edge_enc (cfg D)))
    (lat D) sys (static_for D sys) pol).

(** Analyses take a computational scheduling policy and need no law record to run. *)
Definition analysis {N E A} (D : t N E A) (pol : Policy.t N) :=
  Cost.value (analysis_c D pol).

(** Charged construction returns the original analysis record, including its exact static data. *)
Theorem analysis_equation {N E A} (D : t N E A) pol :
  analysis D pol =
    Analysis.Make (Cfg.node_enc (cfg D))
      (constraint_enc (Cfg.node_enc (cfg D)) (Cfg.edge_enc (cfg D)))
      (lat D) (system D) (static D) pol.
Proof.
  unfold analysis, analysis_c; rewrite Cost.value_bind, Cost.value_ret; reflexivity.
Qed.

(** Analysis assembly retains precisely the system preparation charge. *)
Theorem analysis_cost {N E A} (D : t N E A) pol :
  Cost.ticks (analysis_c D pol) = Cost.ticks (system_c D).
Proof.
  unfold analysis_c; rewrite Cost.ticks_bind, Cost.ticks_ret, N.add_0_r; reflexivity.
Qed.

Local Lemma map_ret_cost {X Y} (f : X -> Y) xs :
  Cost.ticks (map_c (fun x => Cost.ret (f x)) xs) = N.of_nat (length xs).
Proof.
  rewrite ticks_map_c; induction xs as [|x xs IH]; [reflexivity|].
  cbn [fold_right length]; rewrite Cost.ticks_ret, IH, Nat2N.inj_succ; lia.
Qed.

(** System preparation charges edge enumeration and all seed, flow and append cell visits. *)
Theorem system_cost {N E A} (D : t N E A) :
  Cost.ticks (system_c D) =
    (Cost.ticks (fw_edges_c (cfg D)) + 2 * N.of_nat (length (seeds D)) +
      N.of_nat (length (Cfg.edges (cfg D))))%N.
Proof.
  unfold system_c; rewrite !Cost.ticks_bind, !value_map_c, fw_edges_value.
  rewrite !map_ret_cost, ticks_app_c, !length_map, Cost.ticks_ret.
  nia.
Qed.

(** Lawful node, row and lattice dictionaries give all generated analysis laws. *)
Theorem analysis_laws {N E A} (D : t N E A) pol :
  encoding_laws (Cfg.node_enc (cfg D)) ->
  encoding_laws (Cfg.edge_enc (cfg D)) ->
  lattice_laws (lat D) -> Analysis.laws (analysis D pol).
Proof.
  intros HN HE HL; constructor; cbn [analysis].
  - exact HN.
  - apply constraint_enc_laws; assumption.
  - exact HL.
  - apply static_laws.
Qed.

(** Post-solutions are the listed optional boundary bounds and listed edge inequalities. *)
Theorem post_solution_iff {N E A} (D : t N E A) (s : N -> A) :
  lattice_laws (lat D) ->
  (post_solution (lat D) (system D) s <->
    (forall n a, In n (seeds D) -> boundary D n = Some a ->
      leb (lat D) a (s n) = true) /\
    (forall e, In e (Cfg.edges (cfg D)) ->
      leb (lat D) (transfer D e (s (from D e))) (s (into D e)) = true)).
Proof.
  intro HL; split.
  - intro Hpost; split.
    + intros n a Hn Ha.
      specialize (Hpost (Seed n)).
      assert (Hr : In (Seed n) (System.constraints (system D))).
      { rewrite system_rows; apply in_or_app; left; apply in_map; exact Hn. }
      destruct (Hpost Hr) as [Hbound _].
      rewrite (proj1 (system_callbacks D _)), (proj2 (system_callbacks D _)) in Hbound.
      change (leb (lat D)
        (match boundary D n with Some a => a | None => bot (lat D) end) (s n) = true)
        in Hbound.
      rewrite Ha in Hbound; exact Hbound.
    + intros e He; specialize (Hpost (Flow e)).
      assert (Hr : In (Flow e) (System.constraints (system D))).
      { rewrite system_rows; apply in_or_app; right; apply in_map; exact He. }
      exact (proj1 (Hpost Hr)).
  - intros [Hseed Hflow] [n|e] Hr.
    all: rewrite system_rows in Hr; apply in_app_or in Hr;
      destruct Hr as [Hr|Hr]; apply in_map_iff in Hr;
      destruct Hr as [x [Heq Hin]]; inversion Heq; subst.
    all: split.
    + change (leb (lat D)
        (match boundary D n with Some a => a | None => bot (lat D) end) (s n) = true).
      destruct (boundary D n) as [a|] eqn:Ha.
      * apply Hseed; assumption.
      * apply (bot_least HL).
    + intros y a Hside; contradiction.
    + apply Hflow; exact Hin.
    + intros y a Hside; contradiction.
Qed.

Arguments system_c {N E A} D : simpl never.
Arguments system {N E A} D : simpl never.
Arguments analysis_c {N E A} D pol : simpl never.
Arguments analysis {N E A} D pol : simpl never.

End Dense.
