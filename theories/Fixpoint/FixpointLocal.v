(** * Restricted local joining

    Discovery selects a finite dependency region before the total engine solves its rows.
    For example, an unrelated root selects a smaller system than a cyclic root.
    Builds on: FixpointLocalDiscover, FixpointTotal and FixpointPartial. *)

From Stdlib Require Import List Bool Arith NArith PArith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseCode BaseEq BaseMap BaseSet.
From Galois.Lattice Require Import LatticeCore.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointEval FixpointIndex
  FixpointPartial FixpointAnalysis FixpointSolver FixpointTotal FixpointLocalDiscover.
Import List.ListNotations Cost.Notations.

Module Local.

(** A local candidate carries an untrusted explored set and finite assignment. *)
Record result (X A : Type) := Result {
  explored : FinSet.t X;
  values : assignment X A
}.

Arguments Result {X A}.
Arguments explored {X A}.
Arguments values {X A}.

(** The discovery record separates unknown membership from selected-row membership. *)
Record region (X C : Type) := Region {
  unknowns : FinSet.t X;
  selected : FinSet.t C
}.

Arguments Region {X C}.
Arguments unknowns {X C}.
Arguments selected {X C}.

Fixpoint lefts_c {X C} (vs : list (X + C)) : Cost.t (list X) :=
  match vs with
  | [] => Cost.ret []
  | inl x :: rest => Cost.step ;; Cost.map (cons x) (lefts_c rest)
  | inr _ :: rest => Cost.step ;; lefts_c rest
  end.

Fixpoint rights_c {X C} (vs : list (X + C)) : Cost.t (list C) :=
  match vs with
  | [] => Cost.ret []
  | inl _ :: rest => Cost.step ;; rights_c rest
  | inr c :: rest => Cost.step ;; Cost.map (cons c) (rights_c rest)
  end.

(** Projection charges enumeration, filtering and construction of both canonical sets. *)
Definition project_c {X C} EX EC (vs : FinSet.t (X + C)) :=
  let* vertices := FinSet.elements_c vs in
  let* xs := lefts_c vertices in
  let* cs := rights_c vertices in
  let* keys := FinSet.of_list_c EX xs in
  let* rows := FinSet.of_list_c EC cs in
  Cost.ret (Region keys rows).

Definition project {X C} EX EC vs := Cost.value (@project_c X C EX EC vs).

(** Region projection exposes the two constructed finite sets without reducing their backends. *)
Theorem project_equation {X C} EX EC (vertices : FinSet.t (X + C)) :
  project EX EC vertices =
    Region (FinSet.of_list EX (Cost.value (lefts_c (FinSet.elements vertices))))
      (FinSet.of_list EC (Cost.value (rights_c (FinSet.elements vertices)))).
Proof.
  reflexivity.
Qed.

(** Indexed discovery keeps exhaustion distinct from a completed projected region. *)
Definition discover_indexed_c {X C A} (a : Analysis.t X C A) ix roots fuel
    : Cost.t (LocalDiscover.state (X + C) + region X C) :=
  let* discovered := LocalDiscover.run_c a ix roots fuel in
  match discovered with
  | inl state => Cost.ret (inl state)
  | inr vertices =>
    Cost.map inr (project_c (Analysis.key_enc a) (Analysis.row_enc a) vertices)
  end.

(** Public discovery prepares its original index once and needs no lattice termination data. *)
Definition discover_c {X C A} (a : Analysis.t X C A) roots fuel :=
  let* ix := index_system_c (Analysis.key_enc a) (Analysis.system a) (Analysis.static a) in
  discover_indexed_c a ix roots fuel.

Definition discover {X C A} (a : Analysis.t X C A) roots fuel :=
  Cost.value (discover_c a roots fuel).

(** Indexed discovery retains the raw traversal and adds projection only after completion. *)
Theorem discover_indexed_cost {X C A} (a : Analysis.t X C A) ix roots fuel :
  Cost.ticks (discover_indexed_c a ix roots fuel) =
    (Cost.ticks (LocalDiscover.run_c a ix roots fuel) +
      match LocalDiscover.run a ix roots fuel with
      | inl _ => 0%N
      | inr marked => Cost.ticks (project_c (Analysis.key_enc a) (Analysis.row_enc a) marked)
      end)%N.
Proof.
  unfold discover_indexed_c; rewrite Cost.ticks_bind.
  fold (LocalDiscover.run a ix roots fuel).
  destruct (LocalDiscover.run a ix roots fuel); rewrite ?Cost.ticks_ret, ?Cost.ticks_map;
    reflexivity.
Qed.

(** Public discovery prepends exactly one original-system index construction. *)
Theorem discover_cost {X C A} (a : Analysis.t X C A) roots fuel :
  Cost.ticks (discover_c a roots fuel) =
    (Cost.ticks (index_system_c (Analysis.key_enc a) (Analysis.system a) (Analysis.static a)) +
      Cost.ticks (discover_indexed_c a
        (index_system (Analysis.key_enc a) (Analysis.system a) (Analysis.static a))
        roots fuel))%N.
Proof.
  unfold discover_c; rewrite Cost.ticks_bind; reflexivity.
Qed.

(** Restriction changes the row list and retains all original computational callbacks. *)
Definition restrict {X C A} (a : Analysis.t X C A) cs : Analysis.t X C A :=
  Analysis.Make (Analysis.key_enc a) (Analysis.row_enc a) (Analysis.lat a)
    (System.Make cs (System.target_c (Analysis.system a)) (System.rhs_c (Analysis.system a)))
    (System.Static (System.deps_c (Analysis.static a))
      (System.side_targets_c (Analysis.static a))) (Analysis.policy a).

(** The selected filter retains source ordering and repeated row occurrences. *)
Definition rows_c {X C A} (a : Analysis.t X C A) (r : region X C) :=
  filter_c (fun c => FinSet.mem_c (Analysis.row_enc a) c (selected r))
    (System.constraints (Analysis.system a)).

Definition rows {X C A} (a : Analysis.t X C A) r := Cost.value (rows_c a r).

(** Filtering never introduces a constraint absent from the original system. *)
Theorem rows_incl {X C A} (a : Analysis.t X C A) r :
  incl (rows a r) (System.constraints (Analysis.system a)).
Proof.
  unfold rows, rows_c; rewrite value_filter_c.
  intros c Hc; apply filter_In in Hc; exact (proj1 Hc).
Qed.

(** A filtered row is an original occurrence with true selected-set membership. *)
Theorem rows_spec {X C A} (a : Analysis.t X C A) r c :
  In c (rows a r) <-> In c (System.constraints (Analysis.system a)) /\
    FinSet.mem (Analysis.row_enc a) c (selected r) = true.
Proof.
  unfold rows, rows_c; rewrite value_filter_c, filter_In; reflexivity.
Qed.

(** Restricted evaluation has exactly the original outputs and read trace. *)
Theorem restrict_outputs {X C A} (a : Analysis.t X C A) cs c s :
  Eval.outputs (Analysis.system (restrict a cs)) c s =
    Eval.outputs (Analysis.system a) c s.
Proof.
  rewrite !Eval.outputs_spec; reflexivity.
Qed.

(** Original termination data applies to every source-list restriction by actual membership. *)
Definition restriction_termination {X C A} (a : Analysis.t X C A)
    (HT : Terminates.t a) cs (Hsub : incl cs (System.constraints (Analysis.system a))) :
    Terminates.t (restrict a cs).
Proof.
  refine (@Terminates.Finite X C A (restrict a cs) (Terminates.inv HT) (Terminates.hgt HT)
    (Terminates.inv_bot HT) (Terminates.inv_join HT) _).
  intros s Hs c Hc xa Hxa.
  rewrite restrict_outputs in Hxa.
  exact (Terminates.inv_closed HT s Hs c (Hsub c Hc) xa Hxa).
Defined.

(** Indexed local solving uses termination data only after a completed discovery. *)
Definition run_indexed_c {X C A} (a : Analysis.t X C A) (HT : Terminates.t a)
    ix roots fuel : Cost.t (Outcome.t X A (result X A)) :=
  let* discovered := discover_indexed_c a ix roots fuel in
  match discovered with
  | inl _ => Cost.ret (Outcome.OutOfFuel Map.empty)
  | inr region =>
    let filtered := rows_c a region in
    let* _ := filtered in
    let* m := Total.run_c (restrict a (Cost.value filtered))
      (restriction_termination a HT (Cost.value filtered) (rows_incl a region)) in
    Cost.ret (Outcome.Solved (Result (unknowns region) m))
  end.

(** Local solving explicitly receives the height data needed by its restricted total call. *)
Definition run_c {X C A} (a : Analysis.t X C A) (HT : Terminates.t a) roots fuel :=
  let* ix := index_system_c (Analysis.key_enc a) (Analysis.system a) (Analysis.static a) in
  run_indexed_c a HT ix roots fuel.

Definition run {X C A} (a : Analysis.t X C A) HT roots fuel := Cost.value (run_c a HT roots fuel).

(** Indexed local outcomes expose discovery exhaustion or the actual restricted total assignment. *)
Theorem run_indexed_equation {X C A} (a : Analysis.t X C A) HT ix roots fuel :
  Cost.value (run_indexed_c a HT ix roots fuel) =
    match Cost.value (discover_indexed_c a ix roots fuel) with
    | inl _ => Outcome.OutOfFuel Map.empty
    | inr region => Outcome.Solved (Result (unknowns region)
      (Total.run (restrict a (rows a region))
        (restriction_termination a HT (rows a region) (rows_incl a region))))
    end.
Proof.
  unfold run_indexed_c; rewrite Cost.value_bind.
  destruct (Cost.value (discover_indexed_c a ix roots fuel));
    rewrite ?Cost.value_bind, ?Cost.value_ret; reflexivity.
Qed.

(** Local solving retains discovery, filtering and the actual restricted total computation. *)
Theorem run_cost {X C A} (a : Analysis.t X C A) HT roots fuel :
  Cost.ticks (run_c a HT roots fuel) =
    (Cost.ticks (discover_c a roots fuel) +
      match Cost.value (discover_indexed_c a
        (index_system (Analysis.key_enc a) (Analysis.system a) (Analysis.static a)) roots fuel) with
      | inl _ => 0%N
      | inr r => Cost.ticks (rows_c a r) +
          Cost.ticks (Total.run_c (restrict a (rows a r))
            (restriction_termination a HT (rows a r) (rows_incl a r)))
      end)%N.
Proof.
  rewrite discover_cost.
  unfold run_c, run_indexed_c; rewrite !Cost.ticks_bind.
  fold (index_system (Analysis.key_enc a) (Analysis.system a) (Analysis.static a)).
  destruct (Cost.value (discover_indexed_c a
    (index_system (Analysis.key_enc a) (Analysis.system a) (Analysis.static a)) roots fuel))
    as [state|r]; rewrite ?Cost.ticks_bind, ?Cost.ticks_ret.
  - lia.
  - fold (rows a r); lia.
Qed.

(** Public local solving uses the internally prepared original-system index. *)
Theorem run_equation {X C A} (a : Analysis.t X C A) HT roots fuel :
  run a HT roots fuel =
    Cost.value (run_indexed_c a HT
      (index_system (Analysis.key_enc a) (Analysis.system a) (Analysis.static a)) roots fuel).
Proof.
  unfold run, run_c; rewrite Cost.value_bind; reflexivity.
Qed.

(** A candidate gate normalizes untrusted explored keys, checks partial closure and covers roots. *)
Definition check_c {X C A} (a : Analysis.t X C A) ix roots (candidate : result X A)
    : Cost.t (Outcome.t X A (result X A)) :=
  let* vertices := FinSet.elements_c (explored candidate) in
  let* region := FinSet.of_list_c (Analysis.key_enc a) vertices in
  let* partial := check_partial_c (Analysis.key_enc a) (Analysis.row_enc a)
    (Analysis.lat a) (Analysis.system a) (Analysis.static a) ix region (values candidate) in
  let* covered := forallb_c (fun x => FinSet.mem_c (Analysis.key_enc a) x region) roots in
  Cost.ret (if partial && covered then Outcome.Solved (Result region (values candidate))
    else Outcome.Rejected Reason.Check_failed).

Definition check {X C A} (a : Analysis.t X C A) ix roots candidate :=
  Cost.value (check_c a ix roots candidate).

(** Checked local solving shares the original index between discovery and the partial checker. *)
Definition checked_c {X C A} (a : Analysis.t X C A) (HT : Terminates.t a) roots fuel :=
  let* ix := index_system_c (Analysis.key_enc a) (Analysis.system a) (Analysis.static a) in
  let* solved := run_indexed_c a HT ix roots fuel in
  match solved with
  | Outcome.Solved candidate => check_c a ix roots candidate
  | Outcome.OutOfFuel have => Cost.ret (Outcome.OutOfFuel have)
  | Outcome.Rejected why => Cost.ret (Outcome.Rejected why)
  end.

Definition checked {X C A} (a : Analysis.t X C A) HT roots fuel :=
  Cost.value (checked_c a HT roots fuel).

(** Checked solving reuses the index and adds its successful candidate's partial gate. *)
Theorem checked_cost {X C A} (a : Analysis.t X C A) HT roots fuel :
  Cost.ticks (checked_c a HT roots fuel) =
    (Cost.ticks (run_c a HT roots fuel) +
      match run a HT roots fuel with
      | Outcome.Solved candidate => Cost.ticks (check_c a
        (index_system (Analysis.key_enc a) (Analysis.system a) (Analysis.static a)) roots candidate)
      | _ => 0%N
      end)%N.
Proof.
  rewrite run_equation.
  unfold checked_c, run_c; rewrite !Cost.ticks_bind.
  fold (index_system (Analysis.key_enc a) (Analysis.system a) (Analysis.static a)).
  destruct (Cost.value (run_indexed_c a HT
    (index_system (Analysis.key_enc a) (Analysis.system a) (Analysis.static a)) roots fuel));
    rewrite ?Cost.ticks_ret; lia.
Qed.

(** Checked local outcomes apply the partial gate only to the successful producer result. *)
Theorem checked_equation {X C A} (a : Analysis.t X C A) HT roots fuel :
  checked a HT roots fuel =
    match run a HT roots fuel with
    | Outcome.Solved candidate => check a
      (index_system (Analysis.key_enc a) (Analysis.system a) (Analysis.static a)) roots candidate
    | Outcome.OutOfFuel have => Outcome.OutOfFuel have
    | Outcome.Rejected why => Outcome.Rejected why
    end.
Proof.
  unfold checked, checked_c; rewrite !Cost.value_bind, run_equation.
  fold (index_system (Analysis.key_enc a) (Analysis.system a) (Analysis.static a)).
  destruct (Cost.value (run_indexed_c a HT
    (index_system (Analysis.key_enc a) (Analysis.system a) (Analysis.static a)) roots fuel));
    rewrite ?Cost.value_ret; reflexivity.
Qed.

(** The candidate equation exposes the existing partial checker and the explicit root guard. *)
Theorem check_equation {X C A} (a : Analysis.t X C A) ix roots candidate :
  check a ix roots candidate =
    let region := FinSet.of_list (Analysis.key_enc a) (FinSet.elements (explored candidate)) in
    if check_partial (Analysis.key_enc a) (Analysis.row_enc a) (Analysis.lat a)
      (Analysis.system a) (Analysis.static a) ix region (values candidate) &&
      forallb (fun x => FinSet.mem (Analysis.key_enc a) x region) roots
    then Outcome.Solved (Result region (values candidate))
    else Outcome.Rejected Reason.Check_failed.
Proof.
  unfold check, check_c; autorewrite with galois_cost; reflexivity.
Qed.

(** Accepted external candidates satisfy the existing closed-partial semantics and cover roots. *)
Theorem check_sound {X C A} (a : Analysis.t X C A) ix roots candidate r :
  Analysis.laws a ->
  sys_index_laws (Analysis.key_enc a) (Analysis.system a) (Analysis.static a) ix ->
  check a ix roots candidate = Outcome.Solved r ->
  FinSet.wf (Analysis.key_enc a) (explored r) /\
  closed_partial (Analysis.key_enc a) (Analysis.lat a) (Analysis.system a)
    (Analysis.static a) (explored r)
    (lookup (Analysis.key_enc a) (Analysis.lat a) (values r)) /\
  forall x, In x roots -> FinSet.mem (Analysis.key_enc a) x (explored r) = true.
Proof.
  intros HL HI Hcheck; rewrite check_equation in Hcheck.
  cbn zeta in Hcheck.
  match type of Hcheck with
  | (if ?guard then _ else _) = _ => destruct guard eqn:Htest
  end; [|discriminate].
  injection Hcheck as <-; cbn [explored values].
  apply andb_true_iff in Htest as [Hpartial Hroots].
  split; [apply FinSet.wf_of_list|]; split.
  - exact (check_partial_sound (Analysis.key_enc a) (Analysis.row_enc a)
      (Analysis.key_laws HL) (Analysis.row_laws HL) (Analysis.lat a) (Analysis.system a)
      (Analysis.static a) ix _ (values candidate) HI (FinSet.wf_of_list _ _) Hpartial).
  - apply (proj1 (forallb_forall _ _) Hroots).
Qed.

Arguments discover_c {X C A} a roots fuel : simpl never.
Arguments discover {X C A} a roots fuel : simpl never.
Arguments run_c {X C A} a HT roots fuel : simpl never.
Arguments run {X C A} a HT roots fuel : simpl never.
Arguments checked_c {X C A} a HT roots fuel : simpl never.
Arguments checked {X C A} a HT roots fuel : simpl never.

End Local.
Import Local.
