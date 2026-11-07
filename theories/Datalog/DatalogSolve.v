(** * Fuelled reference solving of stratified programs

    Each level passes through certified analysis and stores its current-stratum relations.
    For example, exhausted fuel propagates an unchecked local stratum assignment.
    Builds on: DatalogExact and FixpointAnalyze. *)

From Stdlib Require Import List Bool PeanoNat PArith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap.
From Galois.Lattice Require Import LatticeCore LatticeSet.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointLeast FixpointAnalysis
  FixpointAnalyze FixpointCertified FixpointSolver FixpointKleene.
From Galois.Datalog Require Import DatalogSyntax DatalogStratify DatalogModel
  DatalogRelation DatalogFire DatalogCompile DatalogCompileProof DatalogExact.
Import List.ListNotations Cost.Notations.

(** A database stores representation-valid finite relations. *)
Definition database P := Map.t P relation.

Definition rel_of_c {P} (prog : program P) (db : database P) :=
  lookup_c (penc prog) relation_lattice db.
Definition rel_of {P} prog db p := Cost.value (@rel_of_c P prog db p).
Definition db_holds {P} prog db p ts := member ts (@rel_of P prog db p).

(** Storage invokes costed lookups and retains all map construction costs. *)
Definition store_relations_c {P} (prog : program P) (ps : list P)
    (s : P -> Cost.t relation) (db : database P) :=
  fold_right_c (fun p acc =>
    Cost.step ;;
    let* value := s p in Map.set_c (penc prog) p value acc) db ps.

Definition store_relations {P} prog ps s db :=
  Cost.value (@store_relations_c P prog ps s db).

Lemma store_relations_equation {P} (prog : program P) ps s db :
  store_relations prog ps s db =
    fold_right (fun p acc => Map.set (penc prog) p (Cost.value (s p)) acc) db ps.
Proof.
  unfold store_relations, store_relations_c; rewrite value_fold_right_c.
  apply f_equal2; [|reflexivity].
  reflexivity.
Qed.

Definition stratum_targets_c {P} (prog : program P) facts st k :=
  let* cs := stratum_constraints_c prog facts st k in
  map_c (fun c => Cost.ret (Constraint.target c)) cs.
Definition stratum_targets {P} prog facts st k :=
  Cost.value (@stratum_targets_c P prog facts st k).

Lemma stratum_targets_equation {P} (prog : program P) facts st k :
  stratum_targets prog facts st k =
    map Constraint.target (stratum_constraints prog facts st k).
Proof.
  unfold stratum_targets, stratum_targets_c; rewrite Cost.value_bind, value_map_c; reflexivity.
Qed.

(** Only a successful input invokes the second solver callback and retains its invocation charge. *)
Definition finish_stratum_c {P R} (a : Analysis.t P (Constraint.t P) relation) fuel
    (certified : Outcome.t P relation R)
    : Cost.t (Outcome.t P relation (database P)) :=
  match certified with
  | Outcome.OutOfFuel have => Cost.ret (Outcome.OutOfFuel have)
  | Outcome.Rejected why => Cost.ret (Outcome.Rejected why)
  | Outcome.Solved _ => Cost.step ;; Solver.run_c Kleene.solver a fuel
  end.

(** The second reference run recovers a costed map because analyze_ref exposes a pure function. *)
Definition solve_stratum_c {P} (prog : program P) facts st lower k fuel
    : Cost.t (Outcome.t P relation (database P)) :=
  let* a := stratum_analysis_c prog facts st lower k in
  let* certified := analyze_ref_c a fuel in
  finish_stratum_c a fuel certified.

Definition solve_stratum {P} prog facts st lower k fuel :=
  Cost.value (@solve_stratum_c P prog facts st lower k fuel).

Lemma solve_stratum_equation {P} (prog : program P) facts st lower k fuel :
  solve_stratum prog facts st lower k fuel =
    match analyze_ref (stratum_analysis prog facts st lower k) fuel with
    | Outcome.OutOfFuel have => Outcome.OutOfFuel have
    | Outcome.Rejected why => Outcome.Rejected why
    | Outcome.Solved _ => Solver.run Kleene.solver
        (stratum_analysis prog facts st lower k) fuel
    end.
Proof.
  unfold solve_stratum, solve_stratum_c; repeat rewrite Cost.value_bind.
  fold (@stratum_analysis P prog facts st lower k).
  fold (analyze_ref (stratum_analysis prog facts st lower k) fuel).
  destruct (analyze_ref (stratum_analysis prog facts st lower k) fuel); reflexivity.
Qed.

Fixpoint solve_levels_c {P} (prog : program P) facts st fuel n
    : Cost.t (Outcome.t P relation (database P)) :=
  match n with
  | 0 => Cost.ret (Outcome.Solved Map.empty)
  | S k =>
    Cost.step ;;
    let* previous := solve_levels_c prog facts st fuel k in
    match previous with
    | Outcome.OutOfFuel have => Cost.ret (Outcome.OutOfFuel have)
    | Outcome.Rejected why => Cost.ret (Outcome.Rejected why)
    | Outcome.Solved db =>
      let* current := solve_stratum_c prog facts st (rel_of_c prog db) k fuel in
      match current with
      | Outcome.OutOfFuel have => Cost.ret (Outcome.OutOfFuel have)
      | Outcome.Rejected why => Cost.ret (Outcome.Rejected why)
      | Outcome.Solved m =>
        let* ps := stratum_targets_c prog facts st k in
        Cost.map Outcome.Solved (store_relations_c prog ps (rel_of_c prog m) db)
      end
    end
  end.

Definition solve_levels {P} prog facts st fuel n :=
  Cost.value (@solve_levels_c P prog facts st fuel n).

Lemma solve_levels_equation {P} (prog : program P) facts st fuel n :
  solve_levels prog facts st fuel n =
  match n with
  | 0 => Outcome.Solved Map.empty
  | S k =>
    match solve_levels prog facts st fuel k with
    | Outcome.OutOfFuel have => Outcome.OutOfFuel have
    | Outcome.Rejected why => Outcome.Rejected why
    | Outcome.Solved db =>
      match solve_stratum prog facts st (rel_of_c prog db) k fuel with
      | Outcome.OutOfFuel have => Outcome.OutOfFuel have
      | Outcome.Rejected why => Outcome.Rejected why
      | Outcome.Solved m => Outcome.Solved (store_relations prog
          (stratum_targets prog facts st k) (rel_of_c prog m) db)
      end
    end
  end.
Proof.
  destruct n as [|k]; [reflexivity |].
  unfold solve_levels at 1; cbn [solve_levels_c]; repeat rewrite Cost.value_bind.
  fold (@solve_levels P prog facts st fuel k).
  destruct (solve_levels prog facts st fuel k) as [db | have | why]; try reflexivity.
  rewrite Cost.value_bind; fold (@solve_stratum P prog facts st (rel_of_c prog db) k fuel).
  destruct (solve_stratum prog facts st (rel_of_c prog db) k fuel);
    try reflexivity.
Qed.

(** The executable solver needs program data and fuel, with no law or termination proofs. *)
Definition solve_program_c {P} (prog : program P) facts fuel
    : Cost.t (Outcome.t P relation (database P)) :=
  let* checked := stratify_c prog in
  match checked with
  | None => Cost.ret (Outcome.Rejected Reason.Bad_stratification)
  | Some st => solve_levels_c prog facts st fuel (count st)
  end.

Definition solve_program {P} prog facts fuel := Cost.value (@solve_program_c P prog facts fuel).

Lemma solve_program_equation {P} (prog : program P) facts fuel :
  solve_program prog facts fuel =
    match stratify prog with
    | None => Outcome.Rejected Reason.Bad_stratification
    | Some st => solve_levels prog facts st fuel (count st)
    end.
Proof.
  unfold solve_program, solve_program_c; rewrite Cost.value_bind; fold (@stratify P prog).
  destruct (stratify prog); reflexivity.
Qed.

(** A program without a source stratification is explicitly rejected for every fuel. *)
Theorem solve_program_none {P} (prog : program P) facts fuel :
  (forall st, ~ stratified prog st) ->
  solve_program prog facts fuel = Outcome.Rejected Reason.Bad_stratification.
Proof.
  intro Hnone; rewrite solve_program_equation; destruct (stratify prog) as [st |] eqn:Hst;
    [|reflexivity].
  exfalso; apply (Hnone st), (stratify_sound prog st Hst).
Qed.

Arguments solve_program_c {P} prog facts fuel : simpl never.
Arguments solve_program {P} prog facts fuel : simpl never.
