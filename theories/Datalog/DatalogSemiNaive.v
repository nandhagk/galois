(** * Pivot-based semi-naive stratum evaluation

    A stratum keeps accumulated facts, a frontier and incrementally maintained nested Join plans.
    For example, two recursive occurrences produce two jobs that choose different frontier pivots.
    Builds on: DatalogJoin, DatalogJoinPreparedFire, DatalogSolve and CostLoop. *)

From Stdlib Require Import List Bool PeanoNat PArith.
From Galois.Cost Require Import CostMonad CostList CostLoop.
From Galois.Base Require Import BaseEncoding BaseCode BaseMap BaseSet.
From Galois.Lattice Require Import LatticeCore LatticeSet.
From Galois.Fixpoint Require Import FixpointSolver.
From Galois.Datalog Require Import DatalogSyntax DatalogStratify DatalogRelation DatalogFire
  DatalogJoin DatalogJoinPreparedFire DatalogSolve.
Import List.ListNotations Cost.Notations.
Local Open Scope nat_scope.

Module SemiNaive.

(** Ground-fact storage keeps predicates in the key so a batch can span several relations. *)
Definition ground_encoding {P} (prog : program P) :=
  pair_encoding (penc prog) tuple_encoding.

(** Each position counts positive occurrences, including repeated identical atoms. *)
Fixpoint pivots_from_c {P} (st : stratification P) k position (ls : list (literal P))
    : Cost.t (list nat) :=
  match ls with
  | [] => Cost.ret []
  | LNeg _ :: rest => Cost.step ;; pivots_from_c st k position rest
  | LPos a :: rest =>
    Cost.step ;;
    let* next := pivots_from_c st k (S position) rest in
    Cost.step ;;
    let* lev := level_c st (pred a) in
    Cost.ret (if Nat.eqb lev k then position :: next else next)
  end.

Definition pivots {P} st k r := Cost.value (@pivots_from_c P st k 0 (body r)).

Definition classify_one_c {P} (st : stratification P) k (r : rule P)
    (acc : list (rule P) * list (rule P * nat)) :=
  Cost.step ;;
  let* lev := level_c st (pred (head r)) in
  if Nat.eqb lev k then
    let* positions := pivots_from_c st k 0 (body r) in
    match positions with
    | [] => Cost.ret (r :: fst acc, snd acc)
    | _ :: _ =>
      let* specs := map_c (fun position => Cost.ret (r, position)) positions in
      let* tail := app_c specs (snd acc) in
      Cost.ret (fst acc, tail)
    end
  else Cost.ret acc.

(** Classification retains every source rule and recursive positive occurrence in source order. *)
Definition classify_c {P} (st : stratification P) k (rs : list (rule P)) :=
  fold_right_c (classify_one_c st k) ([], []) rs.

Definition classify {P} st k rs := Cost.value (@classify_c P st k rs).

(** Tagging chooses one positive occurrence and leaves every negative literal on the full side. *)
Fixpoint tag_body_from_c {P} pivot position (ls : list (literal P))
    : Cost.t (list (literal (P * bool))) :=
  match ls with
  | [] => Cost.ret []
  | LPos a :: rest =>
    Cost.step ;;
    let* tail := tag_body_from_c pivot (S position) rest in
    Cost.ret (LPos (Atom (pred a, Nat.eqb position pivot) (args a)) :: tail)
  | LNeg a :: rest =>
    Cost.step ;;
    let* tail := tag_body_from_c pivot position rest in
    Cost.ret (LNeg (Atom (pred a, false) (args a)) :: tail)
  end.

Definition tag_rule_c {P} (r : rule P) pivot :=
  let* ls := tag_body_from_c pivot 0 (body r) in
  Cost.ret (Rule (Atom (pred (head r), false) (args (head r))) ls).

Definition tag_rule {P} r pivot := Cost.value (@tag_rule_c P r pivot).

Definition tag_program {P} (prog : program P) :=
  Program (pair_encoding (penc prog) bool_encoding) (fun q => arity_c prog (fst q)) [].

(** Same-level reads use accumulated rows and other reads use the fixed lower environment. *)
Definition current_c {P} (prog : program P) (st : stratification P) k
    (lower : P -> Cost.t relation) (acc : database P) p :=
  Cost.step ;;
  let* lev := level_c st p in
  Cost.step ;;
  if Nat.eqb lev k then rel_of_c prog acc p else lower p.

Definition current {P} prog st k lower acc p :=
  Cost.value (@current_c P prog st k lower acc p).

(** A tagged pivot reads the frontier while every other positive occurrence reads current rows. *)
Definition tagged_c {P} (prog : program P) st k lower acc front (q : P * bool) :=
  if snd q then rel_of_c prog front (fst q) else current_c prog st k lower acc (fst q).

Definition tagged {P} prog st k lower acc front q :=
  Cost.value (@tagged_c P prog st k lower acc front q).

(** Batch insertion updates the predicate index from supplied rows without enumerating old rows. *)
Definition add_atoms_c {P} (prog : program P) (xs : list (ground_atom P))
    (db : database P) :=
  fold_right_c (fun f acc =>
    Cost.step ;;
    let* old := rel_of_c prog acc (fst f) in
    let* extended := set_add_c tuple_encoding (snd f) old in
    Map.set_c (penc prog) (fst f) extended acc) db xs.

Definition add_atoms {P} prog xs db := Cost.value (@add_atoms_c P prog xs db).

(** A job caches its source rule, occurrence position, tagged rule and fixed Join layout. *)
Record job (P : Type) : Type := Job {
  source_rule : rule P;
  pivot : nat;
  tagged_rule : rule (P * bool);
  plan : Join.plan_state (P * bool)
}.

Arguments Job {P}.
Arguments source_rule {P}.
Arguments pivot {P}.
Arguments tagged_rule {P}.
Arguments plan {P}.

Definition prepare_job_c {P} (prog : program P) env (spec : rule P * nat) :=
  let* r := tag_rule_c (fst spec) (snd spec) in
  let* ps := positive_atoms_c (body r) in
  let* prepared := Join.prepare_c (tag_program prog) ps env in
  Cost.ret (Job (fst spec) (snd spec) r prepared).

(** State is computational data and has no semantic or termination proof fields. *)
Record state (P : Type) : Type := State {
  accumulated : FinSet.t (ground_atom P);
  frontier : FinSet.t (ground_atom P);
  accumulated_index : database P;
  frontier_index : database P;
  jobs : list (job P)
}.

Arguments State {P}.
Arguments accumulated {P}.
Arguments frontier {P}.
Arguments accumulated_index {P}.
Arguments frontier_index {P}.
Arguments jobs {P}.

Definition seed_rules_c {P} (prog : program P) (rs : list (rule P)) lower :=
  fold_right_c (fun r acc =>
    let* rel := PreparedFire.fire_c prog r lower in
    let* rows := FinSet.elements_c (set_raw rel) in
    let* here := map_c (fun row => Cost.ret (pred (head r), row)) rows in
    app_c here acc) [] rs.

(** Facts and rules without same-level positives seed the accumulated set and frontier. *)
Definition initial_c {P} (prog : program P) (facts : list (ground_atom P)) st lower k :=
  let* classified := classify_c st k (rules prog) in
  let* seeds := filter_c (fun f =>
    Cost.step ;;
    let* lev := level_c st (fst f) in Cost.ret (Nat.eqb lev k)) facts in
  let* nonrecursive := seed_rules_c prog (fst classified) lower in
  let* all_seeds := app_c seeds nonrecursive in
  let* known := FinSet.of_list_c (ground_encoding prog) all_seeds in
  let* rows := FinSet.elements_c known in
  let* indexed := add_atoms_c prog rows Map.empty in
  let* prepared := map_c (prepare_job_c prog (tagged_c prog st k lower indexed indexed))
    (snd classified) in
  Cost.ret (State known known indexed indexed prepared).

Definition initial {P} prog facts st lower k := Cost.value (@initial_c P prog facts st lower k).

(** Each cached occurrence-pivot job contributes all of its actual indexed firing results. *)
Definition candidates_c {P} (prog : program P) st lower k (s : state P) :=
  let* rows := fold_right_c (fun j acc =>
    let* rel := Join.fire_c (tagged_rule j)
      (tagged_c prog st k lower (accumulated_index s) (frontier_index s)) (plan j) in
    let* tuples := FinSet.elements_c (set_raw rel) in
    let* here := map_c (fun row => Cost.ret (pred (head (source_rule j)), row)) tuples in
    app_c here acc) [] (jobs s) in
  FinSet.of_list_c (ground_encoding prog) rows.

Definition candidates {P} prog st lower k s :=
  Cost.value (@candidates_c P prog st lower k s).

(** Difference traverses candidates independently of accumulated cardinality. *)
Definition new_c {P} prog st lower k (s : state P) :=
  let* offered := candidates_c prog st lower k s in
  FinSet.diff_c offered (accumulated s).

Definition fresh {P} prog st lower k s := Cost.value (@new_c P prog st lower k s).

Definition batch_rows_c {P} (prog : program P) (batch : database P) (q : P * bool) :=
  let* rel := rel_of_c prog batch (fst q) in FinSet.elements_c (set_raw rel).

Definition update_job_c {P} (prog : program P) (batch : database P) (j : job P) :=
  let* next := Join.insert_rows_c (fun q => Cost.ret (snd q))
    (batch_rows_c prog batch) (plan j) in
  Cost.ret (Job (source_rule j) (pivot j) (tagged_rule j) next).

(** Advancement resets frontier indexes and extends accumulated indexes from the fresh batch. *)
Definition advance_c {P} (prog : program P) (s : state P) batch :=
  let* rows := FinSet.elements_c batch in
  let* known := FinSet.union_c (accumulated s) batch in
  let* indexed := add_atoms_c prog rows (accumulated_index s) in
  let* next_front := add_atoms_c prog rows Map.empty in
  let* updated := map_c (update_job_c prog next_front) (jobs s) in
  Cost.ret (State known batch indexed next_front updated).

Definition advance {P} prog s batch := Cost.value (@advance_c P prog s batch).

(** A stationary candidate difference stops before another index-maintenance pass. *)
Definition step_c {P} (prog : program P) st lower k (s : state P)
    : Cost.t (state P + state P) :=
  let* batch := new_c prog st lower k s in
  let* empty := FinSet.is_empty_c batch in
  if empty then Cost.ret (inr s) else Cost.map inl (advance_c prog s batch).

Definition step {P} prog st lower k s := Cost.value (@step_c P prog st lower k s).

(** The only round driver is the common binary-fuel iterator. *)
Definition run_c {P} prog st lower k fuel (s : state P) :=
  iterate (step_c prog st lower k) fuel s.

Definition run {P} prog st lower k fuel s := Cost.value (@run_c P prog st lower k fuel s).

(** Exhaustion exposes the interrupted local assignment and never marks it as solved. *)
Definition stratum_c {P} (prog : program P) facts st lower k (fuel : positive)
    : Cost.t (Outcome.t P relation (database P)) :=
  let* start := initial_c prog facts st lower k in
  let* result := run_c prog st lower k fuel start in
  match result with
  | inl interrupted =>
    Cost.ret (Outcome.OutOfFuel (accumulated_index interrupted))
  | inr stopped => Cost.ret (Outcome.Solved (accumulated_index stopped))
  end.

Definition stratum {P} prog facts st lower k fuel :=
  Cost.value (@stratum_c P prog facts st lower k fuel).

Arguments initial_c {P} prog facts st lower k : simpl never.
Arguments step_c {P} prog st lower k s : simpl never.
Arguments stratum_c {P} prog facts st lower k fuel : simpl never.

End SemiNaive.
Import SemiNaive.
