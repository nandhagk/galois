(** * Rule application and checked saturation plans

    Runs use semi-naive rounds followed by a naive confirmation round.
    For example, a quiet confirmation round returns [Saturated] and establishes closure.
    Builds on: ValueSig, IndexSig, JoinSig, DatabaseSig and Model. *)

From Stdlib Require Import List PArith NArith Relations.Relation_Operators.
From Argent Require Import Time Std.
From Galois.Base Require Import Loop.
From Galois.Egglog Require Import ValueSig IndexSig JoinSig DatabaseSig Syntax Model.

Import List.ListNotations.

Fixpoint binding_env {V} (vars : list positive) (cells : list (cell V))
    (x : positive) : option (cell V) :=
  match vars, cells with
  | v :: vs, c :: cs => if Pos.eqb x v then Some c else binding_env vs cs x
  | _, _ => None
  end.
TimeFun binding_env.

Module Type RUN_OPS (V : VALUE_OPS) (I : INDEX_OPS V) (J : JOIN_OPS V I)
    (D : DATABASE_OPS V I).
  Parameter plan : program V.t -> compiled V.t.
  Parameter check_plan : program V.t -> compiled V.t -> bool.
  Parameter load : program V.t -> compiled V.t -> D.t.
  Parameter round : program V.t -> compiled V.t -> bool -> D.t -> D.t.
  Parameter run : program V.t -> compiled V.t -> limits -> D.t -> stop * D.t.
End RUN_OPS.

Module Type RUN_SPEC (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (Import X : RUN_OPS V I J D).
  Definition plans_ok (p : program V.t) (cp : compiled V.t) : Prop :=
    check_plan p cp = true.
  Definition grows (db db' : D.t) : Prop :=
    (forall i j, same (D.view db) i j -> same (D.view db') i j) /\
    (forall f k o, row (D.view db) f k o -> exists o',
      row (D.view db') f (map (D.canon db') k) o' /\
      D.out_le db' f (option_map (D.canon db') o) o').
  Definition no_ids (db : D.t) : Prop :=
    D.ids db = 0%N /\
    forall f k o, row (D.view db) f k o -> o = None /\
      Forall (fun c => exists v, c = Val v) k.
  Definition includes (a b : Model.view (V := V.t)) : Prop :=
    forall f k o, row a f k o -> row b f k o.
  Definition all_plans (cp : compiled V.t) := naive V.t cp ++ seminaive V.t cp.
  Definition env_of (c : cplan V.t) (b : list (cell V.t)) :=
    binding_env (var_of V.t c) b.
  Definition source_index (db : D.t) (s : source V.t) : I.t :=
    match s with
    | All _ slot => D.index slot false db
    | New _ slot => D.index slot true db
    | Const _ c => I.insert [c] I.empty
    end.
  Definition bindings (_ : compiled V.t) (c : cplan V.t) (db : D.t) :=
    J.run (join V.t c) (map (source_index db) (sources V.t c)).
End RUN_SPEC.

Module Type RUN_LAWS (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (Import X : RUN_OPS V I J D) (Import XS : RUN_SPEC V I J D X).
  (* spec: herbrand *)
  Parameter herbrand : program V.t -> D.t -> nat.
  (** Loading initializes precisely the declarations and compiled index slots. *)
  Parameter load_spec : forall p cp,
    load p cp = D.init (decls V.t p) (Syntax.slots V.t cp).
  (** Every checked run retains well-formedness and ends on canonical rows. *)
  Parameter run_wf : forall p cp lim db, plans_ok p cp -> D.wf db ->
    D.wf (snd (run p cp lim db)) /\ D.canonical (snd (run p cp lim db)).
  (** Every old equality and row persists modulo the final canonicalization. *)
  Parameter run_grows : forall p cp lim db, plans_ok p cp -> D.wf db ->
    grows db (snd (run p cp lim db)).
  (** Running valid rules keeps every satisfying model and old allocated identifier meaning. *)
  Parameter run_sat : forall p cp lim db (M : model (V := V.t)) nu,
    plans_ok p cp -> D.wf db -> valid V.prim V.merge M p ->
    sat V.merge M nu (D.view db) -> exists nu',
      (forall i, D.allocated db i -> nu' i = nu i) /\
      sat V.merge M nu' (D.view (snd (run p cp lim db))).
  (** Saturation establishes every rule's closure obligation. *)
  Parameter run_closed : forall p cp lim db db', plans_ok p cp -> D.wf db ->
    run p cp lim db = (Saturated, db') -> closed V.prim V.merge p (D.view db').
  (** Relational runs insert only rows justified by finite rule derivations. *)
  Parameter run_derives : forall p cp lim db f k o, plans_ok p cp -> D.wf db ->
    relational_fragment p = true -> no_ids db ->
    row (D.view (snd (run p cp lim db))) f k o -> derives V.prim p (D.view db) f k.
  (** A saturated relational result is included in every closed extension of its seed. *)
  Parameter run_least : forall p cp lim db db', plans_ok p cp -> D.wf db ->
    relational_fragment p = true -> no_ids db -> run p cp lim db = (Saturated, db') ->
    forall w, closed V.prim V.merge p w -> includes (D.view db) w ->
      includes (D.view db') w.
  (** A relational run reaches saturation within its finite Herbrand budget. *)
  Parameter run_terminates : forall p cp lim db, plans_ok p cp -> D.wf db ->
    relational_fragment p = true -> no_ids db ->
    N.to_nat (max_iter lim) >= 2 * herbrand p db + 2 ->
    fst (run p cp lim db) = Saturated.
  (** Identifier exhaustion reports allocation above the caller's identifier limit. *)
  Parameter run_limits : forall p cp lim db, fst (run p cp lim db) = IdLimit ->
    (D.ids (snd (run p cp lim db)) > max_ids lim)%N.
End RUN_LAWS.

Module Type RUN (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I) :=
  RUN_OPS V I J D <+ RUN_SPEC V I J D <+ RUN_LAWS V I J D.

Module Type RUN_TIME (V : VALUE_T) (I : INDEX_T V) (J : JOIN_T V I)
    (D : DATABASE_T V I) (Import X : RUN V I J D).
  (* spec: trace round_work act_unit overshoot size_program size_compiled wbits *)
  Parameter trace : program V.t -> compiled V.t -> limits -> D.t -> list (bool * D.t).
  Parameter round_work : program V.t -> compiled V.t -> bool -> D.t -> nat.
  Parameter act_unit : program V.t -> N -> D.t -> N.
  Parameter overshoot : program V.t -> N.
  Parameter size_program : program V.t -> nat.
  Parameter size_compiled : compiled V.t -> nat.
  Parameter wbits : program V.t -> nat.
  Parameter T_plan : program V.t -> N.
  Parameter T_check_plan : program V.t -> compiled V.t -> N.
  Parameter T_load : program V.t -> compiled V.t -> N.
  Parameter T_round : program V.t -> compiled V.t -> bool -> D.t -> N.
  Parameter T_run : program V.t -> compiled V.t -> limits -> D.t -> N.
  Parameter c_run : N.
  (** Running pays for traced round work, binary fuel overhead and initial potential. *)
  Parameter T_run_le : forall p cp lim db, plans_ok p cp -> D.wf db ->
    let B := (max_ids lim + overshoot p)%N in
    (T_run p cp lim db <= c_run *
      (fold_right N.add 0 (map (fun start =>
        N.of_nat (round_work p cp (fst start) (snd start) + 1) *
          act_unit p B (snd start)) (trace p cp lim db)) +
        N.of_nat (N.size_nat (max_iter lim) + 1)) + D.potential B db)%N.
  (** Plan checking pays for program and plan syntax at their identifier width. *)
  Parameter T_check_plan_le : forall p cp,
    (T_check_plan p cp <= c_run * N.of_nat (size_program p + size_compiled cp + 1) *
      N.of_nat (wbits p + 1))%N.
End RUN_TIME.

Module Type RUN_T (V : VALUE_T) (I : INDEX_T V) (J : JOIN_T V I)
    (D : DATABASE_T V I) := RUN V I J D <+ RUN_TIME V I J D.

Module Type RUN_PLAN (V : VALUE_T) (I : INDEX_T V) (J : JOIN_T V I)
    (D : DATABASE_T V I) (Import X : RUN_T V I J D).
  Parameter apply : list (action V.t) -> Model.env (V := V.t) -> D.t -> D.t.
  Parameter query_vars : rule V.t -> list positive.
  Parameter T_apply : list (action V.t) -> Model.env (V := V.t) ->
    (positive -> N) -> D.t -> N.
  Parameter driver : program V.t -> compiled V.t -> limits ->
    (bool * D.t) -> (bool * D.t) + (stop * D.t).
  Parameter T_driver : program V.t -> compiled V.t -> limits -> (bool * D.t) -> N.
  Parameter k_driver : N.
  Definition agrees (s t : Model.env (V := V.t)) (xs : list positive) : Prop :=
    forall x, In x xs -> s x = t x.
  Definition extends (db : D.t) (M : model (V := V.t))
      (nu nu' : positive -> carrier M) : Prop :=
    forall i, D.allocated db i -> nu' i = nu i.
  Definition derived (p : program V.t) (initial current : D.t) : Prop :=
    forall f k o, row (D.view current) f k o -> derives V.prim p (D.view initial) f k.

  (** Every checked plan binding satisfies the source rule body. *)
  Parameter F1_plan_match_sound : forall p cp db c b r, plans_ok p cp -> D.wf db ->
    In c (all_plans cp) -> nth_error (rules V.t p) (N.to_nat (rule_ix V.t c)) = Some r ->
    In b (bindings cp c db) -> matches V.prim (D.view db) (query V.t r) (env_of c b).
  (** Naive plans enumerate every match on a canonical database. *)
  Parameter F2_naive_plans_complete : forall p cp db r s, plans_ok p cp -> D.wf db ->
    D.canonical db -> In r (rules V.t p) -> matches V.prim (D.view db) (query V.t r) s ->
    exists c b, In c (naive V.t cp) /\
      nth_error (rules V.t p) (N.to_nat (rule_ix V.t c)) = Some r /\
      In b (bindings cp c db) /\ agrees (env_of c b) s (query_vars r).
  (** Applying actions keeps the maintained database invariant. *)
  Parameter F3_apply_wf : forall acts s db, D.wf db -> D.wf (apply acts s db).
  (** A matched valid rule keeps satisfaction and the meanings of old identifiers. *)
  Parameter F4_apply_sat : forall (M : model (V := V.t)) nu p r s db,
    valid V.prim V.merge M p -> In r (rules V.t p) ->
    matches V.prim (D.view db) (query V.t r) s -> sat V.merge M nu (D.view db) ->
    exists nu', extends db M nu nu' /\ sat V.merge M nu' (D.view (apply (actions V.t r) s db)).
  (** A quiet action sequence is already present in the old view. *)
  Parameter F5_apply_quiet_present : forall acts s db, D.wf db -> D.changed db = false ->
    D.changed (apply acts s db) = false -> present V.prim V.merge (D.view db) s acts.
  (** Action application retains the old rows and equalities modulo canonicalization. *)
  Parameter F6_apply_grows : forall acts s db, D.wf db -> grows db (apply acts s db).
  (** Applying a relational rule retains derivability of every output row. *)
  Parameter F7_apply_derives : forall p initial db r s, relational_fragment p = true ->
    no_ids initial -> D.wf db -> derived p initial db -> In r (rules V.t p) ->
    derivation_body V.prim p (D.view initial) s (query V.t r) ->
    derived p initial (apply (actions V.t r) s db).
  (** A quiet naive round establishes closure of the current view. *)
  Parameter F8_naive_quiet_closed : forall p cp db, plans_ok p cp -> D.wf db ->
    D.canonical db -> D.changed db = false -> D.changed (round p cp true db) = false ->
    closed V.prim V.merge p (D.view db).
  (** A changed relational round adds a row absent from its starting view. *)
  Parameter F9_round_progress : forall p cp nv db, plans_ok p cp -> D.wf db ->
    relational_fragment p = true -> no_ids db -> D.changed db = false ->
    D.changed (round p cp nv db) = true ->
    exists f k, row (D.view (round p cp nv db)) f k None /\ ~ row (D.view db) f k None.
  (** A final rebuild establishes canonicality even when the caller supplies zero fuel. *)
  Parameter F10_run_loop : forall p cp lim db, plans_ok p cp -> D.wf db ->
    match loopN (driver p cp lim) (max_iter lim) (false, db) with
    | inl (_, db') => run p cp lim db = (IterLimit, D.rebuild db')
    | inr (st, db') => run p cp lim db = (st, D.rebuild db')
    end.
  (** Derivations are contained in every relational closed extension of their seed. *)
  Parameter F11_derives_least : forall p db w f k, relational_fragment p = true ->
    no_ids db -> closed V.prim V.merge p w -> includes (D.view db) w ->
    derives V.prim p (D.view db) f k -> row w f k None.
  (** Every relational round preserves the finite Herbrand bound. *)
  Parameter F12_herbrand_bound : forall p cp db nv, plans_ok p cp -> D.wf db ->
    relational_fragment p = true -> no_ids db ->
    herbrand p (round p cp nv db) <= herbrand p db.
  Parameter universe : program V.t -> D.t -> list (positive * list (cell V.t)).
  (** The Herbrand budget counts a duplicate-free finite universe of possible relation rows. *)
  Parameter F13_herbrand_size : forall p db,
    herbrand p db = length (universe p db) /\ NoDup (universe p db).
  (** Every traced relational round stays within the initial finite universe. *)
  Parameter F14_universe_rows : forall p cp lim db nv current f k o,
    plans_ok p cp -> D.wf db -> relational_fragment p = true -> no_ids db ->
    In (nv, current) (trace p cp lim db) -> row (D.view current) f k o ->
    In (f, k) (universe p db).

  (** Each round pays its action work and transfers the database potential. *)
  Parameter T1_round_le : forall B p cp nv db, plans_ok p cp -> D.wf db ->
    (T_round p cp nv db + D.potential B (round p cp nv db) <=
      c_run * N.of_nat (round_work p cp nv db + 1) * act_unit p B db +
      D.potential B db)%N.
  (** The traced driver aggregates rounds without increasing the public budget. *)
  Parameter T2_run_trace : forall p cp lim db, plans_ok p cp -> D.wf db ->
    let B := (max_ids lim + overshoot p)%N in
    (T_run p cp lim db <= c_run *
      (fold_right N.add 0 (map (fun start =>
        N.of_nat (round_work p cp (fst start) (snd start) + 1) *
          act_unit p B (snd start)) (trace p cp lim db)) +
        N.of_nat (N.size_nat (max_iter lim) + 1)) + D.potential B db)%N.
  (** The wrapper pays for its binary driver, final rebuild and result construction. *)
  Parameter T3_driver_wrapper : forall p cp lim db, plans_ok p cp -> D.wf db ->
    (T_run p cp lim db <=
      T_loopN (driver p cp lim) (T_driver p cp lim) (max_iter lim) (false, db) +
      match loopN (driver p cp lim) (max_iter lim) (false, db) with
      | inl (_, final) => D.T_rebuild final
      | inr (_, final) => D.T_rebuild final
      end + k_driver)%N.

  (* DatalogExact.v at 87192fe supplies the following statements for porting.
     stratum_post_solution_contains k lower :
       program_wf prog facts -> stratified prog st ->
       represents (fun p => Cost.value (lower p)) (model_below prog facts st k) ->
       forall s, post_solution relation_lattice (stratum_system prog facts st lower k) s ->
       forall f, derives prog facts st k (model_below prog facts st k) f ->
         member (snd f) (s (fst f)) = true.
     stratum_reached_derives k lower :
       program_wf prog facts -> stratified prog st ->
       represents (fun p => Cost.value (lower p)) (model_below prog facts st k) ->
       forall s, reached (penc prog) relation_lattice (stratum_system prog facts st lower k) s ->
         stratum_derived k s.
     stratum_least_is_derives k lower :
       program_wf prog facts -> stratified prog st ->
       represents (fun p => Cost.value (lower p)) (model_below prog facts st k) ->
       forall s, least_solution relation_lattice (stratum_system prog facts st lower k) s ->
       forall p ts, member ts (s p) = true <->
         derives prog facts st k (model_below prog facts st k) (p, ts).

     SIG-QUESTION: The public bare-potential bound needs an accounting bridge from
     DATABASE_TIME's unit-scaled credit. Monotonicity of units alone does not establish
     this bridge. T3_driver_wrapper charges the final rebuild and does not establish
     the unchanged public bound. *)
End RUN_PLAN.

Module Type RUN_ALL (V : VALUE_T) (I : INDEX_T V) (J : JOIN_T V I)
    (D : DATABASE_T V I) := RUN_T V I J D <+ RUN_PLAN V I J D.
