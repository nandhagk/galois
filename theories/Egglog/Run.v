(** * Placeholder rule application

    These operations provide the interfaces for planning and running engine rules.
    For example, the placeholder run returns the input database at the iteration limit.
    Builds on: RunSig. *)

From Stdlib Require Import List PArith NArith Relations.Relation_Operators.
From Argent Require Import Time Tactics Std.
From Galois.Base Require Import Loop.
From Galois.Egglog Require Import ValueSig IndexSig JoinSig DatabaseSig Syntax Model RunSig.

Import List.ListNotations.

Module RunCode (V : VALUE_OPS) (I : INDEX_OPS V) (J : JOIN_OPS V I)
    (D : DATABASE_OPS V I) <: RUN_OPS V I J D.
  (* STUB-CODE *)
  Definition plan (_ : program V.t) : compiled V.t := Compiled V.t [] [] [].
  (* STUB-CODE *)
  Definition check_plan (_ : program V.t) (_ : compiled V.t) : bool := false.
  (* STUB-CODE *)
  Definition load (_ : program V.t) (_ : compiled V.t) : D.t := D.init [] [].
  (* STUB-CODE *)
  Definition round (_ : program V.t) (_ : compiled V.t) (_ : bool) (db : D.t) : D.t := db.
  (* STUB-CODE *)
  Definition run (_ : program V.t) (_ : compiled V.t) (_ : limits) (db : D.t) : stop * D.t :=
    (IterLimit, db).
End RunCode.

Module Run (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I) <: RUN V I J D.
  Include RunCode V I J D.
  Include RUN_SPEC V I J D.
  Definition herbrand (_ : program V.t) (_ : D.t) : nat := 0.
  Lemma load_spec : forall p cp,
    load p cp = D.init (decls V.t p) (Syntax.slots V.t cp).
  Proof. Admitted.
  Lemma run_wf : forall p cp lim db, plans_ok p cp -> D.wf db ->
    D.wf (snd (run p cp lim db)) /\ D.canonical (snd (run p cp lim db)).
  Proof. Admitted.
  Lemma run_grows : forall p cp lim db, plans_ok p cp -> D.wf db ->
    grows db (snd (run p cp lim db)).
  Proof. Admitted.
  Lemma run_sat : forall p cp lim db (M : model (V := V.t)) nu,
    plans_ok p cp -> D.wf db -> valid V.prim V.merge M p ->
    sat V.merge M nu (D.view db) -> exists nu',
      (forall i, D.allocated db i -> nu' i = nu i) /\
      sat V.merge M nu' (D.view (snd (run p cp lim db))).
  Proof. Admitted.
  Lemma run_closed : forall p cp lim db db', plans_ok p cp -> D.wf db ->
    run p cp lim db = (Saturated, db') -> closed V.prim V.merge p (D.view db').
  Proof. Admitted.
  Lemma run_derives : forall p cp lim db f k o, plans_ok p cp -> D.wf db ->
    relational_fragment p = true -> no_ids db ->
    row (D.view (snd (run p cp lim db))) f k o -> derives V.prim p (D.view db) f k.
  Proof. Admitted.
  Lemma run_least : forall p cp lim db db', plans_ok p cp -> D.wf db ->
    relational_fragment p = true -> no_ids db -> run p cp lim db = (Saturated, db') ->
    forall w, closed V.prim V.merge p w -> includes (D.view db) w ->
      includes (D.view db') w.
  Proof. Admitted.
  Lemma run_terminates : forall p cp lim db, plans_ok p cp -> D.wf db ->
    relational_fragment p = true -> no_ids db ->
    N.to_nat (max_iter lim) >= 2 * herbrand p db + 2 ->
    fst (run p cp lim db) = Saturated.
  Proof. Admitted.
  Lemma run_limits : forall p cp lim db, fst (run p cp lim db) = IdLimit ->
    (D.ids (snd (run p cp lim db)) > max_ids lim)%N.
  Proof. Admitted.
End Run.

Module RunT (V : VALUE_T) (I : INDEX_T V) (J : JOIN_T V I) (D : DATABASE_T V I)
    <: RUN_ALL V I J D.
  Include Run V I J D.
  TimeFun plan.
  TimeFun check_plan.
  TimeFun load.
  TimeFun round.
  TimeFun run.
  Definition trace (_ : program V.t) (_ : compiled V.t) (_ : limits) (_ : D.t)
      : list (bool * D.t) := [].
  Definition round_work (_ : program V.t) (_ : compiled V.t) (_ : bool) (_ : D.t) : nat := 0.
  Definition act_unit (_ : program V.t) (_ : N) (_ : D.t) : N := 0%N.
  Definition overshoot (_ : program V.t) : N := 0%N.
  Definition size_program (_ : program V.t) : nat := 0.
  Definition size_compiled (_ : compiled V.t) : nat := 0.
  Definition wbits (_ : program V.t) : nat := 0.
  Definition c_run : N := 1. (* STUB *)
  Lemma T_run_le : forall p cp lim db, plans_ok p cp -> D.wf db ->
    let B := (max_ids lim + overshoot p)%N in
    (T_run p cp lim db <= c_run *
      (fold_right N.add 0 (map (fun start =>
        N.of_nat (round_work p cp (fst start) (snd start) + 1) *
          act_unit p B (snd start)) (trace p cp lim db)) +
        N.of_nat (N.size_nat (max_iter lim) + 1)) + D.potential B db)%N.
  Proof. Admitted. (* STUB *)
  Lemma T_check_plan_le : forall p cp,
    (T_check_plan p cp <= c_run * N.of_nat (size_program p + size_compiled cp + 1) *
      N.of_nat (wbits p + 1))%N.
  Proof. Admitted. (* STUB *)
  (* STUB-CODE *)
  Definition apply (_ : list (action V.t)) (_ : Model.env (V := V.t)) (db : D.t) : D.t := db.
  (* STUB-CODE *)
  Definition query_vars (_ : rule V.t) : list positive := [].
  (* STUB-CODE *)
  Definition driver (_ : program V.t) (_ : compiled V.t) (_ : limits) (s : bool * D.t)
      : (bool * D.t) + (stop * D.t) := inl s.
  TimeFun apply.
  TimeFun query_vars.
  TimeFun driver.
  Definition k_driver : N := 1. (* STUB *)
  Definition agrees (s t : Model.env (V := V.t)) (xs : list positive) : Prop :=
    forall x, In x xs -> s x = t x.
  Definition extends (db : D.t) (M : model (V := V.t))
      (nu nu' : positive -> carrier M) : Prop :=
    forall i, D.allocated db i -> nu' i = nu i.
  Definition derived (p : program V.t) (initial current : D.t) : Prop :=
    forall f k o, row (D.view current) f k o -> derives V.prim p (D.view initial) f k.

  Lemma F1_plan_match_sound : forall p cp db c b r, plans_ok p cp -> D.wf db ->
    In c (all_plans cp) -> nth_error (rules V.t p) (N.to_nat (rule_ix V.t c)) = Some r ->
    In b (bindings cp c db) -> matches V.prim (D.view db) (query V.t r) (env_of c b).
  Proof. Admitted. (* STUB *)
  Lemma F2_naive_plans_complete : forall p cp db r s, plans_ok p cp -> D.wf db ->
    D.canonical db -> In r (rules V.t p) -> matches V.prim (D.view db) (query V.t r) s ->
    exists c b, In c (naive V.t cp) /\
      nth_error (rules V.t p) (N.to_nat (rule_ix V.t c)) = Some r /\
      In b (bindings cp c db) /\ agrees (env_of c b) s (query_vars r).
  Proof. Admitted. (* STUB *)
  Lemma F3_apply_wf : forall acts s db, D.wf db -> D.wf (apply acts s db).
  Proof. Admitted. (* STUB *)
  Lemma F4_apply_sat : forall (M : model (V := V.t)) nu p r s db,
    valid V.prim V.merge M p -> In r (rules V.t p) ->
    matches V.prim (D.view db) (query V.t r) s -> sat V.merge M nu (D.view db) ->
    exists nu', extends db M nu nu' /\ sat V.merge M nu' (D.view (apply (actions V.t r) s db)).
  Proof. Admitted. (* STUB *)
  Lemma F5_apply_quiet_present : forall acts s db, D.wf db -> D.changed db = false ->
    D.changed (apply acts s db) = false -> present V.prim V.merge (D.view db) s acts.
  Proof. Admitted. (* STUB *)
  Lemma F6_apply_grows : forall acts s db, D.wf db -> grows db (apply acts s db).
  Proof. Admitted. (* STUB *)
  Lemma F7_apply_derives : forall p initial db r s, relational_fragment p = true ->
    no_ids initial -> D.wf db -> derived p initial db -> In r (rules V.t p) ->
    derivation_body V.prim p (D.view initial) s (query V.t r) ->
    derived p initial (apply (actions V.t r) s db).
  Proof. Admitted. (* STUB *)
  Lemma F8_naive_quiet_closed : forall p cp db, plans_ok p cp -> D.wf db ->
    D.canonical db -> D.changed db = false -> D.changed (round p cp true db) = false ->
    closed V.prim V.merge p (D.view db).
  Proof. Admitted. (* STUB *)
  Lemma F9_round_progress : forall p cp nv db, plans_ok p cp -> D.wf db ->
    relational_fragment p = true -> no_ids db -> D.changed db = false ->
    D.changed (round p cp nv db) = true ->
    exists f k, row (D.view (round p cp nv db)) f k None /\ ~ row (D.view db) f k None.
  Proof. Admitted. (* STUB *)
  Lemma F10_run_loop : forall p cp lim db, plans_ok p cp -> D.wf db ->
    match loopN (driver p cp lim) (max_iter lim) (false, db) with
    | inl (_, db') => run p cp lim db = (IterLimit, D.rebuild db')
    | inr (st, db') => run p cp lim db = (st, D.rebuild db')
    end.
  Proof. Admitted. (* STUB *)
  Lemma F11_derives_least : forall p db w f k, relational_fragment p = true ->
    no_ids db -> closed V.prim V.merge p w -> includes (D.view db) w ->
    derives V.prim p (D.view db) f k -> row w f k None.
  Proof. Admitted. (* STUB *)
  Lemma F12_herbrand_bound : forall p cp db nv, plans_ok p cp -> D.wf db ->
    relational_fragment p = true -> no_ids db ->
    herbrand p (round p cp nv db) <= herbrand p db.
  Proof. Admitted. (* STUB *)
  (* STUB-CODE *)
  Definition universe (_ : program V.t) (_ : D.t) : list (positive * list (cell V.t)) := [].
  TimeFun universe.
  Lemma F13_herbrand_size : forall p db,
    herbrand p db = length (universe p db) /\ NoDup (universe p db).
  Proof. Admitted. (* STUB *)
  Lemma F14_universe_rows : forall p cp lim db nv current f k o,
    plans_ok p cp -> D.wf db -> relational_fragment p = true -> no_ids db ->
    In (nv, current) (trace p cp lim db) -> row (D.view current) f k o ->
    In (f, k) (universe p db).
  Proof. Admitted. (* STUB *)

  Lemma T1_round_le : forall B p cp nv db, plans_ok p cp -> D.wf db ->
    (T_round p cp nv db + D.potential B (round p cp nv db) <=
      c_run * N.of_nat (round_work p cp nv db + 1) * act_unit p B db +
      D.potential B db)%N.
  Proof. Admitted. (* STUB *)
  Lemma T2_run_trace : forall p cp lim db, plans_ok p cp -> D.wf db ->
    let B := (max_ids lim + overshoot p)%N in
    (T_run p cp lim db <= c_run *
      (fold_right N.add 0 (map (fun start =>
        N.of_nat (round_work p cp (fst start) (snd start) + 1) *
          act_unit p B (snd start)) (trace p cp lim db)) +
        N.of_nat (N.size_nat (max_iter lim) + 1)) + D.potential B db)%N.
  Proof. Admitted. (* STUB *)
  Lemma T3_driver_wrapper : forall p cp lim db, plans_ok p cp -> D.wf db ->
    (T_run p cp lim db <=
      T_loopN (driver p cp lim) (T_driver p cp lim) (max_iter lim) (false, db) +
      match loopN (driver p cp lim) (max_iter lim) (false, db) with
      | inl (_, final) => D.T_rebuild final
      | inr (_, final) => D.T_rebuild final
      end + k_driver)%N.
  Proof. Admitted. (* STUB *)

End RunT.
