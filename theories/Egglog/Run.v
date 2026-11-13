(** * Placeholder rule application

    These operations provide the interfaces for planning and running engine rules.
    For example, the placeholder run returns the input database at the iteration limit.
    Builds on: RunSig. *)

From Stdlib Require Import List PArith NArith Bool Relations.Relation_Operators.
From Argent Require Import Time Tactics Std.
From Galois.Base Require Import Loop.
From Galois.Egglog Require Import ValueSig IndexSig JoinSig DatabaseSig Syntax Model Sorts RunSig.

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
  (* STUB-CODE *)
  Definition universe (_ : program V.t) (_ : D.t) : list (positive * list (cell V.t)) := [].
  Definition active_value (p : program V.t) (db : D.t) (v : V.t) : Prop :=
    In (Lit v) (program_terms p) \/
    exists s u, N.to_nat s < length (D.slots db) /\ I.mem (D.index s false db) u /\
      In (Val v) u.
  (* STUB-CODE *)
  Definition herbrand (_ : program V.t) (_ : D.t) : nat := 0.
  Lemma universe_spec : forall p db, D.wf db -> relational_fragment p = true ->
    prim_free p = true -> no_ids db ->
    NoDup (universe p db) /\
    forall f k, In (f, k) (universe p db) <->
      program_kind p f = Some ORel /\
      (exists d, find (fun d => Pos.eqb (name d) f) (decls V.t p) = Some d /\
        length k = length (arg_sorts d)) /\
      Forall (fun c => exists v, c = Val v /\ active_value p db v) k.
  Proof. Admitted. (* STUB *)

  Lemma herbrand_spec : forall p db, herbrand p db = length (universe p db).
  Proof. Admitted. (* STUB *)

  Lemma check_plan_scope : forall p cp r pre a rest x, plans_ok p cp ->
    In r (rules V.t p) -> actions V.t r = pre ++ a :: rest ->
    In x (flat_map term_vars (action_terms a)) ->
    In x (flat_map atom_vars (query V.t r) ++ flat_map action_binds pre).
  Proof. Admitted. (* STUB *)

  Lemma check_plan_arities : forall p cp r a, plans_ok p cp ->
    In r (rules V.t p) -> In a (actions V.t r) ->
    match a with
    | Make _ f args | Put f args _ =>
      exists d, find (fun d => Pos.eqb (name d) f) (decls V.t p) = Some d /\
        length args = length (arg_sorts d)
    | _ => True
    end.
  Proof. Admitted. (* STUB *)

  Lemma check_plan_slots : forall p cp f perm, plans_ok p cp ->
    In (f, perm) (Syntax.slots V.t cp) ->
    exists d, find (fun d => Pos.eqb (name d) f) (decls V.t p) = Some d /\
      NoDup perm /\ Forall (fun i => i <
        length (arg_sorts d) + match out d with ORel => 0 | _ => 1 end) perm.
  Proof. Admitted. (* STUB *)

  Lemma plans_ok_sorted : forall p cp, plans_ok p cp -> program_ok p.
  Proof. Admitted. (* STUB *)

  Lemma plan_checked : forall p, program_ok p -> plans_ok p (plan p).
  Proof. Admitted. (* STUB *)

  Lemma plan_full_slots : forall p f ss, program_kind p f = Some OId ->
    program_sorts p f = Some ss ->
    In (f, seq 0 (S (length ss))) (Syntax.slots V.t (plan p)).
  Proof. Admitted. (* STUB *)

  Lemma load_spec : forall p cp,
    load p cp = D.init (decls V.t p) (Syntax.slots V.t cp).
  Proof. Admitted. (* STUB *)

  Lemma run_wf : forall p cp lim db, plans_ok p cp -> D.wf db -> loaded p cp db ->
    D.wf (snd (run p cp lim db)) /\ D.canonical (snd (run p cp lim db)) /\
    loaded p cp (snd (run p cp lim db)).
  Proof. Admitted. (* STUB *)

  Lemma run_grows : forall p cp lim db, plans_ok p cp -> D.wf db -> loaded p cp db ->
    grows db (snd (run p cp lim db)).
  Proof. Admitted. (* STUB *)

  Lemma run_sat : forall p cp lim db (M : model (V := V.t)) nu,
    plans_ok p cp -> D.wf db -> loaded p cp db -> valid_sorted V.prim V.merge M p ->
    sat V.merge M nu (D.view db) -> exists nu',
      (forall i, D.allocated db i -> nu' i = nu i) /\
      sat V.merge M nu' (D.view (snd (run p cp lim db))).
  Proof. Admitted. (* STUB *)

  Lemma run_closed : forall p cp lim db db', plans_ok p cp -> D.wf db -> loaded p cp db ->
    run p cp lim db = (Saturated, db') -> closed V.prim V.merge p (D.view db').
  Proof. Admitted. (* STUB *)

  Lemma run_derives : forall p cp lim db f k o, plans_ok p cp -> D.wf db -> loaded p cp db ->
    relational_fragment p = true -> no_ids db ->
    row (D.view (snd (run p cp lim db))) f k o -> derives V.prim p (D.view db) f k.
  Proof. Admitted. (* STUB *)

  Lemma run_least : forall p cp lim db db', plans_ok p cp -> D.wf db -> loaded p cp db ->
    relational_fragment p = true -> no_ids db -> run p cp lim db = (Saturated, db') ->
    forall w, closed V.prim V.merge p w -> includes (D.view db) w ->
      includes (D.view db') w.
  Proof. Admitted. (* STUB *)

  Lemma run_terminates : forall p cp lim db, plans_ok p cp -> D.wf db ->
    loaded p cp db -> relational_fragment p = true -> prim_free p = true -> no_ids db ->
    N.to_nat (max_iter lim) >= 2 * herbrand p db + 2 ->
    fst (run p cp lim db) = Saturated.
  Proof. Admitted. (* STUB *)

  Lemma run_limits : forall p cp lim db, fst (run p cp lim db) = IdLimit ->
    (D.ids (snd (run p cp lim db)) > max_ids lim)%N.
  Proof. Admitted. (* STUB *)

End Run.

Module RunT (V : VALUE_T) (I : INDEX_T V) (J : JOIN_T V I) (D : DATABASE_T V I)
    <: RUN_ALL V I J D.
  Include Run V I J D.
  TimeFun plan.
  TimeFun check_plan.
  TimeFun load.
  TimeFun round.
  TimeFun run.
  (* STUB-CODE *)
  Definition driver (_ : program V.t) (_ : compiled V.t) (_ : limits) (s : bool * D.t)
      : (bool * D.t) + (stop * D.t) := inl s.
  Definition trace (p : program V.t) (cp : compiled V.t) (lim : limits) (db : D.t)
      : list (bool * D.t) :=
    driver_trace (driver p cp lim) (N.to_nat (max_iter lim)) (false, db).
  Definition round_work (p : program V.t) (cp : compiled V.t) (nv : bool) (db : D.t) : nat :=
    length (Syntax.slots V.t cp) +
      fold_right Nat.add 0 (map (fun c =>
        (J.work (join V.t c) (map (source_index db) (sources V.t c)) +
          length (sources V.t c) + 2) *
          (nvars (join V.t c) + 1) * (nvars (join V.t c) + 1) +
        length (bindings cp c db) *
          (length (post V.t c) + 1 +
           fold_right (fun a n => match a with
             | Make _ f args | Put f args _ => (length args + 2) * (length args + 2) *
                 (length (filter (fun sl => Pos.eqb (fst sl) f) (Syntax.slots V.t cp)) + 1) + n
             | Union _ _ => 1 + n
             | Let _ _ args => length args + 1 + n
             end) 0 (actions V.t (nth (N.to_nat (rule_ix V.t c)) (rules V.t p)
               (Rule V.t [] [])))) +
        fold_right Nat.add 0 (map (fun binding =>
          let r := nth (N.to_nat (rule_ix V.t c)) (rules V.t p) (Rule V.t [] []) in
          N.to_nat (query_prim_work V.prim_work (query V.t r) (env_of c binding) +
            action_prim_work V.prim V.prim_work (program_kind p) (actions V.t r)
              (env_of c binding))%N)
          (bindings cp c db)))
        (if nv then naive V.t cp else seminaive V.t cp)).
  Definition size_program (p : program V.t) : nat := program_bits p.
  Definition size_compiled (cp : compiled V.t) : nat :=
    fold_right (fun sl n => Pos.size_nat (fst sl) +
        fold_right (fun i m => i + 1 + m) 0 (snd sl) + 1 + n) 0 (Syntax.slots V.t cp) +
      fold_right (fun c n => N.size_nat (rule_ix V.t c) + nvars (join V.t c) +
        fold_right (fun col m => fold_right (fun i k => i + 1 + k) 0 col + 1 + m)
          0 (cols (join V.t c)) +
        fold_right (fun src m => match src with
          | All _ i | New _ i => N.size_nat i + 1 + m
          | Const _ value => cell_bits V.encode value + 1 + m
          end) 0 (sources V.t c) +
        fold_right (fun x m => Pos.size_nat x + 1 + m) 0 (var_of V.t c) +
        fold_right (fun i m => i + 1 + m) 0 (post V.t c) + 1 + n)
        0 (naive V.t cp ++ seminaive V.t cp).
  Definition wbits (p : program V.t) : nat :=
    fold_right (fun x n => Nat.max (Pos.size_nat x) n)
      0 (program_words V.encode p).
  Definition c_run : N := 1. (* STUB *)
  Lemma size_compiled_spec : forall cp,
    size_compiled cp =
      fold_right (fun sl n => Pos.size_nat (fst sl) +
        fold_right (fun i m => i + 1 + m) 0 (snd sl) + 1 + n) 0 (Syntax.slots V.t cp) +
      fold_right (fun c n => N.size_nat (rule_ix V.t c) + nvars (join V.t c) +
        fold_right (fun col m => fold_right (fun i k => i + 1 + k) 0 col + 1 + m)
          0 (cols (join V.t c)) +
        fold_right (fun src m => match src with
          | All _ i | New _ i => N.size_nat i + 1 + m
          | Const _ value => cell_bits V.encode value + 1 + m
          end) 0 (sources V.t c) +
        fold_right (fun x m => Pos.size_nat x + 1 + m) 0 (var_of V.t c) +
        fold_right (fun i m => i + 1 + m) 0 (post V.t c) + 1 + n)
        0 (naive V.t cp ++ seminaive V.t cp).
  Proof. Admitted. (* STUB *)

  Lemma wbits_spec : forall p,
    wbits p = fold_right (fun x n => Nat.max (Pos.size_nat x) n)
      0 (program_words V.encode p).
  Proof. Admitted. (* STUB *)

  Lemma T_plan_le : forall p,
    (T_plan p <= c_run * N.of_nat (size_program p + 1) * N.of_nat (size_program p + 1) *
      N.of_nat (size_program p + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma plan_slots_le : forall p,
    (N.of_nat (fold_right (fun s n =>
      (Pos.size_nat (fst s) + length (snd s) + 1 + n)%nat) 0%nat
      (Syntax.slots V.t (plan p))) <=
      c_run * N.of_nat (size_program p + 1) * N.of_nat (size_program p + 1) *
        N.of_nat (size_program p + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T_load_le : forall p cp,
    (T_load p cp <= D.T_init (decls V.t p) (Syntax.slots V.t cp) + c_run)%N.
  Proof. Admitted. (* STUB *)

  Lemma T_run_le : forall B U p cp lim db, plans_ok p cp -> D.wf db -> loaded p cp db ->
    (D.ids (snd (run p cp lim db)) <= B)%N -> D.unit (snd (run p cp lim db)) <= U ->
    (T_run p cp lim db <=
      c_run * N.of_nat U * N.of_nat ((N.to_nat (N.log2 B) + 1) * (wbits p + 1)) *
        (fold_right N.add 0 (map (fun start =>
          N.of_nat (round_work p cp (fst start) (snd start) + 1)) (trace p cp lim db)) +
         N.of_nat (D.pending db + 1)) +
      c_run * N.of_nat (N.size_nat (max_iter lim) + 1) +
      N.of_nat U * D.potential B db)%N.
  Proof. Admitted. (* STUB *)

  Lemma T_check_plan_le : forall p cp,
    (T_check_plan p cp <= c_run * N.of_nat (size_program p + size_compiled cp + 1) *
      N.of_nat (wbits p + 1))%N.
  Proof. Admitted. (* STUB *)

  (* STUB-CODE *)
  Definition apply (_ : list (action V.t)) (_ : Model.env (V := V.t)) (db : D.t) : D.t := db.
  Definition query_vars (r : rule V.t) : list positive := flat_map atom_vars (query V.t r).
  TimeFun apply.
  (* STUB-CODE *)
  Definition bind_env (_ : cplan V.t) (_ : list (cell V.t))
      : Model.env (V := V.t) := fun _ => None.
  TimeFun bind_env.
  (* STUB-CODE *)
  Definition jobs (_ : program V.t) (_ : compiled V.t) (_ : bool) (_ : D.t)
      : list (cplan V.t * list (cell V.t)) := [].
  Definition job_rule (p : program V.t) (c : cplan V.t) : rule V.t :=
    nth (N.to_nat (rule_ix V.t c)) (rules V.t p) (Rule V.t [] []).
  Fixpoint apply_jobs (p : program V.t) (js : list (cplan V.t * list (cell V.t)))
      (db : D.t) : D.t :=
    match js with
    | [] => db
    | (c, b) :: rest =>
        apply_jobs p rest (apply (actions V.t (job_rule p c)) (bind_env c b) db)
    end.
  Fixpoint T_apply_jobs (p : program V.t) (js : list (cplan V.t * list (cell V.t)))
      (db : D.t) : N :=
    match js with
    | [] => 0%N
    | (c, b) :: rest =>
        (T_apply (actions V.t (job_rule p c)) (bind_env c b) (T_bind_env c b) db +
          T_apply_jobs p rest (apply (actions V.t (job_rule p c)) (bind_env c b) db))%N
    end.

  TimeFun driver.
  Definition k_driver : N := 1. (* STUB *)
  Definition env_allocated (db : D.t) (s : Model.env (V := V.t)) : Prop :=
    forall x i, s x = Some (Id i) -> D.allocated db i.
  Definition agrees (s t : Model.env (V := V.t)) (xs : list positive) : Prop :=
    forall x, In x xs -> s x = t x.
  Definition extends (db : D.t) (M : model (V := V.t))
      (nu nu' : positive -> carrier M) : Prop :=
    forall i, D.allocated db i -> nu' i = nu i.
  Definition derived (p : program V.t) (initial current : D.t) : Prop :=
    forall f k o, row (D.view current) f k o -> derives V.prim p (D.view initial) f k.
  Definition grows_upto (db db' : D.t) : Prop :=
    (forall i j, same (D.view db) i j -> same (D.view db') i j) /\
    (forall f k o, row (D.view db) f k o -> exists k' o',
      row (D.view db') f k' o' /\ Forall2 (cell_rel (same (D.view db'))) k k' /\
      D.out_le db' f (option_map (D.canon db') o) o').
  (* STUB-CODE *)
  Definition check_shape (_ : program V.t) (_ : compiled V.t) : bool := false.
  TimeFun check_shape.
  Definition k_check : N := 1. (* STUB *)
  (** Two identifiers that occur in rows and are equal in the view are identical. *)
  Definition row_ids_unique (w : Model.view (V := V.t)) : Prop :=
    forall f k o f' k' o' i j, row w f k o -> row w f' k' o' ->
      In (Id i) (k ++ option_list o) -> In (Id j) (k' ++ option_list o') ->
      same w i j -> i = j.

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

  Lemma F3_apply_wf : forall p cp r s db, plans_ok p cp -> D.wf db -> loaded p cp db ->
    In r (rules V.t p) -> rule_env (program_sorts p) (program_kind p) r s ->
    env_allocated db s ->
    D.wf (apply (actions V.t r) s db) /\ loaded p cp (apply (actions V.t r) s db) /\
    (D.ids db <= D.ids (apply (actions V.t r) s db))%N /\
    D.unit db <= D.unit (apply (actions V.t r) s db).
  Proof. Admitted. (* STUB *)

  Lemma F4a_match_model : forall (M : model (V := V.t)) nu p cp db q s,
    D.wf db -> loaded p cp db -> sat V.merge M nu (D.view db) ->
    matches V.prim (D.view db) q s ->
    Forall (model_atom V.prim M (program_kind p) (fun x => option_map (den nu) (s x))) q.
  Proof. Admitted. (* STUB *)

  Lemma F4_apply_sat : forall (M : model (V := V.t)) nu p cp r s db,
    plans_ok p cp -> D.wf db -> loaded p cp db -> env_allocated db s ->
    rule_env (program_sorts p) (program_kind p) r s ->
    valid_sorted V.prim V.merge M p -> In r (rules V.t p) ->
    Forall (model_atom V.prim M (program_kind p) (fun x => option_map (den nu) (s x)))
      (query V.t r) ->
    sat V.merge M nu (D.view db) ->
    exists nu', extends db M nu nu' /\
      sat V.merge M nu' (D.view (apply (actions V.t r) s db)).
  Proof. Admitted. (* STUB *)

  Lemma F5_apply_quiet_present : forall p cp r s db, plans_ok p cp -> D.wf db ->
    loaded p cp db -> In r (rules V.t p) -> matches V.prim (D.view db) (query V.t r) s ->
    row_ids_unique (D.view db) ->
    D.changed db = false -> D.changed (apply (actions V.t r) s db) = false ->
    present V.prim V.merge (D.view db) s (actions V.t r).
  Proof. Admitted. (* STUB *)

  Lemma F6_apply_grows : forall p cp r s db, plans_ok p cp -> D.wf db ->
    loaded p cp db -> In r (rules V.t p) ->
    rule_env (program_sorts p) (program_kind p) r s -> env_allocated db s ->
    grows_upto db (apply (actions V.t r) s db).
  Proof. Admitted. (* STUB *)

  Lemma F6a_rebuild_grows : forall db0 db, D.wf db -> grows_upto db0 db ->
    grows db0 (D.rebuild db).
  Proof. Admitted. (* STUB *)

  Lemma F7_apply_derives : forall p initial db r s, relational_fragment p = true ->
    no_ids initial -> D.wf db -> derived p initial db -> In r (rules V.t p) ->
    derivation_body V.prim p (D.view initial) s (query V.t r) ->
    derived p initial (apply (actions V.t r) s db).
  Proof. Admitted. (* STUB *)

  Lemma F8_naive_quiet_closed : forall p cp db, plans_ok p cp -> D.wf db -> loaded p cp db ->
    D.canonical db -> D.changed db = false -> D.changed (round p cp true db) = false ->
    closed V.prim V.merge p (D.view db).
  Proof. Admitted. (* STUB *)

  Lemma F9_round_progress : forall p cp nv db, plans_ok p cp -> D.wf db -> loaded p cp db ->
    relational_fragment p = true -> no_ids db -> D.changed db = false ->
    D.changed (round p cp nv db) = true ->
    exists f k, row (D.view (round p cp nv db)) f k None /\ ~ row (D.view db) f k None.
  Proof. Admitted. (* STUB *)

  Lemma F10_run_loop : forall p cp lim db, plans_ok p cp -> D.wf db -> loaded p cp db ->
    match loopN (driver p cp lim) (max_iter lim) (false, db) with
    | inl (_, db') => run p cp lim db = (IterLimit, D.rebuild db')
    | inr (st, db') => run p cp lim db = (st, D.rebuild db')
    end.
  Proof. Admitted. (* STUB *)

  Lemma F11_derives_least : forall p db w f k, relational_fragment p = true ->
    no_ids db -> closed V.prim V.merge p w -> includes (D.view db) w ->
    derives V.prim p (D.view db) f k -> row w f k None.
  Proof. Admitted. (* STUB *)

  Lemma F12_herbrand_bound : forall p cp db nv, plans_ok p cp -> D.wf db -> loaded p cp db ->
    relational_fragment p = true -> prim_free p = true -> no_ids db ->
    herbrand p (round p cp nv db) <= herbrand p db.
  Proof. Admitted. (* STUB *)

  Lemma F13_herbrand_size : forall p db,
    relational_fragment p = true -> prim_free p = true ->
    herbrand p db = length (universe p db) /\ NoDup (universe p db).
  Proof. Admitted. (* STUB *)

  Lemma F14_universe_rows : forall p cp lim db nv current f k o,
    plans_ok p cp -> D.wf db -> loaded p cp db -> relational_fragment p = true ->
    prim_free p = true -> no_ids db ->
    In (nv, current) (trace p cp lim db) -> row (D.view current) f k o ->
    ~ row (D.view db) f k o ->
    In (f, k) (universe p db).
  Proof. Admitted. (* STUB *)

  Lemma F15_unit_scale : forall (T C P P' : N) (u U : nat), 1 <= u -> u <= U ->
    (T + N.of_nat u * P' <= N.of_nat u * (C + P))%N ->
    (T + N.of_nat U * P' <= N.of_nat U * (C + P))%N.
  Proof. Admitted. (* STUB *)

  Lemma F16_unit_pos : forall db, 1 <= D.unit db.
  Proof. Admitted. (* STUB *)

  Lemma F17_round_mono : forall p cp nv db, plans_ok p cp -> D.wf db -> loaded p cp db ->
    D.wf (round p cp nv db) /\ loaded p cp (round p cp nv db) /\
    (D.ids db <= D.ids (round p cp nv db))%N /\ D.unit db <= D.unit (round p cp nv db).
  Proof. Admitted. (* STUB *)

  Lemma F18_round_idle : forall p cp nv db, plans_ok p cp -> D.wf db -> loaded p cp db ->
    D.canonical (round p cp nv db) /\ D.pending (round p cp nv db) = 0.
  Proof. Admitted. (* STUB *)

  Lemma trace_spec : forall p cp lim db,
    trace p cp lim db =
      driver_trace (driver p cp lim) (N.to_nat (max_iter lim)) (false, db).
  Proof. Admitted. (* STUB *)

  Lemma F19_trace_chain : forall p cp lim db,
    hd_error (trace p cp lim db) = Some (false, db) /\
    length (trace p cp lim db) <= N.to_nat (max_iter lim) + 1 /\
    forall n s s', nth_error (trace p cp lim db) n = Some s ->
      nth_error (trace p cp lim db) (S n) = Some s' -> driver p cp lim s = inl s'.
  Proof. Admitted. (* STUB *)

  Lemma F20_round_work : forall p cp nv db,
    round_work p cp nv db =
      length (Syntax.slots V.t cp) +
      fold_right Nat.add 0 (map (fun c =>
        (J.work (join V.t c) (map (source_index db) (sources V.t c)) +
          length (sources V.t c) + 2) *
          (nvars (join V.t c) + 1) * (nvars (join V.t c) + 1) +
        length (bindings cp c db) *
          (length (post V.t c) + 1 +
           fold_right (fun a n => match a with
             | Make _ f args | Put f args _ =>
                 (length args + 2) * (length args + 2) *
                   (length (filter (fun sl => Pos.eqb (fst sl) f) (Syntax.slots V.t cp)) + 1)
                 + n
             | Union _ _ => 1 + n
             | Let _ _ args => length args + 1 + n
             end) 0 (actions V.t (nth (N.to_nat (rule_ix V.t c)) (rules V.t p)
               (Rule V.t [] [])))) +
        fold_right Nat.add 0 (map (fun binding =>
          let r := nth (N.to_nat (rule_ix V.t c)) (rules V.t p) (Rule V.t [] []) in
          N.to_nat (query_prim_work V.prim_work (query V.t r) (env_of c binding) +
            action_prim_work V.prim V.prim_work (program_kind p) (actions V.t r)
              (env_of c binding))%N)
          (bindings cp c db)))
        (if nv then naive V.t cp else seminaive V.t cp)).
  Proof. Admitted. (* STUB *)

  Lemma F21_put_sorted : forall sorts f k o db, D.wf db -> D.kind_ok db f k o ->
    view_sorted sorts (D.view db) -> row_sorted sorts (kind (D.view db)) f k o ->
    view_sorted sorts (D.view (D.put f k o db)).
  Proof. Admitted. (* STUB *)

  Lemma F22_make_sorted : forall sorts f k db, D.wf db -> kind (D.view db) f = Some OId ->
    sorts f = Some (map cell_sort k) -> view_sorted sorts (D.view db) ->
    view_sorted sorts (D.view (snd (D.make f k db))).
  Proof. Admitted. (* STUB *)

  Lemma F23_union_sorted : forall sorts i j db, D.wf db ->
    view_sorted sorts (D.view db) -> view_sorted sorts (D.view (D.union i j db)).
  Proof. Admitted. (* STUB *)

  Lemma F24_rebuild_sorted : forall sorts db, D.wf db ->
    view_sorted sorts (D.view db) -> view_sorted sorts (D.view (D.rebuild db)).
  Proof. Admitted. (* STUB *)

  Lemma F25_advance_sorted : forall sorts db, D.wf db ->
    view_sorted sorts (D.view db) -> view_sorted sorts (D.view (D.advance db)).
  Proof. Admitted. (* STUB *)

  Lemma F26_bindings_env : forall p cp db c b r, plans_ok p cp -> D.wf db ->
    loaded p cp db -> In c (all_plans cp) ->
    nth_error (rules V.t p) (N.to_nat (rule_ix V.t c)) = Some r -> In b (bindings cp c db) ->
    rule_env (program_sorts p) (program_kind p) r (env_of c b) /\ env_allocated db (env_of c b).
  Proof. Admitted. (* STUB *)

  Lemma F27_check_plan_split : forall p cp,
    check_plan p cp = check_program p && check_shape p cp.
  Proof. Admitted. (* STUB *)

  Lemma F28_plan_shape : forall p, program_ok p -> check_shape p (plan p) = true.
  Proof. Admitted. (* STUB *)

  Lemma F29_shape_slots : forall p cp f perm, plans_ok p cp ->
    In (f, perm) (Syntax.slots V.t cp) -> exists ss out,
      program_sorts p f = Some ss /\ program_kind p f = Some out /\
      NoDup perm /\ Forall (fun i => i < length ss +
        match out_sort out with
        | Some _ => 1
        | None => 0
        end) perm.
  Proof. Admitted. (* STUB *)

  Lemma T4_check_plan_split : forall p cp,
    (T_check_plan p cp <= T_check_program p + T_check_shape p cp + k_check)%N.
  Proof. Admitted. (* STUB *)

  Lemma T5_check_shape_le : forall p cp,
    (T_check_shape p cp <= k_check * N.of_nat (size_program p + size_compiled cp + 1) *
      N.of_nat (wbits p + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma F21_driver_step : forall p cp lim nv db,
    driver p cp lim (nv, db) =
      let next := round p cp nv db in
      if N.ltb (max_ids lim) (D.ids next) then inr (IdLimit, next)
      else if andb nv (negb (D.changed next)) then inr (Saturated, next)
      else inl (negb (D.changed next), D.advance next).
  Proof. Admitted. (* STUB *)

  Lemma F30_bind_env : forall c b x, bind_env c b x = env_of c b x.
  Proof. Admitted. (* STUB *)

  Lemma T6_bind_env_le : forall c b x,
    (T_bind_env c b x <= k_driver * N.of_nat (Pos.size_nat x + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma F31_jobs : forall p cp nv db c b, In (c, b) (jobs p cp nv db) ->
    In c (if nv then naive V.t cp else seminaive V.t cp) /\
    nth_error (rules V.t p) (N.to_nat (rule_ix V.t c)) = Some (job_rule p c) /\
    In b (bindings cp c db).
  Proof. Admitted. (* STUB *)

  Lemma F32_round_jobs : forall p cp nv db,
    round p cp nv db = D.rebuild (apply_jobs p (jobs p cp nv db) db).
  Proof. Admitted. (* STUB *)

  Lemma T1a_round_split : forall p cp nv db, plans_ok p cp -> D.wf db ->
    loaded p cp db ->
    (T_round p cp nv db <=
      fold_right N.add 0 (map (fun c =>
        J.T_run (join V.t c) (map (source_index db) (sources V.t c)))
        (if nv then naive V.t cp else seminaive V.t cp)) +
      T_apply_jobs p (jobs p cp nv db) db +
      D.T_rebuild (apply_jobs p (jobs p cp nv db) db) +
      k_driver * N.of_nat (round_work p cp nv db + 1) * N.of_nat (wbits p + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T1_round_le : forall B U p cp nv db, plans_ok p cp -> D.wf db -> loaded p cp db ->
    (D.ids (round p cp nv db) <= B)%N -> D.unit (round p cp nv db) <= U ->
    (T_round p cp nv db + N.of_nat U * D.potential B (round p cp nv db) <=
      c_run * N.of_nat U * N.of_nat ((N.to_nat (N.log2 B) + 1) * (wbits p + 1)) *
        N.of_nat (round_work p cp nv db + D.pending db + 1) +
      N.of_nat U * D.potential B db)%N.
  Proof. Admitted. (* STUB *)

  Lemma T3_driver_wrapper : forall p cp lim db, plans_ok p cp -> D.wf db -> loaded p cp db ->
    (T_run p cp lim db <=
      T_loopN (driver p cp lim) (T_driver p cp lim) (max_iter lim) (false, db) +
      match loopN (driver p cp lim) (max_iter lim) (false, db) with
      | inl (_, final) => D.T_rebuild final
      | inr (_, final) => D.T_rebuild final
      end + k_driver)%N.
  Proof. Admitted. (* STUB *)

  (** A driver call pays for its round, limit test, flag test and advance. *)
  Lemma T2a_driver_le : forall p cp lim nv db, plans_ok p cp -> D.wf db ->
    loaded p cp db ->
    (T_driver p cp lim (nv, db) <= T_round p cp nv db + k_driver *
      N.of_nat (length (Syntax.slots V.t cp) +
        N.size_nat (D.ids (round p cp nv db)) + 1))%N.
  Proof. Admitted. (* STUB *)
  (** The loop pays for every driver call in the trace prefix and its fuel. *)
  Lemma T2b_loop_trace : forall p cp lim db,
    (T_loopN (driver p cp lim) (T_driver p cp lim) (max_iter lim) (false, db) <=
      fold_right N.add 0 (map (fun st => T_driver p cp lim st + c_loopN)
        (firstn (N.to_nat (max_iter lim)) (trace p cp lim db))) +
      c_loopN * N.of_nat (N.size_nat (max_iter lim) + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Applying a rule pays for its actions, referenced bindings and transferred potential. *)
  Lemma T2c_apply_amort : forall B U p cp r s Ts db, plans_ok p cp -> D.wf db ->
    loaded p cp db -> In r (rules V.t p) ->
    rule_env (program_sorts p) (program_kind p) r s -> env_allocated db s ->
    (D.ids (apply (actions V.t r) s db) <= B)%N ->
    D.unit (apply (actions V.t r) s db) <= U ->
    (T_apply (actions V.t r) s Ts db +
      N.of_nat U * D.potential B (apply (actions V.t r) s db) <=
      c_run * N.of_nat U * N.of_nat ((N.to_nat (N.log2 B) + 1) * (wbits p + 1)) *
        N.of_nat ((fold_right (fun a n => match a with
          | Make _ f args | Put f args _ => ((length args + 2) * (length args + 2) *
              (length (filter (fun sl => Pos.eqb (fst sl) f) (Syntax.slots V.t cp)) + 1) + n)%nat
          | Union _ _ => (1 + n)%nat
          | Let _ _ args => (length args + 1 + n)%nat
          end) 0%nat (actions V.t r) + 1)%nat) +
      fold_right N.add 0 (map Ts (flat_map term_vars (flat_map action_terms (actions V.t r)))) +
      c_run * action_prim_work V.prim V.prim_work (program_kind p) (actions V.t r) s +
      N.of_nat U * D.potential B db)%N.
  Proof. Admitted. (* STUB *)
End RunT.
