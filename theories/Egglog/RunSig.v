(** * Rule application and checked saturation plans

    Runs use semi-naive rounds followed by a naive confirmation round.
    For example, a quiet confirmation round returns [Saturated] and establishes closure.
    Builds on: ValueSig, IndexSig, JoinSig, DatabaseSig and Model. *)

From Stdlib Require Import List PArith NArith Bool Relations.Relation_Operators.
From Argent Require Import Time Std.
From Galois.Base Require Import Loop Code.
From Galois.Egglog Require Import ValueSig IndexSig JoinSig DatabaseSig Syntax Model.

Import List.ListNotations.

Fixpoint binding_env {V} (vars : list positive) (cells : list (cell V))
    (x : positive) : option (cell V) :=
  match vars, cells with
  | v :: vs, c :: cs => if Pos.eqb x v then Some c else binding_env vs cs x
  | _, _ => None
  end.
TimeFun binding_env.

(** Rules compute no new values, so the active domain stays that of the seed and the program. *)
Definition prim_free {V} (p : program V) : bool :=
  forallb (fun r => match r with Rule _ q acts =>
    forallb (fun a => match a with
      | Prim _ _ _ _ => false
      | Fun _ _ _ _ => true
      end) q &&
    forallb (fun a => match a with
      | Let _ _ _ => false
      | _ => true
      end) acts end) (rules V p).
TimeFun prim_free.

(** Variables of a query, in order of occurrence. *)
Definition term_vars {V} (t : term V) : list positive :=
  match t with
  | Var x => [x]
  | Lit _ => []
  end.

TimeFun term_vars.

Definition atom_vars {V} (a : atom V) : list positive :=
  match a with
  | Fun _ _ args res => flat_map term_vars args ++ flat_map term_vars (option_list res)
  | Prim _ _ args res => flat_map term_vars args ++ term_vars res
  end.

TimeFun atom_vars.

(** Encoded words include every literal, variable and function name in the syntax. *)
Definition term_words {V} (encode : V -> positive) (t : term V) : list positive :=
  match t with
  | Var x => [x]
  | Lit v => [encode v]
  end.
TimeFun term_words.

Definition atom_words {V} (encode : V -> positive) (a : atom V) : list positive :=
  match a with
  | Fun _ f args res => f :: flat_map (term_words encode) (args ++ option_list res)
  | Prim _ f args res => f :: flat_map (term_words encode) (args ++ [res])
  end.
TimeFun atom_words.

Definition action_words {V} (encode : V -> positive) (a : action V) : list positive :=
  match a with
  | Make x f args | Let x f args => x :: f :: flat_map (term_words encode) args
  | Put f args res => f :: flat_map (term_words encode) (args ++ option_list res)
  | Union a b => term_words encode a ++ term_words encode b
  end.
TimeFun action_words.

Definition decl_words (d : decl) : list positive :=
  match d with
  | Decl f _ (OLat m) => [f; m]
  | Decl f _ _ => [f]
  end.
TimeFun decl_words.

Definition program_words {V} (encode : V -> positive) (p : program V) : list positive :=
  flat_map decl_words (decls V p) ++
  flat_map (fun r => match r with Rule _ q acts =>
    flat_map (atom_words encode) q ++ flat_map (action_words encode) acts end) (rules V p).
TimeFun program_words.

(** Primitive arguments must all resolve to values. *)
Fixpoint value_terms {V} (s : Model.env (V := V)) (ts : list (term V)) : option (list V) :=
  match ts with
  | [] => Some []
  | t :: rest =>
    let value := match t with Lit v => Some v | Var x =>
      match s x with Some (Val v) => Some v | _ => None end end in
    match value, value_terms s rest with
    | Some v, Some vs => Some (v :: vs)
    | _, _ => None
    end
  end.
TimeFun value_terms.

(** Let work uses the values available after each earlier binding action. *)
Fixpoint action_prim_work {V} (prim : positive -> list V -> option V)
    (work : positive -> list V -> N) (kinds : positive -> option output)
    (acts : list (action V))
    (s : Model.env (V := V)) : N :=
  match acts with
  | [] => 0%N
  | Make x f _ :: rest =>
    match kinds f with
    | Some OId => action_prim_work prim work kinds rest (update s x (Id 1))
    | _ => action_prim_work prim work kinds rest s
    end
  | Let x p args :: rest =>
    match value_terms s args with
    | None => 0%N
    | Some vs =>
      (work p vs + match prim p vs with
        | None => 0
        | Some v => action_prim_work prim work kinds rest (update s x (Val v))
        end)%N
    end
  | _ :: rest => action_prim_work prim work kinds rest s
  end.
TimeFun action_prim_work.

Definition query_prim_work {V} (work : positive -> list V -> N)
    (q : list (atom V)) (s : Model.env (V := V)) : N :=
  fold_right (fun a n => match a with
    | Fun _ _ _ _ => n
    | Prim _ p args _ =>
      match value_terms s args with None => n | Some vs => (work p vs + n)%N end
    end) 0%N q.
TimeFun query_prim_work.

(** Terms retain their order inside each atom or action. *)
Definition atom_terms {V} (a : atom V) : list (term V) :=
  match a with
  | Fun _ _ args res => args ++ option_list res
  | Prim _ _ args res => args ++ [res]
  end.
TimeFun atom_terms.

Definition action_terms {V} (a : action V) : list (term V) :=
  match a with
  | Make _ _ args | Let _ _ args => args
  | Put _ args res => args ++ option_list res
  | Union a b => [a; b]
  end.
TimeFun action_terms.

Definition action_binds {V} (a : action V) : list positive :=
  match a with
  | Make x _ _ | Let x _ _ => [x]
  | _ => []
  end.
TimeFun action_binds.

Definition program_terms {V} (p : program V) : list (term V) :=
  flat_map (fun r => match r with Rule _ q acts =>
    flat_map atom_terms q ++ flat_map action_terms acts end) (rules V p).
TimeFun program_terms.

(** The trace includes each continuing state and its final driver state. *)
Fixpoint driver_trace {S R} (step : S -> S + R) (fuel : nat) (state : S) : list S :=
  state :: match fuel with
    | O => []
    | S remaining => match step state with
      | inl next => driver_trace step remaining next
      | inr _ => []
      end
    end.
TimeFun driver_trace.

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
  (** A database carries the declarations and slot layout of a checked program. *)
  Definition loaded (p : program V.t) (cp : compiled V.t) (db : D.t) : Prop :=
    (forall f, kind (D.view db) f = program_kind p f) /\ D.slots db = Syntax.slots V.t cp.
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
  (* spec: herbrand universe *)
  Parameter universe : program V.t -> D.t -> list (positive * list (cell V.t)).
  Definition active_value (p : program V.t) (db : D.t) (v : V.t) : Prop :=
    In (Lit v) (program_terms p) \/
    exists f k o, row (D.view db) f k o /\ In (Val v) (k ++ option_list o).
  (** The finite universe contains exactly declared relational tuples over active values. *)
  Parameter universe_spec : forall p db, D.wf db -> relational_fragment p = true ->
    prim_free p = true -> no_ids db ->
    NoDup (universe p db) /\
    forall f k, In (f, k) (universe p db) <->
      program_kind p f = Some ORel /\
      (exists d, find (fun d => Pos.eqb (name d) f) (decls V.t p) = Some d /\
        length k = arity d) /\
      Forall (fun c => exists v, c = Val v /\ active_value p db v) k.
  (** The Herbrand budget counts the pinned finite universe. *)
  Parameter herbrand : program V.t -> D.t -> nat.
  Parameter herbrand_spec : forall p db, herbrand p db = length (universe p db).
  (** Checked actions read variables bound by the query or earlier binding actions. *)
  Parameter check_plan_scope : forall p cp r pre a rest x, plans_ok p cp ->
    In r (rules V.t p) -> actions V.t r = pre ++ a :: rest ->
    In x (flat_map term_vars (action_terms a)) ->
    In x (flat_map atom_vars (query V.t r) ++ flat_map action_binds pre).
  (** Checked constructor and put actions have their declared argument count. *)
  Parameter check_plan_arities : forall p cp r a, plans_ok p cp ->
    In r (rules V.t p) -> In a (actions V.t r) ->
    match a with
    | Make _ f args | Put f args _ =>
      exists d, find (fun d => Pos.eqb (name d) f) (decls V.t p) = Some d /\
        length args = arity d
    | _ => True
    end.
  (** Each checked slot selects distinct positions within its declared tuple. *)
  Parameter check_plan_slots : forall p cp f perm, plans_ok p cp ->
    In (f, perm) (Syntax.slots V.t cp) ->
    exists d, find (fun d => Pos.eqb (name d) f) (decls V.t p) = Some d /\
      NoDup perm /\ Forall (fun i => i <
        arity d + match out d with ORel => 0 | _ => 1 end) perm.
  (** Planning a relational program yields a plan that the checker accepts. *)
  Parameter plan_checked : forall p, relational_fragment p = true ->
    check_plan p (plan p) = true.
  (* SIG-QUESTION: malformed relational actions conflict with check_plan_scope and
     check_plan_arities. The universal planning law awaits the reviewer's ruling. *)
  (** Loading initializes precisely the declarations and compiled index slots. *)
  Parameter load_spec : forall p cp,
    load p cp = D.init (decls V.t p) (Syntax.slots V.t cp).
  (** Every checked run retains well-formedness and ends on canonical rows. *)
  Parameter run_wf : forall p cp lim db, plans_ok p cp -> D.wf db -> loaded p cp db ->
    D.wf (snd (run p cp lim db)) /\ D.canonical (snd (run p cp lim db)) /\
    loaded p cp (snd (run p cp lim db)).
  (** Every old equality and row persists modulo the final canonicalization. *)
  Parameter run_grows : forall p cp lim db, plans_ok p cp -> D.wf db -> loaded p cp db ->
    grows db (snd (run p cp lim db)).
  (** Running valid rules keeps every satisfying model and old allocated identifier meaning. *)
  Parameter run_sat : forall p cp lim db (M : model (V := V.t)) nu,
    plans_ok p cp -> D.wf db -> loaded p cp db -> valid V.prim V.merge M p ->
    sat V.merge M nu (D.view db) -> exists nu',
      (forall i, D.allocated db i -> nu' i = nu i) /\
      sat V.merge M nu' (D.view (snd (run p cp lim db))).
  (** Saturation establishes every rule's closure obligation. *)
  Parameter run_closed : forall p cp lim db db', plans_ok p cp -> D.wf db -> loaded p cp db ->
    run p cp lim db = (Saturated, db') -> closed V.prim V.merge p (D.view db').
  (** Relational runs insert only rows justified by finite rule derivations. *)
  Parameter run_derives : forall p cp lim db f k o, plans_ok p cp -> D.wf db -> loaded p cp db ->
    relational_fragment p = true -> no_ids db ->
    row (D.view (snd (run p cp lim db))) f k o -> derives V.prim p (D.view db) f k.
  (** A saturated relational result is included in every closed extension of its seed. *)
  Parameter run_least : forall p cp lim db db', plans_ok p cp -> D.wf db -> loaded p cp db ->
    relational_fragment p = true -> no_ids db -> run p cp lim db = (Saturated, db') ->
    forall w, closed V.prim V.merge p w -> includes (D.view db) w ->
      includes (D.view db') w.
  (** A relational run reaches saturation within its finite Herbrand budget. *)
  Parameter run_terminates : forall p cp lim db, plans_ok p cp -> D.wf db ->
    loaded p cp db -> relational_fragment p = true -> prim_free p = true -> no_ids db ->
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
  (* spec: trace round_work size_program size_compiled wbits *)
  Parameter trace : program V.t -> compiled V.t -> limits -> D.t -> list (bool * D.t).
  Parameter round_work : program V.t -> compiled V.t -> bool -> D.t -> nat.
  Parameter size_program : program V.t -> nat.
  Parameter size_compiled : compiled V.t -> nat.
  Parameter wbits : program V.t -> nat.
  (** Program size counts syntax words, declarations, rules, atoms, actions and arities. *)
  Parameter size_program_spec : forall p,
    size_program p = length (program_words V.encode p) + length (decls V.t p) +
      fold_right (fun d n => arity d + n) 0 (decls V.t p) +
      fold_right (fun r n => length (query V.t r) + length (actions V.t r) + 1 + n)
        0 (rules V.t p).
  (** Compiled size counts slots, permutation positions, joins, sources and post filters. *)
  Parameter size_compiled_spec : forall cp,
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
  (** Program width is the largest binary word width, with zero for empty syntax. *)
  Parameter wbits_spec : forall p,
    wbits p = fold_right (fun x n => Nat.max (Pos.size_nat x) n)
      0 (program_words V.encode p).
  Parameter T_plan : program V.t -> N.
  Parameter T_check_plan : program V.t -> compiled V.t -> N.
  Parameter T_load : program V.t -> compiled V.t -> N.
  Parameter T_round : program V.t -> compiled V.t -> bool -> D.t -> N.
  Parameter T_run : program V.t -> compiled V.t -> limits -> D.t -> N.
  Parameter c_run : N.
  (** Running pays for traced work, binary fuel overhead and scaled initial credit. *)
  Parameter T_run_le : forall B U p cp lim db, plans_ok p cp -> D.wf db -> loaded p cp db ->
    (D.ids (snd (run p cp lim db)) <= B)%N -> D.unit (snd (run p cp lim db)) <= U ->
    (T_run p cp lim db <=
      c_run * N.of_nat U * N.of_nat ((N.to_nat (N.log2 B) + 1) * (wbits p + 1)) *
        (fold_right N.add 0 (map (fun start =>
          N.of_nat (round_work p cp (fst start) (snd start) + 1)) (trace p cp lim db)) +
         N.of_nat (D.pending db + 1)) +
      c_run * N.of_nat (N.size_nat (max_iter lim) + 1) +
      N.of_nat U * D.potential B db)%N.
  (** Plan checking pays for program and plan syntax at their identifier width. *)
  Parameter T_check_plan_le : forall p cp,
    (T_check_plan p cp <= c_run * N.of_nat (size_program p + size_compiled cp + 1) *
      N.of_nat (wbits p + 1))%N.
End RUN_TIME.

Module Type RUN_T (V : VALUE_T) (I : INDEX_T V) (J : JOIN_T V I)
    (D : DATABASE_T V I) := RUN V I J D <+ RUN_TIME V I J D.

Module Type RUN_PLAN (V : VALUE_T) (I : INDEX_T V) (J : JOIN_T V I)
    (D : DATABASE_T V I) (Import X : RUN_T V I J D).
  Parameter apply : program V.t -> list (action V.t) -> Model.env (V := V.t) -> D.t -> D.t.
  Definition query_vars (r : rule V.t) : list positive := flat_map atom_vars (query V.t r).
  Parameter T_apply : program V.t -> list (action V.t) -> Model.env (V := V.t) ->
    (positive -> N) -> D.t -> N.
  Parameter driver : program V.t -> compiled V.t -> limits ->
    (bool * D.t) -> (bool * D.t) + (stop * D.t).
  Parameter T_driver : program V.t -> compiled V.t -> limits -> (bool * D.t) -> N.
  Parameter k_driver : N.
  (** Every identifier of the environment is allocated. *)
  Definition env_allocated (db : D.t) (s : Model.env (V := V.t)) : Prop :=
    forall x i, s x = Some (Id i) -> D.allocated db i.
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
  Parameter F3_apply_wf : forall p cp r s db, plans_ok p cp -> D.wf db -> loaded p cp db ->
    In r (rules V.t p) -> env_allocated db s ->
    D.wf (apply p (actions V.t r) s db) /\ loaded p cp (apply p (actions V.t r) s db) /\
    (D.ids db <= D.ids (apply p (actions V.t r) s db))%N.
  (** A database match gives a model match. *)
  Parameter F4a_match_model : forall (M : model (V := V.t)) nu p cp db q s,
    D.wf db -> loaded p cp db -> sat V.merge M nu (D.view db) ->
    matches V.prim (D.view db) q s ->
    Forall (model_atom V.prim M (program_kind p) (fun x => option_map (den nu) (s x))) q.
  (** A matched valid rule keeps satisfaction and the meanings of old identifiers. *)
  Parameter F4_apply_sat : forall (M : model (V := V.t)) nu p cp r s db,
    plans_ok p cp -> D.wf db -> loaded p cp db -> env_allocated db s ->
    valid V.prim V.merge M p -> In r (rules V.t p) ->
    Forall (model_atom V.prim M (program_kind p) (fun x => option_map (den nu) (s x)))
      (query V.t r) ->
    sat V.merge M nu (D.view db) ->
    exists nu', extends db M nu nu' /\
      sat V.merge M nu' (D.view (apply p (actions V.t r) s db)).
  (** A quiet action sequence is already present in the old view. *)
  Parameter F5_apply_quiet_present : forall p cp r s db, plans_ok p cp -> D.wf db ->
    loaded p cp db -> In r (rules V.t p) -> matches V.prim (D.view db) (query V.t r) s ->
    D.changed db = false -> D.changed (apply p (actions V.t r) s db) = false ->
    present V.prim V.merge (D.view db) s (actions V.t r).
  (** Rows and equalities persist up to the current identifier equality. *)
  Definition grows_upto (db db' : D.t) : Prop :=
    (forall i j, same (D.view db) i j -> same (D.view db') i j) /\
    (forall f k o, row (D.view db) f k o -> exists k' o',
      row (D.view db') f k' o' /\ Forall2 (cell_rel (same (D.view db'))) k k' /\
      D.out_le db' f (option_map (D.canon db') o) o').

  (** Action application retains old rows and equalities up to identifier equality. *)
  Parameter F6_apply_grows : forall p cp r s db, plans_ok p cp -> D.wf db ->
    loaded p cp db -> In r (rules V.t p) -> env_allocated db s ->
    grows_upto db (apply p (actions V.t r) s db).
  (** A rebuild turns growth up to equality into growth at canonical keys. *)
  Parameter F6a_rebuild_grows : forall db0 db, D.wf db -> grows_upto db0 db ->
    grows db0 (D.rebuild db).

  (** Applying a relational rule retains derivability of every output row. *)
  Parameter F7_apply_derives : forall p initial db r s, relational_fragment p = true ->
    no_ids initial -> D.wf db -> derived p initial db -> In r (rules V.t p) ->
    derivation_body V.prim p (D.view initial) s (query V.t r) ->
    derived p initial (apply p (actions V.t r) s db).
  (** A quiet naive round establishes closure of the current view. *)
  Parameter F8_naive_quiet_closed : forall p cp db, plans_ok p cp -> D.wf db -> loaded p cp db ->
    D.canonical db -> D.changed db = false -> D.changed (round p cp true db) = false ->
    closed V.prim V.merge p (D.view db).
  (** A changed relational round adds a row absent from its starting view. *)
  Parameter F9_round_progress : forall p cp nv db, plans_ok p cp -> D.wf db -> loaded p cp db ->
    relational_fragment p = true -> no_ids db -> D.changed db = false ->
    D.changed (round p cp nv db) = true ->
    exists f k, row (D.view (round p cp nv db)) f k None /\ ~ row (D.view db) f k None.
  (** A final rebuild establishes canonicality even when the caller supplies zero fuel. *)
  Parameter F10_run_loop : forall p cp lim db, plans_ok p cp -> D.wf db -> loaded p cp db ->
    match loopN (driver p cp lim) (max_iter lim) (false, db) with
    | inl (_, db') => run p cp lim db = (IterLimit, D.rebuild db')
    | inr (st, db') => run p cp lim db = (st, D.rebuild db')
    end.
  (** Derivations are contained in every relational closed extension of their seed. *)
  Parameter F11_derives_least : forall p db w f k, relational_fragment p = true ->
    no_ids db -> closed V.prim V.merge p w -> includes (D.view db) w ->
    derives V.prim p (D.view db) f k -> row w f k None.
  (** Every relational round preserves the finite Herbrand bound. *)
  Parameter F12_herbrand_bound : forall p cp db nv, plans_ok p cp -> D.wf db -> loaded p cp db ->
    relational_fragment p = true -> prim_free p = true -> no_ids db ->
    herbrand p (round p cp nv db) <= herbrand p db.
  (** The Herbrand budget counts a duplicate-free finite universe of possible relation rows. *)
  Parameter F13_herbrand_size : forall p db,
    relational_fragment p = true -> prim_free p = true ->
    herbrand p db = length (universe p db) /\ NoDup (universe p db).
  (** Every traced relational round stays within the initial finite universe. *)
  Parameter F14_universe_rows : forall p cp lim db nv current f k o,
    plans_ok p cp -> D.wf db -> loaded p cp db -> relational_fragment p = true ->
    prim_free p = true -> no_ids db ->
    In (nv, current) (trace p cp lim db) -> row (D.view current) f k o ->
    In (f, k) (universe p db).

  (** A fixed unit above the result's unit turns scaled database credit into credit at that unit. *)
  Parameter F15_unit_scale : forall (T C P P' : N) (u U : nat), 1 <= u -> u <= U ->
    (T + N.of_nat u * P' <= N.of_nat u * (C + P))%N ->
    (T + N.of_nat U * P' <= N.of_nat U * (C + P))%N.
  (** Every database unit is positive. *)
  Parameter F16_unit_pos : forall db, 1 <= D.unit db.
  (** A round keeps the layout and never lowers allocation or the unit. *)
  Parameter F17_round_mono : forall p cp nv db, plans_ok p cp -> D.wf db -> loaded p cp db ->
    D.wf (round p cp nv db) /\ loaded p cp (round p cp nv db) /\
    (D.ids db <= D.ids (round p cp nv db))%N /\ D.unit db <= D.unit (round p cp nv db).
  (** A round ends rebuilt. *)
  Parameter F18_round_idle : forall p cp nv db, plans_ok p cp -> D.wf db -> loaded p cp db ->
    D.canonical (round p cp nv db) /\ D.pending (round p cp nv db) = 0.

  (** The trace is precisely the finite driver path from the initial state. *)
  Parameter trace_spec : forall p cp lim db,
    trace p cp lim db =
      driver_trace (driver p cp lim) (N.to_nat (max_iter lim)) (false, db).
  (** The trace lists the state of every driver call, from the input on. *)
  Parameter F19_trace_chain : forall p cp lim db,
    hd_error (trace p cp lim db) = Some (false, db) /\
    length (trace p cp lim db) <= N.to_nat (max_iter lim) + 1 /\
    forall n s s', nth_error (trace p cp lim db) n = Some s ->
      nth_error (trace p cp lim db) (S n) = Some s' -> driver p cp lim s = inl s'.
  (** Round work counts join work, matches times action weight, and the slot layout. *)
  Parameter F20_round_work : forall p cp nv db,
    round_work p cp nv db =
      length (Syntax.slots V.t cp) +
      fold_right Nat.add 0 (map (fun c =>
        J.work (join V.t c) (map (source_index db) (sources V.t c)) +
        length (bindings cp c db) *
          (length (post V.t c) + 1 +
           fold_right (fun a n => match a with
             | Make _ _ args | Put _ args _ => (length args + 2) * (length args + 2) + n
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

  (** The driver reads the rebuilt flag before advancing to the next round. *)
  Parameter F21_driver_step : forall p cp lim nv db,
    driver p cp lim (nv, db) =
      let next := round p cp nv db in
      if N.ltb (max_ids lim) (D.ids next) then inr (IdLimit, next)
      else if andb nv (negb (D.changed next)) then inr (Saturated, next)
      else inl (negb (D.changed next), D.advance next).

  (** Each round pays its action work and transfers the database potential. *)
  Parameter T1_round_le : forall B U p cp nv db, plans_ok p cp -> D.wf db -> loaded p cp db ->
    (D.ids (round p cp nv db) <= B)%N -> D.unit (round p cp nv db) <= U ->
    (T_round p cp nv db + N.of_nat U * D.potential B (round p cp nv db) <=
      c_run * N.of_nat U * N.of_nat ((N.to_nat (N.log2 B) + 1) * (wbits p + 1)) *
        N.of_nat (round_work p cp nv db + D.pending db + 1) +
      N.of_nat U * D.potential B db)%N.

  (** The traced driver aggregates rounds without increasing the public budget. *)
  Parameter T2_run_trace : forall B U p cp lim db, plans_ok p cp -> D.wf db -> loaded p cp db ->
    (D.ids (snd (run p cp lim db)) <= B)%N -> D.unit (snd (run p cp lim db)) <= U ->
    (T_run p cp lim db <=
      c_run * N.of_nat U * N.of_nat ((N.to_nat (N.log2 B) + 1) * (wbits p + 1)) *
        (fold_right N.add 0 (map (fun start =>
          N.of_nat (round_work p cp (fst start) (snd start) + 1)) (trace p cp lim db)) +
         N.of_nat (D.pending db + 1)) +
      c_run * N.of_nat (N.size_nat (max_iter lim) + 1) +
      N.of_nat U * D.potential B db)%N.
  (** The wrapper pays for its binary driver, final rebuild and result construction. *)
  Parameter T3_driver_wrapper : forall p cp lim db, plans_ok p cp -> D.wf db -> loaded p cp db ->
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
         derives prog facts st k (model_below prog facts st k) (p, ts). *)
End RUN_PLAN.

Module Type RUN_ALL (V : VALUE_T) (I : INDEX_T V) (J : JOIN_T V I)
    (D : DATABASE_T V I) := RUN_T V I J D <+ RUN_PLAN V I J D.
