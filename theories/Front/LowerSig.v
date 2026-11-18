(** * Lowering specifications to engine programs

    Each clause becomes one engine rule. Its premises become query atoms, and its head becomes
    actions that build each constructor term ([Make]) and each primitive value ([Let]) before
    the last action, which puts a row, puts a lattice value or joins two classes. A rewrite
    matches its left side in the query and joins it with its built right side. An equation
    premise [f x1 .. xn = y] defines [y] by a [Let] when no table atom binds [y], and every
    other primitive premise is a [Prim] check after the table atoms. Fresh variables follow the
    largest variable of the clause. The check [kinds_ok] says that every constructor pattern
    names an identifier table and every lattice premise or head names a lattice table. The
    check [rule_scoped] says that the actions of a rule read bound variables and bind each of
    their variables once, outside the query.

    For example, the clause [Holds copy [x; y], Holds points_to [y; a] => Derive points_to
    [x; a]] lowers to the rule with query [copy(x, y), points_to(y, a)] and the one action
    [Put points_to [x; a]].

    Main results
    - [query_pats_complete], [query_pats_sound] A query of patterns matches the values of the
      patterns, and only those.
    - [build_pats_present_sound], [build_pats_derivation] Present actions that build patterns
      compute their values, and a derivation passes through them.
    - [query_pats_meaning], [build_pats_model] Queries and actions of patterns agree with their
      meanings in a model.
    - [build_pats_represents] The cells that building patterns finds represent their terms.
    - [query_body_matches], [query_body_lets] The query of a body whose premises hold matches,
      and its present definitions compute the values of its equations.
    - [lower_complete], [lower_closed] A derived row is derived by the lowered program and
      present in every view that its rules close.
    - [lower_sound] A row that a well-sorted relational program derives is a derived row.
    - [lower_valid] A model of a well-sorted specification validates its lowered rules.

    Builds on: the specifications and their facts, and the syntax, models, sorts and rule
    syntax of the engine. *)

From Stdlib Require Import List PArith Bool.
From Galois.Egglog Require Import Syntax Model Sorts RunSig.
From Galois.Front Require Import Spec SpecFacts.

Import List.ListNotations.

Local Open Scope positive_scope.

Section Lower.
Context {V : Type}.

(** * Variables *)

(** The largest variable of a pattern, at least 1. *)
Fixpoint pat_top (p : pat V) : positive :=
  match p with
  | PVar x => x
  | PVal _ => 1
  | PNode _ args | POp _ args =>
      (fix tops (ps : list (pat V)) : positive :=
         match ps with
         | [] => 1
         | p :: rest => Pos.max (pat_top p) (tops rest)
         end) args
  end.

(** The largest variable of a list of patterns, at least 1. *)
Definition pats_top (ps : list (pat V)) : positive :=
  fold_right (fun p m => Pos.max (pat_top p) m) 1 ps.

(** The largest variable of a premise. *)
Definition premise_top (p : premise V) : positive :=
  match p with
  | Holds _ args => pats_top args
  | Equals _ args v | Computes _ args v => Pos.max (pats_top args) (pat_top v)
  end.

(** The largest variable of a head. *)
Definition head_top (h : consequence V) : positive :=
  match h with
  | Derive _ args => pats_top args
  | Assign _ args v => Pos.max (pats_top args) (pat_top v)
  | Unify l r | Rewrites l r => Pos.max (pat_top l) (pat_top r)
  end.

(** The first fresh variable of a clause. *)
Definition clause_fresh (c : clause V) : positive :=
  Pos.succ (fold_right (fun p m => Pos.max (premise_top p) m) (head_top (head c)) (body c)).

(** The largest variable of a body, at least 1. *)
Definition body_top (ps : list (premise V)) : positive :=
  fold_right (fun p m => Pos.max (premise_top p) m) 1 ps.

(** * Actions *)

(** The actions that build the subterms of a pattern, its engine term and the next fresh
    variable. *)
Fixpoint build_pat (next : positive) (p : pat V) : list (action V) * term V * positive :=
  match p with
  | PVar x => ([], Var x, next)
  | PVal v => ([], Lit v, next)
  | PNode f args =>
      let '(acts, ts, n) :=
        (fix go (next : positive) (ps : list (pat V)) :
            list (action V) * list (term V) * positive :=
           match ps with
           | [] => ([], [], next)
           | p :: rest =>
               let '(a1, t, n1) := build_pat next p in
               let '(a2, ts, n2) := go n1 rest in
               (a1 ++ a2, t :: ts, n2)
           end) next args in
      (acts ++ [Make n f ts], Var n, Pos.succ n)
  | POp q args =>
      let '(acts, ts, n) :=
        (fix go (next : positive) (ps : list (pat V)) :
            list (action V) * list (term V) * positive :=
           match ps with
           | [] => ([], [], next)
           | p :: rest =>
               let '(a1, t, n1) := build_pat next p in
               let '(a2, ts, n2) := go n1 rest in
               (a1 ++ a2, t :: ts, n2)
           end) next args in
      (acts ++ [Let n q ts], Var n, Pos.succ n)
  end.

(** [build_pat] over a list of patterns. *)
Fixpoint build_pats (next : positive) (ps : list (pat V)) :
    list (action V) * list (term V) * positive :=
  match ps with
  | [] => ([], [], next)
  | p :: rest =>
      let '(a1, t, n1) := build_pat next p in
      let '(a2, ts, n2) := build_pats n1 rest in
      (a1 ++ a2, t :: ts, n2)
  end.

(** * Queries *)

(** The atoms that bind the subterms of a pattern in a query, the engine term of the pattern
    and the next fresh variable. *)
Fixpoint query_pat (next : positive) (p : pat V) : list (atom V) * term V * positive :=
  match p with
  | PVar x => ([], Var x, next)
  | PVal v => ([], Lit v, next)
  | PNode f args =>
      let '(atoms, ts, n) :=
        (fix go (next : positive) (ps : list (pat V)) :
            list (atom V) * list (term V) * positive :=
           match ps with
           | [] => ([], [], next)
           | p :: rest =>
               let '(a1, t, n1) := query_pat next p in
               let '(a2, ts, n2) := go n1 rest in
               (a1 ++ a2, t :: ts, n2)
           end) next args in
      (atoms ++ [Fun V f ts (Some (Var n))], Var n, Pos.succ n)
  | POp q args =>
      let '(atoms, ts, n) :=
        (fix go (next : positive) (ps : list (pat V)) :
            list (atom V) * list (term V) * positive :=
           match ps with
           | [] => ([], [], next)
           | p :: rest =>
               let '(a1, t, n1) := query_pat next p in
               let '(a2, ts, n2) := go n1 rest in
               (a1 ++ a2, t :: ts, n2)
           end) next args in
      (atoms ++ [Prim V q ts (Var n)], Var n, Pos.succ n)
  end.

(** [query_pat] over a list of patterns. *)
Fixpoint query_pats (next : positive) (ps : list (pat V)) :
    list (atom V) * list (term V) * positive :=
  match ps with
  | [] => ([], [], next)
  | p :: rest =>
      let '(a1, t, n1) := query_pat next p in
      let '(a2, ts, n2) := query_pats n1 rest in
      (a1 ++ a2, t :: ts, n2)
  end.

(** The atoms of a premise and the next fresh variable. *)
Definition query_premise (next : positive) (p : premise V) : list (atom V) * positive :=
  match p with
  | Holds r args =>
      let '(a, ts, n) := query_pats next args in (a ++ [Fun V r ts None], n)
  | Equals f args v =>
      let '(a1, ts, n1) := query_pats next args in
      let '(a2, t, n2) := query_pat n1 v in
      (a1 ++ a2 ++ [Fun V f ts (Some t)], n2)
  | Computes q args v =>
      let '(a1, ts, n1) := query_pats next args in
      let '(a2, t, n2) := query_pat n1 v in
      (a1 ++ a2 ++ [Prim V q ts t], n2)
  end.


(** The variables that the table atoms of a pattern bind, outside primitive applications. *)
Fixpoint pat_bound (p : pat V) : list positive :=
  match p with
  | PVar x => [x]
  | PVal _ | POp _ _ => []
  | PNode _ args =>
      (fix go (ps : list (pat V)) : list positive :=
         match ps with
         | [] => []
         | p :: rest => pat_bound p ++ go rest
         end) args
  end.

(** The variables that the table atoms of a body bind. *)
Definition body_bound (ps : list (premise V)) : list positive :=
  flat_map (fun p =>
    match p with
    | Holds _ args => flat_map pat_bound args
    | Equals _ args v => flat_map pat_bound args ++ pat_bound v
    | Computes _ _ _ => []
    end) ps.

(** The query of a body, the actions that define the variables of its equations, and the next
    fresh variable. An equation [f x1 .. xn = y] defines [y] by a [Let] when [y] is not in
    [bound], and [y] is bound for the premises after it. Every other premise gives query
    atoms. *)
Fixpoint query_body (bound : list positive) (next : positive) (ps : list (premise V)) :
    list (atom V) * list (action V) * positive :=
  match ps with
  | [] => ([], [], next)
  | Computes q args (PVar y) :: rest =>
      if existsb (Pos.eqb y) bound then
        let '(a1, n1) := query_premise next (Computes q args (PVar y)) in
        let '(a2, acts, n2) := query_body bound n1 rest in
        (a1 ++ a2, acts, n2)
      else
        let '(a1, ts, n1) := build_pats next args in
        let '(a2, acts, n2) := query_body (y :: bound) n1 rest in
        (a2, a1 ++ Let y q ts :: acts, n2)
  | p :: rest =>
      let '(a1, n1) := query_premise next p in
      let '(a2, acts, n2) := query_body bound n1 rest in
      (a1 ++ a2, acts, n2)
  end.

(** * Rules *)

(** The table atoms of a query, then its [Prim] checks, which need the variables that the table
    atoms bind. *)
Definition checks_last (q : list (atom V)) : list (atom V) :=
  filter (fun a => match a with Fun _ _ _ _ => true | Prim _ _ _ _ => false end) q ++
  filter (fun a => match a with Fun _ _ _ _ => false | Prim _ _ _ _ => true end) q.

(** The engine rule of a clause. The query matches the premises and the left side of a
    rewrite. The actions define the values of the equations, build the terms of the head, and
    then put its row or lattice value or join its two sides. *)
Definition clause_rule (c : clause V) : rule V :=
  let left := match head c with Rewrites l _ => pat_bound l | _ => [] end in
  let '(q, lets, n1) := query_body (body_bound (body c) ++ left) (clause_fresh c) (body c) in
  match head c with
  | Derive r args =>
      let '(acts, ts, _) := build_pats n1 args in
      Rule V (checks_last q) (lets ++ acts ++ [Put r ts None])
  | Assign f args v =>
      let '(a1, ts, n2) := build_pats n1 args in
      let '(a2, t, _) := build_pat n2 v in
      Rule V (checks_last q) (lets ++ a1 ++ a2 ++ [Put f ts (Some t)])
  | Unify l r =>
      let '(a1, tl, n2) := build_pat n1 l in
      let '(a2, tr, _) := build_pat n2 r in
      Rule V (checks_last q) (lets ++ a1 ++ a2 ++ [Union tl tr])
  | Rewrites l r =>
      let '(lq, tl, n2) := query_pat n1 l in
      let '(acts, tr, _) := build_pat n2 r in
      Rule V (checks_last (q ++ lq)) (lets ++ acts ++ [Union tl tr])
  end.

(** * Programs *)

(** The engine rules of a specification, one for each clause in clause order. *)
Definition spec_rules (s : spec V) : list (rule V) := map clause_rule (clauses s).

(** The engine program of a specification. *)
Definition spec_program (s : spec V) : program V := Program V (tables s) (spec_rules s).

End Lower.

(** * Checks *)

Section Checks.
Context {V : Type}.

(** The variables of a pattern in order, also those inside primitive applications. *)
Fixpoint pat_vars (p : pat V) : list positive :=
  match p with
  | PVar x => [x]
  | PVal _ => []
  | PNode _ args | POp _ args =>
      (fix go (ps : list (pat V)) : list positive :=
         match ps with
         | [] => []
         | p :: rest => pat_vars p ++ go rest
         end) args
  end.

(** The variables of a premise. *)
Definition premise_vars (p : premise V) : list positive :=
  match p with
  | Holds _ args => flat_map pat_vars args
  | Equals _ args v | Computes _ args v => flat_map pat_vars args ++ pat_vars v
  end.

(** A pattern without constructor applications. *)
Fixpoint pat_free (p : pat V) : bool :=
  match p with
  | PVar _ | PVal _ => true
  | PNode _ _ => false
  | POp _ args =>
      (fix go (ps : list (pat V)) : bool :=
         match ps with
         | [] => true
         | p :: rest => pat_free p && go rest
         end) args
  end.

(** Every constructor application of a pattern names an identifier table of [ds]. *)
Fixpoint pat_kinds (ds : list decl) (p : pat V) : bool :=
  match p with
  | PVar _ | PVal _ => true
  | PNode f args =>
      match lookup_kind ds f with
      | Some OId => true
      | _ => false
      end &&
      (fix go (ps : list (pat V)) : bool :=
         match ps with
         | [] => true
         | p :: rest => pat_kinds ds p && go rest
         end) args
  | POp _ args =>
      (fix go (ps : list (pat V)) : bool :=
         match ps with
         | [] => true
         | p :: rest => pat_kinds ds p && go rest
         end) args
  end.

(** The terms of a list of patterns, when each has one. *)
Fixpoint pat_terms (prim : positive -> list V -> option V) (e : positive -> option (@expr V))
    (ps : list (pat V)) : option (list (@expr V)) :=
  match ps with
  | [] => Some []
  | p :: rest =>
      match pat_term prim e p, pat_terms prim e rest with
      | Some t, Some ts => Some (t :: ts)
      | _, _ => None
      end
  end.

End Checks.

(** A table of [ds] is a lattice table. *)
Definition lat_table (ds : list decl) (f : positive) : bool :=
  match lookup_kind ds f with
  | Some (OLat _) => true
  | _ => false
  end.

(** Every constructor application names an identifier table, and every lattice premise or head
    names a lattice table. The sort check of the lowered program cannot see this, because a
    constructor pattern and a lattice premise both become a function atom with an output. *)
Definition kinds_ok {V} (s : spec V) : bool :=
  let ok := pat_kinds (tables s) in
  forallb (fun c =>
    forallb (fun p =>
      match p with
      | Holds _ args => forallb ok args
      | Equals f args v => lat_table (tables s) f && forallb ok args && ok v
      | Computes _ args v => forallb ok args && ok v
      end) (body c) &&
    match head c with
    | Derive _ args => forallb ok args
    | Assign f args v => lat_table (tables s) f && forallb ok args && ok v
    | Unify l r | Rewrites l r => ok l && ok r
    end) (clauses s).

(** The values of an engine environment. *)
Definition val_env {V} (s : @env V) (x : positive) : option V :=
  match s x with
  | Some (Val v) => Some v
  | _ => None
  end.

(** Each action reads variables in [bound] or bound by an earlier action, and binds a variable
    that is neither. *)
Fixpoint actions_scoped {V} (bound : list positive) (acts : list (action V)) : bool :=
  match acts with
  | [] => true
  | a :: rest =>
      forallb (fun x => existsb (Pos.eqb x) bound) (flat_map term_vars (action_terms a)) &&
      forallb (fun x => negb (existsb (Pos.eqb x) bound)) (action_binds a) &&
      actions_scoped (action_binds a ++ bound) rest
  end.

(** The actions of a rule read the variables of its query or of earlier actions, and bind each
    of their variables once, outside the query. *)
Definition rule_scoped {V} (r : rule V) : bool :=
  actions_scoped (flat_map atom_vars (query V r)) (actions V r).

(** The rows of values without output of a view, as a relation. *)
Definition view_rows {V} (w : @view V) (r : positive) (vs : list V) : Prop :=
  row w r (map Val vs) None.

(** * Laws *)

(** The query of patterns agrees with the values of the patterns. *)
Module Type LOWER_QUERIES.
  (** A query of patterns reads their variables and fresh variables from [next] on. *)
  Parameter query_pats_fresh : forall {V} next (ps : list (pat V)),
    (next <= snd (query_pats next ps))%positive /\
    forall x, In x (flat_map atom_vars (fst (fst (query_pats next ps))) ++
        flat_map term_vars (snd (fst (query_pats next ps)))) ->
      In x (flat_map pat_vars ps) \/
      ((next <= x)%positive /\ (x < snd (query_pats next ps))%positive).
  (** The query of patterns with values matches when the fresh variables hold the values of
      the subpatterns, and its terms give the values. *)
  Parameter query_pats_complete : forall {V} (prim : positive -> list V -> option V)
      (w : @view V) next ps e vs (s : @env V),
    (pats_top ps < next)%positive -> pat_values prim e ps = Some vs ->
    (forall x v, e x = Some v -> s x = Some (Val v)) ->
    exists s', (forall x, (x < next)%positive \/ (snd (query_pats next ps) <= x)%positive ->
        s' x = s x) /\
      matches prim w (fst (fst (query_pats next ps))) s' /\
      terms_value s' (snd (fst (query_pats next ps))) (map Val vs).
  (** A matched query of patterns without constructors gives the values of the patterns. *)
  Parameter query_pats_sound : forall {V} (prim : positive -> list V -> option V)
      (w : @view V) next ps (s : @env V) vs,
    forallb pat_free ps = true ->
    matches prim w (fst (fst (query_pats next ps))) s ->
    terms_value s (snd (fst (query_pats next ps))) (map Val vs) ->
    pat_values prim (val_env s) ps = Some vs.
End LOWER_QUERIES.

(** The actions that build patterns agree with the values of the patterns. *)
Module Type LOWER_BUILDS.
  (** The actions that build patterns read their variables and fresh variables from [next] on,
      and bind distinct fresh variables. *)
  Parameter build_pats_fresh : forall {V} next (ps : list (pat V)),
    (next <= snd (build_pats next ps))%positive /\
    (forall x, In x (flat_map term_vars (flat_map action_terms (fst (fst (build_pats next ps)))) ++
        flat_map term_vars (snd (fst (build_pats next ps)))) ->
      In x (flat_map pat_vars ps) \/
      ((next <= x)%positive /\ (x < snd (build_pats next ps))%positive)) /\
    (forall x, In x (flat_map action_binds (fst (fst (build_pats next ps)))) ->
      (next <= x)%positive /\ (x < snd (build_pats next ps))%positive) /\
    NoDup (flat_map action_binds (fst (fst (build_pats next ps)))).
  (** Present actions that build patterns with values compute the values, and then the
      actions that follow are present. *)
  Parameter build_pats_present_sound : forall {V} (prim : positive -> list V -> option V)
      (merge : positive -> V -> V -> V) (w : @view V) next ps e vs (s : @env V) rest,
    (pats_top ps < next)%positive -> pat_values prim e ps = Some vs ->
    (forall x v, e x = Some v -> s x = Some (Val v)) ->
    present prim merge w s (fst (fst (build_pats next ps)) ++ rest) ->
    exists s', (forall x, (x < next)%positive \/ (snd (build_pats next ps) <= x)%positive ->
        s' x = s x) /\
      terms_value s' (snd (fst (build_pats next ps))) (map Val vs) /\
      present prim merge w s' rest.
  (** A derivation passes through the actions that build patterns with values. *)
  Parameter build_pats_derivation : forall {V} (prim : positive -> list V -> option V)
      next ps e vs (s : @env V) rest f k,
    (pats_top ps < next)%positive -> pat_values prim e ps = Some vs ->
    (forall x v, e x = Some v -> s x = Some (Val v)) ->
    (forall s', (forall x, (x < next)%positive \/ (snd (build_pats next ps) <= x)%positive ->
        s' x = s x) ->
      terms_value s' (snd (fst (build_pats next ps))) (map Val vs) ->
      derivation_action prim s' rest f k) ->
    derivation_action prim s (fst (fst (build_pats next ps)) ++ rest) f k.
  (** A derivation through the actions that build patterns computes the values of the
      patterns. *)
  Parameter build_pats_derivation_sound : forall {V} (prim : positive -> list V -> option V)
      next ps (s : @env V) rest f k,
    (pats_top ps < next)%positive ->
    (forall x, In x (flat_map pat_vars ps) -> exists v, s x = Some (Val v)) ->
    derivation_action prim s (fst (fst (build_pats next ps)) ++ rest) f k ->
    exists s' vs, (forall x, (x < next)%positive \/ (snd (build_pats next ps) <= x)%positive ->
        s' x = s x) /\
      terms_value s' (snd (fst (build_pats next ps))) (map Val vs) /\
      pat_values prim (val_env s') ps = Some vs /\ derivation_action prim s' rest f k.
End LOWER_BUILDS.

(** The query and the actions of patterns agree with the values of the patterns. *)
Module Type LOWER_VALUES := LOWER_QUERIES <+ LOWER_BUILDS.

(** The query and the actions of patterns agree with models and with represented terms. *)
Module Type LOWER_MODELS.
  (** The query atoms of patterns whose constructors are identifier tables hold in a model as
      the meanings of the patterns say. *)
  Parameter query_pats_meaning : forall {V} (prim : positive -> list V -> option V)
      (M : @model V) ds next ps (s : model_env M) xs,
    forallb (pat_kinds ds) ps = true ->
    Forall (model_atom prim M (lookup_kind ds) s) (fst (fst (query_pats next ps))) ->
    Forall2 (model_term M s) (snd (fst (query_pats next ps))) xs ->
    pat_meanings prim M s ps = Some xs.
  (** The actions that build patterns with meanings hold in a model, and then the actions that
      follow hold. *)
  Parameter build_pats_model : forall {V} (prim : positive -> list V -> option V)
      (M : @model V) ds next ps (s : model_env M) xs rest,
    (pats_top ps < next)%positive -> forallb (pat_kinds ds) ps = true ->
    pat_meanings prim M s ps = Some xs ->
    (forall s', (forall x, (x < next)%positive \/ (snd (build_pats next ps) <= x)%positive ->
        s' x = s x) ->
      Forall2 (model_term M s') (snd (fst (build_pats next ps))) xs ->
      model_actions prim M (lookup_kind ds) s' rest) ->
    model_actions prim M (lookup_kind ds) s (fst (fst (build_pats next ps)) ++ rest).
  (** In a view, the actions that build patterns find cells that represent the terms of the
      patterns, and then the actions that follow hold. *)
  Parameter build_pats_represents : forall {V} (prim : positive -> list V -> option V)
      (merge : positive -> V -> V -> V) (w : @view V) next ps e ts (s : @env V) rest,
    (pats_top ps < next)%positive -> (forall i, same w i i) ->
    pat_terms prim e ps = Some ts ->
    (forall x t, In x (flat_map pat_vars ps) -> e x = Some t ->
      exists c, s x = Some c /\ represents w c t) ->
    present prim merge w s (fst (fst (build_pats next ps)) ++ rest) ->
    exists s' cs, (forall x, (x < next)%positive \/ (snd (build_pats next ps) <= x)%positive ->
        s' x = s x) /\
      terms_value s' (snd (fst (build_pats next ps))) cs /\
      Forall2 (represents w) cs ts /\ present prim merge w s' rest.
End LOWER_MODELS.

(** The query and the definitions of a whole body agree with its premises. *)
Module Type LOWER_BODY.
  (** The query of a body whose premises hold in the value rows of a view matches, with fresh
      variables from [next] on. *)
  Parameter query_body_matches : forall {V} (prim : positive -> list V -> option V)
      (w : @view V) bound next ps e (s : @env V),
    (body_top ps < next)%positive -> Forall (premise_in prim (view_rows w) e) ps ->
    (forall x v, e x = Some v -> s x = Some (Val v)) ->
    exists s', (forall x, (x < next)%positive \/ (snd (query_body bound next ps) <= x)%positive ->
        s' x = s x) /\
      matches prim w (fst (fst (query_body bound next ps))) s'.
  (** The definitions of a body whose premises hold, when present, compute the values of the
      premises, and then the actions that follow are present. *)
  Parameter query_body_lets : forall {V} (prim : positive -> list V -> option V)
      (merge : positive -> V -> V -> V) (w : @view V) bound next ps e (s : @env V) rest,
    (body_top ps < next)%positive -> Forall (premise_in prim (view_rows w) e) ps ->
    (forall x v, e x = Some v -> s x = Some (Val v)) ->
    present prim merge w s (snd (fst (query_body bound next ps)) ++ rest) ->
    exists s', (forall x, (x < next)%positive \/ (snd (query_body bound next ps) <= x)%positive ->
        s' x = s x) /\ present prim merge w s' rest.
  (** The checks after the table atoms match exactly when the atoms match. *)
  Parameter checks_last_matches : forall {V} (prim : positive -> list V -> option V)
      (w : @view V) q (s : @env V),
    matches prim w (checks_last q) s <-> matches prim w q s.
End LOWER_BODY.

(** The lowered program derives the derived rows, and a view that its rules close holds them. *)
Module Type LOWER_COMPLETE.
  (** A derived row of a relational specification is derived by its lowered program. *)
  Parameter lower_complete : forall {V} (prim : positive -> list V -> option V) (s : spec V)
      (w0 : @view V) r vs,
    relational_fragment (spec_program s) = true ->
    derived prim s (view_rows w0) r vs -> derives prim (spec_program s) w0 r (map Val vs).
  (** A view that the rules of a well-sorted specification close, and whose relation rows have
      no output, holds every row derived from its own rows. *)
  Parameter lower_closed : forall {V} (prim : positive -> list V -> option V)
      (merge : positive -> V -> V -> V) (s : spec V) (w : @view V) r vs,
    check_program (spec_program s) = true -> closed prim merge (spec_program s) w ->
    (forall f k o, row w f k o -> lookup_kind (tables s) f = Some ORel -> o = None) ->
    derived prim s (view_rows w) r vs -> view_rows w r vs.
End LOWER_COMPLETE.

(** The rows that the lowered program derives are derived rows. *)
Module Type LOWER_SOUND.
  (** A row that a well-sorted relational program derives from value rows of input tables is a
      derived row of the specification. *)
  Parameter lower_sound : forall {V} (prim : positive -> list V -> option V) (s : spec V)
      (w0 : @view V) r k,
    check_program (spec_program s) = true -> relational_fragment (spec_program s) = true ->
    (forall r' k' o', row w0 r' k' o' ->
      In r' (inputs s) /\ o' = None /\ exists vs, k' = map Val vs) ->
    derives prim (spec_program s) w0 r k ->
    exists vs, k = map Val vs /\ derived prim s (view_rows w0) r vs.
End LOWER_SOUND.

(** The models of a specification validate its lowered rules. *)
Module Type LOWER_VALID.
  (** A model of a well-sorted specification that passes the kind check validates the rules of
      its lowered program on well-sorted environments. *)
  Parameter lower_valid : forall {V} (prim : positive -> list V -> option V)
      (merge : positive -> V -> V -> V) (s : spec V) I (M : @model V),
    check_program (spec_program s) = true -> kinds_ok s = true ->
    satisfies prim merge M s I -> valid_sorted prim merge M (spec_program s).
End LOWER_VALID.

Module Type LOWER_LAWS :=
  LOWER_VALUES <+ LOWER_MODELS <+ LOWER_BODY <+ LOWER_COMPLETE <+ LOWER_SOUND <+ LOWER_VALID.

(** * Proof plan *)

(** The kinds and the head variables of well-sorted specifications. *)
Module Type LOWER_KINDS_PLAN.
  (** A well-sorted relational program has no constructor pattern and no lattice premise or
      head, so it passes the kind check. *)
  Parameter relational_kinds_ok : forall {V} (s : spec V),
    check_program (spec_program s) = true -> relational_fragment (spec_program s) = true ->
    kinds_ok s = true.
  (** Every variable of the head of a clause of a well-sorted specification is bound by a table
      premise or by the left side of its rewrite, or is computed by an equation premise. *)
  Parameter head_vars_bound : forall {V} (s : spec V) c x,
    check_program (spec_program s) = true -> In c (clauses s) ->
    In x (match head c with
          | Derive _ args => flat_map pat_vars args
          | Assign _ args v => flat_map pat_vars args ++ pat_vars v
          | Unify l r | Rewrites l r => pat_vars l ++ pat_vars r
          end) ->
    In x (body_bound (body c)) \/
    In x (match head c with Rewrites l _ => pat_bound l | _ => [] end) \/
    exists q args, In (Computes q args (PVar x)) (body c).
End LOWER_KINDS_PLAN.

(** The well-sorted rules of a specification are scoped. *)
Module Type LOWER_SCOPES_PLAN.
  (** The rule of a clause of a well-sorted specification that passes the kind check is
      scoped. *)
  Parameter clause_rule_scoped : forall {V} (s : spec V) c,
    check_program (spec_program s) = true -> kinds_ok s = true -> In c (clauses s) ->
    rule_scoped (clause_rule c) = true.
End LOWER_SCOPES_PLAN.

(** The plan of the lowering laws. *)
Module Type LOWER_PLAN := LOWER_KINDS_PLAN <+ LOWER_SCOPES_PLAN.
