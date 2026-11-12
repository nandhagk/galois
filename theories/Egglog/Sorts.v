(** * Sorts of engine rules

    Rules are typed against the argument sorts and output kinds of their declarations, and a
    checker decides the typing in one pass over the rule text.
    For example, [mul(x, y) = z => Union z x] is well sorted when [mul] takes two classes,
    and [R(x, y) => Union x y] is rejected when [R] takes two values.
    Builds on: Syntax, Model, binary tries and Argent. *)

From Stdlib Require Import List PArith NArith Bool.
From Argent Require Import Time Std.
From Galois.Base Require Import Trie.
From Galois.Egglog Require Import Syntax Model.

Import List.ListNotations.

(** * Contexts and the judgment *)

(** A context gives some variables a sort. *)
Definition ctx := positive -> option sort.

Definition ctx_empty : ctx := fun _ => None.

Definition ctx_set (g : ctx) (x : positive) (s : sort) : ctx :=
  fun y => if Pos.eqb x y then Some s else g y.

(** A term has a sort when it is a variable of that sort or a literal at the value sort. *)
Definition has {V} (g : ctx) (t : term V) (s : sort) : Prop :=
  match t with
  | Var x => g x = Some s
  | Lit _ => s = SVal
  end.

(** A result term agrees with the output sort, and a relation has no result. *)
Definition has_result {V} (g : ctx) (out : output) (res : option (term V)) : Prop :=
  match out_sort out, res with
  | None, None => True
  | Some s, Some t => has g t s
  | _, _ => False
  end.

(** Binding a term at a position checks a bound variable and adds an unbound one. *)
Inductive binds {V : Type} (g : ctx) : term V -> sort -> ctx -> Prop :=
  | binds_old x s : g x = Some s -> binds g (Var x) s g
  | binds_new x s : g x = None -> binds g (Var x) s (ctx_set g x s)
  | binds_lit v : binds g (Lit v) SVal g.

Inductive binds_list {V : Type} : ctx -> list (term V) -> list sort -> ctx -> Prop :=
  | binds_nil g : binds_list g [] [] g
  | binds_cons g g1 g2 t ts s ss :
      binds g t s g1 -> binds_list g1 ts ss g2 -> binds_list g (t :: ts) (s :: ss) g2.

Definition binds_result {V} (g : ctx) (out : output) (res : option (term V))
    (g' : ctx) : Prop :=
  match out_sort out, res with
  | None, None => g' = g
  | Some s, Some t => binds g t s g'
  | _, _ => False
  end.

(** A query is well sorted when each function atom names a declared function with matching
    argument and result sorts, and each primitive atom reads values bound before it. *)
Inductive query_ok {V : Type} (sorts : positive -> option (list sort))
    (kinds : positive -> option output) : ctx -> list (atom V) -> ctx -> Prop :=
  | query_nil g : query_ok sorts kinds g [] g
  | query_fun g g1 g2 g3 f args res ss out rest :
      sorts f = Some ss -> kinds f = Some out -> binds_list g args ss g1 ->
      binds_result g1 out res g2 -> query_ok sorts kinds g2 rest g3 ->
      query_ok sorts kinds g (Fun V f args res :: rest) g3
  | query_prim g g1 p args res rest :
      Forall (fun t => has g t SVal) args -> has g res SVal ->
      query_ok sorts kinds g rest g1 ->
      query_ok sorts kinds g (Prim V p args res :: rest) g1.

(** Actions are well sorted when every argument has its declared sort, [Make] targets a
    constructor and binds a class, [Let] binds a value and [Union] joins two classes. *)
Fixpoint actions_ok {V} (sorts : positive -> option (list sort))
    (kinds : positive -> option output) (g : ctx) (acts : list (action V)) : Prop :=
  match acts with
  | [] => True
  | a :: rest =>
      match a with
      | Make x f args =>
          exists ss, sorts f = Some ss /\ kinds f = Some OId /\ Forall2 (has g) args ss /\
            actions_ok sorts kinds (ctx_set g x SId) rest
      | Put f args res =>
          exists ss out, sorts f = Some ss /\ kinds f = Some out /\
            Forall2 (has g) args ss /\ has_result g out res /\ actions_ok sorts kinds g rest
      | Union t u => has g t SId /\ has g u SId /\ actions_ok sorts kinds g rest
      | Let x _ args =>
          Forall (fun t => has g t SVal) args /\
            actions_ok sorts kinds (ctx_set g x SVal) rest
      end
  end.

(** A rule is well sorted when its query types its variables and its actions use them. *)
Definition rule_ok {V} (sorts : positive -> option (list sort))
    (kinds : positive -> option output) (r : rule V) : Prop :=
  exists g, query_ok sorts kinds ctx_empty (query V r) g /\
    actions_ok sorts kinds g (actions V r).

(** A program is well sorted when every rule is well sorted against its declarations. *)
Definition program_ok {V} (p : program V) : Prop :=
  Forall (rule_ok (program_sorts p) (program_kind p)) (rules V p).

(** * Sorted rows, environments and models *)

(** A row has the argument sorts of its function and the output sort of its kind. *)
Definition row_sorted {V} (sorts : positive -> option (list sort))
    (kinds : positive -> option output) (f : positive) (k : list (cell V))
    (o : option (cell V)) : Prop :=
  exists out, sorts f = Some (map cell_sort k) /\ kinds f = Some out /\
    option_map cell_sort o = out_sort out.

(** Every row of a view is well sorted. *)
Definition view_sorted {V} (sorts : positive -> option (list sort))
    (w : view (V := V)) : Prop :=
  forall f k o, row w f k o -> row_sorted sorts (kind w) f k o.

(** An environment binds every variable of a context to a cell of its sort. *)
Definition env_sorted {V} (g : ctx) (s : env (V := V)) : Prop :=
  forall x t, g x = Some t -> exists c, s x = Some c /\ cell_sort c = t.

(** An environment is well sorted for the variables that the query of a rule binds. *)
Definition rule_env {V} (sorts : positive -> option (list sort))
    (kinds : positive -> option output) (r : rule V) (s : env (V := V)) : Prop :=
  exists g, query_ok sorts kinds ctx_empty (query V r) g /\ env_sorted g s.

(** A model value is a class or a value. *)
Definition value_sort {C V : Type} (c : C + V) : sort :=
  match c with
  | inl _ => SId
  | inr _ => SVal
  end.

(** A model environment binds every variable of a context to a value of its sort. *)
Definition model_env_sorted {V} (M : model (V := V)) (g : ctx) (s : model_env M) : Prop :=
  forall x t, g x = Some t -> exists c, s x = Some c /\ value_sort c = t.

(** A rule is valid in a model when its actions hold in every well-sorted environment that
    satisfies its query. *)
Definition rule_valid_sorted {V} (prim : positive -> list V -> option V)
    (M : model (V := V)) (sorts : positive -> option (list sort))
    (kinds : positive -> option output) (r : rule V) : Prop :=
  forall g s, query_ok sorts kinds ctx_empty (query V r) g -> model_env_sorted M g s ->
    Forall (model_atom prim M kinds s) (query V r) ->
    model_actions prim M kinds s (actions V r).

(** A program is valid in a model on well-sorted environments, and its lattice functions are
    closed under their merges. *)
Definition valid_sorted {V} (prim : positive -> list V -> option V)
    (merge : positive -> V -> V -> V) (M : model (V := V)) (p : program V) : Prop :=
  Forall (rule_valid_sorted prim M (program_sorts p) (program_kind p)) (rules V p) /\
  (forall f m k a b, program_kind p f = Some (OLat m) ->
    lat M f k a -> lat M f k b -> lat M f k (merge m a b)).

(** * The checker *)

Definition sort_eqb (a b : sort) : bool :=
  match a, b with
  | SId, SId => true
  | SVal, SVal => true
  | _, _ => false
  end.
TimeFun sort_eqb.

Definition has_b {V} (g : ptrie sort) (t : term V) (s : sort) : bool :=
  match t with
  | Var x =>
      match trie_get x g with
      | Some s' => sort_eqb s' s
      | None => false
      end
  | Lit _ => sort_eqb s SVal
  end.
TimeFun has_b.

Fixpoint has_list_b {V} (g : ptrie sort) (ts : list (term V)) (ss : list sort) : bool :=
  match ts, ss with
  | [], [] => true
  | t :: ts', s :: ss' => has_b g t s && has_list_b g ts' ss'
  | _, _ => false
  end.
TimeFun has_list_b.

Fixpoint has_vals_b {V} (g : ptrie sort) (ts : list (term V)) : bool :=
  match ts with
  | [] => true
  | t :: rest => has_b g t SVal && has_vals_b g rest
  end.
TimeFun has_vals_b.

Definition has_result_b {V} (g : ptrie sort) (out : output) (res : option (term V)) : bool :=
  match out_sort out, res with
  | None, None => true
  | Some s, Some t => has_b g t s
  | _, _ => false
  end.
TimeFun has_result_b.

Definition bind_b {V} (g : ptrie sort) (t : term V) (s : sort) : option (ptrie sort) :=
  match t with
  | Var x =>
      match trie_get x g with
      | Some s' => if sort_eqb s' s then Some g else None
      | None => Some (PTrieCode.set x s g)
      end
  | Lit _ => if sort_eqb s SVal then Some g else None
  end.
TimeFun bind_b.

Fixpoint bind_list_b {V} (g : ptrie sort) (ts : list (term V)) (ss : list sort)
    : option (ptrie sort) :=
  match ts, ss with
  | [], [] => Some g
  | t :: ts', s :: ss' =>
      match bind_b g t s with
      | Some g1 => bind_list_b g1 ts' ss'
      | None => None
      end
  | _, _ => None
  end.
TimeFun bind_list_b.

Definition bind_result_b {V} (g : ptrie sort) (out : output) (res : option (term V))
    : option (ptrie sort) :=
  match out_sort out, res with
  | None, None => Some g
  | Some s, Some t => bind_b g t s
  | _, _ => None
  end.
TimeFun bind_result_b.

(** The first declaration of a name wins, as in [lookup_sorts] and [lookup_kind]. *)
Fixpoint decl_table (ds : list decl) : ptrie (list sort * output) :=
  match ds with
  | [] => Empty
  | d :: rest => PTrieCode.set (name d) (arg_sorts d, out d) (decl_table rest)
  end.
TimeFun decl_table.

Fixpoint bind_query_b {V} (tb : ptrie (list sort * output)) (g : ptrie sort)
    (q : list (atom V)) : option (ptrie sort) :=
  match q with
  | [] => Some g
  | a :: rest =>
      match a with
      | Fun _ f args res =>
          match trie_get f tb with
          | Some (ss, out) =>
              match bind_list_b g args ss with
              | Some g1 =>
                  match bind_result_b g1 out res with
                  | Some g2 => bind_query_b tb g2 rest
                  | None => None
                  end
              | None => None
              end
          | None => None
          end
      | Prim _ _ args res =>
          if has_vals_b g args && has_b g res SVal then bind_query_b tb g rest else None
      end
  end.
TimeFun bind_query_b.

Fixpoint check_actions_b {V} (tb : ptrie (list sort * output)) (g : ptrie sort)
    (acts : list (action V)) : bool :=
  match acts with
  | [] => true
  | a :: rest =>
      match a with
      | Make x f args =>
          match trie_get f tb with
          | Some (ss, OId) =>
              has_list_b g args ss && check_actions_b tb (PTrieCode.set x SId g) rest
          | _ => false
          end
      | Put f args res =>
          match trie_get f tb with
          | Some (ss, out) =>
              has_list_b g args ss && has_result_b g out res && check_actions_b tb g rest
          | None => false
          end
      | Union t u => has_b g t SId && has_b g u SId && check_actions_b tb g rest
      | Let x _ args => has_vals_b g args && check_actions_b tb (PTrieCode.set x SVal g) rest
      end
  end.
TimeFun check_actions_b.

Definition check_rule {V} (tb : ptrie (list sort * output)) (r : rule V) : bool :=
  match r with
  | Rule _ q acts =>
      match bind_query_b tb Empty q with
      | Some g => check_actions_b tb g acts
      | None => false
      end
  end.
TimeFun check_rule.

Fixpoint check_rules {V} (tb : ptrie (list sort * output)) (rs : list (rule V)) : bool :=
  match rs with
  | [] => true
  | r :: rest => check_rule tb r && check_rules tb rest
  end.
TimeFun check_rules.

Definition check_program {V} (p : program V) : bool :=
  check_rules (decl_table (decls V p)) (rules V p).
TimeFun check_program.

(** * Sizes *)

Definition term_bits {V} (t : term V) : nat :=
  match t with
  | Var x => Pos.size_nat x + 1
  | Lit _ => 1
  end.

Definition terms_bits {V} (ts : list (term V)) : nat :=
  fold_right (fun t n => term_bits t + n) 0 ts.

Definition result_bits {V} (res : option (term V)) : nat :=
  match res with
  | Some t => term_bits t
  | None => 0
  end.

Definition atom_bits {V} (a : atom V) : nat :=
  match a with
  | Fun _ f args res => Pos.size_nat f + terms_bits args + result_bits res + 1
  | Prim _ _ args res => terms_bits args + term_bits res + 1
  end.

Definition action_bits {V} (a : action V) : nat :=
  match a with
  | Make x f args => Pos.size_nat x + Pos.size_nat f + terms_bits args + 1
  | Put f args res => Pos.size_nat f + terms_bits args + result_bits res + 1
  | Union t u => term_bits t + term_bits u + 1
  | Let x _ args => Pos.size_nat x + terms_bits args + 1
  end.

Definition rule_bits {V} (r : rule V) : nat :=
  fold_right (fun a n => atom_bits a + n) 0 (query V r) +
  fold_right (fun a n => action_bits a + n) 0 (actions V r) + 1.

Definition decl_bits (d : decl) : nat := Pos.size_nat (name d) + length (arg_sorts d) + 1.

(** The bits of every name, variable and list cell of a program. *)
Definition program_bits {V} (p : program V) : nat :=
  fold_right (fun d n => decl_bits d + n) 0 (decls V p) +
  fold_right (fun r n => rule_bits r + n) 0 (rules V p) + 1.

(** * Lemmas *)

(** The checker decides well-sortedness. *)
Lemma check_program_spec : forall V (p : program V),
  check_program p = true <-> program_ok p.
Proof. Admitted. (* STUB *)

Definition c_sorts : N := 1. (* STUB *)

(** Checking pays for each bit of the program text once. *)
Lemma T_check_program_le : forall V (p : program V),
  (T_check_program p <= c_sorts * N.of_nat (program_bits p + 1))%N.
Proof. Admitted. (* STUB *)

(** A match of a well-sorted query binds every variable of its context to a cell of its sort. *)
Lemma matches_rule_env : forall V prim (w : view (V := V)) sorts kinds (r : rule V) g s,
  view_sorted sorts w -> (forall f, kind w f = kinds f) ->
  query_ok sorts kinds ctx_empty (query V r) g -> matches prim w (query V r) s ->
  env_sorted g s.
Proof. Admitted. (* STUB *)

(** Validity in every environment gives validity in well-sorted environments. *)
Lemma valid_sorted_of_valid : forall V prim merge (M : model (V := V)) (p : program V),
  valid prim merge M p -> valid_sorted prim merge M p.
Proof. Admitted. (* STUB *)
