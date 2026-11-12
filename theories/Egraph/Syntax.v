(** * Flat equality-saturation syntax

    Patterns and expressions store nodes in post-order and name their roots by index.
    For example, a literal pattern has one [PLit] node and root zero.
    Builds on: Egglog syntax and Stdlib lists. *)

From Stdlib Require Import List PArith NArith.
From Galois.Egglog Require Import Syntax Model Sorts.

Inductive pnode (V : Type) : Type :=
  | PHole (h : positive)
  | PApp (f : positive) (args : list nat)
  | PLit (v : V).

Arguments PHole {V}.
Arguments PApp {V}.
Arguments PLit {V}.

Record fpat (V : Type) : Type := FPat {
  nodes : list (pnode V);
  root : nat
}.

(** A pattern whose root is a constructor node. *)
Definition app_rooted {V} (p : fpat V) : Prop :=
  exists f children, nth_error (nodes V p) (root V p) = Some (PApp f children).

Inductive enode (V : Type) : Type :=
  | EApp (f : positive) (args : list nat)
  | ELit (v : V).

Arguments EApp {V}.
Arguments ELit {V}.

Record fexpr (V : Type) : Type := FExpr {
  expr_nodes : list (enode V);
  expr_root : nat
}.

Record rewrite (V : Type) : Type := Rewrite {
  lhs : fpat V;
  rhs : fpat V;
  cond : list (atom V)
}.

(** An expression node unfolds when each child refers to an earlier node. *)
Inductive unfolds_expr {V : Type} (ns : list (enode V)) : nat -> @Model.expr V -> Prop :=
  | unfold_expr_lit i v :
      nth_error ns i = Some (ELit v) -> unfolds_expr ns i (Model.ELit v)
  | unfold_expr_app i f children args :
      nth_error ns i = Some (EApp f children) ->
      Forall (fun j => j < i) children ->
      Forall2 (unfolds_expr ns) children args ->
      unfolds_expr ns i (Model.EApp f args).

(** A pattern hole unfolds to the expression supplied by its substitution. *)
Inductive unfolds_pat {V : Type} (tau : positive -> option (@Model.expr V))
    (ns : list (pnode V)) : nat -> @Model.expr V -> Prop :=
  | unfold_pat_hole i h e :
      nth_error ns i = Some (PHole h) -> tau h = Some e -> unfolds_pat tau ns i e
  | unfold_pat_lit i v :
      nth_error ns i = Some (PLit v) -> unfolds_pat tau ns i (Model.ELit v)
  | unfold_pat_app i f children args :
      nth_error ns i = Some (PApp f children) ->
      Forall (fun j => j < i) children ->
      Forall2 (unfolds_pat tau ns) children args ->
      unfolds_pat tau ns i (Model.EApp f args).

(** A flat expression denotes the value of any expression that it unfolds to. *)
Definition denotes_expr {V} (merge : positive -> V -> V -> V)
    (M : model (V := V)) (e : fexpr V) (value : carrier M + V) : Prop :=
  exists t, unfolds_expr (expr_nodes V e) (expr_root V e) t /\
    denote M t = value.

(** A flat pattern denotes the value of any expression obtained from its holes. *)
Definition denotes_pat {V} (merge : positive -> V -> V -> V)
    (M : model (V := V)) (tau : positive -> option (@Model.expr V))
    (p : fpat V) (value : carrier M + V) : Prop :=
  exists t, unfolds_pat tau (nodes V p) (root V p) t /\
    denote M t = value.

(** A flat pattern takes a value when its holes take carrier values. *)
Inductive pat_value {V : Type} (M : model (V := V)) (s : positive -> option (carrier M + V))
    (ns : list (pnode V)) : nat -> carrier M + V -> Prop :=
  | pat_value_hole i h c :
      nth_error ns i = Some (PHole h) -> s h = Some c -> pat_value M s ns i c
  | pat_value_lit i v :
      nth_error ns i = Some (PLit v) -> pat_value M s ns i (inr v)
  | pat_value_app i f children cs :
      nth_error ns i = Some (PApp f children) ->
      Forall (fun j => j < i) children ->
      Forall2 (pat_value M s ns) children cs ->
      pat_value M s ns i (inl (con M f cs)).

(** The front end names the first item that fails its check. *)
Inductive reject : Type :=
  | BadRewrite (n : nat)
  | BadAnalysis (n : nat)
  | BadInput (n : nat).

(** A constructor node is a class, a literal is a value, and a hole has its context sort. *)
Definition pnode_sort {V} (g : ctx) (n : pnode V) : option sort :=
  match n with
  | PHole h => g h
  | PApp _ _ => Some SId
  | PLit _ => Some SVal
  end.

(** A node of a pattern has a sort. *)
Definition pat_sort {V} (g : ctx) (p : fpat V) (j : nat) (s : sort) : Prop :=
  exists n, nth_error (nodes V p) j = Some n /\ pnode_sort g n = Some s.

(** A pattern is well sorted when its root is its last node and a class, every other node is
    a child of a later node, and every constructor node is a declared constructor whose earlier
    children have its argument sorts. *)
Definition pat_ok {V} (sorts : positive -> option (list sort))
    (kinds : positive -> option output) (g : ctx) (p : fpat V) : Prop :=
  S (root V p) = length (nodes V p) /\ pat_sort g p (root V p) SId /\
  (forall j, j < root V p -> exists i f ch,
    j < i /\ nth_error (nodes V p) i = Some (PApp f ch) /\ In j ch) /\
  (forall i f ch, nth_error (nodes V p) i = Some (PApp f ch) ->
    kinds f = Some OId /\ exists ss, sorts f = Some ss /\
      Forall2 (fun j s => j < i /\ pat_sort g p j s) ch ss).

(** A rewrite is well sorted in the context [g] of its holes and condition variables when
    its left side is rooted at a constructor and gives each hole the sort of its position, its
    condition is a well-sorted query from there, and its right side is well sorted in [g]. *)
Definition rewrite_ok {V} (sorts : positive -> option (list sort))
    (kinds : positive -> option output) (rw : rewrite V) (g : ctx) : Prop :=
  exists g0, app_rooted (lhs V rw) /\ pat_ok sorts kinds g0 (lhs V rw) /\
    (forall h s, g0 h = Some s -> In (PHole h) (nodes V (lhs V rw))) /\
    query_ok sorts kinds g0 (cond V rw) g /\ pat_ok sorts kinds g (rhs V rw).

(** An input node is a class when it applies a constructor and a value when it is a literal. *)
Definition enode_sort {V} (n : enode V) : sort :=
  match n with
  | EApp _ _ => SId
  | ELit _ => SVal
  end.

(** An input is well sorted when its root applies a constructor and every constructor node
    has earlier children of its argument sorts. *)
Definition expr_sorted {V} (sorts : positive -> option (list sort))
    (kinds : positive -> option output) (e : fexpr V) : Prop :=
  (exists f ch, nth_error (expr_nodes V e) (expr_root V e) = Some (EApp f ch)) /\
  (forall i f ch, nth_error (expr_nodes V e) i = Some (EApp f ch) ->
    kinds f = Some OId /\ exists ss, sorts f = Some ss /\
      Forall2 (fun j s => j < i /\ exists n,
        nth_error (expr_nodes V e) j = Some n /\ enode_sort n = s) ch ss).

(** An analysis action writes a relation or a lattice function, or computes a value. *)
Definition analysis_action {V} (kinds : positive -> option output) (a : action V) : Prop :=
  match a with
  | Put f _ _ => kinds f = Some ORel \/ exists m, kinds f = Some (OLat m)
  | Let _ _ _ => True
  | _ => False
  end.

(** An analysis rule is a well-sorted rule that creates no class and joins no classes. *)
Definition analysis_ok {V} (sorts : positive -> option (list sort))
    (kinds : positive -> option output) (r : rule V) : Prop :=
  rule_ok sorts kinds r /\ Forall (analysis_action kinds) (actions V r).

(** The rewrites and the analysis rules are well sorted against the declarations. *)
Definition rules_ok {V} (ds : list decl) (rws : list (rewrite V)) (ans : list (rule V))
    : Prop :=
  Forall (fun rw => exists g, rewrite_ok (lookup_sorts ds) (lookup_kind ds) rw g) rws /\
  Forall (analysis_ok (lookup_sorts ds) (lookup_kind ds)) ans.

(** Every rule and every input is well sorted against the declarations. *)
Definition front_ok {V} (ds : list decl) (rws : list (rewrite V)) (ans : list (rule V))
    (es : list (fexpr V)) : Prop :=
  rules_ok ds rws ans /\ Forall (expr_sorted (lookup_sorts ds) (lookup_kind ds)) es.

(** A reported item fails its check. *)
Definition rejected {V} (ds : list decl) (rws : list (rewrite V)) (ans : list (rule V))
    (es : list (fexpr V)) (e : reject) : Prop :=
  match e with
  | BadRewrite n => exists rw, nth_error rws n = Some rw /\
      ~ exists g, rewrite_ok (lookup_sorts ds) (lookup_kind ds) rw g
  | BadAnalysis n => exists r, nth_error ans n = Some r /\
      ~ analysis_ok (lookup_sorts ds) (lookup_kind ds) r
  | BadInput n => exists x, nth_error es n = Some x /\
      ~ expr_sorted (lookup_sorts ds) (lookup_kind ds) x
  end.

(** A rewrite is valid in a model when, under every well-sorted assignment of its holes and
    condition variables that meets its condition, its two sides take the same class. *)
Definition valid_rw {V} (prim : positive -> list V -> option V) (M : model (V := V))
    (sorts : positive -> option (list sort)) (kinds : positive -> option output)
    (rw : rewrite V) : Prop :=
  forall g s x y, rewrite_ok sorts kinds rw g -> model_env_sorted M g s ->
    Forall (model_atom prim M kinds s) (cond V rw) ->
    pat_value M s (nodes V (lhs V rw)) (root V (lhs V rw)) (inl x) ->
    pat_value M s (nodes V (rhs V rw)) (root V (rhs V rw)) (inl y) -> x = y.

(** * Sizes *)

Definition pnode_size {V} (n : pnode V) : nat :=
  match n with
  | PHole h => Pos.size_nat h + 1
  | PApp f ch => Pos.size_nat f + fold_right (fun j m => j + 1 + m) 0 ch + 1
  | PLit _ => 1
  end.

Definition pat_size {V} (p : fpat V) : nat :=
  fold_right (fun n m => pnode_size n + m) (root V p + 1) (nodes V p).

Definition rewrite_size {V} (rw : rewrite V) : nat :=
  pat_size (lhs V rw) + pat_size (rhs V rw) +
  fold_right (fun a m => atom_bits a + m) 0 (cond V rw).

Definition enode_size {V} (n : enode V) : nat :=
  match n with
  | EApp f ch => Pos.size_nat f + fold_right (fun j m => j + 1 + m) 0 ch + 1
  | ELit _ => 1
  end.

Definition expr_size {V} (e : fexpr V) : nat :=
  fold_right (fun n m => enode_size n + m) (expr_root V e + 1) (expr_nodes V e).

(** The size of everything that the front end reads before it compiles. *)
Definition front_size {V} (ds : list decl) (rws : list (rewrite V)) (ans : list (rule V))
    (es : list (fexpr V)) : nat :=
  fold_right (fun d m => decl_bits d + m) 0 ds +
  fold_right (fun rw m => rewrite_size rw + m) 0 rws +
  fold_right (fun r m => rule_bits r + m) 0 ans +
  fold_right (fun x m => expr_size x + m) 0 es.

(** Adding a node costs the square of its width and one step per unit of each child index. *)
Definition enode_work {V} (n : enode V) : nat :=
  match n with
  | EApp _ ch => (length ch + 2) * (length ch + 2) + fold_right (fun j m => j + 1 + m) 0 ch
  | ELit _ => 1
  end.

Definition expr_work {V} (e : fexpr V) : nat :=
  fold_right (fun n m => enode_work n + m) (expr_root V e + 1) (expr_nodes V e).
