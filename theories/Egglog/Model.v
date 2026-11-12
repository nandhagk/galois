(** * Models of engine programs

    Views expose rows and identifier equality, and models interpret declared functions.
    For example, a relation row holds when its arguments belong to the model relation.
    Builds on: Syntax and Stdlib lists. *)

From Stdlib Require Import List PArith.
From Argent Require Import Time Std.
From Galois.Egglog Require Import Syntax.

Import List.ListNotations.

Section Model.
Context {V : Type} (prim : positive -> list V -> option V)
  (merge : positive -> V -> V -> V).

Record view : Type := View {
  row : positive -> list (cell V) -> option (cell V) -> Prop;
  same : positive -> positive -> Prop;
  kind : positive -> option output
}.

Record model : Type := Model {
  carrier : Type;
  rel : positive -> list (carrier + V) -> Prop;
  con : positive -> list (carrier + V) -> carrier;
  lat : positive -> list (carrier + V) -> V -> Prop;
  lat_merge : forall f m k a b, lat f k a -> lat f k b -> lat f k (merge m a b)
}.

Definition den {M : model} (nu : positive -> carrier M) (c : cell V) : carrier M + V :=
  match c with
  | Id i => inl (nu i)
  | Val v => inr v
  end.

Definition holds (M : model) (nu : positive -> carrier M) (w : view)
    (f : positive) (k : list (cell V)) (o : option (cell V)) : Prop :=
  match kind w f, o with
  | Some ORel, None => rel M f (map (den nu) k)
  | Some OId, Some (Id i) => con M f (map (den nu) k) = nu i
  | Some (OLat _), Some (Val v) => lat M f (map (den nu) k) v
  | _, _ => False
  end.

Definition sat (M : model) (nu : positive -> carrier M) (w : view) : Prop :=
  (forall f k o, row w f k o -> holds M nu w f k o) /\
  (forall i j, same w i j -> nu i = nu j).

Definition env := positive -> option (cell V).

Definition term_value (s : env) (t : term V) (c : cell V) : Prop :=
  match t with
  | Var x => s x = Some c
  | Lit v => c = Val v
  end.

Definition terms_value (s : env) (ts : list (term V)) (cs : list (cell V)) : Prop :=
  Forall2 (term_value s) ts cs.

Definition values (cs : list (cell V)) (vs : list V) : Prop :=
  Forall2 (fun c v => c = Val v) cs vs.

Definition atom_holds (w : view) (s : env) (a : atom V) : Prop :=
  match a with
  | Fun _ f args res =>
      exists k o, terms_value s args k /\
        (match res, o with
         | None, None => True
         | Some t, Some c => term_value s t c
         | _, _ => False
         end) /\ row w f k o
  | Prim _ p args res =>
      exists k vs v, terms_value s args k /\ values k vs /\
        prim p vs = Some v /\ term_value s res (Val v)
  end.

Definition matches (w : view) (q : list (atom V)) (s : env) : Prop :=
  Forall (atom_holds w s) q.

Definition update (s : env) (x : positive) (c : cell V) : env :=
  fun y => if Pos.eqb x y then Some c else s y.

Definition cell_le (w : view) (f : positive) (a b : cell V) : Prop :=
  match a, b with
  | Id i, Id j => same w i j
  | Val v, Val v' => exists m, kind w f = Some (OLat m) /\ merge m v v' = v'
  | _, _ => False
  end.

Fixpoint present (w : view) (s : env) (acts : list (action V)) : Prop :=
  match acts with
  | [] => True
  | a :: rest =>
      match a with
      | Make x f args =>
          exists k i, terms_value s args k /\ row w f k (Some (Id i)) /\
            present w (update s x (Id i)) rest
      | Put f args res =>
          exists k o, terms_value s args k /\ row w f k o /\
            (match res with
             | None => True
             | Some t => exists c d, term_value s t c /\ o = Some d /\ cell_le w f c d
             end) /\ present w s rest
      | Union a b =>
          exists c d, term_value s a c /\ term_value s b d /\
            (match c, d with
             | Id i, Id j => same w i j
             | Val v, Val v' => v = v'
             | _, _ => False
             end) /\ present w s rest
      | Let x p args =>
          exists k vs, terms_value s args k /\ values k vs /\
            match prim p vs with
            | None => True
            | Some v => present w (update s x (Val v)) rest
            end
      end
  end.

Definition closed (p : program V) (w : view) : Prop :=
  forall r s, In r (rules V p) -> matches w (query V r) s -> present w s (actions V r).

Definition model_env (M : model) := positive -> option (carrier M + V).

Definition model_term (M : model) (s : model_env M) (t : term V)
    (c : carrier M + V) : Prop :=
  match t with
  | Var x => s x = Some c
  | Lit v => c = inr v
  end.

Definition model_values (M : model) (cs : list (carrier M + V)) (vs : list V) : Prop :=
  Forall2 (fun c v => c = inr v) cs vs.

Definition model_atom (M : model) (kinds : positive -> option output)
    (s : model_env M) (a : atom V) : Prop :=
  match a with
  | Fun _ f args res =>
      exists k, Forall2 (model_term M s) args k /\
        match kinds f, res with
        | Some ORel, None => rel M f k
        | Some OId, Some t => model_term M s t (inl (con M f k))
        | Some (OLat _), Some t => exists v, model_term M s t (inr v) /\ lat M f k v
        | _, _ => False
        end
  | Prim _ p args res =>
      exists k vs v, Forall2 (model_term M s) args k /\ model_values M k vs /\
        prim p vs = Some v /\ model_term M s res (inr v)
  end.

Definition model_update (M : model) (s : model_env M) (x : positive)
    (c : carrier M + V) : model_env M :=
  fun y => if Pos.eqb x y then Some c else s y.

Fixpoint model_actions (M : model) (kinds : positive -> option output)
    (s : model_env M) (acts : list (action V)) : Prop :=
  match acts with
  | [] => True
  | a :: rest =>
      match a with
      | Make x f args =>
          exists k, Forall2 (model_term M s) args k /\ kinds f = Some OId /\
            model_actions M kinds (model_update M s x (inl (con M f k))) rest
      | Put f args res =>
          exists k, Forall2 (model_term M s) args k /\
            (match kinds f, res with
             | Some ORel, None => rel M f k
             | Some OId, Some t => model_term M s t (inl (con M f k))
             | Some (OLat _), Some t => exists v, model_term M s t (inr v) /\ lat M f k v
             | _, _ => False
             end) /\ model_actions M kinds s rest
      | Union a b =>
          exists c, model_term M s a c /\ model_term M s b c /\
            model_actions M kinds s rest
      | Let x p args =>
          exists k vs, Forall2 (model_term M s) args k /\ model_values M k vs /\
            match prim p vs with
            | None => True
            | Some v => model_actions M kinds (model_update M s x (inr v)) rest
            end
      end
  end.

Fixpoint lookup_kind (ds : list decl) (f : positive) : option output :=
  match ds with
  | [] => None
  | d :: rest => if Pos.eqb (name d) f then Some (out d) else lookup_kind rest f
  end.

Definition program_kind (p : program V) (f : positive) : option output :=
  lookup_kind (decls V p) f.

Definition valid (M : model) (p : program V) : Prop :=
  forall r s, In r (rules V p) ->
    Forall (model_atom M (program_kind p) s) (query V r) ->
    model_actions M (program_kind p) s (actions V r).

Inductive derivation_action : env -> list (action V) -> positive -> list (cell V) -> Prop :=
  | derive_put s f args k rest : terms_value s args k ->
      derivation_action s (Put f args None :: rest) f k
  | derive_put_later s f args input rest g k : terms_value s args input ->
      derivation_action s rest g k -> derivation_action s (Put f args None :: rest) g k
  | derive_let s x q args k vs v rest f out : terms_value s args k -> values k vs ->
      prim q vs = Some v -> derivation_action (update s x (Val v)) rest f out ->
      derivation_action s (Let x q args :: rest) f out.

Inductive derives (p : program V) (w0 : view) : positive -> list (cell V) -> Prop :=
  | derive_fact f k : row w0 f k None -> derives p w0 f k
  | derive_rule r s f k : In r (rules V p) ->
      derivation_body p w0 s (query V r) ->
      derivation_action s (actions V r) f k -> derives p w0 f k
with derivation_body (p : program V) (w0 : view) : env -> list (atom V) -> Prop :=
  | derive_body_nil s : derivation_body p w0 s []
  | derive_body_fun s f args k rest : terms_value s args k -> derives p w0 f k ->
      derivation_body p w0 s rest -> derivation_body p w0 s (Fun V f args None :: rest)
  | derive_body_prim s q args res k vs v rest : terms_value s args k -> values k vs ->
      prim q vs = Some v -> term_value s res (Val v) -> derivation_body p w0 s rest ->
      derivation_body p w0 s (Prim V q args res :: rest).

Scheme All for list.

Inductive expr : Type :=
  | EApp (f : positive) (args : list expr)
  | ELit (v : V).

Scheme All for Forall2.

Fixpoint denote (M : model) (e : expr) : carrier M + V :=
  match e with
  | ELit v => inr v
  | EApp f args => inl (con M f (map (denote M) args))
  end.

Inductive represents (w : view) : cell V -> expr -> Prop :=
  | rep_lit v : represents w (Val v) (ELit v)
  | rep_app f k i j args : row w f k (Some (Id j)) -> same w i j ->
      Forall2 (represents w) k args -> represents w (Id i) (EApp f args).

End Model.

TimeFun den.
TimeFun update.
TimeFun model_update.
TimeFun lookup_kind.
TimeFun program_kind.
