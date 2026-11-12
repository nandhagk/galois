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
