(** * Integer environment budgets

    Integer budgets connect bounded interval values and scoped instructions to system rows.
    For example, havoc writes only a variable listed by the program.
    Builds on: CutIntervalSig, EnvSig and SystemSig. *)

From Stdlib Require Import List ZArith.
From Galois.Base Require Import KeySig MapSig.
From Galois.Domains Require Import LangSig ValueSig IntervalSig ThresholdsSig CutIntervalSig.
From Galois.States Require Import EnvSig.
From Galois.Fixpoint Require Import SystemSig.

Local Open Scope nat_scope.

Inductive int_instruction (X O G : Type) :=
  | IAssign (x : X) (e : term O X)
  | IHavoc (x : X)
  | IAssume (g : G) (es : list (term O X))
  | IIdentity.

Arguments IAssign {X O G} x e.
Arguments IHavoc {X O G} x.
Arguments IAssume {X O G} g es.
Arguments IIdentity {X O G}.

(** Every leaf of a term is a declared variable. *)
Fixpoint term_in {O X : Type} (vs : list X) (e : term O X) : Prop :=
  match e with
  | Leaf x => In x vs
  | Node _ es =>
    (fix all (es : list (term O X)) : Prop :=
      match es with
      | nil => True
      | e :: rest => term_in vs e /\ all rest
      end) es
  end.

Module Type ENV_INT_PROGRAM (X : KEY_T) (M : MAP_T X) (C : INTERVAL_CUTOFF)
    (L : Z_LANGUAGE_T) (T : THRESHOLDS_T) (V : CUT_INTERVAL_T C L T)
    (E : ENV_ALL X M L V) (S : SYSTEM_T E).
  (* spec: variables row_plan *)
  Parameter variables : S.prog -> list X.t.
  Parameter row_plan :
    S.prog -> S.row -> option (S.key * list (int_instruction X.t L.op L.guard)).
  Definition scoped p (i : int_instruction X.t L.op L.guard) : Prop :=
    match i with
    | IAssign x e => In x (variables p) /\ term_in (variables p) e
    | IHavoc x => In x (variables p)
    | IAssume _ es => Forall (term_in (variables p)) es
    | IIdentity => True
    end.
  Definition apply_instruction (i : int_instruction X.t L.op L.guard) (s : E.t) : E.t :=
    match i with
    | IAssign x e => E.assign x e s
    | IHavoc x => E.havoc x s
    | IAssume g es => E.assume g es s
    | IIdentity => s
    end.
  (** Listed rows use only declared variables. *)
  Parameter instruction_scoped : forall p r, S.wf p -> In r (S.rows p) ->
    match row_plan p r with
    | None => True
    | Some (_, instructions) => Forall (scoped p) instructions
    end.
  (** Rows seed top or fold their ordered instructions over the actual source state. *)
  Parameter row_execution : forall p r look, S.wf p -> In r (S.rows p) ->
    S.eval p r look = Some
      (match row_plan p r with
       | None => E.top
       | Some (source, instructions) =>
         fold_left (fun s i => apply_instruction i s) instructions (look source)
       end, nil).
  (** Environment size charges every stored value and the map skeleton. *)
  Parameter size_environment : forall m, E.size (Reached m) =
    M.nodes m + fold_right Nat.add 1
      (map (fun code => match M.find code m with Some a => V.size a + 1 | None => 0 end)
        (M.codes m)).
  (** Unreachable environments carry no stored values. *)
  Parameter size_unreached : E.size Unreached = 0%nat.
  (** Unreachable environments carry no widening rank. *)
  Parameter rank_unreached : forall q, E.wrank q Unreached = 0%nat.
End ENV_INT_PROGRAM.

Module Type ENV_INT_BUDGET_SPEC (X : KEY_T) (M : MAP_T X) (C : INTERVAL_CUTOFF)
    (L : Z_LANGUAGE_T) (T : THRESHOLDS_T) (V : CUT_INTERVAL_T C L T)
    (E : ENV_ALL X M L V) (S : SYSTEM_T E)
    (P : ENV_INT_PROGRAM X M C L T V E S).
  Definition inv (p : S.prog) (s : E.t) : Prop :=
    match s with
    | Unreached => True
    | Reached m => M.wf m /\
        Forall (fun xa => In (fst xa) (P.variables p)) (M.elements m)
    end.
  Definition vsize (p : S.prog) : nat :=
    fold_right Nat.add 1 (map (fun x => X.bits x + C.bits + 3) (P.variables p)).
  Definition wmax (p : S.prog) (q : E.wparam) : nat :=
    fold_right Nat.add 0 (map (fun _ : X.t =>
      1 + 2 * (length (T.vals q) + 1)) (P.variables p)).
  Definition wunits (p : S.prog) : nat := length (P.variables p).
End ENV_INT_BUDGET_SPEC.
