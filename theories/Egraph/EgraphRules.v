(** * Partial semantics and fact-guarded rules

    Interpretations assign partial results to terms, and guards read facts about holes.
    For example, a fact can distinguish an undefined result from a defined value.
    Builds on: EgraphSyntax and CostMonad. *)

From Stdlib Require Import List NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding.
From Galois.Egraph Require Import EgraphSyntax.
Import List.ListNotations.

(** * Partial term semantics *)

Module EggSem.

Record t (K V C : Type) : Type := Make {
  var_value : V -> option C;
  eval_op : K -> list C -> option C
}.

Arguments var_value {K V C} _ _.
Arguments eval_op {K V C} _ _ _.

Fixpoint denote {K Sort V C} (sem : t K V C) (term : EggTerm.t K Sort V) : option C :=
  match term with
  | EggTerm.Var _ v => var_value sem v
  | EggTerm.App _ op args =>
    match (fix go (ts : list (EggTerm.t K Sort V)) : option (list C) :=
      match ts with
      | [] => Some []
      | child :: rest =>
        match denote sem child with
        | None => None
        | Some c =>
          match go rest with
          | None => None
          | Some cs => Some (c :: cs)
          end
        end
      end) args with
    | None => None
    | Some cs => eval_op sem op cs
    end
  end.

Definition denote_args {K Sort V C} (sem : t K V C) (ts : list (EggTerm.t K Sort V)) :
    option (list C) :=
  (fix go (ts : list (EggTerm.t K Sort V)) : option (list C) :=
    match ts with
    | [] => Some []
    | child :: rest =>
      match denote sem child with
      | None => None
      | Some c =>
        match go rest with
        | None => None
        | Some cs => Some (c :: cs)
        end
      end
    end) ts.

(** Semantic equivalence compares the complete option result in each admissible model. *)
Definition equiv {K Sort V C} (adm : t K V C -> Prop) (l r : EggTerm.t K Sort V) : Prop :=
  forall sem, adm sem -> denote sem l = denote sem r.

End EggSem.

(** * Facts *)

Module EggFact.

Record t (F K Sort V C : Type) : Type := Make {
  holds : F -> option C -> Prop;
  check_c : F -> EggTerm.t K Sort V -> Cost.t bool
}.

Arguments holds {F K Sort V C} _ _ _.
Arguments check_c {F K Sort V C} _ _ _.

Definition check {F K Sort V C} (facts : t F K Sort V C) phi term :=
  Cost.value (check_c facts phi term).

(** A fact constrains the whole partial result in every admissible interpretation. *)
Definition valid {F K Sort V C} (facts : t F K Sort V C)
    (adm : EggSem.t K V C -> Prop) phi (term : EggTerm.t K Sort V) : Prop :=
  forall sem, adm sem -> holds facts phi (EggSem.denote sem term).

(** A successful ground check establishes the semantic meaning of its fact. *)
Record laws {F K Sort V C} (facts : t F K Sort V C) (adm : EggSem.t K V C -> Prop) :
    Prop := Laws {
  check_valid : forall phi term, check facts phi term = true -> valid facts adm phi term
}.

End EggFact.

(** * Rules *)

Module EggRule.

Record t (K Sort V H F : Type) : Type := Make {
  hole_enc : encoding H;
  holes : list H;
  hole_sort_c : H -> Cost.t (option Sort);
  lhs : EggPattern.t K Sort V H;
  rhs : EggPattern.t K Sort V H;
  guard_c : (H -> F) -> Cost.t bool
}.

Arguments hole_enc {K Sort V H F} _.
Arguments holes {K Sort V H F} _.
Arguments hole_sort_c {K Sort V H F} _ _.
Arguments lhs {K Sort V H F} _.
Arguments rhs {K Sort V H F} _.
Arguments guard_c {K Sort V H F} _ _.

Definition hole_sort {K Sort V H F} (rule : t K Sort V H F) h :=
  Cost.value (hole_sort_c rule h).

Definition guard {K Sort V H F} (rule : t K Sort V H F) (facts : H -> F) :=
  Cost.value (guard_c rule facts).

(** Class-substitution maps require an injective hole encoding independently of rule typing. *)
Definition encoding_laws {K Sort V H F} (rule : t K Sort V H F) : Prop :=
  BaseEncoding.encoding_laws (hole_enc rule).

(** The declared hole environment types both sides and gives them the same result sort. *)
Definition wf {K Sort V H F} (a : EggAlg.t K Sort V) (rule : t K Sort V H F) : Prop :=
  NoDup (holes rule) /\
  (forall h, In h (holes rule) <-> exists s, hole_sort rule h = Some s) /\
  EggPattern.typed a (hole_sort rule) (lhs rule) /\
  EggPattern.typed a (hole_sort rule) (rhs rule) /\
  EggPattern.sort_of (lhs rule) = EggPattern.sort_of (rhs rule).

(** A guarded instance equates its sides when every declared hole has a valid fact. *)
Definition sound {K Sort V H F C} (a : EggAlg.t K Sort V)
    (adm : EggSem.t K V C -> Prop) (facts : EggFact.t F K Sort V C)
    (rule : t K Sort V H F) : Prop :=
  forall sub phi l r,
    EggSubst.sub_typed a (hole_sort rule) sub ->
    (forall h term, In h (holes rule) -> EggSubst.get sub h = Some term ->
      EggFact.valid facts adm (phi h) term) ->
    guard rule phi = true ->
    EggSubst.instantiate sub (lhs rule) = Some l ->
    EggSubst.instantiate sub (rhs rule) = Some r ->
    EggSem.equiv adm l r.

End EggRule.
