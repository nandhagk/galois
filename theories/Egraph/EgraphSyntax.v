(** * Sorted terms and patterns

    Terms and patterns carry sort annotations checked against an algebra.
    For example, instantiating a hole substitutes its assigned term.
    Builds on: BaseEncoding and CostMonad. *)

From Stdlib Require Import List NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding.
Import List.ListNotations.
Import Cost.Notations.

Scheme All for list.
Scheme All for Forall.

(** * Algebra *)

Module EggAlg.

Record t (K Sort V : Type) : Type := Make {
  op_enc : encoding K;
  sort_enc : encoding Sort;
  var_enc : encoding V;
  var_sort_c : V -> Cost.t (option Sort);
  op_shape_c : K -> list Sort -> Sort -> Cost.t bool
}.

Arguments var_sort_c {K Sort V} _ _.
Arguments op_shape_c {K Sort V} _ _ _ _.

Definition var_sort {K Sort V} (a : t K Sort V) (v : V) :=
  Cost.value (var_sort_c a v).

Definition op_shape {K Sort V} (a : t K Sort V) (op : K) (args : list Sort) (s : Sort) :=
  Cost.value (op_shape_c a op args s).

(** Primitive callbacks charge one tick in addition to each caller's invocation cost. *)
Definition of_pure {K Sort V} (ek : encoding K) (es : encoding Sort) (ev : encoding V)
    (vs : V -> option Sort) (shape : K -> list Sort -> Sort -> bool) : t K Sort V :=
  Make K Sort V ek es ev (fun v => Cost.lift (fun _ => 1%N) vs v)
    (fun op args s => Cost.lift (fun _ => 1%N) (fun _ => shape op args s) tt).

End EggAlg.

(** * Terms *)

Module EggTerm.

Inductive t (K Sort V : Type) : Type :=
  | Var (s : Sort) (v : V)
  | App (s : Sort) (op : K) (args : list (t K Sort V)).

Arguments Var {K Sort V}.
Arguments App {K Sort V}.

Definition sort_of {K Sort V} (term : t K Sort V) : Sort :=
  match term with
  | Var s _ => s
  | App s _ _ => s
  end.

Inductive typed {K Sort V} (a : EggAlg.t K Sort V) : t K Sort V -> Prop :=
  | typed_var : forall s v,
      EggAlg.var_sort a v = Some s -> typed a (Var s v)
  | typed_app : forall s op args,
      Forall (typed a) args ->
      EggAlg.op_shape a op (map sort_of args) s = true -> typed a (App s op args).

End EggTerm.

(** * Patterns *)

Module EggPattern.

Inductive t (K Sort V H : Type) : Type :=
  | Hole (s : Sort) (h : H)
  | Var (s : Sort) (v : V)
  | App (s : Sort) (op : K) (args : list (t K Sort V H)).

Arguments Hole {K Sort V H}.
Arguments Var {K Sort V H}.
Arguments App {K Sort V H}.

Definition sort_of {K Sort V H} (p : t K Sort V H) : Sort :=
  match p with
  | Hole s _ => s
  | Var s _ => s
  | App s _ _ => s
  end.

Inductive typed {K Sort V H} (a : EggAlg.t K Sort V) (hs : H -> option Sort) :
    t K Sort V H -> Prop :=
  | typed_hole : forall s h,
      hs h = Some s -> typed a hs (Hole s h)
  | typed_var : forall s v,
      EggAlg.var_sort a v = Some s -> typed a hs (Var s v)
  | typed_app : forall s op args,
      Forall (typed a hs) args ->
      EggAlg.op_shape a op (map sort_of args) s = true -> typed a hs (App s op args).

End EggPattern.

(** * Partial substitutions *)

Module EggSubst.

Definition t (K Sort V H : Type) := H -> Cost.t (option (EggTerm.t K Sort V)).

Definition get {K Sort V H} (sub : t K Sort V H) h := Cost.value (sub h).

(** A pure substitution charges one tick each time a hole is looked up. *)
Definition of_pure {K Sort V H} (sub : H -> option (EggTerm.t K Sort V)) : t K Sort V H :=
  fun h => Cost.lift (fun _ => 1%N) sub h.

Definition sub_typed {K Sort V H} (a : EggAlg.t K Sort V) (hs : H -> option Sort)
    (sub : t K Sort V H) : Prop :=
  forall h s, hs h = Some s ->
    exists term, get sub h = Some term /\ EggTerm.sort_of term = s /\ EggTerm.typed a term.

(** Each pattern and list cell is charged, including calls to the substitution. *)
Fixpoint instantiate_c {K Sort V H} (sub : t K Sort V H) (p : EggPattern.t K Sort V H)
    : Cost.t (option (EggTerm.t K Sort V)) :=
  Cost.step ;;
  match p with
  | EggPattern.Hole _ h =>
    Cost.step ;; sub h
  | EggPattern.Var s v =>
    Cost.ret (Some (EggTerm.Var s v))
  | EggPattern.App s op args =>
    let* result := (fix go (ps : list (EggPattern.t K Sort V H)) :=
      Cost.step ;;
      match ps with
      | [] => Cost.ret (Some [])
      | q :: rest =>
        let* term := instantiate_c sub q in
        match term with
        | None => Cost.ret None
        | Some term =>
          let* terms := go rest in
          Cost.ret (option_map (cons term) terms)
        end
      end) args in
    Cost.ret (option_map (EggTerm.App s op) result)
  end.

Definition instantiate {K Sort V H} (sub : t K Sort V H) (p : EggPattern.t K Sort V H) :=
  Cost.value (instantiate_c sub p).

Definition instantiate_args_c {K Sort V H} (sub : t K Sort V H)
    (ps : list (EggPattern.t K Sort V H)) : Cost.t (option (list (EggTerm.t K Sort V))) :=
  (fix go ps :=
    Cost.step ;;
    match ps with
    | [] => Cost.ret (Some [])
    | p :: rest =>
      let* term := instantiate_c sub p in
      match term with
      | None => Cost.ret None
      | Some term =>
        let* terms := go rest in
        Cost.ret (option_map (cons term) terms)
      end
    end) ps.

Definition instantiate_args {K Sort V H} (sub : t K Sort V H)
    (ps : list (EggPattern.t K Sort V H)) :=
  Cost.value (instantiate_args_c sub ps).

Local Lemma instantiate_app {K Sort V H} (sub : t K Sort V H) s op args :
  instantiate sub (EggPattern.App s op args) =
    option_map (EggTerm.App s op) (instantiate_args sub args).
Proof.
  reflexivity.
Qed.

Local Lemma pattern_typed_ind_all {K Sort V H} (a : EggAlg.t K Sort V)
    (hs : H -> option Sort) (P : EggPattern.t K Sort V H -> Prop)
    (Hhole : forall s h, hs h = Some s -> P (EggPattern.Hole s h))
    (Hvar : forall s v, EggAlg.var_sort a v = Some s -> P (EggPattern.Var s v))
    (Happ : forall s op args, Forall (EggPattern.typed a hs) args -> Forall P args ->
      EggAlg.op_shape a op (map EggPattern.sort_of args) s = true ->
      P (EggPattern.App s op args)) :
  forall p, EggPattern.typed a hs p -> P p.
Proof.
  fix IH 2.
  intros p Htyped.
  destruct Htyped as [s h Hsort|s v Hsort|s op args Hargs Hshape].
  - exact (Hhole s h Hsort).
  - exact (Hvar s v Hsort).
  - apply Happ; [exact Hargs| |exact Hshape].
    clear Hshape.
    induction Hargs as [|p ps Hp Hps IHps].
    + constructor.
    + constructor; [exact (IH p Hp)|exact IHps].
Qed.

Local Lemma instantiate_args_typed {K Sort V H} (a : EggAlg.t K Sort V)
    (sub : t K Sort V H) (ps : list (EggPattern.t K Sort V H)) :
  Forall (fun p => exists term, instantiate sub p = Some term /\
    EggTerm.typed a term /\ EggTerm.sort_of term = EggPattern.sort_of p) ps ->
  exists terms, instantiate_args sub ps = Some terms /\
    Forall (EggTerm.typed a) terms /\ map EggTerm.sort_of terms = map EggPattern.sort_of ps.
Proof.
  intros Hargs.
  induction Hargs as [|p ps [term [Hinst [Htyped Hsort]]] Hps
    [terms [Hinsts [Htypeds Hsorts]]]].
  - exists []; split; [reflexivity|split; [constructor|reflexivity]].
  - exists (term :: terms).
    split.
    + change (Cost.value (Cost.step ;;
        let* u := instantiate_c sub p in
        match u with
        | None => Cost.ret None
        | Some u =>
          let* us := instantiate_args_c sub ps in
          Cost.ret (option_map (cons u) us)
        end) = Some (term :: terms)).
      rewrite !Cost.value_bind.
      change (Cost.value (match instantiate sub p with
        | None => Cost.ret None
        | Some u =>
          let* us := instantiate_args_c sub ps in
          Cost.ret (option_map (cons u) us)
        end) = Some (term :: terms)).
      rewrite Hinst, Cost.value_bind, Cost.value_ret.
      unfold instantiate_args in Hinsts.
      now rewrite Hinsts.
    + split; [now constructor|cbn; now rewrite Hsort, Hsorts].
Qed.

(** A typed substitution instantiates a typed pattern at the pattern's annotated sort. *)
Theorem instantiate_typed {K Sort V H} (a : EggAlg.t K Sort V)
    (hs : H -> option Sort) (sub : t K Sort V H) (p : EggPattern.t K Sort V H) :
  EggPattern.typed a hs p -> sub_typed a hs sub ->
  exists term, instantiate sub p = Some term /\ EggTerm.typed a term /\
    EggTerm.sort_of term = EggPattern.sort_of p.
Proof.
  intros Htyped Hsub.
  apply (pattern_typed_ind_all a hs
    (fun p => exists term, instantiate sub p = Some term /\ EggTerm.typed a term /\
      EggTerm.sort_of term = EggPattern.sort_of p)); [| | |exact Htyped].
  - intros s h Hsort.
    destruct (Hsub h s Hsort) as [term [Hinst [Hsortt Htypedt]]].
    exists term; split; [exact Hinst|split; assumption].
  - intros s v Hsort.
    exists (EggTerm.Var s v); split; [reflexivity|split; [now constructor|reflexivity]].
  - intros s op args Hargs IHargs Hshape.
    destruct (instantiate_args_typed a sub args IHargs)
      as [terms [Hinst [Htypeds Hsorts]]].
    exists (EggTerm.App s op terms); split.
    + rewrite instantiate_app, Hinst; reflexivity.
    + split; [apply EggTerm.typed_app; [exact Htypeds|now rewrite Hsorts]|reflexivity].
Qed.

End EggSubst.
