(** * Numeric and payload dictionaries

    Numeric values describe complete words and payloads describe integers at a supplied width.
    For example, the same singleton payload can be tagged at width one or width eight.
    Builds on: DomainsValue, DomainsTerm and BitsExpr. *)

From Stdlib Require Import ZArith List Bool.
From Galois.Cost Require Import CostMonad.
From Galois.Lattice Require Import LatticeCore LatticeConcrete.
From Galois.Bits Require Import BitsWord BitsOp BitsExpr.
From Galois.Domains Require Import DomainsValue DomainsTerm.
Import List.ListNotations Cost.Notations Expr.

(** Numeric callbacks retain their own traversal charges. *)
Record numeric_domain (A : Type) : Type := NumericDomain {
  lat : lattice A;
  top_at : width -> A;
  of_const_c : width -> Z -> Cost.t A;
  forward_c : op -> list A -> Cost.t A;
  assume_c : op -> A -> list A -> Cost.t (list A);
  meet_c : A -> A -> Cost.t A
}.

Arguments lat {A}.
Arguments top_at {A}.
Arguments of_const_c {A}.
Arguments forward_c {A}.
Arguments assume_c {A}.
Arguments meet_c {A}.

Definition of_const {A} (D : numeric_domain A) w z := Cost.value (of_const_c D w z).
Definition forward {A} (D : numeric_domain A) o xs := Cost.value (forward_c D o xs).
Definition assume {A} (D : numeric_domain A) o a xs := Cost.value (assume_c D o a xs).
Definition meet {A} (D : numeric_domain A) a b := Cost.value (meet_c D a b).

(** Numeric laws retain defined words and make result assumptions reductive. *)
Record numeric_laws {A} (D : numeric_domain A) (G : concretisation A word) : Prop := {
  lat_laws : lattice_laws (lat D);
  gamma_laws : concretisation_laws (lat D) G;
  bot_empty : bottom_empty (lat D) G;
  top_at_sound : forall w z, is_word w z -> gamma G (top_at D w) (w, z);
  of_const_sound : forall w z, gamma G (of_const D w z) (w, wrap w z);
  forward_sound : forall o xs ys r, Forall2 (gamma G) xs ys ->
    eval_op o ys = Some r -> gamma G (forward D o xs) r;
  assume_sound : forall o a xs ys r, Forall2 (gamma G) xs ys ->
    eval_op o ys = Some r -> gamma G a r -> Forall2 (gamma G) (assume D o a xs) ys;
  assume_length : forall o a xs, length (assume D o a xs) = length xs;
  assume_refines : forall o a xs,
    Forall2 (fun x' x => leb (lat D) x' x = true) (assume D o a xs) xs;
  meet_sound : forall a b c, gamma G a c -> gamma G b c -> gamma G (meet D a b) c;
  meet_lower_left : forall a b, leb (lat D) (meet D a b) a = true
}.

Arguments lat_laws {A D G}.
Arguments gamma_laws {A D G}.
Arguments bot_empty {A D G}.
Arguments top_at_sound {A D G}.
Arguments of_const_sound {A D G}.
Arguments forward_sound {A D G}.
Arguments assume_sound {A D G}.
Arguments assume_length {A D G}.
Arguments assume_refines {A D G}.
Arguments meet_sound {A D G}.
Arguments meet_lower_left {A D G}.

(** Payload callbacks receive operand widths and an explicit result width. *)
Record word_domain (P : Type) : Type := WordDomain {
  plat : width -> lattice P;
  ptop : width -> P;
  pconst_c : width -> Z -> Cost.t P;
  pforward_c : op -> list (width * P) -> width -> Cost.t P;
  passume_c : op -> list (width * P) -> width -> P -> Cost.t (list P);
  pmeet_c : width -> P -> P -> Cost.t P
}.

Arguments plat {P}.
Arguments ptop {P}.
Arguments pconst_c {P}.
Arguments pforward_c {P}.
Arguments passume_c {P}.
Arguments pmeet_c {P}.

Definition pconst {P} (D : word_domain P) w z := Cost.value (pconst_c D w z).
Definition pforward {P} (D : word_domain P) o xs w := Cost.value (pforward_c D o xs w).
Definition passume {P} (D : word_domain P) o xs w a := Cost.value (passume_c D o xs w a).
Definition pmeet {P} (D : word_domain P) w a b := Cost.value (pmeet_c D w a b).

(** A payload describes a normalized word with its recorded operand width. *)
Definition payload_sound {P} (G : width -> P -> Z -> Prop) (wp : width * P)
    (y : word) : Prop :=
  fst wp = fst y /\ is_word (fst y) (snd y) /\ G (fst wp) (snd wp) (snd y).

(** Payload laws suffice to recover the complete numeric interface through width tags. *)
Record word_laws {P} (D : word_domain P) (G : width -> P -> Z -> Prop) : Prop := {
  plat_laws : forall w, lattice_laws (plat D w);
  pgamma_monotone : forall w a b z, leb (plat D w) a b = true -> G w a z -> G w b z;
  pgamma_bot_empty : forall w z, ~ G w (bot (plat D w)) z;
  ptop_sound : forall w z, is_word w z -> G w (ptop D w) z;
  pconst_sound : forall w z, G w (pconst D w z) (wrap w z);
  pforward_sound : forall o wps ys rw z, Forall2 (payload_sound G) wps ys ->
    eval_op o ys = Some (rw, z) -> G rw (pforward D o wps rw) z;
  passume_sound : forall o wps ys rw z q, Forall2 (payload_sound G) wps ys ->
    eval_op o ys = Some (rw, z) -> G rw q z ->
    Forall2 (fun p y => G (fst p) (snd p) (snd y))
      (combine (map fst wps) (passume D o wps rw q)) ys;
  passume_refines : forall o wps rw q,
    Forall2 (fun wp p' => leb (plat D (fst wp)) p' (snd wp) = true)
      wps (passume D o wps rw q);
  pmeet_sound : forall w a b z, G w a z -> G w b z -> G w (pmeet D w a b) z;
  pmeet_lower_left : forall w a b, leb (plat D w) (pmeet D w a b) a = true
}.

Arguments plat_laws {P D G}.
Arguments pgamma_monotone {P D G}.
Arguments pgamma_bot_empty {P D G}.
Arguments ptop_sound {P D G}.
Arguments pconst_sound {P D G}.
Arguments pforward_sound {P D G}.
Arguments passume_sound {P D G}.
Arguments passume_refines {P D G}.
Arguments pmeet_sound {P D G}.
Arguments pmeet_lower_left {P D G}.

(** Literal operators let numeric expressions use the generic term traversal. *)
Inductive numeric_op : Type :=
  | Literal (w : width) (z : Z)
  | Operator (o : op).

(** Translation retains every variable, literal and application. *)
Fixpoint numeric_term (e : expr) : term numeric_op nat :=
  match e with
  | Var i => Leaf i
  | Const w z => Node (Literal w z) []
  | App o es => Node (Operator o) (map numeric_term es)
  end.

(** Translation charges every syntax node and every operand-list cell. *)
Fixpoint numeric_term_c (e : expr) : Cost.t (term numeric_op nat) :=
  Cost.step ;;
  match e with
  | Var i => Cost.ret (Leaf i)
  | Const w z => Cost.ret (Node (Literal w z) [])
  | App o es =>
    Cost.map (Node (Operator o))
      ((fix go (es : list expr) : Cost.t (list (term numeric_op nat)) :=
        match es with
        | [] => Cost.ret []
        | e :: es =>
          Cost.step ;;
          let* t := numeric_term_c e in Cost.map (cons t) (go es)
        end) es)
  end.

(** Charged translation agrees with the structural syntax specification. *)
Theorem numeric_term_equation e : Cost.value (numeric_term_c e) = numeric_term e.
Proof.
  induction e as [i|w z|o es IH]; cbn [numeric_term_c numeric_term];
    autorewrite with galois_cost; try reflexivity.
  f_equal. induction IH as [|e He es Hes IHes]; cbn; [reflexivity|].
  now rewrite He, IHes.
Qed.

(** The internal term adapter uses transfers alone and leaves its width-one top unused. *)
Definition numeric_values {A} (D : numeric_domain A) : ValueAbs.t A numeric_op unit :=
  {| ValueAbs.lat := lat D;
     ValueAbs.top := top_at D 1%positive;
     ValueAbs.op_c := fun k xs =>
       match k with
       | Literal w z => Cost.step ;; of_const_c D w z
       | Operator o => Cost.step ;; forward_c D o xs
       end;
     ValueAbs.back_c := fun k a xs =>
       match k with
       | Literal _ _ => Cost.ret xs
       | Operator o => Cost.step ;; assume_c D o a xs
       end;
     ValueAbs.guard_c := fun _ xs => Cost.ret xs |}.

(** The concrete term evaluator uses word normalization for literals. *)
Definition numeric_eval (k : numeric_op) (xs : list word) : option word :=
  match k with
  | Literal w z => Some (w, wrap w z)
  | Operator o => eval_op o xs
  end.

(** Concrete environments contain normalized words. *)
Definition env_ok (env : nat -> word) := forall i, is_word (fst (env i)) (snd (env i)).

(** Environment meaning is pointwise. *)
Definition env_sound {A} (G : concretisation A word) (env : nat -> A)
    (cenv : nat -> word) := forall i, gamma G (env i) (cenv i).

(** Numeric evaluation retains translation and environment callback costs. *)
Definition num_eval_c {A} (D : numeric_domain A) (env : nat -> Cost.t A) e :=
  let* t := numeric_term_c e in abs_eval_c (numeric_values D) env t.

(** Pure numeric evaluation observes the charged implementation. *)
Definition num_eval {A} (D : numeric_domain A) (env : nat -> A) e :=
  Cost.value (num_eval_c D (fun x => Cost.ret (env x)) e).

(** Numeric assumptions retain translation costs and return charged environment lookups. *)
Definition num_assume_c {A} (D : numeric_domain A) (env : nat -> Cost.t A) e a :=
  let* t := numeric_term_c e in
  abs_assume_c (fun x y => Cost.step ;; Cost.ret (Nat.eqb x y)) (meet_c D)
    (numeric_values D) env t a.

(** Numeric assumptions use word equality on variable indices and the domain's meet. *)
Definition num_assume {A} (D : numeric_domain A) (env : nat -> A) e a :=
  fun i => Cost.value (Cost.value (num_assume_c D (fun x => Cost.ret (env x)) e a) i).

Local Lemma num_eval_equation {A} (D : numeric_domain A) env e :
  num_eval D env e = abs_eval (numeric_values D) env (numeric_term e).
Proof.
  unfold num_eval, num_eval_c. rewrite Cost.value_bind, numeric_term_equation. reflexivity.
Qed.

Local Lemma num_assume_equation {A} (D : numeric_domain A) env e a i :
  num_assume D env e a i =
  abs_assume (fun x y => Cost.step ;; Cost.ret (Nat.eqb x y)) (meet_c D)
    (numeric_values D) (fun x => Cost.ret (env x)) (numeric_term e) a i.
Proof.
  unfold num_assume, num_assume_c. rewrite Cost.value_bind, numeric_term_equation. reflexivity.
Qed.

Local Lemma numeric_term_eval env e : env_ok env ->
  eval_term numeric_eval env (numeric_term e) = eval eval_op env e.
Proof.
  intro Hok. induction e as [i|w z|o es IH].
  - rewrite eval_var, normalize_word_id by apply Hok. reflexivity.
  - reflexivity.
  - rewrite eval_app. cbn [numeric_term]. rewrite eval_term_node, map_map.
    assert (Hargs : sequence
      (map (fun e => eval_term numeric_eval env (numeric_term e)) es) =
      eval_args eval_op env es).
    { induction IH as [|e He es Hes IHes]; [reflexivity|].
      rewrite eval_args_cons.
      change ((match eval_term numeric_eval env (numeric_term e) with
        | Some c => match sequence
            (map (fun e => eval_term numeric_eval env (numeric_term e)) es) with
          | Some cs => Some (c :: cs)
          | None => None
          end
        | None => None
        end) =
        match eval eval_op env e, eval_args eval_op env es with
        | Some c, Some cs => Some (c :: cs)
        | _, _ => None
        end).
      rewrite He, IHes.
      destruct (eval eval_op env e), (eval_args eval_op env es); reflexivity. }
    rewrite Hargs. reflexivity.
Qed.

Local Lemma numeric_op_sound {A} (D : numeric_domain A) G :
  numeric_laws D G -> forall k xs cs c, Forall2 (gamma G) xs cs ->
  numeric_eval k cs = Some c -> gamma G (ValueAbs.op (numeric_values D) k xs) c.
Proof.
  intros H [w z|o] xs cs c Hxs Heval.
  - inversion Heval; subst c. apply (of_const_sound H).
  - exact (forward_sound H o xs cs c Hxs Heval).
Qed.

Local Lemma numeric_back_sound {A} (D : numeric_domain A) G :
  numeric_laws D G -> forall k a xs cs c, Forall2 (gamma G) xs cs ->
  numeric_eval k cs = Some c -> gamma G a c ->
  Forall2 (gamma G) (ValueAbs.back (numeric_values D) k a xs) cs.
Proof.
  intros H [w z|o] a xs cs c Hxs Heval Ha.
  - exact Hxs.
  - exact (assume_sound H o a xs cs c Hxs Heval Ha).
Qed.

(** Numeric evaluation retains every successful expression result in normalized environments. *)
Theorem num_eval_sound {A} (D : numeric_domain A) G env cenv e r :
  numeric_laws D G -> env_ok cenv -> env_sound G env cenv ->
  eval eval_op cenv e = Some r -> gamma G (num_eval D env e) r.
Proof.
  intros H Hok Henv Heval. rewrite num_eval_equation.
  eapply (term_eval_sound (numeric_values D)
    {| ValueSem.eval := numeric_eval; ValueSem.holds := fun _ _ => True |} G).
  - exact (numeric_op_sound D G H).
  - exact Henv.
  - rewrite numeric_term_eval by exact Hok. exact Heval.
Qed.

(** Numeric assumptions keep concrete environments satisfying the evaluated result. *)
Theorem num_assume_sound {A} (D : numeric_domain A) G env cenv e a r :
  numeric_laws D G -> env_ok cenv -> env_sound G env cenv ->
  eval eval_op cenv e = Some r -> gamma G a r ->
  env_sound G (num_assume D env e a) cenv.
Proof.
  intros H Hok Henv Heval Ha. unfold env_sound. intro i. rewrite num_assume_equation.
  eapply (term_assume_sound (numeric_values D)
    {| ValueSem.eval := numeric_eval; ValueSem.holds := fun _ _ => True |} G).
  - exact (numeric_op_sound D G H).
  - exact (numeric_back_sound D G H).
  - intros x y Hxy. apply Nat.eqb_eq. exact Hxy.
  - exact (meet_sound H).
  - exact Henv.
  - rewrite numeric_term_eval by exact Hok. exact Heval.
  - exact Ha.
Qed.

(** Numeric assumptions are pointwise reductive. *)
Theorem num_assume_refines {A} (D : numeric_domain A) G env e a i :
  numeric_laws D G -> leb (lat D) (num_assume D env e a i) (env i) = true.
Proof.
  intro H. rewrite num_assume_equation. exact (abs_assume_refines (numeric_values D)
    (fun x y => Cost.step ;; Cost.ret (Nat.eqb x y)) (meet_c D)
    (lat_laws H) (meet_lower_left H) (numeric_term e) (fun x => Cost.ret (env x)) a i).
Qed.

(** The charged numeric evaluator retains the values supplied by charged environment callbacks. *)
Theorem num_eval_c_sound {A} (D : numeric_domain A) G env cenv e r :
  numeric_laws D G -> env_ok cenv ->
  (forall i, gamma G (Cost.value (env i)) (cenv i)) ->
  eval eval_op cenv e = Some r -> gamma G (Cost.value (num_eval_c D env e)) r.
Proof.
  intros H Hok Henv He.
  unfold num_eval_c. rewrite Cost.value_bind, numeric_term_equation, abs_eval_projection.
  eapply (term_eval_sound (numeric_values D)
    {| ValueSem.eval := numeric_eval; ValueSem.holds := fun _ _ => True |} G).
  - exact (numeric_op_sound D G H).
  - exact Henv.
  - change (eval_term numeric_eval cenv (numeric_term e) = Some r).
    rewrite numeric_term_eval by exact Hok. exact He.
Qed.

(** Charged numeric assumptions retain concrete environments and all callback costs. *)
Theorem num_assume_c_sound {A} (D : numeric_domain A) G env cenv e a r :
  numeric_laws D G -> env_ok cenv ->
  (forall i, gamma G (Cost.value (env i)) (cenv i)) ->
  eval eval_op cenv e = Some r -> gamma G a r ->
  forall i, gamma G (Cost.value (Cost.value (num_assume_c D env e a) i)) (cenv i).
Proof.
  intros H Hok Henv He Ha i. unfold num_assume_c.
  rewrite Cost.value_bind, numeric_term_equation.
  eapply (term_assume_sound (numeric_values D)
    {| ValueSem.eval := numeric_eval; ValueSem.holds := fun _ _ => True |} G)
    with (env := env) (cenv := cenv) (t := numeric_term e) (a := a) (c := r).
  - exact (numeric_op_sound D G H).
  - exact (numeric_back_sound D G H).
  - intros x y Hxy. apply Nat.eqb_eq. exact Hxy.
  - exact (meet_sound H).
  - exact Henv.
  - change (eval_term numeric_eval cenv (numeric_term e) = Some r).
    rewrite numeric_term_eval by exact Hok. exact He.
  - exact Ha.
Qed.

Arguments num_eval_c : simpl never.
Arguments num_eval : simpl never.
Arguments num_assume_c : simpl never.
Arguments num_assume : simpl never.
