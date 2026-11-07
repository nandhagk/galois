(** * Generic terms and refinement

    Evaluation and assumptions recurse through ordered operand lists.
    For example, two occurrences of a variable share the refinements from the first occurrence.
    Builds on: DomainsValue and CostList. *)

From Stdlib Require Import List Bool.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Lattice Require Import LatticeCore LatticeConcrete.
From Galois.Domains Require Import DomainsValue.
Import List.ListNotations Cost.Notations.

Scheme All for list.

(** Terms use arbitrary operators and variables. *)
Inductive term (K X : Type) : Type :=
  | Leaf (x : X)
  | Node (k : K) (ts : list (term K X)).

Arguments Leaf {K X}.
Arguments Node {K X}.

(** Nested induction supplies a hypothesis for every immediate operand. *)
Theorem term_ind' {K X} (P : term K X -> Prop) :
  (forall x, P (Leaf x)) ->
  (forall k ts, Forall P ts -> P (Node k ts)) -> forall t, P t.
Proof.
  intros Hleaf Hnode. fix IH 1. intros [x|k ts].
  - apply Hleaf.
  - apply Hnode. induction ts as [|t ts Hts]; constructor; auto.
Qed.

(** Sequencing successful optional values retains their list order. *)
Fixpoint sequence {C} (xs : list (option C)) : option (list C) :=
  match xs with
  | [] => Some []
  | Some c :: xs =>
    match sequence xs with
    | Some cs => Some (c :: cs)
    | None => None
    end
  | None :: _ => None
  end.

(** Concrete evaluation propagates an undefined operand. *)
Fixpoint eval_term {C K X} (ev : K -> list C -> option C) (env : X -> C)
    (t : term K X) : option C :=
  match t with
  | Leaf x => Some (env x)
  | Node k ts =>
    match sequence (map (eval_term ev env) ts) with
    | Some cs => ev k cs
    | None => None
    end
  end.

(** A concrete leaf reads its environment unchanged. *)
Theorem eval_term_leaf {C K X} (ev : K -> list C -> option C) env (x : X) :
  eval_term ev env (Leaf x) = Some (env x).
Proof.
  reflexivity.
Qed.

(** A concrete node evaluates its ordered operands before dispatch. *)
Theorem eval_term_node {C K X} (ev : K -> list C -> option C) env k
    (ts : list (term K X)) :
  eval_term ev env (Node k ts) =
    match sequence (map (eval_term ev env) ts) with
    | Some cs => ev k cs
    | None => None
    end.
Proof.
  reflexivity.
Qed.

(** Abstract evaluation charges term visits, operand visits and dictionary calls. *)
Fixpoint abs_eval_c {A K G X} (D : ValueAbs.t A K G) (env : X -> Cost.t A)
    (t : term K X) : Cost.t A :=
  Cost.step ;;
  match t with
  | Leaf x => Cost.step ;; env x
  | Node k ts =>
    let* xs := (fix go (ts : list (term K X)) : Cost.t (list A) :=
      match ts with
      | [] => Cost.ret []
      | t :: ts =>
        Cost.step ;;
        let* a := abs_eval_c D env t in
        Cost.map (cons a) (go ts)
      end) ts in
    Cost.step ;; ValueAbs.op_c D k xs
  end.

(** The pure evaluator is the result of the charged traversal. *)
Definition abs_eval {A K G X} (D : ValueAbs.t A K G) (env : X -> A) t :=
  Cost.value (abs_eval_c D (fun x => Cost.ret (env x)) t).

(** An abstract leaf reads its environment unchanged. *)
Theorem abs_eval_leaf {A K G X} (D : ValueAbs.t A K G) (env : X -> A) x :
  abs_eval D env (Leaf x) = env x.
Proof.
  reflexivity.
Qed.

(** A node transfers the ordered values of its children. *)
Theorem abs_eval_node {A K G X} (D : ValueAbs.t A K G) (env : X -> A) k ts :
  abs_eval D env (Node k ts) = ValueAbs.op D k (map (abs_eval D env) ts).
Proof.
  assert (Hargs : Cost.value
    ((fix go (ts : list (term K X)) : Cost.t (list A) :=
      match ts with
      | [] => Cost.ret []
      | t :: ts =>
        Cost.step ;;
        let* a := abs_eval_c D (fun x => Cost.ret (env x)) t in
        Cost.map (cons a) (go ts)
      end) ts) = map (abs_eval D env) ts).
  { induction ts as [|t ts IH]; cbn; [reflexivity|]. now rewrite IH. }
  unfold abs_eval at 1. cbn [abs_eval_c].
  autorewrite with galois_cost. rewrite Hargs. reflexivity.
Qed.

(** Assumptions visit operands left to right and retain each earlier update. *)
Fixpoint abs_assume_c {A K G X} (eqb : X -> X -> Cost.t bool)
    (meet : A -> A -> Cost.t A) (D : ValueAbs.t A K G)
    (env : X -> Cost.t A) (t : term K X) (a : A) : Cost.t (X -> Cost.t A) :=
  Cost.step ;;
  match t with
  | Leaf x =>
    Cost.ret (fun y =>
      Cost.step ;;
      let* same := eqb y x in
      if same then
        let* b := env y in Cost.step ;; meet b a
      else env y)
  | Node k ts =>
    let* xs := map_c (fun t => abs_eval_c D env t) ts in
    let* qs := Cost.step ;; ValueAbs.back_c D k a xs in
    (fix go (ts : list (term K X)) (qs : list A)
        (env : X -> Cost.t A) : Cost.t (X -> Cost.t A) :=
      match ts, qs with
      | t :: ts, q :: qs =>
        Cost.step ;;
        let* env' := abs_assume_c eqb meet D env t q in
        go ts qs env'
      | _, _ => Cost.ret env
      end) ts qs env
  end.

(** Pure assumptions retain the costed environment representation until each lookup. *)
Definition abs_assume {A K G X} (eqb : X -> X -> Cost.t bool)
    (meet : A -> A -> Cost.t A) (D : ValueAbs.t A K G)
    (env : X -> Cost.t A) t a : X -> A :=
  fun x => Cost.value (Cost.value (abs_assume_c eqb meet D env t a) x).

(** Successful evaluation gives a related list of abstract operand values. *)
Local Lemma sequence_sound {T A C} (R : A -> C -> Prop) (af : T -> A)
    (cf : T -> option C) ts :
  Forall (fun t => forall c, cf t = Some c -> R (af t) c) ts ->
  forall cs, sequence (map cf ts) = Some cs -> Forall2 R (map af ts) cs.
Proof.
  intros H. induction H as [|t ts Ht Hts IH]; intros cs Heval; cbn in Heval.
  - inversion Heval. constructor.
  - destruct (cf t) as [c|] eqn:Hc; [|discriminate].
    destruct (sequence (map cf ts)) as [tail|] eqn:Htail; [|discriminate].
    inversion Heval; subst cs. constructor; [now apply Ht|now apply IH].
Qed.

(** Forward soundness alone suffices for term evaluation. *)
Theorem term_eval_sound {A C K G X} (D : ValueAbs.t A K G)
    (M : ValueSem.t C K G) gam :
  (forall k xs cs c, Forall2 (gamma gam) xs cs -> ValueSem.eval M k cs = Some c ->
    gamma gam (ValueAbs.op D k xs) c) ->
  forall (env : X -> A) cenv t c,
  (forall x, gamma gam (env x) (cenv x)) ->
  eval_term (ValueSem.eval M) cenv t = Some c -> gamma gam (abs_eval D env t) c.
Proof.
  intros H env cenv t. induction t using term_ind'; intros c Henv Heval.
  - cbn in Heval. inversion Heval; subst c. apply Henv.
  - rewrite abs_eval_node. cbn [eval_term] in Heval.
    destruct (sequence (map (eval_term (ValueSem.eval M) cenv) ts)) as [cs|]
      eqn:Hcs; [|discriminate].
    eapply H; [|exact Heval].
    eapply sequence_sound; [|exact Hcs].
    eapply Forall_impl; [|exact H0]. intros t IH d Hd. now apply IH.
Qed.

(** Abstract evaluation describes every successfully evaluated concrete term. *)
Theorem abs_eval_sound {A C K G X} (D : ValueAbs.t A K G)
    (M : ValueSem.t C K G) gam :
  value_laws D M gam -> forall (env : X -> A) cenv t c,
  (forall x, gamma gam (env x) (cenv x)) ->
  eval_term (ValueSem.eval M) cenv t = Some c -> gamma gam (abs_eval D env t) c.
Proof.
  intro H. apply term_eval_sound. exact (op_sound H).
Qed.

(** Evaluation observes environment values independently of their callback charges. *)
Theorem abs_eval_projection {A K G X} (D : ValueAbs.t A K G)
    (env : X -> Cost.t A) t :
  Cost.value (abs_eval_c D env t) = abs_eval D (fun x => Cost.value (env x)) t.
Proof.
  induction t using term_ind'.
  - reflexivity.
  - assert (Hargs : Cost.value
      ((fix go (ts : list (term K X)) : Cost.t (list A) :=
        match ts with
        | [] => Cost.ret []
        | t :: ts =>
          Cost.step ;;
          let* a := abs_eval_c D env t in Cost.map (cons a) (go ts)
        end) ts) = map (abs_eval D (fun x => Cost.value (env x))) ts).
    { induction H as [|t ts Ht Hts IH]; cbn; [reflexivity|].
      now rewrite Ht, IH. }
    rewrite abs_eval_node. cbn [abs_eval_c].
    autorewrite with galois_cost. rewrite Hargs. reflexivity.
Qed.

(** Forward and backward soundness suffice for term assumptions. *)
Theorem term_assume_sound {A C K G X} (D : ValueAbs.t A K G)
    (M : ValueSem.t C K G) gam (eqb : X -> X -> Cost.t bool)
    (meet : A -> A -> Cost.t A) :
  (forall k xs cs c, Forall2 (gamma gam) xs cs -> ValueSem.eval M k cs = Some c ->
    gamma gam (ValueAbs.op D k xs) c) ->
  (forall k a xs cs c, Forall2 (gamma gam) xs cs -> ValueSem.eval M k cs = Some c ->
    gamma gam a c -> Forall2 (gamma gam) (ValueAbs.back D k a xs) cs) ->
  (forall x y, Cost.value (eqb x y) = true -> x = y) ->
  (forall a b c, gamma gam a c -> gamma gam b c ->
    gamma gam (Cost.value (meet a b)) c) ->
  forall t (env : X -> Cost.t A) cenv a c,
  (forall x, gamma gam (Cost.value (env x)) (cenv x)) ->
  eval_term (ValueSem.eval M) cenv t = Some c -> gamma gam a c ->
  forall x, gamma gam (abs_assume eqb meet D env t a x) (cenv x).
Proof.
  intros Hforward Hback Heq Hmeet t. induction t using term_ind';
    intros env cenv a c Henv Heval Ha j.
  - cbn [eval_term] in Heval. inversion Heval; subst c.
    unfold abs_assume. cbn [abs_assume_c]. autorewrite with galois_cost.
    destruct (Cost.value (eqb j x)) eqn:Hsame; autorewrite with galois_cost.
    + apply Heq in Hsame. subst j. apply Hmeet; [apply Henv|exact Ha].
    + apply Henv.
  - unfold abs_assume. cbn [abs_assume_c]. autorewrite with galois_cost.
    cbn [eval_term] in Heval.
    destruct (sequence (map (eval_term (ValueSem.eval M) cenv) ts)) as [cs|]
      eqn:Hcs; [|discriminate].
    assert (Hxs : Forall2 (gamma gam)
      (map (fun t => Cost.value (abs_eval_c D env t)) ts) cs).
    { eapply sequence_sound; [|exact Hcs]. apply Forall_forall.
      intros t Hin d Hd. rewrite abs_eval_projection.
      eapply term_eval_sound; eauto. }
    pose proof (Hback k a _ cs c Hxs Heval Ha) as Hqs.
    unfold ValueAbs.back in Hqs.
    remember (Cost.value (ValueAbs.back_c D k a
      (map (fun t => Cost.value (abs_eval_c D env t)) ts))) as qs eqn:Hqdef in *.
    clear Hqdef.
    clear Ha Heval Hxs. generalize dependent env. generalize dependent cs. revert qs.
    induction H as [|t ts Ht Hts IH]; intros qs cs Hcs Hqs env Henv.
    + apply Henv.
    + cbn [map sequence] in Hcs.
      destruct (eval_term (ValueSem.eval M) cenv t) as [d|] eqn:Hd;
        [|discriminate].
      destruct (sequence (map (eval_term (ValueSem.eval M) cenv) ts)) as [ds|]
        eqn:Hds; [|discriminate].
      inversion Hcs; subst cs. inversion Hqs as [|q d' qs' ds' Hq Htail]; subst.
      cbn. autorewrite with galois_cost.
      apply (IH qs' ds eq_refl Htail _).
      intro y. apply (Ht env cenv q d Henv Hd Hq y).
Qed.

(** Assumptions retain any concrete environment satisfying the result fact and term. *)
Theorem abs_assume_sound {A C K G X} (D : ValueAbs.t A K G)
    (M : ValueSem.t C K G) gam (eqb : X -> X -> Cost.t bool)
    (meet : A -> A -> Cost.t A) :
  value_laws D M gam ->
  (forall x y, Cost.value (eqb x y) = true -> x = y) ->
  (forall a b c, gamma gam a c -> gamma gam b c ->
    gamma gam (Cost.value (meet a b)) c) ->
  forall t (env : X -> Cost.t A) cenv a c,
  (forall x, gamma gam (Cost.value (env x)) (cenv x)) ->
  eval_term (ValueSem.eval M) cenv t = Some c -> gamma gam a c ->
  forall x, gamma gam (abs_assume eqb meet D env t a x) (cenv x).
Proof.
  intro H. apply term_assume_sound; [exact (op_sound H)|exact (back_sound H)].
Qed.

(** Every assumption is pointwise below its original environment when meet lowers its left input. *)
Theorem abs_assume_refines {A K G X} (D : ValueAbs.t A K G)
    (eqb : X -> X -> Cost.t bool) (meet : A -> A -> Cost.t A) :
  lattice_laws (ValueAbs.lat D) ->
  (forall a b, leb (ValueAbs.lat D) (Cost.value (meet a b)) a = true) ->
  forall t (env : X -> Cost.t A) a x,
  leb (ValueAbs.lat D) (abs_assume eqb meet D env t a x) (Cost.value (env x)) = true.
Proof.
  intros HL Hmeet t. induction t using term_ind'; intros env a j.
  - unfold abs_assume. cbn [abs_assume_c]. autorewrite with galois_cost.
    destruct (Cost.value (eqb j x)); autorewrite with galois_cost;
      [apply Hmeet|apply (leb_refl HL)].
  - unfold abs_assume. cbn [abs_assume_c]. autorewrite with galois_cost.
    generalize (Cost.value (ValueAbs.back_c D k a
      (map (fun t => Cost.value (abs_eval_c D env t)) ts))) as qs.
    revert env. induction H as [|t ts Ht Hts IH]; intros env qs.
    + apply (leb_refl HL).
    + destruct qs as [|q qs]; cbn; autorewrite with galois_cost.
      * apply (leb_refl HL).
      * eapply (leb_trans HL); [apply IH|apply Ht].
Qed.

Arguments abs_eval_c : simpl never.
Arguments abs_eval : simpl never.
Arguments abs_assume_c : simpl never.
Arguments abs_assume : simpl never.
Arguments eval_term : simpl never.
