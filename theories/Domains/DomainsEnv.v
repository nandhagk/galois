(** * Finite environment states

    Reached maps read absent variables as top and fresh bottom denotes unreachable states.
    For example, assignment stores a term value and leaves every other variable unchanged.
    Builds on: LatticeEnv, DomainsTerm, DomainsState and DomainsRelational. *)

From Stdlib Require Import List Bool NArith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap.
From Galois.Lattice Require Import LatticeCore LatticeConcrete LatticeAdjoin LatticeEnv.
From Galois.Domains Require Import DomainsValue DomainsTerm DomainsState DomainsRelational.
Import List.ListNotations Cost.Notations.

Module StateEnv.

(** State carriers retain map representation validity and a distinct unreachable constructor. *)
Definition t {X} (E : encoding X) A := env_carrier Top_default E A.

(** The computational lattice needs the component top value without a top-order proof. *)
Definition lat {A K G X} (E : encoding X) (D : ValueAbs.t A K G) : lattice (t E A) :=
  lift_bot (env_valid_core E Top_default (ValueAbs.top D) (ValueAbs.lat D)).

(** Reached reads retain the public map lookup charge. *)
Definition read_c {A K G X} (E : encoding X) (D : ValueAbs.t A K G)
    (m : env_map E A) x :=
  Map.find_or_c E (ValueAbs.top D) x (env_raw m).

Definition read {A K G X} (E : encoding X) (D : ValueAbs.t A K G) m x :=
  Cost.value (read_c E D m x).

(** Projection of unreachable states returns the component bottom. *)
Definition project_c {A K G X} (E : encoding X) (D : ValueAbs.t A K G) x (s : t E A) :=
  Cost.step ;;
  match s with
  | None => Cost.ret (bot (ValueAbs.lat D))
  | Some m => read_c E D m x
  end.

(** Assignment evaluates before writing and keeps fresh bottom unreachable. *)
Definition assign_c {A K G X} (E : encoding X) (D : ValueAbs.t A K G)
    x e (s : t E A) :=
  Cost.step ;;
  match s with
  | None => Cost.ret None
  | Some m =>
    let* a := abs_eval_c D (read_c E D m) e in
    env_set_c Top_default E x a s
  end.

(** Havoc replaces the selected fact with top even when it already has a binding. *)
Definition havoc_c {A K G X} (E : encoding X) (D : ValueAbs.t A K G) x (s : t E A) :=
  env_set_c Top_default E x (ValueAbs.top D) s.

(** Variable support lists leaf occurrences in source order. *)
Fixpoint vars {K X} (e : term K X) : list X :=
  match e with
  | Leaf x => [x]
  | Node _ es => flat_map vars es
  end.

(** Support traversal charges term visits, operand visits and copied support cells. *)
Fixpoint vars_c {K X} (e : term K X) : Cost.t (list X) :=
  Cost.step ;;
  match e with
  | Leaf x => Cost.ret [x]
  | Node _ es =>
    (fix go (es : list (term K X)) : Cost.t (list X) :=
      match es with
      | [] => Cost.ret []
      | e :: es =>
        Cost.step ;;
        let* xs := vars_c e in
        let* ys := go es in app_c xs ys
      end) es
  end.

(** Charged variable collection agrees with the structural support specification. *)
Theorem vars_equation {K X} (e : term K X) : Cost.value (vars_c e) = vars e.
Proof.
  induction e using term_ind'.
  - reflexivity.
  - cbn [vars_c vars]. autorewrite with galois_cost.
    induction H as [|e es He Hes IH]; cbn; autorewrite with galois_cost.
    + reflexivity.
    + now rewrite He, IH.
Qed.

(** Support collection keeps all leaf occurrences across the ordered term list. *)
Fixpoint supports_c {K X} (es : list (term K X)) : Cost.t (list X) :=
  match es with
  | [] => Cost.ret []
  | e :: es =>
    Cost.step ;;
    let* xs := vars_c e in
    let* ys := supports_c es in app_c xs ys
  end.

(** Collected support contains exactly the term-list leaf occurrences. *)
Theorem supports_equation {K X} (es : list (term K X)) :
  Cost.value (supports_c es) = flat_map vars es.
Proof.
  induction es as [|e es IH]; cbn [supports_c flat_map];
    autorewrite with galois_cost; [reflexivity|].
  now rewrite vars_equation, IH.
Qed.

(** Term-list refinement delegates each term to the generic engine in left-to-right order. *)
Fixpoint refine_c {A K G X} (E : encoding X) (D : ValueAbs.t A K G)
    (meet : A -> A -> Cost.t A) (es : list (term K X)) (qs : list A)
    (f : X -> Cost.t A) : Cost.t (X -> Cost.t A) :=
  match es, qs with
  | e :: es, q :: qs =>
    Cost.step ;;
    let* f' := abs_assume_c (eqb_c E) meet D f e q in refine_c E D meet es qs f'
  | _, _ => Cost.ret f
  end.

(** Materialization reads the final lookup once per support occurrence and stores its value. *)
Fixpoint materialize_c {A X} (E : encoding X) (xs : list X) (f : X -> Cost.t A)
    (m : env_map E A) : Cost.t (env_map E A) :=
  match xs with
  | [] => Cost.ret m
  | x :: xs =>
    Cost.step ;;
    let* a := Cost.step ;; f x in
    let* m' := env_update_c E x a m in materialize_c E xs f m'
  end.

(** Guard refinement materializes only affected leaves after the complete generic term fold. *)
Definition assume_c {A K G X} (E : encoding X) (D : ValueAbs.t A K G)
    (meet : A -> A -> Cost.t A) g es (s : t E A) :=
  Cost.step ;;
  match s with
  | None => Cost.ret None
  | Some m =>
    let* xs := supports_c es in
    let* args := map_c (fun e => abs_eval_c D (read_c E D m) e) es in
    let* qs := Cost.step ;; ValueAbs.guard_c D g args in
    let* f := refine_c E D meet es qs (read_c E D m) in
    Cost.map Some (materialize_c E xs f m)
  end.

(** Any open value dictionary and charged meet construct a runnable state dictionary. *)
Definition state {A K G X} (E : encoding X) (D : ValueAbs.t A K G)
    (meet : A -> A -> Cost.t A) : StateAbs.t (t E A) A X K G :=
  {| StateAbs.lat := lat E D;
     StateAbs.top := Some (env_empty E);
     StateAbs.assign_c := assign_c E D;
     StateAbs.havoc_c := havoc_c E D;
     StateAbs.assume_c := assume_c E D meet;
     StateAbs.project_c := project_c E D |}.

(** Concrete updates use encoded equality and require injectivity only in their laws. *)
Definition semantics {X C} (E : encoding X) : StateSem.t X C :=
  {| StateSem.update := fun x c st y => if eqb E y x then c else st y |}.

(** Reached states denote pointwise value meanings and fresh bottom has empty meaning. *)
Definition meaning {A C K G X} (E : encoding X) (D : ValueAbs.t A K G)
    (gam : concretisation A C) : concretisation (t E A) (X -> C) :=
  {| gamma := fun s st =>
    match s with
    | None => False
    | Some m => forall x, gamma gam (read E D m x) (st x)
    end |}.

(** Reached reads are the public environment observations. *)
Theorem read_equation {A K G X} (E : encoding X) (D : ValueAbs.t A K G) m x :
  read E D m x = env_read E (ValueAbs.top D) x m.
Proof.
  reflexivity.
Qed.

(** Generic term assumptions leave variables outside the term support unchanged. *)
Theorem assume_frame {A K G X} (E : encoding X) (HE : encoding_laws E)
    (D : ValueAbs.t A K G) meet e :
  forall f q x, ~ In x (vars e) ->
    abs_assume (eqb_c E) meet D f e q x = Cost.value (f x).
Proof.
  induction e using term_ind'; intros f q y Houtside.
  - unfold abs_assume. unfold abs_assume_c at 1. autorewrite with galois_cost.
    assert (Hneq : y <> x).
    { intro Heq. subst y. apply Houtside. left. reflexivity. }
    cbn beta iota. destruct (Cost.value (eqb_c E y x)) eqn:Hsame;
      autorewrite with galois_cost.
    + exfalso. apply Hneq. exact (proj1 (eqb_true_iff E HE y x) Hsame).
    + reflexivity.
  - unfold abs_assume. unfold abs_assume_c at 1. autorewrite with galois_cost.
    generalize (Cost.value (ValueAbs.back_c D k q
      (map (fun e => Cost.value (abs_eval_c D f e)) ts))) as qs.
    revert f Houtside. induction H as [|e es He Hes IH]; intros f Houtside qs.
    + reflexivity.
    + destruct qs as [|a qs]; cbn; autorewrite with galois_cost; [reflexivity|].
      transitivity
        (Cost.value (Cost.value (abs_assume_c (eqb_c E) meet D f e a) y)).
      * apply IH. intro Hin. apply Houtside. cbn [vars flat_map].
        apply in_or_app. right. exact Hin.
      * apply He. intro Hin. apply Houtside. cbn [vars flat_map].
        apply in_or_app. left. exact Hin.
Qed.

(** The complete term fold changes no coordinate outside the union of its leaf supports. *)
Theorem refine_frame {A K G X} (E : encoding X) (HE : encoding_laws E)
    (D : ValueAbs.t A K G) meet es :
  forall qs f x, ~ In x (flat_map vars es) ->
    Cost.value (Cost.value (refine_c E D meet es qs f) x) = Cost.value (f x).
Proof.
  induction es as [|e es IH]; intros [|q qs] f x Houtside;
    cbn [refine_c]; autorewrite with galois_cost; try reflexivity.
  rewrite IH.
  - apply assume_frame; [exact HE|]. intro Hin. apply Houtside.
    cbn [flat_map]. apply in_or_app. left. exact Hin.
  - intro Hin. apply Houtside. cbn [flat_map]. apply in_or_app. right. exact Hin.
Qed.

(** Finite materialization agrees pointwise when its input already agrees outside the support. *)
Theorem materialize_agrees {A X} (E : encoding X) (HE : encoding_laws E)
    d xs (f : X -> Cost.t A) :
  forall m, (forall x, ~ In x xs -> env_read E d x m = Cost.value (f x)) ->
    forall x, env_read E d x (Cost.value (materialize_c E xs f m)) = Cost.value (f x).
Proof.
  induction xs as [|y xs IH]; intros m Houtside x.
  - apply Houtside. cbn. tauto.
  - cbn [materialize_c]. autorewrite with galois_cost. apply IH.
    intros z Hz. change (env_read E d z (env_update E y (Cost.value (f y)) m) =
      Cost.value (f z)).
    destruct (BaseEq.eqb_spec E HE z y) as [Heq|Hneq].
    + subst z. apply env_read_update_same.
    + rewrite env_read_update_other by assumption. apply Houtside. cbn. intuition.
Qed.

(** Materialization retains lookup and setter charges at every occurrence, including duplicates. *)
Theorem materialize_cost {A X} (E : encoding X) x xs (f : X -> Cost.t A) m :
  Cost.ticks (materialize_c E (x :: xs) f m) =
    (2 + Cost.ticks (f x) + Cost.ticks (env_update_c E x (Cost.value (f x)) m) +
      Cost.ticks (materialize_c E xs f (env_update E x (Cost.value (f x)) m)))%N.
Proof.
  cbn [materialize_c]. autorewrite with galois_cost.
  fold (env_update E x (Cost.value (f x)) m). lia.
Qed.

(** The materialized assumption reads exactly the final generic lookup at every coordinate. *)
Theorem assume_agrees {A K G X} (E : encoding X) (HE : encoding_laws E)
    (D : ValueAbs.t A K G) meet g es m x :
  let args := map (fun e => Cost.value (abs_eval_c D (read_c E D m) e)) es in
  let qs := Cost.value (ValueAbs.guard_c D g args) in
  let f := Cost.value (refine_c E D meet es qs (read_c E D m)) in
  StateAbs.project (state E D meet) x
    (StateAbs.assume (state E D meet) g es (Some m)) = Cost.value (f x).
Proof.
  cbn zeta.
  set (qs := Cost.value (ValueAbs.guard_c D g
    (map (fun e => Cost.value (abs_eval_c D (read_c E D m) e)) es))).
  set (f := Cost.value (refine_c E D meet es qs (read_c E D m))).
  change (Cost.value (project_c E D x (Cost.value (assume_c E D meet g es (Some m)))) =
    Cost.value (f x)).
  unfold assume_c. autorewrite with galois_cost. rewrite supports_equation.
  change (env_read E (ValueAbs.top D) x
    (Cost.value (materialize_c E (flat_map vars es) f m)) = Cost.value (f x)).
  apply materialize_agrees; [exact HE|].
  intros y Hy. rewrite <- read_equation. symmetry. apply refine_frame; assumption.
Qed.

(** Assumptions retain the old lookup at every variable outside their collected leaf support. *)
Theorem assume_unchanged {A K G X} (E : encoding X) (HE : encoding_laws E)
    (D : ValueAbs.t A K G) meet g es m x :
  ~ In x (flat_map vars es) ->
  StateAbs.project (state E D meet) x
    (StateAbs.assume (state E D meet) g es (Some m)) = read E D m x.
Proof.
  intro Houtside. rewrite (assume_agrees E HE).
  apply refine_frame; assumption.
Qed.

(** Operand evaluation gives abstract facts for the same ordered concrete result list. *)
Theorem eval_terms_sound {A C K G X} (D : ValueAbs.t A K G)
    (M : ValueSem.t C K G) gam (H : value_laws D M gam) (es : list (term K X)) :
  forall f st cs, (forall x, gamma gam (Cost.value (f x)) (st x)) ->
    sequence (map (eval_term (ValueSem.eval M) st) es) = Some cs ->
    Forall2 (gamma gam) (map (fun e => Cost.value (abs_eval_c D f e)) es) cs.
Proof.
  induction es as [|e es IH]; intros f st cs Henv Heval; cbn [map sequence] in Heval.
  - inversion Heval. constructor.
  - destruct (eval_term (ValueSem.eval M) st e) as [c|] eqn:Hc; [|discriminate].
    destruct (sequence (map (eval_term (ValueSem.eval M) st) es)) as [ds|]
      eqn:Hds; [|discriminate].
    inversion Heval; subst cs. cbn [map]. constructor.
    + rewrite abs_eval_projection. eapply abs_eval_sound; eauto.
    + eapply IH; eauto.
Qed.

(** Left-to-right generic refinement retains every concrete state satisfying the target facts. *)
Theorem refine_sound {A C K G X} (E : encoding X) (HE : encoding_laws E)
    (D : ValueAbs.t A K G) (M : ValueSem.t C K G) gam (H : value_laws D M gam)
    meet (Hmeet : forall a b c, gamma gam a c -> gamma gam b c ->
      gamma gam (Cost.value (meet a b)) c) es :
  forall qs f st cs, (forall x, gamma gam (Cost.value (f x)) (st x)) ->
    sequence (map (eval_term (ValueSem.eval M) st) es) = Some cs ->
    Forall2 (gamma gam) qs cs ->
    forall x, gamma gam (Cost.value (Cost.value (refine_c E D meet es qs f) x)) (st x).
Proof.
  induction es as [|e es IH]; intros qs f st cs Henv Heval Hqs x.
  - exact (Henv x).
  - cbn [map sequence] in Heval.
    destruct (eval_term (ValueSem.eval M) st e) as [c|] eqn:Hc; [|discriminate].
    destruct (sequence (map (eval_term (ValueSem.eval M) st) es)) as [ds|]
      eqn:Hds; [|discriminate].
    inversion Heval; subst cs. inversion Hqs as [|q c' qs' ds' Hq Htail]; subst.
    cbn [refine_c]. autorewrite with galois_cost.
    eapply IH; [|exact Hds|exact Htail].
    intro y. eapply abs_assume_sound; eauto.
    intros u v Htest. exact (proj1 (eqb_true_iff E HE u v) Htest).
Qed.

(** Injective encodings give the concrete selected-variable and distinct-variable update laws. *)
Theorem semantics_laws {X C} (E : encoding X) (HE : encoding_laws E) :
  StateSem.laws (@semantics X C E).
Proof.
  constructor.
  - intros x c st. cbn [semantics StateSem.update]. now rewrite eqb_refl.
  - intros x y c st Hneq. cbn [semantics StateSem.update].
    rewrite (proj2 (eqb_false_iff E HE y x)) by congruence. reflexivity.
Qed.

(** Replacing one stored value describes the corresponding concrete update. *)
Theorem update_sound {A C K G X} (E : encoding X) (HE : encoding_laws E)
    (D : ValueAbs.t A K G) (gam : concretisation A C) m st x a c :
  gamma (meaning E D gam) (Some m) st -> gamma gam a c ->
  gamma (meaning E D gam) (Some (env_update E x a m))
    (StateSem.update (semantics E) x c st).
Proof.
  intros Henv Ha y. cbn [semantics StateSem.update].
  rewrite read_equation. destruct (BaseEq.eqb_spec E HE y x) as [Heq|Hneq].
  - subst y. rewrite env_read_update_same. exact Ha.
  - rewrite env_read_update_other by assumption. apply Henv.
Qed.

(** Assignment describes the selected term result and keeps every distinct variable's meaning. *)
Theorem assign_sound {A C K G X} (E : encoding X) (HE : encoding_laws E)
    (D : ValueAbs.t A K G) (M : ValueSem.t C K G) gam (H : value_laws D M gam)
    meet x e s st c :
  gamma (meaning E D gam) s st -> eval_term (ValueSem.eval M) st e = Some c ->
  gamma (meaning E D gam) (StateAbs.assign (state E D meet) x e s)
    (StateSem.update (semantics E) x c st).
Proof.
  destruct s as [m|]; intros Henv Heval; [|contradiction].
  change (gamma (meaning E D gam) (Cost.value (assign_c E D x e (Some m)))
    (StateSem.update (semantics E) x c st)).
  unfold assign_c. autorewrite with galois_cost.
  change (gamma (meaning E D gam)
    (env_set Top_default E x (Cost.value (abs_eval_c D (read_c E D m) e)) (Some m))
    (StateSem.update (semantics E) x c st)).
  rewrite env_set_top_equation. apply update_sound; [exact HE|exact Henv|].
  rewrite abs_eval_projection. eapply abs_eval_sound; eauto.
Qed.

(** Havoc describes every replacement value at the selected variable. *)
Theorem havoc_sound {A C K G X} (E : encoding X) (HE : encoding_laws E)
    (D : ValueAbs.t A K G) (M : ValueSem.t C K G) gam (H : value_laws D M gam)
    meet x s st c :
  gamma (meaning E D gam) s st ->
  gamma (meaning E D gam) (StateAbs.havoc (state E D meet) x s)
    (StateSem.update (semantics E) x c st).
Proof.
  destruct s as [m|]; intro Henv; [|contradiction].
  change (gamma (meaning E D gam) (env_set Top_default E x (ValueAbs.top D) (Some m))
    (StateSem.update (semantics E) x c st)).
  rewrite env_set_top_equation. apply update_sound; [exact HE|exact Henv|apply (top_full H)].
Qed.

(** Guard materialization describes every state satisfying its ordered concrete operand results. *)
Theorem assume_sound {A C K G X} (E : encoding X) (HE : encoding_laws E)
    (D : ValueAbs.t A K G) (M : ValueSem.t C K G) gam (H : value_laws D M gam)
    meet (Hmeet : forall a b c, gamma gam a c -> gamma gam b c ->
      gamma gam (Cost.value (meet a b)) c) g es s st cs :
  gamma (meaning E D gam) s st ->
  sequence (map (eval_term (ValueSem.eval M) st) es) = Some cs ->
  ValueSem.holds M g cs ->
  gamma (meaning E D gam) (StateAbs.assume (state E D meet) g es s) st.
Proof.
  destruct s as [m|]; intros Henv Heval Hguard; [|contradiction].
  change (gamma (meaning E D gam) (Cost.value (assume_c E D meet g es (Some m))) st).
  unfold assume_c. autorewrite with galois_cost. rewrite supports_equation.
  set (qs := Cost.value (ValueAbs.guard_c D g
    (map (fun e => Cost.value (abs_eval_c D (read_c E D m) e)) es))).
  set (f := Cost.value (refine_c E D meet es qs (read_c E D m))).
  intro x. rewrite read_equation, materialize_agrees with (f := f).
  - eapply refine_sound; [exact HE|exact H|exact Hmeet|exact Henv|exact Heval|].
    apply (guard_sound H); [eapply eval_terms_sound; eauto|exact Hguard].
  - exact HE.
  - intros y Hy. rewrite <- read_equation. symmetry.
    apply refine_frame; assumption.
Qed.

(** Projection describes the selected concrete coordinate of every reached state. *)
Theorem project_sound {A C K G X} (E : encoding X) (D : ValueAbs.t A K G)
    (gam : concretisation A C) meet x s st :
  gamma (meaning E D gam) s st ->
  gamma gam (StateAbs.project (state E D meet) x s) (st x).
Proof.
  destruct s as [m|]; intro Henv; [exact (Henv x)|contradiction].
Qed.

(** The computational lattice inherits weak laws under the separate abstract top-order duty. *)
Theorem lat_laws {A K G X} (E : encoding X) (HE : encoding_laws E)
    (D : ValueAbs.t A K G) :
  lattice_laws (ValueAbs.lat D) ->
  (forall a, leb (ValueAbs.lat D) a (ValueAbs.top D) = true) ->
  lattice_laws (lat E D).
Proof.
  intros H Htop.
  exact (env_laws Top_default E HE (ValueAbs.lat D)
    {| top_value := ValueAbs.top D; top_greatest := Htop |} H).
Qed.

(** Environment meaning is monotone under the same explicit abstract top-order duty. *)
Theorem meaning_laws {A C K G X} (E : encoding X) (HE : encoding_laws E)
    (D : ValueAbs.t A K G) (gam : concretisation A C) :
  concretisation_laws (ValueAbs.lat D) gam ->
  (forall a, leb (ValueAbs.lat D) a (ValueAbs.top D) = true) ->
  concretisation_laws (lat E D) (meaning E D gam).
Proof.
  intros Hgam Htop. constructor. intros s r st Hle Henv.
  change (leb (lat E D) s r = true) in Hle.
  pose proof (eq_trans (eq_sym (leb_lift_bot (env_valid_core E Top_default
    (ValueAbs.top D) (ValueAbs.lat D)) s r)) Hle) as Hcompare.
  clear Hle. destruct s as [m|], r as [n|]; try contradiction; try discriminate.
  intro x. eapply (gamma_monotone Hgam); [|exact (Henv x)].
  apply (proj1 (env_core_leb E HE Top_default _ _ Htop m n) Hcompare x).
Qed.

(** An empty reached map describes every state because its missing coordinates read top. *)
Theorem top_full {A C K G X} (E : encoding X) (D : ValueAbs.t A K G)
    (M : ValueSem.t C K G) gam (H : value_laws D M gam) :
  forall st, gamma (meaning E D gam) (Some (env_empty E)) st.
Proof.
  intros st x. change (gamma gam
    (Map.find_or E (ValueAbs.top D) x Map.empty) (st x)).
  rewrite Map.find_or_equation, Map.get_empty. apply (DomainsValue.top_full H).
Qed.

(** Optional observations retain the fresh-bottom distinction at every coordinate. *)
Definition observe {A K G X} (E : encoding X) (D : ValueAbs.t A K G) x (s : t E A) :=
  option_map (fun m => read E D m x) s.

(** Widening equality requires only the widening operator's optional/default compatibility. *)
Theorem widen_pointwise {A K G X} (E : encoding X) (D : ValueAbs.t A K G)
    (Hwide : forall a b,
      env_default (ValueAbs.top D)
        (env_optional Top_default (ValueAbs.top D) (ValueAbs.lat D) Env_widen a b) =
      widen (ValueAbs.lat D) (env_default (ValueAbs.top D) a)
        (env_default (ValueAbs.top D) b)) x s r :
  observe E D x (widen (lat E D) s r) =
    widen (lift_bot (ValueAbs.lat D)) (observe E D x s) (observe E D x r).
Proof.
  transitivity (observe E D x
    (match s, r with
    | None, _ => r
    | _, None => s
    | Some m, Some n =>
      Some (widen (env_valid_core E Top_default (ValueAbs.top D) (ValueAbs.lat D)) m n)
    end)).
  - exact (f_equal (observe E D x)
      (widen_lift_bot (env_valid_core E Top_default (ValueAbs.top D) (ValueAbs.lat D)) s r)).
  - destruct s as [m|], r as [n|];
      cbn [observe option_map]; rewrite widen_lift_bot; try reflexivity.
    f_equal. rewrite !read_equation.
    change (env_read E (ValueAbs.top D) x
      (Cost.value (env_merge_c E Top_default (ValueAbs.top D) (ValueAbs.lat D)
        Env_widen m n)) = widen (ValueAbs.lat D)
          (env_read E (ValueAbs.top D) x m) (env_read E (ValueAbs.top D) x n)).
    rewrite env_merge_observe, Hwide.
    reflexivity.
Qed.

(** Renaming traverses stored bindings and charges every client key conversion. *)
Definition rename_c {A X} (E : encoding X) (f : X -> Cost.t X) (s : t E A) :=
  Cost.step ;;
  match s with
  | None => Cost.ret None
  | Some m =>
    let* xs := Map.elements_c (env_raw m) in
    let* ys := map_c (fun kv =>
      let* y := Cost.step ;; f (fst kv) in Cost.ret (y, snd kv)) xs in
    Cost.map Some (env_of_list_c E ys)
  end.

(** The environment instance closes by identity and uses generic ordered forgetting. *)
Definition relational {A K G X} (E : encoding X) (D : ValueAbs.t A K G)
    (meet : A -> A -> Cost.t A) : Relational.t (t E A) A X K G :=
  {| Relational.state := state E D meet;
     Relational.closure_c := fun s => Cost.ret s;
     Relational.forget_all_c := Relational.forget_c (state E D meet);
     Relational.rename_c := rename_c E;
     Relational.project_term_c := fun e s =>
       Cost.step ;;
       match s with
       | None => Cost.ret (bot (ValueAbs.lat D))
       | Some m => abs_eval_c D (read_c E D m) e
       end |}.

(** Reached renaming reconstructs precisely the converted stored bindings. *)
Theorem rename_equation {A X} (E : encoding X) (f : X -> Cost.t X) (m : env_map E A) :
  Cost.value (rename_c E f (Some m)) =
    Some (env_of_list E
      (map (fun kv => (Cost.value (f (fst kv)), snd kv)) (Map.elements (env_raw m)))).
Proof.
  unfold rename_c. autorewrite with galois_cost. reflexivity.
Qed.

Local Lemma select_constant {X A} (E : encoding X) z (xs : list (X * A)) a :
  (forall k b, In (k, b) xs -> eqb E z k = true -> b = a) ->
  forall old, fold_left
    (fun old kv => if eqb E z (fst kv) then Some (snd kv) else old) xs old =
    if existsb (fun kv => eqb E z (fst kv)) xs then Some a else old.
Proof.
  induction xs as [|[k b] xs IH]; intros Hall old; [reflexivity|].
  cbn [fold_left existsb fst snd]. rewrite IH.
  - destruct (eqb E z k) eqn:Hsame; cbn [orb].
    + rewrite (Hall k b (or_introl eq_refl) Hsame).
      destruct (existsb (fun kv => eqb E z (fst kv)) xs); reflexivity.
    + reflexivity.
  - intros j c Hin. apply Hall. right. exact Hin.
Qed.

Local Lemma select_origin {X A} (E : encoding X) (HE : encoding_laws E)
    z (xs : list (X * A)) old a :
  fold_left (fun old kv => if eqb E z (fst kv) then Some (snd kv) else old) xs old =
    Some a -> old = Some a \/ In (z, a) xs.
Proof.
  revert old. induction xs as [|[k b] xs IH]; intros old Hresult.
  - left. exact Hresult.
  - cbn [fold_left fst snd] in Hresult.
    destruct (IH _ Hresult) as [Hfirst|Hrest].
    + destruct (eqb E z k) eqn:Hsame.
      * apply (eqb_true_iff E HE) in Hsame. subst k.
        injection Hfirst as Heq. subst b. right. left. reflexivity.
      * left. exact Hfirst.
    + right. right. exact Hrest.
Qed.

(** Every stored result of renaming comes from an original binding at a converted key. *)
Theorem rename_origin {A X} (E : encoding X) (HE : encoding_laws E)
    (f : X -> Cost.t X) (m : env_map E A) z a :
  Map.get E z (env_raw (env_of_list E
    (map (fun kv => (Cost.value (f (fst kv)), snd kv)) (Map.elements (env_raw m))))) =
      Some a ->
  exists x, Cost.value (f x) = z /\ Map.get E x (env_raw m) = Some a.
Proof.
  rewrite env_of_list_raw, Map.of_list_get. intro Hget.
  destruct (select_origin E HE _ _ _ _ Hget) as [Hnone|Hin]; [discriminate|].
  apply in_map_iff in Hin. destruct Hin as [[x b] [Hpair Hin]].
  cbn [fst snd] in Hpair. injection Hpair as Hkey Hval. subst z b.
  exists x. split; [reflexivity|]. apply (Map.elements_spec E HE).
  - exact (proj2_sig m).
  - exact Hin.
Qed.

(** Injective renaming retains the original optional lookup at every image coordinate. *)
Theorem rename_image {A X} (E : encoding X) (HE : encoding_laws E)
    (f : X -> Cost.t X) (Hf : Relational.injective f) (m : env_map E A) x :
  Map.get E (Cost.value (f x)) (env_raw (env_of_list E
    (map (fun kv => (Cost.value (f (fst kv)), snd kv)) (Map.elements (env_raw m))))) =
    Map.get E x (env_raw m).
Proof.
  set (ys := map (fun kv => (Cost.value (f (fst kv)), snd kv))
    (Map.elements (env_raw m))).
  destruct (Map.get E x (env_raw m)) as [a|] eqn:Hx.
  - rewrite env_of_list_raw, Map.of_list_get.
    assert (Hall : forall k b, In (k, b) ys ->
      eqb E (Cost.value (f x)) k = true -> b = a).
    { intros k b Hin Hsame. apply in_map_iff in Hin.
      destruct Hin as [[y c] [Hpair Hin]]. cbn [fst snd] in Hpair.
      injection Hpair as Hkey Hval. subst k b.
      apply (eqb_true_iff E HE) in Hsame. apply Hf in Hsame. subst y.
      pose proof (proj1 (Map.elements_spec E HE x c (env_raw m) (proj2_sig m)) Hin) as Hc.
      rewrite Hx in Hc. now injection Hc. }
    rewrite (select_constant E _ ys a Hall).
    assert (Hhit : existsb (fun kv => eqb E (Cost.value (f x)) (fst kv)) ys = true).
    { apply existsb_exists. exists (Cost.value (f x), a). split.
      - apply in_map_iff. exists (x, a). split; [reflexivity|].
        apply (Map.elements_spec E HE x a (env_raw m) (proj2_sig m)). exact Hx.
      - apply eqb_refl. }
    now rewrite Hhit.
  - destruct (Map.get E (Cost.value (f x)) (env_raw (env_of_list E ys)))
      as [a|] eqn:Hget; [|reflexivity].
    destruct (rename_origin E HE f m _ a Hget) as [y [Hkey Hy]].
    apply Hf in Hkey. subst y. congruence.
Qed.

(** A coordinate outside the renaming image reads top without any inverse or surjectivity duty. *)
Theorem rename_fresh {A K G X} (E : encoding X) (HE : encoding_laws E)
    (D : ValueAbs.t A K G) meet f (m : env_map E A) z :
  (forall x, Cost.value (f x) <> z) ->
  StateAbs.project (state E D meet) z (Cost.value (rename_c E f (Some m))) = ValueAbs.top D.
Proof.
  intro Hfresh. rewrite rename_equation.
  change (Map.find_or E (ValueAbs.top D) z (env_raw (env_of_list E
    (map (fun kv => (Cost.value (f (fst kv)), snd kv)) (Map.elements (env_raw m))))) =
      ValueAbs.top D).
  rewrite Map.find_or_equation.
  destruct (Map.get E z (env_raw (env_of_list E
    (map (fun kv => (Cost.value (f (fst kv)), snd kv)) (Map.elements (env_raw m))))))
    as [a|] eqn:Hget; [|reflexivity].
  destruct (rename_origin E HE f m z a Hget) as [x [Hkey Hx]].
  exfalso. exact (Hfresh x Hkey).
Qed.

(** Renaming has the pullback meaning and leaves all coordinates outside its image at top. *)
Theorem rename_meaning {A C K G X} (E : encoding X) (HE : encoding_laws E)
    (D : ValueAbs.t A K G) (M : ValueSem.t C K G) gam (H : value_laws D M gam)
    f (Hf : Relational.injective f) s st :
  gamma (meaning E D gam) (Cost.value (rename_c E f s)) st <->
    gamma (meaning E D gam) s (fun x => st (Cost.value (f x))).
Proof.
  destruct s as [m|]; [rewrite rename_equation|reflexivity].
  split.
  - intros Henv x. specialize (Henv (Cost.value (f x))).
    rewrite read_equation in Henv |- *.
    change (gamma gam (Map.find_or E (ValueAbs.top D) (Cost.value (f x))
      (env_raw (env_of_list E
        (map (fun kv => (Cost.value (f (fst kv)), snd kv))
          (Map.elements (env_raw m)))))) (st (Cost.value (f x)))) in Henv.
    rewrite Map.find_or_equation, rename_image in Henv by assumption.
    change (gamma gam (Map.find_or E (ValueAbs.top D) x (env_raw m))
      (st (Cost.value (f x)))).
    rewrite Map.find_or_equation. exact Henv.
  - intros Henv z. rewrite read_equation.
    change (gamma gam (Map.find_or E (ValueAbs.top D) z
      (env_raw (env_of_list E
        (map (fun kv => (Cost.value (f (fst kv)), snd kv))
          (Map.elements (env_raw m)))))) (st z)).
    rewrite Map.find_or_equation.
    destruct (Map.get E z (env_raw (env_of_list E
      (map (fun kv => (Cost.value (f (fst kv)), snd kv))
        (Map.elements (env_raw m)))))) as [a|] eqn:Hget.
    + destruct (rename_origin E HE f m z a Hget) as [x [Hkey Hx]].
      specialize (Henv x). rewrite read_equation in Henv.
      change (gamma gam (Map.find_or E (ValueAbs.top D) x (env_raw m))
        (st (Cost.value (f x)))) in Henv.
      rewrite Map.find_or_equation, Hx, Hkey in Henv. exact Henv.
    + apply (DomainsValue.top_full H).
Qed.

End StateEnv.

(** The environment concretisation exposes the reached-pointwise and fresh-bottom meanings. *)
Definition env_concretisation {A C K G X} (E : encoding X) (D : ValueAbs.t A K G)
    (gam : concretisation A C) := StateEnv.meaning E D gam.

(** Environment assignment soundness is independent of abstract top-order evidence. *)
Theorem env_assign_sound {A C K G X} (E : encoding X) (HE : encoding_laws E)
    (D : ValueAbs.t A K G) (M : ValueSem.t C K G) gam (H : value_laws D M gam)
    meet x e s st c :
  gamma (env_concretisation E D gam) s st -> eval_term (ValueSem.eval M) st e = Some c ->
  gamma (env_concretisation E D gam) (StateAbs.assign (StateEnv.state E D meet) x e s)
    (StateSem.update (StateEnv.semantics E) x c st).
Proof.
  exact (StateEnv.assign_sound E HE D M gam H meet x e s st c).
Qed.

(** Environment havoc describes every selected-coordinate replacement. *)
Theorem env_havoc_sound {A C K G X} (E : encoding X) (HE : encoding_laws E)
    (D : ValueAbs.t A K G) (M : ValueSem.t C K G) gam (H : value_laws D M gam)
    meet x s st c :
  gamma (env_concretisation E D gam) s st ->
  gamma (env_concretisation E D gam) (StateAbs.havoc (StateEnv.state E D meet) x s)
    (StateSem.update (StateEnv.semantics E) x c st).
Proof.
  exact (StateEnv.havoc_sound E HE D M gam H meet x s st c).
Qed.

(** Environment guard refinement retains satisfying concrete states after finite materialization. *)
Theorem env_assume_sound {A C K G X} (E : encoding X) (HE : encoding_laws E)
    (D : ValueAbs.t A K G) (M : ValueSem.t C K G) gam (H : value_laws D M gam)
    meet (Hmeet : forall a b c, gamma gam a c -> gamma gam b c ->
      gamma gam (Cost.value (meet a b)) c) g es s st cs :
  gamma (env_concretisation E D gam) s st ->
  sequence (map (eval_term (ValueSem.eval M) st) es) = Some cs ->
  ValueSem.holds M g cs ->
  gamma (env_concretisation E D gam) (StateAbs.assume (StateEnv.state E D meet) g es s) st.
Proof.
  exact (StateEnv.assume_sound E HE D M gam H meet Hmeet g es s st cs).
Qed.

(** Environment projection describes the selected concrete coordinate. *)
Theorem env_project_sound {A C K G X} (E : encoding X) (D : ValueAbs.t A K G)
    (gam : concretisation A C) meet x s st :
  gamma (env_concretisation E D gam) s st ->
  gamma gam (StateAbs.project (StateEnv.state E D meet) x s) (st x).
Proof.
  exact (StateEnv.project_sound E D gam meet x s st).
Qed.

(** Optional pointwise widening uses the applicable widening/default equation alone. *)
Theorem env_widen_pointwise {A K G X} (E : encoding X) (D : ValueAbs.t A K G)
    (Hwide : forall a b,
      env_default (ValueAbs.top D)
        (env_optional Top_default (ValueAbs.top D) (ValueAbs.lat D) Env_widen a b) =
      widen (ValueAbs.lat D) (env_default (ValueAbs.top D) a)
        (env_default (ValueAbs.top D) b)) x s r :
  StateEnv.observe E D x (widen (StateEnv.lat E D) s r) =
    widen (lift_bot (ValueAbs.lat D))
      (StateEnv.observe E D x s) (StateEnv.observe E D x r).
Proof.
  exact (StateEnv.widen_pointwise E D Hwide x s r).
Qed.

(** Two reached states project their widening to the component widening of their projections. *)
Theorem env_widen_reached {A K G X} (E : encoding X) (D : ValueAbs.t A K G)
    meet (Hwide : forall a b,
      env_default (ValueAbs.top D)
        (env_optional Top_default (ValueAbs.top D) (ValueAbs.lat D) Env_widen a b) =
      widen (ValueAbs.lat D) (env_default (ValueAbs.top D) a)
        (env_default (ValueAbs.top D) b)) x (m n : env_map E A) :
  StateAbs.project (StateEnv.state E D meet) x
    (widen (StateEnv.lat E D) (Some m) (Some n)) =
  widen (ValueAbs.lat D)
    (StateAbs.project (StateEnv.state E D meet) x (Some m))
    (StateAbs.project (StateEnv.state E D meet) x (Some n)).
Proof.
  pose proof (env_widen_pointwise E D Hwide x (Some m) (Some n)) as Heq.
  pose proof (f_equal (env_default (bot (ValueAbs.lat D))) Heq) as Hvalues.
  exact Hvalues.
Qed.

(** Value soundness, injective encoding, abstract greatestness and sound meet give full state laws. *)
Theorem env_state_laws {A C K G X} (E : encoding X) (HE : encoding_laws E)
    (D : ValueAbs.t A K G) (M : ValueSem.t C K G) gam meet :
  value_laws D M gam ->
  (forall a, leb (ValueAbs.lat D) a (ValueAbs.top D) = true) ->
  (forall a b c, gamma gam a c -> gamma gam b c -> gamma gam (Cost.value (meet a b)) c) ->
  state_laws (StateEnv.state E D meet) M (StateEnv.semantics E)
    gam (env_concretisation E D gam).
Proof.
  intros H Htop Hmeet. constructor.
  - apply StateEnv.lat_laws; [exact HE|exact (lat_ok H)|exact Htop].
  - apply StateEnv.meaning_laws; [exact HE|exact (gamma_ok H)|exact Htop].
  - intros st Hbot. exact Hbot.
  - apply (StateEnv.top_full E D M gam H).
  - apply StateEnv.semantics_laws. exact HE.
  - exact (env_assign_sound E HE D M gam H meet).
  - exact (env_havoc_sound E HE D M gam H meet).
  - exact (env_assume_sound E HE D M gam H meet Hmeet).
  - exact (env_project_sound E D gam meet).
Qed.

(** The environment relational instance inhabits closure, forgetting, renaming and term laws. *)
Theorem env_relational_laws {A C K G X} (E : encoding X) (HE : encoding_laws E)
    (D : ValueAbs.t A K G) (M : ValueSem.t C K G) gam meet :
  value_laws D M gam ->
  (forall a, leb (ValueAbs.lat D) a (ValueAbs.top D) = true) ->
  (forall a b c, gamma gam a c -> gamma gam b c -> gamma gam (Cost.value (meet a b)) c) ->
  relational_laws (StateEnv.relational E D meet) M (StateEnv.semantics E)
    gam (env_concretisation E D gam).
Proof.
  intros H Htop Hmeet. constructor.
  - exact (env_state_laws E HE D M gam meet H Htop Hmeet).
  - intros s st. reflexivity.
  - intro s. apply (leb_refl (StateEnv.lat_laws E HE D (lat_ok H) Htop)).
  - intros xs s. apply Relational.forget_equation.
  - intros f s old new Hf Hagree Henv.
    apply (proj2 (StateEnv.rename_meaning E HE D M gam H f Hf s new)).
    destruct s as [m|]; [|contradiction]. intro x.
    rewrite (Hagree x). exact (Henv x).
  - intros f s new Hf. exact (StateEnv.rename_meaning E HE D M gam H f Hf s new).
  - intros e [m|] st c Henv Heval; [|contradiction].
    change (gamma gam (Cost.value (abs_eval_c D (StateEnv.read_c E D m) e)) c).
    rewrite abs_eval_projection. eapply abs_eval_sound; eauto.
Qed.
