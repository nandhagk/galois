(** * Integer environment budget instance

    The budget uses the finite variables and row execution of an integer program.
    For example, every assignment writes a declared variable.
    Builds on: EnvIntBudgetSig and SystemSig. *)

From Stdlib Require Import List PArith Bool Lia.
From Stdlib.Sorting Require Import Permutation.
From Galois.Base Require Import KeySig MapSig.
From Galois.Domains Require Import LangSig ValueSig IntervalSig ThresholdsSig CutIntervalSig.
From Galois.States Require Import EnvSig EnvIntBudgetSig.
From Galois.Fixpoint Require Import SystemSig.

Local Open Scope nat_scope.

Module EnvIntBudget (X : KEY_T) (M : MAP_T X) (C : INTERVAL_CUTOFF)
    (L : Z_LANGUAGE_T) (T : THRESHOLDS_T) (V : CUT_INTERVAL_T C L T)
    (E : ENV_ALL X M L V) (S : SYSTEM_T E)
    (P : ENV_INT_PROGRAM X M C L T V E S) <: BUDGET E S.
  Include ENV_INT_BUDGET_SPEC X M C L T V E S P.

  (** Every successful lookup in an invariant map names a declared variable. *)
  Lemma inv_get : forall p m x a, inv p (Reached m) ->
    M.get x m = Some a -> In x (P.variables p).
  Proof.
    intros p m x a [Hwf Hsupport] Hget.
    rewrite Forall_forall in Hsupport.
    apply (Hsupport (x, a)).
    apply (proj2 (M.elements_spec V.t m x a Hwf)). exact Hget.
  Qed.

  (** Consistent maps with declared lookup keys satisfy the environment invariant. *)
  Lemma inv_of_get : forall p m, M.wf m ->
    (forall x a, M.get x m = Some a -> In x (P.variables p)) -> inv p (Reached m).
  Proof.
    intros p m Hwf Hget. split; [exact Hwf|]. apply Forall_forall.
    intros [x a] Hin. apply (Hget x a).
    apply (proj1 (M.elements_spec V.t m x a Hwf)). exact Hin.
  Qed.

  (** A merge preserving absence stores only keys from its two invariant inputs. *)
  Lemma inv_merge : forall p ma mb (f : option V.t -> option V.t -> option V.t),
    inv p (Reached ma) -> inv p (Reached mb) -> f None None = None ->
    inv p (Reached (M.merge f ma mb)).
  Proof.
    intros p ma mb f Ha Hb Hnone. apply inv_of_get.
    - apply M.wf_merge; [exact (proj1 Ha)|exact (proj1 Hb)].
    - intros x a Hget. rewrite (M.get_merge V.t V.t V.t f ma mb x Hnone) in Hget.
      destruct (M.get x ma) as [va|] eqn:Hleft.
      + exact (inv_get p ma x va Ha Hleft).
      + destruct (M.get x mb) as [vb|] eqn:Hright.
        * exact (inv_get p mb x vb Hb Hright).
        * now rewrite Hnone in Hget.
  Qed.

  (** Bottom satisfies the scoped environment invariant. *)
  Lemma inv_bot : forall p, inv p E.bot.
  Proof.
    intro p. rewrite E.F_bot. constructor.
  Qed.

  (** Joining scoped environments preserves the invariant. *)
  Lemma inv_join : forall p a b, inv p a -> inv p b -> inv p (E.join a b).
  Proof.
    intros p a b Ha Hb. rewrite E.F_join.
    destruct a as [|ma], b as [|mb]; try assumption.
    rewrite E.F_join_map. apply inv_merge; [exact Ha|exact Hb|reflexivity].
  Qed.

  (** Narrowing scoped environments preserves the invariant. *)
  Lemma inv_narrow : forall p a b, inv p a -> inv p b -> inv p (E.narrow a b).
  Proof.
    intros p a b Ha Hb. rewrite E.F_narrow. destruct (E.is_bot b); [exact Hb|].
    destruct a as [|ma], b as [|mb]; try assumption.
    apply inv_merge; [exact Ha|exact Hb|reflexivity].
  Qed.

  (** Widening scoped environments preserves the invariant. *)
  Lemma inv_widen : forall p w a b, inv p a -> inv p b -> inv p (E.widen w a b).
  Proof.
    intros p w a b Ha Hb. rewrite E.F_widen. destruct (E.leb b a); [exact Ha|].
    destruct a as [|ma], b as [|mb]; try assumption.
    apply inv_merge; [exact Ha|exact Hb|reflexivity].
  Qed.

  (** Writing a declared variable preserves the stored-key invariant. *)
  Lemma inv_set : forall p m x a, inv p (Reached m) -> In x (P.variables p) ->
    inv p (Reached (M.set x a m)).
  Proof.
    intros p m x a Hinv Hdeclared. apply inv_of_get.
    - apply M.wf_set. exact (proj1 Hinv).
    - intros y b Hget. destruct (X.eqb_spec y x) as [Heq|Hneq].
      + subst y. exact Hdeclared.
      + rewrite M.get_set_other in Hget by exact Hneq.
        exact (inv_get p m y b Hinv Hget).
  Qed.

  (** The empty reached map stores only declared variables. *)
  Lemma inv_top : forall p, inv p E.top.
  Proof.
    intro p. rewrite E.F_top. apply inv_of_get; [apply M.wf_empty|].
    intros x a Hget. rewrite M.get_empty in Hget. discriminate.
  Qed.

  (** Every child of a scoped operator term is scoped. *)
  Lemma term_in_children : forall p (o : L.op) es,
    term_in (P.variables p) (Node o es) -> Forall (term_in (P.variables p)) es.
  Proof.
    intros p o es. induction es as [|e es IH]; cbn [term_in]; intros Hscope.
    - constructor.
    - destruct Hscope as [Hhead Htail]. constructor; [exact Hhead|now apply IH].
  Qed.

  (** Checked refinement writes only the declared leaves of its cached term. *)
  Lemma refine_checked_inv : forall p e cached current q,
    term_in (P.variables p) e -> inv p (Reached current) ->
    inv p (Reached (fst (E.refine_checked q (E.annotate cached e) current))).
  Proof.
    intros p e. induction e as [x|o es IH]; intros cached current q Hscope Hcurrent.
    - rewrite E.annotate_leaf, E.F_refine_leaf. cbn [fst].
      apply inv_set; [exact Hcurrent|exact Hscope].
    - pose proof (term_in_children p o es Hscope) as Hchildren.
      rewrite E.annotate_node, E.F_refine_node, map_map.
      remember (V.backward o q (map (fun e => E.root (E.annotate cached e)) es))
        as requests.
      clear Heqrequests Hscope. revert IH current Hcurrent requests.
      generalize false as bad.
      induction Hchildren as [|e es Hhead Htail IHtail];
        intros bad IH current Hcurrent requests.
      + cbn [map fst]. exact Hcurrent.
      + inversion IH as [|e' IHe es' IHrest]; subst.
        destruct requests as [|request requests]; cbn [map fst]; [exact Hcurrent|].
        apply IHtail; [exact IHrest|]. apply IHe; assumption.
  Qed.

  (** Assignment adds only its declared destination to the stored support. *)
  Lemma inv_assign : forall p x e s, inv p s -> In x (P.variables p) ->
    inv p (E.assign x e s).
  Proof.
    intros p x e [|m] Hinv Hdeclared; rewrite E.F_assign; [constructor|].
    now apply inv_set.
  Qed.

  (** Havoc adds only its declared destination to the stored support. *)
  Lemma inv_havoc : forall p x s, inv p s -> In x (P.variables p) ->
    inv p (E.havoc x s).
  Proof.
    intros p x [|m] Hinv Hdeclared; rewrite E.F_havoc; [constructor|].
    now apply inv_set.
  Qed.

  (** Folding checked requests over scoped terms preserves the support invariant. *)
  Lemma refine_fold_inv : forall p cached es requests current bad,
    Forall (term_in (P.variables p)) es -> inv p (Reached current) ->
    inv p (Reached (fst (fold_left (fun result nq =>
      let next := E.refine_checked (snd nq) (fst nq) (fst result) in
      (fst next, orb (snd result) (snd next)))
      (combine (map (E.annotate cached) es) requests) (current, bad)))).
  Proof.
    intros p cached es requests current bad Hscope. revert requests current bad.
    induction Hscope as [|e es Hhead Htail IH]; intros requests current bad Hcurrent.
    - cbn [map combine fold_left fst]. exact Hcurrent.
    - destruct requests as [|request requests]; cbn [map combine fold_left fst snd];
        [exact Hcurrent|].
      apply IH. now apply refine_checked_inv.
  Qed.

  (** Assumption refinement preserves support even when it introduces previously absent leaves. *)
  Lemma inv_assume : forall p g es s, inv p s ->
    Forall (term_in (P.variables p)) es -> inv p (E.assume g es s).
  Proof.
    intros p g es [|m] Hinv Hscope; rewrite E.F_assume; [constructor|].
    cbn iota zeta.
    pose proof (refine_fold_inv p m es (V.guard g (map E.root (map (E.annotate m) es)))
      m false Hscope Hinv) as Hrefined.
    match goal with
    | |- inv _ (if ?bad then _ else _) => destruct bad
    end; [constructor|exact Hrefined].
  Qed.

  (** Every scoped instruction preserves the environment invariant. *)
  Lemma inv_instruction : forall p i s,
    P.scoped p i -> inv p s -> inv p (P.apply_instruction i s).
  Proof.
    intros p [x e|x|g es|] s Hscope Hinv; cbn [P.apply_instruction].
    - destruct Hscope as [Hdeclared Hterm]. now apply inv_assign.
    - now apply inv_havoc.
    - now apply inv_assume.
    - exact Hinv.
  Qed.

  (** Ordered scoped instructions preserve the invariant from their actual source state. *)
  Lemma inv_instructions : forall p instructions s,
    Forall (P.scoped p) instructions -> inv p s ->
    inv p (fold_left (fun s i => P.apply_instruction i s) instructions s).
  Proof.
    intros p instructions s Hscope. revert s.
    induction Hscope as [|i instructions Hi Hrest IH]; intros s Hinv.
    - exact Hinv.
    - cbn [fold_left]. apply IH. now apply inv_instruction.
  Qed.

  (** Scoped rows preserve the invariant on all contributions. *)
  Lemma inv_rows : forall p r look a ss, S.wf p -> In r (S.rows p) ->
    (forall x, inv p (look x)) -> S.eval p r look = Some (a, ss) ->
    inv p a /\ Forall (fun xa => inv p (snd xa)) ss.
  Proof.
    intros p r look a ss Hwf Hrow Hlook Heval.
    rewrite (P.row_execution p r look Hwf Hrow) in Heval.
    injection Heval as <- <-. split; [|constructor].
    pose proof (P.instruction_scoped p r Hwf Hrow) as Hscope.
    destruct (P.row_plan p r) as [[source instructions]|] in Hscope |- *.
    - now apply inv_instructions.
    - apply inv_top.
  Qed.

  (** The declared variables bound the size of a scoped environment. *)
  Lemma size_le : forall p a, inv p a -> E.size a <= vsize p.
  Proof. Admitted. (* STUB *)
  (** The declared variables bound the number of widening units. *)
  Lemma wunits_le : forall p a, inv p a -> E.wunits a <= wunits p.
  Proof. Admitted. (* STUB *)
  (** The declared variables and thresholds bound widening rank. *)
  Lemma wrank_le : forall p w a, inv p a -> E.wrank w a <= wmax p w.
  Proof. Admitted. (* STUB *)
End EnvIntBudget.
