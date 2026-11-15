(** * IDE micro-function path edges

    Rules compose symbolic functions along balanced paths.
    For example, a return combines the caller, call, callee and return functions.
    Builds on: Framework.IdeSig and Framework.Ifds. *)

From Stdlib Require Import List Bool NArith PArith Arith Lia.
From Argent Require Import Time Tactics Std Loop.
From Galois.Base Require Import KeySig Code.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import Query SystemSig.
From Galois.Program Require Import CfgSig IcfgSig.
From Galois.Framework Require Import IfdsSig Ifds IdeSig.

(** A fact path records the value obtained by applying each edge weight in order. *)
Inductive fact_value_path {E F A V}
    (flow : E -> F -> list F) (weight : E -> F -> F -> A) (apply : A -> V -> V)
    : F -> V -> list E -> F -> V -> Prop :=
  | FactValue_nil : forall x value,
      fact_value_path flow weight apply x value nil x value
  | FactValue_cons : forall e path x y z input output,
      In y (flow e x) ->
      fact_value_path flow weight apply y (apply (weight e x y) input) path z output ->
      fact_value_path flow weight apply x input (e :: path) z output.

(** An empty value path keeps its fact and value. *)
Lemma fact_value_path_nil {E F A V}
    (flow : E -> F -> list F) (weight : E -> F -> F -> A) (apply : A -> V -> V) :
  forall x input y output, fact_value_path flow weight apply x input nil y output ->
    x = y /\ input = output.
Proof.
  intros x input y output Hpath; inversion Hpath; now split.
Qed.

(** The first edge supplies the fact and value for the remaining path. *)
Lemma fact_value_path_cons {E F A V}
    (flow : E -> F -> list F) (weight : E -> F -> F -> A) (apply : A -> V -> V) :
  forall x input e path y output,
    fact_value_path flow weight apply x input (e :: path) y output ->
    exists z, In z (flow e x) /\
      fact_value_path flow weight apply z (apply (weight e x z) input) path y output.
Proof.
  intros x input e path y output Hpath; inversion Hpath; subst.
  eexists; split; eassumption.
Qed.

(** A one-edge value path applies exactly that edge's weight. *)
Lemma fact_value_path_single {E F A V}
    (flow : E -> F -> list F) (weight : E -> F -> F -> A) (apply : A -> V -> V) :
  forall x input e y output,
    fact_value_path flow weight apply x input (e :: nil) y output ->
    In y (flow e x) /\ output = apply (weight e x y) input.
Proof.
  intros x input e y output Hpath.
  destruct (fact_value_path_cons flow weight apply x input e nil y output Hpath)
    as [z [Hflow Htail]].
  destruct (fact_value_path_nil flow weight apply z _ y output Htail) as [-> <-].
  now split.
Qed.

(** A value path over a concatenation has a value at its intermediate fact. *)
Lemma fact_value_path_app {E F A V}
    (flow : E -> F -> list F) (weight : E -> F -> F -> A) (apply : A -> V -> V) :
  forall left right x input y output,
    fact_value_path flow weight apply x input (left ++ right) y output ->
    exists z middle,
      fact_value_path flow weight apply x input left z middle /\
      fact_value_path flow weight apply z middle right y output.
Proof.
  induction left as [|e left IH]; intros right x input y output Hpath.
  - exists x, input; split; [constructor|exact Hpath].
  - inversion Hpath as [|e' path' x' z' y' input' output' Hflow Hrest]; subst.
    destruct (IH right z' (apply (weight e x z') input) y output Hrest)
      as [z [middle [Hleft Hright]]].
    exists z, middle; split; [econstructor; eassumption|exact Hright].
Qed.

(** Every weighted fold result follows one input occurrence's value path. *)
Lemma weighted_fold_path {E F A V}
    (flow : E -> F -> list F) (weight : E -> F -> F -> A)
    (compose : A -> A -> A) (apply : A -> V -> V)
    (Hcompose : forall f g value, apply (compose f g) value = apply f (apply g value)) :
  forall path current d f,
    In (d, f) (fold_left (fun current e => flat_map (fun xf =>
      map (fun y => (y, compose (weight e (fst xf) y) (snd xf)))
        (flow e (fst xf))) current) path current) ->
    forall value, exists x prefix, In (x, prefix) current /\
      fact_value_path flow weight apply x (apply prefix value) path d (apply f value).
Proof.
  induction path as [|e path IH]; intros current d f Hin value.
  - exists d, f; split; [exact Hin|constructor].
  - cbn [fold_left] in Hin.
    destruct (IH _ d f Hin value) as [middle [g [Hstep Hpath]]].
    apply in_flat_map in Hstep; destruct Hstep as [[x prefix] [Hx Hstep]].
    cbn [fst snd] in Hstep.
    apply in_map_iff in Hstep; destruct Hstep as [y [Heq Hflow]].
    injection Heq as <- <-.
    exists x, prefix; split; [exact Hx|].
    rewrite Hcompose in Hpath; econstructor; eassumption.
Qed.

(** Applying a symbolic weighted result agrees with its stepwise value path. *)
Lemma weighted_facts_path {E F A V}
    (flow : E -> F -> list F) (weight : E -> F -> F -> A) (identity : A)
    (compose : A -> A -> A) (apply : A -> V -> V)
    (Hidentity : forall value, apply identity value = value)
    (Hcompose : forall f g value, apply (compose f g) value = apply f (apply g value)) :
  forall origin path d f,
    In (d, f) (weighted_facts flow weight identity compose origin path) ->
    forall value, fact_value_path flow weight apply origin value path d (apply f value).
Proof.
  intros origin path d f Hin value.
  destruct (weighted_fold_path flow weight compose apply Hcompose path
    ((origin, identity) :: nil) d f Hin value) as [x [prefix [Hstart Hpath]]].
  destruct Hstart as [Hstart|[]]; injection Hstart as <- <-.
  now rewrite Hidentity in Hpath.
Qed.

Module IdeCode (P : TYPE) (N : KEY_OPS) (E : TYPE) (C : CFG_OPS P N E)
    (Site : KEY_OPS) (I : ICFG_OPS P N E C Site) (F : KEY_OPS)
    (V : LATTICE_OPS) (M : MICRO_OPS V) (FL : IDE_FLOW_OPS P N E F V M)
    (R : IFDS_RULES_OPS P N E F)
    <: IDE_OPS P N E F V M.
  Definition prog := P.t.
  Definition key := path_edge N.t F.t.
  Definition row := path_row N.t E.t F.t.
  Definition frame := path_frame N.t E.t F.t M.t.
  Definition key_code := path_edge_code N.encode F.encode.
  Definition key_eqb (x y : key) :=
    F.eqb (fst x) (fst y) && N.eqb (fst (snd x)) (fst (snd y)) &&
      F.eqb (snd (snd x)) (snd (snd y)).
  Definition rows p : list row := path_number 1%positive
    (R.rules p).
  Definition target p (r : row) : key := match path_row_rule r with
    | PathIdentity n d => (d, (n, d))
    | PathStep d0 e _ y => (d0, (C.dst p e, y))
    | PathReturn d0 _ ret _ _ _ y => (d0, (C.dst p ret, y))
    end.
  Definition deps p (r : row) : list key := match path_row_rule r with
    | PathIdentity _ _ => nil
    | PathStep d0 e x _ => (d0, (C.src p e, x)) :: nil
    | PathReturn d0 call ret x a b _ =>
        (d0, (C.src p call, x)) :: (a, (C.src p ret, b)) :: nil
    end.
  Definition sides (_ : prog) (_ : row) : list key := nil.
  Definition finish p (r : path_rule N.t E.t F.t) (xs : list M.t) : M.t :=
    match r, xs with
    | PathIdentity _ _, _ => M.identity
    | PathStep _ e x y, a :: _ => M.compose (FL.weight p e x y) a
    | PathReturn _ call ret x a b y, caller :: callee :: _ =>
        M.compose (FL.weight p ret b y)
          (M.compose callee (M.compose (FL.weight p call x a) caller))
    | _, _ => M.bot
    end.
  Definition start p (r : row) : query key M.t frame :=
    path_query (finish p) (path_row_rule r) (deps p r) nil.
  Definition resume p (f : frame) (a : M.t) : query key M.t frame :=
    match f with
    | PathFrame _ _ _ _ rule pending received => path_query (finish p) rule pending (a :: received)
    end.
End IdeCode.

Module Ide (P : TYPE) (N : KEY) (E : TYPE) (C : CFG P N E)
    (Site : KEY) (I : ICFG P N E C Site) (F : KEY) (V : LATTICE) (M : MICRO V)
    (FL : IDE_FLOW P N E C F V M) (R : IFDS_RULES P N E C Site I F FL) <: IDE P N E C Site I F V M FL.
  Include IdeCode P N E C Site I F V M FL R.
  Include SYSTEM_SPEC M.
  Definition wf (p : prog) := R.wf p.
  (** Codes distinguish all system keys. *)
  Lemma key_code_inj : forall a b, key_code a = key_code b -> a = b.
  Proof.
    intros [d [n x]] [d' [n' x']] Hcode.
    unfold key_code, path_edge_code, pair_code in Hcode; cbn [fst snd] in Hcode.
    destruct (glue_inj _ _ _ _ Hcode) as [Hd Hrest].
    destruct (glue_inj _ _ _ _ Hrest) as [Hn Hx].
    apply F.encode_inj in Hd; apply N.encode_inj in Hn; apply F.encode_inj in Hx.
    now subst.
  Qed.
  (** Key equality decides equality of system keys. *)
  Lemma key_eqb_spec : forall a b, reflect (a = b) (key_eqb a b).
  Proof.
    intros [d [n x]] [d' [n' x']].
    unfold key_eqb; cbn [fst snd].
    destruct (F.eqb_spec d d'), (N.eqb_spec n n'), (F.eqb_spec x x');
      cbn [andb]; constructor; congruence.
  Qed.
  (** Matched returns compose caller, call, callee and return effects in that order. *)
  Lemma eval_spec : forall p r look, eval p r look = Some
    (match path_row_rule r with
     | PathIdentity _ _ => M.identity
     | PathStep d0 e x y => M.compose (FL.weight p e x y) (look (d0, (C.src p e, x)))
     | PathReturn d0 call ret x a b y => M.compose (FL.weight p ret b y)
         (M.compose (look (a, (C.src p ret, b)))
           (M.compose (FL.weight p call x a) (look (d0, (C.src p call, x)))))
     end, nil).
  Proof.
    intros p [code rule] look; destruct rule; reflexivity.
  Qed.
  (** Declared rows finish within their dependency-derived fuel. *)
  Lemma eval_total : forall p r look,
    wf p -> In r (rows p) -> eval p r look <> None.
  Proof.
    intros p r look _ _; rewrite eval_spec; discriminate.
  Qed.
  (** A row observes its declared dependencies. *)
  Lemma reads_within : forall p r s u, wf p -> In r (rows p) ->
    (forall x, In x (deps p r) -> s x = u x) -> eval p r s = eval p r u.
  Proof.
    intros p [code rule] s u _ _ Hagree.
    rewrite !eval_spec; destruct rule; cbn [path_row_rule] in *.
    - reflexivity.
    - rewrite (Hagree _ (or_introl eq_refl)); reflexivity.
    - rewrite (Hagree _ (or_introl eq_refl)),
        (Hagree _ (or_intror (or_introl eq_refl))); reflexivity.
  Qed.

  (** A continuing path query only asks keys still present in its input list. *)
  Lemma path_query_asks : forall p look n rule pending received q acc x f,
    loop_fuel (eval_step (resume p) look) n
      (path_query (finish p) rule pending received, nil) = inl (q, acc) ->
    fst (peel q acc) = inr (x, f) -> In x pending.
  Proof.
    intros p look n; induction n as [|n IH];
      intros rule pending received q acc x f Hloop Hask.
    - cbn [loop_fuel] in Hloop; injection Hloop as <- <-.
      destruct pending as [|y pending]; cbn [path_query peel fst] in Hask.
      + discriminate.
      + injection Hask as <- <-; now left.
    - destruct pending as [|y pending];
        cbn [loop_fuel path_query eval_step peel resume fst snd] in Hloop.
      + discriminate.
      + right; eapply IH; eassumption.
  Qed.
  (** A row asks only its declared dependencies. *)
  Lemma asks_within : forall p r look n q acc x f, wf p -> In r (rows p) ->
    loop_fuel (eval_step (resume p) look) n (start p r, nil) = inl (q, acc) ->
    fst (peel q acc) = inr (x, f) -> In x (deps p r).
  Proof.
    intros p r look n q acc x f _ _ Hloop Hask.
    eapply path_query_asks; eassumption.
  Qed.
  (** Side contributions use declared side keys. *)
  Lemma sides_within : forall p r look a ss x b, wf p -> In r (rows p) ->
    eval p r look = Some (a, ss) -> In (x, b) ss -> In x (sides p r).
  Proof.
    intros p r look a ss x b _ _ Heval Hin.
    rewrite eval_spec in Heval; injection Heval as <- <-; contradiction.
  Qed.
  (** Side contributions fit the declared occurrence budget. *)
  Lemma sides_count : forall p r look a ss, wf p -> In r (rows p) ->
    eval p r look = Some (a, ss) -> length ss <= length (sides p r).
  Proof.
    intros p r look a ss _ _ Heval.
    rewrite eval_spec in Heval; injection Heval as <- <-; reflexivity.
  Qed.
  Include IDE_RULE_SPEC P N E C Site I F V M FL.
  (** The path-edge encoding retains all three components. *)
  Lemma key_code_spec : key_code = path_edge_code N.encode F.encode.
  Proof.
    reflexivity.
  Qed.
  (** Rows contain exactly the enabled finite rules. *)
  Lemma rows_spec : forall p rule, wf p ->
    (exists r, In r (rows p) /\ path_row_rule r = rule) <-> enabled p rule.
  Proof.
    intros p rule Hwf; unfold rows, enabled.
    rewrite <- (R.rules_enabled p rule Hwf).
    split.
    - intros [r [Hin Hrule]]; rewrite <- Hrule.
      rewrite <- (path_number_rules 1%positive (R.rules p)).
      apply in_map; exact Hin.
    - intro Hin.
      assert (Hmap : In rule (map path_row_rule (path_number 1%positive (R.rules p)))).
      { now rewrite path_number_rules. }
      apply in_map_iff in Hmap; destruct Hmap as [r [Hrule Hr]].
      exists r; now split.
  Qed.
  (** Every rule writes its destination path edge. *)
  Lemma target_spec : forall p r, target p r =
    match path_row_rule r with
    | PathIdentity n d => (d, (n, d))
    | PathStep d0 e _ y => (d0, (C.dst p e, y))
    | PathReturn d0 _ ret _ _ _ y => (d0, (C.dst p ret, y))
    end.
  Proof.
    reflexivity.
  Qed.
End Ide.

Module IdeT (P : TYPE) (N : KEY_T) (E : KEY_T) (C : CFG_T P N E)
    (Site : KEY_T) (I : ICFG_T P N E C Site) (F : KEY_T)
    (V : LATTICE_T) (M : MICRO_T V) (FL : IDE_FLOW_T P N E C F V M)
    (R : IFDS_RULES_T P N E C Site I F FL)
    <: IDE_T P N E C Site I F V M FL.
  Include Ide P N E C Site I F V M FL R.

  TimeFun key_code.
  TimeFun key_eqb.
  TimeFun rows.
  TimeFun target.
  TimeFun deps.
  TimeFun sides.
  TimeFun finish.
  TimeFun start.
  TimeFun resume.
  Definition row_work p s :=
    (3 * (M.c_micro + 1) ^ 3 * N.of_nat (FL.weight_work p + s + 1) +
      N.of_nat (length (rows p) + M.size M.identity + M.size M.bot))%N.
  Definition path_kw (p : prog) : nat := fold_right Nat.max 0
    (flat_map (fun r => map key_bits (writes p r ++ deps p r)) (rows p)).
  Definition kw := path_kw.
  Definition c_sys : N := 1%N. (* STUB *)
  Lemma row_work_mono : forall p s t, s <= t ->
    (row_work p s <= row_work p t)%N.
  Proof. Admitted. (* STUB *)
  Lemma key_bits_le : forall p r x, wf p -> In r (rows p) ->
    In x (writes p r ++ deps p r) -> key_bits x <= kw p.
  Proof. Admitted. (* STUB *)
  Lemma T_key_code_le : forall x,
    (T_key_code x <= c_sys * N.of_nat (key_bits x + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_key_eqb_le : forall a b,
    (T_key_eqb a b <= c_sys * N.of_nat (key_bits a + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_rows_le : forall p, wf p ->
    (T_rows p <= c_sys * N.of_nat (length (rows p) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_target_le : forall p r, wf p -> In r (rows p) ->
    (T_target p r <= c_sys * (row_work p 0 + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_start_le : forall p r, wf p -> In r (rows p) ->
    (T_start p r <= c_sys * (row_work p 0 + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_resume_le : forall p r look s n q acc x f, wf p -> In r (rows p) ->
    (forall y, M.size (look y) <= s) ->
    loop_fuel (eval_step (resume p) look) n (start p r, nil) = inl (q, acc) ->
    fst (peel q acc) = inr (x, f) ->
    (T_resume p f (look x) <= c_sys * (row_work p s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_deps_le : forall p r, wf p -> In r (rows p) ->
    (T_deps p r <= c_sys * N.of_nat (length (deps p r) + 1) *
      N.of_nat (kw p + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_sides_le : forall p r, wf p -> In r (rows p) ->
    (T_sides p r <= c_sys * N.of_nat (length (sides p r) + 1) *
      N.of_nat (kw p + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma eval_size_le : forall p r look s a ss, wf p -> In r (rows p) ->
    (forall x, M.size (look x) <= s) -> eval p r look = Some (a, ss) ->
    (N.of_nat (M.size a) <= row_work p s)%N /\
    Forall (fun xb => (N.of_nat (M.size (snd xb)) <= row_work p s)%N) ss.
  Proof. Admitted. (* STUB *)
End IdeT.

Module IdeSound (P : TYPE) (N : KEY) (E : TYPE) (C : CFG P N E)
    (Site : KEY) (I : ICFG P N E C Site) (F : KEY) (V : LATTICE) (M : MICRO V)
    (FL : IDE_FLOW P N E C F V M) (A : IDE P N E C Site I F V M FL)
    <: IDE_SOUND P N E C Site I F V M FL A.
  (** A post-solution bounds the symbolic result of each enabled rule. *)
  Lemma enabled_bound : forall p look, A.wf p -> A.post_solution p look ->
    forall rule, A.enabled p rule ->
      M.leb
        (match rule with
         | PathIdentity _ _ => M.identity
         | PathStep d0 e x y => M.compose (FL.weight p e x y) (look (d0, (C.src p e, x)))
         | PathReturn d0 call ret x a b y => M.compose (FL.weight p ret b y)
             (M.compose (look (a, (C.src p ret, b)))
               (M.compose (FL.weight p call x a) (look (d0, (C.src p call, x)))))
         end)
        (look (match rule with
         | PathIdentity n d => (d, (n, d))
         | PathStep d0 e _ y => (d0, (C.dst p e, y))
         | PathReturn d0 _ ret _ _ _ y => (d0, (C.dst p ret, y))
         end)) = true.
  Proof.
    intros p look Hwf Hpost rule Henabled.
    destruct (proj2 (A.rows_spec p rule Hwf) Henabled) as [r [Hin Hrule]].
    pose proof (Hpost r Hin) as Hrow.
    rewrite A.eval_spec, A.target_spec, Hrule in Hrow.
    cbn [row_ok] in Hrow; now apply andb_prop in Hrow as [Hbound _].
  Qed.

  (** Every supported call input is covered by its callee's identity summary. *)
  Lemma call_identity : forall p look, A.wf p -> A.post_solution p look ->
    forall call site x a, In call (C.edges p) -> I.kind p call = Call site ->
      In x (FL.facts p) -> In a (FL.flow p call x) ->
      forall value, V.leb value (M.apply (look (a, (C.dst p call, a))) value) = true.
  Proof.
    intros p look Hwf Hpost call site x a Hcall Hkind Hx Ha value.
    assert (Hidentity : M.leb M.identity (look (a, (C.dst p call, a))) = true).
    { apply (enabled_bound p look Hwf Hpost (PathIdentity (C.dst p call) a)).
      right; exists call, site, x; repeat split; assumption || reflexivity. }
    pose proof (M.apply_mono _ _ value Hidentity) as Hbound.
    now rewrite M.apply_identity in Hbound.
  Qed.

  (** An internal rule propagates any value covered at its source. *)
  Lemma step_bound : forall p look, A.wf p -> A.post_solution p look ->
    forall d0 e x y input initial,
      In d0 (FL.facts p) -> In e (C.edges p) ->
      (I.kind p e = Intra \/ exists site, I.kind p e = CallToReturn site) ->
      In x (FL.facts p) -> In y (FL.flow p e x) ->
      V.leb input (M.apply (look (d0, (C.src p e, x))) initial) = true ->
      V.leb (M.apply (FL.weight p e x y) input)
        (M.apply (look (d0, (C.dst p e, y))) initial) = true.
  Proof.
    intros p look Hwf Hpost d0 e x y input initial Hd0 He Hkind Hx Hy Hinput.
    assert (Hrule : A.enabled p (PathStep d0 e x y)).
    { split; [exact Hd0|]. split; [exact He|]. split; [exact Hkind|]. now split. }
    pose proof (M.apply_mono _ _ initial
      (enabled_bound p look Hwf Hpost (PathStep d0 e x y) Hrule)) as Hrow.
    rewrite M.apply_compose in Hrow.
    eapply V.leb_trans; [apply M.value_mono; exact Hinput|exact Hrow].
  Qed.

  (** A return propagates the caller and callee bounds in execution order. *)
  Lemma return_bound : forall p look, A.wf p -> A.post_solution p look ->
    forall d0 call ret site x a b y input middle initial,
      In d0 (FL.facts p) -> In call (C.edges p) -> In ret (C.edges p) ->
      I.kind p call = Call site -> I.kind p ret = Return site ->
      In x (FL.facts p) -> In a (FL.flow p call x) -> In b (FL.facts p) ->
      In y (FL.flow p ret b) ->
      V.leb input (M.apply (look (d0, (C.src p call, x))) initial) = true ->
      V.leb middle
        (M.apply (look (a, (C.src p ret, b))) (M.apply (FL.weight p call x a) input)) = true ->
      V.leb (M.apply (FL.weight p ret b y) middle)
        (M.apply (look (d0, (C.dst p ret, y))) initial) = true.
  Proof.
    intros p look Hwf Hpost d0 call ret site x a b y input middle initial
      Hd0 Hcall Hret Hcall_kind Hret_kind Hx Ha Hb Hy Hcaller Hcallee.
    assert (Hrule : A.enabled p (PathReturn d0 call ret x a b y)).
    { split; [exact Hd0|]. split; [exact Hcall|]. split; [exact Hret|].
      split; [exists site; now split|].
      split; [exact Hx|]. split; [exact Ha|]. now split. }
    pose proof (M.apply_mono _ _ initial
      (enabled_bound p look Hwf Hpost (PathReturn d0 call ret x a b y) Hrule)) as Hrow.
    rewrite !M.apply_compose in Hrow.
    eapply V.leb_trans; [|exact Hrow].
    apply M.value_mono.
    eapply V.leb_trans; [exact Hcallee|].
    apply M.value_mono, M.value_mono; exact Hcaller.
  Qed.

  (** Balanced value paths stay below the symbolic summary at their endpoint. *)
  Lemma path_propagates : forall p look, A.wf p -> A.post_solution p look ->
    forall n path m,
      valid_path (C.edges p) (C.src p) (C.dst p) (I.kind p) n path m ->
      forall d0 x y input output initial,
        In d0 (FL.facts p) -> In x (FL.facts p) ->
        V.leb input (M.apply (look (d0, (n, x))) initial) = true ->
        fact_value_path (FL.flow p) (FL.weight p) M.apply x input path y output ->
        In y (FL.facts p) /\
          V.leb output (M.apply (look (d0, (m, y))) initial) = true.
  Proof.
    intros p look Hwf Hpost n path m Hpath.
    induction Hpath as [n|e He Hkind|n m t left right Hleft IHleft Hright IHright|
      call ret site inside Hcall Hret Hcall_kind Hret_kind Hinside IHinside];
      intros d0 x y input output initial Hd0 Hx Hinput Hvalues.
    - destruct (fact_value_path_nil _ _ _ _ _ _ _ Hvalues) as [<- <-]; now split.
    - destruct (fact_value_path_single _ _ _ _ _ _ _ _ Hvalues) as [Hy ->]; split.
      + eapply FL.flow_closed; eassumption.
      + exact (step_bound p look Hwf Hpost d0 e x y input initial
          Hd0 He Hkind Hx Hy Hinput).
    - destruct (fact_value_path_app _ _ _ left right x input y output Hvalues)
        as [z [middle [Hvalues_left Hvalues_right]]].
      destruct (IHleft d0 x z input middle initial Hd0 Hx Hinput Hvalues_left)
        as [Hz Hmiddle].
      exact (IHright d0 z y middle output initial Hd0 Hz Hmiddle Hvalues_right).
    - destruct (fact_value_path_cons _ _ _ _ _ _ _ _ _ Hvalues) as [a [Ha Hrest]].
      destruct (fact_value_path_app _ _ _ inside (ret :: nil) a _ y output Hrest)
        as [b [middle [Hinner Hreturn]]].
      destruct (fact_value_path_single _ _ _ _ _ _ _ _ Hreturn) as [Hy ->].
      pose proof (FL.flow_closed p call x a Hcall Hx Ha) as Ha_supported.
      pose proof (call_identity p look Hwf Hpost call site x a Hcall
        Hcall_kind Hx Ha (M.apply (FL.weight p call x a) input)) as Ha_bound.
      destruct (IHinside a a b _ middle _ Ha_supported Ha_supported Ha_bound Hinner)
        as [Hb Hmiddle].
      split.
      + eapply FL.flow_closed; eassumption.
      + exact (return_bound p look Hwf Hpost d0 call ret site x a b y input middle initial
          Hd0 Hcall Hret Hcall_kind Hret_kind Hx Ha Hb Hy Hinput Hmiddle).
  Qed.

  (** Weighted balanced paths are pointwise below every symbolic post-solution. *)
  Lemma covers : forall p look, A.wf p -> A.post_solution p look ->
    forall entry d0 n path d f, In (entry, d0) (FL.seeds p) ->
      valid_path (C.edges p) (C.src p) (C.dst p) (I.kind p) entry path n ->
      In (d, f) (weighted_facts (FL.flow p) (FL.weight p) M.identity M.compose d0 path) ->
      forall a, V.leb (M.apply f a) (M.apply (look (d0, (n, d))) a) = true.
  Proof.
    intros p look Hwf Hpost entry d0 n path d f Hseed Hpath Hweighted value.
    pose proof (FL.seeds_facts p entry d0 Hseed) as Hd0.
    assert (Hidentity : M.leb M.identity (look (d0, (entry, d0))) = true).
    { apply (enabled_bound p look Hwf Hpost (PathIdentity entry d0)); now left. }
    pose proof (M.apply_mono _ _ value Hidentity) as Hstart.
    rewrite M.apply_identity in Hstart.
    pose proof (weighted_facts_path (FL.flow p) (FL.weight p) M.identity M.compose M.apply
      M.apply_identity M.apply_compose d0 path d f Hweighted value) as Hvalues.
    exact (proj2 (path_propagates p look Hwf Hpost entry path n Hpath
      d0 d0 d value (M.apply f value) value Hd0 Hd0 Hstart Hvalues)).
  Qed.
End IdeSound.
