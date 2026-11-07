(** * Nested-loop reference rule firing

    Positive atoms extend bindings in source order before negative literals are tested.
    For example, repeated variables require equal tuple components.
    Builds on: DatalogSyntax, DatalogRelation, CostList and BaseEq. *)

From Stdlib Require Import List Bool PeanoNat PArith NArith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseEq BaseSet.
From Galois.Lattice Require Import LatticeSet.
From Galois.Datalog Require Import DatalogSyntax DatalogRelation.
Import List.ListNotations Cost.Notations.
Local Open Scope nat_scope.

(** Bindings are finite partial valuations with first-match lookup. *)
Definition binding := list (nat * positive).

Fixpoint binding_get_c (b : binding) v : Cost.t (option positive) :=
  match b with
  | [] => Cost.ret None
  | (w, c) :: rest =>
    Cost.step ;;
    if Nat.eqb v w then Cost.ret (Some c) else binding_get_c rest v
  end.

Definition binding_get b v := Cost.value (binding_get_c b v).

Lemma binding_get_equation b v :
  binding_get b v =
  match b with
  | [] => None
  | (w, c) :: rest => if Nat.eqb v w then Some c else binding_get rest v
  end.
Proof.
  destruct b as [|[w c] rest]; [reflexivity |].
  cbn [binding_get_c]; unfold binding_get at 1; cbn [binding_get_c].
  rewrite Cost.value_bind; destruct (Nat.eqb v w); reflexivity.
Qed.

Definition binding_value_c b v := Cost.map
  (fun x => match x with Some c => c | None => 1%positive end) (binding_get_c b v).
Definition binding_value b v := Cost.value (binding_value_c b v).

(** Agreement fixes every variable already assigned by the partial valuation. *)
Definition binding_agrees b (sigma : nat -> positive) :=
  forall v c, binding_get b v = Some c -> sigma v = c.

Definition binding_extends b b' :=
  forall v c, binding_get b v = Some c -> binding_get b' v = Some c.

Lemma binding_value_agrees b : binding_agrees b (binding_value b).
Proof.
  intros v c Hget; unfold binding_value, binding_value_c; rewrite Cost.value_map.
  change ((match binding_get b v with Some d => d | None => 1%positive end) = c).
  rewrite Hget; reflexivity.
Qed.

Lemma binding_agrees_extends b b' sigma :
  binding_extends b b' -> binding_agrees b' sigma -> binding_agrees b sigma.
Proof.
  intros Hext Hagree v c Hget; apply Hagree, Hext, Hget.
Qed.

Lemma binding_extends_trans b b' b'' :
  binding_extends b b' -> binding_extends b' b'' -> binding_extends b b''.
Proof.
  intros Hleft Hright v c Hget; apply Hright, Hleft, Hget.
Qed.

Lemma binding_cons_extends b v c : binding_get b v = None ->
  binding_extends b ((v, c) :: b).
Proof.
  intros Hnone w d Hget; rewrite binding_get_equation.
  destruct (Nat.eqb w v) eqn:Heq; [|exact Hget].
  apply Nat.eqb_eq in Heq; subst w; congruence.
Qed.

Lemma binding_cons_agrees b sigma v c : binding_agrees b sigma -> sigma v = c ->
  binding_agrees ((v, c) :: b) sigma.
Proof.
  intros Hagree Hvalue w d Hget; rewrite binding_get_equation in Hget.
  destruct (Nat.eqb w v) eqn:Heq.
  - apply Nat.eqb_eq in Heq; subst w; injection Hget as <-; exact Hvalue.
  - apply Hagree, Hget.
Qed.

Definition bind_term_c b t c : Cost.t (option binding) :=
  Cost.step ;;
  match t with
  | TConst d =>
    let* same := positive_eqb_c c d in Cost.ret (if same then Some b else None)
  | TVar v =>
    let* old := binding_get_c b v in
    match old with
    | Some d =>
      let* same := positive_eqb_c c d in Cost.ret (if same then Some b else None)
    | None => Cost.ret (Some ((v, c) :: b))
    end
  end.

Definition bind_term b t c := Cost.value (bind_term_c b t c).

Lemma bind_term_equation b t c :
  bind_term b t c =
  match t with
  | TConst d => if Pos.eqb c d then Some b else None
  | TVar v =>
    match binding_get b v with
    | Some d => if Pos.eqb c d then Some b else None
    | None => Some ((v, c) :: b)
    end
  end.
Proof.
  unfold bind_term, bind_term_c; rewrite Cost.value_bind.
  destruct t as [v | d]; autorewrite with galois_cost.
  - fold (binding_get b v); destruct (binding_get b v) as [d |]; [|reflexivity].
    autorewrite with galois_cost; rewrite positive_eqb_equation; reflexivity.
  - rewrite positive_eqb_equation; reflexivity.
Qed.

Fixpoint bind_terms_c ts cs b : Cost.t (option binding) :=
  Cost.step ;;
  match ts, cs with
  | [], [] => Cost.ret (Some b)
  | t :: ts', c :: cs' =>
    let* next := bind_term_c b t c in
    match next with
    | Some b' => bind_terms_c ts' cs' b'
    | None => Cost.ret None
    end
  | _, _ => Cost.ret None
  end.

Definition bind_terms ts cs b := Cost.value (bind_terms_c ts cs b).

Lemma bind_terms_equation ts cs b :
  bind_terms ts cs b =
  match ts, cs with
  | [], [] => Some b
  | t :: ts', c :: cs' =>
    match bind_term b t c with
    | Some b' => bind_terms ts' cs' b'
    | None => None
    end
  | _, _ => None
  end.
Proof.
  destruct ts as [|t ts], cs as [|c cs]; try reflexivity.
  unfold bind_terms at 1; cbn [bind_terms_c]; autorewrite with galois_cost.
  fold (bind_term b t c); destruct (bind_term b t c); reflexivity.
Qed.

Lemma bind_term_sound b t c b' : bind_term b t c = Some b' ->
  binding_extends b b' /\
  (forall sigma, binding_agrees b' sigma -> inst sigma t = c) /\
  (forall v, t = TVar v -> exists d, binding_get b' v = Some d).
Proof.
  rewrite bind_term_equation; destruct t as [v | d].
  - destruct (binding_get b v) as [d |] eqn:Hget.
    + destruct (Pos.eqb c d) eqn:Heq; [|discriminate].
      apply Pos.eqb_eq in Heq; subst d; intro Hsome; injection Hsome as <-.
      split; [intros w d Hwd; exact Hwd | split].
      * intros sigma Hagree; apply Hagree, Hget.
      * intros w Heq; injection Heq as <-; exists c; exact Hget.
    + intro Hsome; injection Hsome as <-; split.
      * apply binding_cons_extends, Hget.
      * split.
        -- intros sigma Hagree; apply Hagree; rewrite binding_get_equation, Nat.eqb_refl.
           reflexivity.
        -- intros w Heq; injection Heq as <-; exists c.
           rewrite binding_get_equation, Nat.eqb_refl; reflexivity.
  - destruct (Pos.eqb c d) eqn:Heq; [|discriminate].
    apply Pos.eqb_eq in Heq; subst d; intro Hsome; injection Hsome as <-.
    split; [intros w d Hwd; exact Hwd | split].
    + intros sigma _; reflexivity.
    + intros v Hbad; discriminate.
Qed.

Lemma bind_term_complete b t sigma : binding_agrees b sigma ->
  exists b', bind_term b t (inst sigma t) = Some b' /\ binding_agrees b' sigma.
Proof.
  intro Hagree; rewrite bind_term_equation; destruct t as [v | c]; cbn [inst].
  - destruct (binding_get b v) as [d |] eqn:Hget.
    + rewrite (Hagree v d Hget), Pos.eqb_refl; exists b; auto.
    + eexists; split; [reflexivity | apply binding_cons_agrees; [exact Hagree | reflexivity]].
  - rewrite Pos.eqb_refl; exists b; auto.
Qed.

Lemma bind_terms_sound ts cs b b' : bind_terms ts cs b = Some b' ->
  binding_extends b b' /\
  (forall sigma, binding_agrees b' sigma -> cs = map (inst sigma) ts) /\
  (forall v, In (TVar v) ts -> exists d, binding_get b' v = Some d).
Proof.
  revert cs b b'; induction ts as [|t ts IH]; intros [|c cs] b b';
    rewrite bind_terms_equation; try discriminate.
  - intro Hsome; injection Hsome as <-; split.
    + intros v d Hget; exact Hget.
    + split; [intros sigma _; reflexivity | intros v Hbad; contradiction].
  - destruct (bind_term b t c) as [b1 |] eqn:Hterm; [|discriminate].
    intro Hrest; destruct (bind_term_sound b t c b1 Hterm) as [Hext [Hvalue Hbound]].
    destruct (IH cs b1 b' Hrest) as [Hrestext [Hvalues Hbounds]].
    split; [eapply binding_extends_trans; eassumption | split].
    + intros sigma Hagree; cbn [map]; f_equal.
      * symmetry; apply Hvalue; eapply binding_agrees_extends; eassumption.
      * apply Hvalues, Hagree.
    + intros v [Heq | Hin].
      * destruct (Hbound v Heq) as [d Hget]; exists d; apply Hrestext, Hget.
      * apply Hbounds, Hin.
Qed.

Lemma bind_terms_complete ts b sigma : binding_agrees b sigma ->
  exists b', bind_terms ts (map (inst sigma) ts) b = Some b' /\ binding_agrees b' sigma.
Proof.
  revert b; induction ts as [|t ts IH]; intros b Hagree; rewrite bind_terms_equation.
  - exists b; auto.
  - cbn [map].
    destruct (bind_term_complete b t sigma Hagree) as [b1 [Hterm Hagree1]].
    rewrite Hterm; apply IH, Hagree1.
Qed.

Definition instantiate_c b ts :=
  map_c (fun t =>
    match t with
    | TVar v => binding_value_c b v
    | TConst c => Cost.ret c
    end) ts.

Lemma instantiate_equation b ts :
  Cost.value (instantiate_c b ts) = map (inst (binding_value b)) ts.
Proof.
  unfold instantiate_c; rewrite value_map_c; apply map_ext.
  intros [v | c]; reflexivity.
Qed.

Lemma inst_agrees_on_bound ts b sigma : binding_agrees b sigma ->
  (forall v, In (TVar v) ts -> exists d, binding_get b v = Some d) ->
  map (inst (binding_value b)) ts = map (inst sigma) ts.
Proof.
  intros Hagree Hbound; apply map_ext_in; intros [v | c] Hin; [|reflexivity].
  destruct (Hbound v Hin) as [d Hget].
  change (binding_value b v = sigma v).
  unfold binding_value, binding_value_c; rewrite Cost.value_map.
  change ((match binding_get b v with Some c => c | None => 1%positive end) = sigma v).
  rewrite Hget; symmetry; apply Hagree, Hget.
Qed.

Definition positive_atoms_c {P} (ls : list (literal P)) :=
  filter_map_c (fun l => Cost.ret
    (match l with LPos a => Some a | LNeg _ => None end)) ls.

Definition positive_atoms {P} ls := Cost.value (@positive_atoms_c P ls).

Lemma positive_atoms_spec {P} (ls : list (literal P)) a :
  In a (positive_atoms ls) <-> In (LPos a) ls.
Proof.
  unfold positive_atoms, positive_atoms_c; rewrite value_filter_map_c.
  change (In a (filter_map (fun l : literal P =>
    match l with LPos b => Some b | LNeg _ => None end) ls) <-> In (LPos a) ls).
  induction ls as [|[b | b] ls IH]; cbn [filter_map fold_right In].
  - tauto.
  - rewrite IH; intuition congruence.
  - rewrite IH; intuition discriminate.
Qed.

(** One atom probes every row for every input binding without an index. *)
Definition join_atom_c {P} (a : atom P) (env : P -> Cost.t relation) bs :=
  Cost.step ;;
  let* rows := env (pred a) in
  let* tuples := FinSet.elements_c (set_raw rows) in
  fold_right_c (fun b acc =>
    let* matches := filter_map_c (fun cs => bind_terms_c (args a) cs b) tuples in
    app_c matches acc) [] bs.

Definition join_atom {P} a env bs := Cost.value (@join_atom_c P a env bs).

Lemma in_filter_map {A B} (f : A -> option B) xs y :
  In y (filter_map f xs) <-> exists x, In x xs /\ f x = Some y.
Proof.
  induction xs as [|x xs IH]; cbn [filter_map fold_right].
  - split; [contradiction | intros [x [Hbad _]]; contradiction].
  - destruct (f x) as [b |] eqn:Hx; cbn [In]; rewrite IH; split.
    + intros [<- | [a [Ha Hf]]].
      * exists x; auto.
      * exists a; auto.
    + intros [a [[<- | Ha] Hf]].
      * rewrite Hx in Hf; injection Hf as <-; now left.
      * right; exists a; auto.
    + intros [a [Ha Hf]]; exists a; auto.
    + intros [a [[<- | Ha] Hf]]; [congruence | exists a; auto].
Qed.

Lemma join_atom_members {P} (a : atom P) env bs b' :
  In b' (join_atom a env bs) <->
  exists b cs, In b bs /\
    FinSet.mem tuple_encoding cs (set_raw (Cost.value (env (pred a)))) = true /\
    bind_terms (args a) cs b = Some b'.
Proof.
  unfold join_atom, join_atom_c; repeat rewrite Cost.value_bind.
  rewrite value_fold_right_c.
  assert (Heq : forall xs : list binding,
    fold_right (fun b acc => Cost.value
      (let* matches := filter_map_c (fun cs => bind_terms_c (args a) cs b)
        (FinSet.elements (set_raw (Cost.value (env (pred a))))) in app_c matches acc)) [] xs =
    flat_map (fun b => filter_map (fun cs => bind_terms (args a) cs b)
      (FinSet.elements (set_raw (Cost.value (env (pred a)))))) xs).
  { intro xs; induction xs as [|b xs IH]; cbn [fold_right flat_map]; [reflexivity |].
    rewrite Cost.value_bind, value_app_c, value_filter_map_c, IH; reflexivity. }
  rewrite Heq, in_flat_map; split.
  - intros [b [Hb Hin]].
    apply in_filter_map in Hin as [cs [Hcs Hbind]].
    exists b, cs; repeat split; try assumption.
    apply (FinSet.elements_spec tuple_encoding tuple_encoding_laws), Hcs.
    apply (proj2_sig (Cost.value (env (pred a)))).
  - intros [b [cs [Hb [Hcs Hbind]]]]; exists b; split; [exact Hb |].
    apply in_filter_map; exists cs; split; [|exact Hbind].
    apply (FinSet.elements_spec tuple_encoding tuple_encoding_laws cs _
      (proj2_sig (Cost.value (env (pred a))))), Hcs.
Qed.

Fixpoint join_positive_c {P} (ps : list (atom P)) env bs : Cost.t (list binding) :=
  match ps with
  | [] => Cost.ret bs
  | a :: rest =>
    Cost.step ;;
    let* next := join_atom_c a env bs in join_positive_c rest env next
  end.

Definition join_positive_ref {P} ps env bs := Cost.value (@join_positive_c P ps env bs).

Lemma join_positive_equation {P} (ps : list (atom P)) env bs :
  join_positive_ref ps env bs =
  match ps with
  | [] => bs
  | a :: rest => join_positive_ref rest env (join_atom a env bs)
  end.
Proof.
  destruct ps; reflexivity.
Qed.

Lemma join_positive_sound {P} (ps : list (atom P)) env bs b' :
  In b' (join_positive_ref ps env bs) ->
  exists b, In b bs /\ binding_extends b b' /\
    (forall sigma, binding_agrees b' sigma -> forall a, In a ps ->
      FinSet.mem tuple_encoding (map (inst sigma) (args a))
        (set_raw (Cost.value (env (pred a)))) = true) /\
    (forall a, In a ps -> forall v, In (TVar v) (args a) ->
      exists c, binding_get b' v = Some c).
Proof.
  revert bs; induction ps as [|a ps IH]; intros bs Hin; rewrite join_positive_equation in Hin.
  - exists b'; split; [exact Hin | split].
    + intros v c Hget; exact Hget.
    + split; intros; contradiction.
  - destruct (IH _ Hin) as [b1 [Hb1 [Hext1 [Hvalues Hvars]]]].
    apply join_atom_members in Hb1 as [b0 [cs [Hb0 [Hcs Hmatch]]]].
    destruct (bind_terms_sound _ _ _ _ Hmatch) as [Hext0 [Hvalue Hbound]].
    exists b0; split; [exact Hb0 | split].
    + eapply binding_extends_trans; eassumption.
    + split.
      * intros sigma Hagree x [<- | Hx].
        -- rewrite <- (Hvalue sigma); [exact Hcs |].
           eapply binding_agrees_extends; eassumption.
        -- apply Hvalues; assumption.
      * intros x [<- | Hx] v Hv.
        -- destruct (Hbound v Hv) as [c Hget]; exists c; apply Hext1, Hget.
        -- apply Hvars with x; assumption.
Qed.

Lemma join_positive_complete {P} (ps : list (atom P)) env bs b sigma :
  In b bs -> binding_agrees b sigma ->
  (forall a, In a ps -> FinSet.mem tuple_encoding (map (inst sigma) (args a))
    (set_raw (Cost.value (env (pred a)))) = true) ->
  exists b', In b' (join_positive_ref ps env bs) /\ binding_agrees b' sigma /\
    binding_extends b b' /\
    (forall a, In a ps -> forall v, In (TVar v) (args a) ->
      exists c, binding_get b' v = Some c).
Proof.
  revert bs b; induction ps as [|a ps IH]; intros bs b Hb Hagree Hvalues;
    rewrite join_positive_equation.
  - exists b; split; [exact Hb | split; [exact Hagree | split]].
    + intros v c Hget; exact Hget.
    + intros x Hbad; contradiction.
  - destruct (bind_terms_complete (args a) b sigma Hagree) as [b1 [Hmatch Hagree1]].
    destruct (bind_terms_sound _ _ _ _ Hmatch) as [Hext1 [_ Hbound1]].
    assert (Hb1 : In b1 (join_atom a env bs)).
    { apply join_atom_members; exists b, (map (inst sigma) (args a)); repeat split;
        try assumption; apply Hvalues; now left. }
    destruct (IH _ b1 Hb1 Hagree1) as [b' [Hb' [Hagree' [Hext' Hvars]]]].
    + intros x Hx; apply Hvalues; now right.
    + exists b'; split; [exact Hb' | split; [exact Hagree' | split]].
      * eapply binding_extends_trans; eassumption.
      * intros x [<- | Hx] v Hv.
        -- destruct (Hbound1 v Hv) as [c Hget]; exists c; apply Hext', Hget.
        -- apply Hvars with x; assumption.
Qed.

Definition negative_ok_c {P} (r : rule P) (env : P -> Cost.t relation) b :=
  forallb_c (fun l =>
    match l with
    | LPos _ => Cost.ret true
    | LNeg a =>
      let* ts := instantiate_c b (args a) in
      Cost.step ;;
      let* rows := env (pred a) in
      Cost.map negb (FinSet.mem_c tuple_encoding ts (set_raw rows))
    end) (body r).

Definition negative_ok {P} r env b := Cost.value (@negative_ok_c P r env b).

Lemma negative_ok_spec {P} (r : rule P) env b : negative_ok r env b = true <->
  forall a, In (LNeg a) (body r) ->
    FinSet.mem tuple_encoding (map (inst (binding_value b)) (args a))
      (set_raw (Cost.value (env (pred a)))) = false.
Proof.
  unfold negative_ok, negative_ok_c; rewrite value_forallb_c, forallb_forall.
  split.
  - intros H a Hin; specialize (H _ Hin).
    change (negb (FinSet.mem tuple_encoding (Cost.value (instantiate_c b (args a)))
      (set_raw (Cost.value (env (pred a))))) = true) in H.
    rewrite instantiate_equation in H; apply negb_true_iff, H.
  - intros H [a | a] Hin; [reflexivity |].
    change (negb (FinSet.mem tuple_encoding (Cost.value (instantiate_c b (args a)))
      (set_raw (Cost.value (env (pred a))))) = true).
    rewrite instantiate_equation.
    apply negb_true_iff, H, Hin.
Qed.

(** Firing retains every nested-loop and binding cost and returns a valid set. *)
Definition fire_rule_c {P} (_ : program P) (r : rule P) env : Cost.t relation :=
  let* ps := positive_atoms_c (body r) in
  let* bindings := join_positive_c ps env [[]] in
  let* selected := filter_c (negative_ok_c r env) bindings in
  let* tuples := map_c (fun b => instantiate_c b (args (head r))) selected in
  set_of_list_c tuple_encoding tuples.

Definition fire_rule {P} prog r env := Cost.value (@fire_rule_c P prog r env).

Lemma fire_rule_members {P} (prog : program P) r env ts :
  FinSet.mem tuple_encoding ts (set_raw (fire_rule prog r env)) = true <->
  exists b, In b (join_positive_ref (positive_atoms (body r)) env [[]]) /\
    negative_ok r env b = true /\ ts = map (inst (binding_value b)) (args (head r)).
Proof.
  unfold fire_rule, fire_rule_c; repeat rewrite Cost.value_bind.
  rewrite value_filter_c, value_map_c.
  fold (@positive_atoms P (body r)).
  fold (join_positive_ref (positive_atoms (body r)) env [[]]).
  fold (@negative_ok P r env).
  change (FinSet.mem tuple_encoding ts
    (set_raw (set_of_list tuple_encoding
      (map (fun b => Cost.value (instantiate_c b (args (head r))))
        (filter (negative_ok r env)
          (join_positive_ref (positive_atoms (body r)) env [[]]))))) = true <->
    exists b, In b (join_positive_ref (positive_atoms (body r)) env [[]]) /\
      negative_ok r env b = true /\ ts = map (inst (binding_value b)) (args (head r))).
  rewrite set_of_list_raw, FinSet.mem_of_list.
  rewrite existsb_exists; split.
  - intros [us [Hin Heq]]; apply (eqb_true_iff tuple_encoding tuple_encoding_laws) in Heq.
    subst us; apply in_map_iff in Hin as [b [Heq Hin]].
    rewrite instantiate_equation in Heq; apply filter_In in Hin.
    exists b; intuition congruence.
  - intros [b [Hin [Hneg Heq]]]; exists ts; split; [|apply eqb_refl].
    apply in_map_iff; exists b; split.
    + rewrite instantiate_equation; symmetry; exact Heq.
    + apply filter_In; auto.
Qed.

Lemma safe_binding_agrees {P} (r : rule P) b sigma :
  safe_rule r -> binding_agrees b sigma ->
  (forall a, In (LPos a) (body r) -> forall v, In (TVar v) (args a) ->
    exists c, binding_get b v = Some c) ->
  map (inst (binding_value b)) (args (head r)) = map (inst sigma) (args (head r)) /\
  forall a, In (LNeg a) (body r) ->
    map (inst (binding_value b)) (args a) = map (inst sigma) (args a).
Proof.
  intros Hsafe Hagree Hbound; split.
  - apply inst_agrees_on_bound; [exact Hagree |].
    intros v Hin; apply atom_vars_spec in Hin.
    destruct (Hsafe v (or_introl Hin)) as [a [Ha Hv]]; apply Hbound with a;
      [exact Ha | apply atom_vars_spec, Hv].
  - intros a Ha; apply inst_agrees_on_bound; [exact Hagree |].
    intros v Hin; apply atom_vars_spec in Hin.
    destruct (Hsafe v (or_intror (ex_intro _ a (conj Ha Hin)))) as [a' [Ha' Hv]].
    apply Hbound with a'; [exact Ha' | apply atom_vars_spec, Hv].
Qed.

(** Every fired tuple has a satisfying valuation even when the source rule is unsafe. *)
Theorem fire_rule_sound {P} (prog : program P) r env ts :
  FinSet.mem tuple_encoding ts (set_raw (fire_rule prog r env)) = true ->
  exists sigma, ts = map (inst sigma) (args (head r)) /\
    (forall a, In (LPos a) (body r) ->
      FinSet.mem tuple_encoding (map (inst sigma) (args a))
        (set_raw (Cost.value (env (pred a)))) = true) /\
    (forall a, In (LNeg a) (body r) ->
      FinSet.mem tuple_encoding (map (inst sigma) (args a))
        (set_raw (Cost.value (env (pred a)))) = false).
Proof.
  rewrite fire_rule_members; intros [b [Hin [Hneg Heq]]].
  exists (binding_value b); split; [exact Heq | split].
  - destruct (join_positive_sound _ _ _ _ Hin) as [b0 [_ [_ [Hvalues _]]]].
    intros a Ha; apply Hvalues; [apply binding_value_agrees | apply positive_atoms_spec, Ha].
  - apply negative_ok_spec, Hneg.
Qed.

(** Safe firing returns exactly the heads of valuations satisfying all body literals. *)
Theorem fire_rule_exact {P} (prog : program P) r env : safe_rule r -> forall ts,
  FinSet.mem tuple_encoding ts (set_raw (fire_rule prog r env)) = true <->
  exists sigma, ts = map (inst sigma) (args (head r)) /\
    (forall a, In (LPos a) (body r) ->
      FinSet.mem tuple_encoding (map (inst sigma) (args a))
        (set_raw (Cost.value (env (pred a)))) = true) /\
    (forall a, In (LNeg a) (body r) ->
      FinSet.mem tuple_encoding (map (inst sigma) (args a))
        (set_raw (Cost.value (env (pred a)))) = false).
Proof.
  intros Hsafe ts; rewrite fire_rule_members; split.
  - intros [b [Hin [Hneg Heq]]]; exists (binding_value b); split; [exact Heq | split].
    + destruct (join_positive_sound _ _ _ _ Hin) as [b0 [_ [_ [Hvalues _]]]].
      intros a Ha; apply Hvalues; [apply binding_value_agrees | apply positive_atoms_spec, Ha].
    + apply negative_ok_spec, Hneg.
  - intros [sigma [Heq [Hpos Hneg]]].
    assert (Hempty : binding_agrees [] sigma).
    { intros v c Hbad; rewrite binding_get_equation in Hbad; discriminate. }
    destruct (join_positive_complete (positive_atoms (body r)) env [[]] [] sigma
      (or_introl eq_refl) Hempty) as [b [Hin [Hagree [_ Hbound]]]].
    + intros a Ha; apply Hpos, positive_atoms_spec, Ha.
    + assert (Hbound' : forall a, In (LPos a) (body r) -> forall v,
        In (TVar v) (args a) -> exists c, binding_get b v = Some c).
      { intros a Ha; apply Hbound, positive_atoms_spec, Ha. }
      destruct (safe_binding_agrees r b sigma Hsafe Hagree Hbound') as [Hhead Hnegative].
      exists b; split; [exact Hin | split].
      * apply negative_ok_spec; intros a Ha; rewrite Hnegative by exact Ha; apply Hneg, Ha.
      * rewrite Hhead; exact Heq.
Qed.

(** Every firing result has a valid representation without encoding-law inputs. *)
Theorem fire_rule_wf {P} (prog : program P) r env :
  FinSet.wf tuple_encoding (set_raw (fire_rule prog r env)).
Proof.
  exact (proj2_sig (fire_rule prog r env)).
Qed.

Arguments fire_rule_c {P} prog r env : simpl never.
Arguments fire_rule {P} prog r env : simpl never.
