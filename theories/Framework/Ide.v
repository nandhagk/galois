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

(** The fixed cubic budget is an ordinary product of three factors. *)
Lemma ide_cube : forall x : N, (x ^ 3 = x * (x * x))%N.
Proof.
  intro x; change (x ^ (N.succ 2) = x * (x * x))%N.
  rewrite N.pow_succ_r', N.pow_2_r; reflexivity.
Qed.

(** Three successive linear size increases fit the released cubic coefficient. *)
Lemma ide_three_sizes : forall c budget first second third : N,
  (first <= c * budget)%N ->
  (second <= c * (budget + first))%N ->
  (third <= c * (budget + second))%N ->
  (third <= 3 * (c + 1) ^ 3 * budget)%N.
Proof.
  intros c budget first second third Hfirst Hsecond Hthird.
  pose proof (N.mul_le_mono_l _ _ c Hfirst) as Hfirst_scaled.
  assert (Hsecond_bound : (second <= c * (1 + c) * budget)%N) by nia.
  pose proof (N.mul_le_mono_l _ _ c Hsecond_bound) as Hsecond_scaled.
  assert (Hthird_bound : (third <= c * (1 + c * (1 + c)) * budget)%N) by nia.
  eapply N.le_trans; [exact Hthird_bound|].
  apply N.mul_le_mono_r; rewrite ide_cube; nia.
Qed.

(** The three composition clocks follow the same two intermediate size bounds. *)
Lemma ide_three_clocks : forall c budget first second t1 t2 t3 : N,
  (first <= c * budget)%N -> (second <= c * (budget + first))%N ->
  (t1 <= c * (c * budget + 1))%N ->
  (t2 <= c * (c * (budget + first) + 1))%N ->
  (t3 <= c * (c * (budget + second) + 1))%N ->
  (t1 + t2 + t3 <= c * c * (3 + 2 * c + c * c) * budget + 3 * c)%N.
Proof.
  intros c budget first second t1 t2 t3 Hfirst Hsecond Ht1 Ht2 Ht3.
  pose proof (N.mul_le_mono_l _ _ c Hfirst) as Hfirst_scaled.
  assert (Hsecond_bound : (second <= c * (1 + c) * budget)%N) by nia.
  pose proof (N.mul_le_mono_l _ _ (c * c) Hfirst) as Hfirst_clock.
  pose proof (N.mul_le_mono_l _ _ (c * c) Hsecond_bound) as Hsecond_clock.
  nia.
Qed.

(** Weight reads and composition clocks fit a constant multiple of the cubic budget. *)
Lemma ide_finish_budget : forall c budget cost : N,
  (1 <= budget)%N ->
  (cost <= (c * c * (3 + 2 * c + c * c) + 2 * c) * budget + 3 * c + 8)%N ->
  (cost <= 32 * (c + 1) * (3 * (c + 1) ^ 3 * budget + 1))%N.
Proof.
  intros c budget cost Hbudget Hcost.
  assert (Hfixed : (3 * c + 8 <= (3 * c + 8) * budget)%N) by nia.
  assert (Htotal :
    (cost <= (c * c * (3 + 2 * c + c * c) + 5 * c + 8) * budget)%N) by nia.
  assert (Hcoefficient : (c * c * (3 + 2 * c + c * c) + 5 * c + 8 <=
    96 * (c + 1) * (c + 1) * (c + 1) * (c + 1))%N) by nia.
  pose proof (N.mul_le_mono_r _ _ budget Hcoefficient) as Hscaled.
  rewrite ide_cube; nia.
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
  Definition c_sys : N :=
    (128 * (N.c_key + F.c_key + C.c_cfg + R.c_rules + M.c_micro + 1))%N.
  Lemma row_work_mono : forall p s t, s <= t ->
    (row_work p s <= row_work p t)%N.
  Proof.
    intros p s t Hst; unfold row_work.
    apply N.add_le_mono_r, N.mul_le_mono_l; lia.
  Qed.

  (** A maximum bounds every width that occurs in its inventory. *)
  Lemma path_width_member : forall widths width, In width widths ->
    width <= fold_right Nat.max 0 widths.
  Proof.
    induction widths as [|head widths IH]; intros width Hin.
    - contradiction.
    - destruct Hin as [<-|Hin]; cbn [fold_right].
      + apply Nat.le_max_l.
      + eapply Nat.le_trans; [exact (IH width Hin)|apply Nat.le_max_r].
  Qed.
  Lemma key_bits_le : forall p r x, wf p -> In r (rows p) ->
    In x (writes p r ++ deps p r) -> key_bits x <= kw p.
  Proof.
    intros p r x _ Hr Hx; unfold kw, path_kw.
    apply path_width_member, in_flat_map.
    exists r; split; [exact Hr|now apply in_map].
  Qed.

  (** A path-edge code contains the widths of all three key components. *)
  Lemma path_key_bits : forall d n x,
    key_bits (d, (n, x)) + 2 = 2 * F.bits d + 2 * N.bits n + F.bits x.
  Proof.
    intros d n x; unfold key_bits, key_code, path_edge_code, pair_code.
    cbn [fst snd]; rewrite !glue_bits.
    unfold F.bits, N.bits.
    pose proof (Pos.size_nat_pos (F.encode d)).
    pose proof (Pos.size_nat_pos (N.encode n)).
    pose proof (Pos.size_nat_pos (F.encode x)); lia.
  Qed.

  (** Each component fits the code's common bit budget. *)
  Lemma path_key_widths : forall d n x,
    F.bits d <= key_bits (d, (n, x)) /\ N.bits n <= key_bits (d, (n, x)) /\
      F.bits x <= key_bits (d, (n, x)).
  Proof.
    intros d n x; pose proof (path_key_bits d n x) as Hbits.
    unfold F.bits, N.bits in *.
    pose proof (Pos.size_nat_pos (F.encode d)).
    pose proof (Pos.size_nat_pos (N.encode n)).
    pose proof (Pos.size_nat_pos (F.encode x)); lia.
  Qed.
  Lemma T_key_code_le : forall x,
    (T_key_code x <= c_sys * N.of_nat (key_bits x + 1))%N.
  Proof.
    intros [d [n x]].
    pose proof (F.T_encode_le d) as Hd.
    pose proof (N.T_encode_le n) as Hn.
    pose proof (F.T_encode_le x) as Hx.
    pose proof (T_glue_le (N.encode n) (F.encode x)) as Hinner.
    pose proof (T_glue_le (F.encode d) (glue (N.encode n) (F.encode x))) as Houter.
    destruct (path_key_widths d n x) as [Hd_width [Hn_width Hx_width]].
    set (budget := N.of_nat (key_bits (d, (n, x)) + 1)).
    set (scale := (N.c_key + F.c_key + C.c_cfg + R.c_rules + M.c_micro + 1)%N).
    assert (Hd_cost : (F.T_encode d <= scale * budget)%N).
    { eapply N.le_trans; [exact Hd|]. apply N.mul_le_mono; unfold scale, budget; lia. }
    assert (Hn_cost : (N.T_encode n <= scale * budget)%N).
    { eapply N.le_trans; [exact Hn|]. apply N.mul_le_mono; unfold scale, budget; lia. }
    assert (Hx_cost : (F.T_encode x <= scale * budget)%N).
    { eapply N.le_trans; [exact Hx|]. apply N.mul_le_mono; unfold scale, budget; lia. }
    assert (Hinner_cost : (T_glue (N.encode n) (F.encode x) <= budget)%N).
    { unfold c_glue in Hinner; unfold N.bits in Hn_width; unfold budget; lia. }
    assert (Houter_cost :
      (T_glue (F.encode d) (glue (N.encode n) (F.encode x)) <= budget)%N).
    { unfold c_glue in Houter; unfold F.bits in Hd_width; unfold budget; lia. }
    assert (Hscale : (1 <= scale)%N) by (unfold scale; lia).
    assert (Hbudget : (1 <= budget)%N) by (unfold budget; lia).
    clear Hd Hn Hx Hinner Houter Hd_width Hn_width Hx_width.
    unfold c_sys; fold scale; fold budget.
    time_unfold T_key_code; time_unfold @T_path_edge_code; time_unfold @T_pair_code.
    time_simpl; time_cbn; time_unfold @T_pair_code.
    time_simpl; time_cbn; unfold pair_code; cbn [fst snd].
    fold scale; fold budget; clearbody scale budget; nia.
  Qed.
  Lemma T_key_eqb_le : forall a b,
    (T_key_eqb a b <= c_sys * N.of_nat (key_bits a + 1))%N.
  Proof.
    intros [d [n x]] [d' [n' x']].
    pose proof (F.T_eqb_le d d') as Hd.
    pose proof (N.T_eqb_le n n') as Hn.
    pose proof (F.T_eqb_le x x') as Hx.
    destruct (path_key_widths d n x) as [Hd_width [Hn_width Hx_width]].
    set (budget := N.of_nat (key_bits (d, (n, x)) + 1)).
    set (scale := (N.c_key + F.c_key + C.c_cfg + R.c_rules + M.c_micro + 1)%N).
    assert (Hd_cost : (F.T_eqb d d' <= scale * budget)%N).
    { eapply N.le_trans; [exact Hd|]. apply N.mul_le_mono; unfold scale, budget; lia. }
    assert (Hn_cost : (N.T_eqb n n' <= scale * budget)%N).
    { eapply N.le_trans; [exact Hn|]. apply N.mul_le_mono; unfold scale, budget; lia. }
    assert (Hx_cost : (F.T_eqb x x' <= scale * budget)%N).
    { eapply N.le_trans; [exact Hx|]. apply N.mul_le_mono; unfold scale, budget; lia. }
    assert (Hscale : (1 <= scale)%N) by (unfold scale; lia).
    assert (Hbudget : (1 <= budget)%N) by (unfold budget; lia).
    clear Hd Hn Hx Hd_width Hn_width Hx_width.
    unfold c_sys; fold scale; fold budget.
    time_unfold T_key_eqb; time_simpl; time_cbn.
    fold scale; fold budget; clearbody scale budget; nia.
  Qed.
  Lemma T_rows_le : forall p, wf p ->
    (T_rows p <= c_sys * N.of_nat (length (rows p) + 1))%N.
  Proof.
    intros p _.
    pose proof (R.T_rules_le p) as Hrules.
    pose proof (T_path_number_le 1%positive (R.rules p)) as Hnumber.
    change (T_rows p <= c_sys *
      N.of_nat (length (path_number 1%positive (R.rules p)) + 1))%N.
    rewrite path_number_length; unfold c_sys.
    time_unfold T_rows; time_cbn_all; nia.
  Qed.

  (** Target selection performs at most one bounded destination projection. *)
  Lemma target_clock : forall p r, (T_target p r <= C.c_cfg + 4)%N.
  Proof.
    intros p [code rule]; destruct rule; time_step.
  Qed.

  (** Starting a row reads at most two bounded source projections. *)
  Lemma start_clock : forall p r, (T_start p r <= 2 * C.c_cfg + 16)%N.
  Proof.
    intros p [code rule].
    pose proof (List.T_rev_append_le (@nil M.t) (@nil M.t)) as Hreverse.
    destruct rule.
    all: time_unfold T_start; time_unfold T_deps; time_unfold @T_path_query.
    all: time_simpl; time_cbn; try time_unfold T_finish.
    all: time_simpl; time_cbn_all; time_pose; nia.
  Qed.

  (** A supplied operand budget also bounds the size of their composition. *)
  Lemma compose_size_budget : forall f g budget,
    (N.of_nat (M.size f + M.size g + 1) <= budget)%N ->
    (N.of_nat (M.size (M.compose f g)) <= M.c_micro * budget)%N.
  Proof.
    intros f g budget Hbudget; eapply N.le_trans; [apply M.compose_size|].
    now apply N.mul_le_mono_l.
  Qed.

  (** A supplied operand budget bounds the work oracle and its composition clock. *)
  Lemma compose_clock_budget : forall f g budget,
    (N.of_nat (M.size f + M.size g + 1) <= budget)%N ->
    (M.T_compose f g <= M.c_micro * (M.c_micro * budget + 1))%N.
  Proof.
    intros f g budget Hbudget; eapply N.le_trans; [apply M.T_compose_le|].
    apply N.mul_le_mono_l, N.add_le_mono_r.
    eapply N.le_trans; [apply M.compose_work_le|].
    now apply N.mul_le_mono_l.
  Qed.

  (** One composition fits the same cubic budget used for a matched return. *)
  Lemma step_size_budget : forall weight value w s,
    M.size weight <= w -> M.size value <= s ->
    (N.of_nat (M.size (M.compose weight value)) <=
      3 * (M.c_micro + 1) ^ 3 * N.of_nat (w + s + 1))%N.
  Proof.
    intros weight value w s Hweight Hvalue.
    assert (Hsize : (N.of_nat (M.size (M.compose weight value)) <=
      M.c_micro * N.of_nat (w + s + 1))%N).
    { apply compose_size_budget; lia. }
    eapply N.le_trans; [exact Hsize|].
    apply N.mul_le_mono_r; rewrite ide_cube; nia.
  Qed.

  (** The call, callee and return compositions fit the three-stage size budget. *)
  Lemma return_size_budget : forall call_weight ret_weight caller callee w s,
    M.size call_weight <= w -> M.size ret_weight <= w ->
    M.size caller <= s -> M.size callee <= s ->
    (N.of_nat (M.size
      (M.compose ret_weight (M.compose callee (M.compose call_weight caller)))) <=
      3 * (M.c_micro + 1) ^ 3 * N.of_nat (w + s + 1))%N.
  Proof.
    intros call_weight ret_weight caller callee w s Hcall Hret Hcaller Hcallee.
    assert (Hfirst : (N.of_nat (M.size (M.compose call_weight caller)) <=
      M.c_micro * N.of_nat (w + s + 1))%N).
    { apply compose_size_budget; lia. }
    assert (Hsecond : (N.of_nat (M.size (M.compose callee (M.compose call_weight caller))) <=
      M.c_micro * (N.of_nat (w + s + 1) +
        N.of_nat (M.size (M.compose call_weight caller))))%N).
    { apply compose_size_budget; lia. }
    assert (Hthird : (N.of_nat (M.size
      (M.compose ret_weight (M.compose callee (M.compose call_weight caller)))) <=
      M.c_micro * (N.of_nat (w + s + 1) +
        N.of_nat (M.size (M.compose callee (M.compose call_weight caller)))))%N).
    { apply compose_size_budget; lia. }
    exact (ide_three_sizes M.c_micro (N.of_nat (w + s + 1)) _ _ _
      Hfirst Hsecond Hthird).
  Qed.

  (** The three return compositions have one common polynomial clock bound. *)
  Lemma return_clock_budget : forall call_weight ret_weight caller callee w s,
    M.size call_weight <= w -> M.size ret_weight <= w ->
    M.size caller <= s -> M.size callee <= s ->
    (M.T_compose call_weight caller +
      M.T_compose callee (M.compose call_weight caller) +
      M.T_compose ret_weight (M.compose callee (M.compose call_weight caller)) <=
      M.c_micro * M.c_micro * (3 + 2 * M.c_micro + M.c_micro * M.c_micro) *
        N.of_nat (w + s + 1) + 3 * M.c_micro)%N.
  Proof.
    intros call_weight ret_weight caller callee w s Hcall Hret Hcaller Hcallee.
    assert (Hfirst : (N.of_nat (M.size (M.compose call_weight caller)) <=
      M.c_micro * N.of_nat (w + s + 1))%N).
    { apply compose_size_budget; lia. }
    assert (Hsecond : (N.of_nat (M.size (M.compose callee (M.compose call_weight caller))) <=
      M.c_micro * (N.of_nat (w + s + 1) +
        N.of_nat (M.size (M.compose call_weight caller))))%N).
    { apply compose_size_budget; lia. }
    eapply ide_three_clocks; [exact Hfirst|exact Hsecond| | |].
    - apply compose_clock_budget; lia.
    - apply compose_clock_budget; lia.
    - apply compose_clock_budget; lia.
  Qed.

  (** Finishing an enabled rule respects the budget for its supplied values. *)
  Lemma finish_size_le : forall p rule xs s, enabled p rule ->
    (forall value, In value xs -> M.size value <= s) ->
    (N.of_nat (M.size (finish p rule xs)) <= row_work p s)%N.
  Proof.
    intros p rule xs s Henabled Hxs; destruct rule as [n d|d0 e x y|d0 call ret x a b y].
    - cbn [finish]; unfold row_work; lia.
    - destruct xs as [|value xs]; [cbn [finish]; unfold row_work; lia|].
      destruct Henabled as [_ [He [_ [Hx Hy]]]].
      pose proof (FL.weight_size p e x y He Hx Hy) as Hweight.
      pose proof (Hxs value (or_introl eq_refl)) as Hvalue.
      pose proof (step_size_budget _ _ _ _ Hweight Hvalue) as Hsize.
      cbn [finish]; unfold row_work; lia.
    - destruct xs as [|caller [|callee xs]];
        try solve [cbn [finish]; unfold row_work; lia].
      destruct Henabled as [_ [Hcall [Hret [_ [Hx [Ha [Hb Hy]]]]]]].
      pose proof (FL.weight_size p call x a Hcall Hx Ha) as Hcall_weight.
      pose proof (FL.weight_size p ret b y Hret Hb Hy) as Hret_weight.
      pose proof (Hxs caller (or_introl eq_refl)) as Hcaller.
      pose proof (Hxs callee (or_intror (or_introl eq_refl))) as Hcallee.
      pose proof (return_size_budget _ _ _ _ _ _ Hcall_weight Hret_weight Hcaller Hcallee)
        as Hsize.
      cbn [finish]; unfold row_work; lia.
  Qed.

  (** The enabled rule's finish clock is charged to its weights and supplied values. *)
  Lemma finish_clock : forall p rule xs s, enabled p rule ->
    (forall value, In value xs -> M.size value <= s) ->
    (T_finish p rule xs <= 32 * (M.c_micro + 1) * (row_work p s + 1))%N.
  Proof.
    intros p rule xs s Henabled Hxs; destruct rule as [n d|d0 e x y|d0 call ret x a b y].
    - time_step.
    - destruct xs as [|value xs]; [time_step|].
      destruct Henabled as [_ [He [_ [Hx Hy]]]].
      pose proof (FL.weight_size p e x y He Hx Hy) as Hweight.
      pose proof (Hxs value (or_introl eq_refl)) as Hvalue.
      assert (Hweight_clock : (FL.T_weight p e x y <=
        M.c_micro * N.of_nat (FL.weight_work p + s + 1))%N).
      { eapply N.le_trans; [apply FL.T_weight_le; eassumption|].
        apply N.mul_le_mono_l; lia. }
      pose proof (compose_clock_budget (FL.weight p e x y) value
        (N.of_nat (FL.weight_work p + s + 1)) ltac:(lia)) as Hcompose.
      eapply N.le_trans with (m := (32 * (M.c_micro + 1) *
        (3 * (M.c_micro + 1) ^ 3 * N.of_nat (FL.weight_work p + s + 1) + 1))%N).
      + apply ide_finish_budget; [lia|].
        time_unfold T_finish; time_simpl; time_cbn; nia.
      + apply N.mul_le_mono_l, N.add_le_mono_r; unfold row_work; lia.
    - destruct xs as [|caller [|callee xs]]; try solve [time_step].
      destruct Henabled as [_ [Hcall [Hret [_ [Hx [Ha [Hb Hy]]]]]]].
      pose proof (FL.weight_size p call x a Hcall Hx Ha) as Hcall_weight.
      pose proof (FL.weight_size p ret b y Hret Hb Hy) as Hret_weight.
      pose proof (Hxs caller (or_introl eq_refl)) as Hcaller.
      pose proof (Hxs callee (or_intror (or_introl eq_refl))) as Hcallee.
      pose proof (return_clock_budget _ _ _ _ _ _ Hcall_weight Hret_weight Hcaller Hcallee)
        as Hcompose.
      assert (Hcall_clock : (FL.T_weight p call x a <=
        M.c_micro * N.of_nat (FL.weight_work p + s + 1))%N).
      { eapply N.le_trans; [apply FL.T_weight_le; eassumption|].
        apply N.mul_le_mono_l; lia. }
      assert (Hret_clock : (FL.T_weight p ret b y <=
        M.c_micro * N.of_nat (FL.weight_work p + s + 1))%N).
      { eapply N.le_trans; [apply FL.T_weight_le; eassumption|].
        apply N.mul_le_mono_l; lia. }
      eapply N.le_trans with (m := (32 * (M.c_micro + 1) *
        (3 * (M.c_micro + 1) ^ 3 * N.of_nat (FL.weight_work p + s + 1) + 1))%N).
      + apply ide_finish_budget; [lia|].
        time_unfold T_finish; time_simpl; time_cbn; nia.
      + apply N.mul_le_mono_l, N.add_le_mono_r; unfold row_work; lia.
  Qed.

  (** Every listed row carries one of the rule provider's enabled rules. *)
  Lemma listed_rule_enabled : forall p r, wf p -> In r (rows p) ->
    enabled p (path_row_rule r).
  Proof.
    intros p r Hwf Hr; apply (proj1 (rows_spec p (path_row_rule r) Hwf)).
    exists r; now split.
  Qed.

  (** Evaluation supplies the dependency values to the rule in their declared order. *)
  Lemma eval_finish : forall p r look,
    eval p r look = Some (finish p (path_row_rule r) (map look (deps p r)), nil).
  Proof.
    intros p [code rule] look; destruct rule; reflexivity.
  Qed.

  (** Finishing a frame reverses only its received values before evaluating the rule. *)
  Lemma resume_done_clock : forall p rule received value,
    (T_resume p (PathFrame _ _ _ _ rule nil received) value <=
      T_finish p rule (rev_append (value :: received) nil) +
        N.of_nat (length received) + 4)%N.
  Proof.
    intros p rule received value.
    pose proof (List.T_rev_append_le (value :: received) nil) as Hreverse.
    time_unfold T_resume; time_unfold @T_path_query.
    time_simpl; time_cbn_all; lia.
  Qed.

  (** A frame with at most one earlier answer fits the enabled rule's resume budget. *)
  Lemma resume_clock_le : forall p rule pending received value s,
    enabled p rule -> length received <= 1 ->
    (forall a, In a (value :: received) -> M.size a <= s) ->
    (T_resume p (PathFrame _ _ _ _ rule pending received) value <=
      c_sys * (row_work p s + 1))%N.
  Proof.
    intros p rule pending received value s Henabled Hreceived Hvalues.
    assert (Hscale : (64 * (M.c_micro + 1) <= c_sys)%N) by (unfold c_sys; lia).
    destruct pending as [|x pending].
    - pose proof (resume_done_clock p rule received value) as Hresume.
      assert (Hfinish : (T_finish p rule (rev_append (value :: received) nil) <=
        32 * (M.c_micro + 1) * (row_work p s + 1))%N).
      { apply finish_clock; [exact Henabled|].
        intros a Hin; rewrite rev_append_rev, app_nil_r in Hin.
        rewrite <- (in_rev (value :: received) a) in Hin; now apply Hvalues. }
      nia.
    - time_unfold T_resume; time_unfold @T_path_query.
      time_simpl; time_cbn; nia.
  Qed.
  Lemma T_target_le : forall p r, wf p -> In r (rows p) ->
    (T_target p r <= c_sys * (row_work p 0 + 1))%N.
  Proof.
    intros p r _ _; pose proof (target_clock p r) as Hclock.
    assert (Hscale : (C.c_cfg + 4 <= c_sys)%N) by (unfold c_sys; lia).
    nia.
  Qed.
  Lemma T_start_le : forall p r, wf p -> In r (rows p) ->
    (T_start p r <= c_sys * (row_work p 0 + 1))%N.
  Proof.
    intros p r _ _; pose proof (start_clock p r) as Hclock.
    assert (Hscale : (2 * C.c_cfg + 16 <= c_sys)%N) by (unfold c_sys; lia).
    nia.
  Qed.
  Lemma T_resume_le : forall p r look s n q acc x f, wf p -> In r (rows p) ->
    (forall y, M.size (look y) <= s) ->
    loop_fuel (eval_step (resume p) look) n (start p r, nil) = inl (q, acc) ->
    fst (peel q acc) = inr (x, f) ->
    (T_resume p f (look x) <= c_sys * (row_work p s + 1))%N.
  Proof.
    intros p [code rule] look s n q acc x f Hwf Hr Hlook Hloop Hpeel.
    pose proof (listed_rule_enabled p (PathRow code rule) Hwf Hr) as Henabled.
    destruct rule; destruct n as [|[|[|n]]];
      cbn [start deps path_row_rule path_query loop_fuel eval_step peel resume fst snd]
        in Hloop; try discriminate;
      injection Hloop as <- <-;
      cbn [peel fst snd] in Hpeel; try discriminate;
      injection Hpeel as <- <-.
    all: eapply resume_clock_le; [exact Henabled|cbn [length]; lia|].
    all: intros value Hin; repeat destruct Hin as [<-|Hin]; try contradiction; apply Hlook.
  Qed.
  Lemma T_deps_le : forall p r, wf p -> In r (rows p) ->
    (T_deps p r <= c_sys * N.of_nat (length (deps p r) + 1) *
      N.of_nat (kw p + 1))%N.
  Proof.
    intros p [code rule] _ _; destruct rule; unfold c_sys; time_step.
  Qed.
  Lemma T_sides_le : forall p r, wf p -> In r (rows p) ->
    (T_sides p r <= c_sys * N.of_nat (length (sides p r) + 1) *
      N.of_nat (kw p + 1))%N.
  Proof.
    intros p r _ _; unfold c_sys; time_step.
  Qed.
  Lemma eval_size_le : forall p r look s a ss, wf p -> In r (rows p) ->
    (forall x, M.size (look x) <= s) -> eval p r look = Some (a, ss) ->
    (N.of_nat (M.size a) <= row_work p s)%N /\
    Forall (fun xb => (N.of_nat (M.size (snd xb)) <= row_work p s)%N) ss.
  Proof.
    intros p r look s a ss Hwf Hr Hlook Heval.
    rewrite eval_finish in Heval; injection Heval as <- <-.
    split; [|constructor].
    apply finish_size_le; [exact (listed_rule_enabled p r Hwf Hr)|].
    intros value Hin; apply in_map_iff in Hin; destruct Hin as [x [<- Hx]].
    apply Hlook.
  Qed.
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
