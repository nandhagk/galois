(** * Predicate levels for stratified negation

    The reference checker raises head levels along literal dependencies.
    For example, a negative self-dependency exhausts the finite round budget.
    Builds on: DatalogSyntax, BaseMap and CostList. *)

From Stdlib Require Import List Bool PeanoNat NArith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap.
From Galois.Datalog Require Import DatalogSyntax.
Import List.ListNotations Cost.Notations.
Local Open Scope nat_scope.

(** Levels are computational callbacks, independent of stratification evidence. *)
Record stratification (P : Type) := Stratification {
  level_c : P -> Cost.t nat;
  count : nat
}.

Arguments Stratification {P}.
Arguments level_c {P}.
Arguments count {P}.

Definition level {P} (st : stratification P) p := Cost.value (level_c st p).

(** Positive dependencies may stay at the head level and negative dependencies descend. *)
Definition stratified {P} (prog : program P) (st : stratification P) : Prop :=
  (forall p, level st p < count st) /\
  forall r l, In r (rules prog) -> In l (body r) ->
    match l with
    | LPos a => level st (pred a) <= level st (pred (head r))
    | LNeg a => level st (pred a) < level st (pred (head r))
    end.

Definition rule_edges_c {P} (r : rule P) :=
  map_c (fun l => Cost.ret (pred (head r), (pred (lit_atom l),
    match l with
    | LPos _ => 0
    | LNeg _ => 1
    end))) (body r).

Definition rule_edges {P} (r : rule P) := Cost.value (rule_edges_c r).

Definition program_edges_c {P} (prog : program P) :=
  fold_right_c (fun r es =>
    let* here := rule_edges_c r in app_c here es) [] (rules prog).

Definition program_edges {P} (prog : program P) := Cost.value (program_edges_c prog).

Definition rule_predicates_c {P} (r : rule P) :=
  Cost.map (cons (pred (head r)))
    (map_c (fun l => Cost.ret (pred (lit_atom l))) (body r)).

Definition rule_predicates {P} (r : rule P) := Cost.value (rule_predicates_c r).

(** Occurrences suffice for the round bound, so preparation needs no deduplication. *)
Definition rule_nodes_c {P} (prog : program P) :=
  fold_right_c (fun r ps =>
    let* here := rule_predicates_c r in app_c here ps) [] (rules prog).

Definition rule_nodes {P} (prog : program P) := Cost.value (rule_nodes_c prog).

Lemma rule_edges_equation {P} (r : rule P) :
  rule_edges r = map (fun l => (pred (head r), (pred (lit_atom l),
    match l with LPos _ => 0 | LNeg _ => 1 end))) (body r).
Proof.
  unfold rule_edges, rule_edges_c; rewrite value_map_c; reflexivity.
Qed.

Lemma program_edges_equation {P} (prog : program P) :
  program_edges prog = flat_map rule_edges (rules prog).
Proof.
  unfold program_edges, program_edges_c; rewrite value_fold_right_c.
  induction (rules prog) as [|r rs IH]; cbn [fold_right flat_map]; [reflexivity |].
  rewrite Cost.value_bind, value_app_c, IH; reflexivity.
Qed.

Lemma rule_predicates_equation {P} (r : rule P) :
  rule_predicates r = pred (head r) :: map (fun l => pred (lit_atom l)) (body r).
Proof.
  unfold rule_predicates, rule_predicates_c; rewrite Cost.value_map, value_map_c.
  reflexivity.
Qed.

Lemma rule_nodes_spec {P} (prog : program P) p :
  In p (rule_nodes prog) <-> exists r, In r (rules prog) /\ In p (rule_predicates r).
Proof.
  assert (Heq : rule_nodes prog = flat_map rule_predicates (rules prog)).
  { unfold rule_nodes, rule_nodes_c; rewrite value_fold_right_c.
    induction (rules prog) as [|r rs IH]; cbn [fold_right flat_map]; [reflexivity |].
    rewrite Cost.value_bind, value_app_c, IH; reflexivity. }
  rewrite Heq, in_flat_map; reflexivity.
Qed.

Lemma edge_nodes {P} (prog : program P) h b w :
  In (h, (b, w)) (program_edges prog) ->
  In h (rule_nodes prog) /\ In b (rule_nodes prog).
Proof.
  rewrite program_edges_equation, in_flat_map.
  intros [r [Hr He]]; rewrite rule_edges_equation in He.
  apply in_map_iff in He as [l [He Hl]].
  injection He as Hh Hb Hw; subst h b.
  split; apply rule_nodes_spec; exists r; split; try exact Hr;
    rewrite rule_predicates_equation.
  - now left.
  - right; apply in_map_iff; exists l; auto.
Qed.

Definition level_at_c {P} (E : encoding P) (m : Map.t P nat) p :=
  Map.find_or_c E 0 p m.

Definition level_at {P} (E : encoding P) (m : Map.t P nat) p :=
  Cost.value (level_at_c E m p).

Lemma level_at_equation {P} (E : encoding P) m p :
  level_at E m p = match Map.get E p m with Some n => n | None => 0 end.
Proof.
  apply Map.find_or_equation.
Qed.

Definition edge_ok_c {P} (E : encoding P) (m : Map.t P nat) (e : P * (P * nat)) :=
  let* b := level_at_c E m (fst (snd e)) in
  let* h := level_at_c E m (fst e) in
  Cost.step ;; Cost.ret (Nat.leb (b + snd (snd e)) h).

Definition edge_ok {P} (E : encoding P) m e := Cost.value (edge_ok_c E m e).

Definition levels_ok_c {P} (prog : program P) m :=
  let* es := program_edges_c prog in
  forallb_c (edge_ok_c (penc prog) m) es.

Definition levels_ok {P} (prog : program P) m := Cost.value (levels_ok_c prog m).

Lemma levels_ok_spec {P} (prog : program P) m :
  levels_ok prog m = true <-> forall h b w,
    In (h, (b, w)) (program_edges prog) ->
    level_at (penc prog) m b + w <= level_at (penc prog) m h.
Proof.
  unfold levels_ok, levels_ok_c; rewrite Cost.value_bind, value_forallb_c.
  fold (program_edges prog).
  change (forallb (edge_ok (penc prog) m) (program_edges prog) = true <->
    forall h b w, In (h, (b, w)) (program_edges prog) ->
      level_at (penc prog) m b + w <= level_at (penc prog) m h).
  rewrite forallb_forall; split.
  - intros H h b w Hin; specialize (H _ Hin); apply Nat.leb_le; exact H.
  - intros H [h [b w]] Hin; apply Nat.leb_le; apply H; exact Hin.
Qed.

Definition raise_edge_c {P} (E : encoding P) (m : Map.t P nat) (e : P * (P * nat)) :=
  let* h := level_at_c E m (fst e) in
  let* b := level_at_c E m (fst (snd e)) in
  Cost.step ;; Map.set_c E (fst e) (Nat.max h (b + snd (snd e))) m.

Definition raise_edge {P} (E : encoding P) m e := Cost.value (raise_edge_c E m e).

Definition raise_pass_c {P} (E : encoding P) es m := fold_left_c (raise_edge_c E) es m.
Definition raise_pass {P} (E : encoding P) es m := Cost.value (raise_pass_c E es m).

Lemma raise_pass_equation {P} (E : encoding P) es m :
  raise_pass E es m = fold_left (raise_edge E) es m.
Proof.
  apply value_fold_left_c.
Qed.

Lemma raise_edge_equation {P} (E : encoding P) m e :
  raise_edge E m e = Map.set E (fst e)
    (Nat.max (level_at E m (fst e)) (level_at E m (fst (snd e)) + snd (snd e))) m.
Proof.
  reflexivity.
Qed.

Lemma raise_pass_wf {P} (E : encoding P) es m :
  Map.wf E m -> Map.wf E (raise_pass E es m).
Proof.
  rewrite raise_pass_equation; revert m; induction es as [|e es IH]; intros m Hwf.
  - exact Hwf.
  - cbn [fold_left]; apply IH; rewrite raise_edge_equation; apply Map.wf_set, Hwf.
Qed.

Lemma level_set {P} (E : encoding P) m h v p :
  Map.wf E m ->
  level_at E (Map.set E h v m) p =
    if eqb E p h then v else level_at E m p.
Proof.
  intro Hwf; rewrite !level_at_equation, Map.get_set by exact Hwf.
  destruct (eqb E p h); reflexivity.
Qed.

Lemma level_code {P} (E : encoding P) m p q :
  encode E p = encode E q -> level_at E m p = level_at E m q.
Proof.
  intro Heq; rewrite !level_at_equation, !Map.get_equation, Heq; reflexivity.
Qed.

Lemma raise_edge_grows {P} (E : encoding P) m e p :
  Map.wf E m -> level_at E m p <= level_at E (raise_edge E m e) p.
Proof.
  intro Hwf; rewrite raise_edge_equation, level_set by exact Hwf.
  destruct (eqb E p (fst e)) eqn:Heq; [|lia].
  rewrite eqb_equation in Heq.
  apply Pos.eqb_eq in Heq; rewrite (level_code E m p (fst e) Heq).
  apply Nat.le_max_l.
Qed.

Lemma raise_pass_grows {P} (E : encoding P) es m p :
  Map.wf E m -> level_at E m p <= level_at E (raise_pass E es m) p.
Proof.
  intro Hwf; rewrite raise_pass_equation; revert m Hwf.
  induction es as [|e es IH]; intros m Hwf; cbn [fold_left]; [lia |].
  eapply Nat.le_trans; [apply raise_edge_grows, Hwf |].
  apply IH; rewrite raise_edge_equation; apply Map.wf_set, Hwf.
Qed.

Lemma raise_pass_edge {P} (E : encoding P) es m h b w :
  Map.wf E m -> In (h, (b, w)) es ->
  level_at E m b + w <= level_at E (raise_pass E es m) h.
Proof.
  rewrite raise_pass_equation; revert m.
  induction es as [|[h' [b' w']] es IH]; intros m Hwf Hin; cbn in Hin;
    [contradiction |].
  assert (Hnext : Map.wf E (raise_edge E m (h', (b', w')))).
  { rewrite raise_edge_equation; apply Map.wf_set, Hwf. }
  cbn [fold_left]; destruct Hin as [Heq | Hin].
  - injection Heq as Hh Hb Hw; subst h' b' w'.
    eapply Nat.le_trans with (m := level_at E (raise_edge E m (h, (b, w))) h).
    + rewrite raise_edge_equation, level_set by exact Hwf.
      rewrite eqb_refl; apply Nat.le_max_r.
    + rewrite <- raise_pass_equation; apply raise_pass_grows, Hnext.
  - specialize (IH _ Hnext Hin).
    pose proof (raise_edge_grows E m (h', (b', w')) b Hwf); lia.
Qed.

(** The checker uses a structurally recursive natural budget. *)
Fixpoint stratify_loop_c {P} (prog : program P) (n : nat) (m : Map.t P nat)
    : Cost.t (Map.t P nat * bool) :=
  match n with
  | 0 => Cost.ret (m, false)
  | S n' =>
    Cost.step ;;
    let* ok := levels_ok_c prog m in
    if ok then Cost.ret (m, true)
    else
      let* es := program_edges_c prog in
      let* next := raise_pass_c (penc prog) es m in
      stratify_loop_c prog n' next
  end.

Definition stratify_loop {P} (prog : program P) n m :=
  Cost.value (stratify_loop_c prog n m).

Lemma stratify_loop_equation {P} (prog : program P) n m :
  stratify_loop prog n m =
  match n with
  | 0 => (m, false)
  | S n' =>
    if levels_ok prog m then (m, true)
    else stratify_loop prog n' (raise_pass (penc prog) (program_edges prog) m)
  end.
Proof.
  destruct n as [|n]; [reflexivity |].
  unfold stratify_loop at 1; cbn [stratify_loop_c].
  rewrite Cost.value_bind, Cost.value_bind.
  fold (levels_ok prog m); destruct (levels_ok prog m);
    reflexivity.
Qed.

Definition maximum_c {P} (prog : program P) m :=
  let* ps := rule_nodes_c prog in
  fold_left_c (fun n p =>
    let* v := level_at_c (penc prog) m p in Cost.ret (Nat.max n v)) ps 0.

Definition maximum {P} (prog : program P) m := Cost.value (maximum_c prog m).

Definition stratify_c {P} (prog : program P) : Cost.t (option (stratification P)) :=
  let* ps := rule_nodes_c prog in
  let* n := length_c ps in
  Cost.step ;;
  let* result := stratify_loop_c prog (n * n + 1) Map.empty in
  let '(m, done) := result in
  if done then
    let* hi := maximum_c prog m in
    Cost.ret (Some (Stratification (level_at_c (penc prog) m) (S hi)))
  else Cost.ret None.

Definition stratify {P} (prog : program P) := Cost.value (stratify_c prog).

Lemma stratify_equation {P} (prog : program P) :
  stratify prog =
  let '(m, done) := stratify_loop prog
    (length (rule_nodes prog) * length (rule_nodes prog) + 1) Map.empty in
  if done then Some (Stratification (level_at_c (penc prog) m) (S (maximum prog m)))
  else None.
Proof.
  unfold stratify, stratify_c; rewrite Cost.value_bind, Cost.value_bind, value_length_c.
  rewrite Cost.value_bind, Cost.value_bind; fold (rule_nodes prog).
  fold (stratify_loop prog (length (rule_nodes prog) * length (rule_nodes prog) + 1)
    Map.empty).
  destruct (stratify_loop prog _ Map.empty) as [m []]; reflexivity.
Qed.

Lemma maximum_member {P} (prog : program P) m p :
  In p (rule_nodes prog) -> level_at (penc prog) m p <= maximum prog m.
Proof.
  unfold maximum, maximum_c; rewrite Cost.value_bind, value_fold_left_c.
  fold (rule_nodes prog).
  generalize 0 as n; generalize (rule_nodes prog) as ps.
  intros ps; induction ps as [|q ps IH]; intros n Hin; [contradiction |].
  cbn [fold_left]; destruct Hin as [<- | Hin].
  - assert (Hacc : forall xs n, n <= fold_left
      (fun n p => Nat.max n (level_at (penc prog) m p)) xs n).
    { intro xs; induction xs as [|x xs IHxs]; intro a; cbn; [lia |].
      eapply Nat.le_trans; [apply Nat.le_max_l | apply IHxs]. }
    eapply Nat.le_trans; [apply Nat.le_max_r | apply Hacc].
  - apply IH, Hin.
Qed.

(** Support is stated by encoded equality so soundness also covers aliasing dictionaries. *)
Definition level_supported {P} (prog : program P) m :=
  forall p, level_at (penc prog) m p = 0 \/
    exists q, In q (rule_nodes prog) /\ encode (penc prog) p = encode (penc prog) q.

Lemma raise_pass_support {P} (prog : program P) es m :
  Map.wf (penc prog) m -> level_supported prog m ->
  (forall h b w, In (h, (b, w)) es -> In h (rule_nodes prog)) ->
  level_supported prog (raise_pass (penc prog) es m).
Proof.
  rewrite raise_pass_equation; revert m.
  induction es as [|[h [b w]] es IH]; intros m Hwf Hsupport Hheads; [exact Hsupport |].
  cbn [fold_left]; apply IH.
  - rewrite raise_edge_equation; apply Map.wf_set, Hwf.
  - intro p; rewrite raise_edge_equation, level_set by exact Hwf.
    cbn [fst snd].
    destruct (eqb (penc prog) p h) eqn:Heq; [right | apply Hsupport].
    exists h; split; [apply (Hheads h b w); now left |].
    rewrite eqb_equation in Heq; apply Pos.eqb_eq, Heq.
  - intros h' b' w' Hin; apply (Hheads h' b' w'); now right.
Qed.

Lemma stratify_loop_sound {P} (prog : program P) n m :
  Map.wf (penc prog) m -> level_supported prog m ->
  let '(next, done) := stratify_loop prog n m in
  (done = true -> levels_ok prog next = true) /\ level_supported prog next.
Proof.
  revert m; induction n as [|n IH]; intros m Hwf Hsupport;
    rewrite stratify_loop_equation.
  - split; [discriminate | exact Hsupport].
  - destruct (levels_ok prog m) eqn:Hok.
    + split; [intros _; exact Hok | exact Hsupport].
    + apply IH.
      * apply raise_pass_wf, Hwf.
      * apply raise_pass_support; [exact Hwf | exact Hsupport |].
        intros h b w Hin; exact (proj1 (edge_nodes prog h b w Hin)).
Qed.

(** Successful checking supplies bounded levels without requiring predicate injectivity. *)
Theorem stratify_sound {P} (prog : program P) st :
  stratify prog = Some st -> stratified prog st.
Proof.
  rewrite stratify_equation.
  pose proof (stratify_loop_sound prog
    (length (rule_nodes prog) * length (rule_nodes prog) + 1) Map.empty
    (Map.wf_empty (penc prog))) as Hstate.
  assert (Hempty : level_supported prog Map.empty).
  { intro p; left; rewrite level_at_equation, Map.get_empty; reflexivity. }
  specialize (Hstate Hempty).
  destruct (stratify_loop prog _ Map.empty) as [m done].
  destruct Hstate as [Hdone Hsupport]; destruct done; [|discriminate].
  intro Hsome; injection Hsome as <-; split.
  - intro p; change (level_at (penc prog) m p < S (maximum prog m)).
    destruct (Hsupport p) as [Hzero | [q [Hq Hcode]]]; [lia |].
    rewrite (level_code (penc prog) m p q Hcode).
    pose proof (maximum_member prog m q Hq); lia.
  - intros r l Hr Hl; specialize (Hdone eq_refl).
    pose proof (proj1 (levels_ok_spec prog m) Hdone) as Hedges.
    assert (Hin : In (pred (head r), (pred (lit_atom l),
      match l with LPos _ => 0 | LNeg _ => 1 end)) (program_edges prog)).
    { rewrite program_edges_equation; apply in_flat_map; exists r; split; [exact Hr |].
      rewrite rule_edges_equation; apply in_map_iff; exists l; auto. }
    specialize (Hedges _ _ _ Hin); destruct l as [a | a]; cbn [lit_atom] in Hedges.
    + change (level_at (penc prog) m (pred a) <= level_at (penc prog) m (pred (head r))).
      lia.
    + change (level_at (penc prog) m (pred a) < level_at (penc prog) m (pred (head r))).
      lia.
Qed.

Section Complete.
Context {P : Type} (prog : program P) (HE : encoding_laws (penc prog)).

Definition levels_sum ps m := fold_right (fun p n => level_at (penc prog) m p + n) 0 ps.

Lemma levels_sum_mono ps m m' :
  (forall p, level_at (penc prog) m p <= level_at (penc prog) m' p) ->
  levels_sum ps m <= levels_sum ps m'.
Proof.
  intro Hle; unfold levels_sum; induction ps as [|p ps IH]; cbn [fold_right]; [lia |].
  specialize (Hle p); lia.
Qed.

Lemma levels_sum_strict ps m m' p :
  (forall q, level_at (penc prog) m q <= level_at (penc prog) m' q) ->
  In p ps -> level_at (penc prog) m p < level_at (penc prog) m' p ->
  levels_sum ps m < levels_sum ps m'.
Proof.
  intros Hle Hin Hstrict; induction ps as [|q ps IH]; cbn in Hin; [contradiction |].
  change (level_at (penc prog) m q + levels_sum ps m <
    level_at (penc prog) m' q + levels_sum ps m').
  destruct Hin as [<- | Hin].
  - pose proof (levels_sum_mono ps m m' Hle); lia.
  - specialize (IH Hin); specialize (Hle q); lia.
Qed.

Lemma forallb_failed {A} (f : A -> bool) xs :
  forallb f xs = false -> exists x, In x xs /\ f x = false.
Proof.
  induction xs as [|x xs IH]; cbn; [discriminate |].
  destruct (f x) eqn:Hx; cbn.
  - intro Hrest; destruct (IH Hrest) as [y [Hin Hy]]; exists y; auto.
  - intros _; exists x; auto.
Qed.

Lemma failed_pass_grows m : Map.wf (penc prog) m -> levels_ok prog m = false ->
  levels_sum (rule_nodes prog) m <
  levels_sum (rule_nodes prog) (raise_pass (penc prog) (program_edges prog) m).
Proof.
  intros Hwf Hfalse.
  assert (Hbad : exists h b w, In (h, (b, w)) (program_edges prog) /\
    level_at (penc prog) m h < level_at (penc prog) m b + w).
  { unfold levels_ok, levels_ok_c in Hfalse.
    rewrite Cost.value_bind, value_forallb_c in Hfalse.
    fold (program_edges prog) in Hfalse.
    apply forallb_failed in Hfalse as [[h [b w]] [Hin Hbad]].
    exists h, b, w; split; [exact Hin | apply Nat.leb_gt; exact Hbad]. }
  destruct Hbad as [h [b [w [Hin Hbad]]]].
  apply levels_sum_strict with (p := h).
  - intro q; apply raise_pass_grows, Hwf.
  - exact (proj1 (edge_nodes prog h b w Hin)).
  - pose proof (raise_pass_edge (penc prog) (program_edges prog) m h b w Hwf Hin); lia.
Qed.

Definition level_rank (ps : list P) (f : P -> nat) p :=
  length (filter (fun q => Nat.ltb (f q) (f p)) ps).

Lemma level_rank_mono ps (f : P -> nat) p q :
  f p <= f q -> level_rank ps f p <= level_rank ps f q.
Proof.
  intro Hpq; unfold level_rank; induction ps as [|x ps IH]; cbn [filter length]; [lia |].
  destruct (Nat.ltb (f x) (f p)) eqn:Hp;
    destruct (Nat.ltb (f x) (f q)) eqn:Hq; cbn [length]; try lia.
  apply Nat.ltb_lt in Hp; apply Nat.ltb_ge in Hq; lia.
Qed.

Lemma level_rank_strict ps (f : P -> nat) p q :
  In p ps -> f p < f q -> level_rank ps f p < level_rank ps f q.
Proof.
  intros Hin Hpq; unfold level_rank; induction ps as [|x ps IH]; cbn in Hin;
    [contradiction |].
  destruct Hin as [Heq | Hin]; cbn [filter length].
  - subst x; rewrite Nat.ltb_irrefl.
    assert (Hlt : Nat.ltb (f p) (f q) = true) by (apply Nat.ltb_lt; exact Hpq).
    rewrite Hlt; cbn [length].
    pose proof (level_rank_mono ps f p q (Nat.lt_le_incl _ _ Hpq)) as Hmono.
    unfold level_rank in Hmono; lia.
  - specialize (IH Hin).
    destruct (Nat.ltb (f x) (f p)) eqn:Hp;
      destruct (Nat.ltb (f x) (f q)) eqn:Hq; cbn [length]; try lia.
    apply Nat.ltb_lt in Hp; apply Nat.ltb_ge in Hq; lia.
Qed.

Lemma level_rank_bound ps (f : P -> nat) p : level_rank ps f p <= length ps.
Proof.
  unfold level_rank; induction ps as [|q ps IH]; cbn [filter length]; [lia |].
  destruct (Nat.ltb (f q) (f p)); cbn [length]; lia.
Qed.

Lemma ranked_edges st : stratified prog st -> forall h b w,
  In (h, (b, w)) (program_edges prog) ->
  level_rank (rule_nodes prog) (level st) b + w <=
  level_rank (rule_nodes prog) (level st) h.
Proof.
  intros [_ Hstrat] h b w Hin.
  pose proof (proj2 (edge_nodes prog h b w Hin)) as Hb.
  rewrite program_edges_equation in Hin; apply in_flat_map in Hin as [r [Hr He]].
  rewrite rule_edges_equation in He; apply in_map_iff in He as [l [He Hl]].
  specialize (Hstrat r l Hr Hl).
  destruct l as [a | a]; injection He as <- <- <-; cbn in Hstrat |- *.
  - rewrite Nat.add_0_r; apply level_rank_mono, Hstrat.
  - pose proof (level_rank_strict (rule_nodes prog) (level st) (pred a)
      (pred (head r)) Hb Hstrat); lia.
Qed.

Lemma raise_pass_bound es m (f : P -> nat) :
  Map.wf (penc prog) m -> (forall p, level_at (penc prog) m p <= f p) ->
  (forall h b w, In (h, (b, w)) es -> f b + w <= f h) ->
  forall p, level_at (penc prog) (raise_pass (penc prog) es m) p <= f p.
Proof.
  rewrite raise_pass_equation; revert m.
  induction es as [|[h [b w]] es IH]; intros m Hwf Hbound Hedges p; [apply Hbound |].
  cbn [fold_left]; apply IH.
  - rewrite raise_edge_equation; apply Map.wf_set, Hwf.
  - intro q; rewrite raise_edge_equation, level_set by exact Hwf.
    cbn [fst snd].
    destruct (eqb (penc prog) q h) eqn:Heq; [|apply Hbound].
    apply (eqb_true_iff _ HE) in Heq; subst q; apply Nat.max_lub; [apply Hbound |].
    specialize (Hedges h b w (or_introl eq_refl)); specialize (Hbound b); lia.
  - intros h' b' w' Hin; apply (Hedges h' b' w'); now right.
Qed.

Lemma levels_sum_bound ps m B :
  (forall p, In p ps -> level_at (penc prog) m p <= B) ->
  levels_sum ps m <= length ps * B.
Proof.
  intro Hbound; induction ps as [|p ps IH].
  - change (0 <= 0); lia.
  - change (level_at (penc prog) m p + levels_sum ps m <= B + length ps * B).
    assert (Hp := Hbound p (or_introl eq_refl)).
    assert (Hrest : levels_sum ps m <= length ps * B).
    { apply IH; intros q Hin; apply Hbound; now right. }
    lia.
Qed.

Lemma stratify_loop_complete st : stratified prog st -> forall n m,
  Map.wf (penc prog) m ->
  (forall p, level_at (penc prog) m p <= level_rank (rule_nodes prog) (level st) p) ->
  length (rule_nodes prog) * length (rule_nodes prog) <
    n + levels_sum (rule_nodes prog) m ->
  snd (stratify_loop prog n m) = true.
Proof.
  intro Hst; induction n as [|n IH]; intros m Hwf Hbound Hcapacity;
    rewrite stratify_loop_equation.
  - pose proof (levels_sum_bound (rule_nodes prog) m (length (rule_nodes prog)))
      as Hsum.
    assert (Hsum' : levels_sum (rule_nodes prog) m <=
      length (rule_nodes prog) * length (rule_nodes prog)).
    { apply Hsum; intros p _; eapply Nat.le_trans; [apply Hbound | apply level_rank_bound]. }
    lia.
  - destruct (levels_ok prog m) eqn:Hok; [reflexivity |].
    apply IH.
    + apply raise_pass_wf, Hwf.
    + apply raise_pass_bound; [exact Hwf | exact Hbound | apply ranked_edges, Hst].
    + pose proof (failed_pass_grows m Hwf Hok); lia.
Qed.

(** Injective predicate keys make the finite checker complete for source stratifications. *)
Theorem stratify_complete :
  (exists st, stratified prog st) -> exists st, stratify prog = Some st.
Proof.
  intros [st Hst]; rewrite stratify_equation.
  pose proof (stratify_loop_complete st Hst
    (length (rule_nodes prog) * length (rule_nodes prog) + 1)
    Map.empty (Map.wf_empty (penc prog))) as Hdone.
  assert (Hbound : forall p, level_at (penc prog) Map.empty p <=
    level_rank (rule_nodes prog) (level st) p).
  { intro p; rewrite level_at_equation, Map.get_empty; lia. }
  specialize (Hdone Hbound).
  assert (Hcapacity : length (rule_nodes prog) * length (rule_nodes prog) <
    length (rule_nodes prog) * length (rule_nodes prog) + 1 +
      levels_sum (rule_nodes prog) Map.empty) by lia.
  specialize (Hdone Hcapacity).
  destruct (stratify_loop prog _ Map.empty) as [m done]; cbn in Hdone.
  rewrite Hdone; eexists; reflexivity.
Qed.

End Complete.

Arguments stratify_c {P} prog : simpl never.
Arguments stratify {P} prog : simpl never.
